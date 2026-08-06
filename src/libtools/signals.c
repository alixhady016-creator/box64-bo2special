#define _GNU_SOURCE
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <syscall.h>
#include <stddef.h>
#include <stdarg.h>
#include <ucontext.h>
#include <setjmp.h>
#include <sys/mman.h>
#include <pthread.h>
#include <dirent.h>

// Validate if address is in executable code section
static int is_valid_code_range(uint32_t addr) {
    // t6zm.exe main code: 0x401000 - 0xB00000
    if (addr >= 0x401000 && addr < 0xB00000) return 1;
    
    // Wine DLLs: 0x7b000000 - 0x7c000000 
    if (addr >= 0x7b000000 && addr < 0x7c000000) return 1;
    
    // Reject data sections: 0xB00000+
    return 0;
}

#ifndef ANDROID
#include <execinfo.h>
#endif

#include "x64_signals.h"
#include "os.h"
#include "backtrace.h"
#include "box64context.h"
#include "debug.h"
#include "x64emu.h"
#include "emu/x64emu_private.h"
#include "emu/x64run_private.h"
#include <stdint.h>
#include <unistd.h>
#include <sys/mman.h>
#include <stdio.h> // For dprintf and close

#include "signals.h"
#include "box64stack.h"
#include "box64cpu.h"
#include "callback.h"
#include "elfloader.h"
#include "threads.h"
#include "custommem.h"
#include <fcntl.h> // For open, O_WRONLY, O_CREAT, O_APPEND
#define EIP_TRACE_SIZE 128
static volatile uint32_t eip_trace[EIP_TRACE_SIZE];
static volatile int eip_trace_idx = 0;

static int trace_fd = -1;
static void init_trace_fd() {
    if (trace_fd == -1) {
        trace_fd = open("/sdcard/box64_crash_debug.txt", O_WRONLY | O_CREAT | O_APPEND, 0666);
    }
}

// === 32-BIT ADDRESSABLE TLS ALLOCATION === 
// __thread variables can be allocated in 64-bit address space on ARM64, 
// but x86-32 code can only access 32-bit addresses. 
// Use static array pool instead to ensure 32-bit addressability. 

#define MAX_THREADS 32 
#define TLS_BLOCK_SIZE 4096 

// Static TLS pool - guaranteed to be in 32-bit addressable range 
static uint8_t tls_pool[MAX_THREADS][TLS_BLOCK_SIZE] __attribute__((aligned(16))) = {0}; 
static int tls_pool_used[MAX_THREADS] = {0}; 
static pthread_mutex_t tls_pool_mutex = PTHREAD_MUTEX_INITIALIZER; 

// Per-thread TLS block pointer (uses pthread_key for thread-local access) 
static pthread_key_t tls_block_key; 
static pthread_once_t tls_key_once = PTHREAD_ONCE_INIT; 

static void tls_key_destructor(void* ptr) { 
    // Free the TLS slot when thread exits 
    if (ptr) { 
        for (int i = 0; i < MAX_THREADS; i++) { 
            if (tls_pool[i] == (uint8_t*)ptr) { 
                pthread_mutex_lock(&tls_pool_mutex); 
                tls_pool_used[i] = 0; 
                pthread_mutex_unlock(&tls_pool_mutex); 
                break; 
            } 
        } 
    } 
} 

static void tls_key_create_once() { 
    pthread_key_create(&tls_block_key, tls_key_destructor); 
} 

// Allocate a TLS block for the current thread from the 32-bit pool 
static uint8_t* allocate_tls_block() { 
    pthread_once(&tls_key_once, tls_key_create_once); 
    
    // Check if this thread already has a TLS block 
    uint8_t* existing = (uint8_t*)pthread_getspecific(tls_block_key); 
    if (existing) return existing; 
    
    // Find free slot in pool 
    pthread_mutex_lock(&tls_pool_mutex); 
    for (int i = 0; i < MAX_THREADS; i++) { 
        if (!tls_pool_used[i]) { 
            tls_pool_used[i] = 1; 
            uint8_t* block = tls_pool[i]; 
            pthread_mutex_unlock(&tls_pool_mutex); 
            
            // Initialize to zero 
            memset(block, 0, TLS_BLOCK_SIZE); 
            
            // Store in thread-local storage 
            pthread_setspecific(tls_block_key, block); 
            
            return block; 
        } 
    } 
    pthread_mutex_unlock(&tls_pool_mutex); 
    
    // Pool exhausted - this shouldn't happen 
    init_trace_fd(); 
    if (trace_fd >= 0) { 
        dprintf(trace_fd, "[TLS_ALLOC] ERROR: TLS pool exhausted (max %d threads)\n", MAX_THREADS); 
    } 
    return NULL; 
} 

// Global array for per‑thread base structure pointers (emulates DAT_0280a410) 
static void* g_thread_base_ptrs[MAX_THREADS] = {0}; 

// Global array for status structures (size 0x4b8 each) 
static uint8_t g_status_array[MAX_THREADS][0x4b8] __attribute__((aligned(16))); 

static void init_fake_tls() { 
    // Get or allocate TLS block for this thread 
    uint8_t* tls_block = allocate_tls_block(); 
    if (!tls_block) { 
        // Fallback: allocation failed 
        return; 
    } 
    
    // Verify TLS block is in 32-bit addressable range 
    uintptr_t tls_addr = (uintptr_t)tls_block; 
    if (tls_addr > 0xFFFFFFFF) { 
        init_trace_fd(); 
        if (trace_fd >= 0) { 
            dprintf(trace_fd, "[TLS_INIT] ERROR: TLS block %p is above 32-bit range!\n", tls_block); 
        } 
        return; 
    } 
    
    // === PROACTIVE FULL PE MAPPING === 
    // Wine's WINEPRELOADRESERVE is too small (800KB vs 64MB needed) 
    // Force-map entire PE image space at startup 
    // t6zm.exe full range: 0x00400000 - 0x04376000 
    
    static int pe_mapped = 0; 
    if (!pe_mapped) { 
        void* pe_start = (void*)0x00400000; 
        size_t pe_size = 0x04376000 - 0x00400000;  // Full PE image 
        
        // Check if already mapped 
        if (msync(pe_start, 1, MS_ASYNC) == -1 && errno == ENOMEM) { 
            // Not mapped - force allocation 
            void* result = mmap(pe_start, pe_size, 
                               PROT_READ | PROT_WRITE | PROT_EXEC, 
                               MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 
                               -1, 0); 
            
            if (result != MAP_FAILED) { 
                memset(result, 0, pe_size); 

                // Verify .data section (0xcf7000-0x4332000) has EXEC permission 
                mprotect((void*)0x00CF7000, 0x04332000 - 0x00CF7000, 
                         PROT_READ | PROT_WRITE | PROT_EXEC); 
                
                init_trace_fd(); 
                if (trace_fd >= 0) { 
                    dprintf(trace_fd, "[PROACTIVE_PE_MAP] Mapped full PE image %p - %p (%zu MB)\n", 
                            pe_start, (void*)((uintptr_t)pe_start + pe_size), pe_size / 1024 / 1024); 
                    dprintf(trace_fd, "[PROACTIVE_PE_MAP] Explicitly set RWX on .data section (0x00CF7000-0x04332000)\n"); 
                } 
            } else { 
                init_trace_fd(); 
                if (trace_fd >= 0) { 
                    dprintf(trace_fd, "[PROACTIVE_PE_MAP] FAILED: %s\n", strerror(errno)); 
                } 
            } 
        } 
        pe_mapped = 1; 
  
    } 

    // Initialize common TLS fields 
    *(uint32_t*)(&tls_block[0x00]) = 0;          // Exception list 
    *(uint32_t*)(&tls_block[0x04]) = 0;          // Stack base 
    *(uint32_t*)(&tls_block[0x08]) = 0;          // Stack limit 
    *(uint32_t*)(&tls_block[0x18]) = (uintptr_t)tls_block;  // Self 
    
    // Setup TLS Array for FS:[0x2C] chain 
    *(uint32_t*)(&tls_block[0x2C]) = (uintptr_t)&tls_block[0x400]; 
    for(int i=0; i<128; ++i) { 
        *(uint32_t*)(&tls_block[0x400 + i*4]) = (uintptr_t)tls_block; 
    } 

    // Fix 0x5C Thread ID check (DAT_0280a5c8) 
    uint32_t this_tid = (uint32_t)syscall(__NR_gettid); 
    if (this_tid == 0) this_tid = 1; 

    uint32_t global_tid = 0; 
    if (memExist(0x0280a5c8) && (getProtection(0x0280a5c8) & PROT_READ)) { 
        global_tid = *(uint32_t*)0x0280a5c8; 
    } 

    if (global_tid == 0) { 
        // Main thread – set global and local TID 
        *(uint32_t*)0x0280a5c8 = this_tid; 
        *(uint32_t*)(tls_block + 0x5C) = this_tid; 
    }

    // Populate the real TEB ClientId.UniqueThread field at offset +0x24.
    // This is what Windows' actual GetCurrentThreadId() implementation reads
    // (via FS:[0x18] -> TEB self-pointer -> [TEB+0x24]).
    *(uint32_t*)(tls_block + 0x24) = this_tid;

    // Worker threads: do NOT touch TLS[0x5C] here. allocate_tls_block() 
    // already memset the block to 0 exactly once, on first allocation

    // TLS[0x58] will be linked lazily in the signal handler 
    *(uint32_t*)(tls_block + 0x58) = 0; 
    
    init_trace_fd();
    if (trace_fd >= 0) {
        dprintf(trace_fd, "[TLS_INIT] Fake TLS Initialized at %p\n", tls_block);
        dprintf(trace_fd, "           - FS:[0x2C] -> Array at %p\n", &tls_block[0x400]);
        dprintf(trace_fd, "           - TLS[0x5C] (TID) = %u (Global=0x%x)\n", this_tid, memExist(0x0280a5c8) ? *(uint32_t*)0x0280a5c8 : 0);
        dprintf(trace_fd, "           - 32-bit safe address: 0x%08lx\n", tls_addr);

        uint32_t tls_idx = memExist(0x003a3be4) ? *(uint32_t*)0x003a3be4 : 0xdeadbeef;
        uintptr_t tls_base_ptr = (uintptr_t)&tls_block[0x400];
        dprintf(trace_fd, "[TLS_INDEX] _tls_index = 0x%08x (at 0x003a3be4)\n", tls_idx);
        dprintf(trace_fd, "[TLS_INDEX] FS:[0x2c] array slot for game = addr 0x%08lx, value = 0x%08x\n",
                tls_base_ptr + tls_idx * 4,
                memExist(tls_base_ptr + tls_idx * 4) ? *(uint32_t*)(tls_base_ptr + tls_idx * 4) : 0);
    } 
    
    // Force FS base to point to our fake TLS if possible 
    x64emu_t *emu = thread_get_emu(); 
    if(emu) { 
         emu->segs_offs[_FS] = (uintptr_t)tls_block; 
         emu->segs_serial[_FS] = emu->context->sel_serial; // Match current global serial so GetSegmentBaseEmu() does NOT invalidate this override on the next FS access
         dprintf(trace_fd, "[SERIAL_CHECK] segs_serial[FS]=%u context->sel_serial=%u match=%s\n",
                    emu->segs_serial[_FS], emu->context->sel_serial,
                                (emu->segs_serial[_FS] == emu->context->sel_serial) ? "YES" : "NO -- STALE OVERRIDE");
         dprintf(trace_fd, "[TLS_FIX] segs_serial[_FS] stamped to context->sel_serial=%u (was %u)\n", emu->context->sel_serial, emu->segs_serial[_FS]);
         dprintf(trace_fd, "[TLS_FIX] segs_offs[FS] set to %p\n", (void*)emu->segs_offs[_FS]);
    } 
} 

#include "emu/x87emu_private.h"
#include "bridge.h"
#include "khash.h"
#include "x64trace.h"
#ifdef DYNAREC
#include "dynablock.h"
#include "../dynarec/dynablock_private.h"
#include "dynarec_native.h"
#include "dynarec/dynarec_arch.h"
#include "gdbjit.h"
#if defined(ARM64)
#include "dynarec/arm64/arm64_mapping.h"
#define CONTEXT_REG(P, X)   (P)->uc_mcontext.regs[X]
#define CONTEXT_PC(P)       (P)->uc_mcontext.pc
#elif defined(LA64)
#include "dynarec/la64/la64_mapping.h"
#define CONTEXT_REG(P, X)   (P)->uc_mcontext.__gregs[X]
#define CONTEXT_PC(P)       (P)->uc_mcontext.__pc;
#elif defined(RV64)
#include "dynarec/rv64/rv64_mapping.h"
#define CONTEXT_REG(P, X)   (P)->uc_mcontext.__gregs[X]
#define CONTEXT_PC(P)       (P)->uc_mcontext.__gregs[REG_PC]
#else
#error Unsupported Architecture
#endif //arch
#endif

#if defined(__powerpc64__)
#define PT_NIP 32
#endif

#include <libtools/signal_private.h>
#include <time.h>

#include <dlfcn.h> // For dlsym

// 1. Expanded buffer to accommodate the 0x3000 offsets found in Ghidra
static uint8_t engine_bootstrap[0x10000] __attribute__((aligned(16)));

static uint8_t vtable_object[0x5000] __attribute__((aligned(4096)));
static int dat_initialized = 0;

static int is_wine_environment() {
    return 0;
}

// --- SAFE ZONE FOR RESCUE RETURN VALUES ---
static void* global_safe_zone = NULL;
static size_t safe_zone_size = 0x10000;      // 64KB data
static size_t safe_zone_guard = 0x200000;    // 2MB guard (was 64KB)
static size_t safe_zone_total = 0x210000;    // 2MB + 64KB total
static void* safe_zone_base = NULL;          // Base allocation

static void* rescue_stub_page = NULL;
static size_t rescue_stub_cursor = 0;

static void init_safe_zone() {
    if (global_safe_zone) {
        // Already initialized
        return;
    }
    
    init_trace_fd();
    if (trace_fd >= 0) {
        dprintf(trace_fd, "[SAFEZONE_INIT_START] Allocating 0x%zx bytes (with 0x%zx guard)\n", 
               safe_zone_total, safe_zone_guard);
    }

    // Allocate 128KB total (64KB guard + 64KB data)
    safe_zone_base = mmap(NULL, safe_zone_total, 
                          PROT_READ | PROT_WRITE | PROT_EXEC, 
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    
    // Also allocate a page for rescue stubs (executable)
    rescue_stub_page = mmap(NULL, 0x1000, 
                           PROT_READ | PROT_WRITE | PROT_EXEC, 
                           MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);

    if (safe_zone_base != MAP_FAILED && rescue_stub_page != MAP_FAILED) {
        // SafeZone starts after guard region
        global_safe_zone = (void*)((char*)safe_zone_base + safe_zone_guard);
        
        // Fill guard region with pointers to guard base
        // This handles negative offsets from SafeZone (e.g. SafeZone[-1920])
        uint64_t* guard_ptrs = (uint64_t*)safe_zone_base;
        size_t guard_num = safe_zone_guard / sizeof(uint64_t);
        for (size_t i = 0; i < guard_num; i++) {
            guard_ptrs[i] = (uint64_t)safe_zone_base;
        }
        
        // Fill data region with pointers to data base (SafeZone)
        // This handles positive offsets from SafeZone
        uint64_t* data_ptrs = (uint64_t*)global_safe_zone;
        size_t data_num = safe_zone_size / sizeof(uint64_t);
        for (size_t i = 0; i < data_num; i++) {
            data_ptrs[i] = (uint64_t)global_safe_zone;
        }

        memset(rescue_stub_page, 0xCC, 0x1000); // Fill with INT3
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[SAFEZONE_INIT_OK] Base: %p, Guard: %p-%p, SafeZone: %p-%p, StubPage: %p\n", 
                   safe_zone_base, 
                   safe_zone_base, (char*)safe_zone_base + safe_zone_guard, 
                   global_safe_zone, (char*)global_safe_zone + safe_zone_size, 
                   rescue_stub_page);
        }
    } else {
        global_safe_zone = NULL;
        safe_zone_base = NULL;
        rescue_stub_page = NULL;
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[SAFEZONE_FAIL] Failed to allocate SafeZone or StubPage! Error: %s\n", strerror(errno));
        }
    }
}

// Generate a unique stub for this rescue target
// Stub: MOV RAX, SafeZone; JMP target
static void* generate_rescue_stub(uintptr_t target_addr) {
    init_trace_fd();
    if (trace_fd >= 0) {
        dprintf(trace_fd, "[STUB_GEN] Called with target=0x%lx, stub_page=%p, cursor=%zu\n", 
               target_addr, rescue_stub_page, rescue_stub_cursor);
    }

    if (!rescue_stub_page || rescue_stub_cursor + 32 > 0x1000) {
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[STUB_GEN_FAIL] page=%p, cursor=%zu\n", 
                   rescue_stub_page, rescue_stub_cursor);
        }
        return NULL;
    }
    
    uint8_t* p = (uint8_t*)rescue_stub_page + rescue_stub_cursor;
    void* stub_addr = (void*)p;
    
    // MOV RAX, global_safe_zone (64-bit mov: 48 B8 ... 8 bytes ...)
    *p++ = 0x48; *p++ = 0xB8;
    *(uint64_t*)p = (uint64_t)global_safe_zone;
    p += 8;
    
    // MOV R10, target (49 BA ... 8 bytes ...)
    *p++ = 0x49; *p++ = 0xBA;
    *(uint64_t*)p = (uint64_t)target_addr;
    p += 8;
    
    // JMP R10 (41 FF E2)
    *p++ = 0x41; *p++ = 0xFF; *p++ = 0xE2;
    
    rescue_stub_cursor += 32; // Advance cursor (aligned)
    
    if (trace_fd >= 0) {
        dprintf(trace_fd, "[STUB_GEN_OK] Created at %p, sets RAX=%p\n", 
               stub_addr, global_safe_zone);
    }

    return stub_addr;
}

static void log_memory_map_once() {
    static int done = 0;
    if(done) return;
    int out = open("/sdcard/box64_maps.txt", O_WRONLY | O_CREAT | O_TRUNC, 0666);
    int in = open("/proc/self/maps", O_RDONLY, 0);
    if(in >= 0 && out >= 0) {
        char buf[4096];
        ssize_t r;
        while((r = read(in, buf, sizeof(buf))) > 0) {
            ssize_t dummy_write_result = write(out, buf, r);
        }
    }
    if(in >= 0) close(in);
    if(out >= 0) close(out);
    done = 1;
}

// Get memory map information for a given address
// Returns 1 on success, 0 on failure
static int get_map_info(uintptr_t addr, uintptr_t* map_start, uintptr_t* map_end, char* path) {
    FILE* f = fopen("/proc/self/maps", "r");
    if (!f) {
        return 0;
    }
    
    char line[1024];
    while (fgets(line, sizeof(line), f)) {
        uintptr_t start, end;
        char perms[5];
        char pathname[512];
        
        // Parse line format: start-end perms offset dev inode pathname
        if (sscanf(line, "%lx-%lx %4s %*x %*x:%*x %*d %511[^\n]", 
                   &start, &end, perms, pathname) >= 3) {
            
            // Check if the address falls within this range
            if (addr >= start && addr < end) {
                *map_start = start;
                *map_end = end;
                
                // If pathname was not captured (no path in maps entry), set to empty string
                if (sscanf(line, "%lx-%lx %4s %*x %*x:%*x %*d %511[^\n]", 
                          &start, &end, perms, pathname) == 4) {
                    strcpy(path, pathname);
                } else {
                    path[0] = '\0';
                }
                
                fclose(f);
                return 1;
            }
        }
    }
    
    fclose(f);
    return 0;
}

// Simple x86-32 instruction length decoder (handles common cases) 
static int get_x86_instruction_length(uint8_t* code) { 
    int len = 0; 
    int has_modrm = 0; 
    
    if (!code) return 0; 
    
    // Prefixes 
    while(code[len] == 0x66 || code[len] == 0x67 || 
          code[len] == 0xf2 || code[len] == 0xf3 || 
          code[len] == 0x2e || code[len] == 0x3e || 
          code[len] == 0x26 || code[len] == 0x64 || code[len] == 0x65) { 
        len++; 
    } 
    
    uint8_t opcode = code[len++]; 
    
    // Two-byte opcode 
    if(opcode == 0x0f) { 
        opcode = code[len++]; 
    } 
    
    // Instructions that require ModR/M byte 
    if((opcode >= 0x00 && opcode <= 0x0b) ||   // ADD, OR, ADC, SBB, AND, SUB, XOR, CMP 
       (opcode >= 0x10 && opcode <= 0x3b && opcode != 0x0f) || 
       (opcode >= 0x80 && opcode <= 0x8f) ||   // immediate ops, MOV, LEA, etc. 
       opcode == 0xc0 || opcode == 0xc1 ||     // shift/rotate with imm8 
       opcode == 0xc6 || opcode == 0xc7 ||     // MOV imm to r/m 
       opcode == 0xd0 || opcode == 0xd1 || 
       opcode == 0xd2 || opcode == 0xd3 || 
       opcode == 0xf6 || opcode == 0xf7 ||     // TEST, NOT, NEG, MUL, etc. 
       opcode == 0xfe || opcode == 0xff) {     // INC, DEC, CALL, JMP, PUSH 
        has_modrm = 1; 
    } 
    
    if(has_modrm) { 
        uint8_t modrm = code[len++]; 
        uint8_t mod = (modrm >> 6) & 3; 
        uint8_t rm = modrm & 7; 
        
        // SIB byte 
        if(mod != 3 && rm == 4) { 
            len++;  // SIB byte 
        } 
        
        // Displacement 
        if(mod == 1) { 
            len += 1;  // disp8 
        } else if(mod == 2 || (mod == 0 && rm == 5)) { 
            len += 4;  // disp32 
        } 
    } 
    
    // Immediate operands (simplified - covers common cases) 
    switch(opcode) { 
        case 0x68:  // PUSH imm32 
        case 0xa9:  // TEST EAX, imm32 
        case 0xb8: case 0xb9: case 0xba: case 0xbb:  // MOV reg, imm32 
        case 0xbc: case 0xbd: case 0xbe: case 0xbf: 
            len += 4; 
            break; 
        case 0x6a:  // PUSH imm8 
        case 0x70: case 0x71: case 0x72: case 0x73:  // Jcc short 
        case 0x74: case 0x75: case 0x76: case 0x77: 
        case 0x78: case 0x79: case 0x7a: case 0x7b: 
        case 0x7c: case 0x7d: case 0x7e: case 0x7f: 
        case 0xeb:  // JMP short 
            len += 1; 
            break; 
        case 0xe8:  // CALL near 
        case 0xe9:  // JMP near 
            len += 4; 
            break; 
    } 
    
    return len; 
}

// GLOBAL / STATIC VARIABLES for Rescue History
#define HISTORY_SIZE 16
static uintptr_t rescue_history[HISTORY_SIZE] = {0};
static int history_idx = 0;
static __thread uintptr_t targeted_last_rip = 0;
static __thread int targeted_count = 0;
static void* bridge_dummy = NULL;
static void* engine_dummy_zone = NULL;
static uint32_t engine_zone_magic = 0xDEADBEEF;
static __thread int bridge_call_counter = 0;

static void sigstack_destroy(void* p)
{
    x64_stack_t *ss = (x64_stack_t*)p;
    box_free(ss);
}

static pthread_key_t sigstack_key;
static pthread_once_t sigstack_key_once = PTHREAD_ONCE_INIT;

static void sigstack_key_alloc() {
    pthread_key_create(&sigstack_key, sigstack_destroy);
}

x64_stack_t* sigstack_getstack() {
    return (x64_stack_t*)pthread_getspecific(sigstack_key);
}

#ifndef DYNAREC
typedef void dynablock_t;
dynablock_t* FindDynablockFromNativeAddress(void* addr) {return NULL;}
uintptr_t getX64Address(dynablock_t* db, uintptr_t pc) {return 0;}
#endif

// this allow handling "safe" function that just abort if accessing a bad address
static __thread JUMPBUFF signal_jmpbuf;
#ifdef ANDROID
#define SIG_JMPBUF signal_jmpbuf
#else
#define SIG_JMPBUF &signal_jmpbuf
#endif
static __thread int signal_jmpbuf_active = 0;


//1<<1 is mutex_prot, 1<<8 is mutex_dyndump
#define is_memprot_locked (1<<1)
#define is_dyndump_locked (1<<8)
uint64_t RunFunctionHandler(x64emu_t* emu, int* exit, int dynarec, x64_ucontext_t* sigcontext, uintptr_t fnc, int nargs, ...)
{
    if(fnc==0 || fnc==1) {
        va_list va;
        va_start (va, nargs);
        int sig = va_arg(va, int);
        va_end (va);
        printf_log(LOG_NONE, "%04d|Warning, calling Signal %d function handler %s\n", GetTID(), sig, fnc?"SIG_IGN":"SIG_DFL");
        if(fnc==0) {
            printf_log(LOG_NONE, "Unhandled signal %d caught, aborting\n", sig);
            abort();
        }
        return 0;
    }
#ifdef HAVE_TRACE
    uintptr_t old_start = trace_start, old_end = trace_end;
#if 0
    trace_start = 0; trace_end = 1; // disabling trace, globably for now...
#endif
#endif
#ifndef USE_CUSTOM_MEM
    // because a signal can interupt a malloc-like function
    // Dynarec cannot be used in signal handling unless custom malloc is used
    if(dynarec==1)
        dynarec = 0;
#endif
    if(!emu)
        emu = thread_get_emu();
    #ifdef DYNAREC
    if (BOX64ENV(dynarec_test))
        emu->test.test = 0;
    #endif

    /*SetFS(emu, default_fs);*/
    for (int i=0; i<6; ++i)
        emu->segs_serial[i] = 0;

    int align = nargs&1;

    if(nargs>6)
        R_RSP -= (nargs-6+align)*sizeof(void*);   // need to push in reverse order

    uint64_t *p = (uint64_t*)R_RSP;

    va_list va;
    va_start (va, nargs);
    for (int i=0; i<nargs; ++i) {
        if(i<6) {
            int nn[] = {_DI, _SI, _DX, _CX, _R8, _R9};
            emu->regs[nn[i]].q[0] = va_arg(va, uint64_t);
        } else {
            *p = va_arg(va, uint64_t);
            p++;
        }
    }
    va_end (va);

    printf_log(LOG_DEBUG, "%04d|signal #%d function handler %p called, RSP=%p\n", GetTID(), R_EDI, (void*)fnc, (void*)R_RSP);

    int oldquitonlongjmp = emu->flags.quitonlongjmp;
    emu->flags.quitonlongjmp = 2;
    int old_cs = R_CS;
    R_CS = 0x33;

    if(dynarec)
        DynaCall(emu, fnc);
    else
        EmuCall(emu, fnc);

    if(nargs>6 && !emu->flags.longjmp)
        R_RSP+=((nargs-6+align)*sizeof(void*));

    if(!emu->flags.longjmp && R_CS==0x33)
        R_CS = old_cs;

    emu->flags.quitonlongjmp = oldquitonlongjmp;

    #ifdef DYNAREC
    if (BOX64ENV(dynarec_test)) {
        emu->test.test = 0;
        emu->test.clean = 0;
    }
#endif

    if(emu->flags.longjmp) {
        // longjmp inside signal handler, lets grab all relevent value and do the actual longjmp in the signal handler
        emu->flags.longjmp = 0;
        if(sigcontext) {
            sigcontext->uc_mcontext.gregs[X64_R8] = R_R8;
            sigcontext->uc_mcontext.gregs[X64_R9] = R_R9;
            sigcontext->uc_mcontext.gregs[X64_R10] = R_R10;
            sigcontext->uc_mcontext.gregs[X64_R11] = R_R11;
            sigcontext->uc_mcontext.gregs[X64_R12] = R_R12;
            sigcontext->uc_mcontext.gregs[X64_R13] = R_R13;
            sigcontext->uc_mcontext.gregs[X64_R14] = R_R14;
            sigcontext->uc_mcontext.gregs[X64_R15] = R_R15;
            sigcontext->uc_mcontext.gregs[X64_RAX] = R_RAX;
            sigcontext->uc_mcontext.gregs[X64_RCX] = R_RCX;
            sigcontext->uc_mcontext.gregs[X64_RDX] = R_RDX;
            sigcontext->uc_mcontext.gregs[X64_RDI] = R_RDI;
            sigcontext->uc_mcontext.gregs[X64_RSI] = R_RSI;
            sigcontext->uc_mcontext.gregs[X64_RBP] = R_RBP;
            sigcontext->uc_mcontext.gregs[X64_RSP] = R_RSP;
            sigcontext->uc_mcontext.gregs[X64_RBX] = R_RBX;
            sigcontext->uc_mcontext.gregs[X64_RIP] = R_RIP;
            // flags
            sigcontext->uc_mcontext.gregs[X64_EFL] = emu->eflags.x64;
            // get segments
            sigcontext->uc_mcontext.gregs[X64_CSGSFS] = ((uint64_t)(R_CS)) | (((uint64_t)(R_GS))<<16) | (((uint64_t)(R_FS))<<32);
        } else {
            printf_log(LOG_NONE, "Warning, longjmp in signal but no sigcontext to change\n");
        }
    }
    if(exit)
        *exit = emu->exit;

    uint64_t ret = R_RAX;

#ifdef HAVE_TRACE
    trace_start = old_start; trace_end = old_end;
#endif

    return ret;
}

EXPORT int my_sigaltstack(x64emu_t* emu, const x64_stack_t* ss, x64_stack_t* oss)
{
    if(!ss && !oss) {   // this is not true, ss can be NULL to retreive oss info only
        errno = EFAULT;
        return -1;
    }
    signal_jmpbuf_active = 1;
    if(sigsetjmp(SIG_JMPBUF, 1)) {
        // segfault while gathering function name...
        errno = EFAULT;
        return -1;
    }

    x64_stack_t *new_ss = (x64_stack_t*)pthread_getspecific(sigstack_key);
    if(oss) {
        if(!new_ss) {
            oss->ss_flags = SS_DISABLE;
            oss->ss_sp = emu->init_stack;
            oss->ss_size = emu->size_stack;
        } else {
            oss->ss_flags = new_ss->ss_flags;
            oss->ss_sp = new_ss->ss_sp;
            oss->ss_size = new_ss->ss_size;
        }
    }
    if(!ss) {
        signal_jmpbuf_active = 0;
        return 0;
    }
    printf_log(LOG_DEBUG, "%04d|sigaltstack called ss=%p[flags=0x%x, sp=%p, ss=0x%lx], oss=%p\n", GetTID(), ss, ss->ss_flags, ss->ss_sp, ss->ss_size, oss);
    if(ss->ss_flags && ss->ss_flags!=SS_DISABLE && ss->ss_flags!=SS_ONSTACK) {
        errno = EINVAL;
        signal_jmpbuf_active = 0;
        return -1;
    }

    if(ss->ss_flags==SS_DISABLE) {
        if(new_ss)
            box_free(new_ss);
        pthread_setspecific(sigstack_key, NULL);
        signal_jmpbuf_active = 0;
        return 0;
    }

    if(!new_ss)
        new_ss = (x64_stack_t*)box_calloc(1, sizeof(x64_stack_t));
    new_ss->ss_flags = 0;
    new_ss->ss_sp = ss->ss_sp;
    new_ss->ss_size = ss->ss_size;

    pthread_setspecific(sigstack_key, new_ss);
    signal_jmpbuf_active = 0;
    return 0;
}

#ifdef DYNAREC
x64emu_t* getEmuSignal(x64emu_t* emu, ucontext_t* p, dynablock_t* db)
{
    if(db && CONTEXT_REG(p, xEmu)>0x10000) {
        emu = (x64emu_t*)CONTEXT_REG(p, xEmu);
    }
    return emu;
}
#endif
int write_opcode(uintptr_t rip, uintptr_t native_ip, int is32bits);
void adjustregs(x64emu_t* emu, void* pc) {
    if(!pc) return;
// tests some special cases
    uint8_t* mem = (uint8_t*)R_RIP;
    rex_t rex = {0};
    int rep = 0;
    int is66 = 0;
    int idx = 0;
    rex.is32bits = (R_CS==0x0023);
    while ((mem[idx]>=0x40 && mem[idx]<=0x4f && !rex.is32bits) || mem[idx]==0xF2 || mem[idx]==0xF3 || mem[idx]==0x66) {
        switch(mem[idx]) {
            case 0x40 ... 0x4f:
                rex.rex = mem[idx];
                break;
            case 0xF2:
            case 0xF3:
                rep = mem[idx]-0xF1;
                break;
            case 0x66:
                is66 = 1;
                break;
        }
        ++idx;
    }
    dynarec_log(LOG_INFO, "Checking opcode: rex=%02hhx is32bits=%d, rep=%d is66=%d %02hhX %02hhX %02hhX %02hhX\n", rex.rex, rex.is32bits, rep, is66, mem[idx+0], mem[idx+1], mem[idx+2], mem[idx+3]);
#ifdef DYNAREC
#ifdef ARM64
    if(mem[idx+0]==0xA4 || mem[idx+0]==0xA5) {
        uint32_t opcode = *(uint32_t*)pc;
        // (rep) movsX, read done, write not... so opcode is a STR?_S9_postindex(A, B, C) with C to be substracted to RSI
        // xx111000000iiiiiiiii01nnnnnttttt xx = size, iiiiiiiii = signed offset, t = value, n = address
        if((opcode & 0b00111111111000000000110000000000)==0b00111000000000000000010000000000) {
            int offset = (opcode>>12)&0b111111111;
            offset<<=31-9;
            offset>>=31-9;  // sign extend
            dynarec_log(LOG_INFO, "\tAdjusting RSI: %d\n", -offset);
            R_RSI -= offset;
        }
        return;
    }
    if(mem[idx+0]==0x8F && (mem[idx+1]&0xc0)!=0xc0) {
        // POP Ed, issue on write address, restore RSP as in before the pop
        dynarec_log(LOG_INFO, "\tAdjusting RSP: %d\n", -(is66?2:(rex.is32bits?4:8)));
        R_RSP -= is66?2:(rex.is32bits?4:8);
    }
#elif defined(LA64)
#elif defined(RV64)
#else
#error  Unsupported architecture
#endif
#endif
}

void copyUCTXreg2Emu(x64emu_t* emu, ucontext_t* p, uintptr_t ip) {
#ifdef DYNAREC
    #define GO(R) emu->regs[_##R].q[0] = CONTEXT_REG(p, x##R)
    GO(RAX);
    GO(RCX);
    GO(RDX);
    GO(RBX);
    GO(RSP);
    GO(RBP);
    GO(RSI);
    GO(RDI);
    GO(R8);
    GO(R9);
    GO(R10);
    GO(R11);
    GO(R12);
    GO(R13);
    GO(R14);
    GO(R15);
    #undef GO
    emu->ip.q[0] = ip;
    emu->eflags.x64 = CONTEXT_REG(p, xFlags);
#endif
}

KHASH_SET_INIT_INT64(unaligned)
static kh_unaligned_t    *unaligned = NULL;

void add_unaligned_address(uintptr_t addr)
{
    if(!unaligned)
        unaligned = kh_init(unaligned);
    khint_t k;
    int ret;
    k = kh_put(unaligned, unaligned, addr, &ret);    // just add
}

int is_addr_unaligned(uintptr_t addr)
{
    if(!unaligned)
        return 0;
    khint_t k = kh_get(unaligned, unaligned, addr);
    return (k==kh_end(unaligned))?0:1;
}

#ifdef DYNAREC
int nUnalignedRange(uintptr_t start, size_t size)
{
    if(!unaligned)
        return 0;
    int n = 0;
    uintptr_t end = start + size -1;
    uintptr_t addr;
    kh_foreach_key(unaligned, addr,
        if(addr>=start && addr<=end)
            ++n;
    );
    return n;
}
void getUnalignedRange(uintptr_t start, size_t size, uintptr_t addrs[])
{
    if(!unaligned)
        return;
    int n = 0;
    uintptr_t end = start + size -1;
    uintptr_t addr;
    kh_foreach_key(unaligned, addr,
        if(addr>=start && addr<=end)
            addrs[n++] = addr;
    );
}

int mark_db_unaligned(dynablock_t* db, uintptr_t x64pc)
{
    add_unaligned_address(x64pc);
    db->hash++; // dirty the block
    MarkDynablock(db);      // and mark it
if(BOX64ENV(showsegv)) printf_log(LOG_INFO, "Marked db %p as dirty, and address %p as needing unaligned handling\n", db, (void*)x64pc);
    return 2;   // marked, exit handling...
}
#endif

int sigbus_specialcases(siginfo_t* info, void * ucntx, void* pc, void* _fpsimd, dynablock_t* db, uintptr_t x64pc, int is32bits)
{
    ucontext_t *p = (ucontext_t *)ucntx;
    if((uintptr_t)pc<0x10000)
        return 0;
#ifdef DYNAREC
    if(ARCH_UNALIGNED(db, x64pc))
        /*return*/ mark_db_unaligned(db, x64pc);    // don't force an exit for now
#endif
#ifdef ARM64

    uint32_t opcode = *(uint32_t*)pc;
    struct fpsimd_context *fpsimd = (struct fpsimd_context *)_fpsimd;
    //printf_log(LOG_INFO, "Checking SIGBUS special cases with pc=%p, opcode=%x, fpsimd=%p\n", pc, opcode, fpsimd);
    if((opcode&0b10111111110000000000000000000000)==0b10111001000000000000000000000000) {
        // this is STR
        int scale = (opcode>>30)&3;
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        uint64_t offset = (opcode>>10)&0b111111111111;
        offset<<=scale;
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = p->uc_mcontext.regs[val];
        if(scale==3 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<2; ++i)
                ((volatile uint32_t*)addr)[i] = (value>>(i*32))&0xffffffff;
        } else
            for(int i=0; i<(1<<scale); ++i)
                addr[i] = (value>>(i*8))&0xff;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b10111111111000000000110000000000) == 0b10111000000000000000000000000000) {
        // this is a STUR that SIGBUS if accessing unaligned device memory
        int size = 1<<((opcode>>30)&3);
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        int64_t offset = (opcode>>12)&0b111111111;
        if((offset>>(9-1))&1)
            offset |= (0xffffffffffffffffll<<9);
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = p->uc_mcontext.regs[val];
        if(size==8 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<2; ++i)
                ((volatile uint32_t*)addr)[i] = (value>>(i*32))&0xffffffff;
        } else
            for(int i=0; i<size; ++i)
                addr[i] = (value>>(i*8))&0xff;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b00111111010000000000000000000000)==0b00111101000000000000000000000000) {
        // this is VSTR
        int scale = (opcode>>30)&3;
        if((opcode>>23)&1)
            scale+=4;
        if(scale>4)
            return 0;
        if(!fpsimd)
            return 0;
        uint64_t offset = (opcode>>10)&0b111111111111;
        offset<<=scale;
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        __uint128_t value = fpsimd->vregs[val];
        if(scale>2 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<(1<<(scale-2)); ++i)
                ((volatile uint32_t*)addr)[i] = (value>>(i*32))&0xffffffff;
        } else
            for(int i=0; i<(1<<scale); ++i)
                addr[i] = (value>>(i*8))&0xff;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b00111111011000000000110000000000)==0b00111100000000000000000000000000) {
        // this is VSTRU
        int scale = (opcode>>30)&3;
        if((opcode>>23)&1)
            scale+=4;
        if(scale>4)
            return 0;
        if(!fpsimd)
            return 0;
        int64_t offset = (opcode>>12)&0b111111111;
        if((offset>>(9-1))&1)
            offset |= (0xffffffffffffffffll<<9);
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        __uint128_t value = fpsimd->vregs[val];
        if(scale>2 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<(1<<(scale-2)); ++i)
                ((volatile uint32_t*)addr)[i] = (value>>(i*32))&0xffffffff;
        } else
            for(int i=0; i<(1<<scale); ++i)
                addr[i] = (value>>(i*8))&0xff;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b00111111010000000000000000000000)==0b00111101010000000000000000000000) {
        // this is VLDR
        int scale = (opcode>>30)&3;
        if((opcode>>23)&1)
            scale+=4;
        if(scale>4)
            return 0;
        if(!fpsimd)
            return 0;
        uint64_t offset = (opcode>>10)&0b111111111111;
        offset<<=scale;
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        __uint128_t value = 0;
        if(scale>2 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<(1<<(scale-2)); ++i)
                value |= ((__uint128_t)(((volatile uint32_t*)addr)[i]))<<(i*32);
        } else
            for(int i=0; i<(1<<scale); ++i)
                value |= ((__uint128_t)addr[i])<<(i*8);
        fpsimd->vregs[val] = value;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b00111111011000000000110000000000)==0b00111100010000000000000000000000) {
        // this is VLDRU
        int scale = (opcode>>30)&3;
        if((opcode>>23)&1)
            scale+=4;
        if(scale>4)
            return 0;
        if(!fpsimd)
            return 0;
        int64_t offset = (opcode>>12)&0b111111111;
        if((offset>>(9-1))&1)
            offset |= (0xffffffffffffffffll<<9);
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        __uint128_t value = 0;
        if(scale>2 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<(1<<(scale-2)); ++i)
                value |= ((__uint128_t)(((volatile  uint32_t*)addr)[i]))<<(i*32);
        } else
            for(int i=0; i<(1<<scale); ++i)
                value |= ((__uint128_t)addr[i])<<(i*8);
        fpsimd->vregs[val] = value;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b10111111110000000000000000000000)==0b10111001010000000000000000000000) {
        // this is LDR
        int scale = (opcode>>30)&3;
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        uint64_t offset = (opcode>>10)&0b111111111111;
        offset<<=scale;
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = 0;
        if(scale==3 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<2; ++i)
                value |= ((uint64_t)((volatile  uint32_t*)addr)[i]) << (i*32);
        } else
            for(int i=0; i<(1<<scale); ++i)
                value |= ((uint64_t)addr[i]) << (i*8);
        p->uc_mcontext.regs[val] = value;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b10111111111000000000110000000000) == 0b10111000010000000000000000000000) {
        // this is a LDUR
        int size = 1<<((opcode>>30)&3);
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        int64_t offset = (opcode>>12)&0b111111111;
        if((offset>>(9-1))&1)
            offset |= (0xffffffffffffffffll<<9);
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = 0;
        if(size==8 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<2; ++i)
                value |= ((uint64_t)((volatile  uint32_t*)addr)[i]) << (i*32);
        } else
            for(int i=0; i<size; ++i)
                value |= ((uint64_t)addr[i]) << (i*8);
        p->uc_mcontext.regs[val] = value;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b11111111110000000000000000000000)==0b01111001000000000000000000000000) {
        // this is STRH
        int scale = (opcode>>30)&3;
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        uint64_t offset = (opcode>>10)&0b111111111111;
        offset<<=scale;
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = p->uc_mcontext.regs[val];
        for(int i=0; i<(1<<scale); ++i)
            addr[i] = (value>>(i*8))&0xff;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b11111111111000000000110000000000)==0b01111000000000000000000000000000) {
        // this is STURH
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        int64_t offset = (opcode>>12)&0b111111111;
        if((offset>>(9-1))&1)
            offset |= (0xffffffffffffffffll<<9);
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = p->uc_mcontext.regs[val];
        for(int i=0; i<2; ++i)
            addr[i] = (value>>(i*8))&0xff;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b11111111111000000000110000000000)==0b01111000001000000000100000000000) {
        // this is STRH reg, reg
        int scale = (opcode>>30)&3;
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        int dest2 = (opcode>>16)&31;
        int option = (opcode>>13)&0b111;
        int S = (opcode>>12)&1;
        if(option!=0b011)
            return 0;   // only LSL is supported
        uint64_t offset = p->uc_mcontext.regs[dest2]<<S;
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest] + offset);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = p->uc_mcontext.regs[val];
        for(int i=0; i<(1<<scale); ++i)
            addr[i] = (value>>(i*8))&0xff;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b11111111110000000000000000000000)==0b10101001000000000000000000000000) {
        // This is STP reg1, reg2, [reg3 + off]
        int scale = 2+((opcode>>31)&1);
        int val1 = opcode&31;
        int val2 = (opcode>>10)&31;
        int dest = (opcode>>5)&31;
        int64_t offset = (opcode>>15)&0b1111111;
        if((offset>>(7-1))&1)
            offset |= (0xffffffffffffffffll<<7);
        offset <<= scale;
        uintptr_t addr= p->uc_mcontext.regs[dest] + offset;
        if(is32bits) addr = addr&0xffffffff;
        if((((uintptr_t)addr)&3)==0) {
            ((volatile uint32_t*)addr)[0] = p->uc_mcontext.regs[val1];
            ((volatile uint32_t*)addr)[1] = p->uc_mcontext.regs[val2];
        } else {
            __uint128_t value = ((__uint128_t)p->uc_mcontext.regs[val2])<<64 | p->uc_mcontext.regs[val1];
            for(int i=0; i<(1<<scale); ++i)
                ((volatile uint8_t*)addr)[i] = (value>>(i*8))&0xff;
        }
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b11111111110000000000000000000000)==0b10101101000000000000000000000000) {
        // This is (V)STP qreg1, qreg2, [reg3 + off]
        int scale = 2+((opcode>>30)&3);
        int val1 = opcode&31;
        int val2 = (opcode>>10)&31;
        int dest = (opcode>>5)&31;
        int64_t offset = (opcode>>15)&0b1111111;
        if((offset>>(7-1))&1)
            offset |= (0xffffffffffffffffll<<7);
        offset <<= scale;
        uintptr_t addr= p->uc_mcontext.regs[dest] + offset;
        if(is32bits) addr = addr&0xffffffff;
        if((((uintptr_t)addr)&3)==0) {
            for(int i=0; i<4; ++i)
                ((volatile uint32_t*)addr)[0+i] = (fpsimd->vregs[val1]>>(i*32))&0xffffffff;
            for(int i=0; i<4; ++i)
                ((volatile uint32_t*)addr)[4+i] = (fpsimd->vregs[val2]>>(i*32))&0xffffffff;
        } else {
            for(int i=0; i<16; ++i)
                ((volatile uint8_t*)addr)[i] = (fpsimd->vregs[val1]>>(i*8))&0xff;
            for(int i=0; i<16; ++i)
                ((volatile uint8_t*)addr)[16+i] = (fpsimd->vregs[val2]>>(i*8))&0xff;
        }
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b10111111111111111111110000000000)==0b00001101000000001000010000000000) {
        // this is ST1.D
        int idx = (opcode>>30)&1;
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest]);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = fpsimd->vregs[val]>>(idx*64);
        if((((uintptr_t)addr)&3)==0) {
            for(int i=0; i<2; ++i)
                ((volatile uint32_t*)addr)[i] = (value>>(i*32))&0xffffffff;
        } else
            for(int i=0; i<8; ++i)
                addr[i] = (value>>(i*8))&0xff;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b10111111111000000000110000000000) == 0b10111000010000000000010000000000) {
        // this is a LDR postoffset
        int size = 1<<((opcode>>30)&3);
        int val = opcode&31;
        int dest = (opcode>>5)&31;
        int64_t offset = (opcode>>12)&0b111111111;
        if((offset>>(9-1))&1)
            offset |= (0xffffffffffffffffll<<9);
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[dest]);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = 0;
        if(size==8 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<2; ++i)
                value |= ((uint64_t)((volatile  uint32_t*)addr)[i]) << (i*32);
        } else
            for(int i=0; i<size; ++i)
                value |= ((uint64_t)addr[i]) << (i*8);
        p->uc_mcontext.regs[val] = value;
        p->uc_mcontext.regs[dest] += offset;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
    if((opcode&0b10111111111000000000110000000000) == 0b10111000000000000000010000000000) {
        // this is a STR postoffset
        int size = 1<<((opcode>>30)&3);
        int val = opcode&31;
        int src = (opcode>>5)&31;
        int64_t offset = (opcode>>12)&0b111111111;
        if((offset>>(9-1))&1)
            offset |= (0xffffffffffffffffll<<9);
        volatile uint8_t* addr = (void*)(p->uc_mcontext.regs[src]);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = p->uc_mcontext.regs[val];
        if(size==8 && (((uintptr_t)addr)&3)==0) {
            for(int i=0; i<2; ++i)
                ((volatile uint32_t*)addr)[i] = (value>>(i*32))&0xffffffff;
        } else
            for(int i=0; i<size; ++i)
                addr[i] = (value>>(i*8))&0xff;
        p->uc_mcontext.regs[src] += offset;
        p->uc_mcontext.pc+=4;   // go to next opcode
        return 1;
    }
#elif RV64
#define GET_FIELD(v, high, low) (((v) >> low) & ((1ULL << (high - low + 1)) - 1))
#define SIGN_EXT(val, val_sz) (((int32_t)(val) << (32 - (val_sz))) >> (32 - (val_sz)))


    uint32_t inst = *(uint32_t*)pc;

    uint32_t funct3 = GET_FIELD(inst, 14, 12);
    uint32_t opcode = GET_FIELD(inst, 6, 0);
    if ((opcode == 0b0100011 || opcode == 0b0100111 /* F */) && (funct3 == 0b010 /* (F)SW */ || funct3 == 0b011 /* (F)SD */ || funct3 == 0b001 /* SH */)) {
        int val = (inst >> 20) & 0x1f;
        int dest = (inst >> 15) & 0x1f;
        int64_t imm = (GET_FIELD(inst, 31, 25) << 5) | (GET_FIELD(inst, 11, 7));
        imm = SIGN_EXT(imm, 12);
        volatile uint8_t *addr = (void *)(p->uc_mcontext.__gregs[dest] + imm);
        if(is32bits) addr = (uint8_t*)(((uintptr_t)addr)&0xffffffff);
        uint64_t value = opcode == 0b0100011 ? p->uc_mcontext.__gregs[val] : p->uc_mcontext.__fpregs.__d.__f[val<<1];
        for(int i = 0; i < (funct3 == 0b010 ? 4 : funct3 == 0b011 ? 8 : 2); ++i) {
            addr[i] = (value >> (i * 8)) & 0xff;
        }
        p->uc_mcontext.__gregs[0] += 4; // pc += 4
        return 1;
    } else {
        printf_log(LOG_NONE, "Unsupported SIGBUS special cases with pc=%p, opcode=%x\n", pc, inst);
    }

#undef GET_FIELD
#undef SIGN_EXT
#endif
    return 0;
#undef CHECK
}

#ifdef USE_CUSTOM_MUTEX
extern uint32_t mutex_prot;
extern uint32_t mutex_blocks;
#else
extern pthread_mutex_t mutex_prot;
extern pthread_mutex_t mutex_blocks;
#endif

// unlock mutex that are locked by current thread (for signal handling). Return a mask of unlock mutex
int unlockMutex()
{
    int ret = 0;
    int i;
    #ifdef USE_CUSTOM_MUTEX
    uint32_t tid = (uint32_t)GetTID();
    #define GO(A, B)                                    \
    i = (native_lock_storeifref2_d(&A, 0, tid) == tid); \
    if (i) {                                            \
        ret |= (1 << B);                                \
    }
    #else
    #define GO(A, B)          \
    i = checkUnlockMutex(&A); \
    if (i) {                  \
        ret |= (1 << B);      \
    }
    #endif

    GO(mutex_blocks, 0)
    GO(mutex_prot, 1)

    GO(my_context->mutex_trace, 7)
    #ifdef DYNAREC
    GO(my_context->mutex_dyndump, 8)
    #else
    GO(my_context->mutex_lock, 8)
    #endif
    GO(my_context->mutex_tls, 9)
    GO(my_context->mutex_thread, 10)
    GO(my_context->mutex_bridge, 11)
    #undef GO

    return ret;
}

#ifdef BOX32
void my_sigactionhandler_oldcode_32(x64emu_t* emu, int32_t sig, int simple, siginfo_t* info, void * ucntx, int* old_code, void* cur_db);
#endif
void my_sigactionhandler_oldcode_64(x64emu_t* emu, int32_t sig, int simple, siginfo_t* info, void * ucntx, int* old_code, void* cur_db)
{
    int Locks = unlockMutex();


    int log_minimum = (BOX64ENV(showsegv))?LOG_NONE:LOG_DEBUG;

    printf_log(LOG_DEBUG, "Sigactionhanlder for signal #%d called (jump to %p/%s)\n", sig, (void*)my_context->signals[sig], GetNativeName((void*)my_context->signals[sig]));

    uintptr_t restorer = my_context->restorer[sig];
    // get that actual ESP first!
    if(!emu)
        emu = thread_get_emu();
    uintptr_t frame = R_RSP;
#if defined(DYNAREC)
    dynablock_t* db = (dynablock_t*)cur_db;//FindDynablockFromNativeAddress(pc);
    ucontext_t *p = (ucontext_t *)ucntx;
    void* pc = NULL;
    if(p) {
        pc = (void*)CONTEXT_PC(p);
        if(db)
            frame = (uintptr_t)CONTEXT_REG(p, xRSP);
    }
#else
    (void)ucntx; (void)cur_db;
    void* pc = NULL;
#endif

    // stack tracking
    x64_stack_t *new_ss = my_context->onstack[sig]?(x64_stack_t*)pthread_getspecific(sigstack_key):NULL;
    int used_stack = 0;
    if(new_ss) {
        if(new_ss->ss_flags == SS_ONSTACK) { // already using it!
            frame = ((uintptr_t)emu->regs[_SP].q[0] - 128) & ~0x0f;
        } else {
            frame = (uintptr_t)(((uintptr_t)new_ss->ss_sp + new_ss->ss_size - 16) & ~0x0f);
            used_stack = 1;
            new_ss->ss_flags = SS_ONSTACK;
        }
    } else {
        frame = frame&~15;
        frame -= 0x200; // redzone
    }

    // TODO: do I need to really setup 2 stack frame? That doesn't seems right!
    // setup stack frame
    frame -= 512+64+16*16;
    void* xstate = (void*)frame;
    frame -= sizeof(siginfo_t);
    siginfo_t* info2 = (siginfo_t*)frame;
    memcpy(info2, info, sizeof(siginfo_t));
    // try to fill some sigcontext....
    frame -= sizeof(x64_ucontext_t);
    x64_ucontext_t   *sigcontext = (x64_ucontext_t*)frame;
    // get general register
    sigcontext->uc_mcontext.gregs[X64_R8] = R_R8;
    sigcontext->uc_mcontext.gregs[X64_R9] = R_R9;
    sigcontext->uc_mcontext.gregs[X64_R10] = R_R10;
    sigcontext->uc_mcontext.gregs[X64_R11] = R_R11;
    sigcontext->uc_mcontext.gregs[X64_R12] = R_R12;
    sigcontext->uc_mcontext.gregs[X64_R13] = R_R13;
    sigcontext->uc_mcontext.gregs[X64_R14] = R_R14;
    sigcontext->uc_mcontext.gregs[X64_R15] = R_R15;
    sigcontext->uc_mcontext.gregs[X64_RAX] = R_RAX;
    sigcontext->uc_mcontext.gregs[X64_RCX] = R_RCX;
    sigcontext->uc_mcontext.gregs[X64_RDX] = R_RDX;
    sigcontext->uc_mcontext.gregs[X64_RDI] = R_RDI;
    sigcontext->uc_mcontext.gregs[X64_RSI] = R_RSI;
    sigcontext->uc_mcontext.gregs[X64_RBP] = R_RBP;
    sigcontext->uc_mcontext.gregs[X64_RSP] = R_RSP;
    sigcontext->uc_mcontext.gregs[X64_RBX] = R_RBX;
    sigcontext->uc_mcontext.gregs[X64_RIP] = R_RIP;
    // flags
    sigcontext->uc_mcontext.gregs[X64_EFL] = emu->eflags.x64;
    CLEAR_FLAG(F_TF);   // now clear TF flags inside the signal handler
    // get segments
    sigcontext->uc_mcontext.gregs[X64_CSGSFS] = ((uint64_t)(R_CS)) | (((uint64_t)(R_GS))<<16) | (((uint64_t)(R_FS))<<32);
    if(R_CS==0x23) {
        // trucate regs to 32bits, just in case
        #define GO(R)   sigcontext->uc_mcontext.gregs[X64_R##R]&=0xFFFFFFFF
        GO(AX);
        GO(CX);
        GO(DX);
        GO(DI);
        GO(SI);
        GO(BP);
        GO(SP);
        GO(BX);
        GO(IP);
        #undef GO
    }
    // get FloatPoint status
    sigcontext->uc_mcontext.fpregs = xstate;//(struct x64_libc_fpstate*)&sigcontext->xstate;
    fpu_xsave_mask(emu, xstate, 0, 0b111);
    memcpy(&sigcontext->xstate, xstate, sizeof(sigcontext->xstate));
    ((struct x64_fpstate*)xstate)->res[12] = 0x46505853;   // magic number to signal an XSTATE type of fpregs
    ((struct x64_fpstate*)xstate)->res[13] = 0; // offset to xstate after this?
    // get signal mask

    if(new_ss) {
        sigcontext->uc_stack.ss_sp = new_ss->ss_sp;
        sigcontext->uc_stack.ss_size = new_ss->ss_size;
        sigcontext->uc_stack.ss_flags = new_ss->ss_flags;
    } else
        sigcontext->uc_stack.ss_flags = SS_DISABLE;
    // Try to guess some X64_TRAPNO
    /*
    TRAP_x86_DIVIDE     = 0,   // Division by zero exception
    TRAP_x86_TRCTRAP    = 1,   // Single-step exception
    TRAP_x86_NMI        = 2,   // NMI interrupt
    TRAP_x86_BPTFLT     = 3,   // Breakpoint exception
    TRAP_x86_OFLOW      = 4,   // Overflow exception
    TRAP_x86_BOUND      = 5,   // Bound range exception
    TRAP_x86_PRIVINFLT  = 6,   // Invalid opcode exception
    TRAP_x86_DNA        = 7,   // Device not available exception
    TRAP_x86_DOUBLEFLT  = 8,   // Double fault exception
    TRAP_x86_FPOPFLT    = 9,   // Coprocessor segment overrun
    TRAP_x86_TSSFLT     = 10,  // Invalid TSS exception
    TRAP_x86_SEGNPFLT   = 11,  // Segment not present exception
    TRAP_x86_STKFLT     = 12,  // Stack fault
    TRAP_x86_PROTFLT    = 13,  // General protection fault
    TRAP_x86_PAGEFLT    = 14,  // Page fault
    TRAP_x86_ARITHTRAP  = 16,  // Floating point exception
    TRAP_x86_ALIGNFLT   = 17,  // Alignment check exception
    TRAP_x86_MCHK       = 18,  // Machine check exception
    TRAP_x86_CACHEFLT   = 19   // SIMD exception (via SIGFPE) if CPU is SSE capable otherwise Cache flush exception (via SIGSEV)
    */
    uint32_t prot = getProtection((uintptr_t)info->si_addr);
    uint32_t mmapped = memExist((uintptr_t)info->si_addr);
    uint32_t sysmapped = (info->si_addr<(void*)box64_pagesize)?1:mmapped;
    uint32_t real_prot = 0;
    int skip = 1;   // in case sigjump is used to restore exectuion, 1 will switch to interpreter, 3 will switch to dynarec
    if(prot&PROT_READ) real_prot|=PROT_READ;
    if(prot&PROT_WRITE) real_prot|=PROT_WRITE;
    if(prot&PROT_EXEC) real_prot|=PROT_WRITE;
    if(prot&PROT_DYNAREC) real_prot|=PROT_WRITE;
    sigcontext->uc_mcontext.gregs[X64_ERR] = 0;
    sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 0;
    if(sig==X64_SIGBUS)
        sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 17;
    else if(sig==X64_SIGSEGV) {
        if((uintptr_t)info->si_addr == sigcontext->uc_mcontext.gregs[X64_RIP]) {
            if(info->si_errno==0xbad0) {
                //bad opcode
                sigcontext->uc_mcontext.gregs[X64_ERR] = 0;
                sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 13;
                info2->si_code = 128;
                info2->si_errno = 0;
                info2->si_addr = NULL;
            } else if (info->si_errno==0xecec) {
                // no excute bit on segment
                sigcontext->uc_mcontext.gregs[X64_ERR] = 0x14|((sysmapped && !(real_prot&PROT_READ))?0:1);
                sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 14;
                if(!mmapped) info2->si_code = 1;
                info2->si_errno = 0;
            } else if (info->si_errno==0xb09d) {
                // bound exception
                sigcontext->uc_mcontext.gregs[X64_ERR] = 0;
                sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 5;
                info2->si_errno = 0;
            }else {
                sigcontext->uc_mcontext.gregs[X64_ERR] = 0x14|((sysmapped && !(real_prot&PROT_READ))?0:1);
                sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 14;
            }
        } else {
            sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 14;
            sigcontext->uc_mcontext.gregs[X64_ERR] = 4|((sysmapped && !(real_prot&PROT_READ))?0:1);
            if(write_opcode(sigcontext->uc_mcontext.gregs[X64_RIP], (uintptr_t)pc, (R_CS==0x23)))
                sigcontext->uc_mcontext.gregs[X64_ERR] |= 2;
        }
        if(info->si_code == SEGV_ACCERR && old_code)
            *old_code = -1;
        if(info->si_errno==0x1234) {
            sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 13;
            info2->si_errno = 0;
        } else if(info->si_errno==0xdead) {
            // INT x
            uint8_t int_n = info->si_code;
            info2->si_errno = 0;
            info2->si_code = 128;
            info2->si_addr = NULL;
            sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 13;
            skip = 3;   // can resume in dynarec
            // some special cases...
            if(int_n==3) {
                info2->si_signo = X64_SIGTRAP;
                sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 3;
                sigcontext->uc_mcontext.gregs[X64_ERR] = 0;
            } else if(int_n==0x04) {
                sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 4;
                sigcontext->uc_mcontext.gregs[X64_ERR] = 0;
            } else if (int_n==0x29 || int_n==0x2c || int_n==0x2d) {
                sigcontext->uc_mcontext.gregs[X64_ERR] = 0x02|(int_n<<3);
            } else {
                sigcontext->uc_mcontext.gregs[X64_ERR] = 0x0a|(int_n<<3);
                sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 13;
            }
        } else if(info->si_errno==0xcafe) { // divide by 0
            info2->si_errno = 0;
            sigcontext->uc_mcontext.gregs[X64_ERR] = 0;
            sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 0;
            info2->si_signo = X64_SIGFPE;
            skip = 3; // can resume in dynarec
        }
    } else if(sig==X64_SIGFPE) {
        if (info->si_code == FPE_INTOVF)
            sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 4;
        else
            sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 19;
        skip = 3;
    } else if(sig==X64_SIGILL) {
        info2->si_code = 2;
        sigcontext->uc_mcontext.gregs[X64_TRAPNO] = 6;
        info2->si_addr = (void*)sigcontext->uc_mcontext.gregs[X64_RIP];
    } else if(sig==X64_SIGTRAP) {
        if(info->si_code==1) {  //single step
            info2->si_code = 2;
            info2->si_addr = (void*)sigcontext->uc_mcontext.gregs[X64_RIP];
        } else
            info2->si_code = 128;
        sigcontext->uc_mcontext.gregs[X64_TRAPNO] = info->si_code;
        sigcontext->uc_mcontext.gregs[X64_ERR] = 0;
    } else {
        skip = 3;   // other signal can resume in interpretor
    }
    //TODO: SIGABRT generate what?
    printf_log((sig==10)?LOG_DEBUG:log_minimum, "Signal %d: si_addr=%p, TRAPNO=%d, ERR=%d, RIP=%p, prot=%x, mmapped:%d\n", sig, (void*)info2->si_addr, sigcontext->uc_mcontext.gregs[X64_TRAPNO], sigcontext->uc_mcontext.gregs[X64_ERR],sigcontext->uc_mcontext.gregs[X64_RIP], prot, mmapped);
    #ifdef DYNAREC
    if(sig==3)
        SerializeAllMapping();  // Signal Interupt: it's a good time to serialize the mappings if needed
    #endif
    // call the signal handler
    x64_ucontext_t sigcontext_copy = *sigcontext;
    // save old value from emu
    #define GO(A) uint64_t old_##A = R_##A
    GO(RAX);
    GO(RDI);
    GO(RSI);
    GO(RDX);
    GO(RCX);
    GO(R8);
    GO(R9);
    GO(RBP);
    #undef GO
    // set stack pointer
    R_RSP = frame;
    // set frame pointer
    R_RBP = sigcontext->uc_mcontext.gregs[X64_RBP];

    int exits = 0;
    int ret;
    int dynarec = 0;
    #ifdef DYNAREC
    if(!(sig==X64_SIGSEGV || (Locks&is_dyndump_locked) || (Locks&is_memprot_locked)))
        dynarec = 1;
    #endif
    ret = RunFunctionHandler(emu, &exits, dynarec, sigcontext, my_context->signals[info2->si_signo], 3, info2->si_signo, info2, sigcontext);
    // restore old value from emu
    if(used_stack)  // release stack
        new_ss->ss_flags = 0;
    #define GO(A) R_##A = old_##A
    GO(RAX);
    GO(RDI);
    GO(RSI);
    GO(RDX);
    GO(RCX);
    GO(R8);
    GO(R9);
    GO(RBP);
    #undef GO

    if(memcmp(sigcontext, &sigcontext_copy, sizeof(x64_ucontext_t))) {
        if(emu->jmpbuf) {
            #define GO(R)   emu->regs[_##R].q[0]=sigcontext->uc_mcontext.gregs[X64_R##R]
            GO(AX);
            GO(CX);
            GO(DX);
            GO(DI);
            GO(SI);
            GO(BP);
            GO(SP);
            GO(BX);
            #undef GO
            #define GO(R)   emu->regs[_##R].q[0]=sigcontext->uc_mcontext.gregs[X64_##R]
            GO(R8);
            GO(R9);
            GO(R10);
            GO(R11);
            GO(R12);
            GO(R13);
            GO(R14);
            GO(R15);
            #undef GO
            if((skip==1) && (emu->ip.q[0]!=sigcontext->uc_mcontext.gregs[X64_RIP]))
                skip = 3;   // if it jumps elsewhere, it can resume with dynarec...
            emu->ip.q[0]=sigcontext->uc_mcontext.gregs[X64_RIP];
            // flags
            emu->eflags.x64=sigcontext->uc_mcontext.gregs[X64_EFL];
            // get segments
            uint16_t seg;
            seg = (sigcontext->uc_mcontext.gregs[X64_CSGSFS] >> 0)&0xffff;
            #define GO(S) if(emu->segs[_##S]!=seg)  emu->segs[_##S]=seg
            GO(CS);
            seg = (sigcontext->uc_mcontext.gregs[X64_CSGSFS] >> 16)&0xffff;
            GO(GS);
            seg = (sigcontext->uc_mcontext.gregs[X64_CSGSFS] >> 32)&0xffff;
            GO(FS);
            #undef GO
            for(int i=0; i<6; ++i)
                emu->segs_serial[i] = 0;
            printf_log((sig==10)?LOG_DEBUG:log_minimum, "Context has been changed in Sigactionhanlder, doing siglongjmp to resume emu at %p, RSP=%p (resume with %s)\n", (void*)R_RIP, (void*)R_RSP, (skip==3)?"Dynarec":"Interp");
            if(old_code)
                *old_code = -1;    // re-init the value to allow another segfault at the same place
            //relockMutex(Locks);   // do not relock mutex, because of the siglongjmp, whatever was running is canceled
            #ifdef DYNAREC
            if(Locks & is_dyndump_locked)
                CancelBlock64(1);
            #endif
            #ifdef RV64
            emu->xSPSave = emu->old_savedsp;
            #endif
            #ifdef ANDROID
            siglongjmp(*emu->jmpbuf, skip);
            #else
            siglongjmp(emu->jmpbuf, skip);
            #endif
        }
        printf_log(LOG_INFO, "Warning, context has been changed in Sigactionhanlder%s\n", (sigcontext->uc_mcontext.gregs[X64_RIP]!=sigcontext_copy.uc_mcontext.gregs[X64_RIP])?" (EIP changed)":"");
    }
    // restore regs...
    #define GO(R)   R_##R=sigcontext->uc_mcontext.gregs[X64_##R]
    GO(RAX);
    GO(RCX);
    GO(RDX);
    GO(RDI);
    GO(RSI);
    GO(RBP);
    GO(RSP);
    GO(RBX);
    GO(R8);
    GO(R9);
    GO(R10);
    GO(R11);
    GO(R12);
    GO(R13);
    GO(R14);
    GO(R15);
    GO(RIP);
    #undef GO
    emu->eflags.x64=sigcontext->uc_mcontext.gregs[X64_EFL];
    uint16_t seg;
    seg = (sigcontext->uc_mcontext.gregs[X64_CSGSFS] >> 0)&0xffff;
    #define GO(S) emu->segs[_##S]=seg; emu->segs_serial[_##S] = 0;
    GO(CS);
    seg = (sigcontext->uc_mcontext.gregs[X64_CSGSFS] >> 16)&0xffff;
    GO(GS);
    seg = (sigcontext->uc_mcontext.gregs[X64_CSGSFS] >> 32)&0xffff;
    GO(FS);
    #undef GO

    printf_log(LOG_DEBUG, "Sigactionhanlder main function returned (exit=%d, restorer=%p)\n", exits, (void*)restorer);
    if(exits) {
        //relockMutex(Locks);   // the thread will exit, so no relock there
        #ifdef DYNAREC
        if(Locks & is_dyndump_locked)
            CancelBlock64(1);
        #endif
        exit(ret);
    }
    if(restorer)
        RunFunctionHandler(emu, &exits, 0, NULL, restorer, 0);
    relockMutex(Locks);
}

static int get_mov_rax_length(uintptr_t rip) {
    if (!memExist(rip)) return 0;
    uint8_t* code = (uint8_t*)rip;
    
    // Check for REX prefix
    int offset = 0;
    if (code[0] >= 0x40 && code[0] <= 0x4f) {
        offset++;
    }
    
    if (!memExist(rip + offset + 1)) return 0; // Check opcode and modrm
    
    uint8_t opcode = code[offset];
    
    // Case: MOV r/m -> r (8B)
    if (opcode == 0x8B) {
        uint8_t modrm = code[offset+1];
        int reg = (modrm >> 3) & 7;
        
        // Destination must be RAX (reg=0)
        if (reg != 0) return 0;
        
        int mod = (modrm >> 6) & 3;
        int rm = modrm & 7;
        
        int len = offset + 2; // Prefix + Opcode + ModRM
        
        if (mod == 0 && rm == 5) { // RIP-relative (32-bit disp)
            return len + 4;
        }
        if (mod == 0) {
            if (rm == 4) { // SIB (no disp)
                 // Check SIB existence
                 if (!memExist(rip + len)) return 0;
                 uint8_t sib = code[offset+2];
                 if ((sib & 7) == 5) return len + 1 + 4; // SIB + disp32
                 return len + 1;
            }
            return len; // [reg]
        }
        if (mod == 1) {
            if (rm == 4) return len + 1 + 1; // SIB + disp8
            return len + 1; // [reg] + disp8
        }
        if (mod == 2) {
            if (rm == 4) return len + 1 + 4; // SIB + disp32
            return len + 4; // [reg] + disp32
        }
    }
    
    return 0;
}

void my_sigactionhandler_oldcode(x64emu_t* emu, int32_t sig, int simple, siginfo_t* info, void * ucntx, int* old_code, void* cur_db, uintptr_t x64pc)
{
    #define GO(A) uintptr_t old_##A = R_##A;
    GO(RAX);
    GO(RBX);
    GO(RCX);
    GO(RDX);
    GO(RBP);
    GO(RSP);
    GO(RDI);
    GO(RSI);
    GO(R8);
    GO(R9);
    GO(R10);
    GO(R11);
    GO(R12);
    GO(R13);
    GO(R14);
    GO(R15);
    GO(RIP);
    #undef GO
    x64flags_t old_eflags;
    deferred_flags_t old_df;
    multiuint_t old_op1;
    multiuint_t old_op2;
    multiuint_t old_res;
    sse_regs_t old_xmm[16];
    sse_regs_t old_ymm[16];
    mmx87_regs_t old_mmx[8];
    mmx87_regs_t old_x87[8];
    uint32_t old_top = emu->top;
    memcpy(old_xmm, emu->xmm, sizeof(old_xmm));
    memcpy(old_ymm, emu->ymm, sizeof(old_ymm));
    memcpy(old_mmx, emu->mmx, sizeof(old_mmx));
    memcpy(old_x87, emu->x87, sizeof(old_x87));
    #define GO(A) old_##A = emu->A
    GO(eflags);
    GO(df);
    GO(op1);
    GO(op2);
    GO(res);
    #undef GO
    #ifdef DYNAREC
    dynablock_t* db = cur_db;
    if(db && ucntx) {
        void * pc =(void*)CONTEXT_PC((ucontext_t*)ucntx);
        copyUCTXreg2Emu(emu, ucntx, x64pc);
        adjustregs(emu, pc);
        if(db && db->arch_size)
            ARCH_ADJUST(db, emu, ucntx, x64pc);
    }
    #endif
    #ifdef BOX32
    if(box64_is32bits) {
        my_sigactionhandler_oldcode_32(emu, sig, simple, info, ucntx, old_code, cur_db);
    } else
    #endif
    my_sigactionhandler_oldcode_64(emu, sig, simple, info, ucntx, old_code, cur_db);
    #define GO(A) R_##A = old_##A
    GO(RAX);
    GO(RBX);
    GO(RCX);
    GO(RDX);
    GO(RBP);
    GO(RSP);
    GO(RDI);
    GO(RSI);
    GO(R8);
    GO(R9);
    GO(R10);
    GO(R11);
    GO(R12);
    GO(R13);
    GO(R14);
    GO(R15);
    GO(RIP);
    #undef GO
    #define GO(A) emu->A = old_##A
    GO(eflags);
    GO(df);
    GO(op1);
    GO(op2);
    GO(res);
    #undef GO
    memcpy(emu->xmm, old_xmm, sizeof(old_xmm));
    memcpy(emu->ymm, old_ymm, sizeof(old_ymm));
    memcpy(emu->mmx, old_mmx, sizeof(old_mmx));
    memcpy(emu->x87, old_x87, sizeof(old_x87));
    emu->top = old_top;
}

extern void* current_helper;
#define USE_SIGNAL_MUTEX
#ifdef USE_SIGNAL_MUTEX
#ifdef USE_CUSTOM_MUTEX
static uint32_t mutex_dynarec_prot = 0;
#else
static pthread_mutex_t mutex_dynarec_prot = PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP;
#endif
#define lock_signal()     mutex_lock(&mutex_dynarec_prot)
#define unlock_signal()   mutex_unlock(&mutex_dynarec_prot)
#else   // USE_SIGNAL_MUTEX
#define lock_signal()
#define unlock_signal()
#endif

extern int box64_quit;
extern int box64_exit_code;

#ifdef DYNAREC
extern void ClearCache(void* start, size_t len);
#endif

static void mark_exception_handled(uintptr_t fault_addr, uintptr_t pc) {
    (void)fault_addr;
    (void)pc;
}

static void* watchdog_thread(void* arg) {
    (void)arg;
    int tick = 0;
    while (1) {
        sleep(10);
        tick++;
        init_trace_fd();
        if (trace_fd < 0) continue;

        dprintf(trace_fd, "[WATCHDOG] ===== Tick=%d =====\n", tick);

        // Log known game .data addresses
        if (memExist(0x0280a5c0) && (getProtection(0x0280a5c8) & PROT_READ))
            dprintf(trace_fd, "[WATCHDOG] DAT_0280a5c0       = 0x%08x\n",
                    *(uint32_t*)0x0280a5c0);
        if (memExist(0x0280a5c8) && (getProtection(0x0280a5c8) & PROT_READ))
            dprintf(trace_fd, "[WATCHDOG] DAT_0280a5c8       = 0x%08x (main TID)\n",
                    *(uint32_t*)0x0280a5c8);
        if (memExist(0x0280a628) && (getProtection(0x0280a5c8) & PROT_READ))
            dprintf(trace_fd, "[WATCHDOG] DAT_0280a628       = 0x%08x (thread handle)\n",
                    *(uint32_t*)0x0280a628);

        // Log DAT_01258ff0 and DAT_01259950 — HMAC table pointer and sentinel
        if (memExist(0x01258ff0) && (getProtection(0x0280a5c8) & PROT_READ))
            dprintf(trace_fd, "[WATCHDOG] DAT_01258ff0       = 0x%08x (HMAC table ptr)\n",
                    *(uint32_t*)0x01258ff0);
        if (memExist(0x01259950) && (getProtection(0x0280a5c8) & PROT_READ))
            dprintf(trace_fd, "[WATCHDOG] DAT_01259950       = 0x%08x (HMAC sentinel)\n",
                    *(uint32_t*)0x01259950);
        // Log DAT_03396074 — VEH handle, confirm it survives
        if (memExist(0x03396074) && (getProtection(0x0280a5c8) & PROT_READ))
            dprintf(trace_fd, "[WATCHDOG] DAT_03396074       = 0x%08x (VEH handle)\n",
                    *(uint32_t*)0x03396074);

        // Enumerate all threads via /proc/self/task and log wchan + state
        // This shows what kernel function each thread is blocked in
        // wchan = 0 means thread is running (not blocked in kernel)
        char task_path[64];
        DIR* task_dir = opendir("/proc/self/task");
        if (task_dir) {
            struct dirent* entry;
            int thread_count = 0;
            dprintf(trace_fd, "[WATCHDOG] Thread states:\n");
            while ((entry = readdir(task_dir)) != NULL) {
                if (entry->d_name[0] == '.') continue;
                pid_t tid = (pid_t)atoi(entry->d_name);
                if (tid == 0) continue;
                thread_count++;

                // Read wchan
                char wchan[128] = "unknown";
                snprintf(task_path, sizeof(task_path),
                         "/proc/self/task/%d/wchan", tid);
                int wfd = open(task_path, O_RDONLY);
                if (wfd >= 0) {
                    int n = read(wfd, wchan, sizeof(wchan)-1);
                    if (n > 0) wchan[n] = '\0';
                    else wchan[0] = '\0';
                    close(wfd);
                }

                // Read thread name from comm
                char comm[32] = "?";
                snprintf(task_path, sizeof(task_path),
                         "/proc/self/task/%d/comm", tid);
                int cfd = open(task_path, O_RDONLY);
                if (cfd >= 0) {
                    int n = read(cfd, comm, sizeof(comm)-1);
                    if (n > 0) {
                        comm[n] = '\0';
                        // Strip trailing newline
                        if (n > 0 && comm[n-1] == '\n') comm[n-1] = '\0';
                    }
                    close(cfd);
                }

                dprintf(trace_fd, "[WATCHDOG]   TID=%-6d %-20s wchan=%s\n",
                        tid, comm, wchan);
            }
            closedir(task_dir);
            dprintf(trace_fd, "[WATCHDOG] Total threads: %d\n", thread_count);
        } else {
            dprintf(trace_fd, "[WATCHDOG] opendir(/proc/self/task) failed: %s\n",
                    strerror(errno));
        }
    }
    return NULL;
}


void my_box64signalhandler(int32_t sig, siginfo_t* info, void * ucntx)
{
    // === Fix 3: Add Safety to TRACE Blocks (Single trace_fd) ===
    init_trace_fd();
    
    // Get emu structure for register access
    x64emu_t* emu = thread_get_emu();

    // === VEH diagnostics (periodic) ===
    static int veh_check_counter = 0;
    if (trace_fd >= 0 && (veh_check_counter++ % 100 == 0)) {
        if (memExist(0x03396074) && (getProtection(0x0280a5c8) & PROT_READ)) {
            dprintf(trace_fd, "[VEH_CHECK #%d] DAT_03396074 = 0x%08x\n",
                    veh_check_counter, *(uint32_t*)0x03396074);
        }
        if (memExist(0x03396078) && (getProtection(0x0280a5c8) & PROT_READ)) {
            dprintf(trace_fd, "[VEH_CHECK #%d] DAT_03396078 = %p\n",
                    veh_check_counter, *(void**)0x03396078);
        }
    }
    
    // === EIP TRACE RECORDING ===
    uint32_t current_rip = (uint32_t)R_RIP;
    int idx = eip_trace_idx++ % EIP_TRACE_SIZE;
    eip_trace[idx] = current_rip;

    void* addr = (void*)info->si_addr;
    uintptr_t fault_addr = (uintptr_t)addr;
    int x64_sig = signal_from_x64(sig);

    // [HANDLER_ENTRY]
    if (trace_fd >= 0) {
        dprintf(trace_fd, "\n[HANDLER_ENTRY] Sig=%d | Addr=%p | Code=%d | Thread=%d\n", 
            x64_sig, addr, info->si_code, GetTID());
    }

    static int box64_ready = 0;
    static __thread void* my_base = NULL;
    static __thread void* my_secondary = NULL;

    // Defer until box64 is fully initialized
    if (!box64_ready && my_context && my_context->system) {
        box64_ready = 1; // box64 is now initialized globally
    }

    if (box64_ready && !my_base) {
        // This thread hasn't had its structures allocated yet
        init_fake_tls(); // sets up the basic TLS block (FS:[0x2C] etc.)

        my_base = box_calloc(1, 0x6000);
        my_secondary = box_calloc(1, 0x77c0);
        if (my_base && my_secondary) {
            *(uintptr_t*)((uint8_t*)my_base + 0x5da8) = (uintptr_t)my_secondary;
            
            // Use a global status array index – assign a slot number.
            static int next_slot = 0;
            static pthread_mutex_t slot_mutex = PTHREAD_MUTEX_INITIALIZER;
            pthread_mutex_lock(&slot_mutex);
            int slot = next_slot++;
            if (slot >= MAX_THREADS) slot = 0; // wrap around
            pthread_mutex_unlock(&slot_mutex);

            *(uintptr_t*)((uint8_t*)my_secondary + 0x1220) = (uintptr_t)&g_status_array[slot];
            *(uint32_t*)&g_status_array[slot] = 7;
            
            // Store base pointer in global array for backward compatibility if needed
            g_thread_base_ptrs[slot] = my_base;
        }

        // Also set TLS[0x58] to my_base
        x64emu_t* emu = thread_get_emu();
        if (emu && emu->segs_offs[_FS]) {
            *(uintptr_t*)(emu->segs_offs[_FS] + 0x58) = (uintptr_t)my_base;

        // FIX: populate the TLS pointer array slot for this thread.
        // FS:[0x2c] at TEB+0x2c is a POINTER to the TLS array, not the array itself.
        // init_fake_tls() allocates the array separately (e.g. at 0x361a7b00) and stores
        // that address at segs_offs[_FS]+0x2c. We must dereference that pointer first,
        // then write my_base into slot _tls_index of the array.
        // FUN_0047fb60: ECX=FS:[0x2c] → EDX=[ECX+_tls_index*4] → CMP [EDX+0x5c],0
        {
            uint32_t tls_idx = memExist(0x003a3be4) && (getProtection(0x0280a5c8) & PROT_READ) ? *(uint32_t*)0x003a3be4 : 0;
            // Read the array pointer from TEB+0x2c (dereference FS:[0x2c])
            uintptr_t tls_array_ptr = *(uintptr_t*)(emu->segs_offs[_FS] + 0x2c);
            if (tls_array_ptr && my_base) {
                // Write my_base into the correct slot of the array
                *(uintptr_t*)(tls_array_ptr + tls_idx * sizeof(uintptr_t)) = (uintptr_t)my_base;
                // Zero +0x5c so FUN_0047fb60's lazy GetCurrentThreadId() init fires correctly
                *(uint32_t*)((uint8_t*)my_base + 0x5c) = 0;
                if (trace_fd >= 0) {
                    dprintf(trace_fd,
                        "[TLS_LAZY_FIX] TLS array=0x%08lx slot[%u]=0x%p for TID=%d\n",
                        tls_array_ptr, tls_idx, my_base, GetTID());
                }
            } else {
                if (trace_fd >= 0) {
                    dprintf(trace_fd,
                        "[TLS_LAZY_FIX] WARNING: tls_array_ptr=0x%08lx my_base=%p — skipped\n",
                        tls_array_ptr, my_base);
                }
            }
        }

        }
        
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[TLS_LAZY] Thread %d allocated structures: base=%p secondary=%p\n",
                    GetTID(), my_base, my_secondary);
        }
    }

    ucontext_t *p = (ucontext_t *)ucntx;
    void * pc = NULL;
    int Locks = 0;
    struct fpsimd_context *fpsimd = NULL;
    sig = signal_from_x64(sig);
    // sig==X64_SIGSEGV || sig==X64_SIGBUS || sig==X64_SIGILL || sig==X64_SIGABRT here!
    int log_minimum = (BOX64ENV(showsegv))?LOG_NONE:((((sig==X64_SIGSEGV) || (sig==X64_SIGILL)) && my_context->is_sigaction[sig])?LOG_DEBUG:LOG_INFO);
    if(signal_jmpbuf_active) {
        signal_jmpbuf_active = 0;
        longjmp(SIG_JMPBUF, 1);
    }
    void* rsp = NULL;
    int tid = GetTID();

    // === MEMORY DUMP FOR DEBUGGING === 
    if(trace_fd >= 0) { 
        uintptr_t rip = (uintptr_t)R_RIP;  
        
        // Dump 64 bytes at the faulting instruction pointer 
        dprintf(trace_fd, "[MEMORY_DUMP] Dumping 64 bytes at Guest RIP=0x%lx:\n", rip);  
        
        // CRITICAL: Check BOTH existence AND read permission before accessing memory 
        int prot = getProtection(rip); 
        if (memExist(rip) && (prot & PROT_READ)) {  
            uint8_t* code = (uint8_t*)rip;  
            for (int i = 0; i < 64; i += 16) {  
                dprintf(trace_fd, "  %08lx: ", rip + i);  
                for (int j = 0; j < 16 && (i+j) < 64; j++) {  
                    // Also check each byte before reading to avoid partial-page issues 
                    if (memExist(rip + i + j) && (getProtection(rip + i + j) & PROT_READ)) { 
                        dprintf(trace_fd, "%02x ", code[i+j]);  
                    } else { 
                        dprintf(trace_fd, "?? "); 
                    } 
                }  
                dprintf(trace_fd, "\n");  
            }  
        } else {  
            if (!memExist(rip)) { 
                dprintf(trace_fd, "  Guest RIP points to UNMAPPED memory\n");  
            } else { 
                dprintf(trace_fd, "  Guest RIP at mapped memory with NO READ permission (prot=0x%x)\n", prot); 
            } 
        }  
        
        // Also check if this is in .data section 
        if (rip >= 0x00CF7000 && rip <= 0x04332000) {  
            dprintf(trace_fd, "[WARNING] Guest RIP is in .data section (0x%lx), expecting runtime-generated code\n", rip);  
        } 
    } 

// === AFTER MEMORY_DUMP (around line 1940) ===
if (trace_fd >= 0) {
    dprintf(trace_fd, "[TRACE_1] After MEMORY_DUMP, before pc assignment | Sig=%d Addr=%p Code=%d\n", 
            x64_sig, addr, info->si_code);
}

#ifdef __aarch64__
    pc = (void*)p->uc_mcontext.pc;
#elif defined __x86_64__
    pc = (void*)p->uc_mcontext.regs[X64_RIP];
#elif defined __powerpc64__
    pc = (void*)p->uc_mcontext.gp_regs[PT_NIP];
#elif defined(LA64)
    pc = (void*)p->uc_mcontext.__pc;
#elif defined(SW64)
    pc = (void*)p->uc_mcontext.sc_pc;
#elif defined(RV64)
    pc = (void*)p->uc_mcontext.__gregs[REG_PC];
#else
    void * pc = NULL;    // unknow arch...
    #warning Unhandled architecture
#endif

// === WINE RESERVED SPACE EXECUTION BLOCK === 
uintptr_t guest_rip = (uintptr_t)R_RIP; 

if (guest_rip >= 0x7f000000 && guest_rip <= 0x82000000) { 
    if (trace_fd >= 0) { 
        dprintf(trace_fd, "\n=== FATAL: EXECUTION IN WINE RESERVED SPACE ===\n"); 
        dprintf(trace_fd, "[WINE_RESERVED_FATAL] RIP: 0x%lx\n", guest_rip); 
        dprintf(trace_fd, "[WINE_RESERVED_FATAL] This indicates catastrophic memory corruption\n"); 
        
        // Dump context 
        dprintf(trace_fd, "\n[WINE_RESERVED_FATAL] Register State:\n"); 
        dprintf(trace_fd, "  RAX=0x%lx RBX=0x%lx RCX=0x%lx RDX=0x%lx\n", 
                (uintptr_t)R_RAX, (uintptr_t)R_RBX, (uintptr_t)R_RCX, (uintptr_t)R_RDX); 
        dprintf(trace_fd, "  RSP=0x%lx RBP=0x%lx\n", (uintptr_t)R_RSP, (uintptr_t)R_RBP); 
        
        // Try to find return address 
        uint32_t* esp = (uint32_t*)(uintptr_t)R_RSP; 
        if (memExist((uintptr_t)esp)) { 
            dprintf(trace_fd, "\n[WINE_RESERVED_FATAL] Stack Analysis:\n"); 
            for (int i = 0; i < 16; i++) { 
                if (memExist((uintptr_t)&esp[i])) { 
                    uint32_t val = esp[i]; 
                    const char* note = ""; 
                    if (val >= 0x00400000 && val < 0x00B00000) note = " [GAME CODE]"; 
                    else if (val >= 0x7bf00000 && val < 0x7c000000) note = " [WINE DLL]"; 
                    dprintf(trace_fd, "  ESP[%2d] = 0x%08x%s\n", i, val, note); 
                } 
            } 
        } 
    } 
    
    // Create trap page with UD2 instructions 
    static void* trap_page = NULL; 
    if (!trap_page) { 
        trap_page = mmap(NULL, 0x1000, PROT_READ | PROT_WRITE | PROT_EXEC, 
                        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0); 
        if (trap_page != MAP_FAILED) { 
            // Fill with UD2 (0x0F 0x0B) - Undefined Instruction 
            uint8_t* p = (uint8_t*)trap_page; 
            for (int i = 0; i < 0x1000; i += 2) { 
                p[i] = 0x0F;     // UD2 opcode byte 1 
                p[i+1] = 0x0B;   // UD2 opcode byte 2 
            } 
            
            if (trace_fd >= 0) { 
                dprintf(trace_fd, "[WINE_RESERVED_FATAL] Created trap page at %p\n", trap_page); 
            } 
        } 
    } 
    
    if (trap_page && trap_page != MAP_FAILED) { 
        R_RIP = (uintptr_t)trap_page; 
        if (trace_fd >= 0) { 
            dprintf(trace_fd, "[WINE_RESERVED_FATAL] Redirected RIP to UD2 trap → will SIGILL immediately\n"); 
            dprintf(trace_fd, "=====================================\n\n"); 
        } 
        
        // Mark as handled to prevent Wine from seeing this 
        mark_exception_handled(fault_addr, (uintptr_t)pc); 
        relockMutex(Locks); 
        return;  // Will crash with clean SIGILL at trap_page 
    } 
    
    // Fallback: if trap page failed, let it crash naturally 
    if (trace_fd >= 0) { 
        dprintf(trace_fd, "[WINE_RESERVED_FATAL] Trap page unavailable - passing to Wine\n"); 
        dprintf(trace_fd, "=================================\n\n"); 
    } 
} 

// === AFTER PC ASSIGNMENT ===
if (trace_fd >= 0) {
    dprintf(trace_fd, "[TRACE_2] After pc assignment | pc=%p\n", pc);
}

// === BEFORE .DATA SECTION CHECK ===
if (trace_fd >= 0) {
    dprintf(trace_fd, "[TRACE_3] Before .DATA check | fault_addr=0x%lx\n", (uintptr_t)addr);
}

    // === .DATA SECTION FORCE-MAP FIX === 
    // Wine's internal memory view shows .data as mapped (0xcf7000-0x4333fff) 
    // but Linux kernel never allocated it. Force allocation on first access. 
    // t6zm.exe .data section: VirtualAddress 0x00CF7000, VirtualSize 0x363A904 
    // Mapped range should be: 0x00CF7000 - 0x04331903 
    
    fault_addr = (uintptr_t)addr;
    if ((sig == X64_SIGSEGV || sig == SIGBUS) &&  
        fault_addr >= 0x00CF7000 && fault_addr <= 0x04332000) { 
         
        // This is in the .data section range 
        // Check if actually mapped at kernel level 
        if (msync((void*)fault_addr, 1, MS_ASYNC) == -1 && errno == ENOMEM) { 
            // NOT MAPPED - force allocation 
            void* page_start = (void*)(fault_addr & ~0xFFFUL); 
            size_t page_size = 4096; 
             
            // Allocate with exact address (MAP_FIXED) 
            void* result = mmap(page_start, page_size, 
                               PROT_READ | PROT_WRITE, 
                               MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 
                               -1, 0); 
             
            if (result != MAP_FAILED) { 
                // Zero-initialize the page 
                memset(result, 0, page_size); 
                 
                if (trace_fd >= 0) { 
                    dprintf(trace_fd, "[DATA_SECTION_FIX] Force-mapped .data page at %p for fault 0x%lx\n", 
                            page_start, fault_addr); 
                } 
                 
                // Mark handled and retry 
                mark_exception_handled(fault_addr, (uintptr_t)pc); 
                relockMutex(Locks); 
                return; 
            } else { 
                if (trace_fd >= 0) { 
                    dprintf(trace_fd, "[DATA_SECTION_FIX] FAILED to map page at %p: %s\n", 
                            page_start, strerror(errno)); 
                } 
            } 
        } else { 
            // Already mapped but still faulting - permission issue? 
            if (trace_fd >= 0) { 
                dprintf(trace_fd, "[DATA_SECTION_FIX] Address 0x%lx is mapped but still faulting (si_code=%d)\n", 
                        fault_addr, info->si_code); 
                 
                // Try changing permissions 
                void* page_start = (void*)(fault_addr & ~0xFFFUL); 
                if (mprotect(page_start, 4096, PROT_READ | PROT_WRITE | PROT_EXEC) == 0) { 
                    dprintf(trace_fd, "[DATA_SECTION_FIX] Changed permissions to RWX for %p\n", page_start); 
                    mark_exception_handled(fault_addr, (uintptr_t)pc); 
                    relockMutex(Locks); 
                    return; 
                } 
            } 
        } 
    } 

// === AFTER .DATA SECTION CHECK (after line 2024) ===
if (trace_fd >= 0) {
    dprintf(trace_fd, "[TRACE_4] After .DATA check, before .RSRC check\n");
}

    // === RESOURCE SECTION FORCE-MAP FIX === 
    // .rsrc section: 0x04336000 - 0x04375fff 
    if ((sig == X64_SIGSEGV || sig == SIGBUS) &&  
        fault_addr >= 0x04336000 && fault_addr <= 0x04376000) { 
         
        if (msync((void*)fault_addr, 1, MS_ASYNC) == -1 && errno == ENOMEM) { 
            void* page_start = (void*)(fault_addr & ~0xFFFUL); 
             
            void* result = mmap(page_start, 4096, 
                               PROT_READ | PROT_WRITE | PROT_EXEC, 
                               MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, 
                               -1, 0); 
             
            if (result != MAP_FAILED) { 
                memset(result, 0, 4096); 
                 
                if (trace_fd >= 0) { 
                    dprintf(trace_fd, "[RSRC_SECTION_FIX] Force-mapped .rsrc page at %p for fault 0x%lx\n", 
                            page_start, fault_addr); 
                } 
                 
                mark_exception_handled(fault_addr, (uintptr_t)pc); 
                relockMutex(Locks); 
                return; 
            } 
        } 
    } 

// === AFTER .RSRC SECTION CHECK (after line 2054) ===
if (trace_fd >= 0) {
    dprintf(trace_fd, "[TRACE_5] After .RSRC check, sig=%d\n", sig);
}

    // --- Start of SIGILL Handling ---
    if (sig == X64_SIGILL) {
        static uintptr_t last_sigill_native_pc = 0;
        static int sigill_consecutive_count = 0;

        #ifdef __aarch64__
        uintptr_t native_pc = (uintptr_t)p->uc_mcontext.pc;
        #elif defined __x86_64__
        uintptr_t native_pc = (uintptr_t)p->uc_mcontext.gregs[X64_RIP];
        #else
        uintptr_t native_pc = 0;
        #endif
        uintptr_t x64_rip = (uintptr_t)R_RIP;

        if (trace_fd >= 0) {
            dprintf(trace_fd, "[SIGILL_HANDLER] SIGILL at Native PC=0x%lx, x64 RIP=0x%lx\n", native_pc, x64_rip);
            int page_ok = memExist(native_pc) && (getProtection(native_pc) & PROT_READ);
            if (page_ok) {
                uint8_t* p_bytes = (uint8_t*)native_pc;
                dprintf(trace_fd, "BYTES[Native PC]: ");
                for (int i = 0; i < 32; i++) {
                    if (memExist(native_pc + i) && (getProtection(native_pc + i) & PROT_READ)) {
                        dprintf(trace_fd, "%02x", p_bytes[i]);
                    } else {
                        dprintf(trace_fd, "??"); // Unreadable byte
                    }
                }
                dprintf(trace_fd, "\n");
            }
            dprintf(trace_fd, "REGS: RIP=0x%lx RSP=0x%lx RAX=0x%lx RBX=0x%lx RCX=0x%lx RDX=0x%lx RSI=0x%lx RDI=0x%lx RBP=0x%lx\n",
                    x64_rip, (uintptr_t)R_RSP, (uintptr_t)R_RAX, (uintptr_t)R_RBX, (uintptr_t)R_RCX, (uintptr_t)R_RDX, (uintptr_t)R_RSI, (uintptr_t)R_RDI, (uintptr_t)R_RBP);
        }
        
        if (last_sigill_native_pc == native_pc) {
            sigill_consecutive_count++;
            #ifdef __aarch64__
            if (sigill_consecutive_count > 5) {
                R_RAX = 1;
                p->uc_mcontext.pc += 4;
                R_RIP = p->uc_mcontext.pc;
                return;
            }
            #endif
        } else {
            last_sigill_native_pc = native_pc;
            sigill_consecutive_count = 1;
        }

        #if defined __x86_64__
        if ((uintptr_t)R_RIP == 0x0047FB6F) {
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[FIX] Targeting 0x5C fault at RIP=0x%lx. Skipping exact instruction length.\n", (uintptr_t)R_RIP);
            }
            R_EAX = 1;
            p->uc_mcontext.gregs[X64_RIP] += 3;
            R_RIP = p->uc_mcontext.gregs[X64_RIP];
            return;
        }
        #endif
        // Fall through without generic byte skipping; universal rescue will handle
    }
    // --- End of SIGILL Handling ---

// === AFTER SIGILL HANDLING (after line 2126) ===
if (trace_fd >= 0) {
    dprintf(trace_fd, "[TRACE_6] After SIGILL handling | sig=%d pc=%p addr=%p\n", sig, pc, addr);
}

    // --- Start of Fake Object Strategy ---
    if (sig == X64_SIGSEGV && (uintptr_t)pc == 0x0047FB6F && (uintptr_t)addr == 0x5C) {
        static void* fake_object_page = NULL;
        if (fake_object_page == NULL) {
            // Allocate a small, read/write memory page for the fake object
            fake_object_page = mmap(NULL, 0x1000, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
            if (fake_object_page == MAP_FAILED) {
                printf_log(LOG_ERROR, "Failed to mmap fake object page for 0x5C fault!\n");
                relockMutex(Locks);
                return; // Let the normal signal handler deal with it if mmap fails
            }
            printf_log(LOG_INFO, "Allocated fake object page at %p for 0x5C fault.\n", fake_object_page);
        }

        // Set RCX to the address of the fake object page
        // The fault is MOV EAX, [ECX + 5Ch], so ECX is the base register that is NULL
        R_RCX = (uintptr_t)fake_object_page;

        // Set RIP back to the faulting instruction to retry it
        #ifdef __aarch64__
        R_RIP = 0x0047FB6F;
        p->uc_mcontext.pc = 0x0047FB6F;
        #elif defined __x86_64__
        R_RIP = 0x0047FB6F;
        p->uc_mcontext.gregs[X64_RIP] = 0x0047FB6F;
        #endif

        printf_log(LOG_INFO, "Handled 0x5C fault at PC=0x0047FB6F. RCX set to %p, retrying instruction.\n", fake_object_page);
        return;
    }
    // --- End of Fake Object Strategy ---

// === AFTER FAKE OBJECT STRATEGY (after line 2158) ===
if (trace_fd >= 0) {
    dprintf(trace_fd, "[TRACE_7] After Fake Object strategy\n");
}

#if defined(__aarch64__)
    // find fpsimd struct
    {
        struct _aarch64_ctx * ff = (struct _aarch64_ctx*)p->uc_mcontext.__reserved;
        while (ff->magic && !fpsimd) {
            if(ff->magic==FPSIMD_MAGIC)
                fpsimd = (struct fpsimd_context*)ff;
            else
                ff = (struct _aarch64_ctx*)((uintptr_t)ff + ff->size);
        }
    }
#elif defined(__x86_64__)
    pc = (void*)p->uc_mcontext.regs[X64_RIP];
#elif defined(__powerpc64__)
    pc = (void*)p->uc_mcontext.gp_regs[PT_NIP];
#elif defined(LA64)
    pc = (void*)p->uc_mcontext.__pc;
#elif defined(SW64)
    pc = (void*)p->uc_mcontext.sc_pc;
#elif defined(RV64)
    pc = (void*)p->uc_mcontext.__gregs[REG_PC];
#else
    pc = NULL;    // unknow arch...
    #warning Unhandled architecture
#endif
    dynablock_t* db = NULL;
    int db_searched = 0;
    uintptr_t x64pc = (uintptr_t)-1;
    x64pc = R_RIP;
    if((sig==X64_SIGBUS) && (addr!=pc) || ((sig==X64_SIGSEGV)) && emu->segs[_CS]==0x23 && ((uintptr_t)addr>>32)==0xffffffff) {
        db = FindDynablockFromNativeAddress(pc);
        if(db)
            x64pc = getX64Address(db, (uintptr_t)pc);
        db_searched = 1;
        int fixed = 0;
        if((fixed=sigbus_specialcases(info, ucntx, pc, fpsimd, db, x64pc, emu->segs[_CS]==0x23))) {
            // special case fixed, restore everything and just continues
            if (BOX64ENV(log)>=LOG_DEBUG || BOX64ENV(showsegv)) {
                static void*  old_pc[2] = {0};
                static int old_pc_i = 0;
                if(old_pc[0]!=pc && old_pc[1]!=pc) {
                    old_pc[old_pc_i++] = pc;
                    if(old_pc_i==2)
                        old_pc_i = 0;
                    uint8_t* x64 = (uint8_t*)x64pc;
                    if(db)
                        printf_log(LOG_INFO, "Special unaligned case fixed @%p, opcode=%08x (addr=%p, db=%p, x64pc=%p[%02hhX %02hhX %02hhX %02hhX %02hhX])\n", pc, *(uint32_t*)pc, addr, db, x64pc, x64[0], x64[1], x64[2], x64[3], x64[4], x64[5]);
                    else
                        printf_log(LOG_INFO, "Special unaligned case fixed @%p, opcode=%08x (addr=%p)\n", pc, *(uint32_t*)pc, addr);
                }
            }
            return;
        }
    }
    #ifdef ARCH_NOP
    if(sig==X64_SIGILL) {
        if(!db_searched) {
            db = FindDynablockFromNativeAddress(pc);
            if(db)
                x64pc = getX64Address(db, (uintptr_t)pc);   // this will be incorect in the case of the callret!
            db_searched = 1;
        }
        if(db && db->callret_size) {
            int is_callrets = 0;
            int type_callret = 0;
            for(int i=0; i<db->callret_size && !is_callrets; ++i)
                if(pc==(db->block+db->callrets[i].offs)) {
                    is_callrets = 1;
                    type_callret = db->callrets[i].type;
                }
            if(is_callrets) {
                if(!type_callret) {
                    // adjust x64pc for "ret" type
                    x64pc = CONTEXT_REG(p, xRIP);
                }
                // check if block is still valid
                int is_hotpage = checkInHotPage(x64pc);
                uint32_t hash = (db->gone || is_hotpage)?0:X31_hash_code(db->x64_addr, db->x64_size);
                if(!db->gone && !is_hotpage && hash==db->hash) {
                    dynarec_log(LOG_INFO, "Dynablock (%p, x64addr=%p, always_test=%d) is clean, %s continuing at %p (%p)!\n", db, db->x64_addr, db->always_test, type_callret?"self-loop":"ret from callret", (void*)x64pc, (void*)addr);
                    // it's good! go next opcode
                    CONTEXT_PC(p)+=4;
                    if(db->always_test)
                        protectDB((uintptr_t)db->x64_addr, 1);
                    else {
                        if(db->callret_size) {
                            // mark all callrets to NOP
                            for(int i=0; i<db->callret_size; ++i)
                                *(uint32_t*)(db->block+db->callrets[i].offs) = ARCH_NOP;
                            #ifdef DYNAREC
                            ClearCache(db->block, db->size);
                            #endif
                        }
                        protectDBJumpTable((uintptr_t)db->x64_addr, db->x64_size, db->block, db->jmpnext);
                    }
                    return;
                } else {
                    // dynablock got dirty! need to get out of it!!!
                    if(emu->jmpbuf) {
                        copyUCTXreg2Emu(emu, p, x64pc);
                        // only copy as it's a return address, so there is just the "epilog" to mimic here on "ret" type. "loop" type need everything
                        if(type_callret) {
                            adjustregs(emu, pc);
                            if(db && db->arch_size)
                                ARCH_ADJUST(db, emu, p, x64pc);
                            
                        }
                        dynarec_log(LOG_INFO, "Dynablock (%p, x64addr=%p) %s, getting out at %s %p (%p)!\n", db, db->x64_addr, is_hotpage?"in HotPage":"dirty", getAddrFunctionName(R_RIP), (void*)R_RIP, type_callret?"self-loop":"ret from callret", (void*)addr);
                        emu->test.clean = 0;
                        // use "3" to regen a dynablock at current pc (else it will first do an interp run)
                        #ifdef ANDROID
                        siglongjmp(*(JUMPBUFF*)emu->jmpbuf, 3);
                        #else
                        siglongjmp(emu->jmpbuf, 3);
                        #endif
                    }
                    dynarec_log(LOG_INFO, "Warning, Dirty %s (%p for db %p/%p) detected, but jmpbuffer not ready!\n", type_callret?"self-loop":"ret from callret", (void*)addr, db, (void*)db->x64_addr);
                }
            }
        }
    }
    #endif

    uint32_t prot = getProtection((uintptr_t)addr);
    #ifdef BAD_SIGNAL
    // try to see if the si_code makes sense
    // the RK3588 tend to need a special Kernel that seems to have a weird behaviour sometimes
    if((sig==X64_SIGSEGV) && (addr) && (info->si_code == 1) && getMmapped((uintptr_t)addr)) {
        printf_log(LOG_DEBUG, "Workaround for suspicious si_code for %p / prot=0x%hhx\n", addr, prot);
        info->si_code = 2;
    }
    #endif
#ifdef RV64
    if((sig==X64_SIGSEGV) && (addr==pc) && (info->si_code==2) && (prot==(PROT_READ|PROT_WRITE|PROT_EXEC))) {
        if(!db_searched) {
            db = FindDynablockFromNativeAddress(pc);
            if(db)
                x64pc = getX64Address(db, (uintptr_t)pc);
            db_searched = 1;
        }
        int fixed = 0;
        if((fixed = sigbus_specialcases(info, ucntx, pc, fpsimd, db, x64pc, emu->segs[_CS]==0x23))) {
            // special case fixed, restore everything and just continues
            if (BOX64ENV(log) >= LOG_DEBUG || BOX64ENV(showsegv)) {
                static void*  old_pc[2] = {0};
                static int old_pc_i = 0;
                if(old_pc[0]!=pc && old_pc[1]!=pc) {
                    old_pc[old_pc_i++] = pc;
                    if(old_pc_i==2)
                        old_pc_i = 0;
                    printf_log(LOG_NONE, "Special unalinged cased fixed @%p, opcode=%08x (addr=%p)\n", pc, *(uint32_t *)pc, addr);
                }
            }
            relockMutex(Locks);
            return;
        }
    }
#endif
// Macro to safely resume execution after altering CPU state (R_RIP, registers, etc.)
// This forces a siglongjmp which tells the emulator to break out of the JIT block
// and fetch the instruction at the new R_RIP.
#define RESUME_EXECUTION_INTERP() \
    do { \
        if(emu && emu->jmpbuf) { \
            dprintf(trace_fd, "[RESUME_EXECUTION_INTERP] About to siglongjmp, target jmpbuf=%p, current R_RIP=0x%lx\n", (void*)emu->jmpbuf, R_RIP); \
            relockMutex(Locks); \
            siglongjmp(emu->jmpbuf, 1); \
        } else { \
            dprintf(trace_fd, "[RESUME_EXECUTION_INTERP] No jmpbuf available, returning to signal handler emu = %p & emu->jmpbuf = %p\n", (void*)emu, emu ? (void*)emu->jmpbuf : NULL); \
            relockMutex(Locks); \
            return; \
        } \
    } while(0)

// Wine wow64 RtlDecodePointer mismatch: route to real VEH at 0x0099da00
if ((sig == X64_SIGSEGV || sig == X64_SIGBUS) && (uint32_t)R_RIP == 0xEFFF86A5) {
    if (trace_fd >= 0) {
        dprintf(trace_fd, "[VEH_FIX] Broken RtlDecodePointer (0xEFFF86A5) -> handler 0x0099da00\n");
    }
    R_RIP = 0x0099da00;
    
#ifdef DYNAREC
    CONTEXT_PC(p) = 0x0099da00;
#endif
    mark_exception_handled(fault_addr, (uintptr_t)pc);
    RESUME_EXECUTION_INTERP();
}

// === BEFORE SIGNAL_ENTRY ===
if (trace_fd >= 0) {
    dprintf(trace_fd, "[TRACE_8] About to enter SIGNAL_ENTRY logging\n");
}

// PRE-PATCH DEBUG LOGGING
if(trace_fd >= 0) {
    dprintf(trace_fd, "[SIGNAL_ENTRY] Sig=%d Addr=%p Code=%d PC=%p\n", sig, addr, info->si_code, (void*)pc);
    if(!addr) dprintf(trace_fd, "[SIGNAL_ENTRY] WARNING: Addr is NULL (Universal Patch might skip)\n");
}

// === DIAGNOSTIC: Inspect what called 0x49d1e40 ===
if (guest_rip == 0x49d1e40 && trace_fd >= 0) {
    dprintf(trace_fd, "\n=== FASTFILE FUNCTION TABLE DIAGNOSTIC ===\n");
    
    // Get the return address (who called this invalid function?)
    uintptr_t* stack = (uintptr_t*)(uintptr_t)R_ESP;
    if (stack && memExist((uintptr_t)stack)) {
        uintptr_t return_addr = stack[0];
        dprintf(trace_fd, "[FASTFILE] Return address: 0x%08lx\n", return_addr);
        
        // Is the caller in the DEFRAG region?
        if (return_addr >= 0x04400000 && return_addr <= 0x04B00000) {
            dprintf(trace_fd, "[FASTFILE] Caller is in DEFRAG region (decrypted code)\n");
            
            // Dump memory around the call site
            dprintf(trace_fd, "[FASTFILE] Dumping 64 bytes at caller:\n");
            uint8_t* code = (uint8_t*)(return_addr - 16);
            if (memExist((uintptr_t)code)) {
                dprintf(trace_fd, "  ");
                for (int i = 0; i < 64; i++) {
                    dprintf(trace_fd, "%02x ", code[i]);
                    if ((i + 1) % 16 == 0) dprintf(trace_fd, "\n  ");
                }
                dprintf(trace_fd, "\n");
            }
        }
    }
    
    // Check if there's a function pointer table in the data structures
    if (memExist(R_EBX)) {
        uint32_t* table_base = (uint32_t*)(uintptr_t)R_EBX;
        dprintf(trace_fd, "[FASTFILE] EBX points to structure at 0x%08x:\n", R_EBX);
        for (int i = 0; i < 24; i++) {
            if (memExist((uintptr_t)(table_base + i))) {
                dprintf(trace_fd, "[FASTFILE]   +0x%02x: 0x%08x\n", i*4, table_base[i]);
            }
        }
    }
    
    dprintf(trace_fd, "==========================================\n\n");
}

// === FUNC_SKIP_49D1E40 ===
// Skip problematic function at 0x49d1e40 causing NULL pointer dereferences
if (guest_rip >= 0x49d1e40 && guest_rip <= 0x49d1e50) {
    uint32_t* esp = (uint32_t*)(uintptr_t)R_RSP;
    
    // ===== DIAGNOSTIC: WHO IS CALLING THIS? =====
    if (trace_fd >= 0) {
        dprintf(trace_fd, "\n[DIAGNOSTIC_49D1E40] ==== FUNCTION POINTER CRASH ====\n");
        dprintf(trace_fd, "[DIAGNOSTIC_49D1E40] RIP attempting to execute: 0x%08lx\n", guest_rip);
        
        // Dump stack to find caller
        if (memExist((uintptr_t)esp)) {
            dprintf(trace_fd, "[DIAGNOSTIC_49D1E40] Stack dump (return addresses):\n");
            for (int i = 0; i < 16; i++) {
                if (memExist((uintptr_t)(esp + i))) {
                    uint32_t stack_val = esp[i];
                    if (stack_val >= 0x400000 && stack_val < 0xB00000) {
                        dprintf(trace_fd, "  [ESP+0x%02x] = 0x%08x <- CALLER in .text\n", i*4, stack_val);
                    }
                }
            }
        }
        
        // Check registers that might hold the function pointer
        dprintf(trace_fd, "[DIAGNOSTIC_49D1E40] Register state:\n");
        dprintf(trace_fd, "  EAX = 0x%08lx\n", (uintptr_t)R_RAX);
        dprintf(trace_fd, "  ECX = 0x%08lx\n", (uintptr_t)R_RCX);
        dprintf(trace_fd, "  EDX = 0x%08lx\n", (uintptr_t)R_RDX);
        dprintf(trace_fd, "  EBX = 0x%08lx\n", (uintptr_t)R_RBX);
        dprintf(trace_fd, "  ESI = 0x%08lx\n", (uintptr_t)R_RSI);
        dprintf(trace_fd, "  EDI = 0x%08lx\n", (uintptr_t)R_RDI);
        dprintf(trace_fd, "===================================\n\n");
    }
    
    // Try to return gracefully
    if(memExist((uintptr_t)esp)) {
        R_RIP = esp[0];  // Return from function
        R_RSP += 4;      // Pop return address
        // Return non-zero to Wine's BaseThreadInitThunk so it does not
        // retry the call. EAX=1 signals "completed" in most Windows
        // thread wrapper conventions.
        emu->regs[_AX].dword[0] = 1;
        R_RAX = 1;
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[FUNC_SKIP_49D1E40] Returning EAX=1 to prevent Wine loop retry\n");
        }
    } else {
        R_RIP += 5;      // Fallback: just skip instruction
        if (trace_fd >= 0) {
             dprintf(trace_fd, "[FUNC_SKIP_49D1E40] Skipped problematic function at 0x%lx becuase memExist((uintptr_t)esp failed\n", guest_rip);
        }
    }
    
    RESUME_EXECUTION_INTERP();
}
// === END FUNC_SKIP ===

// 1. Prevents reading corrupt _tls_index from uninitialized memory 
// 2. Breaks infinite loop by manually executing instructions and advancing RIP 

current_rip = (uintptr_t)R_RIP; 
// Trigger on ANY crash with TLS-related fault address in the TLS access function range 
uintptr_t fault = (uintptr_t)info->si_addr; 
int is_tls_fault = (fault == 0x5c || fault == 0x58 || fault == 0x2c); 
int in_tls_function = (current_rip >= 0x47fb60 && current_rip <= 0x47fb9b); // FUN_0047fb60 range 
int in_init_function = (current_rip >= 0x4cd220 && current_rip <= 0x4cd2a2); // FUN_004cd220 range 
 
if ((is_tls_fault && (in_tls_function || in_init_function)) ||  
    current_rip == 0x47fb6f || current_rip == 0x4cd229 || current_rip == 0x733400 || current_rip == 0x733609 || 
    current_rip == 0x73360c) {  // Also handle next instruction after 0x733609
    init_fake_tls();  // Ensure base TLS structure exists 
    
    // Log successful progression past 0x733609
    if (current_rip == 0x73360c) {
        static int success_count = 0;
        success_count++;
        if (trace_fd >= 0 && success_count <= 5) {
            dprintf(trace_fd, "[SUCCESS] Reached 0x73360c (after 0x733609) - progression confirmed! Count=%d\n", 
                    success_count);
        }
    } 
    
    // BEFORE the read at 0x733600 (function entry, not crash point)
    if (current_rip == 0x733600 && !dat_initialized) {
        dat_initialized = 1;
        
        // Allocate object with vtable structure 
        uint32_t* obj = (uint32_t*)vtable_object; 
        
        // Safe RET instruction to use for all vtable entries 
        uint32_t safe_ret = 0x006e2b1a;  // Known safe RET from bootstrap 
        
        obj[0x00/4] = safe_ret;  // +0x00 
        obj[0x04/4] = safe_ret;  // +0x04
        obj[0x08/4] = safe_ret;  // +0x08 - Critical for crash at 0x733609
        obj[0x0C/4] = safe_ret;  // +0x0C 
        obj[0x18/4] = safe_ret;  // +0x18 
        obj[0x1C/4] = safe_ret;  // +0x1C - THIS IS THE CRITICAL ONE 
        obj[0x20/4] = safe_ret;  // +0x20 
        obj[0x24/4] = safe_ret;  // +0x24 
        obj[0x30/4] = safe_ret;  // +0x30 
        obj[0x34/4] = safe_ret;  // +0x34 
        obj[0x38/4] = safe_ret;  // +0x38 
        
        // Write pointer to DAT_0357927c 
        *(uint32_t*)0x0357927c = (uint32_t)(uintptr_t)obj; 
        
        if (trace_fd >= 0) {
             dprintf(trace_fd, "[DAT_FIX] Initialized DAT_0357927c = %p\n", obj); 
         }

         // Mark exception handled and return to retry the read instruction
         mark_exception_handled(fault, (uintptr_t)pc);
         relockMutex(Locks);
         return;
     }
     
     // Handle crash at 0x733609: MOV EAX,[EAX+8]
     // Strategy: SKIP the instruction and manually set EAX
     // Wine exception handlers return 1 (CONTINUE_SEARCH), which conflicts with retry
     if (current_rip == 0x733609) {
         static int fix_count_733609 = 0;
         fix_count_733609++;
         
         if (!dat_initialized) {
             dat_initialized = 1;
             
             // Initialize vtable object
             uint32_t* obj = (uint32_t*)vtable_object;
             uint32_t safe_ret = 0x006e2b1a;
             
             obj[0x00/4] = safe_ret;
             obj[0x04/4] = safe_ret;
             obj[0x08/4] = safe_ret;  // Critical - accessed by this instruction
             obj[0x0C/4] = safe_ret;
             obj[0x18/4] = safe_ret;
             obj[0x1C/4] = safe_ret;
             obj[0x20/4] = safe_ret;
             obj[0x24/4] = safe_ret;
             obj[0x30/4] = safe_ret;
             obj[0x34/4] = safe_ret;
             obj[0x38/4] = safe_ret;
             
             // Write to DAT_0357927c
             if (memExist(0x0357927c)) {
                 *(uint32_t*)0x0357927c = (uint32_t)(uintptr_t)obj;
             }
             
             if (trace_fd >= 0) {
                 dprintf(trace_fd, "[DAT_FIX_0x733609] Initialized DAT_0357927c = %p\n", obj);
             }
         }
         
         // CRITICAL: Instead of retrying, SKIP the instruction and set result manually
         // Instruction: MOV EAX,[EAX+8] - reads from [EAX+8] and stores in EAX
         // Result should be vtable_object[8/4] = 0x006e2b1a (safe RET)
         uint32_t* obj = (uint32_t*)vtable_object;
         uint32_t result = obj[0x08/4];  // Read what the instruction would read
         
         // Get current RAX value before fix
         uint32_t old_rax = (uint32_t)R_RAX;
         
         // Set EAX to the result of the instruction
         emu->regs[_AX].dword[0] = result;
         R_RAX = result;
         
         // SKIP the instruction (MOV EAX,[EAX+8] is 3 bytes: 8B 40 08)
         emu->ip.dword[0] = current_rip + 3;
         R_RIP = current_rip + 3;
         
         if (trace_fd >= 0) {
             dprintf(trace_fd, "[DAT_FIX_0x733609 #%d] SKIP instruction | Fault=0x%lx | Old RAX=0x%08x | Set EAX=0x%08x | RIP: 0x%x -> 0x%x\n", 
                     fix_count_733609, fault, old_rax, result, (uint32_t)current_rip, (uint32_t)current_rip + 3);
             
             // Log if we're stuck in a loop
             if (fix_count_733609 > 10 && fix_count_733609 % 100 == 0) {
                 dprintf(trace_fd, "[DAT_FIX_0x733609] WARNING: Fixed %d times - possible infinite loop!\n", 
                         fix_count_733609);
             }
         }
         
         // Use RESUME_EXECUTION_INTERP() macro instead of mark_exception_handled
         RESUME_EXECUTION_INTERP();
     }

    // Run bootstrap once 
    static int bootstrap_done = 0; 
    if (!bootstrap_done) { 
        bootstrap_done = 1; 

        // Initialise master structure
        uintptr_t base = (uintptr_t)&engine_bootstrap[0]; 
        if (memExist(0x01279fcc)) *(uint32_t*)(0x01279fcc) = (uint32_t)base;

        uintptr_t ptr1 = (uintptr_t)(base + 0x1000); 
        uintptr_t ptr2 = (uintptr_t)(base + 0x2000); 

        *(uint32_t*)(base + 0x5da8) = (uint32_t)ptr1; 
        *(uint32_t*)(ptr1 + 0x1220) = (uint32_t)ptr2; 
        *(uint32_t*)(ptr2) = 7; 
        *(uint32_t*)(ptr2 + 4) = 0xFFFFFFFF; 

        uintptr_t vtable_ptr = (uintptr_t)(base + 0x3000); 
        uintptr_t vtable_base = (uintptr_t)(base + 0x3100); 
        *(uint32_t*)(base + 0x10) = (uint32_t)vtable_ptr; 
        *(uint32_t*)(vtable_ptr) = (uint32_t)vtable_base; 
        *(uint32_t*)(vtable_base + 4) = 0x006e2b1a; // safe RET 

        if (memExist(0x017913f4)) *(uint32_t*)(0x017913f4) = 7; 

        // Allocate heap for DAT_017913d0 
        void* custom_heap = mmap(NULL, 64 * 1024 * 1024, 
                                  PROT_READ | PROT_WRITE | PROT_EXEC, 
                                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0); 
        if (custom_heap != MAP_FAILED && memExist(0x017913d0)) { 
            *(uint32_t*)0x017913d0 = (uint32_t)(uintptr_t)custom_heap; 
            if (trace_fd >= 0) dprintf(trace_fd, "[BOOTSTRAP] Set DAT_017913d0 = %p\n", custom_heap); 
        } 

        // Allocate context array (DAT_0280a410) 
        void* ctx_array = mmap(NULL, 0x1000, PROT_READ|PROT_WRITE, 
                                MAP_PRIVATE|MAP_ANONYMOUS, -1, 0); 
        if (ctx_array != MAP_FAILED && memExist(0x0280a410)) { 
            *(uint32_t*)0x0280a410 = (uint32_t)(uintptr_t)ctx_array; 
            if (trace_fd >= 0) dprintf(trace_fd, "[BOOTSTRAP] Set DAT_0280a410 = %p\n", ctx_array); 
        } 

        // Allocate function table (DAT_0280a6a8) 
        void* func_table = mmap(NULL, 0x1000, PROT_READ|PROT_WRITE, 
                                 MAP_PRIVATE|MAP_ANONYMOUS, -1, 0); 
        if (func_table != MAP_FAILED && memExist(0x0280a6a8)) { 
            *(uint32_t*)0x0280a6a8 = (uint32_t)(uintptr_t)func_table; 
            if (trace_fd >= 0) dprintf(trace_fd, "[BOOTSTRAP] Set DAT_0280a6a8 = %p\n", func_table); 
        } 

        // Initialise master structure with sentinels and sizes 
        if (base) { 
            uint32_t* master = (uint32_t*)base; 

            // Sentinels (fields that should be -1) 
            uint32_t sentinels[] = { 
                0x100, 0x110, 0x118, 0x120, 0x128, 0x130, 0x138, 0x140, 0x148, 0x150, 
                0x158, 0x160, 0x188, 0x21c, 0x240, 0x2e8, 0x2ec, 0x2f0, 0x2f4, 0x2f8, 
                0x2fc, 0x304, 0x308, 0x30c, 0x3e0, 0x3e8, 0x3f4, 0x3f8 
            }; 
            for (int i = 0; i < (int)(sizeof(sentinels)/sizeof(sentinels[0])); i++) { 
                master[sentinels[i]/4] = 0xFFFFFFFF; 
            } 

            // Size fields (set to 1 as minimal safe value) 
            uint32_t sizes[] = {0x8, 0xc, 0x10c, 0x114, 0x11c, 0x124, 0x12c}; 
            for (int i = 0; i < (int)(sizeof(sizes)/sizeof(sizes[0])); i++) { 
                master[sizes[i]/4] = 1; 
            } 

            // Dummy pointers 
            master[0x10/4] = (uint32_t)(base + 0x4000); 
            master[0x14/4] = (uint32_t)(base + 0x4100); 

            // Set _DAT_0127a440 = DAT_01279fcc + 0x174 and its sentinels 
            if (memExist(0x0127a440)) { 
                uint32_t a440_base = (uint32_t)(base + 0x174); 
                *(uint32_t*)0x0127a440 = a440_base; 
                if (memExist(a440_base)) { 
                    uint32_t* a440_ptr = (uint32_t*)(uintptr_t)a440_base; 
                    a440_ptr[1] = 0xFFFFFFFF; 
                    a440_ptr[2] = 0xFFFFFFFF; 
                    a440_ptr[3] = 0xFFFFFFFF; 
                } 
            } 

            if (trace_fd >= 0) { 
                dprintf(trace_fd, "[FIX] Bootstrap (v5) executed from TLS_FIX. Master structure initialised.\n"); 
            } 
        } 
    } 
    
    uint8_t* tls_block = (uint8_t*)pthread_getspecific(tls_block_key); 
    if (!tls_block) { 
        init_fake_tls(); 
        tls_block = (uint8_t*)pthread_getspecific(tls_block_key); 
    } 
    uintptr_t tls_base = (uintptr_t)tls_block; 
    
    // t6zm.exe .data section: (zeroing skipped)
    //   - Disk size:    0x302200 (3.15 MB) - initialized data from PE file 
    //   - Virtual size: 0x363a904 (57 MB)  - total allocation 
    //   - Uninitialized: 54 MB that should be zero but contains garbage 
    // 
    // Addresses like DAT_0357927c (offset 0x0288227c) are uninitialized 
    
    // === WINE .DATA SECTION BUG - FORCE ZERO INITIALIZATION === 
    // Wine maps .data as file-backed from PE file. 
    // The uninitialized portion should be zero but contains garbage from the file. 
    // Solution: Force copy-on-write by writing to every page, then zero it. 
        
    static int data_section_fixed = 0;  
    if (!data_section_fixed && memExist(0x00CF7000)) {  
        uintptr_t data_start = 0x00CF7000;  
        size_t disk_size = 0x302200;      // Size on disk (initialized from file) 
        size_t virt_size = 0x363a904;     // Total virtual size 
        
        // Calculate page-aligned boundaries 
        size_t page_size = 4096; 
        uintptr_t zero_start_unaligned = data_start + disk_size;  // 0x00FF9200 
        uintptr_t zero_start = (zero_start_unaligned / page_size) * page_size;  // Round down to page 
        uintptr_t zero_end = data_start + virt_size; 
        size_t zero_size = zero_end - zero_start; 
        
        // Ensure the region is writable 
        mprotect((void*)zero_start, zero_size, PROT_READ | PROT_WRITE | PROT_EXEC); 
        
        // NEW DIAGNOSTIC: Check the "Security/Jump" table area before we wipe it
        // Addresses taken from Ghidra analysis of FUN_0060ecd0 callers
        uint32_t jump_key_1 = memExist(0x01261b24) ? *(uint32_t*)0x01261b24 : 0;
        uint32_t jump_key_2 = memExist(0x01261b2c) ? *(uint32_t*)0x01261b2c : 0;
        dprintf(trace_fd, "[DIAGNOSTIC] Jump Keys BEFORE zero-fill pe: K1=0x%08x, K2=0x%08x\n", jump_key_1, jump_key_2);

        // Force copy-on-write for ALL pages by writing to the first byte of each page 
        // This breaks the file-backed mapping and creates private anonymous pages 
        for (uintptr_t addr = zero_start; addr < zero_end; addr += page_size) { 
            volatile uint8_t* page = (volatile uint8_t*)addr; 
            *page = 0;  // Force page fault and copy-on-write 
        } 
        
        // DIAGNOSTIC: Check DAT_00cff6bc BEFORE zero-fill
        uint32_t cff6bc_before = 0;
        if (memExist(0x00cff6bc)) {
            cff6bc_before = *(uint32_t*)0x00cff6bc;
            dprintf(trace_fd, "[DATA_FIX] DAT_00cff6bc BEFORE zero-fill = 0x%08x\n", cff6bc_before);
        }

        // Capture the six CreateEventA handles from FUN_006b2d00 before they are wiped.
        uint32_t evt_0280a3ec = memExist(0x0280a3ec) ? *(uint32_t*)0x0280a3ec : 0;
        uint32_t evt_0280a5c0 = memExist(0x0280a5c0) ? *(uint32_t*)0x0280a5c0 : 0;
        uint32_t evt_0280a694 = memExist(0x0280a694) ? *(uint32_t*)0x0280a694 : 0;
        uint32_t evt_0280a3f8 = memExist(0x0280a3f8) ? *(uint32_t*)0x0280a3f8 : 0;
        uint32_t evt_0280a5c4 = memExist(0x0280a5c4) ? *(uint32_t*)0x0280a5c4 : 0;
        uint32_t evt_0280a6a0 = memExist(0x0280a6a0) ? *(uint32_t*)0x0280a6a0 : 0;
        dprintf(trace_fd, "[DATA_FIX] Captured event handles: E3ec=0x%08x E5c0=0x%08x E694=0x%08x E3f8=0x%08x E5c4=0x%08x E6a0=0x%08x\n",
                evt_0280a3ec, evt_0280a5c0, evt_0280a694, evt_0280a3f8, evt_0280a5c4, evt_0280a6a0);
                
        // Save ONLY pool base pointer (slots are initialized later)
        uint32_t saved_pool_base = 0;
        if (memExist(0x01259a28)) {
            saved_pool_base = *(uint32_t*)0x01259a28;
            dprintf(trace_fd, "[DATA_FIX] Saved pool_base: 0x%08x\n", saved_pool_base);
        }

        // Log slot monitoring
        if (memExist(0x01259b00)) {
            uint32_t s0_base_pre = *(uint32_t*)(0x01259b00 + 0x8020);
            uint32_t s0_size_pre = *(uint32_t*)(0x01259b00 + 0x8024);
            dprintf(trace_fd, "[DATA_FIX_TIMING] Slot[0] BEFORE zeroing: Base=0x%08x, Size=0x%08x\n", 
                    s0_base_pre, s0_size_pre);
            dprintf(trace_fd, "[DATA_FIX_VERIFY] Captured real slot0_buffer_start=0x%08x vs guessed formula (pool_base+0x10) would be 0x%08x\n",
                    s0_base_pre, saved_pool_base + 0x10);
        }

        // Log pool state BEFORE zeroing
        if (memExist(0x01259a28)) {
            uint32_t pool_base_before = *(uint32_t*)0x01259a28;
            uint32_t slot_counter_before = *(uint32_t*)0x01259a34;
            dprintf(trace_fd, "[DATA_FIX_TIMING] Pool state BEFORE zeroing:\n");
            dprintf(trace_fd, "[DATA_FIX_TIMING]   DAT_01259a28 = 0x%08x\n", pool_base_before);
            dprintf(trace_fd, "[DATA_FIX_TIMING]   DAT_01259a34 = 0x%08x\n", slot_counter_before);
            if (pool_base_before != 0) {
                dprintf(trace_fd, "[DATA_FIX_WARNING] *** POOL HAS SOME PARTIAL INITIALIZATION ***\n");
            }
        }
        
        // Zero entire .data section
        // memset((void*)zero_start, 0, zero_size);
        // dprintf(trace_fd, "[DATA_FIX] Zeroed entire .data: 0x%lx - 0x%lx (%zu MB)\n",
        //        zero_start, zero_end, zero_size / 1024 / 1024);

        // Re-initialize Bootstrap structures
        *(uint32_t*)0x017913d0 = 0x30280000;
        *(uint32_t*)0x0280a410 = 0x34280000;
        *(uint32_t*)0x0280a6a8 = 0x34290000;

        // Restore pool base AND properly initialize slot[0]
        if (saved_pool_base != 0) {
            *(uint32_t*)0x01259a28 = saved_pool_base;

            // Restore ctrl block[0]'s pool_base_copy field at offset +8 from ctrl[0] base.
            // ctrl blocks are at DAT_01259a3c, layout: 5 DWORDs per slot (0x14 bytes each).
            // ctrl[0][2] (pool_base_copy) at 0x01259a3c + 8 = 0x01259a44 must equal
            // pool_base so the game's size calculation produces a valid byte count.
            if (memExist(0x01259a44)) {
                *(uint32_t*)0x01259a44 = saved_pool_base;
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[DATA_FIX] Restored ctrl[0].pool_base_copy at 0x01259a44 = 0x%08x\n",
                            saved_pool_base);
                }
            }
            
            // Set slot configuration
            *(uint32_t*)0x00cff6bc = 0x00000004;
            *(uint32_t*)0x01259a38 = 0x00000004;
            
            // Initialize slot[0] with correct values
            // buf_start should be pool_base + small offset (observed: pool_base + 16 bytes)
            uint32_t slot0_buffer_start = saved_pool_base + 0x10;  // pool_base + 16 bytes
            uint32_t slot0_buffer_size = 0x80000;  // 512 KB (standard pool size)
            
            *(uint32_t*)(0x01259b00 + 0x8020) = slot0_buffer_start;  // buf_start
            *(uint32_t*)(0x01259b00 + 0x8024) = slot0_buffer_size;   // size
            *(uint32_t*)(0x01259b00 + 0x8028) = 0;                    // read_pos
            *(uint32_t*)(0x01259b00 + 0x802c) = 0;                    // write_pos
            *(uint8_t*)(0x01259b00 + 0x8030) = 1;                     // in_use = true
            
            dprintf(trace_fd, "[DATA_FIX] Initialized slot[0]: base=0x%08x size=0x%08x\n", 
                    slot0_buffer_start, slot0_buffer_size);
            
            dprintf(trace_fd, "[DATA_FIX] Restored pool_base: 0x%08x\n", saved_pool_base);
            dprintf(trace_fd, "[DATA_FIX] Set DAT_00cff6bc = 4 (slot count)\n");
            dprintf(trace_fd, "[DATA_FIX] Set DAT_01259a38 = 4 (slot total)\n");

            // CRITICAL CHECK: Did the jump keys survive or were they in the wipe zone?
            uint32_t jump_key_1_post = memExist(0x01261b24) ? *(uint32_t*)0x01261b24 : 0;
            if (jump_key_1 != 0 && jump_key_1_post == 0) {
                dprintf(trace_fd, "[DATA_FIX_WARNING] Jump Keys were WIPED! This will cause the 0x49d1e40 crash.\n");
                // Temporary restoration test
                *(uint32_t*)0x01261b24 = jump_key_1;
                *(uint32_t*)0x01261b2c = jump_key_2;
                dprintf(trace_fd, "[DATA_FIX] Attempted restoration of Jump Keys.\n");
            }

        }

        dprintf(trace_fd, "[DATA_FIX] Re-initialized Bootstrap after zeroing\n");
        dprintf(trace_fd, "[DATA_FIX]   DAT_017913d0 = 0x30280000\n");
        dprintf(trace_fd, "[DATA_FIX]   DAT_0280a410 = 0x34280000\n");
        dprintf(trace_fd, "[DATA_FIX]   DAT_0280a6a8 = 0x34290000\n");

        if (memExist(0x01259b00)) {
            uint32_t s0_base_post = *(uint32_t*)(0x01259b00 + 0x8020);
            uint32_t s0_size_post = *(uint32_t*)(0x01259b00 + 0x8024);
            dprintf(trace_fd, "[DATA_FIX_TIMING] Slot[0] AFTER restoration: Base=0x%08x, Size=0x%08x\n", 
                    s0_base_post, s0_size_post);

            // Check for Parameter Corruption (The 22MB Size bug)
            if (s0_size_post == saved_pool_base) {
                dprintf(trace_fd, "[DATA_FIX_WARNING] Parameter Corruption Detected! Size is being overwritten by Pool Base.\n");
            }
                
            // EMERGENCY OVERRIDE: If slots are empty or corrupted, force the known correct size
            if (s0_size_post == 0 || s0_size_post == saved_pool_base) {
                *(uint32_t*)(0x01259b00 + 0x8024) = 0x00001a40; 
                dprintf(trace_fd, "[DATA_FIX] MANUAL_OVERRIDE: Forced Slot[0] size to 0x1A40 (6.56 KB)\n");
            }
        }

        // Log pool state AFTER zeroing
        if (memExist(0x01259a28)) {
            uint32_t pool_base_after = *(uint32_t*)0x01259a28;
            dprintf(trace_fd, "[DATA_FIX_TIMING] Pool state AFTER zeroing:\n");
            dprintf(trace_fd, "[DATA_FIX_TIMING]   DAT_01259a28 = 0x%08x\n", pool_base_after);
        }

        data_section_fixed = 1;
        
    }
    // === DAT_0357927c WRITE PROTECTION === 
    // FUN_00732ca0 at 0x733400 writes EDI to DAT_0357927c 
    // If EDI contains garbage, this corrupts the global pointer 
    // Intercept this write and validate EDI first 
    
    if (current_rip == 0x733400) { 
        uint32_t edi_value = (uint32_t)R_RDI; 
        
        // Check if EDI is a valid pointer (in game or Wine space) 
        // Valid pointers should be in ranges: 
        //   - Game PE: 0x00400000 - 0x04376000 
        //   - Wine DLLs: 0x10000000 - 0x80000000 
        // Garbage like 0x74b28208 is in the unmapped gap 
        
        int is_valid = 0; 
        if (edi_value >= 0x00400000 && edi_value < 0x04b70000) { 
            is_valid = 1;  // Game PE space 
        } else if (edi_value >= 0x10000000 && edi_value < 0x80000000) { 
            is_valid = 1;  // Wine DLL space 
        } else if (edi_value == 0) { 
            is_valid = 1;  // NULL is valid (means uninitialized) 
        } 
        
        if (!is_valid) { 
            // EDI contains garbage - skip this write by moving past the instruction 
            // MOV [DAT_0357927c], EDI is 6 bytes: 89 3D 7C 92 57 03 
            R_RIP += 6; 
            
            if (trace_fd >= 0) { 
                dprintf(trace_fd, "[WRITE_PROTECT] Skipped garbage write to DAT_0357927c\n"); 
                dprintf(trace_fd, "[WRITE_PROTECT] EDI = 0x%08x (invalid, rejected)\n", edi_value); 
                dprintf(trace_fd, "[WRITE_PROTECT] Skipped to RIP = 0x%lx\n", (uintptr_t)R_RIP); 
            } 
            
            mark_exception_handled(fault_addr, (uintptr_t)pc); 
            relockMutex(Locks); 
            return; 
        } 
    } 
    
    // === SIMPLIFIED TLS FIX === 
    // NOTE: This used to eagerly pre-write TLS[0x5C] with the real TID here,
    // unconditionally, on every entry. That directly defeats the sentinel
    // check in the in_tls_function/0x47fb6f branch below: it makes the
    // sentinel non-zero BEFORE we ever decide whether the game's own
    // GetCurrentThreadId()-based init (native code at 0x47fb7f) should be
    // allowed to run. Removed — TLS[0x5C] is now owned exclusively by:
    //   (a) init_fake_tls(), which zeroes it for worker threads, and
    //   (b) the sentinel-check block below, which lets native fall-through
    //       code write it for real when appropriate.
    // Do NOT reintroduce a write to tls_base+0x5C anywhere above that block.
    
    // Initialize TLS[0x58] with pointer to DAT_0280a410 
    *(uint32_t*)(tls_base + 0x58) = 0x0280a410; 
    
    // Set global main thread ID 
    if (memExist(0x0280a5c8) && *(uint32_t*)0x0280a5c8 == 0) { 
        uint32_t current_tid = *(uint32_t*)(tls_base + 0x5C); 
        *(uint32_t*)0x0280a5c8 = current_tid; 
        
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[TLS_FIX] Set DAT_0280a5c8 = %u (main thread only)\n", current_tid);
        }
    } 
    
    if (trace_fd >= 0) { 
        dprintf(trace_fd, "\n=== TLS SIMPLIFIED FIX ===\n"); 
        dprintf(trace_fd, "[TLS_FIX] RIP: 0x%x, PC: 0x%lx, ESP: 0x%lx [ESP]=0x%08x, (tid=%d)\n",
            current_rip, (unsigned long)pc, (unsigned long)R_ESP, *(uint32_t*)(uintptr_t)(R_ESP), GetTID()); 
        dprintf(trace_fd, "[TLS_FIX] TLS Base: %p\n", (void*)tls_base); 
        dprintf(trace_fd, "[TLS_FIX] TLS[0x5C] = %u (Thread ID)\n", *(uint32_t*)(tls_base + 0x5C)); 
        dprintf(trace_fd, "[TLS_FIX] TLS[0x58] = 0x0280a410\n"); 
        dprintf(trace_fd, "=========================\n\n"); 
    } 
    
    // === MANUAL INSTRUCTION EXECUTION === 
    // Instead of re-executing, manually perform the CMP and skip it 
    
    // === COMPREHENSIVE TLS INSTRUCTION HANDLING === 
    // Handle crashes anywhere in FUN_0047fb60 by skipping to safe point 
    
    // CRITICAL: Get emu structure for interpreter mode 
    x64emu_t* emu = thread_get_emu(); 
    if (!emu) { 
        // Fallback if emu not available 
        mark_exception_handled(fault_addr, (uintptr_t)pc); 
        relockMutex(Locks); 
        return; 
    } 

    if (trace_fd >= 0 && (in_tls_function || current_rip == 0x47fb6f || current_rip == 0x47fb67)) {
        trace_x64emu_gate = 1;
        dprintf(trace_fd, "[TLS_DIAG] trace_x64emu_gate is set to 0x%x\n", trace_x64emu_gate);
        dprintf(trace_fd,
            "[TLS_DIAG] emu=%p pre-fix EAX=0x%08x ECX=0x%08x EDX=0x%08x segs_offs[FS]=0x%08lx segs_serial[FS]=%u tls_block(pthread)=%p array_slot0_now=0x%08x\n",
            (void*)emu,
            emu->regs[_AX].dword[0],
            emu->regs[_CX].dword[0],
            emu->regs[_DX].dword[0],
            (uintptr_t)emu->segs_offs[_FS],
            emu->segs_serial[_FS],
            pthread_getspecific(tls_block_key),
            memExist((uintptr_t)pthread_getspecific(tls_block_key)+0x400) ? *(uint32_t*)((uint8_t*)pthread_getspecific(tls_block_key)+0x400) : 0xffffffff);
        }

    if (in_tls_function || current_rip == 0x47fb6f) { 
        // === INTERPRETER MODE REGISTER FIX === 
        // In interpreter mode, registers are tracked in emu structure, NOT ucontext 
        // We must set BOTH for compatibility 
        
        // Reproduce the actual TLS lookup the game performs:
        //   EAX = _tls_index (from 0x003a3be4, confirmed = 0)
        //   ECX = FS:[0x2c]  (the TLS pointer array)
        //   EDX = [ECX + EAX*4] (the per-thread TLS block)
        // init_fake_tls() already wrote tls_block into all 128 slots of the array,
        // so this resolves to tls_block — but computing it correctly means if
        // _tls_index ever changes or EAX was non-zero at fault time, EDX is still right.
        uint32_t tls_idx = memExist(0x003a3be4) ? *(uint32_t*)0x003a3be4 : 0;
        uint32_t tls_array32 = *(uint32_t*)(tls_base + 0x2c); // FS:[0x2c], 32-bit guest ptr
        uintptr_t tls_array = (uintptr_t)tls_array32;          // zero-extend, don't widen-read
        uintptr_t candidate_addr = tls_array + (uintptr_t)tls_idx * 4;
        uintptr_t tls_block_ptr = (tls_array && memExist(candidate_addr))
                                  ? (uintptr_t)(*(uint32_t*)candidate_addr)  // slot is also 32-bit
                                  : tls_base; // safe fallback
        emu->regs[_AX].dword[0] = tls_idx;
        emu->regs[_CX].dword[0] = (uint32_t)tls_array;
        emu->regs[_DX].dword[0] = (uint32_t)tls_block_ptr;
        R_RAX = tls_idx;
        R_RCX = tls_array;
        R_RDX = (uint32_t)tls_block_ptr;
        
        // Ghidra-confirmed semantics of FUN_0047fb60:
        //   if (*(EDX+0x5C) == 0) { *(EDX+0x5C) = GetCurrentThreadId(); }
        //   return *(EDX+0x5C) == DAT_0280a5c8;   <- unrelated epilogue check,
        //                                            must NOT drive this branch.
        // ZF here must reflect ONLY whether the sentinel at [EDX+0x5C] is zero.
        // Do not write the sentinel — let the native fall-through
        // at 0x47fb7f run for real (it does LEA/CALL GetCurrentThreadId/MOV),
        // so the game's own init path executes exactly once, for real,
        // exactly as it would on native Windows.
        uint32_t *sentinel_ptr = (uint32_t*)(tls_block_ptr + 0x5C);
        int sentinel_is_zero = memExist((uintptr_t)sentinel_ptr) && (*sentinel_ptr == 0);
        if (trace_fd >= 0 && !sentinel_is_zero) {
            dprintf(trace_fd,
                "[TLS_FIX] WARNING: sentinel at %p already non-zero (0x%08x) on entry — "
                "native init at 0x47fb7f will be skipped this call. If this fires on a "
                "thread's FIRST fault, something upstream is writing TLS[0x5C] early.\n",
                (void*)sentinel_ptr, *sentinel_ptr);
        }

        if (sentinel_is_zero) {
            emu->eflags.x64 |= (1 << 6);   // ZF=1 -> JNZ not taken -> real init runs
        } else {
            emu->eflags.x64 &= ~(1 << 6);  // ZF=0 -> JNZ taken -> already inited, skip
        }

        if (trace_fd >= 0) {
            dprintf(trace_fd, "[IAT_CHECK] Value at GetCurrentThreadId IAT slot 0x00b490fc = 0x%08x\n",
                    memExist(0x00b490fc) ? *(uint32_t*)0x00b490fc : 0xffffffff);
        }
        
        // Set guest RIP in emu structure (critical for interpreter mode!) 
        emu->ip.dword[0] = 0x47fb76;  // Jump to safe continuation point 
        
        if (trace_fd >= 0) {  
            dprintf(trace_fd, "[TLS_FIX] Crash at RIP=0x%x, fault=0x%lx\n", current_rip, fault); 
            dprintf(trace_fd, "[TLS_FIX] Set emu->regs: EAX=0x%08x ECX=0x%08x EDX=0x%08x\n",  
                    emu->regs[_AX].dword[0], emu->regs[_CX].dword[0], emu->regs[_DX].dword[0]); 
            dprintf(trace_fd, "[TLS_FIX] Set emu->ip.dword[0] = 0x47fb76, ZF=%d\n",  
                    (sentinel_is_zero));  
            dprintf(trace_fd, "[JMPBUF_CHECK] emu=%p emu->jmpbuf=%p (siglongjmp path %s)\n",
                    (void*)emu, (void*)(emu ? emu->jmpbuf : NULL),
                    (emu && emu->jmpbuf) ? "WILL fire" : "will NOT fire -- falling back to plain return()");
        }  
    } 
    else if (current_rip == 0x4cd229) { 
        // This is the MOV EDI, [_tls_index] instruction 
        // Set in emu structure for interpreter mode 
        emu->regs[_DI].dword[0] = 0;  // EDI = _tls_index = 0 
        emu->ip.dword[0] = current_rip + 6;  // Skip 6-byte MOV instruction 
        
        if (trace_fd >= 0) { 
            dprintf(trace_fd, "[TLS_FIX] Set EDI=0 (_tls_index), emu->ip=0x%lx\n", 
                    (uintptr_t)emu->ip.dword[0]); 
        } 
    } 
    
    // CRITICAL: Use RESUME_EXECUTION_INTERP() to longjmp back to interpreter 
    // This forces interpreter to reload state from emu structure 
    RESUME_EXECUTION_INTERP(); 
} 

// === END TLS SKIP ===

// === DIAGNOSTIC: Monitor jump table initialization ===
static int jump_table_monitor = 0;
if (!jump_table_monitor && trace_fd >= 0) {
    dprintf(trace_fd, "\n=== JUMP TABLE INITIALIZATION MONITOR ===\n");
    dprintf(trace_fd, "[JUMP_INIT] RIP when checked: 0x%lx\n", (unsigned long)pc);
    
    // Check if these addresses are initialized yet
    if (memExist(0x01261b24)) {
        uint32_t k1 = *(uint32_t*)0x01261b24;
        uint32_t k2 = memExist(0x01261b2c) ? *(uint32_t*)0x01261b2c : 0;
        
        dprintf(trace_fd, "[JUMP_INIT] K1 @ 0x01261b24 = 0x%08x\n", k1);
        dprintf(trace_fd, "[JUMP_INIT] K2 @ 0x01261b2c = 0x%08x\n", k2);
        
        // Check if they look like valid code addresses
        if (k1 >= 0x00400000 && k1 <= 0x04376000) {
            dprintf(trace_fd, "[JUMP_INIT] K1 IS IN PE IMAGE RANGE (VALID!)\n");
        } else {
            dprintf(trace_fd, "[JUMP_INIT] K1 IS GARBAGE (not in PE image)\n");
        }
        
        // Check if K2 is valid
        if (k2 >= 0x00400000 && k2 <= 0x04376000) {
            dprintf(trace_fd, "[JUMP_INIT] K2 IS IN PE IMAGE RANGE (VALID!)\n");
        } else if (k2 == 0) {
            dprintf(trace_fd, "[JUMP_INIT] K2 IS NULL (uninitialized)\n");
        } else {
            dprintf(trace_fd, "[JUMP_INIT] K2 IS GARBAGE (not in PE image)\n");
        }
        
        // Additional context: check if we're in startup code
        if ((uintptr_t)pc >= 0x00400000 && (uintptr_t)pc <= 0x01000000) {
            dprintf(trace_fd, "[JUMP_INIT] Currently executing in PE image (startup phase)\n");
        } else {
            dprintf(trace_fd, "[JUMP_INIT] Currently executing outside PE image\n");
        }
    }
    dprintf(trace_fd, "==========================================\n\n");
    jump_table_monitor = 1;
}

// === THREAD & WAIT LOOP FIXES ===

uintptr_t rip = (uintptr_t)R_RIP;
uintptr_t base_addr = (uintptr_t)&engine_bootstrap[0];

// 2. TASK DISPATCHER LOBOTOMY (0x006c7c70)
if (rip == 0x006c7c70) {
    if (memExist(0x02b8d700)) {
        *(uint32_t*)(0x02b8d700 + 0x744) = 0; // Task Count
        *(uint32_t*)(0x02b8d700 + 0x740) = 0; // Active Flag
    }
    uint32_t* esp = (uint32_t*)(uintptr_t)R_RSP;
    if (memExist((uintptr_t)esp)) {
        R_RIP = esp[0];
        R_RSP += 4;
    } else {
        R_RIP += 5;
    }
    RESUME_EXECUTION_INTERP();
}

// 3. STAGE A: THE GATEKEEPER (FUN_00505de0)
// This doesn't change RIP/regs, so we don't need RESUME_EXECUTION_INTERP, but let's be safe if it modifies them.
// It just modifies memory. We can just fall through or return.
if (rip == 0x00505de0) {
    uint32_t* engine_struct = (uint32_t*)(uintptr_t)R_ECX;
    if (engine_struct && memExist((uintptr_t)engine_struct + 0x5dac)) {
        engine_struct[0x5dac/4] = 1; // Force Heartbeat
    }
}


// 5. STAGE C: RESOURCE POOL PROTECTOR (0x005abd80)
if (rip == 0x005abd80) {
    uint32_t* ctx = (uint32_t*)(uintptr_t)R_ECX;
    if (ctx && memExist((uintptr_t)ctx + 0xa7 * 4) && ctx[0xa7] == 0) {
        ctx[0xa7] = (uint32_t)(base_addr + 0x8000);
        *(uint32_t*)(base_addr + 0x8000 + 0x280) = 0x0FFFFFFF; // Limit
    }
}

// 6. STAGE D: VOID JUMP TRAPS (0x005b63df & 0x005b6446)
if (rip == 0x005b63df || rip == 0x005b6446) {
    R_RIP = (rip == 0x005b63df) ? 0x005b63e1 : 0x005b6419;
    RESUME_EXECUTION_INTERP();
}

// 7. SYNTAX ERROR STATE FORCING (0x005b63c0)
if (rip == 0x005b63c0) {
    uintptr_t engine_ptr = (uintptr_t)R_EAX;
    if (engine_ptr > 0x10000 && memExist(engine_ptr + 0x1220)) {
        *(uint32_t*)(engine_ptr + 0x1220) = 7;
    }
}

// Loop Breaker (0x006da00d)
if ((uintptr_t)R_RIP >= 0x006da00d && (uintptr_t)R_RIP <= 0x006da00f) {
    if (trace_fd >= 0) {
        dprintf(trace_fd, "[COMPAT_SHIM] Main Thread released from Wait loop at %p\n", (void*)R_RIP);
    }
    R_EAX = 0;           // Result: WAIT_OBJECT_0 (Success)
    R_RIP = 0x006da00f;  // Jump over CALL ESI
    RESUME_EXECUTION_INTERP();
}

// Improved Status Check (Address 0x006e2b10)
if ((uintptr_t)R_RIP >= 0x006e2b10 && (uintptr_t)R_RIP <= 0x006e2b15) {
    if (trace_fd >= 0) {
        dprintf(trace_fd, "[COMPAT] Forcing System Status to READY at %p\n", (void*)R_RIP);
    }
    R_EAX = 1;           // Return True
    R_RIP = 0x006e2b1d;  // Jump directly to RET
    RESUME_EXECUTION_INTERP();
}

// === CRASH SITE LOGGING AT 0x650960 (XOR Cipher Loop) ===
// Address: 0x00650960 - LAB_00650960, loop entry point in FUN_006508d0
// Instruction: MOVZX EDX, byte ptr [EAX + EBP*0x1]
// This is where guard page cascade begins - capture parameter corruption at source
if ((uintptr_t)R_RIP == 0x00650960) {
    init_trace_fd();
    
    // Capture all registers at crash site
    uint32_t eax = (uint32_t)R_RAX;
    uint32_t ebx = (uint32_t)R_RBX;
    uint32_t ecx = (uint32_t)R_RCX;
    uint32_t edx = (uint32_t)R_RDX;
    uint32_t esi = (uint32_t)R_RSI;
    uint32_t edi = (uint32_t)R_EDI;
    uint32_t ebp = (uint32_t)R_RBP;
    uint32_t esp = (uint32_t)R_RSP;
    
    // Calculate fault address (EAX + EBP)
    uint32_t calculated_fault = eax + ebp;
    
    dprintf(trace_fd, "\n=== CRASH SITE 0x650960 (XOR Cipher Loop) ===\n");
    dprintf(trace_fd, "[CRASH_SITE] Instruction: MOVZX EDX, byte ptr [EAX + EBP]\n");
    dprintf(trace_fd, "[CRASH_SITE] Calculated fault address: [0x%08x + 0x%08x] = 0x%08x\n",
            eax, ebp, calculated_fault);
    
    dprintf(trace_fd, "[CRASH_SITE] Register dump:\n");
    dprintf(trace_fd, "  EAX = 0x%08x  EBX = 0x%08x  ECX = 0x%08x  EDX = 0x%08x\n",
            eax, ebx, ecx, edx);
    dprintf(trace_fd, "  ESI = 0x%08x  EDI = 0x%08x  EBP = 0x%08x  ESP = 0x%08x\n",
            esi, edi, ebp, esp);
    
    // === POOL STATE DIAGNOSTIC LOGGING ===
    // Purpose: Confirm pool_base and slot control block values at RC4 crash time.
    // These values determine whether FUN_0059d310's cap calculation is correct.

    dprintf(trace_fd, "\n=== POOL STATE AT RC4 CRASH ===\n");

    // 1. Pool base (written once at 0x4d3fbe, read by FUN_0059d310 via piVar10[2])
    if (memExist(0x01259a28)) {
        uint32_t pool_base_live = *(uint32_t*)0x01259a28;
        dprintf(trace_fd, "[POOL] DAT_01259a28 (pool_base) = 0x%08x\n", pool_base_live);
        dprintf(trace_fd, "[POOL] pool_end (pool_base + 0x80000) = 0x%08x\n",
                pool_base_live + 0x80000);
        uint32_t dest_base = (uint32_t)R_RBX;
        if (pool_base_live != 0) {
            int32_t offset_in_pool = (int32_t)(dest_base - pool_base_live);
            uint32_t remaining = (pool_base_live + 0x80000) - dest_base;
            dprintf(trace_fd, "[POOL] EBX (dest_base) = 0x%08x\n", dest_base);
            dprintf(trace_fd, "[POOL] dest_base offset from pool_base = 0x%08x (%d)\n",
                    offset_in_pool, offset_in_pool);
            dprintf(trace_fd, "[POOL] remaining bytes to pool_end = 0x%08x (%u)\n",
                    remaining, remaining);
        }
    } else {
        dprintf(trace_fd, "[POOL] DAT_01259a28 NOT MAPPED\n");
    }

    // 2. Pool write offset (DAT_01259a2c)
    if (memExist(0x01259a2c)) {
        dprintf(trace_fd, "[POOL] DAT_01259a2c (pool_write_offset) = 0x%08x\n",
                *(uint32_t*)0x01259a2c);
    }

    // 3. Ring buffer write cursor (DAT_01259a30)
    if (memExist(0x01259a30)) {
        dprintf(trace_fd, "[POOL] DAT_01259a30 (ring_write_cursor) = 0x%08x\n",
                *(uint32_t*)0x01259a30);
    }

    // 4. Slot control blocks at DAT_01259a3c (5 DWORDs per slot, 4 slots)
    // piVar10[2] is the pool_base copy stored in the control block.
    // Layout: [0]=slot_index, [1]=slot_struct_ptr, [2]=pool_base_copy, [3+4]=unknown
    dprintf(trace_fd, "[CTRL] Slot control blocks at 0x01259a3c:\n");
    for (int s = 0; s < 4; s++) {
        uint32_t ctrl_base = 0x01259a3c + s * 0x14; // 5 DWORDs = 0x14 per slot
        if (memExist(ctrl_base + 0x10)) {
            uint32_t c0 = *(uint32_t*)(uintptr_t)(ctrl_base);
            uint32_t c1 = *(uint32_t*)(uintptr_t)(ctrl_base + 4);
            uint32_t c2 = *(uint32_t*)(uintptr_t)(ctrl_base + 8);  // piVar10[2] = pool_base_copy
            uint32_t c3 = *(uint32_t*)(uintptr_t)(ctrl_base + 12);
            uint32_t c4 = *(uint32_t*)(uintptr_t)(ctrl_base + 16);
            dprintf(trace_fd, "  ctrl[%d]: idx=0x%08x struct_ptr=0x%08x pool_base_copy=0x%08x "
                    "c3=0x%08x c4=0x%08x\n", s, c0, c1, c2, c3, c4);
        } else {
            dprintf(trace_fd, "  ctrl[%d]: NOT MAPPED at 0x%08x\n", s, ctrl_base);
        }
    }

    // 5. Slot structures at DAT_01259b00 (4 slots, 0x8080 bytes each)
    // Offset +0x8020 = buf_start, +0x8024 = size, +0x8028 = read_pos,
    // +0x802c = write_pos, +0x8030 = in_use
    dprintf(trace_fd, "[SLOT] Slot structures at 0x01259b00:\n");
    for (int s = 0; s < 4; s++) {
        uint32_t slot_ptr = 0x01259b00 + s * 0x8080;
        if (memExist(slot_ptr + 0x8030)) {
            uint32_t buf_start   = *(uint32_t*)(uintptr_t)(slot_ptr + 0x8020);
            uint32_t buf_size    = *(uint32_t*)(uintptr_t)(slot_ptr + 0x8024);
            uint32_t read_pos    = *(uint32_t*)(uintptr_t)(slot_ptr + 0x8028);
            uint32_t write_pos   = *(uint32_t*)(uintptr_t)(slot_ptr + 0x802c);
            uint8_t  in_use      = *(uint8_t*) (uintptr_t)(slot_ptr + 0x8030);
            dprintf(trace_fd, "  slot[%d]: buf_start=0x%08x size=0x%08x "
                    "read_pos=0x%08x write_pos=0x%08x in_use=%d\n",
                    s, buf_start, buf_size, read_pos, write_pos, in_use);

            // If this slot's buf_start matches our crash dest (EBX), flag it
            if (buf_start == (uint32_t)R_RBX) {
                dprintf(trace_fd, "  *** slot[%d] buf_start MATCHES EBX (crash dest) ***\n", s);
                dprintf(trace_fd, "  *** declared size = 0x%08x — compare to pool size 0x80000 ***\n",
                        buf_size);
            }
        } else {
            dprintf(trace_fd, "  slot[%d]: struct NOT MAPPED at 0x%08x\n", s, slot_ptr);
        }
    }

    // 6. Slot counter globals
    if (memExist(0x01259a34)) {
        dprintf(trace_fd, "[POOL] DAT_01259a34 (slot_counter) = 0x%08x\n", *(uint32_t*)0x01259a34);
    }
    if (memExist(0x01259a38)) {
        dprintf(trace_fd, "[POOL] DAT_01259a38 (slot_total)   = 0x%08x\n", *(uint32_t*)0x01259a38);
    }

    // 7. Stack walk: find FUN_006770b0 frame to get the actual params passed to FUN_006508d0
    // Call chain at crash: FUN_006508d0 (RC4) ← FUN_006770b0 ← FUN_0059d310
    // FUN_006508d0 pushes: ECX, EBP, EBX, EDI (4 regs = 0x10 bytes)
    // Its params at [ESP+0x14], [ESP+0x18], [ESP+0x1C], [ESP+0x20]
    // FUN_006770b0 called FUN_006508d0 from 0x677121
    // Walk stack to find the return address 0x677121 and read FUN_006770b0 params
    dprintf(trace_fd, "[STACK] Walking stack from ESP=0x%08x to find FUN_006770b0 frame:\n",
            (uint32_t)R_RSP);
    {
        uint32_t* sp = (uint32_t*)(uintptr_t)(uint32_t)R_RSP;
        int found = 0;
        for (int i = 0; i < 64 && !found; i++) {
            if (!memExist((uintptr_t)&sp[i])) break;
            uint32_t val = sp[i];
            // Return address from FUN_006508d0 back to FUN_006770b0 is 0x00677121
            if (val == 0x00677121 || val == 0x0067711c) {
                dprintf(trace_fd, "  Found retaddr 0x%08x at ESP[%d] = stack+0x%x\n",
                        val, i, i*4);
                // FUN_006770b0's params were pushed before CALL 006508d0
                // At 0x006770fe: PUSH ESI (param_1=buf), PUSH ESI (dup), PUSH EBX, PUSH EAX
                // At 0x0067711c: PUSH EDI, PUSH ECX, PUSH EDI, PUSH ECX (second block)
                // Reading 8 words above the retaddr gives us the pushed params
                for (int j = i+1; j < i+9 && j < 64; j++) {
                    if (memExist((uintptr_t)&sp[j])) {
                        dprintf(trace_fd, "  stack[%d] (ESP+0x%x) = 0x%08x\n",
                                j, j*4, sp[j]);
                    }
                }
                found = 1;
            }
        }
        if (!found) {
            dprintf(trace_fd, "  Retaddr 0x677121 not found in first 64 stack words\n");
        }
    }

    dprintf(trace_fd, "=== END POOL STATE ===\n\n");
    // === END POOL STATE DIAGNOSTIC LOGGING ===
        
    // Reconstruct FUN_006508d0 parameters from stack
    // Function signature: FUN_006508d0(int param_1, byte *param_2, byte *param_3, uint param_4)
    uint32_t* stack = (uint32_t*)(uintptr_t)esp;
    
    if (memExist((uintptr_t)stack) && memExist((uintptr_t)(stack + 20))) {
        dprintf(trace_fd, "[CRASH_SITE] Reconstructing FUN_006508d0 parameters from stack:\n");
        
        // Parameters are pushed before function entry, then there are PUSHes inside function
        // ESP layout after PUSH ECX, PUSH EBP, PUSH EBX, PUSH EDI:
        // [ESP+0x14] = param_1 (auStack_84 buffer)
        // [ESP+0x18] = param_2 (source buffer - EBX in function)
        // [ESP+0x1c] = param_3 (destination buffer)
        // [ESP+0x20] = param_4 (buffer_size - EBP in function)
        
        uint32_t param_1 = stack[0x14/4];  // auStack_84 pointer
        uint32_t param_2 = stack[0x18/4];  // source buffer (base address)
        uint32_t param_3 = stack[0x1c/4];  // destination buffer
        uint32_t param_4 = stack[0x20/4];  // buffer size
        
        dprintf(trace_fd, "  param_1 (auStack_84) = 0x%08x\n", param_1);
        dprintf(trace_fd, "  param_2 (source)     = 0x%08x\n", param_2);
        dprintf(trace_fd, "  param_3 (dest)       = 0x%08x\n", param_3);
        dprintf(trace_fd, "  param_4 (size)       = 0x%08x (%u bytes)\n", param_4, param_4);

        // CRITICAL: Check for unrealistic buffer sizes (crypto operations typically KB, not MB)
        if (param_4 > 0x01000000) {  // 16 MB
            dprintf(trace_fd, "\n[CRASH_CORRUPTION] *** param_4 (buffer size) is UNREALISTICALLY LARGE ***\n");
            dprintf(trace_fd, "[CRASH_CORRUPTION] Size: 0x%08x (%u bytes = %.2f MB)\n",
                    param_4, param_4, (float)param_4 / 1048576.0);
            dprintf(trace_fd, "[CRASH_CORRUPTION] Normal crypto buffers are KB-sized, not MB-sized\n");
            dprintf(trace_fd, "[CRASH_CORRUPTION] This is the PRIMARY corruption - size parameter is corrupt\n");
            
            // Calculate where the loop will crash
            uint32_t crash_offset = 0x04376000 - param_3;
            dprintf(trace_fd, "[CRASH_CORRUPTION] With dest=0x%08x, loop will crash after %u bytes (0x%08x)\n",
                    param_3, crash_offset, crash_offset);
            dprintf(trace_fd, "[CRASH_CORRUPTION] Crash will occur when EAX reaches 0x04376000 (guard page boundary)\n");
        }

        // The pool should already be initialised
        // Read the pool structures
        uint32_t pool_base = *(uint32_t*)0x01259a28;
        uint32_t* slot0 = (uint32_t*)(0x01259b00);
        uint32_t buf_start = slot0[0x8020/4];
        uint32_t buf_size = slot0[0x8024/4];
        
        if (buf_start != 0 && buf_size > 0 && buf_size <= 0x80000) {
            // Redirect the RC4 loop to use the safe pool
            param_3 = buf_start;
            param_4 = buf_size;
            stack[0x1c/4] = param_3;
            stack[0x20/4] = param_4;
            // EBX = dest base, reset to new dest start
            R_RBX = param_3;
            emu->regs[_BX].dword[0] = param_3;
            // EAX = current position pointer, must also start at new dest
            // The loop ran ~48 iterations before crashing; restart from new base
            R_RAX = param_3;
            emu->regs[_AX].dword[0] = param_3;
            // EBP = XOR key state offset, reset to 0 (fresh start in key stream)
            R_RBP = 0;
            emu->regs[_BP].dword[0] = 0;

            // Fix the OUTER loop counter at [ESP+0x24].
            // The outer loop subtracts 0x40 per iteration and continues until this reaches 0.
            // Without this fix, the corrupt original value (e.g. 0x426f3510) causes ~17M
            // outer iterations, writing XOR output past the pool buffer into arbitrary memory
            // including _tls_index at 0x033a3be4, corrupting it.
            // Setting this to buf_size = 0x00080000 gives exactly 0x2000 outer iterations,
            // spanning precisely the pool buffer range.
            if (memExist((uintptr_t)(stack + 0x24/4))) {
                stack[0x24/4] = buf_size;
            }
            
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[CRASH_FIX] Redirected to pool: dest=0x%08x, size=0x%08x, EAX reset to dest base\n",
                        param_3, param_4);
            }
            // CRITICAL: Resume execution immediately so CRASH_PREVENTION does not fire
            // and negate this fix. The loop will now run with corrected parameters.
            RESUME_EXECUTION_INTERP();
        } else {
            // Fallback: using existing falback code
            dprintf(trace_fd, "[CRASH_FIX] Pool not ready, using fallback\n");

            // CRITICAL FIX: param_4 points to ZERO because buffers are uninitialized
            // Instead of aborting, set a SAFE default buffer size
            if (param_4 >= 0x00CF7000 && param_4 <= 0x04332000) {
                if (memExist((uintptr_t)param_4)) {
                    uint32_t actual_size = *(uint32_t*)(uintptr_t)param_4;
                    dprintf(trace_fd, "[CRASH_FIX] Dereferenced value: 0x%08x (%u bytes)\n", actual_size, actual_size);
                    
                    if (actual_size == 0 || actual_size > 0x01000000) {
                        // Buffer uninitialized or corrupt - set safe default
                        uint32_t safe_size = 0x8000;  // 32 KB - reasonable crypto buffer
                        
                        dprintf(trace_fd, "\n[INIT_FIX] Buffer uninitialized (size=%u). Setting safe default: %u bytes\n", 
                                actual_size, safe_size);
                        
                        // Write safe size to the pointer location
                        *(uint32_t*)(uintptr_t)param_4 = safe_size;
                        
                        // Also update the actual EBP register which holds the size during loop
                        R_RBP = safe_size;
                        // CRITICAL: Check if destination buffer has enough space
                        uint32_t dest_end = param_3 + safe_size;
                        if (dest_end > 0x04376000) {
                        
                            // Destination would overflow into guard pages
                            uint32_t available_space = 0x04376000 - param_3;
                            
                            dprintf(trace_fd, "[INIT_FIX] WARNING: Dest buffer too small\n");
                            dprintf(trace_fd, "[INIT_FIX] Available space: %u bytes, needed: %u bytes\n", 
                                    available_space, safe_size);
                            
                            // CRITICAL: Account for lookahead in XOR cipher
                            // The instruction "MOVZX EDX, [EAX + EBP]" reads AHEAD by EBP bytes
                            // We need space for BOTH the destination buffer AND the lookahead
                            uint32_t lookahead = safe_size;  // EBP = 0x8000, same as buffer size
                            uint32_t total_space_needed = safe_size + lookahead;  // 0x10000 (64 KB)

                            // Move destination back to allow room for buffer + lookahead
                            uint32_t new_dest = 0x04376000 - total_space_needed;  // 0x04366000

                            stack[0x1c/4] = new_dest;  // Update param_3 on stack

                            // CRITICAL: Also update EBX register which holds dest during loop
                            R_RBX = new_dest;
                            // CRITICAL: The loop counter at [ESP+0x10] controls iterations
                            // With EBP=32KB and counter=4, it would process 128KB total
                            // We need to limit it to 1 iteration (32KB only)
                            stack[0x10/4] = 1; // Set loop counter to 1 (was 4)
                            
                            // CRITICAL: The source buffer (param_2) must be large enough for lookahead
                            // Redirect source to a safe, zeroed region in .data
                            uint32_t safe_source = 0x01000000;  // Safe area in .data section
                            stack[0x18/4] = safe_source;  // Update param_2 on stack
                            R_RDI = safe_source;  // Update EDI register which holds source

                            dprintf(trace_fd, "[INIT_FIX] Redirected source buffer to safe address: 0x%08x\n", safe_source);
                            dprintf(trace_fd, "[INIT_FIX] Set loop counter to 1 (was 4) to process only 32KB\n");

                            dprintf(trace_fd, "[INIT_FIX] Sliding window fix: moved dest from 0x%08x to 0x%08x\n", param_3, new_dest);
                            dprintf(trace_fd, "[INIT_FIX] Allocated %u bytes (%u buffer + %u lookahead)\n", 
                                    total_space_needed, safe_size, lookahead);
                            dprintf(trace_fd, "[INIT_FIX] Max lookahead read: 0x%08x (safe, 1 byte before guard)\n", 
                                    new_dest + total_space_needed);
                            dprintf(trace_fd, "[INIT_FIX] Updated EBX register to 0x%08x\n", new_dest);
                            dprintf(trace_fd, "[INIT_FIX] Moved dest from 0x%08x to 0x%08x\n", param_3, new_dest);
                        }
                        
                        dprintf(trace_fd, "[INIT_FIX] Fixed: pointer[0x%08x] = %u, EBP = %u\n", 
                                param_4, safe_size, safe_size);
                        dprintf(trace_fd, "[INIT_FIX] Allowing execution with initialized buffer\n");
                        dprintf(trace_fd, "=====================================\n\n");
                        
                        // Don't prevent - let it run with safe size
                        return;  // Exit handler, let execution continue
                    }
                }
            }    
        }
        
        // Check if param_2 (source buffer) is the corrupt address
        if (param_2 >= 0x04300000 && param_2 <= 0x04400000) {
            dprintf(trace_fd, "\n[CRASH_CORRUPTION] *** param_2 (source buffer) is CORRUPT ***\n");
            dprintf(trace_fd, "[CRASH_CORRUPTION] Base address 0x%08x is near .rsrc boundary (0x04336000-0x04375fff)\n", param_2);
            
            if (param_2 + param_4 > 0x04376000) {
                dprintf(trace_fd, "[CRASH_CORRUPTION] Range [0x%08x - 0x%08x] CROSSES into guard pages!\n",
                        param_2, param_2 + param_4);
                dprintf(trace_fd, "[CRASH_CORRUPTION] This causes infinite guard page cascade\n");
            }
        }
        
        // Log loop counter state
        // The loop decrements [ESP+0x10] counter
        if (memExist((uintptr_t)(stack + 4))) {
            uint32_t loop_counter = stack[0x10/4];
            dprintf(trace_fd, "[CRASH_SITE] Loop counter [ESP+0x10] = 0x%08x (%u iterations remaining)\n",
                    loop_counter, loop_counter);
        }
    }
    
    // Dump stack to find return addresses and caller chain
    dprintf(trace_fd, "[CRASH_SITE] Stack dump (32 bytes):\n");
    if (memExist((uintptr_t)stack) && memExist((uintptr_t)(stack + 8))) {
        for (int i = 0; i < 8; i++) {
            dprintf(trace_fd, "  [ESP+0x%02x] = 0x%08x", i*4, stack[i]);
            
            // Check if this looks like a return address (in code section)
            if (stack[i] >= 0x400000 && stack[i] < 0xB00000) {
                dprintf(trace_fd, " <- potential return address (in .text)\n");
            } else if (stack[i] >= 0x00CF7000 && stack[i] <= 0x04332000) {
                dprintf(trace_fd, " <- pointer to .data\n");
            } else {
                dprintf(trace_fd, "\n");
            }
        }
    }
    
    // ENHANCED: Dump crypto buffer structures to trace 23 MB corruption origin
    dprintf(trace_fd, "\n[BUFFER_STRUCTURES] Crypto buffer structures at DAT_01259b00:\n");
    static int init_check_logged = 0;
    for (int slot = 0; slot < 4; slot++) {
        uint32_t* buffer_struct = (uint32_t*)(uintptr_t)(0x01259b00 + (slot * 0x8080));
        
        if (memExist((uintptr_t)(buffer_struct + 0x8020/4)) && 
            memExist((uintptr_t)(buffer_struct + 0x8028/4))) {
            
            uint32_t base_addr = *(uint32_t*)(uintptr_t)(buffer_struct + 0x8020/4);
            uint32_t buffer_size = *(uint32_t*)(uintptr_t)(buffer_struct + 0x8024/4);
            uint32_t remaining = *(uint32_t*)(uintptr_t)(buffer_struct + 0x8028/4);
            uint32_t position = *(uint32_t*)(uintptr_t)(buffer_struct + 0x802c/4);
            
            dprintf(trace_fd, "  Slot[%d] at 0x%08x:\n", slot, (uint32_t)(uintptr_t)buffer_struct);
            dprintf(trace_fd, "    +0x8020 base_addr  = 0x%08x\n", base_addr);
            dprintf(trace_fd, "    +0x8024 buffer_size = 0x%08x (%u bytes)", buffer_size, buffer_size);
            
            if (buffer_size == 0x01694c80) {
                dprintf(trace_fd, " *** CORRUPT 23 MB SOURCE FOUND ***\n");
            } else if (buffer_size > 0x01000000) {
                dprintf(trace_fd, " (%.2f MB - SUSPICIOUS)\n", (float)buffer_size / 1048576.0);
            } else {
                dprintf(trace_fd, "\n");
            }
            
            dprintf(trace_fd, "    +0x8028 remaining   = 0x%08x (%u bytes)\n", remaining, remaining);
            dprintf(trace_fd, "    +0x802c position    = 0x%08x\n", position);
            // Track when buffers get initialized
            if (!init_check_logged && (buffer_size != 0 || base_addr != 0)) {
                init_check_logged = 1;
                dprintf(trace_fd, "\n[INIT_DETECTION] First non-zero buffer found!\n");
                dprintf(trace_fd, "[INIT_DETECTION] Slot[%d]: base=0x%08x size=%u\n", 
                        slot, base_addr, buffer_size);
                
                // Dump call stack to see who initialized it
                dprintf(trace_fd, "[INIT_DETECTION] Call stack at initialization:\n");
                uint32_t* esp_val = (uint32_t*)(uintptr_t)R_RSP;
                for (int i = 0; i < 20; i++) {
                    if (memExist((uintptr_t)(esp_val + i))) {
                        uint32_t val = esp_val[i];
                        if (val >= 0x400000 && val < 0xB00000) {
                            dprintf(trace_fd, "  [ESP+0x%02x] = 0x%08x <- code\n", i*4, val);
                        }
                    }
                }
            }
        }
    }
    if (!init_check_logged) {
    dprintf(trace_fd, "\n[INIT_NON_DETECTION] NO non-zero buffer found across all 4 slots\n");
    dprintf(trace_fd, "[INIT_NON_DETECTION] All buffers remain uninitialized at crash time\n");
    dprintf(trace_fd, "this is 100 bombastics a new patch\n");
    }
    
    // ENHANCED: Check global crypto state variables
    uint32_t* dat_01259a34 = (uint32_t*)0x01259a34;
    uint32_t* dat_00cff6bc = (uint32_t*)0x00cff6bc;
    if (memExist((uintptr_t)dat_01259a34) && memExist((uintptr_t)dat_00cff6bc)) {
        dprintf(trace_fd, "\n[GLOBAL_STATE] Crypto state variables:\n");
        dprintf(trace_fd, "  DAT_01259a34 = 0x%08x (slot index counter)\n", *dat_01259a34);
        dprintf(trace_fd, "  DAT_00cff6bc = 0x%08x (slot count, should be 4)\n", *dat_00cff6bc);
        if (*dat_00cff6bc != 4) {
            dprintf(trace_fd, "  *** WARNING: Slot count is not 4! ***\n");
        }
    }
    
    // CRITICAL: Check if we're about to trigger guard page cascade
    if (calculated_fault >= 0x04376000 && calculated_fault < 0x04400000) {
        dprintf(trace_fd, "\n[CRASH_PREVENTION] *** GUARD PAGE CASCADE IMMINENT ***\n");
        dprintf(trace_fd, "[CRASH_PREVENTION] Fault address 0x%08x is in unmapped guard page region\n", calculated_fault);
        dprintf(trace_fd, "[CRASH_PREVENTION] Aborting FUN_006508d0 execution to prevent cascade\n");
        dprintf(trace_fd, "=====================================\n\n");
        
        // ABORT: Return from FUN_006508d0 early
        // Function has done: PUSH ECX, PUSH EBP, PUSH EBX, PUSH EDI (4 PUSHes = 16 bytes)
        // Stack analysis shows return address is at [current ESP + 0x14]
        uint32_t* stack = (uint32_t*)(uintptr_t)esp;
        if (memExist((uintptr_t)(stack + 6))) {
            uint32_t return_address = stack[0x14/4];  // Read return address at ESP+0x14
            
            dprintf(trace_fd, "[CRASH_PREVENTION] Return address from stack[ESP+0x14] = 0x%08x\n", return_address);
            
            // Validate return address is in code section
            if (return_address >= 0x400000 && return_address < 0xB00000) {
                // Clean up stack: undo 4 PUSHes (ECX, EBP, EBX, EDI)
                R_RSP += 16;
                
                // Return to caller normally with EAX=0 indicating failure
                R_RIP = return_address;
                R_RSP += 4;  // Simulate RET (pop return address from stack)
                
                // Set return value to indicate failure
                R_EAX = 0;
                
                dprintf(trace_fd, "[CRASH_PREVENTION] Returning to caller at RIP=0x%08x with EAX=0\n", return_address);
                dprintf(trace_fd, "[CRASH_PREVENTION] Cleaned up stack: RSP now 0x%08x\n", (uint32_t)R_RSP);
                dprintf(trace_fd, "[CRASH_PREVENTION] WARNING: Downstream crashes may occur with uninitialized buffers\n");
                RESUME_EXECUTION_INTERP();
            } else {
                dprintf(trace_fd, "[CRASH_PREVENTION] ERROR: Return address 0x%08x is NOT in code section\n", return_address);
                dprintf(trace_fd, "[CRASH_PREVENTION] Stack may be corrupt - cannot safely return\n");
            }
        } else {
            dprintf(trace_fd, "[CRASH_PREVENTION] ERROR: Cannot read return address from stack\n");
        }
    }
    
    dprintf(trace_fd, "[CRASH_SITE] Allowing execution to continue (fault address looks valid)\n");
    dprintf(trace_fd, "=====================================\n\n");
    
}
    // UNIVERSAL PATCH
if((sig == X64_SIGSEGV || sig == X64_SIGILL || sig == SIGBUS) && (addr)) {
    uintptr_t fault_addr = (uintptr_t)addr;

    if(trace_fd >= 0) {
        dprintf(trace_fd, "[UNIVERSAL_PATCH] Sig=%d Fault=0x%lx PC=0x%lx\n", sig, fault_addr, (uintptr_t)pc);
    }
    uintptr_t rsp_ceiling = 0x01000000;
    log_memory_map_once();
    static int map_logged_once = 0;
    if(!map_logged_once) {
        FILE* maps = fopen("/proc/self/maps", "r");
        FILE* out = fopen("/sdcard/box64_memory_map_at_crash.txt", "w");
        if(maps && out) {
            char line[512];
            while(fgets(line, sizeof(line), maps)) {
                fputs(line, out);
            }
        }
        if(maps) fclose(maps);
        if(out) fclose(out);
        map_logged_once = 1;
    }
    uintptr_t current_rip = (uintptr_t)R_RIP;

    // --- WINE PROBLEMATIC CODE SKIP ---
    // Wine has internal crashes at 0x7bf21110 that it can't recover from
    // Skip this code entirely to let game progress
    uintptr_t rip = (uintptr_t)R_RIP;
    if (rip >= 0x7bf21100 && rip <= 0x7bf21120) {
        init_safe_zone();
        
        // Skip the instruction/function
        R_RIP = rip + 8;
        R_RAX = (uintptr_t)global_safe_zone;
        R_RDI = (uintptr_t)global_safe_zone;
        
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[WINE_CODE_SKIP] Skipped Wine crash at 0x%lx, advanced to 0x%lx\n", 
                   rip, (uintptr_t)R_RIP);
        }
        
        mark_exception_handled(fault_addr, (uintptr_t)pc);
        relockMutex(Locks);
        return;
    }

    // SIGILL_LIMIT: Check FIRST, before any other fixes 
    if(sig == X64_SIGILL) { 
        static __thread uintptr_t last_stuck_rip = 0; 
        static __thread int stuck_rip_count = 0; 
        
        uintptr_t x64_rip = (uintptr_t)R_RIP; 
        
        if(last_stuck_rip == x64_rip) { 
            stuck_rip_count++; 
            
            if(stuck_rip_count > 20) { 
                if(trace_fd >= 0) { 
                    dprintf(trace_fd, "[SIGILL_LIMIT] x64 RIP=0x%lx stuck for %d faults - passing to Wine\n", 
                            x64_rip, stuck_rip_count); 
                } 
                
                stuck_rip_count = 0; 
                last_stuck_rip = 0; 
                relockMutex(Locks); 
                return; 
            } 
        } else { 
            last_stuck_rip = x64_rip; 
            stuck_rip_count = 1; 
        } 
    } 

    // === ZONE AREA ON-DEMAND PAGE MAPPING ===
    // The zone decompressor (0x636a96 REP MOVSD) accesses guard pages across the zone address space
    // 0x04376000-0x20000000. Two cases:
    // - SEGV_MAPERR: page not mapped at all → mmap anonymous RWX
    // - SEGV_ACCERR with prot=0: Windows guard page → mprotect RWX
    // Both must be handled before DRA sees them, since DRA rejects upper_byte > 0x06.

    if (sig == X64_SIGSEGV &&
        fault_addr >= 0x04376000 && fault_addr <= 0xF0000000 &&
        (info->si_code == SEGV_MAPERR || info->si_code == SEGV_ACCERR)) {

        void* zone_page   = (void*)(fault_addr & ~(uintptr_t)0xFFF);
        int   zone_handled = 0;

        if (info->si_code == SEGV_MAPERR) {
            void* zone_result = mmap(zone_page, 0x1000,
                                    PROT_READ | PROT_WRITE | PROT_EXEC,
                                    MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
            if (zone_result != MAP_FAILED) {
                zone_handled = 1;
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[ZONE_MAP] mmap page %p for SEGV_MAPERR at 0x%lx | RIP=0x%lx\n",
                            zone_page, fault_addr, (uintptr_t)R_RIP);
                }

            } else if (trace_fd >= 0) {
                dprintf(trace_fd, "[ZONE_MAP_FAIL] mmap failed at %p: %s\n", zone_page, strerror(errno));
            }
        } else {
            // SEGV_ACCERR: page mapped but prot=0 (Windows guard page semantics)
            uint32_t zone_prot = getProtection(fault_addr);
            if (zone_prot == 0) {
                int mp_ret = mprotect(zone_page, 0x1000, PROT_READ | PROT_WRITE | PROT_EXEC);
                zone_handled = (mp_ret == 0);
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[ZONE_GUARD] mprotect %p ret=%d for SEGV_ACCERR at 0x%lx | RIP=0x%lx\n",
                            zone_page, mp_ret, fault_addr, (uintptr_t)R_RIP);
                }
            }
            // If prot != 0, fall through — different issue, let downstream handle it
        }

        if (zone_handled) {
            mark_exception_handled(fault_addr, (uintptr_t)pc);
            relockMutex(Locks);
            return;
        }
    }
    // === END ZONE AREA ON-DEMAND PAGE MAPPING ===

    // === HARDENED DYNAMIC REGION ALLOCATOR === 
    if ((sig == X64_SIGSEGV || sig == SIGBUS) && 
        fault_addr >= 0x10000000 && 
        fault_addr <= 0xf0000000 && 
        (info->si_code == SEGV_MAPERR || info->si_code == SEGV_ACCERR)) { 
        
        if (trace_fd >= 0) { 
            dprintf(trace_fd, "[DRA_CHECK] fault_addr=0x%lx sig=%d si_code=%d\n", 
                    fault_addr, sig, info->si_code); 
        } 
        
        // === CORRUPTION DETECTION - RELAXED FOR WINE HEAP === 
        // Wild pointers from heap corruption have characteristic patterns. 
        // We relax this to allow legitimate Wine heap/stack allocations. 
        
        uint32_t upper_byte = (fault_addr >> 24) & 0xFF; 
        int is_safe_range = 0; 
        const char* reason = "Likely garbage pointer or heap corruption"; 
        
        // 1. Game PE space 
        if (fault_addr >= 0x00400000 && fault_addr < 0x04376000) { 
            is_safe_range = 1; 
        } 
        // 2. Wine heap/stack space (where 0x74b28208 lives) 
        // Most Wine allocations on ARM64/box64 land in 0x70000000-0x80000000 
        else if (fault_addr >= 0x70000000 && fault_addr < 0x80000000) { 
            is_safe_range = 1; 
        } 
        // 3. Known Wine DLL space 
        else if (fault_addr >= 0x35000000 && fault_addr < 0x36000000) { 
            is_safe_range = 1; 
        } 
        // 4. NULL is always invalid 
        else if (fault_addr == 0) { 
            is_safe_range = 0; 
            reason = "NULL pointer access"; 
        } 
        // 5. Fallback for other legitimate ranges 
        else if (upper_byte >= 0x00 && upper_byte <= 0x06) { 
            is_safe_range = 1; 
        } 
        else if (upper_byte >= 0x7b && upper_byte <= 0x7e) { 
            is_safe_range = 1; 
        } 
        
        if (!is_safe_range) { 
            if (trace_fd >= 0) { 
                dprintf(trace_fd, "\n=== CORRUPTION DETECTED ===\n"); 
                dprintf(trace_fd, "[DRA_REJECT] Address: 0x%lx (upper byte: 0x%02x)\n", 
                        fault_addr, upper_byte); 
                dprintf(trace_fd, "[DRA_REJECT] Reason: %s\n", reason); 
                dprintf(trace_fd, "[DRA_REJECT] This appears to be UNINITIALIZED/CORRUPT pointer, not legitimate access\n"); 
                dprintf(trace_fd, "\n[DRA_REJECT] Register Dump:\n"); 
                dprintf(trace_fd, "  RAX=0x%016lx RBX=0x%016lx RCX=0x%016lx RDX=0x%016lx\n", 
                        R_RAX, R_RBX, R_RCX, R_RDX); 
                dprintf(trace_fd, "  RSI=0x%016lx RDI=0x%016lx RBP=0x%016lx RSP=0x%016lx\n", 
                        R_RSI, R_RDI, R_RBP, R_RSP); 
                dprintf(trace_fd, "  R8 =0x%016lx R9 =0x%016lx R10=0x%016lx R11=0x%016lx\n", 
                        R_R8, R_R9, R_R10, R_R11); 
                dprintf(trace_fd, "\n[DRA_REJECT] Execution Context:\n"); 
                dprintf(trace_fd, "  Guest RIP: 0x%lx\n", (uintptr_t)R_RIP); 
                dprintf(trace_fd, "  Native PC: 0x%lx\n", (uintptr_t)pc); 
                
                // Check if any register contains this suspicious address 
                if (R_RAX == fault_addr) dprintf(trace_fd, "  → Fault address is in RAX\n"); 
                if (R_RBX == fault_addr) dprintf(trace_fd, "  → Fault address is in RBX\n"); 
                if (R_RCX == fault_addr) dprintf(trace_fd, "  → Fault address is in RCX\n"); 
                if (R_RDX == fault_addr) dprintf(trace_fd, "  → Fault address is in RDX\n"); 
                if (R_RSI == fault_addr) dprintf(trace_fd, "  → Fault address is in RSI\n"); 
                if (R_RDI == fault_addr) dprintf(trace_fd, "  → Fault address is in RDI\n"); 
                
                // Check TLS state 
                uint8_t* tls_block = (uint8_t*)pthread_getspecific(tls_block_key);
                if (tls_block && memExist((uintptr_t)tls_block)) { 
                    uintptr_t tls_base = (uintptr_t)tls_block; 
                    dprintf(trace_fd, "\n[DRA_REJECT] TLS State:\n"); 
                    dprintf(trace_fd, "  TLS Base: %p\n", (void*)tls_base); 
                    dprintf(trace_fd, "  TLS[0x58]: 0x%08x\n", *(uint32_t*)(tls_base + 0x58)); 
                    dprintf(trace_fd, "  TLS[0x5C]: 0x%08x\n", *(uint32_t*)(tls_base + 0x5C)); 
                } 
                
                // Check allocator state 
                if (memExist(0x017913d0)) { 
                    dprintf(trace_fd, "\n[DRA_REJECT] Allocator State:\n"); 
                    dprintf(trace_fd, "  DAT_017913d0: 0x%08x\n", *(uint32_t*)0x017913d0); 
                } 
                
                dprintf(trace_fd, "\n[DRA_REJECT] REFUSING to allocate - exposing corruption source\n"); 
                dprintf(trace_fd, "=========================\n\n"); 
            } 
            
            // DO NOT ALLOCATE - let Wine's exception handler catch this 
            // This will produce a clean crash that exposes the real bug 
            relockMutex(Locks); 
            return;  // Pass to Wine, crash cleanly 
        } 
        
        // Original DRA logic for LEGITIMATE addresses only 
        // (addresses in 0x00-0x06 or 0x7b-0x7e ranges) 
        if (trace_fd >= 0) { 
            dprintf(trace_fd, "[DRA_TRIGGERED] Legitimate access at 0x%lx\n", fault_addr); 
        } 
        
        // Check if mapped but wrong permissions OR completely unmapped
        int prot = getProtection(fault_addr);
        int needs_alloc = 0;
        
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[DRA_PROT] prot=%d for 0x%lx\n", prot, fault_addr);
        }
        
        if (msync((void*)fault_addr, 1, MS_ASYNC) == -1 && errno == ENOMEM) {
            // Completely unmapped
            needs_alloc = 1;
            
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[DRA_UNMAPPED] 0x%lx is completely unmapped\n", fault_addr);
            }
        } else if (prot == 0 || (prot & (PROT_READ | PROT_EXEC)) == 0) {
            // Mapped but has no permissions or missing READ/EXEC
            needs_alloc = 1;
            
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[DRA_NO_PERM] 0x%lx has no/wrong permissions (prot=%d)\n", fault_addr, prot);
            }
        }
        
        if (needs_alloc) {
            // Allocate 64MB region starting at this address
            void* region_start = (void*)(fault_addr & ~0x3FFFFFFUL);  // Align to 64MB
            size_t region_size = 0x4000000;  // 64MB
            
            // === Fix 4: Emergency Bounds Check in DRA ===
            // Modify DYNAMIC_REGION_ALLOC to refuse allocating Wine space:
            if ((uintptr_t)region_start >= 0x7f000000 && (uintptr_t)region_start <= 0x82000000) {
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[DRA_ABORT] Refusing to allocate Wine reserved space %p\n", region_start);
                }
                // Don't allocate, let it crash naturally
            } else {
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[DRA_ALLOCATING] Attempting mmap at %p size 0x%lx\n", 
                            region_start, region_size);
                }
                
                void* result = mmap(region_start, region_size,
                                   PROT_READ | PROT_WRITE | PROT_EXEC,
                                   MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED,
                                   -1, 0);
                
                if (result != MAP_FAILED) {
                    memset(result, 0, region_size);
                    
                    if (trace_fd >= 0) {
                        dprintf(trace_fd, "[DYNAMIC_REGION_ALLOC] Allocated %p - %p (64MB) for fault 0x%lx si_code=%d | RIP=0x%lx\n",
                                region_start, (void*)((uintptr_t)region_start + region_size),
                                fault_addr, info->si_code, (uintptr_t)R_RIP);
                    }
                    
                    mark_exception_handled(fault_addr, (uintptr_t)pc);
                    relockMutex(Locks);
                    return;
                } else {
                    if (trace_fd >= 0) {
                        dprintf(trace_fd, "[DRA_MMAP_FAILED] mmap failed: %s\n", strerror(errno));
                    }
                    
                    // Fallback: try changing permissions on existing mapping
                    void* page_start = (void*)(fault_addr & ~0xFFFUL);
                    if (mprotect(page_start, 4096, PROT_READ | PROT_WRITE | PROT_EXEC) == 0) {
                        if (trace_fd >= 0) {
                            dprintf(trace_fd, "[DYNAMIC_REGION_ALLOC] Changed permissions to RWX at %p for fault 0x%lx\n",
                                    page_start, fault_addr);
                        }
                        mark_exception_handled(fault_addr, (uintptr_t)pc);
                        relockMutex(Locks);
                        return;
                    }
                }
            }
        } else {
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[DRA_SKIP] needs_alloc=0, skipping allocation\n");
            }
        }
    } else {
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[DRA_NOT_TRIGGERED] sig=%d fault_addr=0x%lx si_code=%d\n", 
                    sig, fault_addr, info->si_code);
        }
    }


    // --- PROACTIVE NULL REGISTER FIX ---
    // Fix NULL registers ANYTIME they cause a crash, not just in Wine
    // This catches Wine crashes, game crashes, and any other NULL pointer dereferences
    if (sig == X64_SIGSEGV) {
        // Check if ANY key registers are NULL or very low (< 64KB)
        int has_null_regs = 0;
        
        // Check common NULL register patterns
        if (R_RAX < 0x10000) has_null_regs = 1;
        if (R_RDI < 0x10000) has_null_regs = 1;
        if (R_RSI < 0x10000) has_null_regs = 1;
        if (R_RBX < 0x10000) has_null_regs = 1;
        
        // Also check if RIP is in Wine code range (stronger indicator)
        uintptr_t rip = (uintptr_t)R_RIP;
        int is_wine_code = (rip >= 0x7b000000 && rip < 0x7c000000);

        // OR if fault address is a known Wine crash address
        int is_wine_crash = (fault_addr == 0x049D1E40 || fault_addr == 0x049D1E48);
        
        if (has_null_regs || is_wine_code || is_wine_crash) {
            init_safe_zone();
            
            // === PROTECT CRITICAL REGISTERS ===
            // Save original values of registers we should NEVER modify
            uintptr_t save_rsp = (uintptr_t)R_RSP;
            uintptr_t save_rbp = (uintptr_t)R_RBP;
            uintptr_t save_rip = (uintptr_t)R_RIP;
            // === END PROTECT ===
            
            int fixed = 0;
            
            // Fix all NULL or low-value registers
            #define FIX_NULL_REG(REG) \
                if (REG < 0x10000) { \
                    REG = (uintptr_t)global_safe_zone; \
                    fixed++; \
                }
            
            FIX_NULL_REG(R_RAX);
            FIX_NULL_REG(R_RDI);
            FIX_NULL_REG(R_RBX);
            FIX_NULL_REG(R_RCX);
            FIX_NULL_REG(R_RDX);
            FIX_NULL_REG(R_RSI);
            
            // === RESTORE CRITICAL REGISTERS ===
            // Ensure we never accidentally modified these
            R_RSP = save_rsp;
            R_RBP = save_rbp;
            R_RIP = save_rip;
            // === END RESTORE ===
            
            if (fixed > 0) {
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[NULL_REG_FIX] Fixed %d NULL register(s) at RIP=0x%lx (Wine=%d), RAX=%p RDI=%p\n", 
                           fixed, rip, is_wine_code, (void*)R_RAX, (void*)R_RDI);
                }
                
                mark_exception_handled(fault_addr, (uintptr_t)pc);
                relockMutex(Locks);
                return;
            }
        }
    }

    if (current_rip == 0x006E686E || current_rip == 0x0047FB6F) {
        if(!engine_dummy_zone)
            engine_dummy_zone = box_calloc(1, 786432);
        if(!engine_dummy_zone) {
            FILE* f = fopen("/sdcard/box64_alloc_failed.txt", "a");
            if(f) { fprintf(f, "[ALLOC_FAIL] box_calloc(786432) NULL\n"); fclose(f); }
            engine_dummy_zone = mmap(NULL, 786432, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        }
        if(engine_dummy_zone) *(uint32_t*)engine_dummy_zone = engine_zone_magic;
        uint32_t cur_magic = engine_dummy_zone ? *(uint32_t*)engine_dummy_zone : 0;
        if(engine_dummy_zone && cur_magic != engine_zone_magic) {
            FILE* f2 = fopen("/sdcard/box64_dummy_zone_write.txt", "a");
            if(f2) { fprintf(f2, "[WRITE_DETECTED] magic_old=0x%08x magic_new=0x%08x\n", engine_zone_magic, cur_magic); fclose(f2); }
            engine_zone_magic = cur_magic;
        }

        R_RAX = (uintptr_t)engine_dummy_zone;

        // Loop detection and instruction skip
        static __thread uintptr_t last_bridge_rip = 0;
        static __thread int bridge_loop_count = 0;

        if (last_bridge_rip == current_rip) {
            bridge_loop_count++;
            if (bridge_loop_count > 5) {
                R_RIP += 5;
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[BRIDGE_SKIP] Loop at 0x%lx, advanced RIP to 0x%lx\n",
                        current_rip, (uintptr_t)R_RIP);
                }
                bridge_loop_count = 0;
                last_bridge_rip = 0;
            }
        } else {
            last_bridge_rip = current_rip;
            bridge_loop_count = 1;
        }
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[FIX_LOG] Bridge enabled at 0x%lx, RAX=0x%lx\n", current_rip, (uintptr_t)R_RAX);
        }
        bridge_call_counter++;
        if(bridge_call_counter % 10000 == 0) {
            FILE* f = fopen("/sdcard/box64_memory_usage.txt", "a");
            if(f) {
                FILE* status = fopen("/proc/self/maps", "r"); // Should be /proc/self/status but maps works for basic check
                if(status) {
                    char line[256];
                    while(fgets(line, sizeof(line), status)) {
                        if(strstr(line, "VmSize") || strstr(line, "VmRSS"))
                            fprintf(f, "[%d] %s", bridge_call_counter, line);
                    }
                    fclose(status);
                }
                fclose(f);
            }
        }
        relockMutex(Locks);
        return;
    } else if (current_rip == 0x006E686E || current_rip == 0x0047FB6F) { // Logic check failure log
         if (trace_fd >= 0) {
            dprintf(trace_fd, "[FIX_LOG_FAIL] Matched RIP 0x%lx but failed conditions?\n", current_rip);
        }
    }

    if(info->si_code == SEGV_ACCERR && engine_dummy_zone) {
        uintptr_t base = (uintptr_t)engine_dummy_zone;
        uintptr_t end = base + 786432;
        if(fault_addr >= base && fault_addr < end) {
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[FIX_LOG] Dummy zone access offset=0x%lx | Fault=0x%lx | PC=0x%lx\n",
                        fault_addr - base, fault_addr, (uintptr_t)pc);
            }
            R_RAX = 0;
            relockMutex(Locks);
            return;
        } else {
             if (trace_fd >= 0) {
                dprintf(trace_fd, "[FIX_LOG_FAIL] SEGV_ACCERR + DummyZone but addr 0x%lx not in range [0x%lx-0x%lx]\n", 
                    fault_addr, base, end);
            }
        }
    }

    // Check if this is code execution fault (PC == Fault) 
    if(fault_addr == (uintptr_t)pc) { 
        // This is trying to EXECUTE, not just access 
        // Add EXEC permission 
        
        size_t page_size = getpagesize(); 
        void* page_base = (void*)(fault_addr & ~(page_size - 1)); 
        
        if(memExist((uintptr_t)page_base)) { 
            uint32_t old_prot = getProtection((uintptr_t)page_base); 
            
            if(!(old_prot & PROT_EXEC)) { 
                mprotect(page_base, page_size, old_prot | PROT_EXEC); 
                
                if(trace_fd >= 0) { 
                    dprintf(trace_fd, "[EXEC_FIX_ACCERR] Added EXEC at 0x%lx | PC=Fault=0x%lx\n", 
                            (uintptr_t)page_base, fault_addr); 
                } 
                
                // Mark as handled
                mark_exception_handled(fault_addr, fault_addr);
                relockMutex(Locks); 
                return; 
            } 
        } else { 
            // Not mapped - map with EXEC 
            void* result = mmap(page_base, page_size, PROT_READ | PROT_EXEC, 
                            MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0); 
            
            if(result != MAP_FAILED && trace_fd >= 0) { 
                dprintf(trace_fd, "[EXEC_MAP_ACCERR] Mapped RX at 0x%lx | PC=Fault=0x%lx\n", 
                        (uintptr_t)page_base, fault_addr); 
            } 
            
            // Mark as handled
            mark_exception_handled(fault_addr, fault_addr);
            relockMutex(Locks); 
            return; 
        } 
    } 
    if(info->si_code == SEGV_ACCERR && fault_addr >= 0x076a0000 && fault_addr < 0x076b0000) {
        size_t page_size_76a = getpagesize();
        void* page_base_76a = (void*)(fault_addr & ~(page_size_76a - 1));
        int exist_76a = memExist((uintptr_t)page_base_76a);
        if (!exist_76a) {
            void* r_76a = mmap(page_base_76a, page_size_76a, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
            if (r_76a != MAP_FAILED) {
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[SEH_BRIDGE] MAP RW at 0x%lx | Fault=0x%lx | PC=0x%lx\n",
                            (uintptr_t)page_base_76a, fault_addr, (uintptr_t)pc);
                }
                relockMutex(Locks);
                return;
            } else {
                 if (trace_fd >= 0) {
                    dprintf(trace_fd, "[SEH_BRIDGE_FAIL] mmap FAILED at 0x%lx | Fault=0x%lx\n",
                            (uintptr_t)page_base_76a, fault_addr);
                }
            }
        } else {
            uint32_t prot_76a = getProtection((uintptr_t)page_base_76a);
            if ((prot_76a & (PROT_READ | PROT_WRITE)) != (PROT_READ | PROT_WRITE)) {
                mprotect(page_base_76a, page_size_76a, PROT_READ | PROT_WRITE);
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[SEH_BRIDGE] PROTECT RW at 0x%lx | old_prot=0x%x | Fault=0x%lx | PC=0x%lx\n",
                            (uintptr_t)page_base_76a, prot_76a, fault_addr, (uintptr_t)pc);
                }
                relockMutex(Locks);
                return;
            } else {
                 if (trace_fd >= 0) {
                    dprintf(trace_fd, "[SEH_BRIDGE_INFO] Already RW at 0x%lx | Fault=0x%lx\n",
                            (uintptr_t)page_base_76a, fault_addr);
                }
            }
        }
    }
    if(info->si_code == SEGV_ACCERR && fault_addr >= 0x077a0000 && fault_addr < 0x077b0000) {
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[SKIP_77A] SIG=%d | Fault=0x%lx | PC=0x%lx\n", sig, fault_addr, (uintptr_t)pc);
        }
        relockMutex(Locks);
        return;
    }

    if(fault_addr >= 0xC0000000 && fault_addr < 0xD0000000) {
        // .NET JIT code cache range
        size_t page_size = getpagesize();
        void* page_base = (void*)(fault_addr & ~(page_size - 1));
        
        if(memExist((uintptr_t)page_base)) {
            uint32_t old_prot = getProtection((uintptr_t)page_base);
            
            if(!(old_prot & PROT_EXEC)) {
                mprotect(page_base, page_size, old_prot | PROT_EXEC);
                
                if(trace_fd >= 0) {
                    dprintf(trace_fd, "[DOTNET_JIT_EXEC] Added EXEC at 0x%lx | RIP=0x%lx\n", 
                            (uintptr_t)page_base, fault_addr);
                }
                
                relockMutex(Locks);
                return;
            }
        } else {
            // Not mapped - map with EXEC
            void* result = mmap(page_base, page_size, PROT_READ | PROT_EXEC, 
                               MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
            
            if(result != MAP_FAILED && trace_fd >= 0) {
                dprintf(trace_fd, "[DOTNET_JIT_MAP] Mapped RX at 0x%lx | RIP=0x%lx\n", 
                        (uintptr_t)page_base, fault_addr);
            }
            
            relockMutex(Locks);
            return;
        }
    }
    if(sig == SIGBUS && info->si_code == BUS_ADRALN && fault_addr >= 0x7bf00000 && fault_addr < 0x7c000000) {
        static __thread int wine_unaligned_count = 0;
        wine_unaligned_count++;
        if (trace_fd >= 0) {
             if (wine_unaligned_count <= 5) {
                dprintf(trace_fd, "[WINE_BUS_SKIP] Fault=0x%lx | RIP=0x%lx | count=%d\n", fault_addr, (uintptr_t)pc, wine_unaligned_count);
             } else {
                 dprintf(trace_fd, "[WINE_BUS_SKIP_SUPPRESS] Count=%d\n", wine_unaligned_count);
             }
        }
        relockMutex(Locks);
        return;
    } else if (sig == SIGBUS && info->si_code == BUS_ADRALN) {
         if (trace_fd >= 0) {
            dprintf(trace_fd, "[WINE_BUS_FAIL] Unaligned access outside range: 0x%lx\n", fault_addr);
        }
    }
    // Stack Exhaustion Detection removed (integrated into main loop)

    // --- MAIN RESCUE LOGIC ---
    
    // --- NULL POINTER GUARD (WRITE REDIRECTION) ---
    // If the game tries to access NULL (or low address), checks registers.
    // If we find a 0 register that matches the fault, we redirect it to SafeZone.
    // This breaks the "infinite loop" where Wine catches the fault but doesn't fix the register.
    // Extended to catch faults up to 16MB (0x1000000) to handle offsets like NULL+0x18c
    if ((sig == X64_SIGSEGV || sig == SIGBUS) && fault_addr < 0x1000000) {
        init_safe_zone();
        int modified = 0;
        
        // Helper macro to check and fix register
        // Fix if register is 0 OR if it's a small value (< 0x10000) that likely caused the fault
        #define CHECK_FIX_REG(REG) \
            if (REG == 0 || REG < 0x10000) { \
                REG = (uintptr_t)global_safe_zone; \
                modified = 1; \
            }

        // Only fix if SafeZone is available
        if (global_safe_zone) {
            CHECK_FIX_REG(R_RAX);
            CHECK_FIX_REG(R_RBX);
            CHECK_FIX_REG(R_RCX);
            CHECK_FIX_REG(R_RDX);
            CHECK_FIX_REG(R_RSI);
            CHECK_FIX_REG(R_RDI);
            CHECK_FIX_REG(R_R8);
            CHECK_FIX_REG(R_R9);
            CHECK_FIX_REG(R_R10);
            CHECK_FIX_REG(R_R11);
            CHECK_FIX_REG(R_R12);
            CHECK_FIX_REG(R_R13);
            CHECK_FIX_REG(R_R14);
            CHECK_FIX_REG(R_R15);
        }
        
        if (modified) {
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[NULL_GUARD] Redirected low-value register(s) to SafeZone (%p) to fix Fault=0x%lx\n", 
                        global_safe_zone, fault_addr);
            }
            // Mark as handled so Wine doesn't see it (or sees the fixed instruction)
            mark_exception_handled(fault_addr, (uintptr_t)pc);
            relockMutex(Locks);
            return; // Retry instruction with new register values
        }
    }

    /* WINE exception redirection removed */

    // === BETTER RETURN ADDRESS VALIDATION === 
    // Check if this looks like a real return address by checking for CALL before it 
    
    int is_likely_return_address(uint32_t ret_addr) { 
        // Must be in valid code range 
        if (ret_addr < 0x401000 || ret_addr >= 0xB00000) { 
            return 0; 
        } 
        
        // Check bytes BEFORE the return address for CALL instruction 
        // CALL is typically 5 bytes: E8 XX XX XX XX (relative call) 
        // Or 2 bytes: FF XX (indirect call) 
        // Return address points AFTER the CALL 
        
        if (ret_addr < 5) return 0;  // Can't check before start of memory 
        
        uint8_t* code = (uint8_t*)(uintptr_t)(ret_addr - 5); 
        
        // Check for CALL rel32 (E8) 
        if (code[0] == 0xE8) { 
            return 1;  // Likely a return from CALL 
        } 
        
        // Check for CALL r/m32 (FF /2) - 2 bytes before 
        code = (uint8_t*)(uintptr_t)(ret_addr - 2); 
        if (code[0] == 0xFF && ((code[1] & 0x38) == 0x10)) { 
            return 1;  // Likely a return from indirect CALL 
        } 
        
        // Check for CALL r/m32 with ModR/M - 3-7 bytes before 
        // This is more complex, but common patterns: 
        code = (uint8_t*)(uintptr_t)(ret_addr - 3); 
        if (code[0] == 0xFF && ((code[1] & 0x38) == 0x10)) { 
            return 1; 
        } 
        
        code = (uint8_t*)(uintptr_t)(ret_addr - 6); 
        if (code[0] == 0xFF && ((code[1] & 0x38) == 0x10)) { 
            return 1; 
        } 
        
        // If we can't find a CALL instruction, it's probably not a return address 
        return 0; 
    }

    // Conditions that trigger stack-scan rescue:
    //   1. Null pointer / low address faults
    //   2. High address faults (> 32-bit range)
    //   3. SIGILL - illegal instruction (untranslated code)
    //   4. SIGBUS - alignment fault
    //   5. SEGV_MAPERR - address not mapped at all
    //   6. NEW: SEGV_ACCERR where the fault address does NOT match
    //          the instruction pointer - meaning the CPU executed valid code
    //          but that code tried to access an invalid address.
    //          Wine cannot recover from this on its own.
    int should_rescue = ((sig == X64_SIGSEGV || sig == X64_SIGILL || sig == SIGBUS) && (
        sig == X64_SIGILL || sig == SIGBUS ||
        fault_addr < 0x10000 ||                    // null / low
        fault_addr > 0x7FFFFFFF ||                 // high / bogus
        info->si_code == SEGV_MAPERR ||            // unmapped
        (info->si_code == SEGV_ACCERR && (uintptr_t)pc != fault_addr)  // data access, not exec
    ));

    if (!should_rescue && (sig == X64_SIGSEGV || sig == X64_SIGILL || sig == SIGBUS) && (addr)) {
         if(trace_fd >= 0) {
            dprintf(trace_fd, "[UNIVERSAL_PATCH_SKIP] Not triggering rescue. Sig=%d Fault=0x%lx si_code=%d\n", sig, fault_addr, info->si_code);
        }
    }

    if (should_rescue) {
    
    // --- PEEK-BEHIND: Handle MOV/LDR -> RAX ---
    if ((sig == X64_SIGSEGV || sig == SIGBUS) && info->si_code == SEGV_ACCERR) {
         int mov_len = get_mov_rax_length(x64pc);
         if (mov_len > 0) {
             if(trace_fd >= 0) {
                 dprintf(trace_fd, "[PEEK_BEHIND] Detected MOV/LDR -> RAX at %p (len=%d). Skipping...\n", (void*)x64pc, mov_len);
             }
             
             init_safe_zone();
             if (global_safe_zone) {
                 R_RAX = (uintptr_t)global_safe_zone;
                 R_EAX = (uint32_t)(uintptr_t)global_safe_zone;
             } else {
                 R_RAX = 1; R_EAX = 1;
             }
             
             // Skip instruction
             R_RIP = x64pc + mov_len;
             
             // Mark as handled
             mark_exception_handled(fault_addr, x64pc);
             
             // Resume execution
             if(emu && emu->jmpbuf) {
                 relockMutex(Locks);
                 #ifdef ANDROID
                 siglongjmp(*(JUMPBUFF*)emu->jmpbuf, 1);
                 #else 
                 siglongjmp(emu->jmpbuf, 1); 
                 #endif 
             }
             
             relockMutex(Locks);
             return;
         }
    }

    // Log why we entered rescue logic
    if(trace_fd >= 0) {
        dprintf(trace_fd, "[RESCUE_START] Triggered by: %s\n", 
            (sig == X64_SIGILL) ? "SIGILL" :
            (sig == SIGBUS) ? "SIGBUS" :
            (fault_addr < 0x10000) ? "NULL/Low Ptr" :
            (fault_addr > 0x7FFFFFFF) ? "High/Bogus Ptr" :
            (info->si_code == SEGV_MAPERR) ? "SEGV_MAPERR" :
            "SEGV_ACCERR (Data Access)");
    }

    // Guard page hit: SEGV_ACCERR on zero-permission page = Windows guard page violation. 
    // Wine/heap manager must handle this, NOT rescue. 
    if(info->si_code == SEGV_ACCERR) { 
        uint32_t fault_prot = getProtection(fault_addr); 
        if(fault_prot == 0) { 
            // Windows guard page semantics: first access consumes the guard. 
            // mprotect the page to rwxp so the CPU retry succeeds. 
            // The surrounding heap pages are rwxp; match them. 
            size_t gp_size  = getpagesize(); 
            void*  gp_base  = (void*)(fault_addr & ~(uintptr_t)(gp_size - 1)); 
            int    mp_ret   = mprotect(gp_base, gp_size, PROT_READ | PROT_WRITE | PROT_EXEC); 
    
            if(trace_fd >= 0) { 
                dprintf(trace_fd, "[GUARD_PAGE] fault=0x%lx base=%p size=0x%zx mprotect=%d" 
                            " - guard consumed, retrying\n", 
                            fault_addr, gp_base, gp_size, mp_ret); 
            } 
            // Mark as handled so Wine doesn't propagate it
            mark_exception_handled(fault_addr, (uintptr_t)pc);
            relockMutex(Locks); 
            return;   // CPU retries the load/store, now succeeds (page is rwxp) 
        } 
        
        // Detect writes to Wine NLS files (r-xs) which block heap expansion
        // We now handle ANY NLS file mapping, not just the one at 0x04400000
        
        // ADD DEBUG: Log what protection we actually see 
        if(trace_fd >= 0) { 
            dprintf(trace_fd, "[NLS_DEBUG] SEGV_ACCERR at 0x%lx | fault_prot=0x%x | " 
                       "READ=%d WRITE=%d EXEC=%d\n", 
                    fault_addr, fault_prot, 
                    !!(fault_prot & PROT_READ), 
                    !!(fault_prot & PROT_WRITE), 
                    !!(fault_prot & PROT_EXEC)); 
        } 

        // --- SOLUTION 1: AGGRESSIVE MEMORY DEFRAGMENTATION ---
        // The game requires a continuous 7MB writable buffer at 0x04400000.
        // Wine's ASLR fragments this with NLS files, DLLs (symsrv.dll), and heap chunks.
        // We detect the first write to this region and aggressively remap the ENTIRE range.
        static int fragmentation_fixed = 0;
        if(!fragmentation_fixed && fault_addr >= 0x04400000 && fault_addr < 0x04B00000) {
            void* target_base = (void*)0x04400000;
            size_t target_size = 0x00700000; // 7MB
            
            if(trace_fd >= 0) dprintf(trace_fd, "[DEFRAG] Critical fragmentation detected at 0x%lx. Checking the data before Executing Solution 1 (Aggressive Remap)...\n", fault_addr);

            // === CHECK IF REGION ALREADY HAS DATA ===
            int has_data = 0;
            for (uintptr_t check = 0x04400000; check < 0x04B00000; check += 4096) {
                if (memExist(check)) {
                    // Sample 10 locations to see if non-zero
                    uint32_t* ptr = (uint32_t*)check;
                    for (int i = 0; i < 10 && memExist((uintptr_t)(ptr + i)); i++) {
                        if (ptr[i] != 0) {
                            has_data = 1;
                            break;
                        }
                    }
                    if (has_data) break;
                }
            }
            
            if (has_data) {
                // Region already has data - just fix permissions, don't remap!
                if(trace_fd >= 0) dprintf(trace_fd, "[DEFRAG] Region has data, fixing permissions only\n");
                mprotect(target_base, target_size, PROT_READ | PROT_WRITE | PROT_EXEC);
                fragmentation_fixed = 1;
                mark_exception_handled(fault_addr, (uintptr_t)pc);
                relockMutex(Locks);
                return;
            } else {

            
                // Otherwise do the full remap (original code)
                if(trace_fd >= 0) dprintf(trace_fd, "[DEFRAG] Region is empty, executing full remap\n");
                munmap(target_base, target_size);

                // 1. Unmap EVERYTHING in the target range (NLS, DLLs, heap, etc.)
                // This clears the path for a continuous allocation.
                munmap(target_base, target_size);

                // 2. Remap as a single, continuous, writable anonymous block
                void* r = mmap(target_base, target_size, 
                            PROT_READ | PROT_WRITE | PROT_EXEC, 
                            MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);

                if(r != MAP_FAILED) {
                    fragmentation_fixed = 1;
                    if(trace_fd >= 0) dprintf(trace_fd, "[DEFRAG] SUCCESS: 0x04400000-0x04B00000 (7MB) is now continuous writable RAM.\n");
                    
                    // Mark as handled so Wine doesn't propagate it
                    mark_exception_handled(fault_addr, (uintptr_t)pc);

                    relockMutex(Locks);
                    return; // Retry instruction
                } else {
                    if(trace_fd >= 0) dprintf(trace_fd, "[DEFRAG] FAILED: mmap errno=%d\n", errno);
                    // Fall through to standard NLS handler if this fails
                }
            }
        }

        // --- THE ATOMIC NLS DISSOLVER (FINAL) --- 
        // Dynamic NLS Detection (No hardcoded ranges) 
        char path[512] = ""; 
        uintptr_t map_start = 0, map_end = 0; 
        
        if(get_map_info(fault_addr, &map_start, &map_end, path)) { 
            if(strstr(path, ".nls")) { 
                size_t map_size = map_end - map_start; 
                
                if(trace_fd >= 0) dprintf(trace_fd, "[NLS_FIX] Collision detected on %s at 0x%lx\n", path, fault_addr); 
    
                void* scratch = malloc(map_size); 
                if(scratch) { 
                    memcpy(scratch, (void*)map_start, map_size); // 1. Save original NLS data 
                    
                    // 2. ATOMIC SWAP: Destroy the read-only file mapping and replace with writable RAM 
                    // Explicitly unmap first to clear the file-backed status and read-only flags
                    munmap((void*)map_start, map_size); 
                    
                    void* r = mmap((void*)map_start, map_size, PROT_READ|PROT_WRITE|PROT_EXEC, 
                                   MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, -1, 0); 
        
                    if(r != MAP_FAILED) { 
                        memcpy((void*)map_start, scratch, map_size); // 3. Restore NLS data into writable RAM 
                        if(trace_fd >= 0) dprintf(trace_fd, "[NLS_OK] %lx is now writable RAM\n", map_start); 
                        
                        // Retry the write 
                        if(trace_fd >= 0) { 
                            dprintf(trace_fd, "[NLS_WRITE_RETRY] Retrying write at 0x%lx\n", fault_addr); 
                        } 
                    } else { 
                        if(trace_fd >= 0) dprintf(trace_fd, "[NLS_FIX] Critical Failure: mmap errno=%d\n", errno); 
                    } 
                    free(scratch); 
                } else { 
                     if(trace_fd >= 0) dprintf(trace_fd, "[NLS_FIX] Malloc failed for scratch buffer (size %zx)\n", map_size); 
                } 
                relockMutex(Locks); 
                return; // Instruction will now retry and succeed 
            } 
        }
    } 

    // === RESCUE LOOP DETECTION  === 
    static __thread int rescue_depth = 0; 
    static __thread uintptr_t rescue_last_rip = 0; 
    static __thread int rescue_rip_count = 0; 
    
    // Check for nested RESCUE 
    if (rescue_depth > 0) { 
        if (trace_fd >= 0) { 
            dprintf(trace_fd, "[RESCUE_NESTED] Depth=%d, aborting nested rescue\n", rescue_depth); 
        } 
        R_RIP += 5;  // Skip instruction 
        relockMutex(Locks); 
        return; 
    } 
    
    // Check for same RIP crashing repeatedly 
    if (current_rip == rescue_last_rip) { 
        rescue_rip_count++; 
        if (rescue_rip_count >= 10) { 
            if (trace_fd >= 0) { 
                dprintf(trace_fd, "[RESCUE_ABORT] RIP 0x%lx crashed %d times, skipping\n", 
                       current_rip, rescue_rip_count); 
            } 
            R_RIP += 5; 
            rescue_rip_count = 0; 
            rescue_last_rip = 0; 
            relockMutex(Locks); 
            return; 
        } 
    } else { 
        rescue_last_rip = current_rip; 
        rescue_rip_count = 1; 
    } 
    
    rescue_depth++; 
    // === END RESCUE LOOP DETECTION === 

    uint32_t *esp = (uint32_t*)(uintptr_t)R_RSP;
    uint32_t ret_addr = 0;
    int stack_offset = -1;

    uintptr_t esp_base = (uintptr_t)R_RSP;
    int page_size = getpagesize();
    int max_scan = 256; // Reduced back to original working value
    if(trace_fd >= 0) {
        dprintf(trace_fd, "\n[CRASH] SIG=%d | si_code=%d | Fault=0x%lx | PC=0x%lx | x86_RIP=0x%08x. Scanning stack...\n", 
                sig, info->si_code, fault_addr, (uintptr_t)pc, (uint32_t)R_RIP);
    }
    for (int i = 0; i < max_scan; i++) {
        // === SAFE STACK READ ===
        // Ensure the stack address is valid before reading!
        if (!memExist((uintptr_t)&esp[i])) {
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[RESCUE_STOP] Stack memory at %p (offset %d) is not mapped! Stopping scan.\n", &esp[i], i);
            }
            break; // Stop scanning, stack is dead
        }
        
        uint32_t candidate = esp[i];
        
        // Gate 1: Address range 
        if(candidate < 0x00400000 || candidate > 0x20000000) continue; 
        
        // Gate 2: Alignment 
        if((candidate & 3) != 0) continue; 
        
        // Gate 3: Must be already mapped AND executable 
        // We reject heap (rw-p) and rodata (r--p) to prevent executing data. 
        uint32_t cand_prot = 0; 
        if(!memExist(candidate)) { 
            if(trace_fd >= 0) dprintf(trace_fd, "[RESCUE_SKIP] RET=0x%08x not mapped\n", candidate); 
            continue; 
        } 
        cand_prot = getProtection(candidate); 
        
        // Must be both readable AND executable 
        if(!(cand_prot & PROT_READ) || !(cand_prot & PROT_EXEC)) { 
            if(trace_fd >= 0) { 
                dprintf(trace_fd, "[RESCUE_SKIP] RET=0x%08x no exec (prot=0x%02x)\n", candidate, cand_prot); 
            } 
            continue; 
        } 
        
        // Gate 4: Not all zeros 
        uint8_t* code = (uint8_t*)(uintptr_t)candidate; 
        int zeros = 0; 
        for(int z = 0; z < 16; z++) { 
            if(memExist((uintptr_t)&code[z]) && code[z] == 0x00) zeros++; 
        } 
        if(zeros >= 8) { 
            if(trace_fd >= 0) { 
                dprintf(trace_fd, "[RESCUE_SKIP] RET=0x%08x mostly zeros (%d/16)\n", candidate, zeros); 
            } 
            continue; 
        } 
        
        // Gate 5: First byte must be a recognizable x86 opcode 
        
        // Gate 5.5: Explicit Code Range Check (Reject Data Sections)
        if (!is_valid_code_range(candidate)) {
             if (trace_fd >= 0) {
                 dprintf(trace_fd, "[RESCUE_REJECT] 0x%x not in valid code range (data section?)\n", candidate);
             }
             continue;
        }

        // Gate 5.6: CALL Instruction Check (Ensure it's a return address)
        if (!is_likely_return_address(candidate)) {
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[RESCUE_SKIP_NOCALL] 0x%x no CALL before it\n", candidate);
            }
            continue;
        }

        uint8_t b = code[0]; 
        int looks_valid = ( 
            // PUSH family 
            b == 0x50 || b == 0x51 || b == 0x52 || b == 0x53 || 
            b == 0x54 || b == 0x55 || b == 0x56 || b == 0x57 || 
            b == 0x6a || b == 0x68 || 
            // REX prefixes (40-4F) 
            (b >= 0x40 && b <= 0x4f) || 
            // Two-byte escape and common prefixes 
            b == 0x0f || b == 0x66 || b == 0xf2 || b == 0xf3 || 
            // MOV/arithmetic 
            b == 0x89 || b == 0x8b || b == 0x8d || 
            b == 0x83 || b == 0x85 || 
            b == 0x01 || b == 0x03 || b == 0x2b || b == 0x2d || 
            b == 0x31 || b == 0x33 || 
            // CALL / JMP 
            b == 0xe8 || b == 0xe9 || b == 0xeb || b == 0xff || 
            // RET 
            b == 0xc3 || b == 0xc2 || 
            // NOP / TEST / CMP 
            b == 0x90 || b == 0x85 || b == 0x3b || b == 0x39 
        ); 
        
        if(!looks_valid) { 
            if(trace_fd >= 0) { 
                dprintf(trace_fd, "[RESCUE_SKIP] RET=0x%08x invalid first byte 0x%02x\n", candidate, b); 
            } 
            continue; 
        } 
        
        // Gate 6: Reject if first 8 bytes contain POPFD/POPF (0x9d), PUSHFD (0x9c), 
        // or IRET (0xcf). These are never valid at a function return point and 
        // will corrupt EFLAGS (POPFD sets TF if bit 8 of the popped stack value is set). 
        { 
            int gate6_fail = 0; 
            for(int g = 0; g < 8 && memExist((uintptr_t)&code[g]); g++) { 
                uint8_t gb = code[g]; 
                if(gb == 0x9d || gb == 0x9c || gb == 0xcf) { 
                    if(trace_fd >= 0) 
                        dprintf(trace_fd, "[RESCUE_SKIP] RET=0x%08x gate6: 0x%02x at byte[%d]\n", 
                                candidate, gb, g); 
                    gate6_fail = 1; 
                    break; 
                } 
            } 
            if(gate6_fail) continue; 
        } 
        
        // Passed all gates 
        ret_addr = candidate; 
        stack_offset = i; 
        if(trace_fd >= 0) { 
            dprintf(trace_fd, "[RESCUE_ACCEPT] RET=0x%08x first=0x%02x zeros=%d\n", candidate, b, zeros); 
            dprintf(trace_fd, "[CORRUPTION_CHECK] Thread %d jumping to 0x%x. First bytes: %02x %02x %02x\n", 
                getpid(), candidate, code[0], code[1], code[2]); 
        } 
        break;
    }

        if(stack_offset == -1) {
            static __thread uintptr_t scan_last_rip = 0;
            static __thread uintptr_t scan_last_esp = 0;
            static __thread uintptr_t scan_last_fault = 0;
            static __thread int scan_repeat = 0;
            int repeating = (scan_last_rip == (uintptr_t)R_RIP) &&
                            (scan_last_esp == (uintptr_t)R_RSP) &&
                            (fault_addr == scan_last_fault + 4);
            if(repeating) {
                scan_repeat++;
            } else {
                scan_last_rip = (uintptr_t)R_RIP;
                scan_last_esp = (uintptr_t)R_RSP;
                scan_last_fault = fault_addr;
                scan_repeat = 1;
            }
            if(scan_repeat >= 20) {
                if(trace_fd >= 0) {
                    dprintf(trace_fd, "[SCAN_SUPPRESS] Repeat=%d | Suppressing rescue and passing to Wine\n", scan_repeat);
                }
                rescue_depth--;
                relockMutex(Locks);
                return;
            }
            if(trace_fd >= 0) {
                dprintf(trace_fd, "[SCAN_FAILED] SIG=%d | Fault=0x%lx | ESP=0x%lx | si_code=%d | Thread=%d | x86_RIP=0x%08x\n",
                        sig, fault_addr, (uintptr_t)R_RSP, info->si_code, GetTID(), (uint32_t)R_RIP);
                int dump_slots = (scan_repeat <= 4) ? max_scan : 16;
                dprintf(trace_fd, "              Stack dump (%d slots):\n", dump_slots);
                for(int j = 0; j < dump_slots; j++) {
                    dprintf(trace_fd, "              ESP[%2d] = 0x%08x\n", j, esp[j]);
                }
            }
            int chosen_idx = -1;
            for(int k=0; k<16; ++k) {
                uint32_t candidate = esp[k];
                if (candidate >= 0x7bf40000 && candidate <= 0x7bfeffff) {
                    chosen_idx = k;
                    break;
                }
            }
            if(chosen_idx != -1) {
                uint32_t ret_addr2 = esp[chosen_idx];
                
                // --- SAFE ZONE RETURN VALUE ---
                init_safe_zone();
                if (global_safe_zone) {
                    R_RAX = (uintptr_t)global_safe_zone;
                    R_EAX = (uint32_t)(uintptr_t)global_safe_zone;
                } else {
                    R_RAX = 1; R_EAX = 1;
                }
                
                if (trace_fd >= 0) {
                    dprintf(trace_fd, "[RESCUE_RAX] Set RAX=%p (SafeZone) for rescued function\n", (void*)R_RAX);
                }
                
                // --- STUB REDIRECTION ---
                void* stub = generate_rescue_stub((uintptr_t)ret_addr2);
                if (stub) {
                    ret_addr2 = (uint32_t)(uintptr_t)stub;
                    if (trace_fd >= 0) {
                        dprintf(trace_fd, "[RESCUE_STUB] Redirecting to x86 stub at %p -> Target %p\n", stub, (void*)(uintptr_t)esp[chosen_idx]);
                    }
                }
                // -----------------------------
                
                R_RSP = (uintptr_t)&esp[chosen_idx + 1];
                #ifdef __aarch64__
                R_RIP = (uint64_t)ret_addr2;
                #endif
                if(trace_fd >= 0) {
                    dprintf(trace_fd, "[NTDLL_TRUST] Using ESP[%d]=0x%08x. New RSP=0x%lx\n", chosen_idx, esp[chosen_idx], (uintptr_t)R_RSP);
                }
                
                // Use siglongjmp to resume interpreter at new RIP.
                if(emu && emu->jmpbuf) {
                    rescue_depth--;
                    relockMutex(Locks);
                    #ifdef ANDROID
                    siglongjmp(*(JUMPBUFF*)emu->jmpbuf, 1);   // 1 = resume interpreter 
                    #else 
                    siglongjmp(emu->jmpbuf, 1); 
                    #endif 
                    // siglongjmp does not return 
                }
                
                rescue_depth--;
                relockMutex(Locks);
                return;
            } else {
                if(trace_fd >= 0) {
                    dprintf(trace_fd, "[SCAN_FAILED_NO_LIFT] No candidate; skipping instruction to break loop.\n");
                    int page_ok = memExist(fault_addr) && (getProtection((uintptr_t)fault_addr) & PROT_READ);
                    if(page_ok) {
                        uint8_t* p = (uint8_t*)(uintptr_t)fault_addr;
                        dprintf(trace_fd, "BYTES[PC]: ");
                        for(int i=0;i<32;i++) dprintf(trace_fd, "%02x", p[i]);
                        dprintf(trace_fd, "\n");
                    }
                    dprintf(trace_fd, "REGS: RIP=0x%lx RSP=0x%lx RAX=0x%lx\n", (uintptr_t)R_RIP, (uintptr_t)R_RSP, (uintptr_t)R_RAX);
                    uintptr_t old_rsp_val = R_RSP;
                    if(scan_repeat >= 10) {
                        if (trace_fd >= 0) {
                            dprintf(trace_fd, "[SCAN_SUPPRESS] Repeat=%d | Escalating with stack lift. Old RSP=0x%lx\n", scan_repeat, old_rsp_val);
                        }
                        
                        R_RSP = old_rsp_val + 0x100;
                        if (trace_fd >= 0) {
                            dprintf(trace_fd, "[SCAN_LIFT] New RSP=0x%lx | Fault=0x%lx | PC=0x%lx\n", (uintptr_t)R_RSP, fault_addr, (uintptr_t)pc);
                        }
                        
                        #ifdef __aarch64__
                        // --- SAFE ZONE RETURN VALUE ---
                        init_safe_zone();
                        if (global_safe_zone) {
                            R_RAX = (uintptr_t)global_safe_zone;
                            R_EAX = (uint32_t)(uintptr_t)global_safe_zone;
                        } else {
                            R_RAX = 1; R_EAX = 1;
                        }

                        if (trace_fd >= 0) {
                            dprintf(trace_fd, "[RESCUE_RAX_LIFT] Set RAX=%p (SafeZone)\n", (void*)R_RAX);
                        }
                        // -----------------------------
                        
                        if(emu && emu->jmpbuf) { 
                            rescue_depth--;
                            relockMutex(Locks); 
                            #ifdef ANDROID
                            siglongjmp(*(JUMPBUFF*)emu->jmpbuf, 1); 
                            #else
                            siglongjmp(emu->jmpbuf, 1);
                            #endif
                        } 
                        #endif
                    }
                    else {
                        #ifdef __aarch64__
                        // --- SAFE ZONE RETURN VALUE ---
                        init_safe_zone();
                        if (global_safe_zone) {
                            uintptr_t sz = (uintptr_t)global_safe_zone;
                            int fixed = 0;
                            
                            // Fix all suspicious registers (0 or garbage > 0x70000000)
                            // This catches the register holding the garbage pointer causing the crash
                            #define FIX_REG(REG) \
                                if (REG == 0 || (REG > 0x70000000 && REG < 0x7FFFFFFFFFFF0000ULL)) { \
                                    REG = sz; \
                                    fixed++; \
                                }
                            
                            FIX_REG(R_RAX); FIX_REG(R_RBX); FIX_REG(R_RCX); FIX_REG(R_RDX);
                            FIX_REG(R_RSI); FIX_REG(R_RDI); FIX_REG(R_R8);  FIX_REG(R_R9);
                            FIX_REG(R_R10); FIX_REG(R_R11); FIX_REG(R_R12); FIX_REG(R_R13);
                            FIX_REG(R_R14); FIX_REG(R_R15);
                            
                            // Ensure RAX is set for return value
                            R_RAX = sz;
                            R_EAX = (uint32_t)sz;

                            if (trace_fd >= 0) {
                                dprintf(trace_fd, "[SCAN_FAILED_FIX] Fixed %d register(s) to SafeZone\n", fixed);
                            }
                        } else {
                            R_RAX = 1; R_EAX = 1;
                        }

                        // --- SKIP INSTRUCTION ---
                        // Advance RIP to skip the faulting instruction and prevent infinite loop
                        uintptr_t proposed_new_rip = R_RIP + 5; 

                        // === Fix 1: Validate RIP Before Instruction Skip === 
                        uintptr_t test_rip = proposed_new_rip; 
                        int prot = getProtection(test_rip);
                        if (memExist(test_rip) && (prot & PROT_READ)) { 
                            uint8_t* code = (uint8_t*)test_rip; 
                            int is_zeros = 1; 
                            for (int i = 0; i < 16; i++) { 
                                if (code[i] != 0x00) { 
                                    is_zeros = 0; 
                                    break; 
                                } 
                            } 
                            
                            if (is_zeros) { 
                                // Don't skip to zero-filled region 
                                if (trace_fd >= 0) {
                                    dprintf(trace_fd, "[INSTRUCTION_SKIP_ABORT] RIP 0x%lx contains all zeros, aborting skip\n", test_rip); 
                                }
                                // We're at the end of the handler anyway, let it crash naturally
                                rescue_depth--;
                                relockMutex(Locks);
                                return;
                            } 
                        } 

                        R_RIP = proposed_new_rip; 
                        
                        if (trace_fd >= 0) {
                            dprintf(trace_fd, "[INSTRUCTION_SKIP] Advanced RIP to 0x%lx\n", (uintptr_t)R_RIP);
                        }
                        // -----------------------------
                        
                        if(emu && emu->jmpbuf) { 
                            relockMutex(Locks); 
                            #ifdef ANDROID
                            siglongjmp(*(JUMPBUFF*)emu->jmpbuf, 1); 
                            #else
                            siglongjmp(emu->jmpbuf, 1);
                            #endif
                        } 
                        #endif
                    }
                }
                rescue_depth--;
                relockMutex(Locks);
                return;
            }
        } else {
            if(trace_fd >= 0) {
                dprintf(trace_fd, "[RESCUE_%d] SIG=%d (%s) | Fault=0x%lx | RET=0x%08x | si_code=%d | Thread=%d\n",
                        stack_offset, sig,
                        (sig == SIGBUS) ? "SIGBUS" : (sig == X64_SIGILL) ? "SIGILL" : "SIGSEGV",
                        fault_addr, ret_addr, info->si_code, GetTID());
            }

        }

        // --- SAFE ZONE RETURN VALUE ---
        init_safe_zone();
        if (global_safe_zone) {
            R_RAX = (uintptr_t)global_safe_zone;
            R_EAX = (uint32_t)(uintptr_t)global_safe_zone;
        } else {
            R_RAX = 1; R_EAX = 1;
        }

        // FORCE LOGGING (Use trace_fd)
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[RESCUE_RAX] Set RAX=%p (SafeZone) for rescued function\n", (void*)R_RAX);
        }
        // -----------------------------
        
        // --- STUB REDIRECTION (Approach A) ---
        // We use a stub to FORCE RAX to be the SafeZone value at the moment of return.
        // This is more reliable than just setting R_RAX in the context, as siglongjmp might restore registers.
        if (trace_fd >= 0) {
            dprintf(trace_fd, "[DEBUG_STUB] stub_req=0x%lx, global_safe_zone=%p\n", 
                   (uintptr_t)ret_addr, global_safe_zone);
        }
        void* stub = generate_rescue_stub((uintptr_t)ret_addr);
        if (stub) {
            ret_addr = (uint32_t)(uintptr_t)stub;
            
            if (trace_fd >= 0) {
                dprintf(trace_fd, "[RESCUE_STUB] Redirecting to x86 stub at %p -> Target %p\n", stub, (void*)(uintptr_t)esp[stack_offset]);
            }
        }
        // -----------------------------

        R_RSP = (uintptr_t)&esp[stack_offset + 1];
        R_RIP = (uint64_t)ret_addr;

        if(trace_fd >= 0) {
            dprintf(trace_fd, "[RESCUE_JUMP] RIP=0x%08x RSP=0x%lx via siglongjmp\n", 
                    ret_addr, (uintptr_t)R_RSP);
        }

        // Use siglongjmp to resume interpreter at new RIP.
        // Do NOT set uc_mcontext.pc to an x86 address — that makes the ARM64 CPU 
        // try to execute x86 bytes directly. 
        if(emu && emu->jmpbuf) {
            rescue_depth--;
            relockMutex(Locks);
            #ifdef ANDROID
            siglongjmp(*(JUMPBUFF*)emu->jmpbuf, 1);   // 1 = resume interpreter 
            #else 
            siglongjmp(emu->jmpbuf, 1); 
            #endif 
            // siglongjmp does not return 
        }

        // Fallback: if no jmpbuf, we cannot safely redirect in interpreter mode.
        // Pass to Wine and crash cleanly.
        rescue_depth--;
        relockMutex(Locks);
        return;
    }

    // Page Mapping - ONLY for faults where pc == fault_addr
    // (meaning the CPU tried to execute unmapped memory, not access it)
    if(sig == X64_SIGSEGV &&
        fault_addr >= 0x10000 &&
        fault_addr <= 0x7FFFFFFF &&
        (uintptr_t)pc == fault_addr) {

        // Don’t try to “fix” faults in the 0x05000000–0x06000000 range
        // by mapping a page there – we’ve seen bogus jumps land here.
        if (fault_addr >= 0x05000000 && fault_addr < 0x06000000) {
            relockMutex(Locks);
            return;  // let normal signal/SEH handling deal with it
        }

        uint8_t f_byte = (fault_addr >> 24) & 0xFF;
        if(f_byte >= 0x20 && f_byte <= 0x7E) {
            if(trace_fd >= 0) {
                dprintf(trace_fd, "[ASCII_PC] PC=0x%lx Fault=0x%lx\n", (uintptr_t)pc, fault_addr);
                int page_ok = memExist(fault_addr) && (getProtection((uintptr_t)fault_addr) & PROT_READ);
                if(page_ok) {
                    uint8_t* p = (uint8_t*)(uintptr_t)fault_addr;
                    dprintf(trace_fd, "BYTES[PC]: ");
                    for(int i=0;i<32;i++) dprintf(trace_fd, "%02x", p[i]);
                    dprintf(trace_fd, "\n");
                }
            }
            relockMutex(Locks);
            return;
        }
        size_t page_size = getpagesize();
        void *page_base = (void*)(fault_addr & ~(page_size - 1));

        if (!getMmapped((uintptr_t)page_base)) {
            void *result = mmap(page_base, page_size, PROT_READ | PROT_EXEC,
                               MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
            if (result != MAP_FAILED) {
                if (trace_fd >= 0 && fault_addr >= 0x7bf00000 && fault_addr < 0x7c000000) {
                    dprintf(trace_fd, "[WINE_CODE_FIX] MAP RX at 0x%lx | Fault=0x%lx\n", (uintptr_t)page_base, fault_addr);
                }
                relockMutex(Locks);
                return;
            }
        } else {
            uint32_t curp = getProtection((uintptr_t)page_base);
            if(!(curp & PROT_EXEC)) {
                mprotect(page_base, page_size, curp | PROT_EXEC);
                if (trace_fd >= 0 && fault_addr >= 0x7bf00000 && fault_addr < 0x7c000000) {
                    dprintf(trace_fd, "[WINE_CODE_FIX] ADD EXEC at 0x%lx | old_prot=0x%x | Fault=0x%lx\n",
                            (uintptr_t)page_base, curp, fault_addr);
                }
                relockMutex(Locks);
                return;
            }
        }
    }
}
#ifdef DYNAREC
    if((Locks & is_dyndump_locked) && ((sig==X64_SIGSEGV) || (sig==X64_SIGBUS)) && current_helper) {
        printf_log(LOG_INFO, "FillBlock triggered a %s at %p from %p\n", (sig==X64_SIGSEGV)?"segfault":"bus error", addr, pc);
        CancelBlock64(0);
        relockMutex(Locks);
        cancelFillBlock();  // Segfault inside a Fillblock, cancel it's creation...
        // cancelFillBlock does not return
    }
    if ((sig==X64_SIGSEGV) && (addr) && (info->si_code == SEGV_ACCERR) && (prot&PROT_DYNAREC)) {
        lock_signal();
        // check if SMC inside block
        if(!db_searched) {
            db = FindDynablockFromNativeAddress(pc);
            if(db)
                x64pc = getX64Address(db, (uintptr_t)pc);
            db_searched = 1;
        }
        // access error, unprotect the block (and mark them dirty)
        unprotectDB((uintptr_t)addr, 1, 1);    // unprotect 1 byte... But then, the whole page will be unprotected
        CheckHotPage((uintptr_t)addr, prot);
        int db_need_test = (db && !BOX64ENV(dynarec_dirty))?getNeedTest((uintptr_t)db->x64_addr):0;
        if(db && ((addr>=db->x64_addr && addr<(db->x64_addr+db->x64_size)) || db_need_test)) {
            emu = getEmuSignal(emu, p, db);
            // dynablock got auto-dirty! need to get out of it!!!
            if(emu->jmpbuf) {
                uintptr_t x64pc = getX64Address(db, (uintptr_t)pc);
                copyUCTXreg2Emu(emu, p, x64pc);
                adjustregs(emu, pc);
                if(db && db->arch_size)
                    ARCH_ADJUST(db, emu, p, x64pc);
                dynarec_log(LOG_INFO, "Dynablock (%p, x64addr=%p, need_test=%d/%d/%d) %s, getting out at %p (%p)!\n", db, db->x64_addr, db_need_test, db->dirty, db->always_test, (addr>=db->x64_addr && addr<(db->x64_addr+db->x64_size))?"Auto-SMC":"unprotected", (void*)R_RIP, (void*)addr);
                //relockMutex(Locks);
                unlock_signal();
                if(Locks & is_dyndump_locked)
                    CancelBlock64(1);
                emu->test.clean = 0;
                #ifdef ANDROID
                siglongjmp(*(JUMPBUFF*)emu->jmpbuf, 2);
                #else
                siglongjmp(emu->jmpbuf, 2);
                #endif
            }
            dynarec_log(LOG_INFO, "Warning, Auto-SMC (%p for db %p/%p) detected, but jmpbuffer not ready!\n", (void*)addr, db, (void*)db->x64_addr);
        }
        // done
        if((prot&PROT_WRITE)/*|| (prot&PROT_DYNAREC)*/) {
            unlock_signal();
            dynarec_log(LOG_INFO, "Writting from %04d|%p(%s, native=%s) to %p!\n", GetTID(), (void*)x64pc, getAddrFunctionName(x64pc), db?"Dynablock":GetNativeName(pc),(void*)addr);
            // if there is no write permission, don't return and continue to program signal handling
            relockMutex(Locks);
            return;
        }
        unlock_signal();
    } else if ((sig==X64_SIGSEGV) && (addr) && (info->si_code == SEGV_ACCERR) && ((prot&(PROT_READ|PROT_WRITE))==(PROT_READ|PROT_WRITE))) {
        lock_signal();
        if(!db_searched) {
            db = FindDynablockFromNativeAddress(pc);
            if(db)
                x64pc = getX64Address(db, (uintptr_t)pc);
            db_searched = 1;
        }
        if(db && db->x64_addr>= addr && (db->x64_addr+db->x64_size)<addr) {
            dynarec_log(LOG_INFO, "Warning, addr inside current dynablock!\n");
        }
        // mark stuff as unclean
        if(BOX64ENV(dynarec))
            cleanDBFromAddressRange(((uintptr_t)addr)&~(box64_pagesize-1), box64_pagesize, 0);
        static void* glitch_pc = NULL;
        static void* glitch_addr = NULL;
        static uint32_t glitch_prot = 0;
        if(addr && pc /*&& db*/) {
            if((glitch_pc!=pc || glitch_addr!=addr || glitch_prot!=prot)) {
                // probably a glitch due to intensive multitask...
                dynarec_log(/*LOG_DEBUG*/LOG_INFO, "%04d|SIGSEGV with Access error on %p for %p, db=%p, prot=0x%x, retrying\n", tid, pc, addr, db, prot);
                glitch_pc = pc;
                glitch_addr = addr;
                glitch_prot = prot;
                relockMutex(Locks);
                unlock_signal();
                return; // try again
            }
dynarec_log(/*LOG_DEBUG*/LOG_INFO, "%04d|Repeated SIGSEGV with Access error on %p for %p, db=%p, prot=0x%x\n", tid, pc, addr, db, prot);
            glitch_pc = NULL;
            glitch_addr = NULL;
            glitch_prot = 0;
            relockMutex(Locks);
            unlock_signal();
            return; // try again
    }
        if(addr && pc && ((prot&(PROT_READ|PROT_WRITE))==(PROT_READ|PROT_WRITE))) {
            static void* glitch2_pc = NULL;
            static void* glitch2_addr = NULL;
            static int glitch2_prot = 0;
            if((glitch2_pc!=pc || glitch2_addr!=addr || glitch2_prot!=prot)) {
                dynarec_log(LOG_INFO, "Is that a multi process glitch too?\n");
                //printf_log(LOG_INFO, "Is that a multi process glitch too?\n");
                glitch2_pc = pc;
                glitch2_addr = addr;
                glitch2_prot = prot;
                sched_yield();  // give time to the other process
                refreshProtection((uintptr_t)addr);
                relockMutex(Locks);
                sched_yield();  // give time to the other process
                unlock_signal();
                return; // try again
            }
            glitch2_pc = NULL;
            glitch2_addr = NULL;
            glitch2_prot = 0;
        }
        unlock_signal();
    } else if ((sig==X64_SIGSEGV) && (addr) && (info->si_code == SEGV_ACCERR) && (prot&PROT_DYNAREC_R)) {
        // unprotect and continue to signal handler, because Write is not there on purpose
        unprotectDB((uintptr_t)addr, 1, 1);    // unprotect 1 byte... But then, the whole page will be unprotected
    }
    if(!db_searched) {
        db = FindDynablockFromNativeAddress(pc);
        if(db)
            x64pc = getX64Address(db, (uintptr_t)pc);
        db_searched = 1;
    }
#endif
    if((sig==X64_SIGSEGV || sig==X64_SIGBUS) && box64_quit) {
        printf_log(LOG_INFO, "Sigfault/Segbus while quitting, exiting silently\n");
        _exit(box64_exit_code);    // Hack, segfault while quiting, exit silently
    }
    static int old_code = -1;
    static void* old_pc = 0;
    static void* old_addr = 0;
    static int old_tid = 0;
    static uint32_t old_prot = 0;
    int mapped = memExist((uintptr_t)addr);
    const char* signame = (sig==X64_SIGSEGV)?"SIGSEGV":((sig==X64_SIGBUS)?"SIGBUS":((sig==X64_SIGILL)?"SIGILL":"SIGABRT"));
    rsp = (void*)R_RSP;
#if defined(DYNAREC)
    if(db && CONTEXT_REG(p, xEmu)>0x10000) {
        emu = (x64emu_t*)CONTEXT_REG(p, xEmu);
    }
    if(db) {
        rsp = (void*)CONTEXT_REG(p, xRSP);
    }
#endif //DYNAREC
    if(!db && (sig==X64_SIGSEGV) && ((uintptr_t)addr==(x64pc-1)))
        x64pc--;
    if(old_code==info->si_code && old_pc==pc && old_addr==addr && old_tid==tid && old_prot==prot) {
        printf_log(log_minimum, "%04d|Double %s (code=%d, pc=%p, x64pc=%p, addr=%p, prot=%02x)!\n", tid, signame, old_code, old_pc, x64pc, old_addr, prot);
        exit(-1);
    } else {
        if((sig==X64_SIGSEGV) && (info->si_code == SEGV_ACCERR) && ((prot&~PROT_CUSTOM)==(PROT_READ|PROT_WRITE) || (prot&~PROT_CUSTOM)==(PROT_READ|PROT_WRITE|PROT_EXEC))) {
            static uintptr_t old_addr = 0;
            #ifdef DYNAREC
            if(prot==(PROT_READ|PROT_WRITE|PROT_EXEC))
                if(cleanDBFromAddressRange(((uintptr_t)addr)&~(box64_pagesize-1), box64_pagesize, 0)) {
                    printf_log(/*LOG_DEBUG*/LOG_INFO, "%04d| Strange SIGSEGV with Access error on %p for %p with DynaBlock(s) in range, db=%p, Lock=0x%x)\n", tid, pc, addr, db, Locks);
                    refreshProtection((uintptr_t)addr);
                    relockMutex(Locks);
                    return;
                }
            #endif
            printf_log(/*LOG_DEBUG*/LOG_INFO, "%04d| Strange SIGSEGV with Access error on %p for %p%s, db=%p, prot=0x%x (old_addr=%p, Lock=0x%x)\n", tid, pc, addr, mapped?" mapped":"", db, prot, (void*)old_addr, Locks);
            if(!(old_addr==(uintptr_t)addr && old_prot==prot) || mapped) {
                old_addr = (uintptr_t)addr;
                old_prot = prot;
                refreshProtection(old_addr);
                relockMutex(Locks);
                sched_yield();  // give time to the other process
                return; // that's probably just a multi-task glitch, like seen in terraria
            }
            old_addr = 0;
        }
        old_code = info->si_code;
        old_pc = pc;
        old_addr = addr;
        old_tid = tid;
        old_prot = prot;
        const char* name = NULL;
        const char* x64name = NULL;
        if (log_minimum<=BOX64ENV(log)) {
            signal_jmpbuf_active = 1;
            if(sigsetjmp(SIG_JMPBUF, 1)) {
                // segfault while gathering function name...
                name = "???";
            } else
                name = GetNativeName(pc);
            signal_jmpbuf_active = 0;
        }
        // Adjust RIP for special case of NULL function run
        if(sig==X64_SIGSEGV && R_RIP==0x1 && (uintptr_t)info->si_addr==0x0)
            R_RIP = 0x0;
        if(log_minimum<=BOX64ENV(log)) {
            elfheader_t* elf = FindElfAddress(my_context, x64pc);
            if(elf) {
                signal_jmpbuf_active = 1;
                if(sigsetjmp(SIG_JMPBUF, 1)) {
                    // segfault while gathering function name...
                    x64name = "?";
                } else
                    x64name = getAddrFunctionName(x64pc);
                signal_jmpbuf_active = 0;
            }
        }
        if(BOX64ENV(jitgdb)) {
            pid_t pid = getpid();
            int v = vfork(); // is this ok in a signal handler???
            if(v<0) {
                printf("Error while forking, cannot launch gdb (errp%d/%s)\n", errno, strerror(errno));
            } else if(v) {
                // parent process, the one that have the segfault
                volatile int waiting = 1;
                printf("Waiting for %s (pid %d)...\n", (BOX64ENV(jitgdb)==2)?"gdbserver":"gdb", pid);
                while(waiting) {
                    // using gdb, use "set waiting=0" to stop waiting...
                    usleep(1000);
                }
            } else {
                char myarg[50] = {0};
                sprintf(myarg, "%d", pid);
                if(BOX64ENV(jitgdb)==2)
                    execlp("gdbserver", "gdbserver", "127.0.0.1:1234", "--attach", myarg, (char*)NULL);
                else if(BOX64ENV(jitgdb)==3)
                    execlp("lldb", "lldb", "-p", myarg, (char*)NULL);
                else
                    execlp("gdb", "gdb", "-pid", myarg, (char*)NULL);
                exit(-1);
            }
        }
        print_rolling_log(log_minimum);

        if((BOX64ENV(showbt) || sig==X64_SIGABRT) && log_minimum<=BOX64ENV(log)) {
            // show native bt
            ShowNativeBT(log_minimum);

#define BT_BUF_SIZE 100
            int nptrs;
            void *buffer[BT_BUF_SIZE];
            char **strings;

            extern int my_backtrace_ip(x64emu_t* emu, void** buffer, int size);   // in wrappedlibc
            extern char** my_backtrace_symbols(x64emu_t* emu, uintptr_t* buffer, int size);
            // save and set real RIP/RSP
            #define GO(A) uintptr_t old_##A = R_##A;
            GO(RAX);
            GO(RBX);
            GO(RCX);
            GO(RDX);
            GO(RBP);
            GO(RSP);
            GO(RDI);
            GO(RSI);
            GO(R8);
            GO(R9);
            GO(R10);
            GO(R11);
            GO(R12);
            GO(R13);
            GO(R14);
            GO(R15);
            GO(RIP);
            #undef GO
            #ifdef DYNAREC
            if(db)
                copyUCTXreg2Emu(emu, p, x64pc);
            #endif
            nptrs = my_backtrace_ip(emu, buffer, BT_BUF_SIZE);
            strings = my_backtrace_symbols(emu, (uintptr_t*)buffer, nptrs);
            if(strings) {
                for (int j = 0; j < nptrs; j++)
                    printf_log(log_minimum, "EmulatedBT: %s\n", strings[j]);
                free(strings);
            } else
                printf_log(log_minimum, "EmulatedBT: none\n");
            #define GO(A) R_##A = old_##A
            GO(RAX);
            GO(RBX);
            GO(RCX);
            GO(RDX);
            GO(RBP);
            GO(RSP);
            GO(RDI);
            GO(RSI);
            GO(R8);
            GO(R9);
            GO(R10);
            GO(R11);
            GO(R12);
            GO(R13);
            GO(R14);
            GO(R15);
            GO(RIP);
            #undef GO
        }

        if(log_minimum<=BOX64ENV(log)) {
            static const char* reg_name[] = {"RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI", " R8", " R9","R10","R11", "R12","R13","R14","R15"};
            static const char* seg_name[] = {"ES", "CS", "SS", "DS", "FS", "GS"};
            int shown_regs = 0;
#ifdef DYNAREC
            #ifdef GDBJIT
            if(db && BOX64ENV(dynarec_gdbjit) == 3) GdbJITBlockReady(db->gdbjit_block);
            #endif
            uint32_t hash = 0;
            if(db)
                hash = X31_hash_code(db->x64_addr, db->x64_size);
            printf_log(log_minimum, "%04d|%s @%p (%s) (x64pc=%p/\"%s\", rsp=%p, stack=%p:%p own=%p fp=%p), for accessing %p (code=%d/prot=%x), db=%p(%p:%p/%p:%p/%s:%s, hash:%x/%x) handler=%p",
                GetTID(), signame, pc, name, (void*)x64pc, x64name?:"???", rsp,
                emu->init_stack, emu->init_stack+emu->size_stack, emu->stack2free, (void*)R_RBP,
                addr, info->si_code,
                prot, db, db?db->block:0, db?(db->block+db->size):0,
                db?db->x64_addr:0, db?(db->x64_addr+db->x64_size):0,
                getAddrFunctionName((uintptr_t)(db?db->x64_addr:0)),
                (db?getNeedTest((uintptr_t)db->x64_addr):0)?"needs_test":"clean", db?db->hash:0, hash,
                (void*)my_context->signals[sig]);
                if(db) {
                    shown_regs = 1;
                    for (int i=0; i<16; ++i) {
                        if(!(i%4)) printf_log_prefix(0, log_minimum, "\n");
                        printf_log_prefix(0, log_minimum, "%s:0x%016llx ", reg_name[i], CONTEXT_REG(p, TO_NAT(i)));
                    }
                    printf_log_prefix(0, log_minimum, "\n");
                    for (int i=0; i<6; ++i)
                        printf_log_prefix(0, log_minimum, "%s:0x%04x ", seg_name[i], emu->segs[i]);
                }
                if(rsp!=addr && getProtection((uintptr_t)rsp-4*8) && getProtection((uintptr_t)rsp+4*8))
                    for (int i=-4; i<4; ++i) {
                        printf_log_prefix(0, log_minimum, "%sRSP%c0x%02x:0x%016lx", (i%4)?" ":"\n", i<0?'-':'+', abs(i)*8, *(uintptr_t*)(rsp+i*8));
                    }
#else
            printf_log(log_minimum, "%04d|%s @%p (%s) (x64pc=%p/\"%s\", rsp=%p), for accessing %p (code=%d)", GetTID(), signame, pc, name, (void*)x64pc, x64name?:"???", rsp, addr, info->si_code);
#endif
            if(!shown_regs) {
                for (int i=0; i<16; ++i) {
                    if(!(i%4)) printf_log_prefix(0, log_minimum, "\n");
                    printf_log_prefix(0, log_minimum, "%s:0x%016llx ", reg_name[i], emu->regs[i].q[0]);
                }
                printf_log_prefix(0, log_minimum, "\n");
                for (int i=0; i<6; ++i)
                    printf_log_prefix(0, log_minimum, "%s:0x%04x ", seg_name[i], emu->segs[i]);
            }
            zydis_dec_t* dec = emu->segs[_CS] == 0x23 ? my_context->dec32 : my_context->dec;
            if(sig==X64_SIGILL) {
                printf_log_prefix(0, log_minimum, " opcode=%02X %02X %02X %02X %02X %02X %02X %02X ", ((uint8_t*)pc)[0], ((uint8_t*)pc)[1], ((uint8_t*)pc)[2], ((uint8_t*)pc)[3], ((uint8_t*)pc)[4], ((uint8_t*)pc)[5], ((uint8_t*)pc)[6], ((uint8_t*)pc)[7]);
                if (dec)
                    printf_log_prefix(0, log_minimum, "(%s)\n", DecodeX64Trace(dec, x64pc, 1));
                else
                    printf_log_prefix(0, log_minimum, "(%02X %02X %02X %02X %02X)\n", ((uint8_t*)x64pc)[0], ((uint8_t*)x64pc)[1], ((uint8_t*)x64pc)[2], ((uint8_t*)x64pc)[3], ((uint8_t*)x64pc)[4]);
            } else if(sig==X64_SIGBUS || (sig==X64_SIGSEGV && (x64pc!=(uintptr_t)addr) && (pc!=addr)) && (getProtection_fast(x64pc)&PROT_READ) && (getProtection_fast((uintptr_t)pc)&PROT_READ)) {
                if (dec)
                    printf_log_prefix(0, log_minimum, " %sopcode=%s; native opcode=%08x\n", (emu->segs[_CS] == 0x23) ? "x86" : "x64", DecodeX64Trace(dec, x64pc, 1), *(uint32_t*)pc);
                else
                    printf_log_prefix(0, log_minimum, " %sopcode=%02X %02X %02X %02X %02X %02X %02X %02X (opcode=%08x)\n", (emu->segs[_CS] == 0x23) ? "x86" : "x64", ((uint8_t*)x64pc)[0], ((uint8_t*)x64pc)[1], ((uint8_t*)x64pc)[2], ((uint8_t*)x64pc)[3], ((uint8_t*)x64pc)[4], ((uint8_t*)x64pc)[5], ((uint8_t*)x64pc)[6], ((uint8_t*)x64pc)[7], *(uint32_t*)pc);
            } else {
                printf_log_prefix(0, log_minimum, "\n");
            }
        }
    }
    relockMutex(Locks);
    if(my_context->signals[sig] && my_context->signals[sig]!=1) {
        my_sigactionhandler_oldcode(emu, sig, my_context->is_sigaction[sig]?0:1, info, ucntx, &old_code, db, x64pc);
        return;
    }
    // no handler (or double identical segfault)
    // set default and that's it, instruction will restart and default segfault handler will be called...
    if(my_context->signals[sig]!=1 || sig==X64_SIGSEGV || sig==X64_SIGILL || sig==X64_SIGFPE || sig==X64_SIGABRT) {
        signal(signal_from_x64(sig), (void*)my_context->signals[sig]);
    }
}

void my_sigactionhandler(int32_t sig, siginfo_t* info, void * ucntx)
{
    sig = signal_from_x64(sig);
    void* pc = NULL;
    #ifdef DYNAREC
    ucontext_t *p = (ucontext_t *)ucntx;
    pc = (void*)CONTEXT_PC(p);
    #endif
    dynablock_t* db = FindDynablockFromNativeAddress(pc);
    x64emu_t* emu = thread_get_emu();
    uintptr_t x64pc = R_RIP;
    if(db)
        x64pc = getX64Address(db, (uintptr_t)pc);
    #ifdef DYNAREC
    if(db && !x64pc) {
        printf_log(LOG_INFO, "Warning, ingnoring incoherent dynablock found for address %p (opcode=%x). db=%p(x64_addr=%p-%p, block:%p-%p)\n", pc, *(uint32_t*)pc, db, (void*)db->x64_addr, (void*)db->x64_addr+db->x64_size, db->actual_block, db->actual_block+db->size);
        db = NULL;
        x64pc = R_RIP;
    }
    #endif
    if(BOX64ENV(showsegv) && (sig!=10 || BOX64ENV(log)>LOG_INFO)) {
        printf_log(LOG_INFO, "%04d|sigaction handler for sig %d, pc=%p, x64pc=%p, db=%p%s", GetTID(), sig, pc, x64pc, db, db?"":"\n");
        #ifdef DYNAREC
        if(db)
            printf_log_prefix(0, LOG_INFO, "(x64_addr=%p-%p, block:%p-%p)\n", (void*)db->x64_addr, (void*)db->x64_addr+db->x64_size, db->actual_block, db->actual_block+db->size);
        #endif
    }
    my_sigactionhandler_oldcode(emu, sig, 0, info, ucntx, NULL, db, x64pc);
}

EXPORT sighandler_t my_signal(x64emu_t* emu, int signum, sighandler_t handler)
{
    if(signum<0 || signum>MAX_SIGNAL)
        return SIG_ERR;

    if(signum==X64_SIGSEGV && emu->context->no_sigsegv)
        return 0;

    // create a new handler
    my_context->signals[signum] = (uintptr_t)handler;
    my_context->is_sigaction[signum] = 0;
    my_context->restorer[signum] = 0;
    my_context->onstack[signum] = 0;

    if(signum==X64_SIGSEGV || signum==X64_SIGBUS || signum==X64_SIGILL || signum==X64_SIGABRT)
        return 0;

    if(handler!=NULL && handler!=(sighandler_t)1) {
        struct sigaction newact = {0};
        struct sigaction oldact = {0};
        newact.sa_flags = 0x04;
        newact.sa_sigaction = my_sigactionhandler;
        sigaction(signal_from_x64(signum), &newact, &oldact);
        return oldact.sa_handler;
    } else
        return signal(signal_from_x64(signum), handler);
}
EXPORT sighandler_t my___sysv_signal(x64emu_t* emu, int signum, sighandler_t handler) __attribute__((alias("my_signal")));
EXPORT sighandler_t my_sysv_signal(x64emu_t* emu, int signum, sighandler_t handler) __attribute__((alias("my_signal")));    // not completely exact

int EXPORT my_sigaction(x64emu_t* emu, int signum, const x64_sigaction_t *act, x64_sigaction_t *oldact)
{
    printf_log(LOG_DEBUG, "Sigaction(signum=%d, act=%p(f=%p, flags=0x%x), old=%p)\n", signum, act, act?act->_u._sa_handler:NULL, act?act->sa_flags:0, oldact);
    if(signum<0 || signum>MAX_SIGNAL) {
        errno = EINVAL;
        return -1;
    }

    if(signum==X64_SIGSEGV && emu->context->no_sigsegv)
        return 0;

    if(signum==X64_SIGILL && emu->context->no_sigill)
        return 0;
    struct sigaction newact = {0};
    struct sigaction old = {0};
    uintptr_t old_handler = my_context->signals[signum];
    if(act) {
        newact.sa_mask = act->sa_mask;
        newact.sa_flags = act->sa_flags&~0x04000000;  // No sa_restorer...
        if(act->sa_flags&0x04) {
            my_context->signals[signum] = (uintptr_t)act->_u._sa_sigaction;
            my_context->is_sigaction[signum] = 1;
            if(act->_u._sa_handler!=NULL && act->_u._sa_handler!=(sighandler_t)1) {
                newact.sa_sigaction = my_sigactionhandler;
            } else
                newact.sa_sigaction = act->_u._sa_sigaction;
        } else {
            my_context->signals[signum] = (uintptr_t)act->_u._sa_handler;
            my_context->is_sigaction[signum] = 0;
            if(act->_u._sa_handler!=NULL && act->_u._sa_handler!=(sighandler_t)1) {
                newact.sa_flags|=0x04;
                newact.sa_sigaction = my_sigactionhandler;
            } else
                newact.sa_handler = act->_u._sa_handler;
        }
        my_context->restorer[signum] = (act->sa_flags&0x04000000)?(uintptr_t)act->sa_restorer:0;
        my_context->onstack[signum] = (act->sa_flags&SA_ONSTACK)?1:0;
    }
    int ret = 0;
    if(signum!=X64_SIGSEGV && signum!=X64_SIGBUS && signum!=X64_SIGILL && signum!=X64_SIGABRT)
        ret = sigaction(signal_from_x64(signum), act?&newact:NULL, oldact?&old:NULL);
    if(oldact) {
        oldact->sa_flags = old.sa_flags;
        oldact->sa_mask = old.sa_mask;
        if(old.sa_flags & 0x04)
            oldact->_u._sa_sigaction = old.sa_sigaction; //TODO should wrap...
        else
            oldact->_u._sa_handler = old.sa_handler;  //TODO should wrap...
        if((uintptr_t)oldact->_u._sa_sigaction == (uintptr_t)my_sigactionhandler && old_handler)
            oldact->_u._sa_sigaction = (void*)old_handler;
        oldact->sa_restorer = NULL; // no handling for now...
    }
    return ret;
}
int EXPORT my___sigaction(x64emu_t* emu, int signum, const x64_sigaction_t *act, x64_sigaction_t *oldact)
__attribute__((alias("my_sigaction")));

int EXPORT my_syscall_rt_sigaction(x64emu_t* emu, int signum, const x64_sigaction_restorer_t *act, x64_sigaction_restorer_t *oldact, int sigsetsize)
{
    printf_log(LOG_DEBUG, "Syscall/Sigaction(signum=%d, act=%p, old=%p, size=%d)\n", signum, act, oldact, sigsetsize);
    if(signum<0 || signum>MAX_SIGNAL) {
        errno = EINVAL;
        return -1;
    }

    if(signum==X64_SIGSEGV && emu->context->no_sigsegv)
        return 0;
    // TODO, how to handle sigsetsize>4?!
    if(signum==32 || signum==33) {
        // cannot use libc sigaction, need to use syscall!
        struct kernel_sigaction newact = {0};
        struct kernel_sigaction old = {0};
        if(act) {
            printf_log(LOG_DEBUG, " New (kernel) action flags=0x%x mask=0x%lx\n", act->sa_flags, *(uint64_t*)&act->sa_mask);
            memcpy(&newact.sa_mask, &act->sa_mask, (sigsetsize>16)?16:sigsetsize);
            newact.sa_flags = act->sa_flags&~0x04000000;  // No sa_restorer...
            if(act->sa_flags&0x04) {
                my_context->signals[signum] = (uintptr_t)act->_u._sa_sigaction;
                my_context->is_sigaction[signum] = 1;
                if(act->_u._sa_handler!=NULL && act->_u._sa_handler!=(sighandler_t)1) {
                    newact.k_sa_handler = (void*)my_sigactionhandler;
                } else {
                    newact.k_sa_handler = (void*)act->_u._sa_sigaction;
                }
            } else {
                my_context->signals[signum] = (uintptr_t)act->_u._sa_handler;
                my_context->is_sigaction[signum] = 0;
                if(act->_u._sa_handler!=NULL && act->_u._sa_handler!=(sighandler_t)1) {
                    newact.sa_flags|=0x4;
                    newact.k_sa_handler = (void*)my_sigactionhandler;
                } else {
                    newact.k_sa_handler = act->_u._sa_handler;
                }
            }
            my_context->restorer[signum] = (act->sa_flags&0x04000000)?(uintptr_t)act->sa_restorer:0;
        }

        if(oldact) {
            old.sa_flags = oldact->sa_flags;
            memcpy(&old.sa_mask, &oldact->sa_mask, (sigsetsize>16)?16:sigsetsize);
        }

        int ret = syscall(__NR_rt_sigaction, signum, act?&newact:NULL, oldact?&old:NULL, (sigsetsize>16)?16:sigsetsize);
        if(oldact && ret==0) {
            oldact->sa_flags = old.sa_flags;
            memcpy(&oldact->sa_mask, &old.sa_mask, (sigsetsize>16)?16:sigsetsize);
            if(old.sa_flags & 0x04)
                oldact->_u._sa_sigaction = (void*)old.k_sa_handler; //TODO should wrap...
            else
                oldact->_u._sa_handler = old.k_sa_handler;  //TODO should wrap...
        }
        return ret;
    } else {
        // using libc sigaction
        struct sigaction newact = {0};
        struct sigaction old = {0};
        if(act) {
            printf_log(LOG_DEBUG, " New action for signal #%d flags=0x%x mask=0x%lx\n", signum, act->sa_flags, *(uint64_t*)&act->sa_mask);
            newact.sa_mask = act->sa_mask;
            newact.sa_flags = act->sa_flags&~0x04000000;  // No sa_restorer...
            if(act->sa_flags&0x04) {
                if(act->_u._sa_handler!=NULL && act->_u._sa_handler!=(sighandler_t)1) {
                    my_context->signals[signum] = (uintptr_t)act->_u._sa_sigaction;
                    newact.sa_sigaction = my_sigactionhandler;
                } else {
                    newact.sa_sigaction = act->_u._sa_sigaction;
                }
            } else {
                if(act->_u._sa_handler!=NULL && act->_u._sa_handler!=(sighandler_t)1) {
                    my_context->signals[signum] = (uintptr_t)act->_u._sa_handler;
                    my_context->is_sigaction[signum] = 0;
                    newact.sa_sigaction = my_sigactionhandler;
                    newact.sa_flags|=0x4;
                } else {
                    newact.sa_handler = act->_u._sa_handler;
                }
            }
            my_context->restorer[signum] = (act->sa_flags&0x04000000)?(uintptr_t)act->sa_restorer:0;
        }

        if(oldact) {
            old.sa_flags = oldact->sa_flags;
            old.sa_mask = oldact->sa_mask;
        }
        int ret = 0;

        if(signum!=X64_SIGSEGV && signum!=X64_SIGBUS && signum!=X64_SIGILL && signum!=X64_SIGABRT)
            ret = sigaction(signal_from_x64(signum), act?&newact:NULL, oldact?&old:NULL);
        if(oldact && ret==0) {
            oldact->sa_flags = old.sa_flags;
            memcpy(&oldact->sa_mask, &old.sa_mask, (sigsetsize>8)?8:sigsetsize);
            if(old.sa_flags & 0x04)
                oldact->_u._sa_sigaction = old.sa_sigaction; //TODO should wrap...
            else
                oldact->_u._sa_handler = old.sa_handler;  //TODO should wrap...
        }
        return ret;
    }
}

EXPORT sighandler_t my_sigset(x64emu_t* emu, int signum, sighandler_t handler)
{
    signum = signal_from_x64(signum);
    // emulated SIG_HOLD
    if(handler == (sighandler_t)2) {
        x64_sigaction_t oact;
        sigset_t nset;
        sigset_t oset;
        if (sigemptyset (&nset) < 0)
            return (sighandler_t)-1;
        if (sigaddset (&nset, signum) < 0)
            return (sighandler_t)-1;
        if (sigprocmask (SIG_BLOCK, &nset, &oset) < 0)
            return (sighandler_t)-1;
        if (sigismember (&oset, signum))
            return (sighandler_t)2;
        if (my_sigaction (emu, signum, NULL, &oact) < 0)
            return (sighandler_t)-1;
        return oact._u._sa_handler;
    }
    return my_signal(emu, signum, handler);
}

EXPORT int my_getcontext(x64emu_t* emu, void* ucp)
{
//    printf_log(LOG_NONE, "Warning: call to partially implemented getcontext\n");
    x64_ucontext_t *u = (x64_ucontext_t*)ucp;
    // stack traking
    u->uc_stack.ss_sp = NULL;
    u->uc_stack.ss_size = 0;    // this need to filled
    // get general register
    u->uc_mcontext.gregs[X64_RAX] = R_RAX;
    u->uc_mcontext.gregs[X64_RCX] = R_RCX;
    u->uc_mcontext.gregs[X64_RDX] = R_RDX;
    u->uc_mcontext.gregs[X64_RDI] = R_RDI;
    u->uc_mcontext.gregs[X64_RSI] = R_RSI;
    u->uc_mcontext.gregs[X64_RBP] = R_RBP;
    u->uc_mcontext.gregs[X64_RIP] = *(uint64_t*)R_RSP;
    u->uc_mcontext.gregs[X64_RSP] = R_RSP+sizeof(uintptr_t);
    u->uc_mcontext.gregs[X64_RBX] = R_RBX;
    u->uc_mcontext.gregs[X64_R8] = R_R8;
    u->uc_mcontext.gregs[X64_R9] = R_R9;
    u->uc_mcontext.gregs[X64_R10] = R_R10;
    u->uc_mcontext.gregs[X64_R11] = R_R11;
    u->uc_mcontext.gregs[X64_R12] = R_R12;
    u->uc_mcontext.gregs[X64_R13] = R_R13;
    u->uc_mcontext.gregs[X64_R14] = R_R14;
    u->uc_mcontext.gregs[X64_R15] = R_R15;
    // get segments
    u->uc_mcontext.gregs[X64_CSGSFS] = ((uint64_t)(R_CS)) | (((uint64_t)(R_GS))<<16) | (((uint64_t)(R_FS))<<32);
    // get FloatPoint status
    u->uc_mcontext.fpregs = ucp + 408;
    fpu_savenv(emu, (void*)u->uc_mcontext.fpregs, 1);
    *(uint32_t*)(ucp + 432) = emu->mxcsr.x32;

    // get signal mask
    sigprocmask(SIG_SETMASK, NULL, (sigset_t*)&u->uc_sigmask);

    return 0;
}

EXPORT int my_setcontext(x64emu_t* emu, void* ucp)
{
//    printf_log(LOG_NONE, "Warning: call to partially implemented setcontext\n");
    x64_ucontext_t *u = (x64_ucontext_t*)ucp;
    // stack tracking
    emu->init_stack = u->uc_stack.ss_sp;
    emu->size_stack = u->uc_stack.ss_size;
    // set general register
    R_RAX = u->uc_mcontext.gregs[X64_RAX];
    R_RCX = u->uc_mcontext.gregs[X64_RCX];
    R_RDX = u->uc_mcontext.gregs[X64_RDX];
    R_RDI = u->uc_mcontext.gregs[X64_RDI];
    R_RSI = u->uc_mcontext.gregs[X64_RSI];
    R_RBP = u->uc_mcontext.gregs[X64_RBP];
    R_RIP = u->uc_mcontext.gregs[X64_RIP];
    R_RSP = u->uc_mcontext.gregs[X64_RSP];
    R_RBX = u->uc_mcontext.gregs[X64_RBX];
    R_R8  = u->uc_mcontext.gregs[X64_R8];
    R_R9  = u->uc_mcontext.gregs[X64_R9];
    R_R10 = u->uc_mcontext.gregs[X64_R10];
    R_R11 = u->uc_mcontext.gregs[X64_R11];
    R_R12 = u->uc_mcontext.gregs[X64_R12];
    R_R13 = u->uc_mcontext.gregs[X64_R13];
    R_R14 = u->uc_mcontext.gregs[X64_R14];
    R_R15 = u->uc_mcontext.gregs[X64_R15];
    // get segments
    R_CS = (u->uc_mcontext.gregs[X64_CSGSFS]>> 0)&0xffff;
    R_GS = (u->uc_mcontext.gregs[X64_CSGSFS]>>16)&0xffff;
    R_FS = (u->uc_mcontext.gregs[X64_CSGSFS]>>32)&0xffff;
    // set FloatPoint status
    fpu_loadenv(emu, (void*)u->uc_mcontext.fpregs, 1);
    emu->mxcsr.x32 = *(uint32_t*)(ucp + 432);
    // set signal mask
    sigprocmask(SIG_SETMASK, (sigset_t*)&u->uc_sigmask, NULL);
    errno = 0;

    return R_EAX;
}
void vFEv(x64emu_t *emu, uintptr_t fnc);
EXPORT void my_start_context(x64emu_t* emu)
{
    // this is call indirectly by swapcontext from a makecontext, and will link context or just exit
    x64_ucontext_t *u = *(x64_ucontext_t**)R_RBX;
    if(u)
        my_setcontext(emu, u);
    else
        emu->quit = 1;
}

EXPORT void my_makecontext(x64emu_t* emu, void* ucp, void* fnc, int32_t argc, int64_t* argv)
{
//    printf_log(LOG_NONE, "Warning: call to unimplemented makecontext\n");
    x64_ucontext_t *u = (x64_ucontext_t*)ucp;
    // setup stack
    uintptr_t* rsp = (uintptr_t*)(u->uc_stack.ss_sp + u->uc_stack.ss_size - sizeof(uintptr_t));
    // setup the function
    u->uc_mcontext.gregs[X64_RIP] = (intptr_t)fnc;
    // setup return to private start_context uc_link
    *rsp = (uintptr_t)u->uc_link;
    u->uc_mcontext.gregs[X64_RBX] = (uintptr_t)rsp;
    --rsp;
    // setup args
    int n = 3;
    int j = 0;
    int regs_abi[] = {_DI, _SI, _DX, _CX, _R8, _R9};
    for (int i=0; i<argc; ++i) {
        // get value first
        uint32_t v;
        if(n<6)
            v = emu->regs[regs_abi[n++]].dword[0];
        else
            v = argv[j++];
        // push value
        switch(i) {
            case 0: u->uc_mcontext.gregs[X64_RDI] = v; break;
            case 1: u->uc_mcontext.gregs[X64_RSI] = v; break;
            case 2: u->uc_mcontext.gregs[X64_RDX] = v; break;
            case 3: u->uc_mcontext.gregs[X64_RCX] = v; break;
            case 4: u->uc_mcontext.gregs[X64_R8] = v; break;
            case 5: u->uc_mcontext.gregs[X64_R9] = v; break;
            default:
                --rsp;
                *rsp = argv[(argc-1)-i];
        }
    }
    // push the return value
    --rsp;
    *rsp = AddCheckBridge(my_context->system, vFEv, my_start_context, 0, "my_start_context");//my_context->exit_bridge;
    u->uc_mcontext.gregs[X64_RSP] = (uintptr_t)rsp;
}

void box64_abort() {
    if(BOX64ENV(showbt) && LOG_INFO<=BOX64ENV(log)) {
            // show native bt
            #define BT_BUF_SIZE 100
            int nptrs;
            void *buffer[BT_BUF_SIZE];
            char **strings;
            x64emu_t* emu = thread_get_emu();

#ifndef ANDROID
            nptrs = backtrace(buffer, BT_BUF_SIZE);
            strings = backtrace_symbols(buffer, nptrs);
            if(strings) {
                for (int j = 0; j < nptrs; j++)
                    printf_log(LOG_INFO, "NativeBT: %s\n", strings[j]);
                free(strings);
            } else
                printf_log(LOG_INFO, "NativeBT: none (%d/%s)\n", errno, strerror(errno));
#endif
            extern int my_backtrace_ip(x64emu_t* emu, void** buffer, int size);   // in wrappedlibc
            extern char** my_backtrace_symbols(x64emu_t* emu, uintptr_t* buffer, int size);
            nptrs = my_backtrace_ip(emu, buffer, BT_BUF_SIZE);
            strings = my_backtrace_symbols(emu, (uintptr_t*)buffer, nptrs);
            if(strings) {
                for (int j = 0; j < nptrs; j++)
                    printf_log(LOG_INFO, "EmulatedBT: %s\n", strings[j]);
                free(strings);
            } else
                printf_log(LOG_INFO, "EmulatedBT: none\n");
        }
    abort();
}


EXPORT int my_swapcontext(x64emu_t* emu, void* ucp1, void* ucp2)
{
//    printf_log(LOG_NONE, "Warning: call to unimplemented swapcontext\n");
    // grab current context in ucp1
    my_getcontext(emu, ucp1);
    // activate ucp2
    my_setcontext(emu, ucp2);
    return 0;
}

#ifdef USE_SIGNAL_MUTEX
static void atfork_child_dynarec_prot(void)
{
    #ifdef USE_CUSTOM_MUTEX
    native_lock_store(&mutex_dynarec_prot, 0);
    #else
    pthread_mutex_t tmp = PTHREAD_ERRORCHECK_MUTEX_INITIALIZER_NP;
    memcpy(&mutex_dynarec_prot, &tmp, sizeof(mutex_dynarec_prot));
    #endif
}
#endif
void init_signal_helper(box64context_t* context)
{
    // setup signal handling
    for(int i=0; i<=MAX_SIGNAL; ++i) {
        context->signals[i] = 0;    // SIG_DFL
    }
    struct sigaction action = {0};
    action.sa_flags = SA_SIGINFO | SA_RESTART | SA_NODEFER;
    action.sa_sigaction = my_box64signalhandler;
    sigaction(SIGSEGV, &action, NULL);
    context->signals[signal_to_x64(SIGSEGV)] = (uintptr_t)my_box64signalhandler;
    action.sa_flags = SA_SIGINFO | SA_RESTART | SA_NODEFER;
    action.sa_sigaction = my_box64signalhandler;
    sigaction(SIGBUS, &action, NULL);
    context->signals[signal_to_x64(SIGBUS)] = (uintptr_t)my_box64signalhandler;
    action.sa_flags = SA_SIGINFO | SA_RESTART | SA_NODEFER;
    action.sa_sigaction = my_box64signalhandler;
    sigaction(SIGILL, &action, NULL);
    context->signals[signal_to_x64(SIGILL)] = (uintptr_t)my_box64signalhandler;
    action.sa_flags = SA_SIGINFO | SA_RESTART | SA_NODEFER;
    action.sa_sigaction = my_box64signalhandler;
    sigaction(SIGABRT, &action, NULL);
    context->signals[signal_to_x64(SIGABRT)] = (uintptr_t)my_box64signalhandler;

    static int watchdog_started = 0;
    if (!watchdog_started) {
        watchdog_started = 1;
        pthread_t wt;
        pthread_create(&wt, NULL, watchdog_thread, NULL);
        pthread_detach(wt);
    }

    pthread_once(&sigstack_key_once, sigstack_key_alloc);
#ifdef USE_SIGNAL_MUTEX
    atfork_child_dynarec_prot();
    pthread_atfork(NULL, NULL, atfork_child_dynarec_prot);
#endif
}

void fini_signal_helper()
{
    signal(SIGSEGV, SIG_DFL);
    signal(SIGBUS, SIG_DFL);
    signal(SIGILL, SIG_DFL);
    signal(SIGABRT, SIG_DFL);
}

#ifdef NEED_SIG_CONV
int signal_to_x64(int sig)
{
    #define GO(A) case A: return X64_##A;
    switch(sig) {
        SUPER_SIGNAL
    }
    #undef GO
    return sig;
}
int signal_from_x64(int sig)
{
    #define GO(A) case X64_##A: return A;
    switch(sig) {
        SUPER_SIGNAL
    }
    #undef GO
    return sig;
}
#endif
