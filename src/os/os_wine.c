#include <stdio.h>
#include <string.h>
#include <stdlib.h> // For getenv, atexit
#include <windows.h>
#include <ntstatus.h>
#include <winternl.h>
#include <pthread.h> // For mutex

#include "os.h"
#include "debug.h"
#include "wine/compiler.h"
#include "wine/debug.h"

#define MAP_GROWSDOWN 0x100 // Placeholder for Linux-specific MAP_GROWSDOWN flag

#define HandleToULong(h) ((ULONG)(ULONG_PTR)(h))

NTSTATUS WINAPI NtYieldExecution(void);

int box64_isAddressSpace32 = 0;

typedef struct stack_info_s {
    void* addr;
    size_t size;
} stack_info_t;

static pthread_mutex_t stack_mutex = PTHREAD_MUTEX_INITIALIZER;
static stack_info_t* stack_allocations = NULL;
static int num_stack_allocations = 0;
static int capacity_stack_allocations = 0;

static FILE* stack_log_file = NULL;

// Function to close the stack log file
void close_stack_log_file() {
    if (stack_log_file) {
        fprintf(stack_log_file, "BOX64_WINE: Stack log ended.\n");
        fclose(stack_log_file);
        stack_log_file = NULL;
    }
}

// Function to initialize the stack log file
void init_stack_log_file() {
    const char* log_file_path = getenv("BOX64_STACK_LOG_FILE");
    if (!log_file_path) {
        // Default to /sdcard/stack_log.txt on Android if not specified
        log_file_path = "/sdcard/stack_log.txt";
    }
    
    if (log_file_path) {
        stack_log_file = fopen(log_file_path, "a");
        if (!stack_log_file) {
            fprintf(stderr, "BOX64_WINE: Warning: Could not open stack log file %s\n", log_file_path);
        } else {
            fprintf(stack_log_file, "BOX64_WINE: Stack log started.\n");
            fflush(stack_log_file);
            atexit(close_stack_log_file); // Register cleanup function
        }
    }
}

static void add_stack_allocation(void* addr, size_t size) {
    pthread_mutex_lock(&stack_mutex);
    if (num_stack_allocations == capacity_stack_allocations) {
        capacity_stack_allocations = capacity_stack_allocations == 0 ? 4 : capacity_stack_allocations * 2;
        stack_allocations = (stack_info_t*)realloc(stack_allocations, capacity_stack_allocations * sizeof(stack_info_t));
    }
    stack_allocations[num_stack_allocations].addr = addr;
    stack_allocations[num_stack_allocations].size = size;
    num_stack_allocations++;
    pthread_mutex_unlock(&stack_mutex);
}

static void remove_stack_allocation(void* addr) {
    pthread_mutex_lock(&stack_mutex);
    for (int i = 0; i < num_stack_allocations; ++i) {
        if (stack_allocations[i].addr == addr) {
            for (int j = i; j < num_stack_allocations - 1; ++j) {
                stack_allocations[j] = stack_allocations[j + 1];
            }
            num_stack_allocations--;
            break;
        }
    }
    pthread_mutex_unlock(&stack_mutex);
}

size_t getStackSize(void* addr) {
    pthread_mutex_lock(&stack_mutex);
    size_t size = 0;
    for (int i = 0; i < num_stack_allocations; ++i) {
        if (stack_allocations[i].addr == addr) {
            size = stack_allocations[i].size;
            break;
        }
    }
    pthread_mutex_unlock(&stack_mutex);
    return size;
}

int GetTID(void)
{
    return HandleToULong(((HANDLE*)NtCurrentTeb())[9]);
}

int SchedYield(void)
{
    return (NtYieldExecution() != STATUS_NO_YIELD_PERFORMED);
}

int IsBridgeSignature(char s, char c)
{
    return FALSE;
}

void* GetSeg43Base()
{
    return NULL;
}

void* GetSegmentBase(uint32_t desc)
{
    printf_log(LOG_NONE, "GetSegmentBase does not apply to Wine dlls\n");
    return NULL;
}

void* EmuFork(void* emu, int forktype) { return NULL; }


void EmuX64Syscall(void* emu)
{
    printf_log(LOG_NONE, "EmuX64Syscall NYI\n");
}

void EmuX86Syscall(void* emu)
{
    printf_log(LOG_NONE, "EmuX86Syscall NYI\n");
}

const char* GetBridgeName(void* p)
{
    return NULL;
}

const char* GetNativeName(void* p)
{
    return NULL;
}

void* GetNativeFnc(uintptr_t fnc)
{
    return NULL;
}

void PersonalityAddrLimit32Bit(void)
{
}

int IsAddrElfOrFileMapped(uintptr_t addr)
{
    return 0;
}


int IsNativeCall(uintptr_t addr, int is32bits, uintptr_t* calladdress, uint16_t* retn)
{
    return 0;
}


ULONG_PTR default_zero_bits32 = 0x7fffffff;

static uint32_t prot_unix_to_win32(uint32_t unx)
{
    if ((unx & (PROT_READ | PROT_WRITE | PROT_EXEC)) == (PROT_READ | PROT_WRITE | PROT_EXEC))
        return PAGE_EXECUTE_READWRITE;
    if ((unx & (PROT_READ | PROT_EXEC)) == (PROT_READ | PROT_EXEC))
        return PAGE_EXECUTE_READ;
    if ((unx & PROT_EXEC) == PROT_EXEC)
        return PAGE_EXECUTE_READ;
    if ((unx & (PROT_READ | PROT_WRITE)) == (PROT_READ | PROT_WRITE))
        return PAGE_READWRITE;
    if ((unx & PROT_READ) == PROT_READ)
        return PAGE_READONLY;
    return 0;
}

int mprotect(void* addr, size_t len, int prot)
{
    NTSTATUS ntstatus;
    ULONG old_prot;
    SIZE_T allocsize = len;
    ntstatus = NtProtectVirtualMemory(NtCurrentProcess(), &addr, &allocsize, prot_unix_to_win32(prot), &old_prot);
    if (ntstatus != STATUS_SUCCESS) {
        return -1;
    }
    return 0;
}

#include <stdio.h>
#include <string.h>
#include <windows.h>
#include <ntstatus.h>
#include <winternl.h>
#include <pthread.h> // For mutex

#include "os.h"
#include "debug.h"
#include "wine/compiler.h"
#include "wine/debug.h"

#define MAP_GROWSDOWN 0x100 // Placeholder for Linux-specific MAP_GROWSDOWN flag

#define HandleToULong(h) ((ULONG)(ULONG_PTR)(h))

NTSTATUS WINAPI NtYieldExecution(void);

int box64_isAddressSpace32 = 0;

typedef struct stack_info_s {
    void* addr;
    size_t size;
} stack_info_t;

static pthread_mutex_t stack_mutex = PTHREAD_MUTEX_INITIALIZER;
static stack_info_t* stack_allocations = NULL;
static int num_stack_allocations = 0;
static int capacity_stack_allocations = 0;

static void add_stack_allocation(void* addr, size_t size) {
    pthread_mutex_lock(&stack_mutex);
    if (num_stack_allocations == capacity_stack_allocations) {
        capacity_stack_allocations = capacity_stack_allocations == 0 ? 4 : capacity_stack_allocations * 2;
        stack_allocations = (stack_info_t*)realloc(stack_allocations, capacity_stack_allocations * sizeof(stack_info_t));
    }
    stack_allocations[num_stack_allocations].addr = addr;
    stack_allocations[num_stack_allocations].size = size;
    num_stack_allocations++;
    pthread_mutex_unlock(&stack_mutex);
}

static void remove_stack_allocation(void* addr) {
    pthread_mutex_lock(&stack_mutex);
    for (int i = 0; i < num_stack_allocations; ++i) {
        if (stack_allocations[i].addr == addr) {
            for (int j = i; j < num_stack_allocations - 1; ++j) {
                stack_allocations[j] = stack_allocations[j + 1];
            }
            num_stack_allocations--;
            break;
        }
    }
    pthread_mutex_unlock(&stack_mutex);
}

size_t getStackSize(void* addr) {
    pthread_mutex_lock(&stack_mutex);
    size_t size = 0;
    for (int i = 0; i < num_stack_allocations; ++i) {
        if (stack_allocations[i].addr == addr) {
            size = stack_allocations[i].size;
            break;
        }
    }
    pthread_mutex_unlock(&stack_mutex);
    return size;
}

int GetTID(void)
{
    return HandleToULong(((HANDLE*)NtCurrentTeb())[9]);
}

int SchedYield(void)
{
    return (NtYieldExecution() != STATUS_NO_YIELD_PERFORMED);
}

int IsBridgeSignature(char s, char c)
{
    return FALSE;
}

void* GetSeg43Base()
{
    return NULL;
}

void* GetSegmentBase(uint32_t desc)
{
    printf_log(LOG_NONE, "GetSegmentBase does not apply to Wine dlls\n");
    return NULL;
}

void* EmuFork(void* emu, int forktype) { return NULL; }


void EmuX64Syscall(void* emu)
{
    printf_log(LOG_NONE, "EmuX64Syscall NYI\n");
}

void EmuX86Syscall(void* emu)
{
    printf_log(LOG_NONE, "EmuX86Syscall NYI\n");
}

const char* GetBridgeName(void* p)
{
    return NULL;
}

const char* GetNativeName(void* p)
{
    return NULL;
}

void* GetNativeFnc(uintptr_t fnc)
{
    return NULL;
}

void PersonalityAddrLimit32Bit(void)
{
}

int IsAddrElfOrFileMapped(uintptr_t addr)
{
    return 0;
}


int IsNativeCall(uintptr_t addr, int is32bits, uintptr_t* calladdress, uint16_t* retn)
{
    return 0;
}


ULONG_PTR default_zero_bits32 = 0x7fffffff;

static uint32_t prot_unix_to_win32(uint32_t unx)
{
    if ((unx & (PROT_READ | PROT_WRITE | PROT_EXEC)) == (PROT_READ | PROT_WRITE | PROT_EXEC))
        return PAGE_EXECUTE_READWRITE;
    if ((unx & (PROT_READ | PROT_EXEC)) == (PROT_READ | PROT_EXEC))
        return PAGE_EXECUTE_READ;
    if ((unx & PROT_EXEC) == PROT_EXEC)
        return PAGE_EXECUTE_READ;
    if ((unx & (PROT_READ | PROT_WRITE)) == (PROT_READ | PROT_WRITE))
        return PAGE_READWRITE;
    if ((unx & PROT_READ) == PROT_READ)
        return PAGE_READONLY;
    return 0;
}

int mprotect(void* addr, size_t len, int prot)
{
    NTSTATUS ntstatus;
    ULONG old_prot;
    SIZE_T allocsize = len;
    ntstatus = NtProtectVirtualMemory(NtCurrentProcess(), &addr, &allocsize, prot_unix_to_win32(prot), &old_prot);
    if (ntstatus != STATUS_SUCCESS) {
        return -1;
    }
    return 0;
}

void* mmap(void* addr, size_t length, int prot, int flags, int fd, off_t offset)
{
    NTSTATUS ntstatus;
    SIZE_T sz = length;
    ULONG_PTR limit;
    void* ret = NULL;

    if (addr != NULL) {
        return MAP_FAILED;
    }
    if (fd && fd != -1) {
        return MAP_FAILED;
    }
    if (offset) {
        return MAP_FAILED;
    }

    if (flags & MAP_32BIT)
        limit = default_zero_bits32;
    else
        limit = 0;

    ntstatus = NtAllocateVirtualMemory(NtCurrentProcess(), &ret, limit, &sz, MEM_COMMIT | MEM_RESERVE, prot_unix_to_win32(prot));
    // UNIVERSAL FIX: Force physical page commit
    if ((ntstatus == 0 || ntstatus == STATUS_SUCCESS) && ret != NULL && sz > 0) {
        volatile unsigned char *touch_page = (volatile unsigned char*)ret;
        size_t page_size = 0x1000;
        
        // Touch first byte of each 4KB page to force kernel mapping
        for (size_t offset = 0; offset < sz; offset += page_size) {
            if (offset < sz) {
                // Read then write to force commit
                unsigned char tmp = touch_page[offset];
                touch_page[offset] = tmp;
            }
        }
        printf_log(LOG_DEBUG, "BOX64_WINE: Force-committed %zu bytes at %p (status=0x%x)\n", 
                   sz, ret, ntstatus);
        if (flags & MAP_GROWSDOWN) {
            add_stack_allocation(ret, sz);
            printf_log(LOG_DEBUG, "BOX64_WINE: Tracking stack allocation at %p with size %zu\n", ret, sz);
        }
    }
    return ret;
}

int munmap(void* addr, size_t length)
{
    int ret = 0;
    remove_stack_allocation(addr);
    printf_log(LOG_DEBUG, "BOX64_WINE: Untracking stack allocation at %p\n", addr);
    if (NtFreeVirtualMemory(NtCurrentProcess(), &addr, &length, MEM_RELEASE))
        ret = -1;
    return ret;
}

void* InternalMmap(void* addr, unsigned long length, int prot, int flags, int fd, ssize_t offset)
{
    return mmap(addr, length, prot, flags, fd, offset);
}

int InternalMunmap(void* addr, unsigned long length)
{
    return munmap(addr, length);
}

void* WinMalloc(size_t size)
{
    void* ret;
    ret = RtlAllocateHeap(GetProcessHeap(), 0, size);
    return ret;
}

void* WinRealloc(void* ptr, size_t size)
{
    void* ret;
    if (!ptr)
        return WinMalloc(size);
    ret = RtlReAllocateHeap(GetProcessHeap(), HEAP_ZERO_MEMORY, ptr, size);
    return ret;
}

void* WinCalloc(size_t nmemb, size_t size)
{
    void* ret;
    ret = RtlAllocateHeap(GetProcessHeap(), HEAP_ZERO_MEMORY, nmemb * size);
    return ret;
}

void WinFree(void* ptr)
{
    RtlFreeHeap(GetProcessHeap(), 0, ptr);
}

void free(void* ptr)
{
    RtlFreeHeap(GetProcessHeap(), 0, ptr);
}

int VolatileRangesContains(uintptr_t addr)
{
    return 0;
}

int VolatileOpcodesHas(uintptr_t addr)
{
    return 0;
}

void PrintfFtrace(int prefix, const char* fmt, ...)
{
    static char buf[1024] = { 0 };

    char* p = buf;
    p[0] = '\0';
    if (prefix) strcpy(p, prefix > 1 ? "[\033[31mBOX64\033[0m] " : "[BOX64] ");
    va_list args;
    va_start(args, fmt);
    vsprintf(p + strlen(p), fmt, args);
    va_end(args);
    __wine_dbg_output(p);
}

void* GetEnv(const char* name)
{
    static char buf[1024] = { 0 };
    int len = GetEnvironmentVariableA(name, buf, sizeof(buf));
    return len ? buf : NULL;
}

int FileExist(const char* filename, int flags)
{
    DWORD attrs = GetFileAttributesA(filename);
    if (attrs == INVALID_FILE_ATTRIBUTES) return 0;
    if (flags == -1) return 1;

    if (flags & IS_FILE) {
        if ((attrs & FILE_ATTRIBUTE_DIRECTORY) || (attrs & FILE_ATTRIBUTE_DEVICE) || (attrs & FILE_ATTRIBUTE_REPARSE_POINT)) {
            return 0;
        }
    } else {
        if (!(attrs & FILE_ATTRIBUTE_DIRECTORY))
            return 0;
    }

    if (flags & IS_EXECUTABLE) {
        printf_log(LOG_NONE, "Warning: Executable check not implemented for Windows\n");
    }

    return 1;
}

int MakeDir(const char* folder)
{
    // TODO
    return 0;
}

size_t FileSize(const char* filename)
{
    // TODO
    return 0;
}
