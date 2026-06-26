# Box64 - Call of Duty: Black Ops 2 (BO2) Compatibility Fork

**PROJECT STATUS: WORK IN PROGRESS / EXPERIMENTAL**
As of right now, there is NO working patch to make BO2 fully playable. This fork is in active development.

This is a specialized, experimental fork of **[Box64](https://github.com/ptitSeb/box64)** specifically targeted at patching x86_64 to ARM64 instruction translation, signal handling, and memory mapping trying to get **Call of Duty: Black Ops 2 (Redacted Version)** running on Android/ARM Linux. 

Huge shoutout and all core credit goes to **[ptitSeb](https://github.com/ptitSeb)** and the incredible contributors of the original Box64 repository.

---

## Current Progress

While the game is not fully booting yet, significant hurdles in the boot sequence have been cleared:
* **TLS (Thread Local Storage) Fixes:** Addressed complex Windows thread initialization that previously caused immediate crashes under Wine/box64.
* **RC4 Cipher Loop:** Successfully navigating the game's early execution RC4 decryption loops.
* **Zone Mapping:** Implemented fixes for the game's memory zone allocation and asset mapping logic.

**Testing Environment:** * Currently testing strictly under Interpreter Mode (`BOX64_DYNAREC=0`). Nothing, but just because redactedbarbone.exe doesn't work with dynarec

---

## Tools used
* **Ghidra:**
* **Winlator:**
* **VS Code:**

---

## Contributing

**please do not open Pull Requests (PRs) just yet.** But contributions well be welcomed
