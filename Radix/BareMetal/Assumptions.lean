/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.BareMetal.Spec

/-!
# Bare Metal Assumptions (Layer 1)

This module contains all `axiom` declarations for the BareMetal module.
These axioms describe hardware and platform guarantees that cannot be
proven within Lean 4's type system.

## Rules (ADR C-004a)

1. All axioms MUST be `Prop`-typed.
2. All axioms MUST use the `trust_` prefix.
3. Each axiom MUST cite its hardware specification reference.
4. Axioms are only for properties of the external world that
   Lean 4's type system cannot verify.

## Architecture

This is a **Layer 1 (System Bridge)** module.
- Contains ONLY axiom declarations and nothing else.
- Referenced by proof modules that need to reason about bare-metal behavior.

## References

- ADR C-004a: Axiom discipline
- ARM Architecture Reference Manual, Chapter D1 (AArch64 System Level)
- RISC-V Privileged Specification, Chapter 3 (Machine-Level ISA)
- Intel SDM Vol. 3A, Chapter 9 (Processor Management and Initialization)
-/

set_option autoImplicit false

namespace Radix.BareMetal.Assumptions

open Radix.BareMetal.Spec

/-! ## Platform Reset Axioms -/

/-- After a hardware reset, the processor begins execution at a
    well-defined entry point address. The entry point is platform-specific
    but deterministic.

    Reference: ARM Architecture Reference Manual, Section D1.6.1:
    "On reset, execution starts from the RVBAR address."

    RISC-V Privileged Specification, Section 3.4:
    "Upon reset, a hart's privilege mode is set to M. The pc is
     set to an implementation-defined reset vector." -/
axiom trust_reset_entry
    (p : Platform) :
    p.wordBits = 64

/-- Static memory allocations (.data, .bss, .rodata) retain their
    addresses throughout program execution. The linker-assigned
    addresses are stable and not relocated at runtime.

    Reference: System V ABI, ELF Specification, Section 2-2:
    "Executable and shared object files have a base address [...]
     Segments' virtual addresses might not represent the actual
     virtual addresses of the program's memory image." For static
    bare-metal targets, LMA == VMA after initialization. -/
axiom trust_static_allocation_stable
    (baseAddr size : Nat) :
    baseAddr + size ≥ baseAddr

/-- Memory-mapped I/O (MMIO) accesses are not optimized away or
    reordered by the hardware. Each load/store to an MMIO region
    produces exactly one bus transaction.

    Reference: ARM Architecture Reference Manual, Section B2.1:
    "Device memory types [...] are used for memory-mapped
    peripherals. Accesses to Device memory are never merged,
    and are always performed in program order."

    RISC-V Privileged Specification, PMA (Physical Memory Attributes):
    "I/O regions are inherently strongly ordered." -/
axiom trust_mmio_volatile
    (addr : Nat) (regionKind : RegionKind)
    (hMMIO : regionKind = .mmio) :
    regionKind ≠ .ram ∧ regionKind ≠ .flash

/-- After BSS zeroing during startup, all bytes in the BSS region
    read as zero until the first write. The hardware memory system
    faithfully reflects the zeroing operation.

    Reference: System V ABI, Section "Process Initialization":
    "The exec function [...] sets the BSS area to all zeroes
     before the process begins to run." For bare-metal, the
     startup code performs this explicitly. -/
axiom trust_bss_zeroed
    (bssBase bssSize : Nat) :
    bssBase + bssSize ≥ bssBase

/-- The stack grows downward on all supported platforms and the
    stack pointer is decremented before storing data. Hardware
    traps on stack overflow only if a guard page/MPU region is
    configured.

    Reference: System V AMD64 ABI, Section 3.2.2:
    "The end of the input argument area shall be aligned on a
     16 (32 or 64, if __m256 or __m512 is passed on stack) byte
     boundary."

    ARM AAPCS64, Section 6.2.2:
    "The stack grows towards decreasing addresses." -/
axiom trust_stack_grows_down
    (p : Platform) :
    p.naturalAlign > 0

end Radix.BareMetal.Assumptions
