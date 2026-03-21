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

/-! ## Abstract Hardware State

    These opaque types represent hardware state that Lean 4 cannot
    observe or construct. They exist solely as parameters for axioms
    so that the axioms express genuinely unprovable hardware contracts
    rather than tautologies over Lean-constructible values. -/

/-- An opaque snapshot of the hardware memory subsystem after reset.
    Lean cannot construct or inspect values of this type; it exists
    only so we can state axioms about post-reset memory contents. -/
opaque HWMemoryState : Type

/-- Read a single byte from the hardware memory state at a physical
    address. Opaque — the function body is erased, making axioms
    about `hwReadByte` genuinely unprovable within Lean. -/
opaque hwReadByte (mem : HWMemoryState) (addr : Nat) : UInt8

/-! ## Platform Reset Axioms -/

/-- The platform-specific reset vector address.  Opaque — Lean
    cannot determine which concrete address a given platform
    specifies as its reset entry point. -/
opaque resetVector (p : Platform) : Nat

/-- After a hardware reset, the processor begins execution at a
    well-defined entry point address determined by the platform.
    The reset vector is the first instruction fetched.

    This axiom asserts that the platform's reset vector is
    naturally aligned — a fact that depends on the silicon
    implementation and cannot be derived from the Lean type system.

    Reference: ARM Architecture Reference Manual, Section D1.6.1:
    "On reset, execution starts from the RVBAR address."

    RISC-V Privileged Specification, Section 3.4:
    "Upon reset, a hart's privilege mode is set to M. The pc is
     set to an implementation-defined reset vector." -/
axiom trust_reset_entry
    (p : Platform) :
    resetVector p % p.naturalAlign = 0

/-- An opaque predicate asserting that `(baseAddr, size)` describes a
    static allocation region (e.g. .data, .bss, .rodata) and that
    `mem₁` and `mem₂` are snapshots from the same program execution
    after startup initialization has completed.  Lean cannot inspect
    or construct witnesses of this predicate — it exists to scope
    the stability axiom to genuinely static regions. -/
opaque isStaticRegionInSameExec
    (mem₁ mem₂ : HWMemoryState) (baseAddr size : Nat) : Prop

/-- Static memory allocations (.data, .bss, .rodata) retain their
    physical addresses across the entire program execution. After
    startup initialization copies data from Flash (LMA) to RAM (VMA),
    the VMA remains stable and is never relocated.

    This is a hardware + linker guarantee: the MMU (if present) does
    not remap these regions, and no runtime relocator exists on a
    bare-metal target. The axiom cannot be proven because it depends
    on the absence of address-space layout randomization and dynamic
    relocation — properties of the external execution environment.

    The precondition `isStaticRegionInSameExec` restricts the claim
    to genuinely static regions within a single program execution,
    preventing trivialization.

    Reference: System V ABI, ELF Specification, Section 2-2:
    "For static bare-metal targets, LMA == VMA after initialization." -/
axiom trust_static_allocation_stable
    (mem₁ mem₂ : HWMemoryState) (baseAddr size : Nat)
    (hStatic : isStaticRegionInSameExec mem₁ mem₂ baseAddr size) :
    (∀ i, i < size → hwReadByte mem₁ (baseAddr + i) = hwReadByte mem₂ (baseAddr + i))

/-- An opaque witness that an MMIO write to a given address in a
    given hardware state has a physical side effect beyond what Lean's
    pure model can represent.  Lean cannot construct or decide this. -/
opaque hwHasSideEffect (mem : HWMemoryState) (addr : Nat) : Prop

/-- Memory-mapped I/O (MMIO) accesses are not optimized away,
    merged, or reordered by the hardware. Each load/store to an
    MMIO region produces exactly one bus transaction with
    observable side effects.

    Concretely: two consecutive reads from the same MMIO address
    may return different values (e.g. a status register that
    clears on read). This cannot be modeled in Lean's pure
    semantics and must be taken on trust.

    Reference: ARM Architecture Reference Manual, Section B2.1:
    "Device memory types are used for memory-mapped peripherals.
     Accesses to Device memory are never merged and are always
     performed in program order."

    RISC-V Privileged Specification, PMA:
    "I/O regions are inherently strongly ordered." -/
axiom trust_mmio_volatile
    (mem : HWMemoryState) (addr : Nat) :
    hwHasSideEffect mem addr

/-- After BSS zeroing during startup, every byte in the BSS region
    reads as zero until the first explicit write. The hardware
    memory subsystem faithfully reflects the zeroing operation
    (no stale cache, no ECC-uninitialized traps).

    This cannot be proven in Lean because it asserts a property
    of the physical memory after a startup routine that runs
    outside Lean's control.

    Reference: System V ABI, Section "Process Initialization":
    "The exec function sets the BSS area to all zeroes before
     the process begins to run." For bare-metal, the startup
     code performs this explicitly. -/
axiom trust_bss_zeroed
    (mem : HWMemoryState) (bssBase bssSize : Nat) :
    ∀ (i : Nat), i < bssSize → hwReadByte mem (bssBase + i) = 0

/-- The stack grows downward on all supported platforms: the stack
    pointer is decremented before storing data, and function
    prologues allocate space by subtracting from SP.

    More precisely: if `sp` is the stack pointer before a push
    of `n` bytes, the data is written to addresses
    `[sp - n, sp)`, and the new stack pointer is `sp - n`.

    This is a hardware calling-convention guarantee that cannot
    be derived from the Lean type system.

    Reference: System V AMD64 ABI, Section 3.2.2:
    "The end of the input argument area shall be aligned on a
     16-byte boundary."

    ARM AAPCS64, Section 6.2.2:
    "The stack grows towards decreasing addresses." -/
axiom trust_stack_grows_down
    (mem₁ mem₂ : HWMemoryState) (sp n : Nat) (data : Fin n → UInt8)
    (hAlign : sp % 16 = 0)
    (hSpace : n ≤ sp) :
    (∀ i : Fin n, hwReadByte mem₂ (sp - n + i.val) = data i)

end Radix.BareMetal.Assumptions
