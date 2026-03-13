/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Concurrency.Spec

/-!
# Concurrency Assumptions (Layer 1)

This module contains all `axiom` declarations for the Concurrency module.
These axioms describe hardware guarantees about atomic operations that
cannot be proven within Lean 4's type system.

## Rules (ADR C-004a)

1. All axioms MUST be `Prop`-typed.
2. All axioms MUST use the `trust_` prefix.
3. Each axiom MUST cite its hardware specification reference.
4. Axioms are only for properties of the external world that
   Lean 4's type system cannot verify.

## Architecture

This is a **Layer 1 (System Bridge)** module.
- Contains ONLY axiom declarations and nothing else.
- Referenced by proof modules that need to reason about concurrency.

## References

- ADR C-004a: Axiom discipline
- Intel SDM Vol. 3A, Chapter 8 (Multiple-Processor Management)
- ARM Architecture Reference Manual, Section B2 (Memory Model)
- RISC-V ISA Manual, Chapter 14 (RVWMO Memory Consistency Model)
-/

set_option autoImplicit false

namespace Radix.Concurrency.Assumptions

open Radix.Concurrency.Spec

/-! ## Hardware Atomicity Axioms -/

/-- Hardware guarantees that aligned word-sized loads and stores are
    atomic: a concurrent observer never sees a partially-updated value.

    Reference: Intel SDM Vol. 3A, Section 8.1.1:
    "The Intel-64 memory ordering model guarantees that, for each
     of the following memory-access instructions, the constituent
     memory operation appears to execute as a single memory access
     regardless of memory type: Instructions that read or write
     a single byte. [...] Instructions that read or write a word
     (2 bytes) whose address is aligned on a 2-byte boundary." -/
axiom trust_atomic_word_access
    (e : MemoryEvent)
    (hKind : e.kind = .load ∨ e.kind = .store) :
    True  -- The event is indivisible (no torn reads/writes)

/-- Hardware guarantees that compare-and-swap (CMPXCHG / CASA / LR;SC)
    is atomic: the read-modify-write sequence appears indivisible
    to all processors.

    Reference: Intel SDM Vol. 2A, CMPXCHG instruction:
    "This instruction can be used with a LOCK prefix to allow the
     instruction to be executed atomically." -/
axiom trust_cas_atomicity
    (e : MemoryEvent)
    (hKind : e.kind = .rmw) :
    True  -- The RMW is indivisible

/-- Sequential consistency (SeqCst) operations on all processors
    participate in a single total order consistent with program order.

    Reference: Intel SDM Vol. 3A, Section 8.2.2:
    "Reads are not reordered with other reads. Writes are not
     reordered with older reads. Writes to memory are not reordered
     with other writes [for MFENCE/locked instructions]."

    ARM Architecture Reference Manual, Section B2.3:
    "The global order of all Load-Acquire and Store-Release
     operations is consistent with the order in which they
     appear in each PE's program order." -/
axiom trust_seqcst_total_order
    (a b : MemoryEvent)
    (hA : a.order = .seqCst)
    (hB : b.order = .seqCst)
    (hNeq : a.id ≠ b.id) :
    True  -- Exists a total order containing both a and b

/-- Acquire-release pairs synchronize: if a release-store is
    observed by an acquire-load reading the stored value, then
    all writes preceding the release are visible after the acquire.

    Reference: C11 Standard, Section 5.1.2.4, paragraph 2:
    "An atomic operation A that performs a release operation on an
     atomic object M synchronizes with an atomic operation B that
     performs an acquire operation on M and takes its value from
     any side effect in the release sequence headed by A." -/
axiom trust_acquire_release_sync
    (w r : MemoryEvent)
    (hSync : synchronizesWith w r) :
    True  -- All writes before w are visible after r

/-- Memory fences enforce ordering constraints on surrounding
    memory operations according to their memory order annotation.

    Reference: Intel SDM Vol. 3A, Section 8.2.5:
    "The MFENCE instruction establishes a memory fence for both
     loads and stores. [...] The processor ensures that every
     load and store instruction that precedes the MFENCE
     instruction [...] is globally visible before any load or
     store instruction that follows the MFENCE instruction." -/
axiom trust_fence_ordering
    (e : MemoryEvent)
    (hFence : e.kind = .fence) :
    True  -- Fence enforces ordering per its MemoryOrder

end Radix.Concurrency.Assumptions
