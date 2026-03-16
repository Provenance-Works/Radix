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

/-! ## Opaque Hardware Types -/

/-- An opaque snapshot of the hardware memory subsystem state.
    Lean cannot construct, inspect, or pattern-match on values of
    this type.  It exists so that axioms about concurrency behaviour
    are genuinely unprovable within the type system. -/
opaque HWConcurrencyState : Type

axiom hwConcurrencyState_nonempty : Nonempty HWConcurrencyState
instance : Nonempty HWConcurrencyState := hwConcurrencyState_nonempty

/-- The result of executing an atomic instruction on real hardware.
    The output trace of memory events is opaque — we cannot inspect
    it, so axioms that quantify over it remain unprovable. -/
noncomputable opaque hwExecute (s : HWConcurrencyState) (events : List MemoryEvent) :
    HWConcurrencyState

/-- Whether a hardware execution produced a globally-consistent
    observation for a given event.  Opaque — Lean cannot compute it. -/
opaque hwObservedAtomic (s : HWConcurrencyState) (e : MemoryEvent) : Prop

/-! ## Hardware Atomicity Axioms -/

/-- Hardware guarantees that aligned word-sized loads and stores are
    atomic: a concurrent observer never sees a partially-updated value.

    The atomicity assertion is about the *hardware execution state*,
    not about ordering-validity (which is a Lean-decidable function).

    Reference: Intel SDM Vol. 3A, Section 8.1.1:
    "The Intel-64 memory ordering model guarantees that, for each
     of the following memory-access instructions, the constituent
     memory operation appears to execute as a single memory access." -/
axiom trust_atomic_word_access
    (s : HWConcurrencyState)
    (e : MemoryEvent)
    (hKind : e.kind = .load ∨ e.kind = .store) :
    hwObservedAtomic s e

/-- Hardware guarantees that compare-and-swap (CMPXCHG / CASA / LR;SC)
    is atomic: the read-modify-write sequence appears indivisible
    to all processors.

    Reference: Intel SDM Vol. 2A, CMPXCHG instruction:
    "This instruction can be used with a LOCK prefix to allow the
     instruction to be executed atomically." -/
axiom trust_cas_atomicity
    (s : HWConcurrencyState)
    (e : MemoryEvent)
    (hKind : e.kind = .rmw) :
    hwObservedAtomic s e

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
    happensBefore a b ∨ happensBefore b a

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
    happensBefore w r

/-- Memory fences enforce ordering constraints on surrounding
    memory operations according to their memory order annotation.
    The hardware guarantees that a fence instruction produces an
    observable ordering barrier in the concurrency state.

    Reference: Intel SDM Vol. 3A, Section 8.2.5:
    "The MFENCE instruction establishes a memory fence for both
     loads and stores. [...] The processor ensures that every
     load and store instruction that precedes the MFENCE
     instruction [...] is globally visible before any load or
     store instruction that follows the MFENCE instruction." -/
axiom trust_fence_ordering
    (s s' : HWConcurrencyState)
    (e : MemoryEvent)
    (hFence : e.kind = .fence)
    (hExec : s' = hwExecute s [e])
    (a b : MemoryEvent)
    (hBefore : programOrder a e)
    (hAfter : programOrder e b) :
    happensBefore a b

end Radix.Concurrency.Assumptions
