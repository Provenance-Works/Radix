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

/-- Trusted witness that the modeled hardware state space is inhabited,
    allowing opaque hardware-state assumptions to be quantified over. -/
axiom trust_hwConcurrencyState_nonempty : Nonempty HWConcurrencyState
instance : Nonempty HWConcurrencyState := trust_hwConcurrencyState_nonempty

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

/-! Sequential consistency (SeqCst) operations on all processors
    participate in a single total order consistent with program order.

    This total order is SEPARATE from happens-before: the C11 model
    defines a distinct "S" order over SeqCst operations.  We model
    it as an opaque relation whose totality is the axiom.

    Reference: Intel SDM Vol. 3A, Section 8.2.2:
    "Reads are not reordered with other reads. Writes are not
     reordered with older reads. Writes to memory are not reordered
     with other writes [for MFENCE/locked instructions]."

    ARM Architecture Reference Manual, Section B2.3:
    "The global order of all Load-Acquire and Store-Release
     operations is consistent with the order in which they
     appear in each PE's program order." -/

/-- An opaque total order over SeqCst events representing the
    single global S-order of the C11 memory model.  Lean cannot
    compute or inspect this relation. -/
opaque seqCstOrder (a b : MemoryEvent) : Prop

axiom trust_seqcst_total_order
    (a b : MemoryEvent)
    (hA : a.order = .seqCst)
    (hB : b.order = .seqCst)
    (hNeq : a.id ≠ b.id) :
    seqCstOrder a b ∨ seqCstOrder b a

/-- SeqCst total order is consistent with happens-before:
    if a happens-before b and both are SeqCst, then a is ordered
    before b in the SeqCst total order. -/
axiom trust_seqcst_consistent_with_hb
    (a b : MemoryEvent)
    (hA : a.order = .seqCst)
    (hB : b.order = .seqCst)
    (hHB : happensBefore a b) :
    seqCstOrder a b

end Radix.Concurrency.Assumptions
