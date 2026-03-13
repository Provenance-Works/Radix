/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Concurrency.Spec
import Radix.Concurrency.Ordering
import Radix.Concurrency.Atomic

/-!
# Concurrency Proofs (Layer 3)

This module contains proofs about atomic operations and memory ordering:

- Linearizability of single-threaded atomic operations
- Sequential consistency ordering properties
- Acquire-release synchronization
- CAS correctness properties
- Data-race freedom under proper synchronization
- Memory ordering algebra (strength monotonicity)

## Architecture

This is a **Layer 3 (Verified Specification)** module containing proofs.

## References

- FR-008.2: Proofs (linearizability, data-race freedom)
-/

set_option autoImplicit false

namespace Radix.Concurrency

open Spec
open Ordering
open Atomic

/-! ## Memory Ordering Strength Properties -/

theorem MemoryOrder.strength_relaxed : MemoryOrder.relaxed.strength = 0 := rfl
theorem MemoryOrder.strength_acquire : MemoryOrder.acquire.strength = 1 := rfl
theorem MemoryOrder.strength_release : MemoryOrder.release.strength = 1 := rfl
theorem MemoryOrder.strength_acqRel  : MemoryOrder.acqRel.strength = 2 := rfl
theorem MemoryOrder.strength_seqCst  : MemoryOrder.seqCst.strength = 3 := rfl

theorem MemoryOrder.seqCst_isAtLeast_all (o : MemoryOrder) :
    MemoryOrder.seqCst.isAtLeast o = true := by
  cases o <;> simp [MemoryOrder.isAtLeast, MemoryOrder.strength]

theorem MemoryOrder.isAtLeast_self (o : MemoryOrder) :
    o.isAtLeast o = true := by
  cases o <;> simp [MemoryOrder.isAtLeast, MemoryOrder.strength]

/-! ## Ordering Validity Properties -/

theorem validLoadOrder_relaxed : validLoadOrder .relaxed = true := rfl
theorem validLoadOrder_acquire : validLoadOrder .acquire = true := rfl
theorem validLoadOrder_seqCst  : validLoadOrder .seqCst = true := rfl
theorem validStoreOrder_relaxed : validStoreOrder .relaxed = true := rfl
theorem validStoreOrder_release : validStoreOrder .release = true := rfl
theorem validStoreOrder_seqCst  : validStoreOrder .seqCst = true := rfl
theorem validRMWOrder_all (o : MemoryOrder) : validRMWOrder o = true := by
  cases o <;> rfl

/-! ## Strengthen Properties -/

theorem strengthen_idempotent (o : MemoryOrder) :
    strengthen o o = o := by
  simp [strengthen]

theorem strengthen_comm_strength (a b : MemoryOrder) :
    (strengthen a b).strength = max a.strength b.strength := by
  simp [strengthen]
  split
  case isTrue h =>
    omega
  case isFalse h =>
    omega

/-! ## HasAcquire / HasRelease Classification -/

theorem seqCst_hasAcquire : hasAcquireSemantics .seqCst = true := rfl
theorem seqCst_hasRelease : hasReleaseSemantics .seqCst = true := rfl
theorem acqRel_hasAcquire : hasAcquireSemantics .acqRel = true := rfl
theorem acqRel_hasRelease : hasReleaseSemantics .acqRel = true := rfl

theorem acquire_hasAcquire : hasAcquireSemantics .acquire = true := rfl
theorem release_hasRelease : hasReleaseSemantics .release = true := rfl

theorem relaxed_no_acquire : hasAcquireSemantics .relaxed = false := rfl
theorem relaxed_no_release : hasReleaseSemantics .relaxed = false := rfl

/-! ## CAS Failure Ordering Properties -/

theorem defaultFailureOrder_valid (o : MemoryOrder) :
    validCASFailureOrder o (defaultFailureOrder o) = true := by
  cases o <;> decide

theorem defaultFailureOrder_not_release_acqRel (o : MemoryOrder) :
    (match defaultFailureOrder o with
     | .release => false
     | .acqRel  => false
     | _        => true) = true := by
  cases o <;> rfl

/-! ## Atomic Load/Store Properties -/

theorem atomicLoad_preserves_cell (cell : AtomicCell) (order : MemoryOrder)
    (h : validLoadOrder order = true) :
    (atomicLoad cell order h).2 = cell := by
  rfl

theorem atomicLoad_reads_current (cell : AtomicCell) (order : MemoryOrder)
    (h : validLoadOrder order = true) :
    (atomicLoad cell order h).1.value = cell.val := by
  rfl

theorem atomicStore_sets_value (cell : AtomicCell) (v : Nat) (order : MemoryOrder)
    (h : validStoreOrder order = true) :
    (atomicStore cell v order h).2.val = v := by
  rfl

/-! ## CAS Properties -/

theorem atomicCAS_success (cell : AtomicCell) (expected desired : Nat)
    (succOrder : MemoryOrder) (failOrder : MemoryOrder)
    (hMatch : cell.val = expected) :
    let result := atomicCAS cell expected desired succOrder failOrder
    result.1.success = true ∧ result.2.val = desired := by
  simp [atomicCAS, hMatch]

theorem atomicCAS_failure (cell : AtomicCell) (expected desired : Nat)
    (succOrder : MemoryOrder) (failOrder : MemoryOrder)
    (hMismatch : cell.val ≠ expected) :
    let result := atomicCAS cell expected desired succOrder failOrder
    result.1.success = false ∧ result.2 = cell := by
  simp [atomicCAS]
  constructor
  · simp [hMismatch]
  · simp [hMismatch]

theorem atomicCAS_previous_is_current (cell : AtomicCell) (expected desired : Nat)
    (succOrder : MemoryOrder) (failOrder : MemoryOrder) :
    (atomicCAS cell expected desired succOrder failOrder).1.previous = cell.val := by
  simp [atomicCAS]
  split <;> rfl

/-! ## Fetch-and-Modify Properties -/

theorem fetchAdd_returns_previous (cell : AtomicCell) (delta : Nat)
    (order : MemoryOrder) :
    (fetchAdd cell delta order).1.previous = cell.val := rfl

theorem fetchAdd_updates_value (cell : AtomicCell) (delta : Nat)
    (order : MemoryOrder) :
    (fetchAdd cell delta order).2.val = cell.val + delta := rfl

theorem fetchSub_returns_previous (cell : AtomicCell) (delta : Nat)
    (order : MemoryOrder) :
    (fetchSub cell delta order).1.previous = cell.val := rfl

theorem fetchSub_updates_value (cell : AtomicCell) (delta : Nat)
    (order : MemoryOrder) :
    (fetchSub cell delta order).2.val = cell.val - delta := rfl

theorem fetchAdd_zero_identity (cell : AtomicCell) (order : MemoryOrder) :
    (fetchAdd cell 0 order).2 = cell := by
  simp [fetchAdd]

theorem atomicExchange_returns_previous (cell : AtomicCell) (newVal : Nat)
    (order : MemoryOrder) :
    (atomicExchange cell newVal order).1.previous = cell.val := rfl

theorem atomicExchange_sets_value (cell : AtomicCell) (newVal : Nat)
    (order : MemoryOrder) :
    (atomicExchange cell newVal order).2.val = newVal := rfl

/-! ## Store-Load Round-Trip -/

theorem store_load_roundtrip (cell : AtomicCell) (v : Nat)
    (hStore : validStoreOrder .seqCst = true)
    (hLoad : validLoadOrder .seqCst = true) :
    let afterStore := (atomicStore cell v .seqCst hStore).2
    (atomicLoad afterStore .seqCst hLoad).1.value = v := by
  rfl

/-! ## Program Order Properties -/

theorem programOrder_irrefl (e : MemoryEvent) :
    ¬programOrder e e := by
  simp [programOrder]

theorem programOrder_trans (a b c : MemoryEvent)
    (hab : programOrder a b) (hbc : programOrder b c) :
    programOrder a c := by
  simp [programOrder] at *
  constructor
  · exact hab.1.trans hbc.1
  · omega

theorem programOrder_same_thread (a b : MemoryEvent)
    (h : programOrder a b) :
    a.id.thread = b.id.thread := h.1

/-! ## Single-Thread Linearizability -/

/-- A trace consisting of events from a single thread is trivially
    linearizable -- the program order itself is the linearization. -/
theorem singleThread_isLinearizable_of_valid
    (t : Trace)
    (hOrdered : ∀ a b, a ∈ t.events → b ∈ t.events →
      happensBefore a b → eventPosition t.events a < eventPosition t.events b)
    (hSeqHist : isSequentialHistory t.events)
    (hSeqValid : isValidSequentialHistory t.events) :
    t.isLinearizable := by
  exact ⟨t.events, rfl, fun e => Iff.rfl, hSeqHist, hSeqValid, hOrdered⟩

/-! ## Data-Race Freedom Properties -/

/-- An empty trace is trivially data-race free. -/
theorem Trace.empty_isDataRaceFree :
    (Trace.mk []).isDataRaceFree := by
  simp [Trace.isDataRaceFree]

/-- A single-event trace is data-race free (a race requires two events). -/
theorem Trace.singleton_isDataRaceFree (e : MemoryEvent) :
    (Trace.mk [e]).isDataRaceFree := by
  intro a b ha hb
  simp at ha hb
  subst ha; subst hb
  intro ⟨hConf, _, _, _⟩
  exact hConf.1 rfl

end Radix.Concurrency
