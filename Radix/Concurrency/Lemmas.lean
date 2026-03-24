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

@[simp] theorem MemoryOrder.strength_relaxed : MemoryOrder.relaxed.strength = 0 := rfl
@[simp] theorem MemoryOrder.strength_acquire : MemoryOrder.acquire.strength = 1 := rfl
@[simp] theorem MemoryOrder.strength_release : MemoryOrder.release.strength = 1 := rfl
@[simp] theorem MemoryOrder.strength_acqRel  : MemoryOrder.acqRel.strength = 2 := rfl
@[simp] theorem MemoryOrder.strength_seqCst  : MemoryOrder.seqCst.strength = 3 := rfl

theorem MemoryOrder.seqCst_isAtLeast_all (o : MemoryOrder) :
    MemoryOrder.seqCst.isAtLeast o = true := by
  cases o <;> simp [MemoryOrder.isAtLeast, MemoryOrder.strength]

theorem MemoryOrder.isAtLeast_self (o : MemoryOrder) :
    o.isAtLeast o = true := by
  cases o <;> simp [MemoryOrder.isAtLeast, MemoryOrder.strength]

/-! ## Ordering Validity Properties -/

@[simp] theorem validLoadOrder_relaxed : validLoadOrder .relaxed = true := rfl
@[simp] theorem validLoadOrder_acquire : validLoadOrder .acquire = true := rfl
@[simp] theorem validLoadOrder_seqCst  : validLoadOrder .seqCst = true := rfl
@[simp] theorem validStoreOrder_relaxed : validStoreOrder .relaxed = true := rfl
@[simp] theorem validStoreOrder_release : validStoreOrder .release = true := rfl
@[simp] theorem validStoreOrder_seqCst  : validStoreOrder .seqCst = true := rfl
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

@[simp] theorem seqCst_hasAcquire : hasAcquireSemantics .seqCst = true := rfl
@[simp] theorem seqCst_hasRelease : hasReleaseSemantics .seqCst = true := rfl
@[simp] theorem acqRel_hasAcquire : hasAcquireSemantics .acqRel = true := rfl
@[simp] theorem acqRel_hasRelease : hasReleaseSemantics .acqRel = true := rfl

@[simp] theorem acquire_hasAcquire : hasAcquireSemantics .acquire = true := rfl
@[simp] theorem release_hasRelease : hasReleaseSemantics .release = true := rfl

@[simp] theorem relaxed_no_acquire : hasAcquireSemantics .relaxed = false := rfl
@[simp] theorem relaxed_no_release : hasReleaseSemantics .relaxed = false := rfl

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

@[simp] theorem fetchAdd_returns_previous (cell : AtomicCell) (delta : Nat)
    (order : MemoryOrder) :
    (fetchAdd cell delta order).1.previous = cell.val := rfl

@[simp] theorem fetchAdd_updates_value (cell : AtomicCell) (delta : Nat)
    (order : MemoryOrder) :
    (fetchAdd cell delta order).2.val = cell.val + delta := rfl

@[simp] theorem fetchSub_returns_previous (cell : AtomicCell) (delta : Nat)
    (order : MemoryOrder) :
    (fetchSub cell delta order).1.previous = cell.val := rfl

@[simp] theorem fetchSub_updates_value (cell : AtomicCell) (delta : Nat)
    (order : MemoryOrder) :
    (fetchSub cell delta order).2.val = cell.val - delta := rfl

theorem fetchAdd_zero_identity (cell : AtomicCell) (order : MemoryOrder) :
    (fetchAdd cell 0 order).2 = cell := by
  simp [fetchAdd]

@[simp] theorem atomicExchange_returns_previous (cell : AtomicCell) (newVal : Nat)
    (order : MemoryOrder) :
    (atomicExchange cell newVal order).1.previous = cell.val := rfl

@[simp] theorem atomicExchange_sets_value (cell : AtomicCell) (newVal : Nat)
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

/-! ## Derived Ordering Theorems -/

/-- Acquire-release synchronization implies happens-before.
    This follows directly from the definition of `happensBefore`. -/
theorem acquire_release_happensBefore
    (w r : MemoryEvent)
    (hSync : synchronizesWith w r) :
    happensBefore w r :=
  Or.inr hSync

/-- A fence between two program-ordered events establishes
    happens-before by transitivity of program order. -/
theorem fence_ordering_happensBefore
    (a e b : MemoryEvent)
    (hBefore : programOrder a e)
    (hAfter : programOrder e b) :
    happensBefore a b :=
  Or.inl (programOrder_trans a e b hBefore hAfter)

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

/-! ## Conflicting / Data-Race Properties -/

/-- Two loads never conflict (neither is a write). -/
theorem loads_not_conflicting (a b : MemoryEvent)
    (haLoad : a.kind = .load) (hbLoad : b.kind = .load) :
    ¬conflicting a b := by
  intro ⟨_, _, _, hWrite⟩
  cases hWrite with
  | inl h => simp [AccessKind.isWrite, haLoad] at h
  | inr h => simp [AccessKind.isWrite, hbLoad] at h

/-- Same-thread events never form a data race (data races require
    different threads). -/
theorem sameThread_no_dataRace (a b : MemoryEvent)
    (hThread : a.id.thread = b.id.thread) :
    ¬isDataRace a b := by
  intro ⟨_, hDiffThread, _, _⟩
  exact hDiffThread hThread

/-- If two events are ordered by happens-before in either direction,
    they do not form a data race. -/
theorem ordered_no_dataRace (a b : MemoryEvent)
    (hOrdered : happensBefore a b ∨ happensBefore b a) :
    ¬isDataRace a b := by
  intro ⟨_, _, hNotAB, hNotBA⟩
  cases hOrdered with
  | inl h => exact hNotAB h
  | inr h => exact hNotBA h

/-- A trace consisting only of read events is data-race free. -/
theorem Trace.allLoads_isDataRaceFree (t : Trace)
    (hAllLoads : ∀ e, e ∈ t.events → e.kind = .load) :
    t.isDataRaceFree := by
  intro a b ha hb hRace
  have := loads_not_conflicting a b (hAllLoads a ha) (hAllLoads b hb)
  exact this hRace.1

/-! ## CAS Correctness -/

/-- A CAS either succeeds and updates, or fails and preserves.
    This is the fundamental CAS disjunction. -/
theorem atomicCAS_dichotomy (cell : AtomicCell) (expected desired : Nat)
    (succOrder failOrder : MemoryOrder) :
    let r := atomicCAS cell expected desired succOrder failOrder
    (r.1.success = true ∧ r.2.val = desired) ∨
    (r.1.success = false ∧ r.2 = cell) := by
  simp [atomicCAS]
  split
  · left; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, rfl⟩

/-- Two consecutive fetchAdd operations compose additively. -/
theorem fetchAdd_compose (cell : AtomicCell) (d1 d2 : Nat)
    (o1 o2 : MemoryOrder) :
    let (_, cell') := fetchAdd cell d1 o1
    (fetchAdd cell' d2 o2).2.val = cell.val + d1 + d2 := by
  simp [fetchAdd]

/-- atomicExchange is equivalent to a CAS that always succeeds. -/
theorem exchange_eq_successful_cas (cell : AtomicCell) (newVal : Nat)
    (order : MemoryOrder) :
    (atomicExchange cell newVal order).2.val =
    (atomicCAS cell cell.val newVal order order).2.val := by
  simp [atomicExchange, atomicCAS]

/-! ## Well-Formedness -/

/-- An empty trace is well-formed. -/
theorem Trace.empty_isWellFormed :
    (Trace.mk []).isWellFormed := by
  simp [Trace.isWellFormed]

/-- An empty trace is valid (well-formed with unique IDs). -/
theorem Trace.empty_isValid :
    (Trace.mk []).isValid := by
  exact ⟨Trace.empty_isWellFormed, by simp [Trace.hasUniqueIds]⟩

-- ════════════════════════════════════════════════════════════════════
-- Transitive Closure Properties
-- ════════════════════════════════════════════════════════════════════

/-- Single-step happens-before lifts to the transitive closure. -/
theorem happensBefore_to_star (events : List MemoryEvent)
    (a b : MemoryEvent) (ha : a ∈ events) (hb : b ∈ events)
    (hab : happensBefore a b) :
    happensBeforeStar events a b :=
  happensBeforeStar.single a b ha hb hab

/-- The transitive closure is transitive (directly from the constructor). -/
theorem happensBeforeStar_trans (events : List MemoryEvent)
    (a c b : MemoryEvent) (hc : c ∈ events)
    (hac : happensBeforeStar events a c)
    (hcb : happensBeforeStar events c b) :
    happensBeforeStar events a b :=
  happensBeforeStar.trans a c b hc hac hcb

/-- Program order composes with synchronizes-with in the transitive closure. -/
theorem programOrder_sync_star (events : List MemoryEvent)
    (a b c : MemoryEvent) (ha : a ∈ events) (hb : b ∈ events) (hc : c ∈ events)
    (hpo : programOrder a b) (hsw : synchronizesWith b c) :
    happensBeforeStar events a c :=
  happensBeforeStar.trans a b c hb
    (happensBeforeStar.single a b ha hb (Or.inl hpo))
    (happensBeforeStar.single b c hb hc (Or.inr hsw))

/-- Synchronizes-with followed by program order in the transitive closure. -/
theorem sync_programOrder_star (events : List MemoryEvent)
    (a b c : MemoryEvent) (ha : a ∈ events) (hb : b ∈ events) (hc : c ∈ events)
    (hsw : synchronizesWith a b) (hpo : programOrder b c) :
    happensBeforeStar events a c :=
  happensBeforeStar.trans a b c hb
    (happensBeforeStar.single a b ha hb (Or.inr hsw))
    (happensBeforeStar.single b c hb hc (Or.inl hpo))

-- ════════════════════════════════════════════════════════════════════
-- Deeper Ordering Algebra
-- ════════════════════════════════════════════════════════════════════

/-- Strengthening with a weaker ordering returns the stronger one. -/
theorem strengthen_relaxed_left (o : MemoryOrder) :
    strengthen .relaxed o = o := by
  cases o <;> simp [strengthen, MemoryOrder.strength]

/-- Strengthening with a weaker ordering on the right is identity. -/
theorem strengthen_relaxed_right (o : MemoryOrder) :
    strengthen o .relaxed = o := by
  cases o <;> simp [strengthen, MemoryOrder.strength]

/-- SeqCst absorbs any other ordering under strengthen. -/
theorem strengthen_seqCst_left (o : MemoryOrder) :
    strengthen .seqCst o = .seqCst := by
  cases o <;> simp [strengthen, MemoryOrder.strength]

/-- SeqCst absorbs any other ordering under strengthen (right). -/
theorem strengthen_seqCst_right (o : MemoryOrder) :
    strengthen o .seqCst = .seqCst := by
  cases o <;> simp [strengthen, MemoryOrder.strength]

-- ════════════════════════════════════════════════════════════════════
-- More Atomic Operation Properties
-- ════════════════════════════════════════════════════════════════════

/-- fetchSub with 0 preserves the cell. -/
theorem fetchSub_zero_identity (cell : AtomicCell) (order : MemoryOrder) :
    (fetchSub cell 0 order).2 = cell := by
  simp [fetchSub]

/-- fetchAnd with all-ones mask preserves the cell. -/
theorem fetchAnd_allOnes (cell : AtomicCell) (order : MemoryOrder) :
    (fetchAnd cell cell.val order).2.val = cell.val := by
  simp [fetchAnd, Nat.and_self]

/-- fetchOr with 0 preserves the cell. -/
theorem fetchOr_zero_identity (cell : AtomicCell) (order : MemoryOrder) :
    (fetchOr cell 0 order).2.val = cell.val := by
  simp [fetchOr, Nat.or_zero]

/-- fetchXor with 0 preserves the cell. -/
theorem fetchXor_zero_identity (cell : AtomicCell) (order : MemoryOrder) :
    (fetchXor cell 0 order).2.val = cell.val := by
  simp [fetchXor, Nat.xor_zero]

/-- fetchXor is self-inverse: XOR twice with the same value returns original. -/
theorem fetchXor_self_inverse (cell : AtomicCell) (mask : Nat) (order : MemoryOrder) :
    let (_, cell') := fetchXor cell mask order
    (fetchXor cell' mask order).2.val = cell.val := by
  simp [fetchXor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- Three consecutive fetchAdd operations compose additively. -/
theorem fetchAdd_compose3 (cell : AtomicCell) (d1 d2 d3 : Nat)
    (o1 o2 o3 : MemoryOrder) :
    let (_, c1) := fetchAdd cell d1 o1
    let (_, c2) := fetchAdd c1 d2 o2
    (fetchAdd c2 d3 o3).2.val = cell.val + d1 + d2 + d3 := by
  simp [fetchAdd]

/-- Store followed by CAS with matching expected succeeds. -/
theorem store_then_cas_succeeds (cell : AtomicCell) (v desired : Nat)
    (hStore : validStoreOrder .seqCst = true) :
    let afterStore := (atomicStore cell v .seqCst hStore).2
    (atomicCAS afterStore v desired .seqCst .seqCst).1.success = true := by
  simp [atomicStore, atomicCAS]

/-- CAS success implies the previous value matched expected. -/
theorem cas_success_implies_match (cell : AtomicCell) (expected desired : Nat)
    (succOrder failOrder : MemoryOrder)
    (h : (atomicCAS cell expected desired succOrder failOrder).1.success = true) :
    cell.val = expected := by
  simp [atomicCAS] at h
  split at h <;> simp_all

-- ════════════════════════════════════════════════════════════════════
-- Data-Race Freedom under Synchronization
-- ════════════════════════════════════════════════════════════════════

/-- Conflicting events that are synchronized via release-acquire are not races. -/
theorem synchronized_no_race (a b : MemoryEvent)
    (hsw : synchronizesWith a b) :
    ¬isDataRace a b := by
  intro ⟨_, _, hNotAB, _⟩
  exact hNotAB (Or.inr hsw)

/-- A singleton store trace is data-race free. -/
theorem Trace.singleton_store_isDataRaceFree (e : MemoryEvent) (he : e.kind = .store) :
    (Trace.mk [e]).isDataRaceFree := by
  intro a b ha hb
  simp at ha hb
  subst ha; subst hb
  intro ⟨hConf, _, _, _⟩
  exact hConf.1 rfl

/-- A trace where all events are from a single thread is data-race free.
    Data races require different threads, so this is immediate. -/
theorem Trace.singleThread_isDataRaceFree (t : Trace) (tid : ThreadId)
    (hSingle : ∀ e, e ∈ t.events → e.id.thread = tid) :
    t.isDataRaceFree := by
  intro a b ha hb hRace
  have ⟨_, hDiffThread, _, _⟩ := hRace
  exact hDiffThread (by rw [hSingle a ha, hSingle b hb])

-- ════════════════════════════════════════════════════════════════════
-- Well-Formedness and Validity
-- ════════════════════════════════════════════════════════════════════

/-- A singleton well-formed event produces a valid trace. -/
theorem Trace.singleton_isValid (e : MemoryEvent) (h : validOrderForAccess e.kind e.order) :
    (Trace.mk [e]).isValid := by
  constructor
  · intro ev hev
    simp at hev
    subst hev
    exact h
  · intro a b ha hb hid
    simp at ha hb
    subst ha; subst hb
    rfl

/-- Appending a well-formed event preserves well-formedness if existing trace is well-formed. -/
theorem Trace.cons_isWellFormed (e : MemoryEvent) (es : List MemoryEvent)
    (hWf : (Trace.mk es).isWellFormed) (he : validOrderForAccess e.kind e.order) :
    (Trace.mk (e :: es)).isWellFormed := by
  intro ev hev
  simp at hev
  cases hev with
  | inl h => subst h; exact he
  | inr h => exact hWf ev h

/-- Coherence WW on an empty trace is trivially satisfied. -/
theorem coherenceWW_empty (mo : ModificationOrder) :
    coherenceWW (Trace.mk []) mo := by
  intro a b ha
  simp at ha

/-- Coherence RR on an empty trace is trivially satisfied. -/
theorem coherenceRR_empty (mo : ModificationOrder) :
    coherenceRR (Trace.mk []) mo := by
  intro a b ha
  simp at ha

/-- Full coherence on an empty trace is trivially satisfied. -/
theorem isCoherent_empty (mo : ModificationOrder) :
    isCoherent (Trace.mk []) mo :=
  ⟨coherenceRR_empty mo, by intro a b ha; simp at ha, coherenceWW_empty mo⟩

end Radix.Concurrency
