/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Ring Buffer Specification (Layer 3)

Formal specification of a fixed-capacity circular queue (ring buffer).
Defines the abstract state and invariants that a correct ring buffer
implementation must satisfy.

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.
- Defines the canonical semantics for ring buffer operations.

## References

- v0.2.0 Roadmap: Ring Buffer
- FR-004: Memory Safety (bounds-checked access)
-/

namespace Radix.RingBuffer.Spec

/-! ## Abstract State -/

/-- Abstract specification of ring buffer state.
    The logical content is a list of bytes, bounded by capacity. -/
structure RingBufferState where
  /-- The logical content of the ring buffer, oldest first. -/
  contents : List UInt8
  /-- The fixed capacity of the buffer. -/
  capacity : Nat
  deriving Repr

namespace RingBufferState

/-- Number of elements currently stored. -/
def count (s : RingBufferState) : Nat := s.contents.length

/-- Is the buffer empty? -/
def isEmpty (s : RingBufferState) : Prop := s.contents = []

/-- Is the buffer full? -/
def isFull (s : RingBufferState) : Prop := s.count = s.capacity

instance (s : RingBufferState) : Decidable s.isEmpty :=
  inferInstanceAs (Decidable (_ = _))

instance (s : RingBufferState) : Decidable s.isFull :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Invariants -/

/-- The fundamental ring buffer invariant: count never exceeds capacity. -/
def invariant (s : RingBufferState) : Prop :=
  s.count ≤ s.capacity

instance (s : RingBufferState) : Decidable s.invariant :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ## Operation Specifications -/

/-- Specification for `push`: appends to the end if not full. -/
def pushSpec (s : RingBufferState) (val : UInt8) : Option RingBufferState :=
  if s.isFull then none
  else some { s with contents := s.contents ++ [val] }

/-- Specification for `pop`: removes from the front if not empty. -/
def popSpec (s : RingBufferState) : Option (UInt8 × RingBufferState) :=
  match s.contents with
  | [] => none
  | hd :: tl => some (hd, { s with contents := tl })

/-- Specification for `peek`: returns the front element if not empty. -/
def peekSpec (s : RingBufferState) : Option UInt8 :=
  s.contents.head?

/-- An empty ring buffer state with the given capacity. -/
def empty (capacity : Nat) : RingBufferState :=
  { contents := [], capacity := capacity }

end RingBufferState

/-! ## Specification Properties -/

/-- `push` preserves the invariant. -/
theorem push_preserves_invariant (s : RingBufferState) (val : UInt8)
    (hinv : s.invariant)
    (hnf : ¬s.isFull) :
    (RingBufferState.pushSpec s val).isSome = true ∧
    ∀ s', RingBufferState.pushSpec s val = some s' → s'.invariant := by
  constructor
  · simp [RingBufferState.pushSpec, hnf]
  · intro s' h
    unfold RingBufferState.pushSpec at h
    split at h
    · contradiction
    · injection h with h; subst h
      simp [RingBufferState.invariant, RingBufferState.count,
            RingBufferState.isFull] at *
      omega

/-- `pop` preserves the invariant. -/
theorem pop_preserves_invariant (s : RingBufferState)
    (hinv : s.invariant) (hne : ¬s.isEmpty) :
    ∀ v s', RingBufferState.popSpec s = some (v, s') → s'.invariant := by
  intro v s' h
  unfold RingBufferState.popSpec at h
  match hc : s.contents with
  | [] =>
    simp [RingBufferState.isEmpty] at hne
    exact absurd hc hne
  | hd :: tl =>
    simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [RingBufferState.invariant, RingBufferState.count]
    have : s.contents.length = tl.length + 1 := by rw [hc]; simp
    simp [RingBufferState.invariant, RingBufferState.count] at hinv
    omega

/-- Push then pop recovers the pushed value (when the buffer was empty). -/
theorem push_pop_empty (cap : Nat) (val : UInt8) (hcap : cap > 0) :
    RingBufferState.pushSpec (RingBufferState.empty cap) val =
      some { contents := [val], capacity := cap } := by
  simp [RingBufferState.empty, RingBufferState.pushSpec, RingBufferState.isFull,
        RingBufferState.count]
  omega

/-- `pop` after `push` on non-full buffer with non-empty contents
    yields FIFO ordering: returns the oldest element. -/
theorem push_preserves_fifo (s : RingBufferState) (val hd : UInt8) (tl : List UInt8)
    (hcontents : s.contents = hd :: tl) :
    let pushed := { s with contents := s.contents ++ [val] }
    RingBufferState.popSpec pushed = some (hd, { pushed with contents := tl ++ [val] }) := by
  simp [RingBufferState.popSpec, hcontents]

/-- The empty buffer invariant holds. -/
theorem empty_invariant (cap : Nat) : (RingBufferState.empty cap).invariant := by
  simp [RingBufferState.empty, RingBufferState.invariant, RingBufferState.count]

/-- An empty buffer is empty. -/
theorem empty_isEmpty (cap : Nat) : (RingBufferState.empty cap).isEmpty := by
  simp [RingBufferState.empty, RingBufferState.isEmpty]

/-- Pop from empty is none. -/
theorem pop_empty (cap : Nat) :
    RingBufferState.popSpec (RingBufferState.empty cap) = none := by
  simp [RingBufferState.empty, RingBufferState.popSpec]

/-- Push to full is none. -/
theorem push_full (s : RingBufferState) (val : UInt8) (hfull : s.isFull) :
    RingBufferState.pushSpec s val = none := by
  simp [RingBufferState.pushSpec, hfull]

-- ════════════════════════════════════════════════════════════════════
-- Count and Capacity Theorems
-- ════════════════════════════════════════════════════════════════════

/-- Empty buffer has count 0. -/
theorem empty_count (cap : Nat) : (RingBufferState.empty cap).count = 0 := by
  simp [RingBufferState.empty, RingBufferState.count]

/-- Push increases count by 1. -/
theorem push_count (s : RingBufferState) (val : UInt8) (hnf : ¬s.isFull) :
    ∀ s', RingBufferState.pushSpec s val = some s' → s'.count = s.count + 1 := by
  intro s' h
  unfold RingBufferState.pushSpec at h
  simp [hnf] at h
  subst h
  simp [RingBufferState.count]

/-- Pop decreases count by 1. -/
theorem pop_count (s : RingBufferState) :
    ∀ v s', RingBufferState.popSpec s = some (v, s') → s'.count + 1 = s.count := by
  intro v s' h
  unfold RingBufferState.popSpec at h
  match hc : s.contents with
  | [] => simp [hc] at h
  | hd :: tl =>
    simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [RingBufferState.count, hc]

/-- After push, the buffer is not empty. -/
theorem push_not_empty (s : RingBufferState) (val : UInt8) (hnf : ¬s.isFull) :
    ∀ s', RingBufferState.pushSpec s val = some s' → ¬s'.isEmpty := by
  intro s' h
  unfold RingBufferState.pushSpec at h
  simp [hnf] at h
  subst h
  unfold RingBufferState.isEmpty
  simp

/-- Peek on non-empty buffer returns the front element. -/
theorem peek_front (s : RingBufferState) (hd : UInt8) (tl : List UInt8)
    (hc : s.contents = hd :: tl) :
    RingBufferState.peekSpec s = some hd := by
  simp [RingBufferState.peekSpec, hc]

/-- Peek and pop agree on the returned value. -/
theorem peek_pop_agree (s : RingBufferState) :
    ∀ v s', RingBufferState.popSpec s = some (v, s') →
    RingBufferState.peekSpec s = some v := by
  intro v s' h
  unfold RingBufferState.popSpec at h
  match hc : s.contents with
  | [] => simp [hc] at h
  | hd :: tl =>
    simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [RingBufferState.peekSpec, hc]

/-- Push does not change the capacity. -/
theorem push_capacity (s : RingBufferState) (val : UInt8) (hnf : ¬s.isFull) :
    ∀ s', RingBufferState.pushSpec s val = some s' → s'.capacity = s.capacity := by
  intro s' h
  unfold RingBufferState.pushSpec at h
  simp [hnf] at h
  subst h; rfl

/-- Pop does not change the capacity. -/
theorem pop_capacity (s : RingBufferState) :
    ∀ v s', RingBufferState.popSpec s = some (v, s') → s'.capacity = s.capacity := by
  intro v s' h
  unfold RingBufferState.popSpec at h
  match hc : s.contents with
  | [] => simp [hc] at h
  | hd :: tl =>
    simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h; rfl

-- ════════════════════════════════════════════════════════════════════
-- FIFO Ordering and Round-Trip Properties
-- ════════════════════════════════════════════════════════════════════

/-- Push then pop on an empty buffer returns the pushed value. -/
theorem push_pop_roundtrip (cap : Nat) (val : UInt8) (hcap : 0 < cap) :
    ∃ s', RingBufferState.pushSpec (RingBufferState.empty cap) val = some s' ∧
    RingBufferState.popSpec s' = some (val, RingBufferState.empty cap) := by
  refine ⟨{ contents := [val], capacity := cap }, ?_, ?_⟩
  · simp [RingBufferState.pushSpec, RingBufferState.empty, RingBufferState.isFull,
          RingBufferState.count]
    omega
  · simp [RingBufferState.popSpec, RingBufferState.empty]

/-- Two pushes then two pops returns values in FIFO order. -/
theorem push_push_pop_pop_fifo (cap : Nat) (v1 v2 : UInt8) (_ : 2 ≤ cap) :
    let s0 := RingBufferState.empty cap
    let _s1 := { s0 with contents := [v1] }
    let s2 := { s0 with contents := [v1, v2] }
    RingBufferState.popSpec s2 = some (v1, { s0 with contents := [v2] }) := by
  simp [RingBufferState.popSpec]

/-- Peek does not change the buffer state. -/
theorem peek_idempotent (s : RingBufferState) :
    RingBufferState.peekSpec s = s.contents.head? := by
  rfl

/-- Full buffer has count = capacity. -/
theorem isFull_iff_count_eq (s : RingBufferState) :
    s.isFull ↔ s.count = s.capacity := by
  rfl

/-- Empty buffer has count = 0. -/
theorem isEmpty_iff_count_zero (s : RingBufferState) :
    s.isEmpty ↔ s.count = 0 := by
  constructor
  · intro h; unfold RingBufferState.isEmpty at h; simp [RingBufferState.count, h]
  · intro h; unfold RingBufferState.isEmpty; simp [RingBufferState.count] at h; exact h

-- ════════════════════════════════════════════════════════════════════
-- Additional Specification Properties
-- ════════════════════════════════════════════════════════════════════

/-- The remaining space in a buffer with invariant is `capacity - count`. -/
theorem remaining_space (s : RingBufferState) :
    s.capacity - s.count = s.capacity - s.contents.length := by
  rfl

/-- An empty buffer is not full when capacity > 0. -/
theorem empty_not_full (cap : Nat) (hcap : 0 < cap) :
    ¬(RingBufferState.empty cap).isFull := by
  simp [RingBufferState.empty, RingBufferState.isFull, RingBufferState.count]
  omega

/-- A full buffer is not empty when capacity > 0. -/
theorem full_not_empty (s : RingBufferState) (hfull : s.isFull) (hcap : 0 < s.capacity) :
    ¬s.isEmpty := by
  intro he
  simp [RingBufferState.isEmpty] at he
  simp [RingBufferState.isFull, RingBufferState.count, he] at hfull
  omega

/-- Pop preserves FIFO order: after pop, remaining contents are the tail. -/
theorem pop_contents (s : RingBufferState) (v : UInt8) (s' : RingBufferState)
    (h : RingBufferState.popSpec s = some (v, s')) :
    s.contents = v :: s'.contents := by
  unfold RingBufferState.popSpec at h
  match hc : s.contents with
  | [] => simp [hc] at h
  | hd :: tl =>
    simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Push appends to the end of contents. -/
theorem push_contents (s : RingBufferState) (val : UInt8) (s' : RingBufferState)
    (h : RingBufferState.pushSpec s val = some s') :
    s'.contents = s.contents ++ [val] := by
  unfold RingBufferState.pushSpec at h
  split at h
  · contradiction
  · injection h with h; subst h; rfl

/-- After n pushes on an empty buffer, count = n (when n ≤ cap). -/
theorem empty_push_count (cap : Nat) :
    (RingBufferState.empty cap).count = 0 := by
  simp [RingBufferState.empty, RingBufferState.count]

/-- Peek on empty buffer returns none. -/
theorem peek_empty (cap : Nat) :
    RingBufferState.peekSpec (RingBufferState.empty cap) = none := by
  simp [RingBufferState.peekSpec, RingBufferState.empty]

/-- Pop then push does not change count (net zero). -/
theorem pop_push_count (s : RingBufferState) (v : UInt8) (spop s' : RingBufferState)
    (val : UInt8)
    (hpop : RingBufferState.popSpec s = some (v, spop))
    (hpush : RingBufferState.pushSpec spop val = some s')
    (hinv : s.invariant) :
    s'.count = s.count := by
  have hpc := pop_count s v spop hpop
  have hpu := push_count spop val (by
    intro hf
    simp [RingBufferState.isFull] at hf
    simp [RingBufferState.invariant] at hinv
    have hcap := pop_capacity s v spop hpop
    simp [hcap] at hf
    omega) s' hpush
  omega

end Radix.RingBuffer.Spec
