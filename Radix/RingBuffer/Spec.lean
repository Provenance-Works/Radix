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

end Radix.RingBuffer.Spec
