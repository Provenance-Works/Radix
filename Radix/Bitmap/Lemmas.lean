/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Bitmap.Spec
import Radix.Bitmap.Ops

/-!
# Bitmap/Bitset Lemmas (Layer 3)

Correctness proofs for the concrete `Bitmap` implementation.

- Structural invariant preservation (numBits, word count)
- Boolean algebra structural properties for set operations
- Spec-level proofs for abstract bitmap (set/clear round-trip, popcount)

The abstract specification (`Bitmap.Spec.BitmapState`) has full set/clear
round-trip proofs and popcount proofs. The concrete implementation
(`Bitmap.Ops.Bitmap`) inherits structural properties proven here.

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- Bridges Layer 2 (`Bitmap.Ops`) to Layer 3 (`Bitmap.Spec`).

## References

- v0.2.0 Roadmap: Bitmap / Bitset — set/clear round-trip, population count proofs
-/

namespace Radix.Bitmap.Lemmas

open Radix.Bitmap

/-! ## Construction Properties -/

/-- Freshly created bitmap has the correct number of bits. -/
theorem zeros_numBits (n : Nat) :
    (Bitmap.zeros n).numBits = n := by
  rfl

/-- Freshly created `ones` bitmap has the correct number of bits. -/
theorem ones_numBits (n : Nat) :
    (Bitmap.ones n).numBits = n := by
  rfl

/-- Zeros bitmap has correct word count. -/
theorem zeros_word_count (n : Nat) :
    (Bitmap.zeros n).words.size = wordsNeeded n := by
  exact (Bitmap.zeros n).hSize

/-- Ones bitmap has correct word count. -/
theorem ones_word_count (n : Nat) :
    (Bitmap.ones n).words.size = wordsNeeded n := by
  exact (Bitmap.ones n).hSize

/-! ## Structural Invariant Preservation -/

/-- Set preserves numBits. -/
theorem set_numBits (bm : Bitmap) (idx : Nat) :
    (bm.set idx).numBits = bm.numBits := by
  simp [Bitmap.set]
  split <;> rfl

/-- Clear preserves numBits. -/
theorem clear_numBits (bm : Bitmap) (idx : Nat) :
    (bm.clear idx).numBits = bm.numBits := by
  simp [Bitmap.clear]
  split <;> rfl

/-- Toggle preserves numBits. -/
theorem toggle_numBits (bm : Bitmap) (idx : Nat) :
    (bm.toggle idx).numBits = bm.numBits := by
  simp [Bitmap.toggle]
  split <;> rfl

/-- Set preserves word count. -/
theorem set_word_count (bm : Bitmap) (idx : Nat) :
    (bm.set idx).words.size = wordsNeeded bm.numBits := by
  simp [Bitmap.set]
  split
  · simp [Array.size_set, bm.hSize]
  · exact bm.hSize

/-- Clear preserves word count. -/
theorem clear_word_count (bm : Bitmap) (idx : Nat) :
    (bm.clear idx).words.size = wordsNeeded bm.numBits := by
  simp [Bitmap.clear]
  split
  · simp [Array.size_set, bm.hSize]
  · exact bm.hSize

/-- Toggle preserves word count. -/
theorem toggle_word_count (bm : Bitmap) (idx : Nat) :
    (bm.toggle idx).words.size = wordsNeeded bm.numBits := by
  simp [Bitmap.toggle]
  split
  · simp [Array.size_set, bm.hSize]
  · exact bm.hSize

/-- Out-of-bounds test always returns false. -/
theorem test_out_of_bounds (bm : Bitmap) (idx : Nat) (h : ¬(idx < bm.numBits)) :
    bm.test idx = false := by
  simp [Bitmap.test, h]

/-- Out-of-bounds set is identity. -/
theorem set_out_of_bounds (bm : Bitmap) (idx : Nat) (h : ¬(idx < bm.numBits)) :
    bm.set idx = bm := by
  simp [Bitmap.set, h]

/-- Out-of-bounds clear is identity. -/
theorem clear_out_of_bounds (bm : Bitmap) (idx : Nat) (h : ¬(idx < bm.numBits)) :
    bm.clear idx = bm := by
  simp [Bitmap.clear, h]

/-- Out-of-bounds toggle is identity. -/
theorem toggle_out_of_bounds (bm : Bitmap) (idx : Nat) (h : ¬(idx < bm.numBits)) :
    bm.toggle idx = bm := by
  simp [Bitmap.toggle, h]

/-! ## Boolean Algebra Structural Properties -/

/-- Complement preserves numBits. -/
theorem complement_numBits (bm : Bitmap) :
    bm.complement.numBits = bm.numBits := by
  simp [Bitmap.complement]
  split <;> rfl

/-- Union preserves numBits (left operand). -/
theorem union_numBits (a b : Bitmap) (h : a.numBits = b.numBits) :
    (Bitmap.union a b h).numBits = a.numBits := by
  rfl

/-- Intersection preserves numBits (left operand). -/
theorem intersection_numBits (a b : Bitmap) (h : a.numBits = b.numBits) :
    (Bitmap.intersection a b h).numBits = a.numBits := by
  rfl

/-- Difference preserves numBits (left operand). -/
theorem difference_numBits (a b : Bitmap) (h : a.numBits = b.numBits) :
    (Bitmap.difference a b h).numBits = a.numBits := by
  rfl

/-! ## Spec-Level Round-Trip Properties

The abstract specification has complete set/clear round-trip proofs.
These are proven purely at the mathematical level (function manipulation). -/

/-- (Spec) Set then test at the same index returns true. -/
theorem spec_set_test_eq (bm : Spec.BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.set idx).test idx = true :=
  Spec.set_test_eq bm idx h

/-- (Spec) Clear then test at the same index returns false. -/
theorem spec_clear_test_eq (bm : Spec.BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.clear idx).test idx = false :=
  Spec.clear_test_eq bm idx h

/-- (Spec) Set at index i does not affect test at different index j. -/
theorem spec_set_test_ne (bm : Spec.BitmapState) (i j : Nat)
    (hi : i < bm.size) (hne : i ≠ j) :
    (bm.set i).test j = bm.test j :=
  Spec.set_test_ne bm i j hi hne

/-- (Spec) Clear at index i does not affect test at different index j. -/
theorem spec_clear_test_ne (bm : Spec.BitmapState) (i j : Nat)
    (hi : i < bm.size) (hne : i ≠ j) :
    (bm.clear i).test j = bm.test j :=
  Spec.clear_test_ne bm i j hi hne

/-- (Spec) Toggle is self-inverse. -/
theorem spec_toggle_toggle (bm : Spec.BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.toggle idx).toggle idx = bm :=
  Spec.toggle_toggle bm idx h

/-- (Spec) Zeros always test as false. -/
theorem spec_zeros_test (n idx : Nat) :
    (Spec.BitmapState.zeros n).test idx = false :=
  Spec.zeros_test n idx

/-- (Spec) Zeros have popcount 0. -/
theorem spec_zeros_popcount (n : Nat) :
    (Spec.BitmapState.zeros n).popcount = 0 :=
  Spec.zeros_popcount n

end Radix.Bitmap.Lemmas
