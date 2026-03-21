/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Bitmap/Bitset Specification (Layer 3)

Formal specification of a dense bit-array (bitmap/bitset) with:
- O(1) set/clear/test operations
- Bulk operations (find-first-set, population count)
- Mathematical properties (set/clear round-trip, popcount bounds)

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.

## References

- v0.2.0 Roadmap: Bitmap / Bitset
- FR-002: Bitwise Operations
-/

namespace Radix.Bitmap.Spec

/-! ## Abstract State -/

/-- Abstract bitmap specification as a function from index to Bool.
    The `size` field determines the valid index range `[0, size)`. -/
structure BitmapState where
  /-- Total number of bits. -/
  size : Nat
  /-- Function from bit index to value. Only valid for `i < size`. -/
  getBit : Nat → Bool
  deriving Inhabited

namespace BitmapState

/-- Create an all-zeros bitmap. -/
def zeros (n : Nat) : BitmapState :=
  { size := n, getBit := fun _ => false }

/-- Create an all-ones bitmap. -/
def ones (n : Nat) : BitmapState :=
  { size := n, getBit := fun i => i < n }

/-- Test a bit at position `idx`. Returns `false` for out-of-range. -/
def test (bm : BitmapState) (idx : Nat) : Bool :=
  if idx < bm.size then bm.getBit idx else false

/-- Set a bit at position `idx`. No-op for out-of-range. -/
def set (bm : BitmapState) (idx : Nat) : BitmapState :=
  if idx < bm.size then
    { bm with getBit := fun i => if i == idx then true else bm.getBit i }
  else bm

/-- Clear a bit at position `idx`. No-op for out-of-range. -/
def clear (bm : BitmapState) (idx : Nat) : BitmapState :=
  if idx < bm.size then
    { bm with getBit := fun i => if i == idx then false else bm.getBit i }
  else bm

/-- Toggle a bit at position `idx`. No-op for out-of-range. -/
def toggle (bm : BitmapState) (idx : Nat) : BitmapState :=
  if idx < bm.size then
    { bm with getBit := fun i => if i == idx then !bm.getBit i else bm.getBit i }
  else bm

/-- Population count: number of set bits. -/
def popcount (bm : BitmapState) : Nat :=
  go bm.size 0
where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | n + 1, acc =>
      let acc' := if bm.getBit (bm.size - 1 - n) then acc + 1 else acc
      go n acc'

/-- Find the first set bit (lowest index). Returns `none` if all clear. -/
def findFirstSet (bm : BitmapState) : Option Nat :=
  go bm.size 0
where
  go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, idx =>
      if idx >= bm.size then none
      else if bm.getBit idx then some idx
      else go fuel (idx + 1)

/-- Find the first clear bit (lowest index). Returns `none` if all set. -/
def findFirstClear (bm : BitmapState) : Option Nat :=
  go bm.size 0
where
  go : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, idx =>
      if idx >= bm.size then none
      else if !bm.getBit idx then some idx
      else go fuel (idx + 1)

end BitmapState

/-! ## Specification Properties -/

/-- Set then test at the same index returns `true`. -/
theorem set_test_eq (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.set idx).test idx = true := by
  simp [BitmapState.set, BitmapState.test, h]

/-- Clear then test at the same index returns `false`. -/
theorem clear_test_eq (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.clear idx).test idx = false := by
  simp [BitmapState.clear, BitmapState.test, h]

/-- Set at index `i` does not affect test at index `j ≠ i`. -/
theorem set_test_ne (bm : BitmapState) (i j : Nat) (hi : i < bm.size) (hne : i ≠ j) :
    (bm.set i).test j = bm.test j := by
  simp [BitmapState.set, BitmapState.test, hi]
  split
  · rename_i hj
    simp [hne, Nat.ne_of_gt (by omega : j > i) |>.symm]
    split
    · rename_i hjlt
      simp [show i ≠ j from hne]
    · rfl
  · rename_i hj
    simp at hj
    simp [show ¬(j < bm.size) from hj]

/-- Clear at index `i` does not affect test at index `j ≠ i`. -/
theorem clear_test_ne (bm : BitmapState) (i j : Nat) (hi : i < bm.size) (hne : i ≠ j) :
    (bm.clear i).test j = bm.test j := by
  simp [BitmapState.clear, BitmapState.test, hi]
  split
  · rename_i hj
    simp [show i ≠ j from hne]
  · rfl

/-- Toggle is self-inverse. -/
theorem toggle_toggle (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.toggle idx).toggle idx = bm := by
  simp [BitmapState.toggle, h]
  ext i
  · rfl
  · simp
    split
    · rename_i heq; subst heq; simp
    · rfl

/-- Zeros bitmap has popcount 0. -/
theorem zeros_popcount (n : Nat) :
    (BitmapState.zeros n).popcount = 0 := by
  simp [BitmapState.zeros, BitmapState.popcount]
  suffices ∀ m acc, BitmapState.popcount.go { size := n, getBit := fun _ => false } m acc = acc by
    exact this n 0
  intro m
  induction m with
  | zero => intro acc; rfl
  | succ k ih => intro acc; simp [BitmapState.popcount.go]; exact ih acc

/-- Test on zeros always returns false. -/
theorem zeros_test (n idx : Nat) :
    (BitmapState.zeros n).test idx = false := by
  simp [BitmapState.zeros, BitmapState.test]

/-- Empty bitmap (size 0) has popcount 0. -/
theorem empty_popcount :
    (BitmapState.zeros 0).popcount = 0 := zeros_popcount 0

end Radix.Bitmap.Spec
