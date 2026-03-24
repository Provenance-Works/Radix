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
  unfold BitmapState.test BitmapState.set
  simp [h, beq_iff_eq]

/-- Clear then test at the same index returns `false`. -/
theorem clear_test_eq (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.clear idx).test idx = false := by
  unfold BitmapState.test BitmapState.clear
  simp [h, beq_iff_eq]

/-- Set at index `i` does not affect test at index `j ≠ i`. -/
theorem set_test_ne (bm : BitmapState) (i j : Nat) (hi : i < bm.size) (hne : i ≠ j) :
    (bm.set i).test j = bm.test j := by
  unfold BitmapState.test BitmapState.set
  simp [hi]
  congr 1
  simp [show j ≠ i from Ne.symm hne]

/-- Clear at index `i` does not affect test at index `j ≠ i`. -/
theorem clear_test_ne (bm : BitmapState) (i j : Nat) (hi : i < bm.size) (hne : i ≠ j) :
    (bm.clear i).test j = bm.test j := by
  unfold BitmapState.test BitmapState.clear
  simp [hi]
  congr 1
  simp [show j ≠ i from Ne.symm hne]

/-- Toggle is self-inverse. -/
theorem toggle_toggle (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.toggle idx).toggle idx = bm := by
  unfold BitmapState.toggle
  simp [h]
  cases bm with
  | mk sz getBit =>
    congr 1
    funext i
    simp
    split
    · simp [Bool.not_not]
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

-- ════════════════════════════════════════════════════════════════════
-- Size Preservation
-- ════════════════════════════════════════════════════════════════════

/-- Set preserves the bitmap size. -/
theorem set_size (bm : BitmapState) (idx : Nat) :
    (bm.set idx).size = bm.size := by
  unfold BitmapState.set
  split <;> rfl

/-- Clear preserves the bitmap size. -/
theorem clear_size (bm : BitmapState) (idx : Nat) :
    (bm.clear idx).size = bm.size := by
  unfold BitmapState.clear
  split <;> rfl

/-- Toggle preserves the bitmap size. -/
theorem toggle_size (bm : BitmapState) (idx : Nat) :
    (bm.toggle idx).size = bm.size := by
  unfold BitmapState.toggle
  split <;> rfl

-- ════════════════════════════════════════════════════════════════════
-- Idempotence and Absorption
-- ════════════════════════════════════════════════════════════════════

/-- Set is idempotent. -/
theorem set_set_same (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.set idx).set idx = bm.set idx := by
  unfold BitmapState.set; simp [h]

/-- Clear is idempotent. -/
theorem clear_clear_same (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.clear idx).clear idx = bm.clear idx := by
  unfold BitmapState.clear; simp [h]

/-- Set then clear at the same index equals clear. -/
theorem set_clear_same (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.set idx).clear idx = bm.clear idx := by
  unfold BitmapState.set BitmapState.clear
  simp [h]
  congr 1; funext i
  by_cases hi : i = idx <;> simp_all

/-- Clear then set at the same index equals set. -/
theorem clear_set_same (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.clear idx).set idx = bm.set idx := by
  unfold BitmapState.clear BitmapState.set
  simp [h]
  congr 1; funext i
  by_cases hi : i = idx <;> simp_all

-- ════════════════════════════════════════════════════════════════════
-- Toggle Properties
-- ════════════════════════════════════════════════════════════════════

/-- Toggle at index `i` does not affect test at index `j ≠ i`. -/
theorem toggle_test_ne (bm : BitmapState) (i j : Nat) (hi : i < bm.size) (hne : i ≠ j) :
    (bm.toggle i).test j = bm.test j := by
  unfold BitmapState.test BitmapState.toggle
  simp [hi]
  congr 1
  simp [show j ≠ i from Ne.symm hne]

/-- Toggle flips the bit value. -/
theorem toggle_test_eq (bm : BitmapState) (idx : Nat) (h : idx < bm.size) :
    (bm.toggle idx).test idx = !(bm.test idx) := by
  unfold BitmapState.test BitmapState.toggle
  simp [h, beq_iff_eq]

-- ════════════════════════════════════════════════════════════════════
-- Ones Bitmap Properties
-- ════════════════════════════════════════════════════════════════════

/-- Test on ones returns true for valid indices. -/
theorem ones_test (n idx : Nat) (h : idx < n) :
    (BitmapState.ones n).test idx = true := by
  simp [BitmapState.ones, BitmapState.test, h]

/-- Test on ones returns false for out-of-range indices. -/
theorem ones_test_out (n idx : Nat) (h : ¬idx < n) :
    (BitmapState.ones n).test idx = false := by
  simp [BitmapState.ones, BitmapState.test, h]

/-- Ones bitmap has popcount equal to its size. -/
theorem ones_popcount (n : Nat) :
    (BitmapState.ones n).popcount = n := by
  simp [BitmapState.ones, BitmapState.popcount]
  suffices ∀ m acc, m ≤ n →
      BitmapState.popcount.go { size := n, getBit := fun i => decide (i < n) } m acc = acc + m by
    have := this n 0 (Nat.le_refl n)
    simpa using this
  intro m
  induction m with
  | zero => intro acc _; rfl
  | succ k ih =>
    intro acc hle
    simp [BitmapState.popcount.go]
    have : n - 1 - k < n := by omega
    simp [this]
    rw [ih (acc + 1) (by omega)]
    omega

/-- Out-of-range test always returns false. -/
theorem test_out_of_range (bm : BitmapState) (idx : Nat) (h : ¬idx < bm.size) :
    bm.test idx = false := by
  simp [BitmapState.test, h]

/-- Set on out-of-range index is a no-op. -/
theorem set_out_of_range (bm : BitmapState) (idx : Nat) (h : ¬idx < bm.size) :
    bm.set idx = bm := by
  simp [BitmapState.set, h]

/-- Clear on out-of-range index is a no-op. -/
theorem clear_out_of_range (bm : BitmapState) (idx : Nat) (h : ¬idx < bm.size) :
    bm.clear idx = bm := by
  simp [BitmapState.clear, h]

/-- Toggle on out-of-range index is a no-op. -/
theorem toggle_out_of_range (bm : BitmapState) (idx : Nat) (h : ¬idx < bm.size) :
    bm.toggle idx = bm := by
  simp [BitmapState.toggle, h]

-- ════════════════════════════════════════════════════════════════════
-- Commutativity of Operations at Different Indices
-- ════════════════════════════════════════════════════════════════════

/-- Set at different indices commutes. -/
theorem set_set_comm (bm : BitmapState) (i j : Nat) (hi : i < bm.size) (hj : j < bm.size)
    (hne : i ≠ j) :
    (bm.set i).set j = (bm.set j).set i := by
  unfold BitmapState.set
  simp [hi, hj]
  congr 1; funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

/-- Clear at different indices commutes. -/
theorem clear_clear_comm (bm : BitmapState) (i j : Nat) (hi : i < bm.size) (hj : j < bm.size)
    (hne : i ≠ j) :
    (bm.clear i).clear j = (bm.clear j).clear i := by
  unfold BitmapState.clear
  simp [hi, hj]
  congr 1; funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

/-- Set and clear at different indices commute. -/
theorem set_clear_comm (bm : BitmapState) (i j : Nat) (hi : i < bm.size) (hj : j < bm.size)
    (hne : i ≠ j) :
    (bm.set i).clear j = (bm.clear j).set i := by
  unfold BitmapState.set BitmapState.clear
  simp [hi, hj]
  congr 1; funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

/-- Toggle at different indices commutes. -/
theorem toggle_toggle_comm (bm : BitmapState) (i j : Nat) (hi : i < bm.size) (hj : j < bm.size)
    (hne : i ≠ j) :
    (bm.toggle i).toggle j = (bm.toggle j).toggle i := by
  unfold BitmapState.toggle
  simp [hi, hj]
  congr 1; funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all

-- ════════════════════════════════════════════════════════════════════
-- FindFirstSet Properties
-- ════════════════════════════════════════════════════════════════════

/-- FindFirstSet on zeros returns none. -/
theorem zeros_findFirstSet (n : Nat) :
    (BitmapState.zeros n).findFirstSet = none := by
  simp [BitmapState.zeros, BitmapState.findFirstSet]
  suffices ∀ m idx, BitmapState.findFirstSet.go { size := n, getBit := fun _ => false } m idx = none by
    exact this n 0
  intro m
  induction m with
  | zero => intro _; rfl
  | succ k ih => intro idx; simp [BitmapState.findFirstSet.go]; intro _; exact ih _

/-- FindFirstClear on zeros returns `some 0` when n > 0. -/
theorem zeros_findFirstClear (n : Nat) (hn : 0 < n) :
    (BitmapState.zeros n).findFirstClear = some 0 := by
  simp [BitmapState.zeros, BitmapState.findFirstClear]
  cases n with
  | zero => omega
  | succ k => simp [BitmapState.findFirstClear.go]

/-- Zeros bitmap has size n. -/
theorem zeros_size (n : Nat) : (BitmapState.zeros n).size = n := rfl

/-- Ones bitmap has size n. -/
theorem ones_size (n : Nat) : (BitmapState.ones n).size = n := rfl

-- ════════════════════════════════════════════════════════════════════
-- Popcount Bounds
-- ════════════════════════════════════════════════════════════════════

/-- Popcount never exceeds the bitmap size. -/
theorem popcount_le_size (bm : BitmapState) :
    bm.popcount ≤ bm.size := by
  simp [BitmapState.popcount]
  suffices ∀ m acc, m ≤ bm.size → acc ≤ bm.size - m →
      BitmapState.popcount.go bm m acc ≤ bm.size by
    exact this bm.size 0 (Nat.le_refl _) (by omega)
  intro m
  induction m with
  | zero => intro acc _ h; simpa [BitmapState.popcount.go] using h
  | succ k ih =>
    intro acc hle hacc
    simp [BitmapState.popcount.go]
    split
    · exact ih (acc + 1) (by omega) (by omega)
    · exact ih acc (by omega) (by omega)

/-- FindFirstSet returns a valid index (within bounds). -/
theorem findFirstSet_lt_size (bm : BitmapState) (idx : Nat)
    (h : bm.findFirstSet = some idx) :
    idx < bm.size := by
  simp [BitmapState.findFirstSet] at h
  exact go_bound _ _ h
where
  go_bound : ∀ m start,
      BitmapState.findFirstSet.go bm m start = some idx → idx < bm.size := by
    intro m
    induction m with
    | zero => intro _ h; simp [BitmapState.findFirstSet.go] at h
    | succ k ih =>
      intro start h
      unfold BitmapState.findFirstSet.go at h
      split at h
      · simp at h
      · split at h
        · injection h with h; omega
        · exact ih _ h

/-- FindFirstClear returns a valid index (within bounds). -/
theorem findFirstClear_lt_size (bm : BitmapState) (idx : Nat)
    (h : bm.findFirstClear = some idx) :
    idx < bm.size := by
  simp [BitmapState.findFirstClear] at h
  exact go_bound _ _ h
where
  go_bound : ∀ m start,
      BitmapState.findFirstClear.go bm m start = some idx → idx < bm.size := by
    intro m
    induction m with
    | zero => intro _ h; simp [BitmapState.findFirstClear.go] at h
    | succ k ih =>
      intro start h
      unfold BitmapState.findFirstClear.go at h
      split at h
      · simp at h
      · split at h
        · injection h with h; omega
        · exact ih _ h

-- ════════════════════════════════════════════════════════════════════
-- Concrete Spec Test Vectors
-- ════════════════════════════════════════════════════════════════════

/-- 8-bit zeros: set bit 3, test bit 3 = true. -/
example : ((BitmapState.zeros 8).set 3).test 3 = true := by native_decide

/-- 8-bit zeros: set bit 3, test bit 4 = false. -/
example : ((BitmapState.zeros 8).set 3).test 4 = false := by native_decide

/-- 8-bit zeros: set bit 3, clear bit 3, test bit 3 = false. -/
example : (((BitmapState.zeros 8).set 3).clear 3).test 3 = false := by native_decide

/-- Toggle twice: testing the toggled bit returns original value. -/
example : (((BitmapState.zeros 8).toggle 5).toggle 5).test 5 = false := by native_decide

/-- Ones(4) has popcount 4. -/
example : (BitmapState.ones 4).popcount = 4 := by native_decide

/-- FindFirstSet on zeros(8) with bit 5 set returns 5. -/
example : ((BitmapState.zeros 8).set 5).findFirstSet = some 5 := by native_decide

/-- FindFirstSet on zeros(8) with bits 3 and 5 set returns 3 (lowest). -/
example : (((BitmapState.zeros 8).set 5).set 3).findFirstSet = some 3 := by native_decide

/-- FindFirstClear on ones(4) with bit 2 cleared returns 2. -/
example : ((BitmapState.ones 4).clear 2).findFirstClear = some 2 := by native_decide

end Radix.Bitmap.Spec
