/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Alignment Specification (Layer 3)

Formal specification of alignment operations used throughout the Memory
and BareMetal subsystems.

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.
- Defines the canonical semantics for alignment operations.

## References

- v0.2.0 Roadmap: Alignment Utilities
- FR-004: Memory Safety
-/

namespace Radix.Alignment.Spec

/-! ## Core Definitions -/

/-- An address/offset is aligned to `align` when `align > 0` and
    `offset` is a multiple of `align`. -/
def isAligned (offset align : Nat) : Prop :=
  align > 0 ∧ offset % align = 0

instance (offset align : Nat) : Decidable (isAligned offset align) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Round `offset` up to the next multiple of `align`.
    Requires `align > 0`. Result is the smallest `m ≥ offset` such that
    `align ∣ m`. -/
def alignUp (offset align : Nat) : Nat :=
  if align == 0 then offset
  else ((offset + align - 1) / align) * align

/-- Round `offset` down to the previous multiple of `align`.
    Requires `align > 0`. Result is the largest `m ≤ offset` such that
    `align ∣ m`. -/
def alignDown (offset align : Nat) : Nat :=
  if align == 0 then offset
  else (offset / align) * align

/-- Check whether `align` is a power of two. Power-of-two alignment
    enables efficient bit-mask operations. -/
def isPowerOfTwo (n : Nat) : Prop := n > 0 ∧ n &&& (n - 1) = 0

instance (n : Nat) : Decidable (isPowerOfTwo n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The alignment padding needed to reach the next aligned offset. -/
def alignPadding (offset align : Nat) : Nat :=
  if align == 0 then 0
  else (align - offset % align) % align

-- ════════════════════════════════════════════════════════════════════
-- Basic Alignment Properties
-- ════════════════════════════════════════════════════════════════════

/-- Zero is aligned to any positive alignment. -/
theorem isAligned_zero (align : Nat) (hpos : 0 < align) : isAligned 0 align := by
  exact ⟨hpos, by simp⟩

/-- Any offset is aligned to 1. -/
theorem isAligned_one (offset : Nat) : isAligned offset 1 := by
  exact ⟨by omega, Nat.mod_one offset⟩

/-- All multiples of the alignment are aligned. -/
theorem isAligned_mul (k align : Nat) (hpos : 0 < align) :
    isAligned (k * align) align := by
  exact ⟨hpos, by rw [Nat.mul_comm]; exact Nat.mul_mod_right align k⟩

/-- isAligned unfolds to a conjunction of positivity and divisibility. -/
theorem isAligned_iff (offset align : Nat) :
    isAligned offset align ↔ align > 0 ∧ offset % align = 0 := by
  rfl

-- ════════════════════════════════════════════════════════════════════
-- AlignDown Properties
-- ════════════════════════════════════════════════════════════════════

/-- alignDown never exceeds the original offset. -/
theorem alignDown_le (offset align : Nat) : alignDown offset align ≤ offset := by
  unfold alignDown
  split
  · exact Nat.le_refl _
  · exact Nat.div_mul_le_self offset align

/-- alignDown of zero is zero. -/
theorem alignDown_zero (align : Nat) : alignDown 0 align = 0 := by
  unfold alignDown; split <;> simp

/-- alignDown with alignment 1 is identity. -/
theorem alignDown_one (offset : Nat) : alignDown offset 1 = offset := by
  simp [alignDown]

/-- alignDown is idempotent. -/
theorem alignDown_alignDown (offset align : Nat) (hpos : 0 < align) :
    alignDown (alignDown offset align) align = alignDown offset align := by
  have hne : align ≠ 0 := by omega
  simp only [alignDown, beq_iff_eq, hne, ↓reduceIte]
  rw [Nat.mul_div_cancel _ hpos]

-- ════════════════════════════════════════════════════════════════════
-- AlignUp Properties
-- ════════════════════════════════════════════════════════════════════

/-- alignUp is always ≥ the original offset. -/
theorem alignUp_ge (offset align : Nat) (hpos : 0 < align) :
    offset ≤ alignUp offset align := by
  unfold alignUp
  split
  · omega
  · -- Need: offset ≤ ((offset + align - 1) / align) * align (ceiling div property)
    rw [Nat.mul_comm]
    have := Nat.div_add_mod (offset + align - 1) align
    have := Nat.mod_lt (offset + align - 1) hpos
    omega

/-- alignUp of zero is zero. -/
theorem alignUp_zero (align : Nat) : alignUp 0 align = 0 := by
  simp only [alignUp, beq_iff_eq]
  split
  · rfl
  · rename_i hne
    have hpos : 0 < align := Nat.pos_of_ne_zero hne
    have : (align - 1) / align = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]

/-- alignUp with alignment 1 is identity. -/
theorem alignUp_one (offset : Nat) : alignUp offset 1 = offset := by
  simp [alignUp]

-- ════════════════════════════════════════════════════════════════════
-- Padding Properties
-- ════════════════════════════════════════════════════════════════════

/-- Padding is in range [0, align). -/
theorem alignPadding_lt (offset align : Nat) (hpos : 0 < align) :
    alignPadding offset align < align := by
  unfold alignPadding
  split
  · omega
  · exact Nat.mod_lt _ hpos

/-- Padding of an aligned offset is zero. -/
theorem alignPadding_zero_of_aligned (offset align : Nat) (h : isAligned offset align) :
    alignPadding offset align = 0 := by
  obtain ⟨hpos, hmod⟩ := h
  unfold alignPadding
  split
  · omega
  · simp [hmod]

/-- Power of 2: 1 is a power of two. -/
theorem isPowerOfTwo_one : isPowerOfTwo 1 := by decide

/-- Power of 2: 2 is a power of two. -/
theorem isPowerOfTwo_two : isPowerOfTwo 2 := by decide

/-- Power of 2: 4 is a power of two. -/
theorem isPowerOfTwo_four : isPowerOfTwo 4 := by decide

end Radix.Alignment.Spec
