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

/-- Power of 2: 8 is a power of two. -/
theorem isPowerOfTwo_eight : isPowerOfTwo 8 := by decide

/-- Power of 2: 16 is a power of two. -/
theorem isPowerOfTwo_sixteen : isPowerOfTwo 16 := by decide

-- ════════════════════════════════════════════════════════════════════
-- Additional Alignment Properties
-- ════════════════════════════════════════════════════════════════════

/-- `alignUp` of an aligned offset is identity. -/
theorem alignUp_of_isAligned (offset align : Nat) (h : isAligned offset align) :
    alignUp offset align = offset := by
  obtain ⟨hpos, hmod⟩ := h
  unfold alignUp
  have hne : (align == 0) = false := by simp; omega
  simp [hne]
  have hdvd := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, show align * k + align - 1 = (align - 1) + align * k from by omega]
  rw [Nat.add_mul_div_left _ _ hpos]
  have : (align - 1) / align = 0 := Nat.div_eq_of_lt (by omega)
  rw [this, Nat.zero_add, Nat.mul_comm]

/-- `alignDown` of an aligned offset is identity. -/
theorem alignDown_of_isAligned (offset align : Nat) (h : isAligned offset align) :
    alignDown offset align = offset := by
  obtain ⟨hpos, hmod⟩ := h
  unfold alignDown
  have hne : (align == 0) = false := by simp; omega
  simp [hne]
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)

/-- `alignUp` produces a result aligned to `align`. -/
theorem alignUp_isAligned (offset align : Nat) (hpos : 0 < align) :
    isAligned (alignUp offset align) align := by
  unfold alignUp
  have hne : (align == 0) = false := by simp; omega
  simp [hne]
  exact ⟨hpos, by rw [Nat.mul_comm]; exact Nat.mul_mod_right align _⟩

/-- `alignDown` produces a result aligned to `align`. -/
theorem alignDown_isAligned (offset align : Nat) (hpos : 0 < align) :
    isAligned (alignDown offset align) align := by
  unfold alignDown
  have hne : (align == 0) = false := by simp; omega
  simp [hne]
  exact ⟨hpos, by rw [Nat.mul_comm]; exact Nat.mul_mod_right align _⟩

/-- If offset is aligned, `alignUp offset align = offset`. -/
theorem alignUp_eq_of_aligned (offset align : Nat) (h : isAligned offset align) :
    alignUp offset align = offset := by
  obtain ⟨hpos, hmod⟩ := h
  unfold alignUp
  have hne : (align == 0) = false := by simp; omega
  simp [hne]
  have hdvd := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, show align * k + align - 1 = (align - 1) + align * k from by omega]
  rw [Nat.add_mul_div_left _ _ hpos]
  have : (align - 1) / align = 0 := Nat.div_eq_of_lt (by omega)
  rw [this, Nat.zero_add, Nat.mul_comm]

/-- If offset is aligned, `alignDown offset align = offset`. -/
theorem alignDown_eq_of_aligned (offset align : Nat) (h : isAligned offset align) :
    alignDown offset align = offset := by
  obtain ⟨hpos, hmod⟩ := h
  unfold alignDown
  have hne : (align == 0) = false := by simp; omega
  simp [hne]
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)

/-- Fundamental sandwich: `alignDown offset align ≤ offset ≤ alignUp offset align`. -/
theorem alignDown_le_le_alignUp (offset align : Nat) (hpos : 0 < align) :
    alignDown offset align ≤ offset ∧ offset ≤ alignUp offset align :=
  ⟨alignDown_le offset align, alignUp_ge offset align hpos⟩

/-- `alignDown` distributes over alignment multiples:
    `alignDown (k * align) align = k * align`. -/
theorem alignDown_mul (k align : Nat) (hpos : 0 < align) :
    alignDown (k * align) align = k * align :=
  alignDown_eq_of_aligned _ _ (isAligned_mul k align hpos)

/-- `alignUp` of a multiple is identity. -/
theorem alignUp_mul (k align : Nat) (hpos : 0 < align) :
    alignUp (k * align) align = k * align :=
  alignUp_eq_of_aligned _ _ (isAligned_mul k align hpos)

/-- Padding at zero offset is always zero. -/
theorem alignPadding_zero (align : Nat) (hpos : 0 < align) :
    alignPadding 0 align = 0 :=
  alignPadding_zero_of_aligned 0 align (isAligned_zero align hpos)

-- ════════════════════════════════════════════════════════════════════
-- Gap and Stride
-- ════════════════════════════════════════════════════════════════════

/-- The alignment gap: distance between alignUp and alignDown.
    Always equals the padding needed. -/
def alignGap (offset align : Nat) : Nat :=
  alignUp offset align - alignDown offset align

/-- Count of aligned addresses in a half-open range [lo, hi).
    Both lo and hi must be multiples of align. -/
def strideCount (lo hi align : Nat) : Nat :=
  if align == 0 then 0
  else if hi ≤ lo then 0
  else (hi - lo) / align

/-- When already aligned, the gap is zero. -/
theorem alignGap_zero_of_aligned (offset align : Nat) (h : isAligned offset align) :
    alignGap offset align = 0 := by
  unfold alignGap
  rw [alignUp_of_isAligned _ _ h, alignDown_of_isAligned _ _ h]
  omega

/-- strideCount of an empty range is zero. -/
theorem strideCount_empty (lo align : Nat) : strideCount lo lo align = 0 := by
  unfold strideCount; split <;> simp_all

/-- Gap of 0 at alignment 4 is 0. -/
theorem alignGap_zero_align4 : alignGap 0 4 = 0 := by native_decide

/-- Gap of 1 at alignment 4 is 4 (full alignment span). -/
theorem alignGap_one_align4 : alignGap 1 4 = 4 := by native_decide

/-- Gap of 3 at alignment 4 is 4 (full alignment span). -/
theorem alignGap_three_align4 : alignGap 3 4 = 4 := by native_decide

/-- Gap of 4 at alignment 4 is 0 (already aligned). -/
theorem alignGap_four_align4 : alignGap 4 4 = 0 := by native_decide

/-- strideCount of [0, 16) at alignment 4 is 4. -/
theorem strideCount_0_16_4 : strideCount 0 16 4 = 4 := by native_decide

/-- strideCount of [4, 16) at alignment 4 is 3. -/
theorem strideCount_4_16_4 : strideCount 4 16 4 = 3 := by native_decide

-- ════════════════════════════════════════════════════════════════════
-- Alignment Composition
-- ════════════════════════════════════════════════════════════════════

/-- Check whether alignment `a` divides alignment `b` (b is at least as strict). -/
def alignmentDivides (a b : Nat) : Prop := a > 0 ∧ b % a = 0

instance (a b : Nat) : Decidable (alignmentDivides a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Stricter alignment implies weaker alignment.
    If offset is aligned to b and a divides b, then offset is aligned to a. -/
theorem isAligned_of_dvd (offset a b : Nat)
    (hdvd : alignmentDivides a b) (hb : isAligned offset b) : isAligned offset a := by
  obtain ⟨hapos, hamod⟩ := hdvd
  obtain ⟨_, hbmod⟩ := hb
  refine ⟨hapos, ?_⟩
  have hadvd := Nat.dvd_of_mod_eq_zero hamod
  have hbdvd := Nat.dvd_of_mod_eq_zero hbmod
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hadvd hbdvd)

/-- 8-aligned implies 4-aligned. -/
theorem aligned_8_implies_4 (offset : Nat) (h : isAligned offset 8) :
    isAligned offset 4 :=
  isAligned_of_dvd offset 4 8 ⟨by omega, by decide⟩ h

/-- 16-aligned implies 4-aligned. -/
theorem aligned_16_implies_4 (offset : Nat) (h : isAligned offset 16) :
    isAligned offset 4 :=
  isAligned_of_dvd offset 4 16 ⟨by omega, by decide⟩ h

/-- 4096-aligned (page) implies 512-aligned (sector). -/
theorem aligned_page_implies_sector (offset : Nat) (h : isAligned offset 4096) :
    isAligned offset 512 :=
  isAligned_of_dvd offset 512 4096 ⟨by omega, by decide⟩ h

/-- 8-aligned implies 2-aligned. -/
theorem aligned_8_implies_2 (offset : Nat) (h : isAligned offset 8) :
    isAligned offset 2 :=
  isAligned_of_dvd offset 2 8 ⟨by omega, by decide⟩ h

/-- 4096-aligned implies 64-aligned (cache line). -/
theorem aligned_page_implies_cacheline (offset : Nat) (h : isAligned offset 4096) :
    isAligned offset 64 :=
  isAligned_of_dvd offset 64 4096 ⟨by omega, by decide⟩ h

-- ════════════════════════════════════════════════════════════════════
-- Alignment Arithmetic
-- ════════════════════════════════════════════════════════════════════

/-- Adding two aligned offsets preserves alignment. -/
theorem isAligned_add (a b align : Nat) (ha : isAligned a align) (hb : isAligned b align) :
    isAligned (a + b) align := by
  obtain ⟨hpos, hamod⟩ := ha
  obtain ⟨_, hbmod⟩ := hb
  exact ⟨hpos, by rw [Nat.add_mod]; simp [hamod, hbmod]⟩

/-- Subtracting aligned offsets preserves alignment (when a ≥ b). -/
theorem isAligned_sub (a b align : Nat) (hab : b ≤ a)
    (ha : isAligned a align) (hb : isAligned b align) :
    isAligned (a - b) align := by
  obtain ⟨hpos, hamod⟩ := ha
  obtain ⟨_, hbmod⟩ := hb
  refine ⟨hpos, ?_⟩
  have hadvd := Nat.dvd_of_mod_eq_zero hamod
  have hbdvd := Nat.dvd_of_mod_eq_zero hbmod
  obtain ⟨ka, hka⟩ := hadvd
  obtain ⟨kb, hkb⟩ := hbdvd
  subst hka; subst hkb
  have _hle : kb ≤ ka := Nat.le_of_mul_le_mul_left hab hpos
  rw [Nat.mul_comm align ka, Nat.mul_comm align kb, ← Nat.sub_mul]
  exact Nat.mul_mod_left _ _

/-- Scaling an aligned offset preserves alignment. -/
theorem isAligned_mul_left (offset align k : Nat) (h : isAligned offset align) :
    isAligned (k * offset) align := by
  obtain ⟨hpos, hmod⟩ := h
  refine ⟨hpos, ?_⟩
  have hdvd := Nat.dvd_of_mod_eq_zero hmod
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hdvd (Nat.dvd_mul_left offset k))

-- ════════════════════════════════════════════════════════════════════
-- Page Alignment (Common Embedded/OS Pattern)
-- ════════════════════════════════════════════════════════════════════

/-- Standard 4KB page size. -/
def pageSize : Nat := 4096

/-- 4096 is a power of two. -/
theorem isPowerOfTwo_pageSize : isPowerOfTwo pageSize := by native_decide

/-- Page-align up. -/
def pageAlignUp (offset : Nat) : Nat := alignUp offset pageSize

/-- Page-align down. -/
def pageAlignDown (offset : Nat) : Nat := alignDown offset pageSize

/-- Page alignment up preserves the >= property. -/
theorem pageAlignUp_ge (offset : Nat) : offset ≤ pageAlignUp offset :=
  alignUp_ge offset pageSize (by decide)

/-- Page alignment down preserves the <= property. -/
theorem pageAlignDown_le (offset : Nat) : pageAlignDown offset ≤ offset :=
  alignDown_le offset pageSize

/-- Page-aligned up result is 4096-aligned. -/
theorem pageAlignUp_isAligned (offset : Nat) : isAligned (pageAlignUp offset) pageSize :=
  alignUp_isAligned offset pageSize (by decide)

/-- Page-aligned down result is 4096-aligned. -/
theorem pageAlignDown_isAligned (offset : Nat) : isAligned (pageAlignDown offset) pageSize :=
  alignDown_isAligned offset pageSize (by decide)

/-- Number of pages needed to cover `size` bytes (ceiling division). -/
def pageCoverage (size : Nat) : Nat :=
  (size + pageSize - 1) / pageSize

/-- Zero bytes needs zero pages. -/
theorem pageCoverage_zero : pageCoverage 0 = 0 := by native_decide

/-- One byte needs one page. -/
theorem pageCoverage_one : pageCoverage 1 = 1 := by native_decide

/-- Exactly 4096 bytes needs one page. -/
theorem pageCoverage_exact : pageCoverage pageSize = 1 := by native_decide

/-- 4097 bytes needs two pages. -/
theorem pageCoverage_overflow : pageCoverage (pageSize + 1) = 2 := by native_decide

-- ════════════════════════════════════════════════════════════════════
-- Cache Line Alignment (Performance-Critical Pattern)
-- ════════════════════════════════════════════════════════════════════

/-- Standard cache line size (64 bytes on most modern CPUs). -/
def cacheLineSize : Nat := 64

/-- 64 is a power of two. -/
theorem isPowerOfTwo_cacheLineSize : isPowerOfTwo cacheLineSize := by native_decide

/-- Cache-line-align up. -/
def cacheAlignUp (offset : Nat) : Nat := alignUp offset cacheLineSize

/-- Cache-line-align down. -/
def cacheAlignDown (offset : Nat) : Nat := alignDown offset cacheLineSize

/-- Cache alignment: 0 is aligned. -/
theorem cacheAligned_zero : isAligned 0 cacheLineSize := isAligned_zero cacheLineSize (by decide)

/-- Cache alignment: 64 is aligned. -/
theorem cacheAligned_64 : isAligned 64 cacheLineSize := by decide

/-- Cache alignment: 128 is aligned. -/
theorem cacheAligned_128 : isAligned 128 cacheLineSize := by decide

-- ════════════════════════════════════════════════════════════════════
-- Struct Layout Helper
-- ════════════════════════════════════════════════════════════════════

/-- Compute the offset for a struct field, accounting for alignment padding.
    Given the current end-of-struct offset and the field's alignment requirement,
    returns the aligned offset where the field should start. -/
def structFieldOffset (currentEnd fieldAlign : Nat) : Nat :=
  alignUp currentEnd fieldAlign

/-- Compute total struct size with tail padding for array layout.
    The struct size must be a multiple of the struct's alignment. -/
def structSize (bodyEnd structAlign : Nat) : Nat :=
  alignUp bodyEnd structAlign

/-- Struct field offset is always >= current end. -/
theorem structFieldOffset_ge (currentEnd fieldAlign : Nat) (hpos : 0 < fieldAlign) :
    currentEnd ≤ structFieldOffset currentEnd fieldAlign :=
  alignUp_ge currentEnd fieldAlign hpos

/-- Struct size is always >= body end. -/
theorem structSize_ge (bodyEnd structAlign : Nat) (hpos : 0 < structAlign) :
    bodyEnd ≤ structSize bodyEnd structAlign :=
  alignUp_ge bodyEnd structAlign hpos

end Radix.Alignment.Spec
