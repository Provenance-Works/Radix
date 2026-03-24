/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Alignment.Spec
import Radix.Alignment.Ops

/-!
# Alignment Proofs (Layer 3)

Formal proofs for alignment operations:
- `alignUp` always produces an aligned result
- `alignDown` always produces an aligned result
- Round-trip: `alignDown x a ≤ x ≤ alignUp x a`
- `isAligned` equivalence with spec
- Power-of-two fast path equivalence
- Padding properties

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- v0.2.0 Roadmap: Alignment Utilities
-/

namespace Radix.Alignment

open Radix.Alignment.Spec

/-! ## Helper for simplifying `if align == 0` with `h : align > 0` -/

private theorem beq_zero_false_of_pos {n : Nat} (h : n > 0) : (n == 0) = false := by
  simp
  omega

/-! ## isAligned Properties -/

/-- Zero is aligned to any positive alignment. -/
theorem isAligned_zero (align : Nat) (h : align > 0) :
    Spec.isAligned 0 align := by
  exact ⟨h, by simp⟩

/-- Any multiple of `align` is aligned. -/
theorem isAligned_mul (k align : Nat) (h : align > 0) :
    Spec.isAligned (k * align) align := by
  exact ⟨h, by rw [Nat.mul_comm]; exact Nat.mul_mod_right align k⟩

/-- `align` itself is aligned to `align`. -/
theorem isAligned_self (align : Nat) (h : align > 0) :
    Spec.isAligned align align := by
  have := isAligned_mul 1 align h
  simp at this
  exact this

/-- Adding `align` to an aligned offset stays aligned. -/
theorem isAligned_add_align (offset align : Nat)
    (h : Spec.isAligned offset align) :
    Spec.isAligned (offset + align) align := by
  obtain ⟨hpos, hmod⟩ := h
  refine ⟨hpos, ?_⟩
  rw [Nat.add_mod_right]
  exact hmod

/-! ## alignDown Properties -/

/-- `alignDown` result is ≤ the input. -/
theorem alignDown_le (offset align : Nat) (h : align > 0) :
    Spec.alignDown offset align ≤ offset := by
  unfold Spec.alignDown
  simp [beq_zero_false_of_pos h]
  exact Nat.div_mul_le_self offset align

/-- `alignDown` produces an aligned result. -/
theorem alignDown_isAligned (offset align : Nat) (h : align > 0) :
    Spec.isAligned (Spec.alignDown offset align) align := by
  unfold Spec.alignDown
  simp [beq_zero_false_of_pos h]
  exact ⟨h, by rw [Nat.mul_comm]; exact Nat.mul_mod_right align (offset / align)⟩

/-- `alignDown` of an already-aligned offset is identity. -/
theorem alignDown_of_isAligned (offset align : Nat)
    (h : Spec.isAligned offset align) :
    Spec.alignDown offset align = offset := by
  obtain ⟨hpos, hmod⟩ := h
  unfold Spec.alignDown
  simp [beq_zero_false_of_pos hpos]
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)

/-! ## alignUp Properties -/

/-- `alignUp` result is ≥ the input. -/
theorem alignUp_ge (offset align : Nat) (h : align > 0) :
    offset ≤ Spec.alignUp offset align := by
  unfold Spec.alignUp
  simp [beq_zero_false_of_pos h]
  have h1 := Nat.mod_lt (offset + align - 1) h
  have h2 := Nat.div_add_mod (offset + align - 1) align
  have h3 : align * ((offset + align - 1) / align) =
      (offset + align - 1) / align * align := Nat.mul_comm _ _
  omega

/-- `alignUp` of an already-aligned offset is identity. -/
theorem alignUp_of_isAligned (offset align : Nat)
    (h : Spec.isAligned offset align) :
    Spec.alignUp offset align = offset := by
  obtain ⟨hpos, hmod⟩ := h
  unfold Spec.alignUp
  simp [beq_zero_false_of_pos hpos]
  -- Goal: (offset + align - 1) / align * align = offset
  have hdvd := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨k, hk⟩ := hdvd
  -- hk : offset = align * k
  rw [hk]
  rw [show align * k + align - 1 = (align - 1) + align * k from by omega]
  rw [Nat.add_mul_div_left _ _ hpos]
  have h1 : (align - 1) / align = 0 := Nat.div_eq_of_lt (by omega)
  rw [h1, Nat.zero_add, Nat.mul_comm]

/-- `alignUp` produces an aligned result. -/
theorem alignUp_isAligned (offset align : Nat) (h : align > 0) :
    Spec.isAligned (Spec.alignUp offset align) align := by
  unfold Spec.alignUp
  simp [beq_zero_false_of_pos h]
  exact ⟨h, by rw [Nat.mul_comm]; exact Nat.mul_mod_right align _⟩

/-! ## alignDown ≤ offset ≤ alignUp -/

/-- The fundamental alignment sandwich: `alignDown ≤ x ≤ alignUp`. -/
theorem alignDown_le_alignUp (offset align : Nat) (h : align > 0) :
    Spec.alignDown offset align ≤ Spec.alignUp offset align := by
  calc Spec.alignDown offset align ≤ offset := alignDown_le offset align h
    _ ≤ Spec.alignUp offset align := alignUp_ge offset align h

/-! ## Padding Properties -/

/-- Padding is always less than alignment. -/
theorem alignPadding_lt (offset align : Nat) (h : align > 0) :
    Spec.alignPadding offset align < align := by
  unfold Spec.alignPadding
  simp [beq_zero_false_of_pos h]
  exact Nat.mod_lt _ h

/-- Padding for an already-aligned offset is zero. -/
theorem alignPadding_of_isAligned (offset align : Nat)
    (h : Spec.isAligned offset align) :
    Spec.alignPadding offset align = 0 := by
  obtain ⟨hpos, hmod⟩ := h
  unfold Spec.alignPadding
  simp [beq_zero_false_of_pos hpos, hmod]

/-- `offset + padding` is aligned. -/
theorem offset_add_padding_isAligned (offset align : Nat) (h : align > 0) :
    Spec.isAligned (offset + Spec.alignPadding offset align) align := by
  unfold Spec.alignPadding
  simp [beq_zero_false_of_pos h]
  refine ⟨h, ?_⟩
  -- Goal: (offset + (align - offset % align) % align) % align = 0
  have hm := Nat.mod_lt offset h
  by_cases hc : offset % align = 0
  · -- padding is (align - 0) % align = align % align = 0
    simp [hc, Nat.mod_self]
  · -- padding is (align - offset % align) which is < align
    have hm_pos : 0 < offset % align := Nat.pos_of_ne_zero hc
    have hsub_lt : align - offset % align < align := by omega
    rw [Nat.mod_eq_of_lt hsub_lt]
    -- Goal: (offset + (align - offset % align)) % align = 0
    -- offset = (offset / align) * align + offset % align
    -- offset + (align - offset % align) = (offset / align) * align + align
    --                                    = (offset / align + 1) * align
    have hdecomp := Nat.div_add_mod offset align
    have h1 : align * (offset / align) = offset / align * align := Nat.mul_comm _ _
    have hsum : offset + (align - offset % align) = offset / align * align + align := by omega
    rw [hsum, Nat.add_mod_right, Nat.mul_comm]
    exact Nat.mul_mod_right align _

/-! ## Ops vs Spec Equivalence -/

/-- `Ops.isAligned` agrees with `Spec.isAligned` for `align > 0`. -/
theorem ops_isAligned_iff_spec (offset align : Nat) (h : align > 0) :
    Alignment.isAligned offset align = true ↔ Spec.isAligned offset align := by
  unfold Alignment.isAligned Spec.isAligned
  simp [h]

/-- `Ops.alignUp` equals `Spec.alignUp`. -/
theorem ops_alignUp_eq_spec (offset align : Nat) :
    Alignment.alignUp offset align = Spec.alignUp offset align := by
  unfold Alignment.alignUp Spec.alignUp
  rfl

/-- `Ops.alignDown` equals `Spec.alignDown`. -/
theorem ops_alignDown_eq_spec (offset align : Nat) :
    Alignment.alignDown offset align = Spec.alignDown offset align := by
  unfold Alignment.alignDown Spec.alignDown
  rfl

/-! ## Power-of-Two Fast Path Equivalence

When alignment is a power of two, the bitwise operations (`alignUpPow2`,
`alignDownPow2`, `isAlignedPow2`) produce exactly the same results as the
division-based spec operations. This formally justifies replacing division
with bit masks as a performance optimization. -/

/-- For 2^k, the lower-bit mask equals the mod: x &&& (2^k - 1) = x % 2^k. -/
private theorem nat_and_two_pow_sub_one_eq_mod (k x : Nat) :
    x &&& (2 ^ k - 1) = x % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_mod_two_pow]

/-- Subtracting the remainder gives the quotient product. -/
private theorem nat_sub_mod_eq_div_mul (x n : Nat) :
    x - x % n = x / n * n := by
  have h := Nat.div_add_mod x n
  rw [Nat.mul_comm] at h
  omega

/-- Bridge from `Spec.isPowerOfTwo` (bitwise test) to `Nat.isPowerOfTwo` (existential). -/
private theorem spec_isPowerOfTwo_to_nat (n : Nat) (h : Spec.isPowerOfTwo n) :
    Nat.isPowerOfTwo n := by
  obtain ⟨hpos, hand⟩ := h
  exact (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).mp hand

/-- For power-of-two n, masking with (n - 1) equals mod n. -/
private theorem land_sub_one_eq_mod (n x : Nat) (hpow : Nat.isPowerOfTwo n) :
    x &&& (n - 1) = x % n := by
  obtain ⟨k, rfl⟩ := hpow
  exact nat_and_two_pow_sub_one_eq_mod k x

/-- `alignDownPow2` equals `Spec.alignDown` when alignment is a power of two. -/
theorem alignDownPow2_eq_spec (offset align : Nat) (h : Spec.isPowerOfTwo align) :
    Alignment.alignDownPow2 offset align = Spec.alignDown offset align := by
  unfold Alignment.alignDownPow2 Spec.alignDown
  have hpos : align > 0 := h.1
  simp [beq_zero_false_of_pos hpos]
  have hpow := spec_isPowerOfTwo_to_nat align h
  rw [land_sub_one_eq_mod align offset hpow, nat_sub_mod_eq_div_mul]

/-- `alignUpPow2` equals `Spec.alignUp` when alignment is a power of two. -/
theorem alignUpPow2_eq_spec (offset align : Nat) (h : Spec.isPowerOfTwo align) :
    Alignment.alignUpPow2 offset align = Spec.alignUp offset align := by
  unfold Alignment.alignUpPow2 Spec.alignUp
  have hpos : align > 0 := h.1
  simp [beq_zero_false_of_pos hpos]
  have hpow := spec_isPowerOfTwo_to_nat align h
  rw [land_sub_one_eq_mod align (offset + (align - 1)) hpow, nat_sub_mod_eq_div_mul]
  have : offset + (align - 1) = offset + align - 1 := by omega
  rw [this]

/-- `isAlignedPow2` is equivalent to `Spec.isAligned` for power-of-two alignment. -/
theorem isAlignedPow2_iff_spec (offset align : Nat) (h : Spec.isPowerOfTwo align) :
    Alignment.isAlignedPow2 offset align = true ↔ Spec.isAligned offset align := by
  unfold Alignment.isAlignedPow2 Spec.isAligned
  have hpos : align > 0 := h.1
  have hpow := spec_isPowerOfTwo_to_nat align h
  constructor
  · intro heq
    refine ⟨hpos, ?_⟩
    have hland : offset &&& (align - 1) = 0 := by simpa using heq
    rw [land_sub_one_eq_mod align offset hpow] at hland
    exact hland
  · intro ⟨_, hmod⟩
    have := land_sub_one_eq_mod align offset hpow
    simp [this, hmod]

/-! ## Additional Alignment Lemmas -/

/-- `alignDown` distributes: `alignDown (offset + k * align) align = alignDown offset align + k * align`. -/
theorem alignDown_add_mul (offset k align : Nat) (h : align > 0) :
    Spec.alignDown (offset + k * align) align =
    Spec.alignDown offset align + k * align := by
  unfold Spec.alignDown
  simp [beq_zero_false_of_pos h]
  rw [Nat.add_mul_div_right _ _ h]
  rw [Nat.add_mul]

/-- `alignDown` monotone: if `a ≤ b` and both are in the same alignment class,
    then `alignDown a align ≤ alignDown b align`. -/
theorem alignDown_mono (a b align : Nat) (h : align > 0) (hab : a ≤ b) :
    Spec.alignDown a align ≤ Spec.alignDown b align := by
  unfold Spec.alignDown
  simp [beq_zero_false_of_pos h]
  exact Nat.mul_le_mul_right align (Nat.div_le_div_right hab)

/-- `alignUp` monotone: if `a ≤ b` then `alignUp a align ≤ alignUp b align`. -/
theorem alignUp_mono (a b align : Nat) (h : align > 0) (hab : a ≤ b) :
    Spec.alignUp a align ≤ Spec.alignUp b align := by
  unfold Spec.alignUp
  simp [beq_zero_false_of_pos h]
  apply Nat.mul_le_mul_right
  apply Nat.div_le_div_right
  omega

/-- Padding is periodic: `alignPadding (offset + align) align = alignPadding offset align`. -/
theorem alignPadding_add_align (offset align : Nat) (h : align > 0) :
    Spec.alignPadding (offset + align) align = Spec.alignPadding offset align := by
  unfold Spec.alignPadding
  simp [beq_zero_false_of_pos h, Nat.add_mod_right]

/-- `isAligned` for `alignDown` output (Ops-level). -/
theorem ops_alignDown_isAligned (offset align : Nat) (h : align > 0) :
    Alignment.isAligned (Alignment.alignDown offset align) align = true := by
  rw [ops_isAligned_iff_spec _ _ h]
  rw [ops_alignDown_eq_spec]
  exact Spec.alignDown_isAligned offset align h

/-- `isAligned` for `alignUp` output (Ops-level). -/
theorem ops_alignUp_isAligned (offset align : Nat) (h : align > 0) :
    Alignment.isAligned (Alignment.alignUp offset align) align = true := by
  rw [ops_isAligned_iff_spec _ _ h]
  rw [ops_alignUp_eq_spec]
  exact Spec.alignUp_isAligned offset align h

/-- `isPowerOfTwo` implies alignment value is positive. -/
theorem isPowerOfTwo_pos (n : Nat) (h : Spec.isPowerOfTwo n) : 0 < n := h.1

/-! ## Gap and Stride Lemmas -/

/-- `alignUp` is idempotent. -/
theorem alignUp_idempotent (offset align : Nat) (h : align > 0) :
    Spec.alignUp (Spec.alignUp offset align) align = Spec.alignUp offset align :=
  Spec.alignUp_of_isAligned _ _ (alignUp_isAligned offset align h)

/-! ## Alignment Arithmetic at Ops Level -/

/-- Adding aligned offsets preserves alignment (Ops). -/
theorem ops_isAligned_add (a b align : Nat) (h : align > 0)
    (ha : Alignment.isAligned a align = true)
    (hb : Alignment.isAligned b align = true) :
    Alignment.isAligned (a + b) align = true := by
  rw [ops_isAligned_iff_spec _ _ h] at ha hb ⊢
  exact Spec.isAligned_add a b align ha hb

/-- Subtracting aligned offsets preserves alignment (Ops, when a ≥ b). -/
theorem ops_isAligned_sub (a b align : Nat) (h : align > 0) (hab : b ≤ a)
    (ha : Alignment.isAligned a align = true)
    (hb : Alignment.isAligned b align = true) :
    Alignment.isAligned (a - b) align = true := by
  rw [ops_isAligned_iff_spec _ _ h] at ha hb ⊢
  exact Spec.isAligned_sub a b align hab ha hb

/-! ## Page Alignment Lemmas -/

/-- Page-aligned address is also cache-line-aligned. -/
theorem pageAligned_implies_cacheAligned (offset : Nat) (h : Spec.isAligned offset Spec.pageSize) :
    Spec.isAligned offset Spec.cacheLineSize :=
  Spec.isAligned_of_dvd offset Spec.cacheLineSize Spec.pageSize
    ⟨by decide, by decide⟩ h

/-- Concrete: alignUp 0x100 0x1000 = 0x1000. -/
theorem alignUp_0x100_page : Spec.alignUp 0x100 0x1000 = 0x1000 := by native_decide

/-- Concrete: alignDown 0x1234 0x1000 = 0x1000. -/
theorem alignDown_0x1234_page : Spec.alignDown 0x1234 0x1000 = 0x1000 := by native_decide

/-- Concrete: alignUp 0x1234 0x1000 = 0x2000. -/
theorem alignUp_0x1234_page : Spec.alignUp 0x1234 0x1000 = 0x2000 := by native_decide

/-- Concrete: alignPadding 0x1234 0x1000 = 0xDCC. -/
theorem alignPadding_0x1234_page : Spec.alignPadding 0x1234 0x1000 = 0xDCC := by native_decide

/-- Concrete: cache-line align 100 → 128. -/
theorem alignUp_100_cacheLine : Spec.alignUp 100 64 = 128 := by native_decide

/-- Concrete: cache-line alignDown 100 → 64. -/
theorem alignDown_100_cacheLine : Spec.alignDown 100 64 = 64 := by native_decide

/-- Concrete: alignPadding 100 64 = 28. -/
theorem alignPadding_100_cacheLine : Spec.alignPadding 100 64 = 28 := by native_decide

/-- Concrete: struct field after 12 bytes at 8-byte alignment starts at 16. -/
theorem structFieldOffset_12_8 : Spec.structFieldOffset 12 8 = 16 := by native_decide

/-- Concrete: struct field after 16 bytes at 8-byte alignment starts at 16. -/
theorem structFieldOffset_16_8 : Spec.structFieldOffset 16 8 = 16 := by native_decide

/-- Concrete: struct size for 20-byte body with 8-byte alignment is 24. -/
theorem structSize_20_8 : Spec.structSize 20 8 = 24 := by native_decide

end Radix.Alignment
