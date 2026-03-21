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
  simp [beq_iff_eq]; omega

/-! ## isAligned Properties -/

/-- Zero is aligned to any positive alignment. -/
theorem isAligned_zero (align : Nat) (h : align > 0) :
    Spec.isAligned 0 align := by
  simp [Spec.isAligned, h]

/-- Any multiple of `align` is aligned. -/
theorem isAligned_mul (k align : Nat) (h : align > 0) :
    Spec.isAligned (k * align) align := by
  simp [Spec.isAligned, h, Nat.mul_mod_right]

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

end Radix.Alignment
