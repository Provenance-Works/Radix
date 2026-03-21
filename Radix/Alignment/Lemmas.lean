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
  constructor
  · exact hpos
  · omega

/-! ## alignDown Properties -/

/-- `alignDown` result is ≤ the input. -/
theorem alignDown_le (offset align : Nat) (h : align > 0) :
    Spec.alignDown offset align ≤ offset := by
  simp [Spec.alignDown, h, Nat.beq_eq_false_of_ne (Nat.not_eq_zero_of_lt h)]
  exact Nat.div_mul_le_self offset align

/-- `alignDown` produces an aligned result. -/
theorem alignDown_isAligned (offset align : Nat) (h : align > 0) :
    Spec.isAligned (Spec.alignDown offset align) align := by
  simp [Spec.alignDown, Nat.beq_eq_false_of_ne (Nat.not_eq_zero_of_lt h)]
  constructor
  · exact h
  · simp [Spec.isAligned]
    exact Nat.mul_mod_right (offset / align) align

/-- `alignDown` of an already-aligned offset is identity. -/
theorem alignDown_of_isAligned (offset align : Nat)
    (h : Spec.isAligned offset align) :
    Spec.alignDown offset align = offset := by
  obtain ⟨hpos, hmod⟩ := h
  simp [Spec.alignDown, Nat.beq_eq_false_of_ne (Nat.not_eq_zero_of_lt hpos)]
  exact Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)

/-! ## alignUp Properties -/

/-- `alignUp` result is ≥ the input. -/
theorem alignUp_ge (offset align : Nat) (h : align > 0) :
    offset ≤ Spec.alignUp offset align := by
  simp [Spec.alignUp, Nat.beq_eq_false_of_ne (Nat.not_eq_zero_of_lt h)]
  calc offset ≤ (offset + align - 1) / align * align := by
        have : offset ≤ offset + align - 1 := by omega
        calc offset
            = offset / align * align + offset % align := (Nat.div_add_mod offset align).symm
          _ ≤ (offset + align - 1) / align * align := by
              have hdiv : offset / align ≤ (offset + align - 1) / align := by
                apply Nat.div_le_div_right; omega
              have := Nat.mul_le_mul_right align hdiv
              omega
    _ = _ := by ring

/-- `alignUp` of an already-aligned offset is identity. -/
theorem alignUp_of_isAligned (offset align : Nat)
    (h : Spec.isAligned offset align) :
    Spec.alignUp offset align = offset := by
  obtain ⟨hpos, hmod⟩ := h
  simp [Spec.alignUp, Nat.beq_eq_false_of_ne (Nat.not_eq_zero_of_lt hpos)]
  have hdvd := Nat.dvd_of_mod_eq_zero hmod
  obtain ⟨k, hk⟩ := hdvd
  subst hk
  simp [Nat.mul_div_cancel_left _ hpos]
  ring_nf
  have : k * align + align - 1 = k * align + (align - 1) := by omega
  rw [this]
  rw [Nat.add_div_right_eq_of_lt (by omega)]
  ring

where
  Nat.add_div_right_eq_of_lt {a b : Nat} (h : 0 < b) :
      (a * b + (b - 1)) / b = a := by
    have : a * b + (b - 1) < (a + 1) * b := by
      rw [Nat.add_mul]; omega
    have hle : a ≤ (a * b + (b - 1)) / b := by
      apply Nat.le_div_iff_mul_le h |>.mpr
      omega
    have hlt : (a * b + (b - 1)) / b < a + 1 := by
      apply Nat.div_lt_iff_lt_mul h |>.mpr
      exact this
    omega

/-- `alignUp` produces an aligned result. -/
theorem alignUp_isAligned (offset align : Nat) (h : align > 0) :
    Spec.isAligned (Spec.alignUp offset align) align := by
  simp [Spec.alignUp, Nat.beq_eq_false_of_ne (Nat.not_eq_zero_of_lt h)]
  constructor
  · exact h
  · simp [Spec.isAligned]
    exact Nat.mul_mod_right _ align

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
  simp [Spec.alignPadding, Nat.beq_eq_false_of_ne (Nat.not_eq_zero_of_lt h)]
  exact Nat.mod_lt _ h

/-- Padding for an already-aligned offset is zero. -/
theorem alignPadding_of_isAligned (offset align : Nat)
    (h : Spec.isAligned offset align) :
    Spec.alignPadding offset align = 0 := by
  obtain ⟨hpos, hmod⟩ := h
  simp [Spec.alignPadding, Nat.beq_eq_false_of_ne (Nat.not_eq_zero_of_lt hpos), hmod]

/-- `offset + padding` is aligned. -/
theorem offset_add_padding_isAligned (offset align : Nat) (h : align > 0) :
    Spec.isAligned (offset + Spec.alignPadding offset align) align := by
  simp [Spec.alignPadding, Nat.beq_eq_false_of_ne (Nat.not_eq_zero_of_lt h)]
  constructor
  · exact h
  · simp [Spec.isAligned]
    omega

/-! ## Ops vs Spec Equivalence -/

/-- `Ops.isAligned` agrees with `Spec.isAligned` for `align > 0`. -/
theorem ops_isAligned_iff_spec (offset align : Nat) (h : align > 0) :
    Alignment.isAligned offset align = true ↔ Spec.isAligned offset align := by
  simp [Alignment.isAligned, Spec.isAligned, h]
  omega

/-- `Ops.alignUp` equals `Spec.alignUp`. -/
theorem ops_alignUp_eq_spec (offset align : Nat) :
    Alignment.alignUp offset align = Spec.alignUp offset align := by
  simp [Alignment.alignUp, Spec.alignUp]

/-- `Ops.alignDown` equals `Spec.alignDown`. -/
theorem ops_alignDown_eq_spec (offset align : Nat) :
    Alignment.alignDown offset align = Spec.alignDown offset align := by
  simp [Alignment.alignDown, Spec.alignDown]

end Radix.Alignment
