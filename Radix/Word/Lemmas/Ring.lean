/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.Arith
import Mathlib.Data.BitVec

/-!
# Wrapping Arithmetic Ring Structure Proofs (Layer 3)

This module proves that wrapping arithmetic on each unsigned integer type
forms a commutative ring modulo `2^n`.

## Architecture

This is a **Layer 3 (Verified Specification)** module with proofs.

## References

- FR-001.3: Wrapping arithmetic forms a ring (mod 2^n)
-/

namespace Radix

/-! ================================================================ -/
/-! ## UInt8 Ring Properties                                       -/
/-! ================================================================ -/

namespace UInt8

@[ext] private theorem ext {a b : _root_.UInt8} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; exact congrArg _ h

-- Helper: unwrap to BitVec for reasoning
private theorem toBitVec_add (x y : UInt8) :
    (x + y).toBitVec = x.toBitVec + y.toBitVec := rfl

private theorem toBitVec_mul (x y : UInt8) :
    (x * y).toBitVec = x.toBitVec * y.toBitVec := rfl

/-- Wrapping addition is commutative. -/
theorem wrappingAdd_comm (x y : UInt8) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; congr 1; bv_decide

/-- Wrapping addition is associative. -/
theorem wrappingAdd_assoc (x y z : UInt8) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; congr 1; bv_decide

/-- Zero is the additive identity. -/
theorem wrappingAdd_zero (x : UInt8) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; cases x; unfold wrappingAdd; congr 1; bv_decide

/-- Wrapping multiplication is commutative. -/
theorem wrappingMul_comm (x y : UInt8) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; congr 1; apply ext; exact mul_comm _ _

/-- Wrapping multiplication is associative. -/
theorem wrappingMul_assoc (x y z : UInt8) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; congr 1; apply ext; exact mul_assoc _ _ _

/-- One is the multiplicative identity. -/
theorem wrappingMul_one (x : UInt8) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; cases x; unfold wrappingMul; congr 1; apply ext; exact mul_one _

/-- Left distributivity of multiplication over addition. -/
theorem wrappingMul_add_distrib (x y z : UInt8) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  cases x; cases y; cases z
  unfold wrappingMul wrappingAdd; congr 1; apply ext; exact mul_add _ _ _

end UInt8

/-! ================================================================ -/
/-! ## UInt16 Ring Properties                                      -/
/-! ================================================================ -/

namespace UInt16

@[ext] private theorem ext {a b : _root_.UInt16} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; exact congrArg _ h

private theorem toBitVec_add (x y : UInt16) :
    (x + y).toBitVec = x.toBitVec + y.toBitVec := rfl

private theorem toBitVec_mul (x y : UInt16) :
    (x * y).toBitVec = x.toBitVec * y.toBitVec := rfl

theorem wrappingAdd_comm (x y : UInt16) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; congr 1; bv_decide

theorem wrappingAdd_assoc (x y z : UInt16) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; congr 1; bv_decide

theorem wrappingAdd_zero (x : UInt16) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingMul_comm (x y : UInt16) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; congr 1; apply ext; exact mul_comm _ _

theorem wrappingMul_assoc (x y z : UInt16) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; congr 1; apply ext; exact mul_assoc _ _ _

theorem wrappingMul_one (x : UInt16) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; cases x; unfold wrappingMul; congr 1; apply ext; exact mul_one _

theorem wrappingMul_add_distrib (x y z : UInt16) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  cases x; cases y; cases z
  unfold wrappingMul wrappingAdd; congr 1; apply ext; exact mul_add _ _ _

end UInt16

/-! ================================================================ -/
/-! ## UInt32 Ring Properties                                      -/
/-! ================================================================ -/

namespace UInt32

@[ext] private theorem ext {a b : _root_.UInt32} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; exact congrArg _ h

private theorem toBitVec_add (x y : UInt32) :
    (x + y).toBitVec = x.toBitVec + y.toBitVec := rfl

private theorem toBitVec_mul (x y : UInt32) :
    (x * y).toBitVec = x.toBitVec * y.toBitVec := rfl

theorem wrappingAdd_comm (x y : UInt32) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; congr 1; bv_decide

theorem wrappingAdd_assoc (x y z : UInt32) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; congr 1; bv_decide

theorem wrappingAdd_zero (x : UInt32) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingMul_comm (x y : UInt32) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; congr 1; apply ext; exact mul_comm _ _

theorem wrappingMul_assoc (x y z : UInt32) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; congr 1; apply ext; exact mul_assoc _ _ _

theorem wrappingMul_one (x : UInt32) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; cases x; unfold wrappingMul; congr 1; apply ext; exact mul_one _

theorem wrappingMul_add_distrib (x y z : UInt32) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  cases x; cases y; cases z
  unfold wrappingMul wrappingAdd; congr 1; apply ext; exact mul_add _ _ _

end UInt32

/-! ================================================================ -/
/-! ## UInt64 Ring Properties                                      -/
/-! ================================================================ -/

namespace UInt64

@[ext] private theorem ext {a b : _root_.UInt64} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; exact congrArg _ h

private theorem toBitVec_add (x y : UInt64) :
    (x + y).toBitVec = x.toBitVec + y.toBitVec := rfl

private theorem toBitVec_mul (x y : UInt64) :
    (x * y).toBitVec = x.toBitVec * y.toBitVec := rfl

theorem wrappingAdd_comm (x y : UInt64) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; congr 1; bv_decide

theorem wrappingAdd_assoc (x y z : UInt64) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; congr 1; bv_decide

theorem wrappingAdd_zero (x : UInt64) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingMul_comm (x y : UInt64) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; congr 1; apply ext; exact mul_comm _ _

theorem wrappingMul_assoc (x y z : UInt64) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; congr 1; apply ext; exact mul_assoc _ _ _

theorem wrappingMul_one (x : UInt64) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; cases x; unfold wrappingMul; congr 1; apply ext; exact mul_one _

theorem wrappingMul_add_distrib (x y z : UInt64) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  cases x; cases y; cases z
  unfold wrappingMul wrappingAdd; congr 1; apply ext; exact mul_add _ _ _

end UInt64

end Radix
