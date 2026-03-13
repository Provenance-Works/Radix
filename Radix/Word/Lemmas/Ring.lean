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



/-! ================================================================ -/
/-! ## Int8 Ring Properties                               -/
/-! ================================================================ -/

namespace Int8

@[ext] private theorem ext {a b : _root_.Radix.Int8} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a with | mk val_a =>
  cases b with | mk val_b =>
  have : val_a = val_b := by
    cases val_a; cases val_b; exact congrArg _ h
  exact congrArg _ this

theorem wrappingAdd_comm (x y : Int8) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; apply ext; exact add_comm _ _

theorem wrappingAdd_assoc (x y z : Int8) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; apply ext; exact add_assoc _ _ _

theorem wrappingAdd_zero (x : Int8) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; unfold wrappingAdd; apply ext; exact add_zero _

theorem wrappingMul_comm (x y : Int8) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; apply ext; exact mul_comm _ _

theorem wrappingMul_assoc (x y z : Int8) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; apply ext; exact mul_assoc _ _ _

theorem wrappingMul_one (x : Int8) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; unfold wrappingMul; apply ext; exact mul_one _

theorem wrappingMul_add_distrib (x y z : Int8) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  unfold wrappingMul wrappingAdd; apply ext; exact mul_add _ _ _

end Int8

/-! ================================================================ -/
/-! ## Int16 Ring Properties                               -/
/-! ================================================================ -/

namespace Int16

@[ext] private theorem ext {a b : _root_.Radix.Int16} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a with | mk val_a =>
  cases b with | mk val_b =>
  have : val_a = val_b := by
    cases val_a; cases val_b; exact congrArg _ h
  exact congrArg _ this

theorem wrappingAdd_comm (x y : Int16) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; apply ext; exact add_comm _ _

theorem wrappingAdd_assoc (x y z : Int16) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; apply ext; exact add_assoc _ _ _

theorem wrappingAdd_zero (x : Int16) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; unfold wrappingAdd; apply ext; exact add_zero _

theorem wrappingMul_comm (x y : Int16) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; apply ext; exact mul_comm _ _

theorem wrappingMul_assoc (x y z : Int16) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; apply ext; exact mul_assoc _ _ _

theorem wrappingMul_one (x : Int16) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; unfold wrappingMul; apply ext; exact mul_one _

theorem wrappingMul_add_distrib (x y z : Int16) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  unfold wrappingMul wrappingAdd; apply ext; exact mul_add _ _ _

end Int16

/-! ================================================================ -/
/-! ## Int32 Ring Properties                               -/
/-! ================================================================ -/

namespace Int32

@[ext] private theorem ext {a b : _root_.Radix.Int32} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a with | mk val_a =>
  cases b with | mk val_b =>
  have : val_a = val_b := by
    cases val_a; cases val_b; exact congrArg _ h
  exact congrArg _ this

theorem wrappingAdd_comm (x y : Int32) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; apply ext; exact add_comm _ _

theorem wrappingAdd_assoc (x y z : Int32) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; apply ext; exact add_assoc _ _ _

theorem wrappingAdd_zero (x : Int32) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; unfold wrappingAdd; apply ext; exact add_zero _

theorem wrappingMul_comm (x y : Int32) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; apply ext; exact mul_comm _ _

theorem wrappingMul_assoc (x y z : Int32) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; apply ext; exact mul_assoc _ _ _

theorem wrappingMul_one (x : Int32) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; unfold wrappingMul; apply ext; exact mul_one _

theorem wrappingMul_add_distrib (x y z : Int32) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  unfold wrappingMul wrappingAdd; apply ext; exact mul_add _ _ _

end Int32

/-! ================================================================ -/
/-! ## Int64 Ring Properties                               -/
/-! ================================================================ -/

namespace Int64

@[ext] private theorem ext {a b : _root_.Radix.Int64} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a with | mk val_a =>
  cases b with | mk val_b =>
  have : val_a = val_b := by
    cases val_a; cases val_b; exact congrArg _ h
  exact congrArg _ this

theorem wrappingAdd_comm (x y : Int64) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; apply ext; exact add_comm _ _

theorem wrappingAdd_assoc (x y z : Int64) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; apply ext; exact add_assoc _ _ _

theorem wrappingAdd_zero (x : Int64) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; unfold wrappingAdd; apply ext; exact add_zero _

theorem wrappingMul_comm (x y : Int64) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; apply ext; exact mul_comm _ _

theorem wrappingMul_assoc (x y z : Int64) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; apply ext; exact mul_assoc _ _ _

theorem wrappingMul_one (x : Int64) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; unfold wrappingMul; apply ext; exact mul_one _

theorem wrappingMul_add_distrib (x y z : Int64) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  unfold wrappingMul wrappingAdd; apply ext; exact mul_add _ _ _

end Int64



/-! ================================================================ -/
/-! ## UWord Ring Properties                                    -/
/-! ================================================================ -/

namespace UWord

variable {w : Nat} [PlatformWidth w]

@[ext] private theorem ext {a b : UWord w} (h : a.val = b.val) : a = b := by
  cases a; cases b; exact congrArg _ h

theorem wrappingAdd_comm (x y : UWord w) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; apply ext; exact add_comm x.val y.val

theorem wrappingAdd_assoc (x y z : UWord w) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; apply ext; exact add_assoc x.val y.val z.val

theorem wrappingAdd_zero (x : UWord w) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; unfold wrappingAdd; apply ext; exact add_zero _

theorem wrappingMul_comm (x y : UWord w) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; apply ext; exact mul_comm x.val y.val

theorem wrappingMul_assoc (x y z : UWord w) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; apply ext; exact mul_assoc x.val y.val z.val

theorem wrappingMul_one (x : UWord w) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; unfold wrappingMul; apply ext; exact mul_one _

theorem wrappingMul_add_distrib (x y z : UWord w) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  unfold wrappingMul wrappingAdd; apply ext; exact left_distrib x.val y.val z.val

end UWord

/-! ================================================================ -/
/-! ## IWord Ring Properties                                    -/
/-! ================================================================ -/

namespace IWord

variable {w : Nat} [PlatformWidth w]

@[ext] private theorem ext {a b : IWord w} (h : a.val = b.val) : a = b := by
  cases a; cases b; exact congrArg _ h

theorem wrappingAdd_comm (x y : IWord w) :
    wrappingAdd x y = wrappingAdd y x := by
  unfold wrappingAdd; apply ext; exact add_comm x.val y.val

theorem wrappingAdd_assoc (x y z : IWord w) :
    wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z) := by
  unfold wrappingAdd; apply ext; exact add_assoc x.val y.val z.val

theorem wrappingAdd_zero (x : IWord w) : wrappingAdd x 0 = x := by
  show wrappingAdd x ⟨0⟩ = x; unfold wrappingAdd; apply ext; exact add_zero _

theorem wrappingMul_comm (x y : IWord w) :
    wrappingMul x y = wrappingMul y x := by
  unfold wrappingMul; apply ext; exact mul_comm x.val y.val

theorem wrappingMul_assoc (x y z : IWord w) :
    wrappingMul (wrappingMul x y) z = wrappingMul x (wrappingMul y z) := by
  unfold wrappingMul; apply ext; exact mul_assoc x.val y.val z.val

theorem wrappingMul_one (x : IWord w) : wrappingMul x 1 = x := by
  show wrappingMul x ⟨1⟩ = x; unfold wrappingMul; apply ext; exact mul_one _

theorem wrappingMul_add_distrib (x y z : IWord w) :
    wrappingMul x (wrappingAdd y z) =
    wrappingAdd (wrappingMul x y) (wrappingMul x z) := by
  unfold wrappingMul wrappingAdd; apply ext; exact left_distrib x.val y.val z.val

end IWord

/-! ================================================================ -/
/-! ## Additional Ring Properties                                     -/
/-! ================================================================ -/

namespace UInt8

theorem zero_wrappingAdd (x : UInt8) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingSub_zero (x : UInt8) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingSub_self (x : UInt8) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; bv_decide

/-- Additive inverse: `x + (-x) = 0` (mod 2⁸). -/
theorem wrappingAdd_wrappingNeg (x : UInt8) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x; unfold wrappingAdd wrappingNeg; congr 1; bv_decide

theorem wrappingAdd_mul_distrib (x y z : UInt8) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end UInt8

namespace UInt16

theorem zero_wrappingAdd (x : UInt16) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingSub_zero (x : UInt16) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingSub_self (x : UInt16) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingAdd_wrappingNeg (x : UInt16) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x; unfold wrappingAdd wrappingNeg; congr 1; bv_decide

theorem wrappingAdd_mul_distrib (x y z : UInt16) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end UInt16

namespace UInt32

theorem zero_wrappingAdd (x : UInt32) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingSub_zero (x : UInt32) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingSub_self (x : UInt32) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingAdd_wrappingNeg (x : UInt32) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x; unfold wrappingAdd wrappingNeg; congr 1; bv_decide

theorem wrappingAdd_mul_distrib (x y z : UInt32) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end UInt32

namespace UInt64

theorem zero_wrappingAdd (x : UInt64) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingSub_zero (x : UInt64) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingSub_self (x : UInt64) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingAdd_wrappingNeg (x : UInt64) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x; unfold wrappingAdd wrappingNeg; congr 1; bv_decide

theorem wrappingAdd_mul_distrib (x y z : UInt64) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end UInt64

namespace Int8

theorem zero_wrappingAdd (x : Int8) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingSub_zero (x : Int8) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingSub_self (x : Int8) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingAdd_wrappingNeg (x : Int8) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x; unfold wrappingAdd wrappingNeg; congr 1; bv_decide

theorem wrappingAdd_mul_distrib (x y z : Int8) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end Int8

namespace Int16

theorem zero_wrappingAdd (x : Int16) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingSub_zero (x : Int16) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingSub_self (x : Int16) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingAdd_wrappingNeg (x : Int16) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x; unfold wrappingAdd wrappingNeg; congr 1; bv_decide

theorem wrappingAdd_mul_distrib (x y z : Int16) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end Int16

namespace Int32

theorem zero_wrappingAdd (x : Int32) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingSub_zero (x : Int32) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingSub_self (x : Int32) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingAdd_wrappingNeg (x : Int32) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x; unfold wrappingAdd wrappingNeg; congr 1; bv_decide

theorem wrappingAdd_mul_distrib (x y z : Int32) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end Int32

namespace Int64

theorem zero_wrappingAdd (x : Int64) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; bv_decide

theorem wrappingSub_zero (x : Int64) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingSub_self (x : Int64) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; bv_decide

theorem wrappingAdd_wrappingNeg (x : Int64) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x; unfold wrappingAdd wrappingNeg; congr 1; bv_decide

theorem wrappingAdd_mul_distrib (x y z : Int64) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end Int64

namespace UWord

variable {w : Nat} [PlatformWidth w]

theorem zero_wrappingAdd (x : UWord w) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; exact zero_add _

theorem wrappingSub_zero (x : UWord w) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; exact sub_zero _

theorem wrappingSub_self (x : UWord w) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; exact sub_self _

theorem wrappingAdd_wrappingNeg (x : UWord w) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x with | mk val =>
  unfold wrappingAdd wrappingNeg; congr 1; simp

theorem wrappingAdd_mul_distrib (x y z : UWord w) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end UWord

namespace IWord

variable {w : Nat} [PlatformWidth w]

theorem zero_wrappingAdd (x : IWord w) : wrappingAdd 0 x = x := by
  show wrappingAdd ⟨0⟩ x = x; cases x; unfold wrappingAdd; congr 1; exact zero_add _

theorem wrappingSub_zero (x : IWord w) : wrappingSub x 0 = x := by
  show wrappingSub x ⟨0⟩ = x; cases x; unfold wrappingSub; congr 1; exact sub_zero _

theorem wrappingSub_self (x : IWord w) : wrappingSub x x = 0 := by
  show wrappingSub x x = ⟨0⟩; cases x; unfold wrappingSub; congr 1; exact sub_self _

theorem wrappingAdd_wrappingNeg (x : IWord w) :
    wrappingAdd x (wrappingNeg x) = 0 := by
  show wrappingAdd x (wrappingNeg x) = ⟨0⟩
  cases x with | mk val =>
  unfold wrappingAdd wrappingNeg; congr 1; simp

theorem wrappingAdd_mul_distrib (x y z : IWord w) :
    wrappingMul (wrappingAdd x y) z =
    wrappingAdd (wrappingMul x z) (wrappingMul y z) := by
  rw [wrappingMul_comm (wrappingAdd x y) z, wrappingMul_add_distrib z x y,
      wrappingMul_comm z x, wrappingMul_comm z y]

end IWord

end Radix
