/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Bit.Ops
import Mathlib.Data.BitVec

/-!
# Generic Bitwise Proofs (Layer 3)

This module defines `LawfulBitwise` instances for all concrete unsigned
integer types (UInt8, UInt16, UInt32, UInt64), then proves the Boolean
algebra identities generically for any `LawfulBitwise` type.

This eliminates the 4× copy-paste pattern found in `Bit.Lemmas` where
commutativity, associativity, De Morgan's laws, etc. are proved separately
for each width using `bv_decide`.  The generic proofs here lift to `BitVec`
via the `toBitVec_band/bor/bxor/bnot` laws and then apply Mathlib's
`BitVec`-level lemmas.

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- FR-002.1: Bitwise operations correctness
-/

set_option autoImplicit false

namespace Radix

/-! ## LawfulBitwise Instances -/

instance : LawfulBitwise UInt8 where
  band := UInt8.band
  bor  := UInt8.bor
  bxor := UInt8.bxor
  bnot := UInt8.bnot
  toBitVec_band x y := by cases x; cases y; rfl
  toBitVec_bor  x y := by cases x; cases y; rfl
  toBitVec_bxor x y := by cases x; cases y; rfl
  toBitVec_bnot x   := by cases x; rfl

instance : LawfulBitwise UInt16 where
  band := UInt16.band
  bor  := UInt16.bor
  bxor := UInt16.bxor
  bnot := UInt16.bnot
  toBitVec_band x y := by cases x; cases y; rfl
  toBitVec_bor  x y := by cases x; cases y; rfl
  toBitVec_bxor x y := by cases x; cases y; rfl
  toBitVec_bnot x   := by cases x; rfl

instance : LawfulBitwise UInt32 where
  band := UInt32.band
  bor  := UInt32.bor
  bxor := UInt32.bxor
  bnot := UInt32.bnot
  toBitVec_band x y := by cases x; cases y; rfl
  toBitVec_bor  x y := by cases x; cases y; rfl
  toBitVec_bxor x y := by cases x; cases y; rfl
  toBitVec_bnot x   := by cases x; rfl

instance : LawfulBitwise UInt64 where
  band := UInt64.band
  bor  := UInt64.bor
  bxor := UInt64.bxor
  bnot := UInt64.bnot
  toBitVec_band x y := by cases x; cases y; rfl
  toBitVec_bor  x y := by cases x; cases y; rfl
  toBitVec_bxor x y := by cases x; cases y; rfl
  toBitVec_bnot x   := by cases x; rfl

/-! ## Generic Boolean Algebra Proofs -/

section GenericBit

variable {α : Type} [inst : LawfulBitwise α]

/-! ### Commutativity -/

/-- Bitwise AND is commutative. -/
theorem GenericBit.band_comm (x y : α) : inst.band x y = inst.band y x := by
  have h : inst.toBitVec (inst.band x y) = inst.toBitVec (inst.band y x) := by
    rw [inst.toBitVec_band, inst.toBitVec_band, BitVec.and_comm]
  exact LawfulFixedWidth.toBitVec_injective h

/-- Bitwise OR is commutative. -/
theorem GenericBit.bor_comm (x y : α) : inst.bor x y = inst.bor y x := by
  have h : inst.toBitVec (inst.bor x y) = inst.toBitVec (inst.bor y x) := by
    rw [inst.toBitVec_bor, inst.toBitVec_bor, BitVec.or_comm]
  exact LawfulFixedWidth.toBitVec_injective h

/-- Bitwise XOR is commutative. -/
theorem GenericBit.bxor_comm (x y : α) : inst.bxor x y = inst.bxor y x := by
  have h : inst.toBitVec (inst.bxor x y) = inst.toBitVec (inst.bxor y x) := by
    rw [inst.toBitVec_bxor, inst.toBitVec_bxor, BitVec.xor_comm]
  exact LawfulFixedWidth.toBitVec_injective h

/-! ### Associativity -/

/-- Bitwise AND is associative. -/
theorem GenericBit.band_assoc (x y z : α) :
    inst.band (inst.band x y) z = inst.band x (inst.band y z) := by
  have h : inst.toBitVec (inst.band (inst.band x y) z) =
           inst.toBitVec (inst.band x (inst.band y z)) := by
    rw [inst.toBitVec_band, inst.toBitVec_band, inst.toBitVec_band,
        inst.toBitVec_band, BitVec.and_assoc]
  exact LawfulFixedWidth.toBitVec_injective h

/-- Bitwise OR is associative. -/
theorem GenericBit.bor_assoc (x y z : α) :
    inst.bor (inst.bor x y) z = inst.bor x (inst.bor y z) := by
  have h : inst.toBitVec (inst.bor (inst.bor x y) z) =
           inst.toBitVec (inst.bor x (inst.bor y z)) := by
    rw [inst.toBitVec_bor, inst.toBitVec_bor, inst.toBitVec_bor,
        inst.toBitVec_bor, BitVec.or_assoc]
  exact LawfulFixedWidth.toBitVec_injective h

/-- Bitwise XOR is associative. -/
theorem GenericBit.bxor_assoc (x y z : α) :
    inst.bxor (inst.bxor x y) z = inst.bxor x (inst.bxor y z) := by
  have h : inst.toBitVec (inst.bxor (inst.bxor x y) z) =
           inst.toBitVec (inst.bxor x (inst.bxor y z)) := by
    rw [inst.toBitVec_bxor, inst.toBitVec_bxor, inst.toBitVec_bxor,
        inst.toBitVec_bxor, BitVec.xor_assoc]
  exact LawfulFixedWidth.toBitVec_injective h

/-! ### Self-Inverse / Involution -/

/-- XOR with self yields zero. -/
theorem GenericBit.bxor_self (x : α) :
    inst.bxor x x = FixedWidth.fromBitVec (0#inst.bitWidth) := by
  have h : inst.toBitVec (inst.bxor x x) =
           inst.toBitVec (FixedWidth.fromBitVec (0#inst.bitWidth) : α) := by
    rw [inst.toBitVec_bxor, inst.toBitVec_fromBitVec, BitVec.xor_self]
  exact LawfulFixedWidth.toBitVec_injective h

/-- Double complement is identity. -/
theorem GenericBit.bnot_bnot (x : α) : inst.bnot (inst.bnot x) = x := by
  have h : inst.toBitVec (inst.bnot (inst.bnot x)) = inst.toBitVec x := by
    rw [inst.toBitVec_bnot, inst.toBitVec_bnot, BitVec.not_not]
  exact LawfulFixedWidth.toBitVec_injective h

/-! ### De Morgan's Laws -/

/-- De Morgan: NOT (AND) = OR (NOT, NOT). -/
theorem GenericBit.demorgan_and (x y : α) :
    inst.bnot (inst.band x y) = inst.bor (inst.bnot x) (inst.bnot y) := by
  have h : inst.toBitVec (inst.bnot (inst.band x y)) =
           inst.toBitVec (inst.bor (inst.bnot x) (inst.bnot y)) := by
    rw [inst.toBitVec_bnot, inst.toBitVec_band, inst.toBitVec_bor,
        inst.toBitVec_bnot, inst.toBitVec_bnot, BitVec.not_and]
  exact LawfulFixedWidth.toBitVec_injective h

/-- De Morgan: NOT (OR) = AND (NOT, NOT). -/
theorem GenericBit.demorgan_or (x y : α) :
    inst.bnot (inst.bor x y) = inst.band (inst.bnot x) (inst.bnot y) := by
  have h : inst.toBitVec (inst.bnot (inst.bor x y)) =
           inst.toBitVec (inst.band (inst.bnot x) (inst.bnot y)) := by
    rw [inst.toBitVec_bnot, inst.toBitVec_bor, inst.toBitVec_band,
        inst.toBitVec_bnot, inst.toBitVec_bnot, BitVec.not_or]
  exact LawfulFixedWidth.toBitVec_injective h

/-! ### Identity Elements -/

/-- AND with allOnes is identity. -/
theorem GenericBit.band_allOnes (x : α) :
    inst.band x (FixedWidth.fromBitVec (BitVec.allOnes inst.bitWidth)) = x := by
  have h : inst.toBitVec (inst.band x (FixedWidth.fromBitVec (BitVec.allOnes inst.bitWidth) : α)) =
           inst.toBitVec x := by
    rw [inst.toBitVec_band, inst.toBitVec_fromBitVec, BitVec.and_allOnes]
  exact LawfulFixedWidth.toBitVec_injective h

/-- OR with zero is identity. -/
theorem GenericBit.bor_zero (x : α) :
    inst.bor x (FixedWidth.fromBitVec (0#inst.bitWidth)) = x := by
  have h : inst.toBitVec (inst.bor x (FixedWidth.fromBitVec (0#inst.bitWidth) : α)) =
           inst.toBitVec x := by
    rw [inst.toBitVec_bor, inst.toBitVec_fromBitVec, BitVec.or_zero]
  exact LawfulFixedWidth.toBitVec_injective h

/-- XOR with zero is identity. -/
theorem GenericBit.bxor_zero (x : α) :
    inst.bxor x (FixedWidth.fromBitVec (0#inst.bitWidth)) = x := by
  have h : inst.toBitVec (inst.bxor x (FixedWidth.fromBitVec (0#inst.bitWidth) : α)) =
           inst.toBitVec x := by
    rw [inst.toBitVec_bxor, inst.toBitVec_fromBitVec, BitVec.xor_zero]
  exact LawfulFixedWidth.toBitVec_injective h

/-! ### Annihilation -/

/-- AND with zero is zero. -/
theorem GenericBit.band_zero (x : α) :
    inst.band x (FixedWidth.fromBitVec (0#inst.bitWidth)) =
    FixedWidth.fromBitVec (0#inst.bitWidth) := by
  apply LawfulFixedWidth.toBitVec_injective
  simp only [inst.toBitVec_band, inst.toBitVec_fromBitVec, BitVec.and_zero]

end GenericBit

end Radix
