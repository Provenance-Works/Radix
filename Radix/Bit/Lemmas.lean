/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field
import Radix.Bit.Spec
import Mathlib.Data.BitVec

/-!
# Bitwise Operations Proofs (Layer 3)

This module proves correctness properties of the bitwise operations
defined in `Bit.Ops`, `Bit.Scan`, and `Bit.Field`:
- Boolean algebra: commutativity, associativity, identity, annihilation
- De Morgan's laws
- Shift/rotate identities
- BitVec specification equivalence
- Bit field round-trip properties

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- FR-002: Bitwise operations correctness
- FR-002.1a: Shift/rotate edge cases
-/

namespace Radix

-- Round-trip helpers
@[simp] private theorem UInt8.toBitVec_fromBitVec (bv : BitVec 8) :
    UInt8.toBitVec (UInt8.fromBitVec bv) = bv := by
  simp [UInt8.fromBitVec, UInt8.toBitVec]

@[simp] private theorem UInt8.fromBitVec_toBitVec (x : UInt8) :
    UInt8.fromBitVec (UInt8.toBitVec x) = x := by
  cases x; simp [UInt8.fromBitVec, UInt8.toBitVec]

/-! ================================================================ -/
/-! ## UInt8 Boolean Algebra                                      -/
/-! ================================================================ -/

namespace UInt8

/-! ### Commutativity -/

theorem band_comm (x y : UInt8) : band x y = band y x := by
  unfold band; congr 1; bv_decide
theorem bor_comm (x y : UInt8) : bor x y = bor y x := by
  unfold bor; congr 1; bv_decide
theorem bxor_comm (x y : UInt8) : bxor x y = bxor y x := by
  unfold bxor; congr 1; bv_decide
/-! ### Associativity -/

theorem band_assoc (x y z : UInt8) : band (band x y) z = band x (band y z) := by
  unfold band; congr 1; bv_decide
theorem bor_assoc (x y z : UInt8) : bor (bor x y) z = bor x (bor y z) := by
  unfold bor; congr 1; bv_decide
theorem bxor_assoc (x y z : UInt8) : bxor (bxor x y) z = bxor x (bxor y z) := by
  unfold bxor; congr 1; bv_decide
/-! ### Identity -/

theorem band_allOnes (x : UInt8) : band x ⟨255⟩ = x := by
  cases x; unfold band; congr 1; bv_decide
theorem bor_zero (x : UInt8) : bor x 0 = x := by
  show bor x ⟨0⟩ = x; cases x; unfold bor; congr 1; bv_decide
theorem bxor_zero (x : UInt8) : bxor x 0 = x := by
  show bxor x ⟨0⟩ = x; cases x; unfold bxor; congr 1; bv_decide
/-! ### Annihilation -/

theorem band_zero (x : UInt8) : band x 0 = 0 := by
  show band x ⟨0⟩ = ⟨0⟩; cases x; unfold band; congr 1; bv_decide
theorem bor_allOnes (x : UInt8) : bor x ⟨255⟩ = ⟨255⟩ := by
  cases x; unfold bor; congr 1; bv_decide
/-! ### Self-inverse -/

theorem bxor_self (x : UInt8) : bxor x x = 0 := by
  show bxor x x = ⟨0⟩; cases x; unfold bxor; congr 1; bv_decide
theorem bnot_bnot (x : UInt8) : bnot (bnot x) = x := by
  cases x; unfold bnot; congr 1; bv_decide
/-! ### De Morgan's Laws -/

theorem demorgan_and (x y : UInt8) : bnot (band x y) = bor (bnot x) (bnot y) := by
  unfold bnot band bor; congr 1; bv_decide
theorem demorgan_or (x y : UInt8) : bnot (bor x y) = band (bnot x) (bnot y) := by
  unfold bnot bor band; congr 1; bv_decide
/-! ### Shift Properties -/

/-- Shifting by 0 is identity. -/
theorem shl_zero (x : UInt8) : shl x 0 = x := by
  show shl x ⟨0⟩ = x; cases x; simp [shl, fromBitVec, toBitVec]
/-- Shifting by 0 is identity. -/
theorem shrLogical_zero (x : UInt8) : shrLogical x 0 = x := by
  show shrLogical x ⟨0⟩ = x; cases x; simp [shrLogical, fromBitVec, toBitVec]
/-! ### BitVec Specification Equivalence -/

/-- `band` matches the Layer 3 specification. -/
theorem band_toBitVec (x y : UInt8) :
    (band x y).toBitVec = Bit.Spec.band x.toBitVec y.toBitVec := by
  simp [band, toBitVec, Bit.Spec.band]
/-- `bor` matches the Layer 3 specification. -/
theorem bor_toBitVec (x y : UInt8) :
    (bor x y).toBitVec = Bit.Spec.bor x.toBitVec y.toBitVec := by
  simp [bor, toBitVec, Bit.Spec.bor]
/-- `bxor` matches the Layer 3 specification. -/
theorem bxor_toBitVec (x y : UInt8) :
    (bxor x y).toBitVec = Bit.Spec.bxor x.toBitVec y.toBitVec := by
  simp [bxor, toBitVec, Bit.Spec.bxor]
/-- `bnot` matches the Layer 3 specification. -/
theorem bnot_toBitVec (x : UInt8) :
    (bnot x).toBitVec = Bit.Spec.bnot x.toBitVec := by
  simp [bnot, toBitVec, Bit.Spec.bnot]
end UInt8

namespace UInt16

theorem band_comm (x y : UInt16) : band x y = band y x := by
  unfold band; congr 1; bv_decide
theorem bor_comm (x y : UInt16) : bor x y = bor y x := by
  unfold bor; congr 1; bv_decide
theorem bxor_comm (x y : UInt16) : bxor x y = bxor y x := by
  unfold bxor; congr 1; bv_decide
theorem band_assoc (x y z : UInt16) : band (band x y) z = band x (band y z) := by
  unfold band; congr 1; bv_decide
theorem bor_assoc (x y z : UInt16) : bor (bor x y) z = bor x (bor y z) := by
  unfold bor; congr 1; bv_decide
theorem bxor_assoc (x y z : UInt16) : bxor (bxor x y) z = bxor x (bxor y z) := by
  unfold bxor; congr 1; bv_decide
theorem band_allOnes (x : UInt16) : band x ⟨65535⟩ = x := by
  cases x; unfold band; congr 1; bv_decide
theorem bor_zero (x : UInt16) : bor x 0 = x := by
  show bor x ⟨0⟩ = x; cases x; unfold bor; congr 1; bv_decide
theorem bxor_zero (x : UInt16) : bxor x 0 = x := by
  show bxor x ⟨0⟩ = x; cases x; unfold bxor; congr 1; bv_decide
theorem band_zero (x : UInt16) : band x 0 = 0 := by
  show band x ⟨0⟩ = ⟨0⟩; cases x; unfold band; congr 1; bv_decide
theorem bor_allOnes (x : UInt16) : bor x ⟨65535⟩ = ⟨65535⟩ := by
  cases x; unfold bor; congr 1; bv_decide
theorem bxor_self (x : UInt16) : bxor x x = 0 := by
  show bxor x x = ⟨0⟩; cases x; unfold bxor; congr 1; bv_decide
theorem bnot_bnot (x : UInt16) : bnot (bnot x) = x := by
  cases x; unfold bnot; congr 1; bv_decide
theorem demorgan_and (x y : UInt16) : bnot (band x y) = bor (bnot x) (bnot y) := by
  unfold bnot band bor; congr 1; bv_decide
theorem demorgan_or (x y : UInt16) : bnot (bor x y) = band (bnot x) (bnot y) := by
  unfold bnot bor band; congr 1; bv_decide
theorem shl_zero (x : UInt16) : shl x 0 = x := by
  show shl x ⟨0⟩ = x; cases x; simp [shl, fromBitVec, toBitVec]
theorem shrLogical_zero (x : UInt16) : shrLogical x 0 = x := by
  show shrLogical x ⟨0⟩ = x; cases x; simp [shrLogical, fromBitVec, toBitVec]
theorem band_toBitVec (x y : UInt16) :
    (band x y).toBitVec = Bit.Spec.band x.toBitVec y.toBitVec := by
  simp [band, toBitVec, Bit.Spec.band]
theorem bor_toBitVec (x y : UInt16) :
    (bor x y).toBitVec = Bit.Spec.bor x.toBitVec y.toBitVec := by
  simp [bor, toBitVec, Bit.Spec.bor]
theorem bxor_toBitVec (x y : UInt16) :
    (bxor x y).toBitVec = Bit.Spec.bxor x.toBitVec y.toBitVec := by
  simp [bxor, toBitVec, Bit.Spec.bxor]
theorem bnot_toBitVec (x : UInt16) :
    (bnot x).toBitVec = Bit.Spec.bnot x.toBitVec := by
  simp [bnot, toBitVec, Bit.Spec.bnot]
end UInt16

namespace UInt32

theorem band_comm (x y : UInt32) : band x y = band y x := by
  unfold band; congr 1; bv_decide
theorem bor_comm (x y : UInt32) : bor x y = bor y x := by
  unfold bor; congr 1; bv_decide
theorem bxor_comm (x y : UInt32) : bxor x y = bxor y x := by
  unfold bxor; congr 1; bv_decide
theorem band_assoc (x y z : UInt32) : band (band x y) z = band x (band y z) := by
  unfold band; congr 1; bv_decide
theorem bor_assoc (x y z : UInt32) : bor (bor x y) z = bor x (bor y z) := by
  unfold bor; congr 1; bv_decide
theorem bxor_assoc (x y z : UInt32) : bxor (bxor x y) z = bxor x (bxor y z) := by
  unfold bxor; congr 1; bv_decide
theorem band_allOnes (x : UInt32) : band x ⟨4294967295⟩ = x := by
  cases x; unfold band; congr 1; bv_decide
theorem bor_zero (x : UInt32) : bor x 0 = x := by
  show bor x ⟨0⟩ = x; cases x; unfold bor; congr 1; bv_decide
theorem bxor_zero (x : UInt32) : bxor x 0 = x := by
  show bxor x ⟨0⟩ = x; cases x; unfold bxor; congr 1; bv_decide
theorem band_zero (x : UInt32) : band x 0 = 0 := by
  show band x ⟨0⟩ = ⟨0⟩; cases x; unfold band; congr 1; bv_decide
theorem bor_allOnes (x : UInt32) : bor x ⟨4294967295⟩ = ⟨4294967295⟩ := by
  cases x; unfold bor; congr 1; bv_decide
theorem bxor_self (x : UInt32) : bxor x x = 0 := by
  show bxor x x = ⟨0⟩; cases x; unfold bxor; congr 1; bv_decide
theorem bnot_bnot (x : UInt32) : bnot (bnot x) = x := by
  cases x; unfold bnot; congr 1; bv_decide
theorem demorgan_and (x y : UInt32) : bnot (band x y) = bor (bnot x) (bnot y) := by
  unfold bnot band bor; congr 1; bv_decide
theorem demorgan_or (x y : UInt32) : bnot (bor x y) = band (bnot x) (bnot y) := by
  unfold bnot bor band; congr 1; bv_decide
theorem shl_zero (x : UInt32) : shl x 0 = x := by
  show shl x ⟨0⟩ = x; cases x; simp [shl, fromBitVec, toBitVec]
theorem shrLogical_zero (x : UInt32) : shrLogical x 0 = x := by
  show shrLogical x ⟨0⟩ = x; cases x; simp [shrLogical, fromBitVec, toBitVec]
theorem band_toBitVec (x y : UInt32) :
    (band x y).toBitVec = Bit.Spec.band x.toBitVec y.toBitVec := by
  simp [band, toBitVec, Bit.Spec.band]
theorem bor_toBitVec (x y : UInt32) :
    (bor x y).toBitVec = Bit.Spec.bor x.toBitVec y.toBitVec := by
  simp [bor, toBitVec, Bit.Spec.bor]
theorem bxor_toBitVec (x y : UInt32) :
    (bxor x y).toBitVec = Bit.Spec.bxor x.toBitVec y.toBitVec := by
  simp [bxor, toBitVec, Bit.Spec.bxor]
theorem bnot_toBitVec (x : UInt32) :
    (bnot x).toBitVec = Bit.Spec.bnot x.toBitVec := by
  simp [bnot, toBitVec, Bit.Spec.bnot]
end UInt32

namespace UInt64

theorem band_comm (x y : UInt64) : band x y = band y x := by
  unfold band; congr 1; bv_decide
theorem bor_comm (x y : UInt64) : bor x y = bor y x := by
  unfold bor; congr 1; bv_decide
theorem bxor_comm (x y : UInt64) : bxor x y = bxor y x := by
  unfold bxor; congr 1; bv_decide
theorem band_assoc (x y z : UInt64) : band (band x y) z = band x (band y z) := by
  unfold band; congr 1; bv_decide
theorem bor_assoc (x y z : UInt64) : bor (bor x y) z = bor x (bor y z) := by
  unfold bor; congr 1; bv_decide
theorem bxor_assoc (x y z : UInt64) : bxor (bxor x y) z = bxor x (bxor y z) := by
  unfold bxor; congr 1; bv_decide
theorem band_allOnes (x : UInt64) : band x ⟨18446744073709551615⟩ = x := by
  cases x; unfold band; congr 1; bv_decide
theorem bor_zero (x : UInt64) : bor x 0 = x := by
  show bor x ⟨0⟩ = x; cases x; unfold bor; congr 1; bv_decide
theorem bxor_zero (x : UInt64) : bxor x 0 = x := by
  show bxor x ⟨0⟩ = x; cases x; unfold bxor; congr 1; bv_decide
theorem band_zero (x : UInt64) : band x 0 = 0 := by
  show band x ⟨0⟩ = ⟨0⟩; cases x; unfold band; congr 1; bv_decide
theorem bor_allOnes (x : UInt64) : bor x ⟨18446744073709551615⟩ = ⟨18446744073709551615⟩ := by
  cases x; unfold bor; congr 1; bv_decide
theorem bxor_self (x : UInt64) : bxor x x = 0 := by
  show bxor x x = ⟨0⟩; cases x; unfold bxor; congr 1; bv_decide
theorem bnot_bnot (x : UInt64) : bnot (bnot x) = x := by
  cases x; unfold bnot; congr 1; bv_decide
theorem demorgan_and (x y : UInt64) : bnot (band x y) = bor (bnot x) (bnot y) := by
  unfold bnot band bor; congr 1; bv_decide
theorem demorgan_or (x y : UInt64) : bnot (bor x y) = band (bnot x) (bnot y) := by
  unfold bnot bor band; congr 1; bv_decide
theorem shl_zero (x : UInt64) : shl x 0 = x := by
  show shl x ⟨0⟩ = x; cases x; simp [shl, fromBitVec, toBitVec]
theorem shrLogical_zero (x : UInt64) : shrLogical x 0 = x := by
  show shrLogical x ⟨0⟩ = x; cases x; simp [shrLogical, fromBitVec, toBitVec]
theorem band_toBitVec (x y : UInt64) :
    (band x y).toBitVec = Bit.Spec.band x.toBitVec y.toBitVec := by
  simp [band, toBitVec, Bit.Spec.band]
theorem bor_toBitVec (x y : UInt64) :
    (bor x y).toBitVec = Bit.Spec.bor x.toBitVec y.toBitVec := by
  simp [bor, toBitVec, Bit.Spec.bor]
theorem bxor_toBitVec (x y : UInt64) :
    (bxor x y).toBitVec = Bit.Spec.bxor x.toBitVec y.toBitVec := by
  simp [bxor, toBitVec, Bit.Spec.bxor]
theorem bnot_toBitVec (x : UInt64) :
    (bnot x).toBitVec = Bit.Spec.bnot x.toBitVec := by
  simp [bnot, toBitVec, Bit.Spec.bnot]
end UInt64

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (UInt8)                        -/
/-! ================================================================ -/

namespace UInt8

/-- Setting a bit then testing it returns true (within bounds). -/
theorem testBit_setBit (x : UInt8) (idx : Nat) (h : idx < 8) :
    testBit (setBit x idx) idx = true := by
  unfold testBit setBit
  simp only [h, ↓reduceIte, UInt8.toBitVec_fromBitVec]
  rw [BitVec.getLsbD_or]
  simp [h]

/-- Clearing a bit then testing it returns false (within bounds). -/
theorem testBit_clearBit (x : UInt8) (idx : Nat) (h : idx < 8) :
    testBit (clearBit x idx) idx = false := by
  unfold testBit clearBit
  simp only [h, ↓reduceIte, UInt8.toBitVec_fromBitVec]
  rw [BitVec.getLsbD_and]
  simp [h]

/-- Double toggle is identity. -/
theorem toggleBit_toggleBit (x : UInt8) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  unfold toggleBit
  split
  · next _ =>
    simp only [UInt8.toBitVec_fromBitVec,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact UInt8.fromBitVec_toBitVec x
  · next h => simp_all

end UInt8

end Radix
