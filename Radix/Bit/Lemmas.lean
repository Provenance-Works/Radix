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
/-! ## Bit Scanning Properties (UInt8)                                -/
/-! ================================================================ -/

namespace UInt8

/-- `clz 0 = 8`: all bits are zero, so all 8 leading positions are zero. -/
theorem clz_zero : clz (0 : UInt8) = ⟨8⟩ := by decide

/-- `ctz 0 = 8`: all bits are zero, so all 8 trailing positions are zero. -/
theorem ctz_zero : ctz (0 : UInt8) = ⟨8⟩ := by decide

/-- `popcount 0 = 0`: no bits are set. -/
theorem popcount_zero : popcount (0 : UInt8) = 0 := by decide

/-- `popcount allOnes = 8`: all bits are set. -/
theorem popcount_allOnes : popcount (⟨255⟩ : UInt8) = ⟨8⟩ := by decide

/-- `popcount (bxor x y)` equals the Hamming distance (FR-002.3). -/
theorem popcount_bxor (x y : UInt8) :
    popcount (bxor x y) = hammingDistance x y := rfl

/-- Hamming distance is commutative. -/
theorem hammingDistance_comm (x y : UInt8) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  congr 1; congr 1; bv_decide

end UInt8

/-! ================================================================ -/
/-! ## Bit Scanning Properties (UInt16)                               -/
/-! ================================================================ -/

namespace UInt16

theorem clz_zero : clz (0 : UInt16) = ⟨16⟩ := by decide
theorem ctz_zero : ctz (0 : UInt16) = ⟨16⟩ := by decide
theorem popcount_zero : popcount (0 : UInt16) = 0 := by decide
theorem popcount_allOnes : popcount (⟨65535⟩ : UInt16) = ⟨16⟩ := by decide

theorem popcount_bxor (x y : UInt16) :
    popcount (bxor x y) = hammingDistance x y := rfl

theorem hammingDistance_comm (x y : UInt16) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  congr 1; congr 1; bv_decide

end UInt16

/-! ================================================================ -/
/-! ## Bit Scanning Properties (UInt32)                               -/
/-! ================================================================ -/

namespace UInt32

theorem clz_zero : clz (0 : UInt32) = ⟨32⟩ := by decide
theorem ctz_zero : ctz (0 : UInt32) = ⟨32⟩ := by decide
theorem popcount_zero : popcount (0 : UInt32) = 0 := by decide
theorem popcount_allOnes : popcount (⟨4294967295⟩ : UInt32) = ⟨32⟩ := by decide

theorem popcount_bxor (x y : UInt32) :
    popcount (bxor x y) = hammingDistance x y := rfl

theorem hammingDistance_comm (x y : UInt32) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  congr 1; congr 1; bv_decide

end UInt32

/-! ================================================================ -/
/-! ## Bit Scanning Properties (UInt64)                               -/
/-! ================================================================ -/

namespace UInt64

theorem clz_zero : clz (0 : UInt64) = ⟨64⟩ := by decide
theorem ctz_zero : ctz (0 : UInt64) = ⟨64⟩ := by decide
theorem popcount_zero : popcount (0 : UInt64) = 0 := by decide
theorem popcount_allOnes : popcount (⟨18446744073709551615⟩ : UInt64) = ⟨64⟩ := by decide

theorem popcount_bxor (x y : UInt64) :
    popcount (bxor x y) = hammingDistance x y := rfl

theorem hammingDistance_comm (x y : UInt64) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  congr 1; congr 1; bv_decide

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

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (UInt16)                       -/
/-! ================================================================ -/

namespace UInt16

@[simp] private theorem toBitVec_fromBitVec_16 (bv : BitVec 16) :
    UInt16.toBitVec (UInt16.fromBitVec bv) = bv := by
  simp [UInt16.fromBitVec, UInt16.toBitVec]

@[simp] private theorem fromBitVec_toBitVec_16 (x : UInt16) :
    UInt16.fromBitVec (UInt16.toBitVec x) = x := by
  cases x; simp [UInt16.fromBitVec, UInt16.toBitVec]

theorem testBit_setBit (x : UInt16) (idx : Nat) (h : idx < 16) :
    testBit (setBit x idx) idx = true := by
  unfold testBit setBit
  simp only [h, ↓reduceIte, toBitVec_fromBitVec_16]
  rw [BitVec.getLsbD_or]
  simp [h]

theorem testBit_clearBit (x : UInt16) (idx : Nat) (h : idx < 16) :
    testBit (clearBit x idx) idx = false := by
  unfold testBit clearBit
  simp only [h, ↓reduceIte, toBitVec_fromBitVec_16]
  rw [BitVec.getLsbD_and]
  simp [h]

theorem toggleBit_toggleBit (x : UInt16) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  unfold toggleBit
  split
  · next _ =>
    simp only [toBitVec_fromBitVec_16,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact fromBitVec_toBitVec_16 x
  · next h => simp_all

end UInt16

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (UInt32)                       -/
/-! ================================================================ -/

namespace UInt32

@[simp] private theorem toBitVec_fromBitVec_32 (bv : BitVec 32) :
    UInt32.toBitVec (UInt32.fromBitVec bv) = bv := by
  simp [UInt32.fromBitVec, UInt32.toBitVec]

@[simp] private theorem fromBitVec_toBitVec_32 (x : UInt32) :
    UInt32.fromBitVec (UInt32.toBitVec x) = x := by
  cases x; simp [UInt32.fromBitVec, UInt32.toBitVec]

theorem testBit_setBit (x : UInt32) (idx : Nat) (h : idx < 32) :
    testBit (setBit x idx) idx = true := by
  unfold testBit setBit
  simp only [h, ↓reduceIte, toBitVec_fromBitVec_32]
  rw [BitVec.getLsbD_or]
  simp [h]

theorem testBit_clearBit (x : UInt32) (idx : Nat) (h : idx < 32) :
    testBit (clearBit x idx) idx = false := by
  unfold testBit clearBit
  simp only [h, ↓reduceIte, toBitVec_fromBitVec_32]
  rw [BitVec.getLsbD_and]
  simp [h]

theorem toggleBit_toggleBit (x : UInt32) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  unfold toggleBit
  split
  · next _ =>
    simp only [toBitVec_fromBitVec_32,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact fromBitVec_toBitVec_32 x
  · next h => simp_all

end UInt32

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (UInt64)                       -/
/-! ================================================================ -/

namespace UInt64

@[simp] private theorem toBitVec_fromBitVec_64 (bv : BitVec 64) :
    UInt64.toBitVec (UInt64.fromBitVec bv) = bv := by
  simp [UInt64.fromBitVec, UInt64.toBitVec]

@[simp] private theorem fromBitVec_toBitVec_64 (x : UInt64) :
    UInt64.fromBitVec (UInt64.toBitVec x) = x := by
  cases x; simp [UInt64.fromBitVec, UInt64.toBitVec]

theorem testBit_setBit (x : UInt64) (idx : Nat) (h : idx < 64) :
    testBit (setBit x idx) idx = true := by
  unfold testBit setBit
  simp only [h, ↓reduceIte, toBitVec_fromBitVec_64]
  rw [BitVec.getLsbD_or]
  simp [h]

theorem testBit_clearBit (x : UInt64) (idx : Nat) (h : idx < 64) :
    testBit (clearBit x idx) idx = false := by
  unfold testBit clearBit
  simp only [h, ↓reduceIte, toBitVec_fromBitVec_64]
  rw [BitVec.getLsbD_and]
  simp [h]

theorem toggleBit_toggleBit (x : UInt64) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  unfold toggleBit
  split
  · next _ =>
    simp only [toBitVec_fromBitVec_64,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact fromBitVec_toBitVec_64 x
  · next h => simp_all

end UInt64

/-! ================================================================ -/
/-! ## Int8 Boolean Algebra                                           -/
/-! ================================================================ -/

namespace Int8

theorem band_comm (x y : Int8) : band x y = band y x := by
  unfold band; congr 1; bv_decide
theorem bor_comm (x y : Int8) : bor x y = bor y x := by
  unfold bor; congr 1; bv_decide
theorem bxor_comm (x y : Int8) : bxor x y = bxor y x := by
  unfold bxor; congr 1; bv_decide

theorem band_assoc (x y z : Int8) : band (band x y) z = band x (band y z) := by
  unfold band; congr 1; bv_decide
theorem bor_assoc (x y z : Int8) : bor (bor x y) z = bor x (bor y z) := by
  unfold bor; congr 1; bv_decide
theorem bxor_assoc (x y z : Int8) : bxor (bxor x y) z = bxor x (bxor y z) := by
  unfold bxor; congr 1; bv_decide

theorem bxor_self (x : Int8) : bxor x x = ⟨0⟩ := by
  cases x; unfold bxor; congr 1; bv_decide
theorem bnot_bnot (x : Int8) : bnot (bnot x) = x := by
  cases x; unfold bnot; congr 1; bv_decide

theorem demorgan_and (x y : Int8) : bnot (band x y) = bor (bnot x) (bnot y) := by
  unfold bnot band bor; congr 1; bv_decide
theorem demorgan_or (x y : Int8) : bnot (bor x y) = band (bnot x) (bnot y) := by
  unfold bnot bor band; congr 1; bv_decide

end Int8

/-! ================================================================ -/
/-! ## Int16 Boolean Algebra                                          -/
/-! ================================================================ -/

namespace Int16

theorem band_comm (x y : Int16) : band x y = band y x := by
  unfold band; congr 1; bv_decide
theorem bor_comm (x y : Int16) : bor x y = bor y x := by
  unfold bor; congr 1; bv_decide
theorem bxor_comm (x y : Int16) : bxor x y = bxor y x := by
  unfold bxor; congr 1; bv_decide

theorem band_assoc (x y z : Int16) : band (band x y) z = band x (band y z) := by
  unfold band; congr 1; bv_decide
theorem bor_assoc (x y z : Int16) : bor (bor x y) z = bor x (bor y z) := by
  unfold bor; congr 1; bv_decide
theorem bxor_assoc (x y z : Int16) : bxor (bxor x y) z = bxor x (bxor y z) := by
  unfold bxor; congr 1; bv_decide

theorem bxor_self (x : Int16) : bxor x x = ⟨0⟩ := by
  cases x; unfold bxor; congr 1; bv_decide
theorem bnot_bnot (x : Int16) : bnot (bnot x) = x := by
  cases x; unfold bnot; congr 1; bv_decide

theorem demorgan_and (x y : Int16) : bnot (band x y) = bor (bnot x) (bnot y) := by
  unfold bnot band bor; congr 1; bv_decide
theorem demorgan_or (x y : Int16) : bnot (bor x y) = band (bnot x) (bnot y) := by
  unfold bnot bor band; congr 1; bv_decide

end Int16

/-! ================================================================ -/
/-! ## Int32 Boolean Algebra                                          -/
/-! ================================================================ -/

namespace Int32

theorem band_comm (x y : Int32) : band x y = band y x := by
  unfold band; congr 1; bv_decide
theorem bor_comm (x y : Int32) : bor x y = bor y x := by
  unfold bor; congr 1; bv_decide
theorem bxor_comm (x y : Int32) : bxor x y = bxor y x := by
  unfold bxor; congr 1; bv_decide

theorem band_assoc (x y z : Int32) : band (band x y) z = band x (band y z) := by
  unfold band; congr 1; bv_decide
theorem bor_assoc (x y z : Int32) : bor (bor x y) z = bor x (bor y z) := by
  unfold bor; congr 1; bv_decide
theorem bxor_assoc (x y z : Int32) : bxor (bxor x y) z = bxor x (bxor y z) := by
  unfold bxor; congr 1; bv_decide

theorem bxor_self (x : Int32) : bxor x x = ⟨0⟩ := by
  cases x; unfold bxor; congr 1; bv_decide
theorem bnot_bnot (x : Int32) : bnot (bnot x) = x := by
  cases x; unfold bnot; congr 1; bv_decide

theorem demorgan_and (x y : Int32) : bnot (band x y) = bor (bnot x) (bnot y) := by
  unfold bnot band bor; congr 1; bv_decide
theorem demorgan_or (x y : Int32) : bnot (bor x y) = band (bnot x) (bnot y) := by
  unfold bnot bor band; congr 1; bv_decide

end Int32

/-! ================================================================ -/
/-! ## Int64 Boolean Algebra                                          -/
/-! ================================================================ -/

namespace Int64

theorem band_comm (x y : Int64) : band x y = band y x := by
  unfold band; congr 1; bv_decide
theorem bor_comm (x y : Int64) : bor x y = bor y x := by
  unfold bor; congr 1; bv_decide
theorem bxor_comm (x y : Int64) : bxor x y = bxor y x := by
  unfold bxor; congr 1; bv_decide

theorem band_assoc (x y z : Int64) : band (band x y) z = band x (band y z) := by
  unfold band; congr 1; bv_decide
theorem bor_assoc (x y z : Int64) : bor (bor x y) z = bor x (bor y z) := by
  unfold bor; congr 1; bv_decide
theorem bxor_assoc (x y z : Int64) : bxor (bxor x y) z = bxor x (bxor y z) := by
  unfold bxor; congr 1; bv_decide

theorem bxor_self (x : Int64) : bxor x x = ⟨0⟩ := by
  cases x; unfold bxor; congr 1; bv_decide
theorem bnot_bnot (x : Int64) : bnot (bnot x) = x := by
  cases x; unfold bnot; congr 1; bv_decide

theorem demorgan_and (x y : Int64) : bnot (band x y) = bor (bnot x) (bnot y) := by
  unfold bnot band bor; congr 1; bv_decide
theorem demorgan_or (x y : Int64) : bnot (bor x y) = band (bnot x) (bnot y) := by
  unfold bnot bor band; congr 1; bv_decide

end Int64

/-! ================================================================ -/
/-! ## UWord Boolean Algebra                                          -/
/-! ================================================================ -/

namespace UWord

variable {w : Nat} [PlatformWidth w]

theorem band_comm (x y : UWord w) : band x y = band y x := by
  simp [band, BitVec.and_comm]

theorem bor_comm (x y : UWord w) : bor x y = bor y x := by
  simp [bor, BitVec.or_comm]

theorem bxor_comm (x y : UWord w) : bxor x y = bxor y x := by
  simp [bxor, BitVec.xor_comm]

theorem band_assoc (x y z : UWord w) : band (band x y) z = band x (band y z) := by
  simp [band, BitVec.and_assoc]

theorem bor_assoc (x y z : UWord w) : bor (bor x y) z = bor x (bor y z) := by
  simp [bor, BitVec.or_assoc]

theorem bxor_assoc (x y z : UWord w) : bxor (bxor x y) z = bxor x (bxor y z) := by
  simp [bxor, BitVec.xor_assoc]

theorem bxor_self (x : UWord w) : bxor x x = ⟨0⟩ := by
  simp [bxor, BitVec.xor_self]

theorem bnot_bnot (x : UWord w) : bnot (bnot x) = x := by
  cases x; simp [bnot]

end UWord

/-! ================================================================ -/
/-! ## IWord Boolean Algebra                                          -/
/-! ================================================================ -/

namespace IWord

variable {w : Nat} [PlatformWidth w]

theorem band_comm (x y : IWord w) : band x y = band y x := by
  simp [band, BitVec.and_comm]

theorem bor_comm (x y : IWord w) : bor x y = bor y x := by
  simp [bor, BitVec.or_comm]

theorem bxor_comm (x y : IWord w) : bxor x y = bxor y x := by
  simp [bxor, BitVec.xor_comm]

theorem band_assoc (x y z : IWord w) : band (band x y) z = band x (band y z) := by
  simp [band, BitVec.and_assoc]

theorem bor_assoc (x y z : IWord w) : bor (bor x y) z = bor x (bor y z) := by
  simp [bor, BitVec.or_assoc]

theorem bxor_assoc (x y z : IWord w) : bxor (bxor x y) z = bxor x (bxor y z) := by
  simp [bxor, BitVec.xor_assoc]

theorem bxor_self (x : IWord w) : bxor x x = ⟨0⟩ := by
  simp [bxor, BitVec.xor_self]

theorem bnot_bnot (x : IWord w) : bnot (bnot x) = x := by
  cases x; simp [bnot]

end IWord

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (Int8)                         -/
/-! ================================================================ -/

namespace Int8

theorem toggleBit_toggleBit (x : Int8) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  simp only [toggleBit, UInt8.toggleBit, UInt8.toBitVec, UInt8.fromBitVec,
             Int8.fromBitVec]
  split <;> simp_all [BitVec.xor_assoc]

end Int8

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (Int16)                        -/
/-! ================================================================ -/

namespace Int16

theorem toggleBit_toggleBit (x : Int16) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  simp only [toggleBit, UInt16.toggleBit, UInt16.toBitVec, UInt16.fromBitVec,
             Int16.fromBitVec]
  split <;> simp_all [BitVec.xor_assoc]

end Int16

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (Int32)                        -/
/-! ================================================================ -/

namespace Int32

theorem toggleBit_toggleBit (x : Int32) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  simp only [toggleBit, UInt32.toggleBit, UInt32.toBitVec, UInt32.fromBitVec,
             Int32.fromBitVec]
  split <;> simp_all [BitVec.xor_assoc]

end Int32

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (Int64)                        -/
/-! ================================================================ -/

namespace Int64

theorem toggleBit_toggleBit (x : Int64) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  simp only [toggleBit, UInt64.toggleBit, UInt64.toBitVec, UInt64.fromBitVec,
             Int64.fromBitVec]
  split <;> simp_all [BitVec.xor_assoc]

end Int64

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (UWord)                        -/
/-! ================================================================ -/

namespace UWord

variable {w : Nat} [PlatformWidth w]

theorem testBit_setBit (x : UWord w) (idx : Nat) (h : idx < w) :
    testBit (setBit x idx) idx = true := by
  unfold testBit setBit
  simp only [h, ↓reduceIte]
  rw [BitVec.getLsbD_or]
  simp [h]

theorem testBit_clearBit (x : UWord w) (idx : Nat) (h : idx < w) :
    testBit (clearBit x idx) idx = false := by
  unfold testBit clearBit
  simp only [h, ↓reduceIte]
  rw [BitVec.getLsbD_and]
  simp [h]

theorem toggleBit_toggleBit (x : UWord w) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  unfold toggleBit
  split
  · next _ =>
    simp [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · next h => simp_all

end UWord

/-! ================================================================ -/
/-! ## Bit Field Round-Trip Properties (IWord)                        -/
/-! ================================================================ -/

namespace IWord

variable {w : Nat} [PlatformWidth w]

theorem testBit_setBit (x : IWord w) (idx : Nat) (h : idx < w) :
    testBit (setBit x idx) idx = true := by
  unfold testBit setBit
  simp only [h, ↓reduceIte]
  rw [BitVec.getLsbD_or]
  simp [h]

theorem testBit_clearBit (x : IWord w) (idx : Nat) (h : idx < w) :
    testBit (clearBit x idx) idx = false := by
  unfold testBit clearBit
  simp only [h, ↓reduceIte]
  rw [BitVec.getLsbD_and]
  simp [h]

theorem toggleBit_toggleBit (x : IWord w) (idx : Nat) :
    toggleBit (toggleBit x idx) idx = x := by
  unfold toggleBit
  split
  · next _ =>
    simp [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · next h => simp_all

end IWord

/-! ================================================================ -/
/-! ## Shift/Rotate Spec Equivalence (UInt8)                          -/
/-! ================================================================ -/

namespace UInt8

/-- `shl` matches the Layer 3 specification for any shift count. -/
theorem shl_toBitVec (x count : UInt8) :
    (shl x count).toBitVec = Bit.Spec.shl x.toBitVec (count.val.toNat) := by
  unfold shl Bit.Spec.shl; simp

/-- `shrLogical` matches the Layer 3 specification. -/
theorem shrLogical_toBitVec (x count : UInt8) :
    (shrLogical x count).toBitVec = Bit.Spec.shrLogical x.toBitVec (count.val.toNat) := by
  unfold shrLogical Bit.Spec.shrLogical; simp

/-- `shrArith` matches the Layer 3 specification. -/
theorem shrArith_toBitVec (x count : UInt8) :
    (shrArith x count).toBitVec = Bit.Spec.shrArith x.toBitVec (count.val.toNat) := by
  unfold shrArith Bit.Spec.shrArith; simp

end UInt8

/-! ================================================================ -/
/-! ## Shift/Rotate Spec Equivalence (UInt16)                         -/
/-! ================================================================ -/

namespace UInt16

theorem shl_toBitVec (x count : UInt16) :
    (shl x count).toBitVec = Bit.Spec.shl x.toBitVec (count.val.toNat) := by
  unfold shl Bit.Spec.shl; simp

theorem shrLogical_toBitVec (x count : UInt16) :
    (shrLogical x count).toBitVec = Bit.Spec.shrLogical x.toBitVec (count.val.toNat) := by
  unfold shrLogical Bit.Spec.shrLogical; simp

theorem shrArith_toBitVec (x count : UInt16) :
    (shrArith x count).toBitVec = Bit.Spec.shrArith x.toBitVec (count.val.toNat) := by
  unfold shrArith Bit.Spec.shrArith; simp

end UInt16

/-! ================================================================ -/
/-! ## Shift/Rotate Spec Equivalence (UInt32)                         -/
/-! ================================================================ -/

namespace UInt32

theorem shl_toBitVec (x count : UInt32) :
    (shl x count).toBitVec = Bit.Spec.shl x.toBitVec (count.val.toNat) := by
  unfold shl Bit.Spec.shl; simp

theorem shrLogical_toBitVec (x count : UInt32) :
    (shrLogical x count).toBitVec = Bit.Spec.shrLogical x.toBitVec (count.val.toNat) := by
  unfold shrLogical Bit.Spec.shrLogical; simp

theorem shrArith_toBitVec (x count : UInt32) :
    (shrArith x count).toBitVec = Bit.Spec.shrArith x.toBitVec (count.val.toNat) := by
  unfold shrArith Bit.Spec.shrArith; simp

end UInt32

/-! ================================================================ -/
/-! ## Shift/Rotate Spec Equivalence (UInt64)                         -/
/-! ================================================================ -/

namespace UInt64

theorem shl_toBitVec (x count : UInt64) :
    (shl x count).toBitVec = Bit.Spec.shl x.toBitVec (count.val.toNat) := by
  unfold shl Bit.Spec.shl; simp

theorem shrLogical_toBitVec (x count : UInt64) :
    (shrLogical x count).toBitVec = Bit.Spec.shrLogical x.toBitVec (count.val.toNat) := by
  unfold shrLogical Bit.Spec.shrLogical; simp

theorem shrArith_toBitVec (x count : UInt64) :
    (shrArith x count).toBitVec = Bit.Spec.shrArith x.toBitVec (count.val.toNat) := by
  unfold shrArith Bit.Spec.shrArith; simp

end UInt64

/-! ================================================================ -/
/-! ## Int8 Boolean Algebra: Identity/Annihilation/Spec              -/
/-! ================================================================ -/

namespace Int8

theorem band_allOnes (x : Int8) : band x ⟨255⟩ = x := by
  cases x; unfold band; congr 1; bv_decide
theorem bor_zero (x : Int8) : bor x 0 = x := by
  show bor x ⟨0⟩ = x; cases x; unfold bor; congr 1; bv_decide
theorem bxor_zero (x : Int8) : bxor x 0 = x := by
  show bxor x ⟨0⟩ = x; cases x; unfold bxor; congr 1; bv_decide
theorem band_zero (x : Int8) : band x 0 = 0 := by
  show band x ⟨0⟩ = ⟨0⟩; cases x; unfold band; congr 1; bv_decide
theorem bor_allOnes (x : Int8) : bor x ⟨255⟩ = ⟨255⟩ := by
  cases x; unfold bor; congr 1; bv_decide
theorem shl_zero (x : Int8) : shl x 0 = x := by
  show shl x ⟨0⟩ = x; cases x; simp [shl, fromBitVec, toBitVec]
theorem shrLogical_zero (x : Int8) : shrLogical x 0 = x := by
  show shrLogical x ⟨0⟩ = x; cases x; simp [shrLogical, fromBitVec, toBitVec]

end Int8

/-! ================================================================ -/
/-! ## Int16 Boolean Algebra: Identity/Annihilation/Spec             -/
/-! ================================================================ -/

namespace Int16

theorem band_allOnes (x : Int16) : band x ⟨65535⟩ = x := by
  cases x; unfold band; congr 1; bv_decide
theorem bor_zero (x : Int16) : bor x 0 = x := by
  show bor x ⟨0⟩ = x; cases x; unfold bor; congr 1; bv_decide
theorem bxor_zero (x : Int16) : bxor x 0 = x := by
  show bxor x ⟨0⟩ = x; cases x; unfold bxor; congr 1; bv_decide
theorem band_zero (x : Int16) : band x 0 = 0 := by
  show band x ⟨0⟩ = ⟨0⟩; cases x; unfold band; congr 1; bv_decide
theorem bor_allOnes (x : Int16) : bor x ⟨65535⟩ = ⟨65535⟩ := by
  cases x; unfold bor; congr 1; bv_decide
theorem shl_zero (x : Int16) : shl x 0 = x := by
  show shl x ⟨0⟩ = x; cases x; simp [shl, fromBitVec, toBitVec]
theorem shrLogical_zero (x : Int16) : shrLogical x 0 = x := by
  show shrLogical x ⟨0⟩ = x; cases x; simp [shrLogical, fromBitVec, toBitVec]

end Int16

/-! ================================================================ -/
/-! ## Int32 Boolean Algebra: Identity/Annihilation/Spec             -/
/-! ================================================================ -/

namespace Int32

theorem band_allOnes (x : Int32) : band x ⟨4294967295⟩ = x := by
  cases x; unfold band; congr 1; bv_decide
theorem bor_zero (x : Int32) : bor x 0 = x := by
  show bor x ⟨0⟩ = x; cases x; unfold bor; congr 1; bv_decide
theorem bxor_zero (x : Int32) : bxor x 0 = x := by
  show bxor x ⟨0⟩ = x; cases x; unfold bxor; congr 1; bv_decide
theorem band_zero (x : Int32) : band x 0 = 0 := by
  show band x ⟨0⟩ = ⟨0⟩; cases x; unfold band; congr 1; bv_decide
theorem bor_allOnes (x : Int32) : bor x ⟨4294967295⟩ = ⟨4294967295⟩ := by
  cases x; unfold bor; congr 1; bv_decide
theorem shl_zero (x : Int32) : shl x 0 = x := by
  show shl x ⟨0⟩ = x; cases x; simp [shl, fromBitVec, toBitVec]
theorem shrLogical_zero (x : Int32) : shrLogical x 0 = x := by
  show shrLogical x ⟨0⟩ = x; cases x; simp [shrLogical, fromBitVec, toBitVec]

end Int32

/-! ================================================================ -/
/-! ## Int64 Boolean Algebra: Identity/Annihilation/Spec             -/
/-! ================================================================ -/

namespace Int64

theorem band_allOnes (x : Int64) : band x ⟨18446744073709551615⟩ = x := by
  cases x; unfold band; congr 1; bv_decide
theorem bor_zero (x : Int64) : bor x 0 = x := by
  show bor x ⟨0⟩ = x; cases x; unfold bor; congr 1; bv_decide
theorem bxor_zero (x : Int64) : bxor x 0 = x := by
  show bxor x ⟨0⟩ = x; cases x; unfold bxor; congr 1; bv_decide
theorem band_zero (x : Int64) : band x 0 = 0 := by
  show band x ⟨0⟩ = ⟨0⟩; cases x; unfold band; congr 1; bv_decide
theorem bor_allOnes (x : Int64) : bor x ⟨18446744073709551615⟩ = ⟨18446744073709551615⟩ := by
  cases x; unfold bor; congr 1; bv_decide
theorem shl_zero (x : Int64) : shl x 0 = x := by
  show shl x ⟨0⟩ = x; cases x; simp [shl, fromBitVec, toBitVec]
theorem shrLogical_zero (x : Int64) : shrLogical x 0 = x := by
  show shrLogical x ⟨0⟩ = x; cases x; simp [shrLogical, fromBitVec, toBitVec]

end Int64

/-! ================================================================ -/
/-! ## UWord Boolean Algebra: Identity/Annihilation/De Morgan/Spec   -/
/-! ================================================================ -/

namespace UWord

variable {w : Nat} [PlatformWidth w]

theorem bor_zero (x : UWord w) : bor x ⟨0⟩ = x := by
  simp [bor, BitVec.or_zero]

theorem bxor_zero (x : UWord w) : bxor x ⟨0⟩ = x := by
  simp [bxor, BitVec.xor_zero]

theorem band_zero (x : UWord w) : band x ⟨0⟩ = ⟨0⟩ := by
  simp [band, BitVec.and_zero]

theorem shl_zero (x : UWord w) : shl x ⟨0⟩ = x := by
  simp [shl]

theorem shrLogical_zero (x : UWord w) : shrLogical x ⟨0⟩ = x := by
  simp [shrLogical]

theorem demorgan_and (x y : UWord w) : bnot (band x y) = bor (bnot x) (bnot y) := by
  simp [bnot, band, bor]
  ext i
  simp

theorem demorgan_or (x y : UWord w) : bnot (bor x y) = band (bnot x) (bnot y) := by
  simp [bnot, bor, band]
  ext i
  simp

end UWord

/-! ================================================================ -/
/-! ## IWord Boolean Algebra: Identity/Annihilation/De Morgan/Spec   -/
/-! ================================================================ -/

namespace IWord

variable {w : Nat} [PlatformWidth w]

theorem bor_zero (x : IWord w) : bor x ⟨0⟩ = x := by
  simp [bor, BitVec.or_zero]

theorem bxor_zero (x : IWord w) : bxor x ⟨0⟩ = x := by
  simp [bxor, BitVec.xor_zero]

theorem band_zero (x : IWord w) : band x ⟨0⟩ = ⟨0⟩ := by
  simp [band, BitVec.and_zero]

theorem shl_zero (x : IWord w) : shl x ⟨0⟩ = x := by
  simp [shl]

theorem shrLogical_zero (x : IWord w) : shrLogical x ⟨0⟩ = x := by
  simp [shrLogical]

theorem demorgan_and (x y : IWord w) : bnot (band x y) = bor (bnot x) (bnot y) := by
  simp [bnot, band, bor]
  ext i
  simp

theorem demorgan_or (x y : IWord w) : bnot (bor x y) = band (bnot x) (bnot y) := by
  simp [bnot, bor, band]
  ext i
  simp

end IWord

/-! ================================================================ -/
/-! ## Bit Scanning Properties (Int8-64)                              -/
/-! ================================================================ -/

namespace Int8
theorem clz_zero : clz (0 : Int8) = ⟨8⟩ := by decide
theorem ctz_zero : ctz (0 : Int8) = ⟨8⟩ := by decide
theorem popcount_zero : popcount (0 : Int8) = 0 := by decide
theorem popcount_bxor (x y : Int8) :
    popcount (bxor x y) = hammingDistance x y := rfl
theorem hammingDistance_comm (x y : Int8) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  congr 1; congr 1; bv_decide
end Int8

namespace Int16
theorem clz_zero : clz (0 : Int16) = ⟨16⟩ := by decide
theorem ctz_zero : ctz (0 : Int16) = ⟨16⟩ := by decide
theorem popcount_zero : popcount (0 : Int16) = 0 := by decide
theorem popcount_bxor (x y : Int16) :
    popcount (bxor x y) = hammingDistance x y := rfl
theorem hammingDistance_comm (x y : Int16) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  congr 1; congr 1; bv_decide
end Int16

namespace Int32
theorem clz_zero : clz (0 : Int32) = ⟨32⟩ := by decide
theorem ctz_zero : ctz (0 : Int32) = ⟨32⟩ := by decide
theorem popcount_zero : popcount (0 : Int32) = 0 := by decide
theorem popcount_bxor (x y : Int32) :
    popcount (bxor x y) = hammingDistance x y := rfl
theorem hammingDistance_comm (x y : Int32) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  congr 1; congr 1; bv_decide
end Int32

namespace Int64
theorem clz_zero : clz (0 : Int64) = ⟨64⟩ := by decide
theorem ctz_zero : ctz (0 : Int64) = ⟨64⟩ := by decide
theorem popcount_zero : popcount (0 : Int64) = 0 := by decide
theorem popcount_bxor (x y : Int64) :
    popcount (bxor x y) = hammingDistance x y := rfl
theorem hammingDistance_comm (x y : Int64) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  congr 1; congr 1; bv_decide
end Int64

/-! ================================================================ -/
/-! ## Hamming Distance Properties (UWord / IWord)                    -/
/-! ================================================================ -/

namespace UWord
variable {w : Nat} [PlatformWidth w]

theorem popcount_bxor (x y : UWord w) :
    popcount (bxor x y) = hammingDistance x y := rfl

theorem hammingDistance_comm (x y : UWord w) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  have h : x.val ^^^ y.val = y.val ^^^ x.val := by
    ext i; simp [Bool.xor_comm]
  rw [h]

end UWord

namespace IWord
variable {w : Nat} [PlatformWidth w]

theorem popcount_bxor (x y : IWord w) :
    popcount (bxor x y) = hammingDistance x y := rfl

theorem hammingDistance_comm (x y : IWord w) :
    hammingDistance x y = hammingDistance y x := by
  show popcount ⟨x.val ^^^ y.val⟩ = popcount ⟨y.val ^^^ x.val⟩
  have h : x.val ^^^ y.val = y.val ^^^ x.val := by
    ext i; simp [Bool.xor_comm]
  rw [h]

end IWord

end Radix
