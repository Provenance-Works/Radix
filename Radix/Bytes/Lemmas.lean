/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Bytes.Order
import Radix.Bytes.Slice

/-!
# Byte Operation Proofs (Layer 3)

This module contains proofs for:
- Byte-swap involution: `bswap (bswap x) = x`
- Big-endian round-trip: `fromBigEndian (toBigEndian x) = x`
- Little-endian round-trip: `fromLittleEndian (toLittleEndian x) = x`
- BE/LE relationships

## Architecture

This is a **Layer 3 (Verified Specification)** module containing proofs.

## References

- FR-003.2: Proofs (round-trip, involution)
- FR-004.4: Slice bounds are always valid
-/

namespace Radix

/-! ## BitVec-level bswap mirrors

We define pure `BitVec → BitVec` functions that mirror the exact structure of
the `Radix.UIntN.bswap` implementations. Because the definitions are
definitionally equal once we project through `.val.toBitVec`, we can prove
the bswap involution at the BitVec level using `bv_decide`, then lift the
result back to the wrapper types. -/

private def bswap16_bv (bv : BitVec 16) : BitVec 16 :=
  let lo := (bv >>> 8) &&& 0xFF
  let hi := (bv &&& 0xFF) <<< 8
  hi ||| lo

private def bswap32_bv (bv : BitVec 32) : BitVec 32 :=
  let b0 := (bv >>> 24) &&& 0xFF
  let b1 := (bv >>> 16) &&& 0xFF
  let b2 := (bv >>> 8) &&& 0xFF
  let b3 := bv &&& 0xFF
  (b3 <<< 24 ||| b2 <<< 16) ||| (b1 <<< 8 ||| b0)

private def bswap64_bv (bv : BitVec 64) : BitVec 64 :=
  let b0 := (bv >>> 56) &&& 0xFF
  let b1 := (bv >>> 48) &&& 0xFF
  let b2 := (bv >>> 40) &&& 0xFF
  let b3 := (bv >>> 32) &&& 0xFF
  let b4 := (bv >>> 24) &&& 0xFF
  let b5 := (bv >>> 16) &&& 0xFF
  let b6 := (bv >>> 8) &&& 0xFF
  let b7 := bv &&& 0xFF
  (b7 <<< 56 ||| b6 <<< 48) |||
    ((b5 <<< 40 ||| b4 <<< 32) |||
      ((b3 <<< 24 ||| b2 <<< 16) |||
        (b1 <<< 8 ||| b0)))

/-! ## Lifting lemmas (all definitional) -/

private theorem bswap16_eq (x : UInt16) :
    UInt16.bswap x = UInt16.fromBitVec (bswap16_bv x.val.toBitVec) := rfl

private theorem bswap32_eq (x : UInt32) :
    UInt32.bswap x = UInt32.fromBitVec (bswap32_bv x.val.toBitVec) := rfl

private theorem bswap64_eq (x : UInt64) :
    UInt64.bswap x = UInt64.fromBitVec (bswap64_bv x.val.toBitVec) := rfl

private theorem fromBitVec16_roundtrip (bv : BitVec 16) :
    (UInt16.fromBitVec bv).val.toBitVec = bv := rfl

private theorem fromBitVec32_roundtrip (bv : BitVec 32) :
    (UInt32.fromBitVec bv).val.toBitVec = bv := rfl

private theorem fromBitVec64_roundtrip (bv : BitVec 64) :
    (UInt64.fromBitVec bv).val.toBitVec = bv := rfl

/-! ## BitVec-level involution (proven by bv_decide) -/

private theorem bswap16_bv_invol (bv : BitVec 16) :
    bswap16_bv (bswap16_bv bv) = bv := by
  unfold bswap16_bv; bv_decide

private theorem bswap32_bv_invol (bv : BitVec 32) :
    bswap32_bv (bswap32_bv bv) = bv := by
  unfold bswap32_bv; bv_decide

private theorem bswap64_bv_invol (bv : BitVec 64) :
    bswap64_bv (bswap64_bv bv) = bv := by
  unfold bswap64_bv; bv_decide

/-! ## UInt16 Byte Swap Involution -/

theorem UInt16.bswap_bswap (x : UInt16) : UInt16.bswap (UInt16.bswap x) = x := by
  rw [bswap16_eq, bswap16_eq]
  simp only [fromBitVec16_roundtrip, bswap16_bv_invol]
  cases x with | mk val => cases val with | ofBitVec bv => rfl

/-! ## UInt16 Endian Round-Trips -/

theorem UInt16.toBigEndian_fromBigEndian (x : UInt16) :
    UInt16.fromBigEndian (UInt16.toBigEndian x) = x := by
  simp [UInt16.toBigEndian, UInt16.fromBigEndian, nativeEndian]
  exact UInt16.bswap_bswap x

theorem UInt16.toLittleEndian_fromLittleEndian (x : UInt16) :
    UInt16.fromLittleEndian (UInt16.toLittleEndian x) = x := by
  simp [UInt16.toLittleEndian, UInt16.fromLittleEndian, nativeEndian]

/-! ## UInt32 Byte Swap Involution -/

theorem UInt32.bswap_bswap (x : UInt32) : UInt32.bswap (UInt32.bswap x) = x := by
  rw [bswap32_eq, bswap32_eq]
  simp only [fromBitVec32_roundtrip, bswap32_bv_invol]
  cases x with | mk val => cases val with | ofBitVec bv => rfl

/-! ## UInt32 Endian Round-Trips -/

theorem UInt32.toBigEndian_fromBigEndian (x : UInt32) :
    UInt32.fromBigEndian (UInt32.toBigEndian x) = x := by
  simp [UInt32.toBigEndian, UInt32.fromBigEndian, nativeEndian]
  exact UInt32.bswap_bswap x

theorem UInt32.toLittleEndian_fromLittleEndian (x : UInt32) :
    UInt32.fromLittleEndian (UInt32.toLittleEndian x) = x := by
  simp [UInt32.toLittleEndian, UInt32.fromLittleEndian, nativeEndian]

/-! ## UInt64 Byte Swap Involution -/

theorem UInt64.bswap_bswap (x : UInt64) : UInt64.bswap (UInt64.bswap x) = x := by
  rw [bswap64_eq, bswap64_eq]
  simp only [fromBitVec64_roundtrip, bswap64_bv_invol]
  cases x with | mk val => cases val with | ofBitVec bv => rfl

/-! ## UInt64 Endian Round-Trips -/

theorem UInt64.toBigEndian_fromBigEndian (x : UInt64) :
    UInt64.fromBigEndian (UInt64.toBigEndian x) = x := by
  simp [UInt64.toBigEndian, UInt64.fromBigEndian, nativeEndian]
  exact UInt64.bswap_bswap x

theorem UInt64.toLittleEndian_fromLittleEndian (x : UInt64) :
    UInt64.fromLittleEndian (UInt64.toLittleEndian x) = x := by
  simp [UInt64.toLittleEndian, UInt64.fromLittleEndian, nativeEndian]

/-! ## BE/LE Relationship -/

theorem UInt16.toBigEndian_eq_bswap_toLittleEndian (x : UInt16) :
    UInt16.toBigEndian x = UInt16.bswap (UInt16.toLittleEndian x) := by
  simp [UInt16.toBigEndian, UInt16.toLittleEndian, nativeEndian]

theorem UInt32.toBigEndian_eq_bswap_toLittleEndian (x : UInt32) :
    UInt32.toBigEndian x = UInt32.bswap (UInt32.toLittleEndian x) := by
  simp [UInt32.toBigEndian, UInt32.toLittleEndian, nativeEndian]

theorem UInt64.toBigEndian_eq_bswap_toLittleEndian (x : UInt64) :
    UInt64.toBigEndian x = UInt64.bswap (UInt64.toLittleEndian x) := by
  simp [UInt64.toBigEndian, UInt64.toLittleEndian, nativeEndian]

/-! ## Signed Type Endian Round-Trips -/

theorem Int16.toBigEndian_fromBigEndian (x : Int16) :
    Int16.fromBigEndian (Int16.toBigEndian x) = x := by
  cases x with | mk val =>
  simp only [Int16.toBigEndian, Int16.fromBigEndian, Radix.Int16.mk.injEq]
  simp only [Radix.UInt16.toBigEndian, Radix.UInt16.fromBigEndian, nativeEndian]
  exact congrArg Radix.UInt16.val (UInt16.bswap_bswap ⟨val⟩)

theorem Int32.toBigEndian_fromBigEndian (x : Int32) :
    Int32.fromBigEndian (Int32.toBigEndian x) = x := by
  cases x with | mk val =>
  simp only [Int32.toBigEndian, Int32.fromBigEndian, Radix.Int32.mk.injEq]
  simp only [Radix.UInt32.toBigEndian, Radix.UInt32.fromBigEndian, nativeEndian]
  exact congrArg Radix.UInt32.val (UInt32.bswap_bswap ⟨val⟩)

theorem Int64.toBigEndian_fromBigEndian (x : Int64) :
    Int64.fromBigEndian (Int64.toBigEndian x) = x := by
  cases x with | mk val =>
  simp only [Int64.toBigEndian, Int64.fromBigEndian, Radix.Int64.mk.injEq]
  simp only [Radix.UInt64.toBigEndian, Radix.UInt64.fromBigEndian, nativeEndian]
  exact congrArg Radix.UInt64.val (UInt64.bswap_bswap ⟨val⟩)

/-! ## ByteSlice Properties -/

@[simp] theorem ByteSlice.subslice_len (s : ByteSlice) (off len : Nat)
    (h : off + len ≤ s.len) : (s.subslice off len h).len = len := rfl

@[simp] theorem ByteSlice.zeros_len (n : Nat) : (ByteSlice.zeros n).len = n := rfl

@[simp] theorem ByteSlice.empty_len : ByteSlice.empty.len = 0 := rfl

@[simp] theorem ByteSlice.ofByteArray_len (arr : ByteArray) :
    (ByteSlice.ofByteArray arr).len = arr.size := rfl

end Radix
