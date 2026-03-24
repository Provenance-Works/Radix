/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Bytes.Order
import Radix.Bytes.Slice
import Radix.Bytes.Spec

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

/-! ## Signed Type Little-Endian Round-Trips -/

theorem Int16.toLittleEndian_fromLittleEndian (x : Int16) :
    Int16.fromLittleEndian (Int16.toLittleEndian x) = x := by
  cases x with | mk val =>
  simp only [Int16.toLittleEndian, Int16.fromLittleEndian, Radix.Int16.mk.injEq]
  simp only [Radix.UInt16.toLittleEndian, Radix.UInt16.fromLittleEndian, nativeEndian]

theorem Int32.toLittleEndian_fromLittleEndian (x : Int32) :
    Int32.fromLittleEndian (Int32.toLittleEndian x) = x := by
  cases x with | mk val =>
  simp only [Int32.toLittleEndian, Int32.fromLittleEndian, Radix.Int32.mk.injEq]
  simp only [Radix.UInt32.toLittleEndian, Radix.UInt32.fromLittleEndian, nativeEndian]

theorem Int64.toLittleEndian_fromLittleEndian (x : Int64) :
    Int64.fromLittleEndian (Int64.toLittleEndian x) = x := by
  cases x with | mk val =>
  simp only [Int64.toLittleEndian, Int64.fromLittleEndian, Radix.Int64.mk.injEq]
  simp only [Radix.UInt64.toLittleEndian, Radix.UInt64.fromLittleEndian, nativeEndian]

/-! ## Signed Type BE/LE Relationship -/

theorem Int16.toBigEndian_eq_bswap_toLittleEndian (x : Int16) :
    Int16.toBigEndian x = Int16.bswap (Int16.toLittleEndian x) := by
  cases x with | mk val =>
  simp only [Int16.toBigEndian, Int16.toLittleEndian, Int16.bswap, Radix.Int16.mk.injEq]
  simp only [Radix.UInt16.toBigEndian, Radix.UInt16.toLittleEndian, nativeEndian]

theorem Int32.toBigEndian_eq_bswap_toLittleEndian (x : Int32) :
    Int32.toBigEndian x = Int32.bswap (Int32.toLittleEndian x) := by
  cases x with | mk val =>
  simp only [Int32.toBigEndian, Int32.toLittleEndian, Int32.bswap, Radix.Int32.mk.injEq]
  simp only [Radix.UInt32.toBigEndian, Radix.UInt32.toLittleEndian, nativeEndian]

theorem Int64.toBigEndian_eq_bswap_toLittleEndian (x : Int64) :
    Int64.toBigEndian x = Int64.bswap (Int64.toLittleEndian x) := by
  cases x with | mk val =>
  simp only [Int64.toBigEndian, Int64.toLittleEndian, Int64.bswap, Radix.Int64.mk.injEq]
  simp only [Radix.UInt64.toBigEndian, Radix.UInt64.toLittleEndian, nativeEndian]

/-! ## Additional Signed Type Bswap Involution -/

theorem Int16.bswap_bswap (x : Int16) : Int16.bswap (Int16.bswap x) = x := by
  cases x with | mk val =>
  simp only [Int16.bswap, Radix.Int16.mk.injEq]
  exact congrArg Radix.UInt16.val (UInt16.bswap_bswap ⟨val⟩)

theorem Int32.bswap_bswap (x : Int32) : Int32.bswap (Int32.bswap x) = x := by
  cases x with | mk val =>
  simp only [Int32.bswap, Radix.Int32.mk.injEq]
  exact congrArg Radix.UInt32.val (UInt32.bswap_bswap ⟨val⟩)

theorem Int64.bswap_bswap (x : Int64) : Int64.bswap (Int64.bswap x) = x := by
  cases x with | mk val =>
  simp only [Int64.bswap, Radix.Int64.mk.injEq]
  exact congrArg Radix.UInt64.val (UInt64.bswap_bswap ⟨val⟩)

/-! ## ByteSlice Properties -/

@[simp] theorem ByteSlice.subslice_len (s : ByteSlice) (off len : Nat)
    (h : off + len ≤ s.len) : (s.subslice off len h).len = len := rfl

@[simp] theorem ByteSlice.zeros_len (n : Nat) : (ByteSlice.zeros n).len = n := rfl

@[simp] theorem ByteSlice.empty_len : ByteSlice.empty.len = 0 := rfl

@[simp] theorem ByteSlice.ofByteArray_len (arr : ByteArray) :
    (ByteSlice.ofByteArray arr).len = arr.size := rfl

/-! ## Spec-Level Byte Swap Involution (BitVec) -/

/-- Spec-level bswap16 involution at BitVec level. -/
theorem Bytes.Spec.bswap16_involution_proof :
    Bytes.Spec.bswap16_involution := by
  intro x
  simp only [Bytes.Spec.bswap16, Bytes.Spec.extractByte]
  bv_decide

/-- Spec-level bswap32 involution at BitVec level. -/
theorem Bytes.Spec.bswap32_involution_proof :
    Bytes.Spec.bswap32_involution := by
  intro x
  simp only [Bytes.Spec.bswap32, Bytes.Spec.extractByte]
  bv_decide

/-- Spec-level bswap64 involution at BitVec level. -/
theorem Bytes.Spec.bswap64_involution_proof :
    Bytes.Spec.bswap64_involution := by
  intro x
  simp only [Bytes.Spec.bswap64, Bytes.Spec.extractByte]
  bv_decide

/-! ## Spec-Level Endian Round-Trip (BitVec) -/

/-- Spec-level big-endian 16-bit round-trip. -/
theorem Bytes.Spec.toBE_fromBE_roundtrip16_proof :
    Bytes.Spec.toBE_fromBE_roundtrip16 := by
  intro x
  simp only [Bytes.Spec.fromBigEndian16,
             Bytes.Spec.toBigEndian16]
  exact Bytes.Spec.bswap16_involution_proof x

/-- Spec-level big-endian 32-bit round-trip. -/
theorem Bytes.Spec.toBE_fromBE_roundtrip32_proof :
    Bytes.Spec.toBE_fromBE_roundtrip32 := by
  intro x
  simp only [Bytes.Spec.fromBigEndian32,
             Bytes.Spec.toBigEndian32]
  exact Bytes.Spec.bswap32_involution_proof x

/-- Spec-level big-endian 64-bit round-trip. -/
theorem Bytes.Spec.toBE_fromBE_roundtrip64_proof :
    Bytes.Spec.toBE_fromBE_roundtrip64 := by
  intro x
  simp only [Bytes.Spec.fromBigEndian64,
             Bytes.Spec.toBigEndian64]
  exact Bytes.Spec.bswap64_involution_proof x

/-- Spec-level little-endian 16-bit round-trip. -/
theorem Bytes.Spec.toLE_fromLE_roundtrip16_proof :
    Bytes.Spec.toLE_fromLE_roundtrip16 := by
  intro x
  simp [Bytes.Spec.fromLittleEndian16,
        Bytes.Spec.toLittleEndian16]

/-- Spec-level little-endian 32-bit round-trip. -/
theorem Bytes.Spec.toLE_fromLE_roundtrip32_proof :
    Bytes.Spec.toLE_fromLE_roundtrip32 := by
  intro x
  simp [Bytes.Spec.fromLittleEndian32,
        Bytes.Spec.toLittleEndian32]

/-- Spec-level little-endian 64-bit round-trip. -/
theorem Bytes.Spec.toLE_fromLE_roundtrip64_proof :
    Bytes.Spec.toLE_fromLE_roundtrip64 := by
  intro x
  simp [Bytes.Spec.fromLittleEndian64,
        Bytes.Spec.toLittleEndian64]

/-! ## Spec-Level ByteSlice Read-After-Write -/

/-- Read-after-write at the same offset returns the written value. -/
theorem Bytes.Spec.readU8_writeU8_same_proof :
    Bytes.Spec.readU8_writeU8_same := by
  intro s off v h
  simp [Bytes.Spec.ByteSliceSpec.readU8,
        Bytes.Spec.ByteSliceSpec.writeU8]

/-- Read-after-write at a different offset returns the original value. -/
theorem Bytes.Spec.readU8_writeU8_diff_proof :
    Bytes.Spec.readU8_writeU8_diff := by
  intro s i j v hi hj hne
  simp [Bytes.Spec.ByteSliceSpec.readU8,
        Bytes.Spec.ByteSliceSpec.writeU8, hne]

/-! ## Additional ByteSlice Properties -/

/-- Subslice start is computed correctly. -/
@[simp] theorem ByteSlice.subslice_start (s : ByteSlice) (off len : Nat)
    (h : off + len ≤ s.len) :
    (s.subslice off len h).start = s.start + off := rfl

/-- WriteU8 preserves the underlying array size. -/
theorem ByteSlice.writeU8_bytes_size (s : ByteSlice) (off : Nat)
    (v : _root_.UInt8) (h : off < s.len) :
    (s.writeU8 off v h).bytes.size = s.bytes.size := by
  unfold ByteSlice.writeU8
  show (ByteArray.set s.bytes (s.start + off) v _).size = s.bytes.size
  unfold ByteArray.size ByteArray.set
  simp

/-- Checked readU8 returns some iff offset is in bounds. -/
theorem ByteSlice.checkedReadU8_isSome (s : ByteSlice) (off : Nat)
    (h : off < s.len) :
    (s.checkedReadU8 off).isSome = true := by
  simp [ByteSlice.checkedReadU8, dif_pos h]

/-- Checked readU8 returns none iff offset is out of bounds. -/
theorem ByteSlice.checkedReadU8_isNone (s : ByteSlice) (off : Nat)
    (h : ¬ off < s.len) :
    s.checkedReadU8 off = none := by
  simp [ByteSlice.checkedReadU8, dif_neg h]

/-- Checked writeU8 returns some iff offset is in bounds. -/
theorem ByteSlice.checkedWriteU8_isSome (s : ByteSlice) (off : Nat)
    (v : _root_.UInt8) (h : off < s.len) :
    (s.checkedWriteU8 off v).isSome = true := by
  simp [ByteSlice.checkedWriteU8, dif_pos h]

/-- Checked writeU8 returns none iff offset is out of bounds. -/
theorem ByteSlice.checkedWriteU8_isNone (s : ByteSlice) (off : Nat)
    (v : _root_.UInt8) (h : ¬ off < s.len) :
    s.checkedWriteU8 off v = none := by
  simp [ByteSlice.checkedWriteU8, dif_neg h]

/-- Checked readU16 returns some iff sufficient space. -/
theorem ByteSlice.checkedReadU16_isSome (s : ByteSlice) (off : Nat)
    (e : Bytes.Spec.Endian) (h : off + 2 ≤ s.len) :
    (s.checkedReadU16 off e).isSome = true := by
  simp [ByteSlice.checkedReadU16, dif_pos h]

/-- Checked readU16 returns none iff insufficient space. -/
theorem ByteSlice.checkedReadU16_isNone (s : ByteSlice) (off : Nat)
    (e : Bytes.Spec.Endian) (h : ¬ off + 2 ≤ s.len) :
    s.checkedReadU16 off e = none := by
  simp [ByteSlice.checkedReadU16, dif_neg h]

/-- Checked readU32 returns some iff sufficient space. -/
theorem ByteSlice.checkedReadU32_isSome (s : ByteSlice) (off : Nat)
    (e : Bytes.Spec.Endian) (h : off + 4 ≤ s.len) :
    (s.checkedReadU32 off e).isSome = true := by
  simp [ByteSlice.checkedReadU32, dif_pos h]

/-- Checked readU32 returns none iff insufficient space. -/
theorem ByteSlice.checkedReadU32_isNone (s : ByteSlice) (off : Nat)
    (e : Bytes.Spec.Endian) (h : ¬ off + 4 ≤ s.len) :
    s.checkedReadU32 off e = none := by
  simp [ByteSlice.checkedReadU32, dif_neg h]

/-- Checked readU64 returns some iff sufficient space. -/
theorem ByteSlice.checkedReadU64_isSome (s : ByteSlice) (off : Nat)
    (e : Bytes.Spec.Endian) (h : off + 8 ≤ s.len) :
    (s.checkedReadU64 off e).isSome = true := by
  simp [ByteSlice.checkedReadU64, dif_pos h]

/-- Checked readU64 returns none iff insufficient space. -/
theorem ByteSlice.checkedReadU64_isNone (s : ByteSlice) (off : Nat)
    (e : Bytes.Spec.Endian) (h : ¬ off + 8 ≤ s.len) :
    s.checkedReadU64 off e = none := by
  simp [ByteSlice.checkedReadU64, dif_neg h]

/-- Empty slice is empty. -/
theorem ByteSlice.empty_isEmpty : ByteSlice.empty.isEmpty = true := rfl

/-- Zeros slice is not empty when n > 0. -/
theorem ByteSlice.zeros_not_empty (n : Nat) (h : 0 < n) :
    (ByteSlice.zeros n).isEmpty = false := by
  simp [ByteSlice.isEmpty, ByteSlice.zeros]
  omega

/-- ofByteArray preserves start at 0. -/
@[simp] theorem ByteSlice.ofByteArray_start (arr : ByteArray) :
    (ByteSlice.ofByteArray arr).start = 0 := rfl

/-- WriteU16 preserves slice length. -/
theorem ByteSlice.writeU16_len (s : ByteSlice) (off : Nat) (v : Radix.UInt16)
    (e : Bytes.Spec.Endian) (h : off + 2 ≤ s.len) :
    (s.writeU16 off v e h).len = s.len := by
  unfold ByteSlice.writeU16; split <;> rfl

/-- WriteU32 preserves slice length. -/
theorem ByteSlice.writeU32_len (s : ByteSlice) (off : Nat) (v : Radix.UInt32)
    (e : Bytes.Spec.Endian) (h : off + 4 ≤ s.len) :
    (s.writeU32 off v e h).len = s.len := by
  unfold ByteSlice.writeU32; split <;> rfl

/-- WriteU64 preserves slice length. -/
theorem ByteSlice.writeU64_len (s : ByteSlice) (off : Nat) (v : Radix.UInt64)
    (e : Bytes.Spec.Endian) (h : off + 8 ≤ s.len) :
    (s.writeU64 off v e h).len = s.len := by
  unfold ByteSlice.writeU64; split <;> rfl

/-! ## Spec-Level Bswap Involution (via bv_decide) -/

open Bytes.Spec in
theorem Bytes.Spec.bswap16_invol (x : BitVec 16) :
    bswap16 (bswap16 x) = x := by
  simp [bswap16, extractByte]; bv_decide

open Bytes.Spec in
theorem Bytes.Spec.bswap32_invol (x : BitVec 32) :
    bswap32 (bswap32 x) = x := by
  simp [bswap32, extractByte]; bv_decide

open Bytes.Spec in
theorem Bytes.Spec.bswap64_invol (x : BitVec 64) :
    bswap64 (bswap64 x) = x := by
  simp [bswap64, extractByte]; bv_decide

/-! ## Nibble Round-Trip -/

open Bytes.Spec in
theorem Bytes.Spec.fromNibbles_round_trip (b : BitVec 8) :
    fromNibbles (highNibble b) (lowNibble b) = b := by
  simp [fromNibbles, highNibble, lowNibble]; bv_decide

open Bytes.Spec in
theorem Bytes.Spec.highNibble_fromNibbles (hi lo : BitVec 4) :
    highNibble (fromNibbles hi lo) = hi := by
  simp [highNibble, fromNibbles]; bv_decide

open Bytes.Spec in
theorem Bytes.Spec.lowNibble_fromNibbles (hi lo : BitVec 4) :
    lowNibble (fromNibbles hi lo) = lo := by
  simp [lowNibble, fromNibbles]

/-! ## BE/LE ReadU16 Relationship -/

open Bytes.Spec in
theorem Bytes.Spec.readU16BE_eq_bswap_readU16LE
    (s : ByteSliceSpec) (off : Nat) (h : off + 2 ≤ s.len) :
    ByteSliceSpec.readU16BE s off h = bswap16 (ByteSliceSpec.readU16LE s off h) := by
  simp [ByteSliceSpec.readU16BE, ByteSliceSpec.readU16LE, bswap16, extractByte]
  bv_decide

/-! ## Endian Identity Properties -/

open Bytes.Spec in
theorem Bytes.Spec.toLittleEndian16_id (x : BitVec 16) :
    toLittleEndian16 x = x := rfl

open Bytes.Spec in
theorem Bytes.Spec.toLittleEndian32_id (x : BitVec 32) :
    toLittleEndian32 x = x := rfl

open Bytes.Spec in
theorem Bytes.Spec.toLittleEndian64_id (x : BitVec 64) :
    toLittleEndian64 x = x := rfl

open Bytes.Spec in
theorem Bytes.Spec.fromBE_toBE_roundtrip16 (x : BitVec 16) :
    fromBigEndian16 (toBigEndian16 x) = x := by
  simp [fromBigEndian16, toBigEndian16]
  exact bswap16_invol x

open Bytes.Spec in
theorem Bytes.Spec.fromBE_toBE_roundtrip32 (x : BitVec 32) :
    fromBigEndian32 (toBigEndian32 x) = x := by
  simp [fromBigEndian32, toBigEndian32]
  exact bswap32_invol x

open Bytes.Spec in
theorem Bytes.Spec.fromBE_toBE_roundtrip64 (x : BitVec 64) :
    fromBigEndian64 (toBigEndian64 x) = x := by
  simp [fromBigEndian64, toBigEndian64]
  exact bswap64_invol x

end Radix
