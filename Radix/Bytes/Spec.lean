/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.BitVec

/-!
# Byte Operations Specification (Layer 3)

This module defines the formal specification of byte-order operations
using Mathlib's `BitVec n`.

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 1 or Layer 2 modules.

## References

- FR-003: Byte Order and Endianness
- FR-003.1: Conversion Functions
- FR-003.2: Proofs (round-trip, involution)
-/

namespace Radix.Bytes.Spec

open BitVec

/-! ## 1. Endianness -/

/-- Endianness enumeration. -/
inductive Endian where
  | big
  | little
  deriving DecidableEq, Repr

/-! ## 2. Byte Extraction Specification -/

/-- Extract byte at position `i` (0 = least significant) from a BitVec. -/
def extractByte {n : Nat} (x : BitVec n) (i : Nat) : BitVec 8 :=
  BitVec.truncate 8 (x >>> (i * 8))

/-! ## 3. Byte Swap Specification -/

/-- Byte-swap specification for 16-bit values. -/
def bswap16 (x : BitVec 16) : BitVec 16 :=
  let b0 := extractByte x 0
  let b1 := extractByte x 1
  (b0.zeroExtend 16 <<< 8) ||| b1.zeroExtend 16

/-- Byte-swap specification for 32-bit values. -/
def bswap32 (x : BitVec 32) : BitVec 32 :=
  let b0 := extractByte x 0
  let b1 := extractByte x 1
  let b2 := extractByte x 2
  let b3 := extractByte x 3
  (b0.zeroExtend 32 <<< 24) |||
  (b1.zeroExtend 32 <<< 16) |||
  (b2.zeroExtend 32 <<< 8) |||
  b3.zeroExtend 32

/-- Byte-swap specification for 64-bit values. -/
def bswap64 (x : BitVec 64) : BitVec 64 :=
  let b0 := extractByte x 0
  let b1 := extractByte x 1
  let b2 := extractByte x 2
  let b3 := extractByte x 3
  let b4 := extractByte x 4
  let b5 := extractByte x 5
  let b6 := extractByte x 6
  let b7 := extractByte x 7
  (b0.zeroExtend 64 <<< 56) |||
  (b1.zeroExtend 64 <<< 48) |||
  (b2.zeroExtend 64 <<< 40) |||
  (b3.zeroExtend 64 <<< 32) |||
  (b4.zeroExtend 64 <<< 24) |||
  (b5.zeroExtend 64 <<< 16) |||
  (b6.zeroExtend 64 <<< 8) |||
  b7.zeroExtend 64

/-! ## 4. Endian Conversion Specifications -/

/-- Convert to big-endian (identity on big-endian, swap on little-endian).
    Spec assumes host is little-endian (the common case for x86). -/
def toBigEndian16 (x : BitVec 16) : BitVec 16 := bswap16 x
def toBigEndian32 (x : BitVec 32) : BitVec 32 := bswap32 x
def toBigEndian64 (x : BitVec 64) : BitVec 64 := bswap64 x

/-- Convert from big-endian to host. -/
def fromBigEndian16 (x : BitVec 16) : BitVec 16 := bswap16 x
def fromBigEndian32 (x : BitVec 32) : BitVec 32 := bswap32 x
def fromBigEndian64 (x : BitVec 64) : BitVec 64 := bswap64 x

/-- On little-endian host, toLittleEndian is identity. -/
def toLittleEndian16 (x : BitVec 16) : BitVec 16 := x
def toLittleEndian32 (x : BitVec 32) : BitVec 32 := x
def toLittleEndian64 (x : BitVec 64) : BitVec 64 := x

/-- On little-endian host, fromLittleEndian is identity. -/
def fromLittleEndian16 (x : BitVec 16) : BitVec 16 := x
def fromLittleEndian32 (x : BitVec 32) : BitVec 32 := x
def fromLittleEndian64 (x : BitVec 64) : BitVec 64 := x

/-! ## 5. ByteSlice Specification -/

/-- Abstract specification of a byte slice: a contiguous subsequence of bytes. -/
structure ByteSliceSpec where
  /-- The underlying byte sequence. -/
  data : List (BitVec 8)
  /-- Length of the slice. -/
  len : Nat
  /-- data length matches len. -/
  hlen : data.length = len

/-- Read a single byte from the slice at the given offset. -/
def ByteSliceSpec.readU8 (s : ByteSliceSpec) (off : Nat)
    (h : off < s.len) : BitVec 8 :=
  s.data.get ⟨off, s.hlen ▸ h⟩

/-- Write a single byte to the slice at the given offset. -/
def ByteSliceSpec.writeU8 (s : ByteSliceSpec) (off : Nat) (v : BitVec 8)
    (_h : off < s.len) : ByteSliceSpec where
  data := s.data.set off v
  len := s.len
  hlen := by simp [List.length_set, s.hlen]

@[simp] theorem ByteSliceSpec.writeU8_len (s : ByteSliceSpec) (off : Nat)
    (v : BitVec 8) (h : off < s.len) :
    (s.writeU8 off v h).len = s.len := rfl

/-- Read a 16-bit value from the slice at the given offset in little-endian order. -/
def ByteSliceSpec.readU16LE (s : ByteSliceSpec) (off : Nat)
    (h : off + 2 ≤ s.len) : BitVec 16 :=
  let b0 := s.readU8 off (by omega)
  let b1 := s.readU8 (off + 1) (by omega)
  (b1.zeroExtend 16 <<< 8) ||| b0.zeroExtend 16

/-- Read a 32-bit value from the slice at the given offset in little-endian order. -/
def ByteSliceSpec.readU32LE (s : ByteSliceSpec) (off : Nat)
    (h : off + 4 ≤ s.len) : BitVec 32 :=
  let b0 := s.readU8 off (by omega)
  let b1 := s.readU8 (off + 1) (by omega)
  let b2 := s.readU8 (off + 2) (by omega)
  let b3 := s.readU8 (off + 3) (by omega)
  (b3.zeroExtend 32 <<< 24) ||| (b2.zeroExtend 32 <<< 16) |||
  (b1.zeroExtend 32 <<< 8) ||| b0.zeroExtend 32

/-- Read a 64-bit value from the slice at the given offset in little-endian order. -/
def ByteSliceSpec.readU64LE (s : ByteSliceSpec) (off : Nat)
    (h : off + 8 ≤ s.len) : BitVec 64 :=
  let b0 := s.readU8 off (by omega)
  let b1 := s.readU8 (off + 1) (by omega)
  let b2 := s.readU8 (off + 2) (by omega)
  let b3 := s.readU8 (off + 3) (by omega)
  let b4 := s.readU8 (off + 4) (by omega)
  let b5 := s.readU8 (off + 5) (by omega)
  let b6 := s.readU8 (off + 6) (by omega)
  let b7 := s.readU8 (off + 7) (by omega)
  (b7.zeroExtend 64 <<< 56) ||| (b6.zeroExtend 64 <<< 48) |||
  (b5.zeroExtend 64 <<< 40) ||| (b4.zeroExtend 64 <<< 32) |||
  (b3.zeroExtend 64 <<< 24) ||| (b2.zeroExtend 64 <<< 16) |||
  (b1.zeroExtend 64 <<< 8) ||| b0.zeroExtend 64

/-- Read a 16-bit value in big-endian order. -/
def ByteSliceSpec.readU16BE (s : ByteSliceSpec) (off : Nat)
    (h : off + 2 ≤ s.len) : BitVec 16 :=
  let b0 := s.readU8 off (by omega)
  let b1 := s.readU8 (off + 1) (by omega)
  (b0.zeroExtend 16 <<< 8) ||| b1.zeroExtend 16

/-- Read a 32-bit value in big-endian order. -/
def ByteSliceSpec.readU32BE (s : ByteSliceSpec) (off : Nat)
    (h : off + 4 ≤ s.len) : BitVec 32 :=
  let b0 := s.readU8 off (by omega)
  let b1 := s.readU8 (off + 1) (by omega)
  let b2 := s.readU8 (off + 2) (by omega)
  let b3 := s.readU8 (off + 3) (by omega)
  (b0.zeroExtend 32 <<< 24) ||| (b1.zeroExtend 32 <<< 16) |||
  (b2.zeroExtend 32 <<< 8) ||| b3.zeroExtend 32

/-- Read a 64-bit value in big-endian order. -/
def ByteSliceSpec.readU64BE (s : ByteSliceSpec) (off : Nat)
    (h : off + 8 ≤ s.len) : BitVec 64 :=
  let b0 := s.readU8 off (by omega)
  let b1 := s.readU8 (off + 1) (by omega)
  let b2 := s.readU8 (off + 2) (by omega)
  let b3 := s.readU8 (off + 3) (by omega)
  let b4 := s.readU8 (off + 4) (by omega)
  let b5 := s.readU8 (off + 5) (by omega)
  let b6 := s.readU8 (off + 6) (by omega)
  let b7 := s.readU8 (off + 7) (by omega)
  (b0.zeroExtend 64 <<< 56) ||| (b1.zeroExtend 64 <<< 48) |||
  (b2.zeroExtend 64 <<< 40) ||| (b3.zeroExtend 64 <<< 32) |||
  (b4.zeroExtend 64 <<< 24) ||| (b5.zeroExtend 64 <<< 16) |||
  (b6.zeroExtend 64 <<< 8) ||| b7.zeroExtend 64

/-! ## 6. Specification Properties (stated, proven in Lemmas) -/

/-- Byte-swap is an involution: swapping twice returns the original. -/
def bswap16_involution : Prop := ∀ x : BitVec 16, bswap16 (bswap16 x) = x
def bswap32_involution : Prop := ∀ x : BitVec 32, bswap32 (bswap32 x) = x
def bswap64_involution : Prop := ∀ x : BitVec 64, bswap64 (bswap64 x) = x

/-- Big-endian round-trip: converting to BE and back gives the original. -/
def toBE_fromBE_roundtrip16 : Prop :=
  ∀ x : BitVec 16, fromBigEndian16 (toBigEndian16 x) = x
def toBE_fromBE_roundtrip32 : Prop :=
  ∀ x : BitVec 32, fromBigEndian32 (toBigEndian32 x) = x
def toBE_fromBE_roundtrip64 : Prop :=
  ∀ x : BitVec 64, fromBigEndian64 (toBigEndian64 x) = x

/-- Little-endian round-trip is trivially identity. -/
def toLE_fromLE_roundtrip16 : Prop :=
  ∀ x : BitVec 16, fromLittleEndian16 (toLittleEndian16 x) = x
def toLE_fromLE_roundtrip32 : Prop :=
  ∀ x : BitVec 32, fromLittleEndian32 (toLittleEndian32 x) = x
def toLE_fromLE_roundtrip64 : Prop :=
  ∀ x : BitVec 64, fromLittleEndian64 (toLittleEndian64 x) = x

/-- ByteSlice read-after-write at the same offset returns the written value. -/
def readU8_writeU8_same : Prop :=
  ∀ (s : ByteSliceSpec) (off : Nat) (v : BitVec 8)
    (h : off < s.len),
    (s.writeU8 off v h).readU8 off (by simp [ByteSliceSpec.writeU8_len]; exact h) = v

/-- ByteSlice read-after-write at a different offset returns the original value. -/
def readU8_writeU8_diff : Prop :=
  ∀ (s : ByteSliceSpec) (i j : Nat) (v : BitVec 8)
    (hi : i < s.len) (hj : j < s.len) (_ : i ≠ j),
    (s.writeU8 i v hi).readU8 j (by simp [ByteSliceSpec.writeU8_len]; exact hj) = s.readU8 j hj

/-! ## 7. Nibble and Hex Encoding -/

/-- Extract the high nibble (bits 7..4) of a byte. -/
def highNibble (b : BitVec 8) : BitVec 4 :=
  BitVec.truncate 4 (b >>> 4)

/-- Extract the low nibble (bits 3..0) of a byte. -/
def lowNibble (b : BitVec 8) : BitVec 4 :=
  BitVec.truncate 4 b

/-- Reconstruct a byte from high and low nibbles. -/
def fromNibbles (hi lo : BitVec 4) : BitVec 8 :=
  (hi.zeroExtend 8 <<< 4) ||| lo.zeroExtend 8

/-- Byte extraction is bounded: extractByte always produces a valid 8-bit value. -/
theorem extractByte_width {n : Nat} (x : BitVec n) (i : Nat) :
    (extractByte x i).toNat < 256 := by
  exact (extractByte x i).isLt

/-- Zero-extending an 8-bit value to width n preserves the value. -/
theorem extractByte_zero {n : Nat} (x : BitVec n) :
    (extractByte x 0).toNat = x.toNat % 256 := by
  simp [extractByte]

end Radix.Bytes.Spec
