/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Bytes.Order

/-!
# Bounds-Checked ByteArray Views (Layer 2)

This module provides `ByteSlice`, a bounds-checked view into a `ByteArray`.
All read/write operations are either proof-carrying (Tier 1) or checked (Tier 2).

## Architecture

This is a **Layer 2 (Verified Implementation)** module.
- MUST NOT import any Layer 1 modules.

## References

- FR-004.1: ByteSlice (bounds-checked view, zero-copy slicing)
- NFR-002: Zero-cost abstractions (proof erasing)
- NFR-005: Interoperate with Lean4's ByteArray without copying
-/

namespace Radix

/-! ## ByteSlice Structure -/

/-- A bounds-checked view into a `ByteArray`.
    Provides zero-copy slicing with proof of bounds. -/
structure ByteSlice where
  /-- The underlying byte array. -/
  bytes : ByteArray
  /-- Start offset within the byte array. -/
  start : Nat
  /-- Length of this slice. -/
  len : Nat
  /-- Proof that the slice is within bounds. -/
  hbounds : start + len ≤ bytes.size

instance : BEq ByteSlice where
  beq a b :=
    if a.len != b.len then false
    else Id.run do
      for i in [:a.len] do
        if h₁ : a.start + i < a.bytes.size then
          if h₂ : b.start + i < b.bytes.size then
            if a.bytes.get (a.start + i) h₁ != b.bytes.get (b.start + i) h₂ then
              return false
          else return false
        else return false
      return true

namespace ByteSlice

/-- Create a ByteSlice from a ByteArray covering the full array. -/
@[inline] def ofByteArray (arr : ByteArray) : ByteSlice where
  bytes := arr
  start := 0
  len := arr.size
  hbounds := by omega

/-- Create a ByteSlice from a list of bytes. -/
def ofList (bs : List _root_.UInt8) : ByteSlice :=
  ofByteArray (ByteArray.mk bs.toArray)

/-- The size (length) of this slice. -/
@[inline] def size (s : ByteSlice) : Nat := s.len

/-- Is this slice empty? -/
@[inline] def isEmpty (s : ByteSlice) : Bool := s.len == 0

/-- Create an empty ByteSlice. -/
@[inline] def empty : ByteSlice where
  bytes := ByteArray.empty
  start := 0
  len := 0
  hbounds := by omega

/-- Create a ByteSlice filled with zeros of the given size. -/
def zeros (n : Nat) : ByteSlice where
  bytes := ByteArray.mk (List.replicate n (0 : _root_.UInt8)).toArray
  start := 0
  len := n
  hbounds := by simp [ByteArray.size]

/-! ## Tier 1: Proof-Carrying Read/Write -/

/-- Read a single byte at the given offset (proof-carrying). -/
@[inline] def readU8 (s : ByteSlice) (off : Nat)
    (h : off < s.len) : _root_.UInt8 :=
  s.bytes.get (s.start + off) (by have := s.hbounds; omega)

/-- Write a single byte at the given offset (proof-carrying).
    Returns a new ByteSlice (functional update). -/
@[inline] def writeU8 (s : ByteSlice) (off : Nat) (v : _root_.UInt8)
    (h : off < s.len) : ByteSlice where
  bytes := s.bytes.set (s.start + off) v (by have := s.hbounds; omega)
  start := s.start
  len := s.len
  hbounds := by
    have hsz : (s.bytes.set (s.start + off) v (by have := s.hbounds; omega)).size = s.bytes.size := by
      unfold ByteArray.set ByteArray.size; simp
    have := s.hbounds
    omega

@[simp] theorem writeU8_len (s : ByteSlice) (off : Nat) (v : _root_.UInt8)
    (h : off < s.len) : (s.writeU8 off v h).len = s.len := rfl

@[simp] theorem writeU8_start (s : ByteSlice) (off : Nat) (v : _root_.UInt8)
    (h : off < s.len) : (s.writeU8 off v h).start = s.start := rfl

/-- Read a 16-bit value at the given offset in the specified endianness (proof-carrying). -/
@[inline] def readU16 (s : ByteSlice) (off : Nat) (e : Bytes.Spec.Endian)
    (h : off + 2 ≤ s.len) : Radix.UInt16 :=
  let b0 := s.readU8 off (by omega)
  let b1 := s.readU8 (off + 1) (by omega)
  match e with
  | .little => ⟨(b0.toNat ||| (b1.toNat <<< 8)).toUInt16⟩
  | .big => ⟨((b0.toNat <<< 8) ||| b1.toNat).toUInt16⟩

/-- Read a 32-bit value at the given offset in the specified endianness (proof-carrying). -/
@[inline] def readU32 (s : ByteSlice) (off : Nat) (e : Bytes.Spec.Endian)
    (h : off + 4 ≤ s.len) : Radix.UInt32 :=
  let b0 := (s.readU8 off (by omega)).toNat
  let b1 := (s.readU8 (off + 1) (by omega)).toNat
  let b2 := (s.readU8 (off + 2) (by omega)).toNat
  let b3 := (s.readU8 (off + 3) (by omega)).toNat
  match e with
  | .little => ⟨(b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)).toUInt32⟩
  | .big => ⟨((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3).toUInt32⟩

/-- Read a 64-bit value at the given offset in the specified endianness (proof-carrying). -/
@[inline] def readU64 (s : ByteSlice) (off : Nat) (e : Bytes.Spec.Endian)
    (h : off + 8 ≤ s.len) : Radix.UInt64 :=
  let b0 := (s.readU8 off (by omega)).toNat
  let b1 := (s.readU8 (off + 1) (by omega)).toNat
  let b2 := (s.readU8 (off + 2) (by omega)).toNat
  let b3 := (s.readU8 (off + 3) (by omega)).toNat
  let b4 := (s.readU8 (off + 4) (by omega)).toNat
  let b5 := (s.readU8 (off + 5) (by omega)).toNat
  let b6 := (s.readU8 (off + 6) (by omega)).toNat
  let b7 := (s.readU8 (off + 7) (by omega)).toNat
  match e with
  | .little =>
    ⟨(b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24) |||
     (b4 <<< 32) ||| (b5 <<< 40) ||| (b6 <<< 48) ||| (b7 <<< 56)).toUInt64⟩
  | .big =>
    ⟨((b0 <<< 56) ||| (b1 <<< 48) ||| (b2 <<< 40) ||| (b3 <<< 32) |||
     (b4 <<< 24) ||| (b5 <<< 16) ||| (b6 <<< 8) ||| b7).toUInt64⟩

/-- Write a 16-bit value at the given offset in the specified endianness (proof-carrying). -/
@[inline] def writeU16 (s : ByteSlice) (off : Nat) (v : Radix.UInt16)
    (e : Bytes.Spec.Endian) (h : off + 2 ≤ s.len) : ByteSlice :=
  let n := v.val.toNat
  let (b0, b1) : _root_.UInt8 × _root_.UInt8 := match e with
    | .little => (((n) &&& 0xFF).toUInt8, ((n >>> 8) &&& 0xFF).toUInt8)
    | .big => (((n >>> 8) &&& 0xFF).toUInt8, ((n) &&& 0xFF).toUInt8)
  let s1 := s.writeU8 off b0 (by omega)
  have h1 : s1.len = s.len := writeU8_len s off b0 (by omega)
  s1.writeU8 (off + 1) b1 (by omega)

/-- Write a 32-bit value at the given offset in the specified endianness (proof-carrying). -/
@[inline] def writeU32 (s : ByteSlice) (off : Nat) (v : Radix.UInt32)
    (e : Bytes.Spec.Endian) (h : off + 4 ≤ s.len) : ByteSlice :=
  let n := v.val.toNat
  let (b0, b1, b2, b3) : _root_.UInt8 × _root_.UInt8 × _root_.UInt8 × _root_.UInt8 :=
    match e with
    | .little =>
      ((n &&& 0xFF).toUInt8, ((n >>> 8) &&& 0xFF).toUInt8,
       ((n >>> 16) &&& 0xFF).toUInt8, ((n >>> 24) &&& 0xFF).toUInt8)
    | .big =>
      (((n >>> 24) &&& 0xFF).toUInt8, ((n >>> 16) &&& 0xFF).toUInt8,
       ((n >>> 8) &&& 0xFF).toUInt8, (n &&& 0xFF).toUInt8)
  let s1 := s.writeU8 off b0 (by omega)
  have h1 : s1.len = s.len := writeU8_len s off b0 (by omega)
  let s2 := s1.writeU8 (off + 1) b1 (by omega)
  have h2 : s2.len = s1.len := writeU8_len s1 (off + 1) b1 (by omega)
  let s3 := s2.writeU8 (off + 2) b2 (by omega)
  have h3 : s3.len = s2.len := writeU8_len s2 (off + 2) b2 (by omega)
  s3.writeU8 (off + 3) b3 (by omega)

/-- Write a 64-bit value at the given offset in the specified endianness (proof-carrying). -/
@[inline] def writeU64 (s : ByteSlice) (off : Nat) (v : Radix.UInt64)
    (e : Bytes.Spec.Endian) (h : off + 8 ≤ s.len) : ByteSlice :=
  let n := v.val.toNat
  let mkByte (shift : Nat) : _root_.UInt8 := ((n >>> shift) &&& 0xFF).toUInt8
  let (a0, a1, a2, a3, a4, a5, a6, a7) :
    _root_.UInt8 × _root_.UInt8 × _root_.UInt8 × _root_.UInt8 ×
    _root_.UInt8 × _root_.UInt8 × _root_.UInt8 × _root_.UInt8 :=
    match e with
    | .little =>
      (mkByte 0, mkByte 8, mkByte 16, mkByte 24,
       mkByte 32, mkByte 40, mkByte 48, mkByte 56)
    | .big =>
      (mkByte 56, mkByte 48, mkByte 40, mkByte 32,
       mkByte 24, mkByte 16, mkByte 8, mkByte 0)
  let s1 := s.writeU8 off a0 (by omega)
  have h1 : s1.len = s.len := writeU8_len s off a0 (by omega)
  let s2 := s1.writeU8 (off + 1) a1 (by omega)
  have h2 : s2.len = s1.len := writeU8_len s1 (off + 1) a1 (by omega)
  let s3 := s2.writeU8 (off + 2) a2 (by omega)
  have h3 : s3.len = s2.len := writeU8_len s2 (off + 2) a2 (by omega)
  let s4 := s3.writeU8 (off + 3) a3 (by omega)
  have h4 : s4.len = s3.len := writeU8_len s3 (off + 3) a3 (by omega)
  let s5 := s4.writeU8 (off + 4) a4 (by omega)
  have h5 : s5.len = s4.len := writeU8_len s4 (off + 4) a4 (by omega)
  let s6 := s5.writeU8 (off + 5) a5 (by omega)
  have h6 : s6.len = s5.len := writeU8_len s5 (off + 5) a5 (by omega)
  let s7 := s6.writeU8 (off + 6) a6 (by omega)
  have h7 : s7.len = s6.len := writeU8_len s6 (off + 6) a6 (by omega)
  s7.writeU8 (off + 7) a7 (by omega)

/-! ## Tier 2: Checked Read/Write -/

/-- Read a single byte at the given offset (checked). -/
@[inline] def checkedReadU8 (s : ByteSlice) (off : Nat) : Option _root_.UInt8 :=
  if h : off < s.len then some (s.readU8 off h)
  else none

/-- Write a single byte at the given offset (checked). -/
@[inline] def checkedWriteU8 (s : ByteSlice) (off : Nat)
    (v : _root_.UInt8) : Option ByteSlice :=
  if h : off < s.len then some (s.writeU8 off v h)
  else none

/-- Read a 16-bit value (checked). -/
@[inline] def checkedReadU16 (s : ByteSlice) (off : Nat)
    (e : Bytes.Spec.Endian) : Option Radix.UInt16 :=
  if h : off + 2 ≤ s.len then some (s.readU16 off e h)
  else none

/-- Write a 16-bit value (checked). -/
@[inline] def checkedWriteU16 (s : ByteSlice) (off : Nat)
    (v : Radix.UInt16) (e : Bytes.Spec.Endian) : Option ByteSlice :=
  if h : off + 2 ≤ s.len then some (s.writeU16 off v e h)
  else none

/-- Read a 32-bit value (checked). -/
@[inline] def checkedReadU32 (s : ByteSlice) (off : Nat)
    (e : Bytes.Spec.Endian) : Option Radix.UInt32 :=
  if h : off + 4 ≤ s.len then some (s.readU32 off e h)
  else none

/-- Write a 32-bit value (checked). -/
@[inline] def checkedWriteU32 (s : ByteSlice) (off : Nat)
    (v : Radix.UInt32) (e : Bytes.Spec.Endian) : Option ByteSlice :=
  if h : off + 4 ≤ s.len then some (s.writeU32 off v e h)
  else none

/-- Read a 64-bit value (checked). -/
@[inline] def checkedReadU64 (s : ByteSlice) (off : Nat)
    (e : Bytes.Spec.Endian) : Option Radix.UInt64 :=
  if h : off + 8 ≤ s.len then some (s.readU64 off e h)
  else none

/-- Write a 64-bit value (checked). -/
@[inline] def checkedWriteU64 (s : ByteSlice) (off : Nat)
    (v : Radix.UInt64) (e : Bytes.Spec.Endian) : Option ByteSlice :=
  if h : off + 8 ≤ s.len then some (s.writeU64 off v e h)
  else none

/-! ## Zero-Copy Slicing -/

/-- Create a sub-slice from the given offset and length (proof-carrying). -/
@[inline] def subslice (s : ByteSlice) (off len : Nat)
    (h : off + len ≤ s.len) : ByteSlice where
  bytes := s.bytes
  start := s.start + off
  len := len
  hbounds := by have := s.hbounds; omega

/-- Create a sub-slice (checked). -/
@[inline] def checkedSubslice (s : ByteSlice) (off len : Nat) :
    Option ByteSlice :=
  if h : off + len ≤ s.len then some (s.subslice off len h)
  else none

/-- Convert the slice to a fresh ByteArray (copies data). -/
def toByteArray (s : ByteSlice) : ByteArray := Id.run do
  let mut arr := ByteArray.empty
  for i in [:s.len] do
    if h : s.start + i < s.bytes.size then
      arr := arr.push (s.bytes.get (s.start + i) h)
  return arr

/-- Convert the slice contents to a list. -/
def toList (s : ByteSlice) : List _root_.UInt8 :=
  (List.range s.len).filterMap fun i =>
    if h : s.start + i < s.bytes.size then
      some (s.bytes.get (s.start + i) h)
    else none

end ByteSlice

end Radix
