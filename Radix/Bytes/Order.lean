/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Int
import Radix.Word.Size
import Radix.Bit.Ops
import Radix.Bytes.Spec

/-!
# Endianness Conversions (Layer 2)

This module implements byte-swap and endian conversion operations for all
fixed-width integer types using bitwise shift-and-OR composition.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.
- Imports Layer 3 (`Bytes.Spec`) for specification reference.
- MUST NOT import any Layer 1 modules.

## References

- FR-003.1: Conversion Functions (bswap, toBigEndian, fromBigEndian, etc.)
- FR-003.2: Proofs (round-trip, involution) -- proven in Bytes.Lemmas
-/

namespace Radix

open Radix.Bytes.Spec (Endian)

/-! ## Endianness Re-export -/

export Bytes.Spec (Endian)

/-! ## Platform Endianness Detection -/

/-- Native endianness: hardcoded to little-endian per C-005 (x86_64 primary target).

    All targets currently supported by Lean 4 (x86_64, aarch64, wasm32) are
    little-endian. Without FFI (C-001), there is no portable way to detect
    endianness at compile time in pure Lean 4.

    Use `validateNativeEndian` at program startup to fail-fast on any
    unexpected target triple. -/
@[inline] def nativeEndian : Endian :=
  Endian.little

/-- Runtime validation that the platform target is a known little-endian
    architecture. Call at program startup to fail-fast on unsupported platforms.
    Returns the target triple on success, or an error message on failure. -/
def validateNativeEndian : IO (Except String String) := do
  let target := System.Platform.target
  if target.contains "x86_64" || target.contains "aarch64" ||
     target.contains "arm" || target.contains "wasm32" ||
     target.contains "x86" then
    return .ok target
  else
    return .error s!"Unknown platform '{target}': endianness assumption may be invalid"

/-! ## UInt16 Byte Swap and Endian Conversions -/

namespace UInt16

@[inline] private def bswap16_fast (x : Radix.UInt16) : Radix.UInt16 :=
  let v := x.val
  ⟨((v &&& 0xFF) <<< (8 : _root_.UInt16)) ||| (v >>> (8 : _root_.UInt16))⟩

/-- Swap the byte order of a 16-bit unsigned integer. -/
@[implemented_by bswap16_fast, inline]
def bswap (x : UInt16) : UInt16 :=
  let lo := Radix.UInt16.band (Radix.UInt16.shrLogical x ⟨8⟩) ⟨0xFF⟩
  let hi := Radix.UInt16.shl (Radix.UInt16.band x ⟨0xFF⟩) ⟨8⟩
  Radix.UInt16.bor hi lo

/-- Convert to big-endian byte order. -/
@[inline] def toBigEndian (x : UInt16) : UInt16 :=
  match nativeEndian with
  | .little => bswap x
  | .big => x

/-- Convert from big-endian byte order. -/
@[inline] def fromBigEndian (x : UInt16) : UInt16 :=
  match nativeEndian with
  | .little => bswap x
  | .big => x

/-- Convert to little-endian byte order. -/
@[inline] def toLittleEndian (x : UInt16) : UInt16 :=
  match nativeEndian with
  | .little => x
  | .big => bswap x

/-- Convert from little-endian byte order. -/
@[inline] def fromLittleEndian (x : UInt16) : UInt16 :=
  match nativeEndian with
  | .little => x
  | .big => bswap x

/-- Convert to the specified endianness. -/
@[inline] def toEndian (e : Endian) (x : UInt16) : UInt16 :=
  match e with
  | .big => toBigEndian x
  | .little => toLittleEndian x

/-- Convert from the specified endianness. -/
@[inline] def fromEndian (e : Endian) (x : UInt16) : UInt16 :=
  match e with
  | .big => fromBigEndian x
  | .little => fromLittleEndian x

end UInt16

/-! ## UInt32 Byte Swap and Endian Conversions -/

namespace UInt32

@[inline] private def bswap32_fast (x : Radix.UInt32) : Radix.UInt32 :=
  let v := x.val
  let v := ((v &&& 0x00FF00FF) <<< (8 : _root_.UInt32)) ||| ((v >>> (8 : _root_.UInt32)) &&& 0x00FF00FF)
  let v := (v <<< (16 : _root_.UInt32)) ||| (v >>> (16 : _root_.UInt32))
  ⟨v⟩

/-- Swap the byte order of a 32-bit unsigned integer. -/
@[implemented_by bswap32_fast, inline]
def bswap (x : UInt32) : UInt32 :=
  let b0 := Radix.UInt32.band (Radix.UInt32.shrLogical x ⟨24⟩) ⟨0xFF⟩
  let b1 := Radix.UInt32.band (Radix.UInt32.shrLogical x ⟨16⟩) ⟨0xFF⟩
  let b2 := Radix.UInt32.band (Radix.UInt32.shrLogical x ⟨8⟩) ⟨0xFF⟩
  let b3 := Radix.UInt32.band x ⟨0xFF⟩
  Radix.UInt32.bor
    (Radix.UInt32.bor (Radix.UInt32.shl b3 ⟨24⟩) (Radix.UInt32.shl b2 ⟨16⟩))
    (Radix.UInt32.bor (Radix.UInt32.shl b1 ⟨8⟩) b0)

@[inline] def toBigEndian (x : UInt32) : UInt32 :=
  match nativeEndian with
  | .little => bswap x
  | .big => x

@[inline] def fromBigEndian (x : UInt32) : UInt32 :=
  match nativeEndian with
  | .little => bswap x
  | .big => x

@[inline] def toLittleEndian (x : UInt32) : UInt32 :=
  match nativeEndian with
  | .little => x
  | .big => bswap x

@[inline] def fromLittleEndian (x : UInt32) : UInt32 :=
  match nativeEndian with
  | .little => x
  | .big => bswap x

@[inline] def toEndian (e : Endian) (x : UInt32) : UInt32 :=
  match e with
  | .big => toBigEndian x
  | .little => toLittleEndian x

@[inline] def fromEndian (e : Endian) (x : UInt32) : UInt32 :=
  match e with
  | .big => fromBigEndian x
  | .little => fromLittleEndian x

end UInt32

/-! ## UInt64 Byte Swap and Endian Conversions -/

namespace UInt64

@[inline] private def bswap64_fast (x : Radix.UInt64) : Radix.UInt64 :=
  let v := x.val
  let v := ((v &&& 0x00FF00FF00FF00FF) <<< (8 : _root_.UInt64)) ||| ((v >>> (8 : _root_.UInt64)) &&& 0x00FF00FF00FF00FF)
  let v := ((v &&& 0x0000FFFF0000FFFF) <<< (16 : _root_.UInt64)) ||| ((v >>> (16 : _root_.UInt64)) &&& 0x0000FFFF0000FFFF)
  let v := (v <<< (32 : _root_.UInt64)) ||| (v >>> (32 : _root_.UInt64))
  ⟨v⟩

/-- Swap the byte order of a 64-bit unsigned integer. -/
@[implemented_by bswap64_fast, inline]
def bswap (x : UInt64) : UInt64 :=
  let b0 := Radix.UInt64.band (Radix.UInt64.shrLogical x ⟨56⟩) ⟨0xFF⟩
  let b1 := Radix.UInt64.band (Radix.UInt64.shrLogical x ⟨48⟩) ⟨0xFF⟩
  let b2 := Radix.UInt64.band (Radix.UInt64.shrLogical x ⟨40⟩) ⟨0xFF⟩
  let b3 := Radix.UInt64.band (Radix.UInt64.shrLogical x ⟨32⟩) ⟨0xFF⟩
  let b4 := Radix.UInt64.band (Radix.UInt64.shrLogical x ⟨24⟩) ⟨0xFF⟩
  let b5 := Radix.UInt64.band (Radix.UInt64.shrLogical x ⟨16⟩) ⟨0xFF⟩
  let b6 := Radix.UInt64.band (Radix.UInt64.shrLogical x ⟨8⟩) ⟨0xFF⟩
  let b7 := Radix.UInt64.band x ⟨0xFF⟩
  Radix.UInt64.bor
    (Radix.UInt64.bor (Radix.UInt64.shl b7 ⟨56⟩) (Radix.UInt64.shl b6 ⟨48⟩))
    (Radix.UInt64.bor
      (Radix.UInt64.bor (Radix.UInt64.shl b5 ⟨40⟩) (Radix.UInt64.shl b4 ⟨32⟩))
      (Radix.UInt64.bor
        (Radix.UInt64.bor (Radix.UInt64.shl b3 ⟨24⟩) (Radix.UInt64.shl b2 ⟨16⟩))
        (Radix.UInt64.bor (Radix.UInt64.shl b1 ⟨8⟩) b0)))

@[inline] def toBigEndian (x : UInt64) : UInt64 :=
  match nativeEndian with
  | .little => bswap x
  | .big => x

@[inline] def fromBigEndian (x : UInt64) : UInt64 :=
  match nativeEndian with
  | .little => bswap x
  | .big => x

@[inline] def toLittleEndian (x : UInt64) : UInt64 :=
  match nativeEndian with
  | .little => x
  | .big => bswap x

@[inline] def fromLittleEndian (x : UInt64) : UInt64 :=
  match nativeEndian with
  | .little => x
  | .big => bswap x

@[inline] def toEndian (e : Endian) (x : UInt64) : UInt64 :=
  match e with
  | .big => toBigEndian x
  | .little => toLittleEndian x

@[inline] def fromEndian (e : Endian) (x : UInt64) : UInt64 :=
  match e with
  | .big => fromBigEndian x
  | .little => fromLittleEndian x

end UInt64

/-! ## Signed Type Endian Conversions (delegate to unsigned) -/

namespace Int16

@[inline] def bswap (x : Int16) : Int16 := ⟨(UInt16.bswap ⟨x.val⟩).val⟩
@[inline] def toBigEndian (x : Int16) : Int16 := ⟨(UInt16.toBigEndian ⟨x.val⟩).val⟩
@[inline] def fromBigEndian (x : Int16) : Int16 := ⟨(UInt16.fromBigEndian ⟨x.val⟩).val⟩
@[inline] def toLittleEndian (x : Int16) : Int16 := ⟨(UInt16.toLittleEndian ⟨x.val⟩).val⟩
@[inline] def fromLittleEndian (x : Int16) : Int16 := ⟨(UInt16.fromLittleEndian ⟨x.val⟩).val⟩

end Int16

namespace Int32

@[inline] def bswap (x : Int32) : Int32 := ⟨(UInt32.bswap ⟨x.val⟩).val⟩
@[inline] def toBigEndian (x : Int32) : Int32 := ⟨(UInt32.toBigEndian ⟨x.val⟩).val⟩
@[inline] def fromBigEndian (x : Int32) : Int32 := ⟨(UInt32.fromBigEndian ⟨x.val⟩).val⟩
@[inline] def toLittleEndian (x : Int32) : Int32 := ⟨(UInt32.toLittleEndian ⟨x.val⟩).val⟩
@[inline] def fromLittleEndian (x : Int32) : Int32 := ⟨(UInt32.fromLittleEndian ⟨x.val⟩).val⟩

end Int32

namespace Int64

@[inline] def bswap (x : Int64) : Int64 := ⟨(UInt64.bswap ⟨x.val⟩).val⟩
@[inline] def toBigEndian (x : Int64) : Int64 := ⟨(UInt64.toBigEndian ⟨x.val⟩).val⟩
@[inline] def fromBigEndian (x : Int64) : Int64 := ⟨(UInt64.fromBigEndian ⟨x.val⟩).val⟩
@[inline] def toLittleEndian (x : Int64) : Int64 := ⟨(UInt64.toLittleEndian ⟨x.val⟩).val⟩
@[inline] def fromLittleEndian (x : Int64) : Int64 := ⟨(UInt64.fromLittleEndian ⟨x.val⟩).val⟩

end Int64

end Radix
