/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Bit.Ops

/-!
# Bit Field Operations (Layer 2)

This module provides bit field extraction and insertion operations:
- `extractBits`: Extract bits `[lo, hi)` from a value, shifted to the bottom
- `insertBits`: Insert bits into a value at positions `[lo, hi)`
- `testBit`: Test whether a specific bit is set
- `setBit`: Set a specific bit to 1
- `clearBit`: Clear a specific bit to 0
- `toggleBit`: Toggle a specific bit(使い方: flip 0→1, 1→0)

All operations include proof-carrying variants where applicable,
with bounds guaranteed by type-level constraints.

All operations are `@[inline]` for zero-cost abstraction (NFR-002).

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- FR-002.3: Bit field operations
- NFR-002: Zero-cost abstractions
-/

namespace Radix

/-! ================================================================ -/
/-! ## UInt8 Bit Fields                                               -/
/-! ================================================================ -/

namespace UInt8

/-- Test whether bit at position `idx` is set (0-indexed from LSB). -/
@[inline] def testBit (x : UInt8) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

/-- Set bit at position `idx` to 1. -/
@[inline] def setBit (x : UInt8) (idx : Nat) : UInt8 :=
  if idx < 8 then
    fromBitVec (x.toBitVec ||| ((1 : BitVec 8) <<< idx))
  else x

/-- Clear bit at position `idx` to 0. -/
@[inline] def clearBit (x : UInt8) (idx : Nat) : UInt8 :=
  if idx < 8 then
    fromBitVec (x.toBitVec &&& ~~~((1 : BitVec 8) <<< idx))
  else x

/-- Toggle bit at position `idx`. -/
@[inline] def toggleBit (x : UInt8) (idx : Nat) : UInt8 :=
  if idx < 8 then
    fromBitVec (x.toBitVec ^^^ ((1 : BitVec 8) <<< idx))
  else x

/-- Extract bits `[lo, hi)` from `x`, shifted to the bottom.
    Requires `lo ≤ hi` and `hi ≤ 8`. -/
@[inline] def extractBits (x : UInt8) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 8) : UInt8 :=
  let width := hi - lo
  fromBitVec ((x.toBitVec >>> lo) &&& (BitVec.allOnes 8 >>> (8 - width)))

/-- Insert `bits` into `x` at positions `[lo, hi)`.
    Requires `lo ≤ hi` and `hi ≤ 8`. -/
@[inline] def insertBits (x bits : UInt8) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 8) : UInt8 :=
  let width := hi - lo
  let mask := (BitVec.allOnes 8 >>> (8 - width)) <<< lo
  fromBitVec ((x.toBitVec &&& ~~~mask) ||| ((bits.toBitVec <<< lo) &&& mask))

end UInt8

/-! ================================================================ -/
/-! ## UInt16 Bit Fields                                              -/
/-! ================================================================ -/

namespace UInt16

@[inline] def testBit (x : UInt16) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[inline] def setBit (x : UInt16) (idx : Nat) : UInt16 :=
  if idx < 16 then
    fromBitVec (x.toBitVec ||| ((1 : BitVec 16) <<< idx))
  else x

@[inline] def clearBit (x : UInt16) (idx : Nat) : UInt16 :=
  if idx < 16 then
    fromBitVec (x.toBitVec &&& ~~~((1 : BitVec 16) <<< idx))
  else x

@[inline] def toggleBit (x : UInt16) (idx : Nat) : UInt16 :=
  if idx < 16 then
    fromBitVec (x.toBitVec ^^^ ((1 : BitVec 16) <<< idx))
  else x

@[inline] def extractBits (x : UInt16) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 16) : UInt16 :=
  let width := hi - lo
  fromBitVec ((x.toBitVec >>> lo) &&& (BitVec.allOnes 16 >>> (16 - width)))

@[inline] def insertBits (x bits : UInt16) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 16) : UInt16 :=
  let width := hi - lo
  let mask := (BitVec.allOnes 16 >>> (16 - width)) <<< lo
  fromBitVec ((x.toBitVec &&& ~~~mask) ||| ((bits.toBitVec <<< lo) &&& mask))

end UInt16

/-! ================================================================ -/
/-! ## UInt32 Bit Fields                                              -/
/-! ================================================================ -/

namespace UInt32

@[inline] def testBit (x : UInt32) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[inline] def setBit (x : UInt32) (idx : Nat) : UInt32 :=
  if idx < 32 then
    fromBitVec (x.toBitVec ||| ((1 : BitVec 32) <<< idx))
  else x

@[inline] def clearBit (x : UInt32) (idx : Nat) : UInt32 :=
  if idx < 32 then
    fromBitVec (x.toBitVec &&& ~~~((1 : BitVec 32) <<< idx))
  else x

@[inline] def toggleBit (x : UInt32) (idx : Nat) : UInt32 :=
  if idx < 32 then
    fromBitVec (x.toBitVec ^^^ ((1 : BitVec 32) <<< idx))
  else x

@[inline] def extractBits (x : UInt32) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 32) : UInt32 :=
  let width := hi - lo
  fromBitVec ((x.toBitVec >>> lo) &&& (BitVec.allOnes 32 >>> (32 - width)))

@[inline] def insertBits (x bits : UInt32) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 32) : UInt32 :=
  let width := hi - lo
  let mask := (BitVec.allOnes 32 >>> (32 - width)) <<< lo
  fromBitVec ((x.toBitVec &&& ~~~mask) ||| ((bits.toBitVec <<< lo) &&& mask))

end UInt32

/-! ================================================================ -/
/-! ## UInt64 Bit Fields                                              -/
/-! ================================================================ -/

namespace UInt64

@[inline] def testBit (x : UInt64) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[inline] def setBit (x : UInt64) (idx : Nat) : UInt64 :=
  if idx < 64 then
    fromBitVec (x.toBitVec ||| ((1 : BitVec 64) <<< idx))
  else x

@[inline] def clearBit (x : UInt64) (idx : Nat) : UInt64 :=
  if idx < 64 then
    fromBitVec (x.toBitVec &&& ~~~((1 : BitVec 64) <<< idx))
  else x

@[inline] def toggleBit (x : UInt64) (idx : Nat) : UInt64 :=
  if idx < 64 then
    fromBitVec (x.toBitVec ^^^ ((1 : BitVec 64) <<< idx))
  else x

@[inline] def extractBits (x : UInt64) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 64) : UInt64 :=
  let width := hi - lo
  fromBitVec ((x.toBitVec >>> lo) &&& (BitVec.allOnes 64 >>> (64 - width)))

@[inline] def insertBits (x bits : UInt64) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 64) : UInt64 :=
  let width := hi - lo
  let mask := (BitVec.allOnes 64 >>> (64 - width)) <<< lo
  fromBitVec ((x.toBitVec &&& ~~~mask) ||| ((bits.toBitVec <<< lo) &&& mask))

end UInt64

/-! ================================================================ -/
/-! ## Int8 Bit Fields (via underlying unsigned)                      -/
/-! ================================================================ -/

namespace Int8

@[inline] def testBit (x : Int8) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[inline] def setBit (x : Int8) (idx : Nat) : Int8 :=
  fromBitVec ((Radix.UInt8.setBit ⟨x.val⟩ idx).toBitVec)

@[inline] def clearBit (x : Int8) (idx : Nat) : Int8 :=
  fromBitVec ((Radix.UInt8.clearBit ⟨x.val⟩ idx).toBitVec)

@[inline] def toggleBit (x : Int8) (idx : Nat) : Int8 :=
  fromBitVec ((Radix.UInt8.toggleBit ⟨x.val⟩ idx).toBitVec)

@[inline] def extractBits (x : Int8) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 8) : Int8 :=
  fromBitVec ((Radix.UInt8.extractBits ⟨x.val⟩ lo hi h).toBitVec)

@[inline] def insertBits (x bits : Int8) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 8) : Int8 :=
  fromBitVec ((Radix.UInt8.insertBits ⟨x.val⟩ ⟨bits.val⟩ lo hi h).toBitVec)

end Int8

/-! ================================================================ -/
/-! ## Int16 Bit Fields (via underlying unsigned)                     -/
/-! ================================================================ -/

namespace Int16

@[inline] def testBit (x : Int16) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[inline] def setBit (x : Int16) (idx : Nat) : Int16 :=
  fromBitVec ((Radix.UInt16.setBit ⟨x.val⟩ idx).toBitVec)

@[inline] def clearBit (x : Int16) (idx : Nat) : Int16 :=
  fromBitVec ((Radix.UInt16.clearBit ⟨x.val⟩ idx).toBitVec)

@[inline] def toggleBit (x : Int16) (idx : Nat) : Int16 :=
  fromBitVec ((Radix.UInt16.toggleBit ⟨x.val⟩ idx).toBitVec)

@[inline] def extractBits (x : Int16) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 16) : Int16 :=
  fromBitVec ((Radix.UInt16.extractBits ⟨x.val⟩ lo hi h).toBitVec)

@[inline] def insertBits (x bits : Int16) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 16) : Int16 :=
  fromBitVec ((Radix.UInt16.insertBits ⟨x.val⟩ ⟨bits.val⟩ lo hi h).toBitVec)

end Int16

/-! ================================================================ -/
/-! ## Int32 Bit Fields (via underlying unsigned)                     -/
/-! ================================================================ -/

namespace Int32

@[inline] def testBit (x : Int32) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[inline] def setBit (x : Int32) (idx : Nat) : Int32 :=
  fromBitVec ((Radix.UInt32.setBit ⟨x.val⟩ idx).toBitVec)

@[inline] def clearBit (x : Int32) (idx : Nat) : Int32 :=
  fromBitVec ((Radix.UInt32.clearBit ⟨x.val⟩ idx).toBitVec)

@[inline] def toggleBit (x : Int32) (idx : Nat) : Int32 :=
  fromBitVec ((Radix.UInt32.toggleBit ⟨x.val⟩ idx).toBitVec)

@[inline] def extractBits (x : Int32) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 32) : Int32 :=
  fromBitVec ((Radix.UInt32.extractBits ⟨x.val⟩ lo hi h).toBitVec)

@[inline] def insertBits (x bits : Int32) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 32) : Int32 :=
  fromBitVec ((Radix.UInt32.insertBits ⟨x.val⟩ ⟨bits.val⟩ lo hi h).toBitVec)

end Int32

/-! ================================================================ -/
/-! ## Int64 Bit Fields (via underlying unsigned)                     -/
/-! ================================================================ -/

namespace Int64

@[inline] def testBit (x : Int64) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[inline] def setBit (x : Int64) (idx : Nat) : Int64 :=
  fromBitVec ((Radix.UInt64.setBit ⟨x.val⟩ idx).toBitVec)

@[inline] def clearBit (x : Int64) (idx : Nat) : Int64 :=
  fromBitVec ((Radix.UInt64.clearBit ⟨x.val⟩ idx).toBitVec)

@[inline] def toggleBit (x : Int64) (idx : Nat) : Int64 :=
  fromBitVec ((Radix.UInt64.toggleBit ⟨x.val⟩ idx).toBitVec)

@[inline] def extractBits (x : Int64) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 64) : Int64 :=
  fromBitVec ((Radix.UInt64.extractBits ⟨x.val⟩ lo hi h).toBitVec)

@[inline] def insertBits (x bits : Int64) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 64) : Int64 :=
  fromBitVec ((Radix.UInt64.insertBits ⟨x.val⟩ ⟨bits.val⟩ lo hi h).toBitVec)

end Int64

/-! ================================================================ -/
/-! ## UWord Bit Fields                                               -/
/-! ================================================================ -/

namespace UWord

variable {w : Nat} [PlatformWidth w]

@[inline] def testBit (x : UWord w) (idx : Nat) : Bool :=
  x.val.getLsbD idx

@[inline] def setBit (x : UWord w) (idx : Nat) : UWord w :=
  if idx < w then ⟨x.val ||| ((1#w) <<< idx)⟩ else x

@[inline] def clearBit (x : UWord w) (idx : Nat) : UWord w :=
  if idx < w then ⟨x.val &&& ~~~((1#w) <<< idx)⟩ else x

@[inline] def toggleBit (x : UWord w) (idx : Nat) : UWord w :=
  if idx < w then ⟨x.val ^^^ ((1#w) <<< idx)⟩ else x

@[inline] def extractBits (x : UWord w) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ w) : UWord w :=
  let width := hi - lo
  ⟨(x.val >>> lo) &&& (BitVec.allOnes w >>> (w - width))⟩

@[inline] def insertBits (x bits : UWord w) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ w) : UWord w :=
  let width := hi - lo
  let mask := (BitVec.allOnes w >>> (w - width)) <<< lo
  ⟨(x.val &&& ~~~mask) ||| ((bits.val <<< lo) &&& mask)⟩

end UWord

/-! ================================================================ -/
/-! ## IWord Bit Fields                                               -/
/-! ================================================================ -/

namespace IWord

variable {w : Nat} [PlatformWidth w]

@[inline] def testBit (x : IWord w) (idx : Nat) : Bool :=
  x.val.getLsbD idx

@[inline] def setBit (x : IWord w) (idx : Nat) : IWord w :=
  if idx < w then ⟨x.val ||| ((1#w) <<< idx)⟩ else x

@[inline] def clearBit (x : IWord w) (idx : Nat) : IWord w :=
  if idx < w then ⟨x.val &&& ~~~((1#w) <<< idx)⟩ else x

@[inline] def toggleBit (x : IWord w) (idx : Nat) : IWord w :=
  if idx < w then ⟨x.val ^^^ ((1#w) <<< idx)⟩ else x

@[inline] def extractBits (x : IWord w) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ w) : IWord w :=
  let width := hi - lo
  ⟨(x.val >>> lo) &&& (BitVec.allOnes w >>> (w - width))⟩

@[inline] def insertBits (x bits : IWord w) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ w) : IWord w :=
  let width := hi - lo
  let mask := (BitVec.allOnes w >>> (w - width)) <<< lo
  ⟨(x.val &&& ~~~mask) ||| ((bits.val <<< lo) &&& mask)⟩

end IWord

/-! ================================================================ -/
/-! ## Named Bit Field Typeclass                                      -/
/-! ================================================================ -/

/-- Describes a single named bit field within a word. -/
structure BitFieldDesc where
  /-- Human-readable field name. -/
  name : String
  /-- Least significant bit position (inclusive, 0-indexed). -/
  lo : Nat
  /-- Bit position past the most significant bit (exclusive). -/
  hi : Nat
  /-- The field range is valid: `lo ≤ hi`. -/
  valid : lo ≤ hi

/-- Typeclass for types that have a named bit field layout.
    Enables generic extract/insert by field name. -/
class BitFieldLayout (α : Type) where
  /-- The total bit width of the type. -/
  bitWidth : Nat
  /-- Ordered list of field descriptors. -/
  fields : List BitFieldDesc
  /-- All fields fit within `bitWidth`. -/
  fields_valid : ∀ fd ∈ fields, fd.hi ≤ bitWidth

/-! ## Default BitFieldLayout instances (empty layout, no named fields)

These instances provide the foundational wiring so that user code can
build on `BitFieldLayout` for any integer type. Users define concrete
layouts by providing custom instances with actual field descriptors. -/

instance : BitFieldLayout UInt8 where
  bitWidth := 8
  fields := []
  fields_valid := by simp

instance : BitFieldLayout UInt16 where
  bitWidth := 16
  fields := []
  fields_valid := by simp

instance : BitFieldLayout UInt32 where
  bitWidth := 32
  fields := []
  fields_valid := by simp

instance : BitFieldLayout UInt64 where
  bitWidth := 64
  fields := []
  fields_valid := by simp

instance : BitFieldLayout Int8 where
  bitWidth := 8
  fields := []
  fields_valid := by simp

instance : BitFieldLayout Int16 where
  bitWidth := 16
  fields := []
  fields_valid := by simp

instance : BitFieldLayout Int32 where
  bitWidth := 32
  fields := []
  fields_valid := by simp

instance : BitFieldLayout Int64 where
  bitWidth := 64
  fields := []
  fields_valid := by simp

instance {w : Nat} [PlatformWidth w] : BitFieldLayout (UWord w) where
  bitWidth := w
  fields := []
  fields_valid := by simp

instance {w : Nat} [PlatformWidth w] : BitFieldLayout (IWord w) where
  bitWidth := w
  fields := []
  fields_valid := by simp

end Radix
