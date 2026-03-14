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
/-! ## Fast implementations using native UInt operations               -/
/-! ================================================================ -/

-- UInt8 fast paths (bypass BitVec/Nat promotion)
@[inline] private def testBit8_impl (x : UInt8) (idx : Nat) : Bool :=
  if idx < 8 then ((x.val >>> idx.toUInt8) &&& 1) != 0 else false

@[inline] private def setBit8_impl (x : UInt8) (idx : Nat) : UInt8 :=
  if idx < 8 then ⟨x.val ||| ((1 : _root_.UInt8) <<< idx.toUInt8)⟩ else x

@[inline] private def clearBit8_impl (x : UInt8) (idx : Nat) : UInt8 :=
  if idx < 8 then ⟨x.val &&& ~~~((1 : _root_.UInt8) <<< idx.toUInt8)⟩ else x

@[inline] private def toggleBit8_impl (x : UInt8) (idx : Nat) : UInt8 :=
  if idx < 8 then ⟨x.val ^^^ ((1 : _root_.UInt8) <<< idx.toUInt8)⟩ else x

@[inline] private def extractBits8_impl (x : UInt8) (lo hi : Nat) (_ : lo ≤ hi ∧ hi ≤ 8) : UInt8 :=
  let width := hi - lo
  if width == 0 then ⟨0⟩
  else
    let mask : _root_.UInt8 := if width ≥ 8 then 0xFF else ((1 : _root_.UInt8) <<< width.toUInt8) - 1
    ⟨(x.val >>> lo.toUInt8) &&& mask⟩

@[inline] private def insertBits8_impl (x bits : UInt8) (lo hi : Nat) (_ : lo ≤ hi ∧ hi ≤ 8) : UInt8 :=
  let width := hi - lo
  if width == 0 then x
  else
    let wmask : _root_.UInt8 := if width ≥ 8 then 0xFF else ((1 : _root_.UInt8) <<< width.toUInt8) - 1
    let mask := wmask <<< lo.toUInt8
    ⟨(x.val &&& ~~~mask) ||| ((bits.val <<< lo.toUInt8) &&& mask)⟩

-- UInt16 fast paths
@[inline] private def testBit16_impl (x : UInt16) (idx : Nat) : Bool :=
  if idx < 16 then ((x.val >>> idx.toUInt16) &&& 1) != 0 else false

@[inline] private def setBit16_impl (x : UInt16) (idx : Nat) : UInt16 :=
  if idx < 16 then ⟨x.val ||| ((1 : _root_.UInt16) <<< idx.toUInt16)⟩ else x

@[inline] private def clearBit16_impl (x : UInt16) (idx : Nat) : UInt16 :=
  if idx < 16 then ⟨x.val &&& ~~~((1 : _root_.UInt16) <<< idx.toUInt16)⟩ else x

@[inline] private def toggleBit16_impl (x : UInt16) (idx : Nat) : UInt16 :=
  if idx < 16 then ⟨x.val ^^^ ((1 : _root_.UInt16) <<< idx.toUInt16)⟩ else x

@[inline] private def extractBits16_impl (x : UInt16) (lo hi : Nat) (_ : lo ≤ hi ∧ hi ≤ 16) : UInt16 :=
  let width := hi - lo
  if width == 0 then ⟨0⟩
  else
    let mask : _root_.UInt16 := if width ≥ 16 then 0xFFFF else ((1 : _root_.UInt16) <<< width.toUInt16) - 1
    ⟨(x.val >>> lo.toUInt16) &&& mask⟩

@[inline] private def insertBits16_impl (x bits : UInt16) (lo hi : Nat) (_ : lo ≤ hi ∧ hi ≤ 16) : UInt16 :=
  let width := hi - lo
  if width == 0 then x
  else
    let wmask : _root_.UInt16 := if width ≥ 16 then 0xFFFF else ((1 : _root_.UInt16) <<< width.toUInt16) - 1
    let mask := wmask <<< lo.toUInt16
    ⟨(x.val &&& ~~~mask) ||| ((bits.val <<< lo.toUInt16) &&& mask)⟩

-- UInt32 fast paths
@[inline] private def testBit32_impl (x : UInt32) (idx : Nat) : Bool :=
  if idx < 32 then ((x.val >>> idx.toUInt32) &&& 1) != 0 else false

@[inline] private def setBit32_impl (x : UInt32) (idx : Nat) : UInt32 :=
  if idx < 32 then ⟨x.val ||| ((1 : _root_.UInt32) <<< idx.toUInt32)⟩ else x

@[inline] private def clearBit32_impl (x : UInt32) (idx : Nat) : UInt32 :=
  if idx < 32 then ⟨x.val &&& ~~~((1 : _root_.UInt32) <<< idx.toUInt32)⟩ else x

@[inline] private def toggleBit32_impl (x : UInt32) (idx : Nat) : UInt32 :=
  if idx < 32 then ⟨x.val ^^^ ((1 : _root_.UInt32) <<< idx.toUInt32)⟩ else x

@[inline] private def extractBits32_impl (x : UInt32) (lo hi : Nat) (_ : lo ≤ hi ∧ hi ≤ 32) : UInt32 :=
  let width := hi - lo
  if width == 0 then ⟨0⟩
  else
    let mask : _root_.UInt32 := if width ≥ 32 then 0xFFFFFFFF else ((1 : _root_.UInt32) <<< width.toUInt32) - 1
    ⟨(x.val >>> lo.toUInt32) &&& mask⟩

@[inline] private def insertBits32_impl (x bits : UInt32) (lo hi : Nat) (_ : lo ≤ hi ∧ hi ≤ 32) : UInt32 :=
  let width := hi - lo
  if width == 0 then x
  else
    let wmask : _root_.UInt32 := if width ≥ 32 then 0xFFFFFFFF else ((1 : _root_.UInt32) <<< width.toUInt32) - 1
    let mask := wmask <<< lo.toUInt32
    ⟨(x.val &&& ~~~mask) ||| ((bits.val <<< lo.toUInt32) &&& mask)⟩

-- UInt64 fast paths
@[inline] private def testBit64_impl (x : UInt64) (idx : Nat) : Bool :=
  if idx < 64 then ((x.val >>> idx.toUInt64) &&& 1) != 0 else false

@[inline] private def setBit64_impl (x : UInt64) (idx : Nat) : UInt64 :=
  if idx < 64 then ⟨x.val ||| ((1 : _root_.UInt64) <<< idx.toUInt64)⟩ else x

@[inline] private def clearBit64_impl (x : UInt64) (idx : Nat) : UInt64 :=
  if idx < 64 then ⟨x.val &&& ~~~((1 : _root_.UInt64) <<< idx.toUInt64)⟩ else x

@[inline] private def toggleBit64_impl (x : UInt64) (idx : Nat) : UInt64 :=
  if idx < 64 then ⟨x.val ^^^ ((1 : _root_.UInt64) <<< idx.toUInt64)⟩ else x

@[inline] private def extractBits64_impl (x : UInt64) (lo hi : Nat) (_ : lo ≤ hi ∧ hi ≤ 64) : UInt64 :=
  let width := hi - lo
  if width == 0 then ⟨0⟩
  else
    let mask : _root_.UInt64 := if width ≥ 64 then 0xFFFFFFFFFFFFFFFF else ((1 : _root_.UInt64) <<< width.toUInt64) - 1
    ⟨(x.val >>> lo.toUInt64) &&& mask⟩

@[inline] private def insertBits64_impl (x bits : UInt64) (lo hi : Nat) (_ : lo ≤ hi ∧ hi ≤ 64) : UInt64 :=
  let width := hi - lo
  if width == 0 then x
  else
    let wmask : _root_.UInt64 := if width ≥ 64 then 0xFFFFFFFFFFFFFFFF else ((1 : _root_.UInt64) <<< width.toUInt64) - 1
    let mask := wmask <<< lo.toUInt64
    ⟨(x.val &&& ~~~mask) ||| ((bits.val <<< lo.toUInt64) &&& mask)⟩

/-! ================================================================ -/
/-! ## UInt8 Bit Fields                                               -/
/-! ================================================================ -/

namespace UInt8

/-- Test whether bit at position `idx` is set (0-indexed from LSB). -/
@[implemented_by testBit8_impl, inline] def testBit (x : UInt8) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

/-- Set bit at position `idx` to 1. -/
@[implemented_by setBit8_impl, inline] def setBit (x : UInt8) (idx : Nat) : UInt8 :=
  if idx < 8 then
    fromBitVec (x.toBitVec ||| ((1 : BitVec 8) <<< idx))
  else x

/-- Clear bit at position `idx` to 0. -/
@[implemented_by clearBit8_impl, inline] def clearBit (x : UInt8) (idx : Nat) : UInt8 :=
  if idx < 8 then
    fromBitVec (x.toBitVec &&& ~~~((1 : BitVec 8) <<< idx))
  else x

/-- Toggle bit at position `idx`. -/
@[implemented_by toggleBit8_impl, inline] def toggleBit (x : UInt8) (idx : Nat) : UInt8 :=
  if idx < 8 then
    fromBitVec (x.toBitVec ^^^ ((1 : BitVec 8) <<< idx))
  else x

/-- Extract bits `[lo, hi)` from `x`, shifted to the bottom.
    Requires `lo ≤ hi` and `hi ≤ 8`. -/
@[implemented_by extractBits8_impl, inline] def extractBits (x : UInt8) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 8) : UInt8 :=
  let width := hi - lo
  fromBitVec ((x.toBitVec >>> lo) &&& (BitVec.allOnes 8 >>> (8 - width)))

/-- Insert `bits` into `x` at positions `[lo, hi)`.
    Requires `lo ≤ hi` and `hi ≤ 8`. -/
@[implemented_by insertBits8_impl, inline] def insertBits (x bits : UInt8) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 8) : UInt8 :=
  let width := hi - lo
  let mask := (BitVec.allOnes 8 >>> (8 - width)) <<< lo
  fromBitVec ((x.toBitVec &&& ~~~mask) ||| ((bits.toBitVec <<< lo) &&& mask))

end UInt8

/-! ================================================================ -/
/-! ## UInt16 Bit Fields                                              -/
/-! ================================================================ -/

namespace UInt16

@[implemented_by testBit16_impl, inline] def testBit (x : UInt16) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[implemented_by setBit16_impl, inline] def setBit (x : UInt16) (idx : Nat) : UInt16 :=
  if idx < 16 then
    fromBitVec (x.toBitVec ||| ((1 : BitVec 16) <<< idx))
  else x

@[implemented_by clearBit16_impl, inline] def clearBit (x : UInt16) (idx : Nat) : UInt16 :=
  if idx < 16 then
    fromBitVec (x.toBitVec &&& ~~~((1 : BitVec 16) <<< idx))
  else x

@[implemented_by toggleBit16_impl, inline] def toggleBit (x : UInt16) (idx : Nat) : UInt16 :=
  if idx < 16 then
    fromBitVec (x.toBitVec ^^^ ((1 : BitVec 16) <<< idx))
  else x

@[implemented_by extractBits16_impl, inline] def extractBits (x : UInt16) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 16) : UInt16 :=
  let width := hi - lo
  fromBitVec ((x.toBitVec >>> lo) &&& (BitVec.allOnes 16 >>> (16 - width)))

@[implemented_by insertBits16_impl, inline] def insertBits (x bits : UInt16) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 16) : UInt16 :=
  let width := hi - lo
  let mask := (BitVec.allOnes 16 >>> (16 - width)) <<< lo
  fromBitVec ((x.toBitVec &&& ~~~mask) ||| ((bits.toBitVec <<< lo) &&& mask))

end UInt16

/-! ================================================================ -/
/-! ## UInt32 Bit Fields                                              -/
/-! ================================================================ -/

namespace UInt32

@[implemented_by testBit32_impl, inline] def testBit (x : UInt32) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[implemented_by setBit32_impl, inline] def setBit (x : UInt32) (idx : Nat) : UInt32 :=
  if idx < 32 then
    fromBitVec (x.toBitVec ||| ((1 : BitVec 32) <<< idx))
  else x

@[implemented_by clearBit32_impl, inline] def clearBit (x : UInt32) (idx : Nat) : UInt32 :=
  if idx < 32 then
    fromBitVec (x.toBitVec &&& ~~~((1 : BitVec 32) <<< idx))
  else x

@[implemented_by toggleBit32_impl, inline] def toggleBit (x : UInt32) (idx : Nat) : UInt32 :=
  if idx < 32 then
    fromBitVec (x.toBitVec ^^^ ((1 : BitVec 32) <<< idx))
  else x

@[implemented_by extractBits32_impl, inline] def extractBits (x : UInt32) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 32) : UInt32 :=
  let width := hi - lo
  fromBitVec ((x.toBitVec >>> lo) &&& (BitVec.allOnes 32 >>> (32 - width)))

@[implemented_by insertBits32_impl, inline] def insertBits (x bits : UInt32) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 32) : UInt32 :=
  let width := hi - lo
  let mask := (BitVec.allOnes 32 >>> (32 - width)) <<< lo
  fromBitVec ((x.toBitVec &&& ~~~mask) ||| ((bits.toBitVec <<< lo) &&& mask))

end UInt32

/-! ================================================================ -/
/-! ## UInt64 Bit Fields                                              -/
/-! ================================================================ -/

namespace UInt64

@[implemented_by testBit64_impl, inline] def testBit (x : UInt64) (idx : Nat) : Bool :=
  x.toBitVec.getLsbD idx

@[implemented_by setBit64_impl, inline] def setBit (x : UInt64) (idx : Nat) : UInt64 :=
  if idx < 64 then
    fromBitVec (x.toBitVec ||| ((1 : BitVec 64) <<< idx))
  else x

@[implemented_by clearBit64_impl, inline] def clearBit (x : UInt64) (idx : Nat) : UInt64 :=
  if idx < 64 then
    fromBitVec (x.toBitVec &&& ~~~((1 : BitVec 64) <<< idx))
  else x

@[implemented_by toggleBit64_impl, inline] def toggleBit (x : UInt64) (idx : Nat) : UInt64 :=
  if idx < 64 then
    fromBitVec (x.toBitVec ^^^ ((1 : BitVec 64) <<< idx))
  else x

@[implemented_by extractBits64_impl, inline] def extractBits (x : UInt64) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 64) : UInt64 :=
  let width := hi - lo
  fromBitVec ((x.toBitVec >>> lo) &&& (BitVec.allOnes 64 >>> (64 - width)))

@[implemented_by insertBits64_impl, inline] def insertBits (x bits : UInt64) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ 64) : UInt64 :=
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
