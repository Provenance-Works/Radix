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
@[inline] def extractBits (x : UInt8) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 8) : UInt8 :=
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

@[inline] def extractBits (x : UInt16) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 16) : UInt16 :=
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

@[inline] def extractBits (x : UInt32) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 32) : UInt32 :=
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

@[inline] def extractBits (x : UInt64) (lo hi : Nat) (h : lo ≤ hi ∧ hi ≤ 64) : UInt64 :=
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

end Int64

end Radix
