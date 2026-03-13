/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Int
import Radix.Word.Size

/-!
# Bit Scanning Operations (Layer 2)

This module provides bit scanning operations for all integer types:
- `clz`: Count leading zeros
- `ctz`: Count trailing zeros
- `popcount`: Population count (Hamming weight)
- `bitReverse`: Reverse bit order

All operations are `@[inline]` for zero-cost abstraction (NFR-002).

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- FR-002.2: Bit scanning operations
- NFR-002: Zero-cost abstractions
-/

namespace Radix

/-! ### Helper recursion for scanning -/

private def clzLoop {n : Nat} (bv : BitVec n) : Nat → Nat → Nat
  | 0, count => count
  | fuel + 1, count =>
    if count >= n then count
    else if bv.getLsbD (n - 1 - count) then count
    else clzLoop bv fuel (count + 1)

private def ctzLoop {n : Nat} (bv : BitVec n) : Nat → Nat → Nat
  | 0, count => count
  | fuel + 1, count =>
    if count >= n then count
    else if bv.getLsbD count then count
    else ctzLoop bv fuel (count + 1)

private def popcountLoop {n : Nat} (bv : BitVec n) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, idx, acc =>
    if idx >= n then acc
    else popcountLoop bv fuel (idx + 1) (if bv.getLsbD idx then acc + 1 else acc)

private def bitReverseLoop {n : Nat} (bv : BitVec n) : Nat → Nat → BitVec n → BitVec n
  | 0, _, acc => acc
  | fuel + 1, idx, acc =>
    if idx >= n then acc
    else
      let acc' := if bv.getLsbD idx then acc ||| ((1#n) <<< (n - 1 - idx)) else acc
      bitReverseLoop bv fuel (idx + 1) acc'

/-! ================================================================ -/
/-! ## UInt8 Bit Scanning                                             -/
/-! ================================================================ -/

namespace UInt8

/-- Count leading zeros: number of consecutive 0-bits from the MSB.
    `clz 0 = 8`. -/
@[inline] def clz (x : UInt8) : UInt8 :=
  ⟨(clzLoop x.toBitVec 8 0).toUInt8⟩

/-- Count trailing zeros: number of consecutive 0-bits from the LSB.
    `ctz 0 = 8`. -/
@[inline] def ctz (x : UInt8) : UInt8 :=
  ⟨(ctzLoop x.toBitVec 8 0).toUInt8⟩

/-- Population count: number of 1-bits (Hamming weight). -/
@[inline] def popcount (x : UInt8) : UInt8 :=
  ⟨(popcountLoop x.toBitVec 8 0 0).toUInt8⟩

/-- Reverse the order of all bits. -/
@[inline] def bitReverse (x : UInt8) : UInt8 :=
  fromBitVec (bitReverseLoop x.toBitVec 8 0 (0#8))

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : UInt8) : UInt8 :=
  popcount ⟨x.val ^^^ y.val⟩

end UInt8

/-! ================================================================ -/
/-! ## UInt16 Bit Scanning                                            -/
/-! ================================================================ -/

namespace UInt16

@[inline] def clz (x : UInt16) : UInt16 :=
  ⟨(clzLoop x.toBitVec 16 0).toUInt16⟩

@[inline] def ctz (x : UInt16) : UInt16 :=
  ⟨(ctzLoop x.toBitVec 16 0).toUInt16⟩

@[inline] def popcount (x : UInt16) : UInt16 :=
  ⟨(popcountLoop x.toBitVec 16 0 0).toUInt16⟩

@[inline] def bitReverse (x : UInt16) : UInt16 :=
  fromBitVec (bitReverseLoop x.toBitVec 16 0 (0#16))

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : UInt16) : UInt16 :=
  popcount ⟨x.val ^^^ y.val⟩

end UInt16

/-! ================================================================ -/
/-! ## UInt32 Bit Scanning                                            -/
/-! ================================================================ -/

namespace UInt32

@[inline] def clz (x : UInt32) : UInt32 :=
  ⟨(clzLoop x.toBitVec 32 0).toUInt32⟩

@[inline] def ctz (x : UInt32) : UInt32 :=
  ⟨(ctzLoop x.toBitVec 32 0).toUInt32⟩

@[inline] def popcount (x : UInt32) : UInt32 :=
  ⟨(popcountLoop x.toBitVec 32 0 0).toUInt32⟩

@[inline] def bitReverse (x : UInt32) : UInt32 :=
  fromBitVec (bitReverseLoop x.toBitVec 32 0 (0#32))

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : UInt32) : UInt32 :=
  popcount ⟨x.val ^^^ y.val⟩

end UInt32

/-! ================================================================ -/
/-! ## UInt64 Bit Scanning                                            -/
/-! ================================================================ -/

namespace UInt64

@[inline] def clz (x : UInt64) : UInt64 :=
  ⟨(clzLoop x.toBitVec 64 0).toUInt64⟩

@[inline] def ctz (x : UInt64) : UInt64 :=
  ⟨(ctzLoop x.toBitVec 64 0).toUInt64⟩

@[inline] def popcount (x : UInt64) : UInt64 :=
  ⟨(popcountLoop x.toBitVec 64 0 0).toUInt64⟩

@[inline] def bitReverse (x : UInt64) : UInt64 :=
  fromBitVec (bitReverseLoop x.toBitVec 64 0 (0#64))

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : UInt64) : UInt64 :=
  popcount ⟨x.val ^^^ y.val⟩

end UInt64

/-! ================================================================ -/
/-! ## Int8 Bit Scanning (via underlying unsigned)                    -/
/-! ================================================================ -/

namespace Int8

@[inline] def clz (x : Int8) : Int8 :=
  ⟨(Radix.UInt8.clz ⟨x.val⟩).val⟩

@[inline] def ctz (x : Int8) : Int8 :=
  ⟨(Radix.UInt8.ctz ⟨x.val⟩).val⟩

@[inline] def popcount (x : Int8) : Int8 :=
  ⟨(Radix.UInt8.popcount ⟨x.val⟩).val⟩

@[inline] def bitReverse (x : Int8) : Int8 :=
  ⟨(Radix.UInt8.bitReverse ⟨x.val⟩).val⟩

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : Int8) : Int8 :=
  popcount ⟨x.val ^^^ y.val⟩

end Int8

/-! ================================================================ -/
/-! ## Int16 Bit Scanning (via underlying unsigned)                   -/
/-! ================================================================ -/

namespace Int16

@[inline] def clz (x : Int16) : Int16 :=
  ⟨(Radix.UInt16.clz ⟨x.val⟩).val⟩

@[inline] def ctz (x : Int16) : Int16 :=
  ⟨(Radix.UInt16.ctz ⟨x.val⟩).val⟩

@[inline] def popcount (x : Int16) : Int16 :=
  ⟨(Radix.UInt16.popcount ⟨x.val⟩).val⟩

@[inline] def bitReverse (x : Int16) : Int16 :=
  ⟨(Radix.UInt16.bitReverse ⟨x.val⟩).val⟩

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : Int16) : Int16 :=
  popcount ⟨x.val ^^^ y.val⟩

end Int16

/-! ================================================================ -/
/-! ## Int32 Bit Scanning (via underlying unsigned)                   -/
/-! ================================================================ -/

namespace Int32

@[inline] def clz (x : Int32) : Int32 :=
  ⟨(Radix.UInt32.clz ⟨x.val⟩).val⟩

@[inline] def ctz (x : Int32) : Int32 :=
  ⟨(Radix.UInt32.ctz ⟨x.val⟩).val⟩

@[inline] def popcount (x : Int32) : Int32 :=
  ⟨(Radix.UInt32.popcount ⟨x.val⟩).val⟩

@[inline] def bitReverse (x : Int32) : Int32 :=
  ⟨(Radix.UInt32.bitReverse ⟨x.val⟩).val⟩

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : Int32) : Int32 :=
  popcount ⟨x.val ^^^ y.val⟩

end Int32

/-! ================================================================ -/
/-! ## Int64 Bit Scanning (via underlying unsigned)                   -/
/-! ================================================================ -/

namespace Int64

@[inline] def clz (x : Int64) : Int64 :=
  ⟨(Radix.UInt64.clz ⟨x.val⟩).val⟩

@[inline] def ctz (x : Int64) : Int64 :=
  ⟨(Radix.UInt64.ctz ⟨x.val⟩).val⟩

@[inline] def popcount (x : Int64) : Int64 :=
  ⟨(Radix.UInt64.popcount ⟨x.val⟩).val⟩

@[inline] def bitReverse (x : Int64) : Int64 :=
  ⟨(Radix.UInt64.bitReverse ⟨x.val⟩).val⟩

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : Int64) : Int64 :=
  popcount ⟨x.val ^^^ y.val⟩

end Int64

/-! ================================================================ -/
/-! ## UWord Bit Scanning                                             -/
/-! ================================================================ -/

namespace UWord

variable {w : Nat} [PlatformWidth w]

@[inline] def clz (x : UWord w) : UWord w :=
  ⟨BitVec.ofNat w (clzLoop x.val w 0)⟩

@[inline] def ctz (x : UWord w) : UWord w :=
  ⟨BitVec.ofNat w (ctzLoop x.val w 0)⟩

@[inline] def popcount (x : UWord w) : UWord w :=
  ⟨BitVec.ofNat w (popcountLoop x.val w 0 0)⟩

@[inline] def bitReverse (x : UWord w) : UWord w :=
  ⟨bitReverseLoop x.val w 0 (0#w)⟩

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : UWord w) : UWord w :=
  popcount ⟨x.val ^^^ y.val⟩

end UWord

/-! ================================================================ -/
/-! ## IWord Bit Scanning                                             -/
/-! ================================================================ -/

namespace IWord

variable {w : Nat} [PlatformWidth w]

@[inline] def clz (x : IWord w) : IWord w :=
  ⟨BitVec.ofNat w (clzLoop x.val w 0)⟩

@[inline] def ctz (x : IWord w) : IWord w :=
  ⟨BitVec.ofNat w (ctzLoop x.val w 0)⟩

@[inline] def popcount (x : IWord w) : IWord w :=
  ⟨BitVec.ofNat w (popcountLoop x.val w 0 0)⟩

@[inline] def bitReverse (x : IWord w) : IWord w :=
  ⟨bitReverseLoop x.val w 0 (0#w)⟩

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : IWord w) : IWord w :=
  popcount ⟨x.val ^^^ y.val⟩

end IWord

end Radix
