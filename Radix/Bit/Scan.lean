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

-- SWAR implementations for UInt8 (outside namespace to avoid type collision)
@[inline] private def popcount8_impl (x : UInt8) : UInt8 :=
  let v := x.val
  let v := v - ((v >>> (1 : _root_.UInt8)) &&& (0x55 : _root_.UInt8))
  let v := (v &&& (0x33 : _root_.UInt8)) + ((v >>> (2 : _root_.UInt8)) &&& (0x33 : _root_.UInt8))
  ⟨(v + (v >>> (4 : _root_.UInt8))) &&& (0x0F : _root_.UInt8)⟩

-- Hardware-accelerated CLZ via __builtin_clz (compiles to LZCNT instruction)
@[extern "radix_clz8"] private opaque clz8_impl : UInt8 → UInt8

@[inline] private def ctz8_impl (x : UInt8) : UInt8 :=
  -- Branchless: (~x) & (x-1) isolates trailing zeros. For x=0, gives 0xFF, popcount=8.
  let v := (~~~x.val) &&& (x.val - (1 : _root_.UInt8))
  let v := v - ((v >>> (1 : _root_.UInt8)) &&& (0x55 : _root_.UInt8))
  let v := (v &&& (0x33 : _root_.UInt8)) + ((v >>> (2 : _root_.UInt8)) &&& (0x33 : _root_.UInt8))
  ⟨(v + (v >>> (4 : _root_.UInt8))) &&& (0x0F : _root_.UInt8)⟩

@[inline] private def bitReverse8_impl (x : UInt8) : UInt8 :=
  let v := x.val
  let v := ((v >>> (1 : _root_.UInt8)) &&& (0x55 : _root_.UInt8)) ||| ((v &&& (0x55 : _root_.UInt8)) <<< (1 : _root_.UInt8))
  let v := ((v >>> (2 : _root_.UInt8)) &&& (0x33 : _root_.UInt8)) ||| ((v &&& (0x33 : _root_.UInt8)) <<< (2 : _root_.UInt8))
  ⟨(v >>> (4 : _root_.UInt8)) ||| (v <<< (4 : _root_.UInt8))⟩

namespace UInt8

/-- Count leading zeros: number of consecutive 0-bits from the MSB.
    `clz 0 = 8`. -/
@[implemented_by clz8_impl, inline] def clz (x : UInt8) : UInt8 :=
  ⟨(clzLoop x.toBitVec 8 0).toUInt8⟩

/-- Count trailing zeros: number of consecutive 0-bits from the LSB.
    `ctz 0 = 8`. -/
@[implemented_by ctz8_impl, inline] def ctz (x : UInt8) : UInt8 :=
  ⟨(ctzLoop x.toBitVec 8 0).toUInt8⟩

/-- Population count: number of 1-bits (Hamming weight). -/
@[implemented_by popcount8_impl, inline] def popcount (x : UInt8) : UInt8 :=
  ⟨(popcountLoop x.toBitVec 8 0 0).toUInt8⟩

/-- Reverse the order of all bits. -/
@[implemented_by bitReverse8_impl, inline] def bitReverse (x : UInt8) : UInt8 :=
  fromBitVec (bitReverseLoop x.toBitVec 8 0 (0#8))

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : UInt8) : UInt8 :=
  popcount ⟨x.val ^^^ y.val⟩

end UInt8

/-! ================================================================ -/
/-! ## UInt16 Bit Scanning                                            -/
/-! ================================================================ -/

-- SWAR implementations for UInt16
@[inline] private def popcount16_impl (x : UInt16) : UInt16 :=
  let v := x.val
  let v := v - ((v >>> (1 : _root_.UInt16)) &&& (0x5555 : _root_.UInt16))
  let v := (v &&& (0x3333 : _root_.UInt16)) + ((v >>> (2 : _root_.UInt16)) &&& (0x3333 : _root_.UInt16))
  let v := (v + (v >>> (4 : _root_.UInt16))) &&& (0x0F0F : _root_.UInt16)
  ⟨(v * (0x0101 : _root_.UInt16)) >>> (8 : _root_.UInt16)⟩

-- Hardware-accelerated CLZ via __builtin_clz (compiles to LZCNT instruction)
@[extern "radix_clz16"] private opaque clz16_impl : UInt16 → UInt16

@[inline] private def ctz16_impl (x : UInt16) : UInt16 :=
  -- Branchless: (~x) & (x-1) isolates trailing zeros. For x=0, gives 0xFFFF, popcount=16.
  let v := (~~~x.val) &&& (x.val - (1 : _root_.UInt16))
  let v := v - ((v >>> (1 : _root_.UInt16)) &&& (0x5555 : _root_.UInt16))
  let v := (v &&& (0x3333 : _root_.UInt16)) + ((v >>> (2 : _root_.UInt16)) &&& (0x3333 : _root_.UInt16))
  let v := (v + (v >>> (4 : _root_.UInt16))) &&& (0x0F0F : _root_.UInt16)
  ⟨(v * (0x0101 : _root_.UInt16)) >>> (8 : _root_.UInt16)⟩

@[inline] private def bitReverse16_impl (x : UInt16) : UInt16 :=
  let v := x.val
  let v := ((v >>> (1 : _root_.UInt16)) &&& (0x5555 : _root_.UInt16)) ||| ((v &&& (0x5555 : _root_.UInt16)) <<< (1 : _root_.UInt16))
  let v := ((v >>> (2 : _root_.UInt16)) &&& (0x3333 : _root_.UInt16)) ||| ((v &&& (0x3333 : _root_.UInt16)) <<< (2 : _root_.UInt16))
  let v := ((v >>> (4 : _root_.UInt16)) &&& (0x0F0F : _root_.UInt16)) ||| ((v &&& (0x0F0F : _root_.UInt16)) <<< (4 : _root_.UInt16))
  ⟨(v >>> (8 : _root_.UInt16)) ||| (v <<< (8 : _root_.UInt16))⟩

namespace UInt16

@[implemented_by clz16_impl, inline] def clz (x : UInt16) : UInt16 :=
  ⟨(clzLoop x.toBitVec 16 0).toUInt16⟩

@[implemented_by ctz16_impl, inline] def ctz (x : UInt16) : UInt16 :=
  ⟨(ctzLoop x.toBitVec 16 0).toUInt16⟩

@[implemented_by popcount16_impl, inline] def popcount (x : UInt16) : UInt16 :=
  ⟨(popcountLoop x.toBitVec 16 0 0).toUInt16⟩

@[implemented_by bitReverse16_impl, inline] def bitReverse (x : UInt16) : UInt16 :=
  fromBitVec (bitReverseLoop x.toBitVec 16 0 (0#16))

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : UInt16) : UInt16 :=
  popcount ⟨x.val ^^^ y.val⟩

end UInt16

/-! ================================================================ -/
/-! ## UInt32 Bit Scanning                                            -/
/-! ================================================================ -/

-- SWAR implementations defined outside namespace to avoid Radix.UInt32/UInt32 collision
@[inline] private def popcount32_impl (x : UInt32) : UInt32 :=
  let v := x.val
  let v := v - ((v >>> (1 : _root_.UInt32)) &&& (0x55555555 : _root_.UInt32))
  let v := (v &&& (0x33333333 : _root_.UInt32)) + ((v >>> (2 : _root_.UInt32)) &&& (0x33333333 : _root_.UInt32))
  let v := (v + (v >>> (4 : _root_.UInt32))) &&& (0x0F0F0F0F : _root_.UInt32)
  ⟨(v * (0x01010101 : _root_.UInt32)) >>> (24 : _root_.UInt32)⟩

-- Hardware-accelerated CLZ via __builtin_clz (compiles to LZCNT instruction)
@[extern "radix_clz32"] private opaque clz32_impl : UInt32 → UInt32

@[inline] private def ctz32_impl (x : UInt32) : UInt32 :=
  -- Branchless: (~x) & (x-1) isolates trailing zeros. For x=0, gives 0xFFFFFFFF, popcount=32.
  let v := (~~~x.val) &&& (x.val - (1 : _root_.UInt32))
  let v := v - ((v >>> (1 : _root_.UInt32)) &&& (0x55555555 : _root_.UInt32))
  let v := (v &&& (0x33333333 : _root_.UInt32)) + ((v >>> (2 : _root_.UInt32)) &&& (0x33333333 : _root_.UInt32))
  let v := (v + (v >>> (4 : _root_.UInt32))) &&& (0x0F0F0F0F : _root_.UInt32)
  ⟨(v * (0x01010101 : _root_.UInt32)) >>> (24 : _root_.UInt32)⟩

@[inline] private def bitReverse32_impl (x : UInt32) : UInt32 :=
  let v := x.val
  let v := ((v >>> (1 : _root_.UInt32)) &&& (0x55555555 : _root_.UInt32)) ||| ((v &&& (0x55555555 : _root_.UInt32)) <<< (1 : _root_.UInt32))
  let v := ((v >>> (2 : _root_.UInt32)) &&& (0x33333333 : _root_.UInt32)) ||| ((v &&& (0x33333333 : _root_.UInt32)) <<< (2 : _root_.UInt32))
  let v := ((v >>> (4 : _root_.UInt32)) &&& (0x0F0F0F0F : _root_.UInt32)) ||| ((v &&& (0x0F0F0F0F : _root_.UInt32)) <<< (4 : _root_.UInt32))
  let v := ((v >>> (8 : _root_.UInt32)) &&& (0x00FF00FF : _root_.UInt32)) ||| ((v &&& (0x00FF00FF : _root_.UInt32)) <<< (8 : _root_.UInt32))
  ⟨(v >>> (16 : _root_.UInt32)) ||| (v <<< (16 : _root_.UInt32))⟩

namespace UInt32

@[implemented_by clz32_impl, inline] def clz (x : UInt32) : UInt32 :=
  ⟨(clzLoop x.toBitVec 32 0).toUInt32⟩

@[implemented_by ctz32_impl, inline] def ctz (x : UInt32) : UInt32 :=
  ⟨(ctzLoop x.toBitVec 32 0).toUInt32⟩

@[implemented_by popcount32_impl, inline] def popcount (x : UInt32) : UInt32 :=
  ⟨(popcountLoop x.toBitVec 32 0 0).toUInt32⟩

@[implemented_by bitReverse32_impl, inline] def bitReverse (x : UInt32) : UInt32 :=
  fromBitVec (bitReverseLoop x.toBitVec 32 0 (0#32))

/-- Hamming distance: popcount of XOR (FR-002.3). -/
@[inline] def hammingDistance (x y : UInt32) : UInt32 :=
  popcount ⟨x.val ^^^ y.val⟩

end UInt32

/-! ================================================================ -/
/-! ## UInt64 Bit Scanning                                            -/
/-! ================================================================ -/

-- SWAR implementations for UInt64
@[inline] private def popcount64_impl (x : UInt64) : UInt64 :=
  let v := x.val
  let v := v - ((v >>> (1 : _root_.UInt64)) &&& (0x5555555555555555 : _root_.UInt64))
  let v := (v &&& (0x3333333333333333 : _root_.UInt64)) + ((v >>> (2 : _root_.UInt64)) &&& (0x3333333333333333 : _root_.UInt64))
  let v := (v + (v >>> (4 : _root_.UInt64))) &&& (0x0F0F0F0F0F0F0F0F : _root_.UInt64)
  ⟨(v * (0x0101010101010101 : _root_.UInt64)) >>> (56 : _root_.UInt64)⟩

-- Hardware-accelerated CLZ via __builtin_clzll (compiles to LZCNT instruction)
@[extern "radix_clz64"] private opaque clz64_impl : UInt64 → UInt64

@[inline] private def ctz64_impl (x : UInt64) : UInt64 :=
  -- Branchless: (~x) & (x-1) isolates trailing zeros. For x=0, gives 0xFFFFFFFFFFFFFFFF, popcount=64.
  let v := (~~~x.val) &&& (x.val - (1 : _root_.UInt64))
  let v := v - ((v >>> (1 : _root_.UInt64)) &&& (0x5555555555555555 : _root_.UInt64))
  let v := (v &&& (0x3333333333333333 : _root_.UInt64)) + ((v >>> (2 : _root_.UInt64)) &&& (0x3333333333333333 : _root_.UInt64))
  let v := (v + (v >>> (4 : _root_.UInt64))) &&& (0x0F0F0F0F0F0F0F0F : _root_.UInt64)
  ⟨(v * (0x0101010101010101 : _root_.UInt64)) >>> (56 : _root_.UInt64)⟩

@[inline] private def bitReverse64_impl (x : UInt64) : UInt64 :=
  let v := x.val
  let v := ((v >>> (1 : _root_.UInt64)) &&& (0x5555555555555555 : _root_.UInt64)) ||| ((v &&& (0x5555555555555555 : _root_.UInt64)) <<< (1 : _root_.UInt64))
  let v := ((v >>> (2 : _root_.UInt64)) &&& (0x3333333333333333 : _root_.UInt64)) ||| ((v &&& (0x3333333333333333 : _root_.UInt64)) <<< (2 : _root_.UInt64))
  let v := ((v >>> (4 : _root_.UInt64)) &&& (0x0F0F0F0F0F0F0F0F : _root_.UInt64)) ||| ((v &&& (0x0F0F0F0F0F0F0F0F : _root_.UInt64)) <<< (4 : _root_.UInt64))
  let v := ((v >>> (8 : _root_.UInt64)) &&& (0x00FF00FF00FF00FF : _root_.UInt64)) ||| ((v &&& (0x00FF00FF00FF00FF : _root_.UInt64)) <<< (8 : _root_.UInt64))
  let v := ((v >>> (16 : _root_.UInt64)) &&& (0x0000FFFF0000FFFF : _root_.UInt64)) ||| ((v &&& (0x0000FFFF0000FFFF : _root_.UInt64)) <<< (16 : _root_.UInt64))
  ⟨(v >>> (32 : _root_.UInt64)) ||| (v <<< (32 : _root_.UInt64))⟩

namespace UInt64

@[implemented_by clz64_impl, inline] def clz (x : UInt64) : UInt64 :=
  ⟨(clzLoop x.toBitVec 64 0).toUInt64⟩

@[implemented_by ctz64_impl, inline] def ctz (x : UInt64) : UInt64 :=
  ⟨(ctzLoop x.toBitVec 64 0).toUInt64⟩

@[implemented_by popcount64_impl, inline] def popcount (x : UInt64) : UInt64 :=
  ⟨(popcountLoop x.toBitVec 64 0 0).toUInt64⟩

@[implemented_by bitReverse64_impl, inline] def bitReverse (x : UInt64) : UInt64 :=
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
