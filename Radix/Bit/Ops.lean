/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Int
import Radix.Word.Size

/-!
# Bitwise Operations (Layer 2)

This module provides bitwise operations for all integer types:
- AND, OR, XOR, NOT
- Shift left, logical right shift, arithmetic right shift
- Rotate left, rotate right

All shift/rotate operations normalize the count by `count % bitWidth`
when `count >= bitWidth` (FR-002.1a: Rust semantics).

All operations are `@[inline]` for zero-cost abstraction (NFR-002).

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- FR-002.1: Bitwise operations
- FR-002.1a: Shift/rotate edge cases
- NFR-002: Zero-cost abstractions
-/

namespace Radix

/-! ================================================================ -/
/-! ## UInt8 Bitwise Operations                                       -/
/-! ================================================================ -/

namespace UInt8

@[inline] def band (x y : UInt8) : UInt8 := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : UInt8) : UInt8 := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : UInt8) : UInt8 := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : UInt8)   : UInt8 := ⟨~~~x.val⟩

@[inline] instance : HAnd UInt8 UInt8 UInt8 := ⟨band⟩
@[inline] instance : HOr  UInt8 UInt8 UInt8 := ⟨bor⟩
@[inline] instance : HXor UInt8 UInt8 UInt8 := ⟨bxor⟩
@[inline] instance : Complement UInt8 := ⟨bnot⟩

/-- Left shift with count normalization (FR-002.1a). -/
@[inline] def shl (x : UInt8) (count : UInt8) : UInt8 :=
  fromBitVec (x.toBitVec.shiftLeft (count.val.toNat % 8))

/-- Logical right shift with count normalization (FR-002.1a). -/
@[inline] def shrLogical (x : UInt8) (count : UInt8) : UInt8 :=
  fromBitVec (x.toBitVec.ushiftRight (count.val.toNat % 8))

/-- Arithmetic right shift with count normalization (FR-002.1a).
    Preserves sign bit (for signed reinterpretation). -/
@[inline] def shrArith (x : UInt8) (count : UInt8) : UInt8 :=
  fromBitVec (x.toBitVec.sshiftRight (count.val.toNat % 8))

/-- Rotate left with count normalization. -/
@[inline] def rotl (x : UInt8) (count : UInt8) : UInt8 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 8
  fromBitVec (bv.shiftLeft c ||| bv.ushiftRight (8 - c))

/-- Rotate right with count normalization. -/
@[inline] def rotr (x : UInt8) (count : UInt8) : UInt8 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 8
  fromBitVec (bv.ushiftRight c ||| bv.shiftLeft (8 - c))

@[inline] instance : HShiftLeft  UInt8 UInt8 UInt8 := ⟨shl⟩
@[inline] instance : HShiftRight UInt8 UInt8 UInt8 := ⟨shrLogical⟩

end UInt8

/-! ================================================================ -/
/-! ## UInt16 Bitwise Operations                                      -/
/-! ================================================================ -/

namespace UInt16

@[inline] def band (x y : UInt16) : UInt16 := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : UInt16) : UInt16 := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : UInt16) : UInt16 := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : UInt16)   : UInt16 := ⟨~~~x.val⟩

@[inline] instance : HAnd UInt16 UInt16 UInt16 := ⟨band⟩
@[inline] instance : HOr  UInt16 UInt16 UInt16 := ⟨bor⟩
@[inline] instance : HXor UInt16 UInt16 UInt16 := ⟨bxor⟩
@[inline] instance : Complement UInt16 := ⟨bnot⟩

@[inline] def shl (x : UInt16) (count : UInt16) : UInt16 :=
  fromBitVec (x.toBitVec.shiftLeft (count.val.toNat % 16))

@[inline] def shrLogical (x : UInt16) (count : UInt16) : UInt16 :=
  fromBitVec (x.toBitVec.ushiftRight (count.val.toNat % 16))

@[inline] def shrArith (x : UInt16) (count : UInt16) : UInt16 :=
  fromBitVec (x.toBitVec.sshiftRight (count.val.toNat % 16))

@[inline] def rotl (x : UInt16) (count : UInt16) : UInt16 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 16
  fromBitVec (bv.shiftLeft c ||| bv.ushiftRight (16 - c))

@[inline] def rotr (x : UInt16) (count : UInt16) : UInt16 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 16
  fromBitVec (bv.ushiftRight c ||| bv.shiftLeft (16 - c))

@[inline] instance : HShiftLeft  UInt16 UInt16 UInt16 := ⟨shl⟩
@[inline] instance : HShiftRight UInt16 UInt16 UInt16 := ⟨shrLogical⟩

end UInt16

/-! ================================================================ -/
/-! ## UInt32 Bitwise Operations                                      -/
/-! ================================================================ -/

namespace UInt32

@[inline] def band (x y : UInt32) : UInt32 := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : UInt32) : UInt32 := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : UInt32) : UInt32 := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : UInt32)   : UInt32 := ⟨~~~x.val⟩

@[inline] instance : HAnd UInt32 UInt32 UInt32 := ⟨band⟩
@[inline] instance : HOr  UInt32 UInt32 UInt32 := ⟨bor⟩
@[inline] instance : HXor UInt32 UInt32 UInt32 := ⟨bxor⟩
@[inline] instance : Complement UInt32 := ⟨bnot⟩

@[inline] def shl (x : UInt32) (count : UInt32) : UInt32 :=
  fromBitVec (x.toBitVec.shiftLeft (count.val.toNat % 32))

@[inline] def shrLogical (x : UInt32) (count : UInt32) : UInt32 :=
  fromBitVec (x.toBitVec.ushiftRight (count.val.toNat % 32))

@[inline] def shrArith (x : UInt32) (count : UInt32) : UInt32 :=
  fromBitVec (x.toBitVec.sshiftRight (count.val.toNat % 32))

@[inline] def rotl (x : UInt32) (count : UInt32) : UInt32 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 32
  fromBitVec (bv.shiftLeft c ||| bv.ushiftRight (32 - c))

@[inline] def rotr (x : UInt32) (count : UInt32) : UInt32 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 32
  fromBitVec (bv.ushiftRight c ||| bv.shiftLeft (32 - c))

@[inline] instance : HShiftLeft  UInt32 UInt32 UInt32 := ⟨shl⟩
@[inline] instance : HShiftRight UInt32 UInt32 UInt32 := ⟨shrLogical⟩

end UInt32

/-! ================================================================ -/
/-! ## UInt64 Bitwise Operations                                      -/
/-! ================================================================ -/

namespace UInt64

@[inline] def band (x y : UInt64) : UInt64 := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : UInt64) : UInt64 := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : UInt64) : UInt64 := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : UInt64)   : UInt64 := ⟨~~~x.val⟩

@[inline] instance : HAnd UInt64 UInt64 UInt64 := ⟨band⟩
@[inline] instance : HOr  UInt64 UInt64 UInt64 := ⟨bor⟩
@[inline] instance : HXor UInt64 UInt64 UInt64 := ⟨bxor⟩
@[inline] instance : Complement UInt64 := ⟨bnot⟩

@[inline] def shl (x : UInt64) (count : UInt64) : UInt64 :=
  fromBitVec (x.toBitVec.shiftLeft (count.val.toNat % 64))

@[inline] def shrLogical (x : UInt64) (count : UInt64) : UInt64 :=
  fromBitVec (x.toBitVec.ushiftRight (count.val.toNat % 64))

@[inline] def shrArith (x : UInt64) (count : UInt64) : UInt64 :=
  fromBitVec (x.toBitVec.sshiftRight (count.val.toNat % 64))

@[inline] def rotl (x : UInt64) (count : UInt64) : UInt64 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 64
  fromBitVec (bv.shiftLeft c ||| bv.ushiftRight (64 - c))

@[inline] def rotr (x : UInt64) (count : UInt64) : UInt64 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 64
  fromBitVec (bv.ushiftRight c ||| bv.shiftLeft (64 - c))

@[inline] instance : HShiftLeft  UInt64 UInt64 UInt64 := ⟨shl⟩
@[inline] instance : HShiftRight UInt64 UInt64 UInt64 := ⟨shrLogical⟩

end UInt64

/-! ================================================================ -/
/-! ## Int8 Bitwise Operations (via underlying UInt8)                  -/
/-! ================================================================ -/

namespace Int8

@[inline] def band (x y : Int8) : Int8 := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : Int8) : Int8 := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : Int8) : Int8 := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : Int8)   : Int8 := ⟨~~~x.val⟩

@[inline] instance : HAnd Int8 Int8 Int8 := ⟨band⟩
@[inline] instance : HOr  Int8 Int8 Int8 := ⟨bor⟩
@[inline] instance : HXor Int8 Int8 Int8 := ⟨bxor⟩
@[inline] instance : Complement Int8 := ⟨bnot⟩

@[inline] def shl (x : Int8) (count : Int8) : Int8 :=
  fromBitVec (x.toBitVec.shiftLeft (count.val.toNat % 8))

@[inline] def shrLogical (x : Int8) (count : Int8) : Int8 :=
  fromBitVec (x.toBitVec.ushiftRight (count.val.toNat % 8))

@[inline] def shrArith (x : Int8) (count : Int8) : Int8 :=
  fromBitVec (x.toBitVec.sshiftRight (count.val.toNat % 8))

@[inline] def rotl (x : Int8) (count : Int8) : Int8 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 8
  fromBitVec (bv.shiftLeft c ||| bv.ushiftRight (8 - c))

@[inline] def rotr (x : Int8) (count : Int8) : Int8 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 8
  fromBitVec (bv.ushiftRight c ||| bv.shiftLeft (8 - c))

@[inline] instance : HShiftLeft  Int8 Int8 Int8 := ⟨shl⟩
@[inline] instance : HShiftRight Int8 Int8 Int8 := ⟨shrLogical⟩

end Int8

/-! ================================================================ -/
/-! ## Int16 Bitwise Operations (via underlying UInt16)                -/
/-! ================================================================ -/

namespace Int16

@[inline] def band (x y : Int16) : Int16 := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : Int16) : Int16 := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : Int16) : Int16 := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : Int16)   : Int16 := ⟨~~~x.val⟩

@[inline] instance : HAnd Int16 Int16 Int16 := ⟨band⟩
@[inline] instance : HOr  Int16 Int16 Int16 := ⟨bor⟩
@[inline] instance : HXor Int16 Int16 Int16 := ⟨bxor⟩
@[inline] instance : Complement Int16 := ⟨bnot⟩

@[inline] def shl (x : Int16) (count : Int16) : Int16 :=
  fromBitVec (x.toBitVec.shiftLeft (count.val.toNat % 16))

@[inline] def shrLogical (x : Int16) (count : Int16) : Int16 :=
  fromBitVec (x.toBitVec.ushiftRight (count.val.toNat % 16))

@[inline] def shrArith (x : Int16) (count : Int16) : Int16 :=
  fromBitVec (x.toBitVec.sshiftRight (count.val.toNat % 16))

@[inline] def rotl (x : Int16) (count : Int16) : Int16 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 16
  fromBitVec (bv.shiftLeft c ||| bv.ushiftRight (16 - c))

@[inline] def rotr (x : Int16) (count : Int16) : Int16 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 16
  fromBitVec (bv.ushiftRight c ||| bv.shiftLeft (16 - c))

@[inline] instance : HShiftLeft  Int16 Int16 Int16 := ⟨shl⟩
@[inline] instance : HShiftRight Int16 Int16 Int16 := ⟨shrLogical⟩

end Int16

/-! ================================================================ -/
/-! ## Int32 Bitwise Operations (via underlying UInt32)                -/
/-! ================================================================ -/

namespace Int32

@[inline] def band (x y : Int32) : Int32 := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : Int32) : Int32 := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : Int32) : Int32 := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : Int32)   : Int32 := ⟨~~~x.val⟩

@[inline] instance : HAnd Int32 Int32 Int32 := ⟨band⟩
@[inline] instance : HOr  Int32 Int32 Int32 := ⟨bor⟩
@[inline] instance : HXor Int32 Int32 Int32 := ⟨bxor⟩
@[inline] instance : Complement Int32 := ⟨bnot⟩

@[inline] def shl (x : Int32) (count : Int32) : Int32 :=
  fromBitVec (x.toBitVec.shiftLeft (count.val.toNat % 32))

@[inline] def shrLogical (x : Int32) (count : Int32) : Int32 :=
  fromBitVec (x.toBitVec.ushiftRight (count.val.toNat % 32))

@[inline] def shrArith (x : Int32) (count : Int32) : Int32 :=
  fromBitVec (x.toBitVec.sshiftRight (count.val.toNat % 32))

@[inline] def rotl (x : Int32) (count : Int32) : Int32 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 32
  fromBitVec (bv.shiftLeft c ||| bv.ushiftRight (32 - c))

@[inline] def rotr (x : Int32) (count : Int32) : Int32 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 32
  fromBitVec (bv.ushiftRight c ||| bv.shiftLeft (32 - c))

@[inline] instance : HShiftLeft  Int32 Int32 Int32 := ⟨shl⟩
@[inline] instance : HShiftRight Int32 Int32 Int32 := ⟨shrLogical⟩

end Int32

/-! ================================================================ -/
/-! ## Int64 Bitwise Operations (via underlying UInt64)                -/
/-! ================================================================ -/

namespace Int64

@[inline] def band (x y : Int64) : Int64 := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : Int64) : Int64 := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : Int64) : Int64 := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : Int64)   : Int64 := ⟨~~~x.val⟩

@[inline] instance : HAnd Int64 Int64 Int64 := ⟨band⟩
@[inline] instance : HOr  Int64 Int64 Int64 := ⟨bor⟩
@[inline] instance : HXor Int64 Int64 Int64 := ⟨bxor⟩
@[inline] instance : Complement Int64 := ⟨bnot⟩

@[inline] def shl (x : Int64) (count : Int64) : Int64 :=
  fromBitVec (x.toBitVec.shiftLeft (count.val.toNat % 64))

@[inline] def shrLogical (x : Int64) (count : Int64) : Int64 :=
  fromBitVec (x.toBitVec.ushiftRight (count.val.toNat % 64))

@[inline] def shrArith (x : Int64) (count : Int64) : Int64 :=
  fromBitVec (x.toBitVec.sshiftRight (count.val.toNat % 64))

@[inline] def rotl (x : Int64) (count : Int64) : Int64 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 64
  fromBitVec (bv.shiftLeft c ||| bv.ushiftRight (64 - c))

@[inline] def rotr (x : Int64) (count : Int64) : Int64 :=
  let bv := x.toBitVec
  let c := count.val.toNat % 64
  fromBitVec (bv.ushiftRight c ||| bv.shiftLeft (64 - c))

@[inline] instance : HShiftLeft  Int64 Int64 Int64 := ⟨shl⟩
@[inline] instance : HShiftRight Int64 Int64 Int64 := ⟨shrLogical⟩

end Int64

/-! ================================================================ -/
/-! ## UWord Bitwise Operations                                       -/
/-! ================================================================ -/

namespace UWord

@[inline] def band (x y : UWord) : UWord := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : UWord) : UWord := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : UWord) : UWord := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : UWord)   : UWord := ⟨~~~x.val⟩

@[inline] instance : HAnd UWord UWord UWord := ⟨band⟩
@[inline] instance : HOr  UWord UWord UWord := ⟨bor⟩
@[inline] instance : HXor UWord UWord UWord := ⟨bxor⟩
@[inline] instance : Complement UWord := ⟨bnot⟩

@[inline] def shl (x : UWord) (count : UWord) : UWord :=
  ⟨x.val.shiftLeft ((count.val.toNat % System.Platform.numBits).toUSize)⟩

@[inline] def shrLogical (x : UWord) (count : UWord) : UWord :=
  ⟨x.val.shiftRight ((count.val.toNat % System.Platform.numBits).toUSize)⟩

@[inline] instance : HShiftLeft  UWord UWord UWord := ⟨shl⟩
@[inline] instance : HShiftRight UWord UWord UWord := ⟨shrLogical⟩

end UWord

/-! ================================================================ -/
/-! ## IWord Bitwise Operations                                       -/
/-! ================================================================ -/

namespace IWord

@[inline] def band (x y : IWord) : IWord := ⟨x.val &&& y.val⟩
@[inline] def bor  (x y : IWord) : IWord := ⟨x.val ||| y.val⟩
@[inline] def bxor (x y : IWord) : IWord := ⟨x.val ^^^ y.val⟩
@[inline] def bnot (x : IWord)   : IWord := ⟨~~~x.val⟩

@[inline] instance : HAnd IWord IWord IWord := ⟨band⟩
@[inline] instance : HOr  IWord IWord IWord := ⟨bor⟩
@[inline] instance : HXor IWord IWord IWord := ⟨bxor⟩
@[inline] instance : Complement IWord := ⟨bnot⟩

@[inline] def shl (x : IWord) (count : IWord) : IWord :=
  ⟨x.val.shiftLeft ((count.val.toNat % System.Platform.numBits).toUSize)⟩

@[inline] def shrLogical (x : IWord) (count : IWord) : IWord :=
  ⟨x.val.shiftRight ((count.val.toNat % System.Platform.numBits).toUSize)⟩

@[inline] def shrArith (x : IWord) (count : IWord) : IWord :=
  ⟨⟨(x.toBitVec.sshiftRight (count.val.toNat % System.Platform.numBits)).toFin⟩⟩

@[inline] instance : HShiftLeft  IWord IWord IWord := ⟨shl⟩
@[inline] instance : HShiftRight IWord IWord IWord := ⟨shrLogical⟩

end IWord

end Radix
