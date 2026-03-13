/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt

/-!
# Signed Fixed-Width Integers (Layer 2)

This module defines `Int8`, `Int16`, `Int32`, `Int64` as wrappers around
Lean 4's built-in unsigned integer types, with two's complement interpretation.
The MSB determines the sign (ADR-003).

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- FR-001.1: Signed integer types
- ADR-003: Signed Integers via Two's Complement Wrapper
- NFR-002: Zero-cost abstractions
-/

namespace Radix

/-! ## Int8 -/

/-- 8-bit signed integer wrapping `UInt8` with two's complement semantics.
    Range: -128 to 127. -/
structure Int8 where
  val : _root_.UInt8
  deriving DecidableEq

namespace Int8

def bitWidth : Nat := 8

instance : Inhabited Int8 := ⟨⟨0⟩⟩
instance : BEq Int8 := ⟨fun a b => a.val == b.val⟩
instance {n : Nat} : OfNat Int8 n := ⟨⟨OfNat.ofNat n⟩⟩

/-- Interpret the underlying bits as a signed integer via two's complement. -/
@[inline] def toInt (x : Int8) : Int := x.val.toBitVec.toInt

/-- Convert from Lean 4 `Int`, truncating to 8 bits. -/
@[inline] def fromInt (i : Int) : Int8 := ⟨⟨(BitVec.ofInt 8 i).toFin⟩⟩

instance : ToString Int8 := ⟨fun a => toString a.toInt⟩
instance : Repr Int8 := ⟨fun a _ => Repr.addAppParen (repr a.toInt) 0⟩

/-- Signed less-than via MSB comparison (zero-cost, no `Int` allocation).
    Two's complement: same-sign ⟹ unsigned order; different-sign ⟹ negative is smaller. -/
@[inline] def slt (a b : Int8) : Bool :=
  let aNeg := a.val >= 128
  let bNeg := b.val >= 128
  if aNeg == bNeg then a.val < b.val else aNeg

/-- Signed less-than-or-equal via MSB comparison (zero-cost, no `Int` allocation). -/
@[inline] def sle (a b : Int8) : Bool :=
  let aNeg := a.val >= 128
  let bNeg := b.val >= 128
  if aNeg == bNeg then a.val <= b.val else aNeg

/-- Signed comparison: greater than. -/
@[inline] def sgt (a b : Int8) : Bool := slt b a

/-- Signed comparison: greater than or equal. -/
@[inline] def sge (a b : Int8) : Bool := sle b a

instance : LT Int8 := ⟨fun a b => a.slt b = true⟩
instance : LE Int8 := ⟨fun a b => a.sle b = true⟩
instance : Ord Int8 := ⟨fun a b =>
  if a.slt b then .lt
  else if b.slt a then .gt
  else .eq⟩

/-- Convert to `Radix.UInt8` preserving bit pattern. -/
@[inline] def toUInt8 (x : Int8) : Radix.UInt8 := ⟨x.val⟩

/-- Convert from `Radix.UInt8` preserving bit pattern. -/
@[inline] def fromUInt8 (x : Radix.UInt8) : Int8 := ⟨x.val⟩

/-- Convert to `BitVec 8` for Layer 3 specification bridging. -/
@[inline] def toBitVec (x : Int8) : BitVec 8 := x.val.toBitVec

/-- Convert from `BitVec 8`. -/
@[inline] def fromBitVec (bv : BitVec 8) : Int8 := ⟨⟨bv.toFin⟩⟩

-- Basic wrapping arithmetic via underlying unsigned operations
@[inline] instance : Add Int8 := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub Int8 := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul Int8 := ⟨fun a b => ⟨a.val * b.val⟩⟩
@[inline] instance : Neg Int8 := ⟨fun a => ⟨0 - a.val⟩⟩

/-- Signed minimum: -128. -/
def minVal : Int8 := ⟨128⟩

/-- Signed maximum: 127. -/
def maxVal : Int8 := ⟨127⟩

/-- Is the value negative? (MSB = 1) -/
@[inline] def isNeg (x : Int8) : Bool := x.val >= 128

end Int8

/-! ## Int16 -/

/-- 16-bit signed integer wrapping `UInt16` with two's complement semantics. -/
structure Int16 where
  val : _root_.UInt16
  deriving DecidableEq

namespace Int16

def bitWidth : Nat := 16

instance : Inhabited Int16 := ⟨⟨0⟩⟩
instance : BEq Int16 := ⟨fun a b => a.val == b.val⟩
instance {n : Nat} : OfNat Int16 n := ⟨⟨OfNat.ofNat n⟩⟩

@[inline] def toInt (x : Int16) : Int := x.val.toBitVec.toInt
@[inline] def fromInt (i : Int) : Int16 := ⟨⟨(BitVec.ofInt 16 i).toFin⟩⟩

instance : ToString Int16 := ⟨fun a => toString a.toInt⟩
instance : Repr Int16 := ⟨fun a _ => Repr.addAppParen (repr a.toInt) 0⟩

/-- Signed less-than via MSB comparison (zero-cost, NFR-002). -/
@[inline] def slt (a b : Int16) : Bool :=
  let aNeg := a.val >= 32768
  let bNeg := b.val >= 32768
  if aNeg == bNeg then a.val < b.val else aNeg

/-- Signed less-than-or-equal via MSB comparison (zero-cost, NFR-002). -/
@[inline] def sle (a b : Int16) : Bool :=
  let aNeg := a.val >= 32768
  let bNeg := b.val >= 32768
  if aNeg == bNeg then a.val <= b.val else aNeg

/-- Signed comparison: greater than. -/
@[inline] def sgt (a b : Int16) : Bool := slt b a

/-- Signed comparison: greater than or equal. -/
@[inline] def sge (a b : Int16) : Bool := sle b a

instance : LT Int16 := ⟨fun a b => a.slt b = true⟩
instance : LE Int16 := ⟨fun a b => a.sle b = true⟩
instance : Ord Int16 := ⟨fun a b =>
  if a.slt b then .lt
  else if b.slt a then .gt
  else .eq⟩

@[inline] def toUInt16 (x : Int16) : Radix.UInt16 := ⟨x.val⟩
@[inline] def fromUInt16 (x : Radix.UInt16) : Int16 := ⟨x.val⟩
@[inline] def toBitVec (x : Int16) : BitVec 16 := x.val.toBitVec
@[inline] def fromBitVec (bv : BitVec 16) : Int16 := ⟨⟨bv.toFin⟩⟩

@[inline] instance : Add Int16 := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub Int16 := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul Int16 := ⟨fun a b => ⟨a.val * b.val⟩⟩
@[inline] instance : Neg Int16 := ⟨fun a => ⟨0 - a.val⟩⟩

def minVal : Int16 := ⟨32768⟩
def maxVal : Int16 := ⟨32767⟩

@[inline] def isNeg (x : Int16) : Bool := x.val >= 32768

end Int16

/-! ## Int32 -/

/-- 32-bit signed integer wrapping `UInt32` with two's complement semantics. -/
structure Int32 where
  val : _root_.UInt32
  deriving DecidableEq

namespace Int32

def bitWidth : Nat := 32

instance : Inhabited Int32 := ⟨⟨0⟩⟩
instance : BEq Int32 := ⟨fun a b => a.val == b.val⟩
instance {n : Nat} : OfNat Int32 n := ⟨⟨OfNat.ofNat n⟩⟩

@[inline] def toInt (x : Int32) : Int := x.val.toBitVec.toInt
@[inline] def fromInt (i : Int) : Int32 := ⟨⟨(BitVec.ofInt 32 i).toFin⟩⟩

instance : ToString Int32 := ⟨fun a => toString a.toInt⟩
instance : Repr Int32 := ⟨fun a _ => Repr.addAppParen (repr a.toInt) 0⟩

/-- Signed less-than via MSB comparison (zero-cost, NFR-002). -/
@[inline] def slt (a b : Int32) : Bool :=
  let aNeg := a.val >= 2147483648
  let bNeg := b.val >= 2147483648
  if aNeg == bNeg then a.val < b.val else aNeg

/-- Signed less-than-or-equal via MSB comparison (zero-cost, NFR-002). -/
@[inline] def sle (a b : Int32) : Bool :=
  let aNeg := a.val >= 2147483648
  let bNeg := b.val >= 2147483648
  if aNeg == bNeg then a.val <= b.val else aNeg

/-- Signed comparison: greater than. -/
@[inline] def sgt (a b : Int32) : Bool := slt b a

/-- Signed comparison: greater than or equal. -/
@[inline] def sge (a b : Int32) : Bool := sle b a

instance : LT Int32 := ⟨fun a b => a.slt b = true⟩
instance : LE Int32 := ⟨fun a b => a.sle b = true⟩
instance : Ord Int32 := ⟨fun a b =>
  if a.slt b then .lt
  else if b.slt a then .gt
  else .eq⟩

@[inline] def toUInt32 (x : Int32) : Radix.UInt32 := ⟨x.val⟩
@[inline] def fromUInt32 (x : Radix.UInt32) : Int32 := ⟨x.val⟩
@[inline] def toBitVec (x : Int32) : BitVec 32 := x.val.toBitVec
@[inline] def fromBitVec (bv : BitVec 32) : Int32 := ⟨⟨bv.toFin⟩⟩

@[inline] instance : Add Int32 := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub Int32 := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul Int32 := ⟨fun a b => ⟨a.val * b.val⟩⟩
@[inline] instance : Neg Int32 := ⟨fun a => ⟨0 - a.val⟩⟩

def minVal : Int32 := ⟨2147483648⟩
def maxVal : Int32 := ⟨2147483647⟩

@[inline] def isNeg (x : Int32) : Bool := x.val >= 2147483648

end Int32

/-! ## Int64 -/

/-- 64-bit signed integer wrapping `UInt64` with two's complement semantics. -/
structure Int64 where
  val : _root_.UInt64
  deriving DecidableEq

namespace Int64

def bitWidth : Nat := 64

instance : Inhabited Int64 := ⟨⟨0⟩⟩
instance : BEq Int64 := ⟨fun a b => a.val == b.val⟩
instance {n : Nat} : OfNat Int64 n := ⟨⟨OfNat.ofNat n⟩⟩

@[inline] def toInt (x : Int64) : Int := x.val.toBitVec.toInt
@[inline] def fromInt (i : Int) : Int64 := ⟨⟨(BitVec.ofInt 64 i).toFin⟩⟩

instance : ToString Int64 := ⟨fun a => toString a.toInt⟩
instance : Repr Int64 := ⟨fun a _ => Repr.addAppParen (repr a.toInt) 0⟩

/-- Signed less-than via MSB comparison (zero-cost, NFR-002). -/
@[inline] def slt (a b : Int64) : Bool :=
  let aNeg := a.val >= 9223372036854775808
  let bNeg := b.val >= 9223372036854775808
  if aNeg == bNeg then a.val < b.val else aNeg

/-- Signed less-than-or-equal via MSB comparison (zero-cost, NFR-002). -/
@[inline] def sle (a b : Int64) : Bool :=
  let aNeg := a.val >= 9223372036854775808
  let bNeg := b.val >= 9223372036854775808
  if aNeg == bNeg then a.val <= b.val else aNeg

/-- Signed comparison: greater than. -/
@[inline] def sgt (a b : Int64) : Bool := slt b a

/-- Signed comparison: greater than or equal. -/
@[inline] def sge (a b : Int64) : Bool := sle b a

instance : LT Int64 := ⟨fun a b => a.slt b = true⟩
instance : LE Int64 := ⟨fun a b => a.sle b = true⟩
instance : Ord Int64 := ⟨fun a b =>
  if a.slt b then .lt
  else if b.slt a then .gt
  else .eq⟩

@[inline] def toUInt64 (x : Int64) : Radix.UInt64 := ⟨x.val⟩
@[inline] def fromUInt64 (x : Radix.UInt64) : Int64 := ⟨x.val⟩
@[inline] def toBitVec (x : Int64) : BitVec 64 := x.val.toBitVec
@[inline] def fromBitVec (bv : BitVec 64) : Int64 := ⟨⟨bv.toFin⟩⟩

@[inline] instance : Add Int64 := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub Int64 := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul Int64 := ⟨fun a b => ⟨a.val * b.val⟩⟩
@[inline] instance : Neg Int64 := ⟨fun a => ⟨0 - a.val⟩⟩

def minVal : Int64 := ⟨9223372036854775808⟩
def maxVal : Int64 := ⟨9223372036854775807⟩

@[inline] def isNeg (x : Int64) : Bool := x.val >= 9223372036854775808

end Int64

/-! ## FixedWidth instances for signed types -/

instance : FixedWidth Int8 where
  bitWidth := 8
  toBitVec := Int8.toBitVec
  fromBitVec := Int8.fromBitVec

instance : FixedWidth Int16 where
  bitWidth := 16
  toBitVec := Int16.toBitVec
  fromBitVec := Int16.fromBitVec

instance : FixedWidth Int32 where
  bitWidth := 32
  toBitVec := Int32.toBitVec
  fromBitVec := Int32.fromBitVec

instance : FixedWidth Int64 where
  bitWidth := 64
  toBitVec := Int64.toBitVec
  fromBitVec := Int64.fromBitVec

end Radix
