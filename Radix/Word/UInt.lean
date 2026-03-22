/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.Spec

/-!
# Unsigned Fixed-Width Integers (Layer 2)

This module defines `Radix.UInt8`, `Radix.UInt16`, `Radix.UInt32`, `Radix.UInt64`
as wrappers around Lean 4's built-in unsigned integer types, providing:
- Typeclass instances (`Inhabited`, `BEq`, `Ord`, `ToString`, `Repr`)
- Conversion to/from Lean 4 built-in types (`toBuiltin`/`fromBuiltin`)
- Conversion to/from `BitVec` for Layer 3 specification bridging
- Basic arithmetic operators (`+`, `-`, `*`) via `@[inline]` definitions

## Architecture

This is a **Layer 2 (Verified Implementation)** module.
- Imports Layer 3 (`Word.Spec`) for specification reference.
- MUST NOT import any Layer 1 modules.

## References

- FR-001.1: Unsigned integer types
- ADR-003: Wrapping built-in types for zero-cost abstraction
- NFR-002: Zero-cost abstractions
-/

namespace Radix

/-! ## UInt8 -/

/-- 8-bit unsigned integer wrapping Lean 4's built-in `UInt8`. -/
structure UInt8 where
  val : _root_.UInt8
  deriving DecidableEq

namespace UInt8

/-- Bit width of `UInt8`. -/
def bitWidth : Nat := 8

instance : Inhabited UInt8 := ⟨⟨0⟩⟩
instance : BEq UInt8 := ⟨fun a b => a.val == b.val⟩
instance : Ord UInt8 := ⟨fun a b => compare a.val b.val⟩
instance : ToString UInt8 := ⟨fun a => toString a.val⟩
instance : Repr UInt8 := ⟨fun a n => reprPrec a.val n⟩
instance {n : Nat} : OfNat UInt8 n := ⟨⟨OfNat.ofNat n⟩⟩

/-- Convert to Lean 4 built-in `UInt8`. -/
@[inline] def toBuiltin (x : UInt8) : _root_.UInt8 := x.val

/-- Convert from Lean 4 built-in `UInt8`. -/
@[inline] def fromBuiltin (x : _root_.UInt8) : UInt8 := ⟨x⟩

/-- Convert to `BitVec 8` for Layer 3 specification bridging. -/
@[inline] def toBitVec (x : UInt8) : BitVec 8 := x.val.toBitVec

/-- Convert from `BitVec 8`. -/
@[inline] def fromBitVec (bv : BitVec 8) : UInt8 := ⟨.ofBitVec bv⟩

/-- Convert to `Nat`. -/
@[inline] def toNat (x : UInt8) : Nat := x.val.toNat

@[inline] instance : Add UInt8 := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub UInt8 := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul UInt8 := ⟨fun a b => ⟨a.val * b.val⟩⟩

/-- The maximum value: `255`. -/
def maxVal : UInt8 := ⟨255⟩

/-- The minimum value: `0`. -/
def minVal : UInt8 := ⟨0⟩

end UInt8

/-! ## UInt16 -/

/-- 16-bit unsigned integer wrapping Lean 4's built-in `UInt16`. -/
structure UInt16 where
  val : _root_.UInt16
  deriving DecidableEq

namespace UInt16

/-- Bit width of `UInt16`. -/
def bitWidth : Nat := 16

instance : Inhabited UInt16 := ⟨⟨0⟩⟩
instance : BEq UInt16 := ⟨fun a b => a.val == b.val⟩
instance : Ord UInt16 := ⟨fun a b => compare a.val b.val⟩
instance : ToString UInt16 := ⟨fun a => toString a.val⟩
instance : Repr UInt16 := ⟨fun a n => reprPrec a.val n⟩
instance {n : Nat} : OfNat UInt16 n := ⟨⟨OfNat.ofNat n⟩⟩

@[inline] def toBuiltin (x : UInt16) : _root_.UInt16 := x.val
@[inline] def fromBuiltin (x : _root_.UInt16) : UInt16 := ⟨x⟩
@[inline] def toBitVec (x : UInt16) : BitVec 16 := x.val.toBitVec
@[inline] def fromBitVec (bv : BitVec 16) : UInt16 := ⟨.ofBitVec bv⟩
@[inline] def toNat (x : UInt16) : Nat := x.val.toNat

@[inline] instance : Add UInt16 := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub UInt16 := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul UInt16 := ⟨fun a b => ⟨a.val * b.val⟩⟩

def maxVal : UInt16 := ⟨65535⟩
def minVal : UInt16 := ⟨0⟩

end UInt16

/-! ## UInt32 -/

/-- 32-bit unsigned integer wrapping Lean 4's built-in `UInt32`. -/
structure UInt32 where
  val : _root_.UInt32
  deriving DecidableEq

namespace UInt32

def bitWidth : Nat := 32

instance : Inhabited UInt32 := ⟨⟨0⟩⟩
instance : BEq UInt32 := ⟨fun a b => a.val == b.val⟩
instance : Ord UInt32 := ⟨fun a b => compare a.val b.val⟩
instance : ToString UInt32 := ⟨fun a => toString a.val⟩
instance : Repr UInt32 := ⟨fun a n => reprPrec a.val n⟩
instance {n : Nat} : OfNat UInt32 n := ⟨⟨OfNat.ofNat n⟩⟩

@[inline] def toBuiltin (x : UInt32) : _root_.UInt32 := x.val
@[inline] def fromBuiltin (x : _root_.UInt32) : UInt32 := ⟨x⟩
@[inline] def toBitVec (x : UInt32) : BitVec 32 := x.val.toBitVec
@[inline] def fromBitVec (bv : BitVec 32) : UInt32 := ⟨.ofBitVec bv⟩
@[inline] def toNat (x : UInt32) : Nat := x.val.toNat

@[inline] instance : Add UInt32 := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub UInt32 := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul UInt32 := ⟨fun a b => ⟨a.val * b.val⟩⟩

def maxVal : UInt32 := ⟨4294967295⟩
def minVal : UInt32 := ⟨0⟩

end UInt32

/-! ## UInt64 -/

/-- 64-bit unsigned integer wrapping Lean 4's built-in `UInt64`. -/
structure UInt64 where
  val : _root_.UInt64
  deriving DecidableEq

namespace UInt64

def bitWidth : Nat := 64

instance : Inhabited UInt64 := ⟨⟨0⟩⟩
instance : BEq UInt64 := ⟨fun a b => a.val == b.val⟩
instance : Ord UInt64 := ⟨fun a b => compare a.val b.val⟩
instance : ToString UInt64 := ⟨fun a => toString a.val⟩
instance : Repr UInt64 := ⟨fun a n => reprPrec a.val n⟩
instance {n : Nat} : OfNat UInt64 n := ⟨⟨OfNat.ofNat n⟩⟩

@[inline] def toBuiltin (x : UInt64) : _root_.UInt64 := x.val
@[inline] def fromBuiltin (x : _root_.UInt64) : UInt64 := ⟨x⟩
@[inline] def toBitVec (x : UInt64) : BitVec 64 := x.val.toBitVec
@[inline] def fromBitVec (bv : BitVec 64) : UInt64 := ⟨.ofBitVec bv⟩
@[inline] def toNat (x : UInt64) : Nat := x.val.toNat

@[inline] instance : Add UInt64 := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub UInt64 := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul UInt64 := ⟨fun a b => ⟨a.val * b.val⟩⟩

def maxVal : UInt64 := ⟨18446744073709551615⟩
def minVal : UInt64 := ⟨0⟩

end UInt64

/-! ## Generic Width Accessor -/

/-- Typeclass for types with a known bit width.
    Used to write generic code over all unsigned/signed integer types. -/
class FixedWidth (α : Type) where
  bitWidth : Nat
  toBitVec : α → BitVec bitWidth
  fromBitVec : BitVec bitWidth → α

instance : FixedWidth UInt8 where
  bitWidth := 8
  toBitVec := UInt8.toBitVec
  fromBitVec := UInt8.fromBitVec

instance : FixedWidth UInt16 where
  bitWidth := 16
  toBitVec := UInt16.toBitVec
  fromBitVec := UInt16.fromBitVec

instance : FixedWidth UInt32 where
  bitWidth := 32
  toBitVec := UInt32.toBitVec
  fromBitVec := UInt32.fromBitVec

instance : FixedWidth UInt64 where
  bitWidth := 64
  toBitVec := UInt64.toBitVec
  fromBitVec := UInt64.fromBitVec

/-! ## Lawful Fixed-Width Unsigned Integers -/

/-- Extension of `FixedWidth` with round-trip laws and wrapping arithmetic
    laws. These laws allow writing generic proofs once instead of repeating
    them for each concrete width (UInt8, UInt16, UInt32, UInt64).

    Each law is an equation relating the concrete operation on `α` to the
    corresponding `BitVec` operation, so that `BitVec`-level theorems
    (commutativity, associativity, distributivity, etc.) lift automatically
    to the concrete type. -/
class LawfulFixedWidth (α : Type) extends FixedWidth α, Add α, Sub α, Mul α where
  /-- `bitWidth > 0`: necessary for overflow predicates and modular arithmetic. -/
  bitWidth_pos : bitWidth > 0
  /-- `fromBitVec ∘ toBitVec = id` (embedding is a retraction). -/
  fromBitVec_toBitVec : ∀ x : α, fromBitVec (toBitVec x) = x
  /-- `toBitVec ∘ fromBitVec = id` (embedding is a section). -/
  toBitVec_fromBitVec : ∀ bv : BitVec bitWidth, toBitVec (fromBitVec bv) = bv
  /-- Addition commutes with `toBitVec`. -/
  toBitVec_add : ∀ x y : α, toBitVec (x + y) = toBitVec x + toBitVec y
  /-- Subtraction commutes with `toBitVec`. -/
  toBitVec_sub : ∀ x y : α, toBitVec (x - y) = toBitVec x - toBitVec y
  /-- Multiplication commutes with `toBitVec`. -/
  toBitVec_mul : ∀ x y : α, toBitVec (x * y) = toBitVec x * toBitVec y

/-- `toBitVec` is injective for any `LawfulFixedWidth` type:
    if two values have the same bit-vector representation, they are equal.
    This is the key lemma that lets us lift `BitVec`-level equalities
    to the concrete type. -/
theorem LawfulFixedWidth.toBitVec_injective {α : Type} [inst : LawfulFixedWidth α]
    {x y : α} (h : inst.toBitVec x = inst.toBitVec y) : x = y := by
  have hx := inst.fromBitVec_toBitVec x
  have hy := inst.fromBitVec_toBitVec y
  rw [← hx, h, hy]

instance : LawfulFixedWidth UInt8 where
  bitWidth_pos := by decide
  fromBitVec_toBitVec x := by cases x; simp [FixedWidth.fromBitVec, FixedWidth.toBitVec, UInt8.fromBitVec, UInt8.toBitVec]
  toBitVec_fromBitVec bv := by simp [FixedWidth.fromBitVec, FixedWidth.toBitVec, UInt8.fromBitVec, UInt8.toBitVec]
  toBitVec_add x y := by cases x; cases y; rfl
  toBitVec_sub x y := by cases x; cases y; rfl
  toBitVec_mul x y := by cases x; cases y; rfl

instance : LawfulFixedWidth UInt16 where
  bitWidth_pos := by decide
  fromBitVec_toBitVec x := by cases x; simp [FixedWidth.fromBitVec, FixedWidth.toBitVec, UInt16.fromBitVec, UInt16.toBitVec]
  toBitVec_fromBitVec bv := by simp [FixedWidth.fromBitVec, FixedWidth.toBitVec, UInt16.fromBitVec, UInt16.toBitVec]
  toBitVec_add x y := by cases x; cases y; rfl
  toBitVec_sub x y := by cases x; cases y; rfl
  toBitVec_mul x y := by cases x; cases y; rfl

instance : LawfulFixedWidth UInt32 where
  bitWidth_pos := by decide
  fromBitVec_toBitVec x := by cases x; simp [FixedWidth.fromBitVec, FixedWidth.toBitVec, UInt32.fromBitVec, UInt32.toBitVec]
  toBitVec_fromBitVec bv := by simp [FixedWidth.fromBitVec, FixedWidth.toBitVec, UInt32.fromBitVec, UInt32.toBitVec]
  toBitVec_add x y := by cases x; cases y; rfl
  toBitVec_sub x y := by cases x; cases y; rfl
  toBitVec_mul x y := by cases x; cases y; rfl

instance : LawfulFixedWidth UInt64 where
  bitWidth_pos := by decide
  fromBitVec_toBitVec x := by cases x; simp [FixedWidth.fromBitVec, FixedWidth.toBitVec, UInt64.fromBitVec, UInt64.toBitVec]
  toBitVec_fromBitVec bv := by simp [FixedWidth.fromBitVec, FixedWidth.toBitVec, UInt64.fromBitVec, UInt64.toBitVec]
  toBitVec_add x y := by cases x; cases y; rfl
  toBitVec_sub x y := by cases x; cases y; rfl
  toBitVec_mul x y := by cases x; cases y; rfl

/-! ## Lawful Bitwise Operations -/

/-- Extension of `LawfulFixedWidth` with bitwise operations and laws.
    Each law states that the concrete bitwise operation on `α` corresponds
    to the `BitVec`-level operation, allowing generic proofs of Boolean
    algebra properties (commutativity, associativity, De Morgan, etc.). -/
class LawfulBitwise (α : Type) extends LawfulFixedWidth α where
  /-- Bitwise AND. -/
  band : α → α → α
  /-- Bitwise OR. -/
  bor  : α → α → α
  /-- Bitwise XOR. -/
  bxor : α → α → α
  /-- Bitwise NOT (complement). -/
  bnot : α → α
  /-- AND commutes with `toBitVec`. -/
  toBitVec_band : ∀ x y : α, toBitVec (band x y) = toBitVec x &&& toBitVec y
  /-- OR commutes with `toBitVec`. -/
  toBitVec_bor  : ∀ x y : α, toBitVec (bor x y)  = toBitVec x ||| toBitVec y
  /-- XOR commutes with `toBitVec`. -/
  toBitVec_bxor : ∀ x y : α, toBitVec (bxor x y) = toBitVec x ^^^ toBitVec y
  /-- NOT commutes with `toBitVec`. -/
  toBitVec_bnot : ∀ x : α,   toBitVec (bnot x)   = ~~~(toBitVec x)

end Radix
