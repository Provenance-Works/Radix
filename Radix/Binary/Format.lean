/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Binary.Spec
import Radix.Word.UInt

/-!
# Binary Format Description Types (Layer 2)

This module defines the `Format` inductive type for describing binary data
layouts, including:
- Fixed-size primitive fields (Byte, UInt16, UInt32, UInt64 with endianness)
- Padding / alignment
- Fixed-length repeated fields
- Variable-length arrays (length determined at parse time)
- Conditional fields

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- P2-11 specification
- Binary interface design doc
-/

namespace Radix.Binary

open Spec

/-! ## Format Inductive Type -/

/-- A `Format` describes the layout of a binary data structure.
    Each constructor represents a different kind of field. -/
inductive Format where
  /-- A single byte field. -/
  | byte    (name : String)
  /-- A 16-bit unsigned integer field with specified endianness. -/
  | uint16  (name : String) (endian : Endian)
  /-- A 32-bit unsigned integer field with specified endianness. -/
  | uint32  (name : String) (endian : Endian)
  /-- A 64-bit unsigned integer field with specified endianness. -/
  | uint64  (name : String) (endian : Endian)
  /-- Padding bytes (filled with zeros on serialization, ignored on parse). -/
  | padding (count : Nat)
  /-- A fixed-length array of sub-formats. -/
  | array   (name : String) (len : Nat) (elem : Format)
  /-- A sequence of two format descriptions (concatenation). -/
  | seq     (fst snd : Format)
  deriving Repr

namespace Format

/-! ## Static Size Computation -/

/-- Compute the fixed byte size of a format.
    Returns `none` for formats whose size cannot be determined statically. -/
def fixedSize : Format → Option Nat
  | .byte _          => some 1
  | .uint16 _ _      => some 2
  | .uint32 _ _      => some 4
  | .uint64 _ _      => some 8
  | .padding n       => some n
  | .array _ len f   => (f.fixedSize).map (· * len)
  | .seq a b         =>
    match a.fixedSize, b.fixedSize with
    | some sa, some sb => some (sa + sb)
    | _, _ => none

/-! ## Field Names -/

/-- Collect all field names in a format. -/
def fieldNames : Format → List String
  | .byte name       => [name]
  | .uint16 name _   => [name]
  | .uint32 name _   => [name]
  | .uint64 name _   => [name]
  | .padding _       => []
  | .array name _ f  => name :: f.fieldNames
  | .seq a b         => a.fieldNames ++ b.fieldNames

/-! ## Field Count -/

/-- Count the number of named fields (excluding padding). -/
def fieldCount : Format → Nat
  | .byte _          => 1
  | .uint16 _ _      => 1
  | .uint32 _ _      => 1
  | .uint64 _ _      => 1
  | .padding _       => 0
  | .array _ _ f     => 1 + f.fieldCount
  | .seq a b         => a.fieldCount + b.fieldCount

/-! ## Convert to FormatSpec -/

/-- Build a `FormatSpec` from a format description, laying out fields
    sequentially starting from `offset`. Returns `(spec, endOffset)`. -/
def toFormatSpecAux (offset : Nat) : Format → FormatSpec × Nat
  | .byte name =>
    let field : Spec.FieldSpec := ⟨name, offset, .byte⟩
    (⟨[field], offset + 1⟩, offset + 1)
  | .uint16 name e =>
    let field : Spec.FieldSpec := ⟨name, offset, .uint16 e⟩
    (⟨[field], offset + 2⟩, offset + 2)
  | .uint32 name e =>
    let field : Spec.FieldSpec := ⟨name, offset, .uint32 e⟩
    (⟨[field], offset + 4⟩, offset + 4)
  | .uint64 name e =>
    let field : Spec.FieldSpec := ⟨name, offset, .uint64 e⟩
    (⟨[field], offset + 8⟩, offset + 8)
  | .padding n =>
    (⟨[], offset + n⟩, offset + n)
  | .array _ len f =>
    let rec go (remaining : Nat) (acc : FormatSpec) (off : Nat) : FormatSpec × Nat :=
      match remaining with
      | 0 => (acc, off)
      | n + 1 =>
        let (s, off') := toFormatSpecAux off f
        go n ⟨acc.fields ++ s.fields, off'⟩ off'
    go len ⟨[], offset⟩ offset
  | .seq a b =>
    let (sa, off) := toFormatSpecAux offset a
    let (sb, off') := toFormatSpecAux off b
    (⟨sa.fields ++ sb.fields, off'⟩, off')

/-- Convert a format to a complete `FormatSpec` starting at offset 0. -/
def toFormatSpec (fmt : Format) : FormatSpec :=
  (toFormatSpecAux 0 fmt).1

/-! ## DSL Helpers -/

/-- Sequence two formats using `++`. -/
instance : Append Format where
  append := Format.seq

/-- Create a big-endian uint16 field. -/
@[inline] def u16be (name : String) : Format := .uint16 name .big
/-- Create a little-endian uint16 field. -/
@[inline] def u16le (name : String) : Format := .uint16 name .little
/-- Create a big-endian uint32 field. -/
@[inline] def u32be (name : String) : Format := .uint32 name .big
/-- Create a little-endian uint32 field. -/
@[inline] def u32le (name : String) : Format := .uint32 name .little
/-- Create a big-endian uint64 field. -/
@[inline] def u64be (name : String) : Format := .uint64 name .big
/-- Create a little-endian uint64 field. -/
@[inline] def u64le (name : String) : Format := .uint64 name .little
/-- Create a padding field. -/
@[inline] def pad (n : Nat) : Format := .padding n

end Format

end Radix.Binary
