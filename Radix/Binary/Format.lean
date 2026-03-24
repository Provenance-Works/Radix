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
- Fixed-size primitive and blob fields (Byte, UInt16, UInt32, UInt64, Bytes)
- Padding and alignment-aware gaps
- Fixed-length repeated fields
- Sequential composition of reusable sub-formats

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
  /-- A fixed-size raw byte blob. -/
  | bytes   (name : String) (count : Nat)
  /-- A length-prefixed raw byte blob. -/
  | lengthPrefixedBytes (name : String) (prefixBytes : Nat) (endian : Endian)
  /-- A count-prefixed array of sub-formats. -/
  | countPrefixedArray (name : String) (prefixBytes : Nat) (endian : Endian) (elem : Format)
  /-- A fixed byte sequence that must match exactly during parsing. -/
  | constBytes (value : ByteArray)
  /-- Padding bytes (filled with zeros on serialization, ignored on parse). -/
  | padding (count : Nat)
  /-- Insert enough zero bytes to align the next field to the requested boundary. -/
  | align   (alignment : Nat)
  /-- A fixed-length array of sub-formats. -/
  | array   (name : String) (len : Nat) (elem : Format)
  /-- A sequence of two format descriptions (concatenation). -/
  | seq     (fst snd : Format)

instance : Repr Format where
  reprPrec fmt _ :=
    match fmt with
    | .byte name => Std.Format.text s!"Format.byte {repr name}"
    | .uint16 name endian => Std.Format.text s!"Format.uint16 {repr name} {repr endian}"
    | .uint32 name endian => Std.Format.text s!"Format.uint32 {repr name} {repr endian}"
    | .uint64 name endian => Std.Format.text s!"Format.uint64 {repr name} {repr endian}"
    | .bytes name count => Std.Format.text s!"Format.bytes {repr name} {count}"
    | .lengthPrefixedBytes name prefixBytes endian =>
      Std.Format.text s!"Format.lengthPrefixedBytes {repr name} {prefixBytes} {repr endian}"
    | .countPrefixedArray name prefixBytes endian _ =>
      Std.Format.text s!"Format.countPrefixedArray {repr name} {prefixBytes} {repr endian}"
    | .constBytes value => Std.Format.text s!"Format.constBytes size={value.size}"
    | .padding count => Std.Format.text s!"Format.padding {count}"
    | .align alignment => Std.Format.text s!"Format.align {alignment}"
    | .array name len _ =>
      Std.Format.text s!"Format.array {repr name} {len}"
    | .seq _ _ =>
      Std.Format.text "Format.seq"

namespace Format

/-! ## Static Size Computation -/

/-- Compute the fixed byte size of a format.
    Returns `none` for formats whose size cannot be determined statically. -/
def fixedEndOffset : Nat → Format → Option Nat
  | offset, .byte _        => some (offset + 1)
  | offset, .uint16 _ _    => some (offset + 2)
  | offset, .uint32 _ _    => some (offset + 4)
  | offset, .uint64 _ _    => some (offset + 8)
  | offset, .bytes _ n     => some (offset + n)
  | _, .lengthPrefixedBytes _ _ _ => none
  | _, .countPrefixedArray _ _ _ _ => none
  | offset, .constBytes v  => some (offset + v.size)
  | offset, .padding n     => some (offset + n)
  | offset, .align n       => some (Spec.alignedOffset offset n)
  | offset, .array _ len f =>
    let rec go (remaining : Nat) (off : Nat) : Option Nat :=
      match remaining with
      | 0 => some off
      | count + 1 =>
        match fixedEndOffset off f with
        | some off' => go count off'
        | none => none
    go len offset
  | offset, .seq a b       =>
    match fixedEndOffset offset a with
    | some off => fixedEndOffset off b
    | none => none

/-- Compute the fixed byte size of a format from offset 0. -/
def fixedSize (fmt : Format) : Option Nat :=
  (fixedEndOffset 0 fmt).map (· - 0)

/-! ## Field Names -/

/-- Collect all field names in a format. -/
def fieldNames : Format → List String
  | .byte name       => [name]
  | .uint16 name _   => [name]
  | .uint32 name _   => [name]
  | .uint64 name _   => [name]
  | .bytes name _    => [name]
  | .lengthPrefixedBytes name _ _ => [name]
  | .countPrefixedArray name _ _ f => name :: f.fieldNames
  | .constBytes _    => []
  | .padding _       => []
  | .align _         => []
  | .array name _ f  => name :: f.fieldNames
  | .seq a b         => a.fieldNames ++ b.fieldNames

/-! ## Field Count -/

/-- Count the number of named fields (excluding padding). -/
def fieldCount : Format → Nat
  | .byte _          => 1
  | .uint16 _ _      => 1
  | .uint32 _ _      => 1
  | .uint64 _ _      => 1
  | .bytes _ _       => 1
  | .lengthPrefixedBytes _ _ _ => 1
  | .countPrefixedArray _ _ _ f => 1 + f.fieldCount
  | .constBytes _    => 0
  | .padding _       => 0
  | .align _         => 0
  | .array _ _ f     => 1 + f.fieldCount
  | .seq a b         => a.fieldCount + b.fieldCount

/-! ## Convert to FormatSpec -/

/-- Build a `FormatSpec` from a format description, laying out fields
    sequentially starting from `offset`. Returns `(spec, endOffset)`. -/
def toFormatSpecAux (offset : Nat) : Format → FormatSpec × Nat
  | .byte name =>
    let field : Spec.FieldSpec := ⟨name, offset, Spec.FieldType.prim Spec.PrimType.byte⟩
    (⟨[field], offset + 1⟩, offset + 1)
  | .uint16 name e =>
    let field : Spec.FieldSpec := ⟨name, offset, Spec.FieldType.prim (Spec.PrimType.uint16 e)⟩
    (⟨[field], offset + 2⟩, offset + 2)
  | .uint32 name e =>
    let field : Spec.FieldSpec := ⟨name, offset, Spec.FieldType.prim (Spec.PrimType.uint32 e)⟩
    (⟨[field], offset + 4⟩, offset + 4)
  | .uint64 name e =>
    let field : Spec.FieldSpec := ⟨name, offset, Spec.FieldType.prim (Spec.PrimType.uint64 e)⟩
    (⟨[field], offset + 8⟩, offset + 8)
  | .bytes name n =>
    let field : Spec.FieldSpec := ⟨name, offset, Spec.FieldType.prim (Spec.PrimType.bytes n)⟩
    (⟨[field], offset + n⟩, offset + n)
  | .lengthPrefixedBytes name prefixBytes endian =>
    let field : Spec.FieldSpec :=
      ⟨name, offset, Spec.FieldType.var (Spec.VarLenType.lengthPrefixed prefixBytes endian)⟩
    (⟨[field], offset + prefixBytes⟩, offset + prefixBytes)
  | .countPrefixedArray name prefixBytes endian elem =>
    let elemMinSize := (toFormatSpecAux 0 elem).1.totalSize
    let field : Spec.FieldSpec :=
      ⟨name, offset, Spec.FieldType.var (Spec.VarLenType.countPrefixedArray prefixBytes endian elemMinSize)⟩
    (⟨[field], offset + prefixBytes⟩, offset + prefixBytes)
  | .constBytes value =>
    (⟨[], offset + value.size⟩, offset + value.size)
  | .padding n =>
    (⟨[], offset + n⟩, offset + n)
  | .align n =>
    let off := Spec.alignedOffset offset n
    (⟨[], off⟩, off)
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
