/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Memory.Spec
import Radix.Bytes.Spec

/-!
# Binary Format Specification (Layer 3)

This module defines the abstract specification for binary format operations:
- Format correctness conditions
- Parser/serializer correctness conditions
- Round-trip property definitions

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.

## References

- P2-10 specification
- FR-003: Byte Order and Endianness
-/

namespace Radix.Binary.Spec

/-! ## Endianness (re-exported from Bytes.Spec) -/

open Radix.Bytes.Spec (Endian)
export Radix.Bytes.Spec (Endian)

/-! ## Primitive Format Field Types -/

/-- Primitive data types that can appear in a binary format. -/
inductive PrimType where
  | byte
  | uint16 (endian : Endian)
  | uint32 (endian : Endian)
  | uint64 (endian : Endian)
  deriving DecidableEq, Repr

/-- The byte size of a primitive type. -/
def PrimType.byteSize : PrimType → Nat
  | .byte         => 1
  | .uint16 _     => 2
  | .uint32 _     => 4
  | .uint64 _     => 8

/-! ## Format Description -/

/-- A binary format is a list of typed fields with names, offsets, and sizes. -/
structure FieldSpec where
  name   : String
  offset : Nat
  ptype  : PrimType
  deriving Repr

/-- The byte range occupied by a field. -/
def FieldSpec.endOffset (f : FieldSpec) : Nat :=
  f.offset + f.ptype.byteSize

/-- A complete binary format specification. -/
structure FormatSpec where
  fields    : List FieldSpec
  totalSize : Nat
  deriving Repr

/-! ## Format Validity -/

/-- A format is valid if:
    1. All fields fit within the total size.
    2. No two fields overlap. -/
def FormatSpec.fieldsInBounds (spec : FormatSpec) : Prop :=
  ∀ f ∈ spec.fields, f.endOffset ≤ spec.totalSize

def FormatSpec.fieldsNonOverlapping (spec : FormatSpec) : Prop :=
  ∀ (f : FieldSpec), f ∈ spec.fields → ∀ (g : FieldSpec), g ∈ spec.fields → f ≠ g →
    f.endOffset ≤ g.offset ∨ g.endOffset ≤ f.offset

def FormatSpec.isValid (spec : FormatSpec) : Prop :=
  spec.fieldsInBounds ∧ spec.fieldsNonOverlapping

/-! ## Round-Trip Property Definitions -/

/-- A parse function is correct with respect to a format if it
    successfully parses any buffer that is large enough. -/
def parseCorrectness {α : Type} (parse : ByteArray → Nat → Option α) (spec : FormatSpec) : Prop :=
  ∀ (buf : ByteArray) (offset : Nat),
    offset + spec.totalSize ≤ buf.size → (parse buf offset).isSome

/-- A serialize function is correct if the output has the expected size. -/
def serializeCorrectness {α : Type} (serialize : α → ByteArray) (spec : FormatSpec) : Prop :=
  ∀ (x : α), (serialize x).size = spec.totalSize

/-- Round-trip property: parsing a serialized value yields the original. -/
def roundTrip {α : Type} (parse : ByteArray → Nat → Option α) (serialize : α → ByteArray) : Prop :=
  ∀ (x : α), parse (serialize x) 0 = some x

/-- Inverse round-trip: serializing a parsed value yields the original bytes
    (restricted to the format region). -/
def inverseRoundTrip {α : Type} (parse : ByteArray → Nat → Option α) (serialize : α → ByteArray)
    (spec : FormatSpec) : Prop :=
  ∀ (buf : ByteArray) (offset : Nat) (x : α),
    offset + spec.totalSize ≤ buf.size →
    parse buf offset = some x →
    serialize x = buf.extract offset (offset + spec.totalSize)

end Radix.Binary.Spec
