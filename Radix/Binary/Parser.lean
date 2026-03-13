/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Binary.Format
import Radix.Bytes.Order

/-!
# Binary Format Parser (Layer 2)

Format-driven parser that reads binary data from a `ByteArray` according
to a `Format` description.

Parsed values are returned as a heterogeneous list of `FieldValue` entries.
Each primitive type is decoded with the correct endianness using the
`Bytes.Order` module.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- P2-12 specification
- Binary behavior design doc
-/

namespace Radix.Binary

open Spec

/-- Errors that can occur during format-driven parsing. -/
inductive ParseError where
  /-- Not enough bytes remaining in the buffer. -/
  | outOfBounds (fieldName : String) (offset : Nat) (need : Nat) (have_ : Nat)
  /-- Internal error (should not happen in well-formed formats). -/
  | internal (msg : String)
  deriving Repr

instance : ToString ParseError where
  toString
    | .outOfBounds name off need have_ =>
      s!"ParseError: field '{name}' at offset {off} needs {need} bytes but only {have_} available"
    | .internal msg =>
      s!"ParseError: internal: {msg}"

/-! ## Parsed Field Values -/

/-- A single parsed field value. -/
inductive FieldValue where
  | byte   (name : String) (val : Radix.UInt8)
  | uint16 (name : String) (val : Radix.UInt16)
  | uint32 (name : String) (val : Radix.UInt32)
  | uint64 (name : String) (val : Radix.UInt64)
  | array  (name : String) (elems : List (List FieldValue))
  deriving Repr

/-- The field name of a parsed value. -/
def FieldValue.name : FieldValue → String
  | .byte n _   => n
  | .uint16 n _ => n
  | .uint32 n _ => n
  | .uint64 n _ => n
  | .array n _  => n

/-! ## Parse Result -/

/-- Parse result: list of field values and the new offset. -/
abbrev ParseResult := Except ParseError (List FieldValue × Nat)

/-! ## Format-driven Parser -/

namespace Parser

/-- Read a single byte from the buffer. -/
private def readByte (data : ByteArray) (offset : Nat) (name : String) :
    Except ParseError (Radix.UInt8 × Nat) :=
  if h : offset < data.size then
    .ok (⟨data.get offset h⟩, offset + 1)
  else
    .error (.outOfBounds name offset 1 (data.size - offset))

/-- Read a 16-bit value with the specified endianness. -/
private def readU16 (data : ByteArray) (offset : Nat) (name : String) (endian : Spec.Endian) :
    Except ParseError (Radix.UInt16 × Nat) :=
  if h : offset + 2 ≤ data.size then
    let b0 := data.get offset (by omega)
    let b1 := data.get (offset + 1) (by omega)
    let val := match endian with
      | .big    => (b0.toUInt16 <<< 8) ||| b1.toUInt16
      | .little => (b1.toUInt16 <<< 8) ||| b0.toUInt16
    .ok (⟨val⟩, offset + 2)
  else
    .error (.outOfBounds name offset 2 (data.size - offset))

/-- Read a 32-bit value with the specified endianness. -/
private def readU32 (data : ByteArray) (offset : Nat) (name : String) (endian : Spec.Endian) :
    Except ParseError (Radix.UInt32 × Nat) :=
  if h : offset + 4 ≤ data.size then
    let b0 := data.get offset (by omega)
    let b1 := data.get (offset + 1) (by omega)
    let b2 := data.get (offset + 2) (by omega)
    let b3 := data.get (offset + 3) (by omega)
    let val := match endian with
      | .big =>
        (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) |||
        (b2.toUInt32 <<< 8) ||| b3.toUInt32
      | .little =>
        (b3.toUInt32 <<< 24) ||| (b2.toUInt32 <<< 16) |||
        (b1.toUInt32 <<< 8) ||| b0.toUInt32
    .ok (⟨val⟩, offset + 4)
  else
    .error (.outOfBounds name offset 4 (data.size - offset))

/-- Read a 64-bit value with the specified endianness. -/
private def readU64 (data : ByteArray) (offset : Nat) (name : String) (endian : Spec.Endian) :
    Except ParseError (Radix.UInt64 × Nat) :=
  if h : offset + 8 ≤ data.size then
    let b0 := data.get offset (by omega)
    let b1 := data.get (offset + 1) (by omega)
    let b2 := data.get (offset + 2) (by omega)
    let b3 := data.get (offset + 3) (by omega)
    let b4 := data.get (offset + 4) (by omega)
    let b5 := data.get (offset + 5) (by omega)
    let b6 := data.get (offset + 6) (by omega)
    let b7 := data.get (offset + 7) (by omega)
    let val := match endian with
      | .big =>
        (b0.toUInt64 <<< 56) ||| (b1.toUInt64 <<< 48) |||
        (b2.toUInt64 <<< 40) ||| (b3.toUInt64 <<< 32) |||
        (b4.toUInt64 <<< 24) ||| (b5.toUInt64 <<< 16) |||
        (b6.toUInt64 <<< 8) ||| b7.toUInt64
      | .little =>
        (b7.toUInt64 <<< 56) ||| (b6.toUInt64 <<< 48) |||
        (b5.toUInt64 <<< 40) ||| (b4.toUInt64 <<< 32) |||
        (b3.toUInt64 <<< 24) ||| (b2.toUInt64 <<< 16) |||
        (b1.toUInt64 <<< 8) ||| b0.toUInt64
    .ok (⟨val⟩, offset + 8)
  else
    .error (.outOfBounds name offset 8 (data.size - offset))

/-- Parse binary data according to a format description.
    Returns a list of `FieldValue`s and the offset after the last parsed byte. -/
def parse (data : ByteArray) (fmt : Format) (offset : Nat) : ParseResult :=
  match fmt with
  | .byte name => do
    let (v, off) ← readByte data offset name
    .ok ([.byte name v], off)
  | .uint16 name endian => do
    let (v, off) ← readU16 data offset name endian
    .ok ([.uint16 name v], off)
  | .uint32 name endian => do
    let (v, off) ← readU32 data offset name endian
    .ok ([.uint32 name v], off)
  | .uint64 name endian => do
    let (v, off) ← readU64 data offset name endian
    .ok ([.uint64 name v], off)
  | .padding count =>
    if offset + count ≤ data.size then
      .ok ([], offset + count)
    else
      .error (.outOfBounds "padding" offset count (data.size - offset))
  | .array name len elem => do
    let rec parseArray (remaining : Nat) (off : Nat) (acc : List (List FieldValue)) :
        ParseResult :=
      match remaining with
      | 0 => .ok ([.array name acc.reverse], off)
      | n + 1 => do
        let (fields, off') ← parse data elem off
        parseArray n off' (fields :: acc)
    parseArray len offset []
  | .seq a b => do
    let (va, off) ← parse data a offset
    let (vb, off') ← parse data b off
    .ok (va ++ vb, off')

end Parser

/-! ## Convenience -/

/-- Parse a complete buffer from offset 0 according to the given format. -/
def parseFormat (data : ByteArray) (fmt : Format) : Except ParseError (List FieldValue) :=
  match Parser.parse data fmt 0 with
  | .ok (fields, _) => .ok fields
  | .error e => .error e

end Radix.Binary
