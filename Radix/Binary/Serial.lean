/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Binary.Format
import Radix.Binary.Parser

/-!
# Binary Format Serializer (Layer 2)

Format-driven serializer that writes binary data to a `ByteArray` according
to a `Format` description.

Takes a list of `FieldValue`s and serializes them according to the format,
inserting padding bytes as specified.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- P2-13 specification
- Binary behavior design doc
-/

namespace Radix.Binary

open Spec

/-! ## Serialization Error -/

/-- Errors that can occur during format-driven serialization. -/
inductive SerialError where
  /-- A required field is missing from the input. -/
  | missingField (name : String)
  /-- A field has the wrong type. -/
  | typeMismatch (name : String) (expected : String) (got : String)
  /-- A length prefix width is unsupported by the serializer. -/
  | unsupportedLengthPrefix (name : String) (prefixBytes : Nat)
  /-- A payload does not fit into the configured length prefix width. -/
  | lengthOverflow (name : String) (prefixBytes : Nat) (actualSize : Nat)
  /-- A field was provided but never consumed by the format. -/
  | unexpectedField (name : String)
  deriving Repr

instance : ToString SerialError where
  toString
    | .missingField name => s!"SerialError: missing field '{name}'"
    | .typeMismatch name exp got => s!"SerialError: field '{name}' expected {exp} got {got}"
    | .unsupportedLengthPrefix name prefixBytes =>
      s!"SerialError: field '{name}' uses unsupported length prefix width {prefixBytes}"
    | .lengthOverflow name prefixBytes actualSize =>
      s!"SerialError: field '{name}' payload size {actualSize} does not fit in {prefixBytes}-byte length prefix"
    | .unexpectedField name => s!"SerialError: unexpected field '{name}'"

/-! ## Field Value Lookup -/

/-- Find a field value by name in a list.
    Linear scan O(n); sufficient for typical format field counts. -/
def findField (name : String) (fields : List FieldValue) : Option FieldValue :=
  fields.find? (fun fv => fv.name == name)

/-- Remove the first field with the given name, preserving all others. -/
private def takeField (name : String) : List FieldValue → Option (FieldValue × List FieldValue)
  | [] => none
  | field :: rest =>
    if field.name == name then
      some (field, rest)
    else
      match takeField name rest with
      | some (found, remaining) => some (found, field :: remaining)
      | none => none

/-- Fail when serialization leaves fields unused. -/
private def ensureConsumed : List FieldValue → Except SerialError Unit
  | [] => .ok ()
  | extra :: _ => .error (.unexpectedField extra.name)

/-- A short runtime type name for serializer diagnostics. -/
private def fieldTypeName : FieldValue → String
  | .byte _ _ => "byte"
  | .uint16 _ _ => "uint16"
  | .uint32 _ _ => "uint32"
  | .uint64 _ _ => "uint64"
  | .bytes _ _ => "bytes"
  | .array _ _ => "array"

/-! ## Byte Writers -/

namespace Serial

/-- Write a single byte to the accumulator. -/
private def writeByte (acc : ByteArray) (v : Radix.UInt8) : ByteArray :=
  acc.push v.val

/-- Write a 16-bit value with the specified endianness. -/
private def writeU16 (acc : ByteArray) (v : Radix.UInt16) (endian : Spec.Endian) : ByteArray :=
  let raw := v.val
  match endian with
  | .big =>
    let b0 := (raw >>> 8).toUInt8
    let b1 := raw.toUInt8
    acc.push b0 |>.push b1
  | .little =>
    let b0 := raw.toUInt8
    let b1 := (raw >>> 8).toUInt8
    acc.push b0 |>.push b1

/-- Write a 32-bit value with the specified endianness. -/
private def writeU32 (acc : ByteArray) (v : Radix.UInt32) (endian : Spec.Endian) : ByteArray :=
  let raw := v.val
  match endian with
  | .big =>
    let b0 := (raw >>> 24).toUInt8
    let b1 := (raw >>> 16).toUInt8
    let b2 := (raw >>> 8).toUInt8
    let b3 := raw.toUInt8
    acc.push b0 |>.push b1 |>.push b2 |>.push b3
  | .little =>
    let b0 := raw.toUInt8
    let b1 := (raw >>> 8).toUInt8
    let b2 := (raw >>> 16).toUInt8
    let b3 := (raw >>> 24).toUInt8
    acc.push b0 |>.push b1 |>.push b2 |>.push b3

/-- Write a 64-bit value with the specified endianness. -/
private def writeU64 (acc : ByteArray) (v : Radix.UInt64) (endian : Spec.Endian) : ByteArray :=
  let raw := v.val
  match endian with
  | .big =>
    let b0 := (raw >>> 56).toUInt8
    let b1 := (raw >>> 48).toUInt8
    let b2 := (raw >>> 40).toUInt8
    let b3 := (raw >>> 32).toUInt8
    let b4 := (raw >>> 24).toUInt8
    let b5 := (raw >>> 16).toUInt8
    let b6 := (raw >>> 8).toUInt8
    let b7 := raw.toUInt8
    acc.push b0 |>.push b1 |>.push b2 |>.push b3
       |>.push b4 |>.push b5 |>.push b6 |>.push b7
  | .little =>
    let b0 := raw.toUInt8
    let b1 := (raw >>> 8).toUInt8
    let b2 := (raw >>> 16).toUInt8
    let b3 := (raw >>> 24).toUInt8
    let b4 := (raw >>> 32).toUInt8
    let b5 := (raw >>> 40).toUInt8
    let b6 := (raw >>> 48).toUInt8
    let b7 := (raw >>> 56).toUInt8
    acc.push b0 |>.push b1 |>.push b2 |>.push b3
       |>.push b4 |>.push b5 |>.push b6 |>.push b7

/-- Append a raw byte blob to the accumulator. -/
private def writeBytes (acc : ByteArray) (bytes : ByteArray) : ByteArray :=
  acc ++ bytes

/-- Write a length prefix with the configured width and endianness. -/
private def writeLengthPrefix (acc : ByteArray) (name : String) (prefixBytes : Nat)
    (endian : Spec.Endian) (length : Nat) : Except SerialError ByteArray :=
  match prefixBytes with
  | 1 =>
    if length ≤ 0xFF then
      .ok (writeByte acc ⟨length.toUInt8⟩)
    else
      .error (.lengthOverflow name prefixBytes length)
  | 2 =>
    if length ≤ 0xFFFF then
      .ok (writeU16 acc ⟨length.toUInt16⟩ endian)
    else
      .error (.lengthOverflow name prefixBytes length)
  | 4 =>
    if length ≤ 0xFFFFFFFF then
      .ok (writeU32 acc ⟨length.toUInt32⟩ endian)
    else
      .error (.lengthOverflow name prefixBytes length)
  | 8 =>
    if length ≤ 0xFFFFFFFFFFFFFFFF then
      .ok (writeU64 acc ⟨length.toUInt64⟩ endian)
    else
      .error (.lengthOverflow name prefixBytes length)
  | _ =>
    .error (.unsupportedLengthPrefix name prefixBytes)

/-- Write `n` zero-padding bytes. -/
def writePadding (acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | n + 1 => writePadding (acc.push 0) n

/-- Serialize field values according to a format description.
    Consumes fields from `fields` in order.
    Returns the accumulated bytes and remaining unconsumed fields. -/
def serialize (fmt : Format) (fields : List FieldValue) (acc : ByteArray) :
    Except SerialError (ByteArray × List FieldValue) :=
  match fmt with
  | .byte name =>
    match takeField name fields with
    | some (.byte _ v, remaining) => .ok (writeByte acc v, remaining)
    | some (actual, _) => .error (.typeMismatch name "byte" (fieldTypeName actual))
    | none => .error (.missingField name)
  | .uint16 name endian =>
    match takeField name fields with
    | some (.uint16 _ v, remaining) => .ok (writeU16 acc v endian, remaining)
    | some (actual, _) => .error (.typeMismatch name "uint16" (fieldTypeName actual))
    | none => .error (.missingField name)
  | .uint32 name endian =>
    match takeField name fields with
    | some (.uint32 _ v, remaining) => .ok (writeU32 acc v endian, remaining)
    | some (actual, _) => .error (.typeMismatch name "uint32" (fieldTypeName actual))
    | none => .error (.missingField name)
  | .uint64 name endian =>
    match takeField name fields with
    | some (.uint64 _ v, remaining) => .ok (writeU64 acc v endian, remaining)
    | some (actual, _) => .error (.typeMismatch name "uint64" (fieldTypeName actual))
    | none => .error (.missingField name)
  | .bytes name count =>
    match takeField name fields with
    | some (.bytes _ value, remaining) =>
      if value.size == count then
        .ok (writeBytes acc value, remaining)
      else
        .error (.typeMismatch name s!"bytes[{count}]" s!"bytes[{value.size}]")
    | some (actual, _) => .error (.typeMismatch name "bytes" (fieldTypeName actual))
    | none => .error (.missingField name)
  | .lengthPrefixedBytes name prefixBytes endian =>
    match takeField name fields with
    | some (.bytes _ value, remaining) =>
      match writeLengthPrefix acc name prefixBytes endian value.size with
      | .ok acc' => .ok (writeBytes acc' value, remaining)
      | .error e => .error e
    | some (actual, _) => .error (.typeMismatch name "bytes" (fieldTypeName actual))
    | none => .error (.missingField name)
  | .countPrefixedArray name prefixBytes endian elem =>
    match takeField name fields with
    | some (.array _ elems, remainingFields) =>
      match writeLengthPrefix acc name prefixBytes endian elems.length with
      | .error e => .error e
      | .ok acc' =>
        let rec serializeCountedArray (remaining : List (List FieldValue)) (a : ByteArray) :
            Except SerialError ByteArray :=
          match remaining with
          | [] => .ok a
          | e :: es => do
            let (a', leftover) ← serialize elem e a
            ensureConsumed leftover
            serializeCountedArray es a'
        match serializeCountedArray elems acc' with
        | .ok a => .ok (a, remainingFields)
        | .error e => .error e
    | some (actual, _) => .error (.typeMismatch name "array" (fieldTypeName actual))
    | none => .error (.missingField name)
  | .constBytes value =>
    .ok (writeBytes acc value, fields)
  | .padding count =>
    .ok (writePadding acc count, fields)
  | .align alignment =>
    .ok (writePadding acc (Spec.paddingToAlign acc.size alignment), fields)
  | .array name len elem =>
    match takeField name fields with
    | some (.array _ elems, remainingFields) =>
      if elems.length != len then
        .error (.typeMismatch name s!"array[{len}]" s!"array[{elems.length}]")
      else
        let rec serializeArray (remaining : List (List FieldValue)) (a : ByteArray) :
            Except SerialError ByteArray :=
          match remaining with
          | [] => .ok a
          | e :: es => do
            let (a', leftover) ← serialize elem e a
            ensureConsumed leftover
            serializeArray es a'
        match serializeArray elems acc with
        | .ok a => .ok (a, remainingFields)
        | .error e => .error e
    | some (actual, _) => .error (.typeMismatch name "array" (fieldTypeName actual))
    | none => .error (.missingField name)
  | .seq a b => do
    let (acc', fields') ← serialize a fields acc
    serialize b fields' acc'

end Serial

/-! ## Convenience -/

/-- Serialize field values according to a format, producing a `ByteArray`. -/
def serializeFormat (fmt : Format) (fields : List FieldValue) :
    Except SerialError ByteArray :=
  match Serial.serialize fmt fields ByteArray.empty with
  | .ok (bytes, remaining) =>
    match ensureConsumed remaining with
    | .ok () => .ok bytes
    | .error e => .error e
  | .error e => .error e

end Radix.Binary
