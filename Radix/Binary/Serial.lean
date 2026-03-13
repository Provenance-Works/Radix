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
  deriving Repr

instance : ToString SerialError where
  toString
    | .missingField name => s!"SerialError: missing field '{name}'"
    | .typeMismatch name exp got => s!"SerialError: field '{name}' expected {exp} got {got}"

/-! ## Field Value Lookup -/

/-- Find a field value by name in a list.
    Linear scan O(n); sufficient for typical format field counts. -/
def findField (name : String) (fields : List FieldValue) : Option FieldValue :=
  fields.find? (fun fv => fv.name == name)

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
    match findField name fields with
    | some (.byte _ v) => .ok (writeByte acc v, fields)
    | some _ => .error (.typeMismatch name "byte" "other")
    | none => .error (.missingField name)
  | .uint16 name endian =>
    match findField name fields with
    | some (.uint16 _ v) => .ok (writeU16 acc v endian, fields)
    | some _ => .error (.typeMismatch name "uint16" "other")
    | none => .error (.missingField name)
  | .uint32 name endian =>
    match findField name fields with
    | some (.uint32 _ v) => .ok (writeU32 acc v endian, fields)
    | some _ => .error (.typeMismatch name "uint32" "other")
    | none => .error (.missingField name)
  | .uint64 name endian =>
    match findField name fields with
    | some (.uint64 _ v) => .ok (writeU64 acc v endian, fields)
    | some _ => .error (.typeMismatch name "uint64" "other")
    | none => .error (.missingField name)
  | .padding count =>
    .ok (writePadding acc count, fields)
  | .array name len elem =>
    match findField name fields with
    | some (.array _ elems) =>
      if elems.length != len then
        .error (.typeMismatch name s!"array[{len}]" s!"array[{elems.length}]")
      else
        let rec serializeArray (remaining : List (List FieldValue)) (a : ByteArray) :
            Except SerialError ByteArray :=
          match remaining with
          | [] => .ok a
          | e :: es => do
            let (a', _) ← serialize elem e a
            serializeArray es a'
        match serializeArray elems acc with
        | .ok a => .ok (a, fields)
        | .error e => .error e
    | some _ => .error (.typeMismatch name "array" "other")
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
  | .ok (bytes, _) => .ok bytes
  | .error e => .error e

end Radix.Binary
