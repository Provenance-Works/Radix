/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.UTF8.Spec

/-!
# UTF-8 Operations (Layer 2)

Executable UTF-8 helpers built on the specification layer.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- v0.3.0 Roadmap: Verified UTF-8 Model
-/

set_option autoImplicit false

namespace Radix.UTF8

abbrev Scalar := Spec.Scalar

export Spec.Scalar (ofNat? replacement null maxScalar byteCount)
export Spec (ByteClass classifyByte isLeadByte isAsciiByte isContinuationByte
             sequenceLength bom hasBOM isOverlong IsScalar IsAscii IsBMP
             IsSurrogate IsHighSurrogate IsLowSurrogate IsNoncharacter
             IsSupplementary DecodeErrorKind DecodeError DecodeStep
             decodeNextStep? maximalSubpartLength firstDecodeError?)

-- ════════════════════════════════════════════════════════════════════
-- ByteArray Conversions
-- ════════════════════════════════════════════════════════════════════

/-- Convert a `ByteArray` to a list of bytes in order. -/
def byteArrayToList (bytes : ByteArray) : List UInt8 :=
  bytes.data.toList

/-- Convert a byte list to a `ByteArray`. -/
def listToByteArray (bytes : List UInt8) : ByteArray :=
  ByteArray.mk bytes.toArray

/-- Encode a single scalar to a `ByteArray`. -/
def encodeScalar (s : Scalar) : ByteArray :=
  ByteArray.mk (Spec.encode s).toArray

/-- Encode a scalar list to a `ByteArray`. -/
def encodeScalars (scalars : List Scalar) : ByteArray :=
  ByteArray.mk (Spec.encodeAll scalars).toArray

/-- Encode a scalar to a byte list. -/
def encodeToList (s : Scalar) : List UInt8 :=
  Spec.encode s

/-- Encode a list of scalars to a byte list. -/
def encodeAllToList (scalars : List Scalar) : List UInt8 :=
  Spec.encodeAll scalars

/-- Decode the first UTF-8 scalar from a byte array. -/
def decodeNextBytes? (bytes : ByteArray) : Option (Scalar × Nat) :=
  Spec.decodeNext? (byteArrayToList bytes)

/-- Decode a full byte array into Unicode scalars. -/
def decodeBytes? (bytes : ByteArray) : Option (List Scalar) :=
  Spec.decodeAll? (byteArrayToList bytes)

/-- Decode a byte list into Unicode scalars. -/
def decodeList? (bytes : List UInt8) : Option (List Scalar) :=
  Spec.decodeAll? bytes

/-- Decode a byte array with U+FFFD replacement for invalid sequences. -/
def decodeBytesReplacing (bytes : ByteArray) : List Scalar :=
  Spec.decodeAllReplacing (byteArrayToList bytes)

/-- Decode a byte list with U+FFFD replacement for invalid sequences. -/
def decodeListReplacing (bytes : List UInt8) : List Scalar :=
  Spec.decodeAllReplacing bytes

/-- Decode the first UTF-8 chunk from a byte array with detailed errors. -/
def decodeNextBytesStep? (bytes : ByteArray) : Option Spec.DecodeStep :=
  Spec.decodeNextStep? (byteArrayToList bytes)

/-- Decode the first UTF-8 chunk from a byte list with detailed errors. -/
def decodeNextListStep? (bytes : List UInt8) : Option Spec.DecodeStep :=
  Spec.decodeNextStep? bytes

/-- Decode a byte array with Unicode maximal-subpart replacement semantics. -/
def decodeBytesReplacingMaximalSubparts (bytes : ByteArray) : List Scalar :=
  Spec.decodeAllReplacingMaximalSubparts (byteArrayToList bytes)

/-- Decode a byte list with Unicode maximal-subpart replacement semantics. -/
def decodeListReplacingMaximalSubparts (bytes : List UInt8) : List Scalar :=
  Spec.decodeAllReplacingMaximalSubparts bytes

/-- Return the first detailed decoding error from a byte array, if any. -/
def firstDecodeErrorBytes? (bytes : ByteArray) : Option Spec.DecodeError :=
  Spec.firstDecodeError? (byteArrayToList bytes)

/-- Return the first detailed decoding error from a byte list, if any. -/
def firstDecodeErrorList? (bytes : List UInt8) : Option Spec.DecodeError :=
  Spec.firstDecodeError? bytes

/-- Check whether a byte array is well-formed UTF-8. -/
def isWellFormed (bytes : ByteArray) : Bool :=
  (decodeBytes? bytes).isSome

/-- Check whether a byte list is well-formed UTF-8. -/
def isWellFormedList (bytes : List UInt8) : Bool :=
  (decodeList? bytes).isSome

/-- Number of bytes produced by encoding a scalar. -/
def encodedLength (s : Scalar) : Nat :=
  (Spec.encode s).length

/-- Number of scalars decoded from a byte array, if well-formed. -/
def scalarCount? (bytes : ByteArray) : Option Nat :=
  (decodeBytes? bytes).map List.length

/-- Number of scalars decoded from a byte list, if well-formed. -/
def scalarCountList? (bytes : List UInt8) : Option Nat :=
  (decodeList? bytes).map List.length

-- ════════════════════════════════════════════════════════════════════
-- Byte Classification
-- ════════════════════════════════════════════════════════════════════

/-- Classify each byte in a byte array. -/
def classifyBytes (bytes : ByteArray) : List Spec.ByteClass :=
  (byteArrayToList bytes).map Spec.classifyByte

/-- Count the number of continuation bytes in a byte array. -/
def countContinuation (bytes : ByteArray) : Nat :=
  Spec.countContinuation (byteArrayToList bytes)

/-- Count the number of lead bytes in a byte array (scalar count estimate). -/
def countLeadBytes (bytes : ByteArray) : Nat :=
  Spec.countLeadBytes (byteArrayToList bytes)

/-- Check whether all bytes in a byte array are ASCII. -/
def allAscii (bytes : ByteArray) : Bool :=
  Spec.allAscii (byteArrayToList bytes)

-- ════════════════════════════════════════════════════════════════════
-- BOM Handling
-- ════════════════════════════════════════════════════════════════════

/-- Check whether a byte array starts with a UTF-8 BOM. -/
def hasByteOrderMark (bytes : ByteArray) : Bool :=
  Spec.hasBOM (byteArrayToList bytes)

/-- Strip a leading UTF-8 BOM from a byte array, if present. -/
def stripByteOrderMark (bytes : ByteArray) : ByteArray :=
  listToByteArray (Spec.stripBOM (byteArrayToList bytes))

-- ════════════════════════════════════════════════════════════════════
-- Scalar Queries
-- ════════════════════════════════════════════════════════════════════

/-- Get the scalar value of a scalar as a natural number. -/
def scalarValue (s : Scalar) : Nat := s.val

/-- Whether a scalar is in the ASCII range. -/
def scalarIsAscii (s : Scalar) : Bool := Spec.Scalar.isAscii s

/-- Whether a scalar is in the BMP. -/
def scalarIsBMP (s : Scalar) : Bool := Spec.Scalar.isBMP s

/-- Whether a scalar is supplementary. -/
def scalarIsSupplementary (s : Scalar) : Bool := Spec.Scalar.isSupplementary s

/-- Whether a scalar is a noncharacter. -/
def scalarIsNoncharacter (s : Scalar) : Bool := Spec.Scalar.isNoncharacter s

/-- Which Unicode plane a scalar belongs to (0–16). -/
def scalarPlane (s : Scalar) : Nat := Spec.Scalar.plane s

/-- Total byte length needed to encode a list of scalars. -/
def totalByteLength (scalars : List Scalar) : Nat :=
  Spec.encodedByteLength scalars

-- ════════════════════════════════════════════════════════════════════
-- String Interop
-- ════════════════════════════════════════════════════════════════════

/-- Convert a list of scalars to their code point values. -/
def scalarsToNats (scalars : List Scalar) : List Nat :=
  scalars.map (·.val)

/-- Attempt to convert a list of natural numbers to scalars. -/
def natsToScalars? (ns : List Nat) : Option (List Scalar) :=
  ns.mapM Spec.Scalar.ofNat?

end Radix.UTF8
