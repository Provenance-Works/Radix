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

export Spec.Scalar (ofNat? replacement byteCount)

/-- Convert a `ByteArray` to a list of bytes in order. -/
def byteArrayToList (bytes : ByteArray) : List UInt8 :=
  bytes.toList

/-- Encode a single scalar to a `ByteArray`. -/
def encodeScalar (s : Scalar) : ByteArray :=
  ByteArray.mk (Spec.encode s).toArray

/-- Encode a scalar list to a `ByteArray`. -/
def encodeScalars (scalars : List Scalar) : ByteArray :=
  ByteArray.mk (Spec.encodeAll scalars).toArray

/-- Decode the first UTF-8 scalar from a byte array. -/
def decodeNextBytes? (bytes : ByteArray) : Option (Scalar × Nat) :=
  Spec.decodeNext? (byteArrayToList bytes)

/-- Decode a full byte array into Unicode scalars. -/
def decodeBytes? (bytes : ByteArray) : Option (List Scalar) :=
  Spec.decodeAll? (byteArrayToList bytes)

/-- Check whether a byte array is well-formed UTF-8. -/
def isWellFormed (bytes : ByteArray) : Bool :=
  (decodeBytes? bytes).isSome

/-- Number of bytes produced by encoding a scalar. -/
def encodedLength (s : Scalar) : Nat :=
  (Spec.encode s).length

/-- Number of scalars decoded from a byte array, if well-formed. -/
def scalarCount? (bytes : ByteArray) : Option Nat :=
  (decodeBytes? bytes).map List.length

end Radix.UTF8
