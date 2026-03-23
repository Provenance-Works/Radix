# UTF-8 Module API Reference

> **Module**: `Radix.UTF8`
> **Source**: `Radix/UTF8/`

## Overview

Provides a verified Unicode scalar model together with executable UTF-8 encoding and decoding helpers. The specification layer works over `List UInt8`, while the operations layer exposes `ByteArray`-based helpers suitable for downstream parsers and binary formats.

## Specification (`UTF8.Spec`)

Pure definitions for Unicode scalar validity and UTF-8 structure:

```lean
def IsScalar (n : Nat) : Prop
abbrev Scalar := { n : Nat // IsScalar n }

namespace Scalar
def ofNat? (n : Nat) : Option Scalar
def replacement : Scalar
def byteCount (s : Scalar) : Nat
end Scalar

def isContinuationByte (b : UInt8) : Bool
def continuationPayload (b : UInt8) : Nat
def encode (s : Scalar) : List UInt8
def encodeAll : List Scalar → List UInt8
def decodeNext? : List UInt8 → Option (Scalar × Nat)
def decodeAll? (bytes : List UInt8) : Option (List Scalar)
def WellFormed (bytes : List UInt8) : Prop
```

### Semantics

- `Scalar.ofNat?` rejects surrogate code points and values outside the Unicode range.
- `decodeNext?` rejects overlong encodings and malformed continuation bytes.
- `decodeAll?` succeeds only when the full byte sequence is valid UTF-8.

## Operations (`UTF8.Ops`)

Executable helpers over `ByteArray`:

```lean
abbrev Scalar := Spec.Scalar

def encodeScalar (s : Scalar) : ByteArray
def encodeScalars (scalars : List Scalar) : ByteArray
def decodeNextBytes? (bytes : ByteArray) : Option (Scalar × Nat)
def decodeBytes? (bytes : ByteArray) : Option (List Scalar)
def isWellFormed (bytes : ByteArray) : Bool
def encodedLength (s : Scalar) : Nat
def scalarCount? (bytes : ByteArray) : Option Nat
```

### Exported Constructors

```lean
def Scalar.ofNat? (n : Nat) : Option Scalar
def Scalar.replacement : Scalar
def Scalar.byteCount (s : Scalar) : Nat
```

## Proofs (`UTF8.Lemmas`)

- `encode_length_eq_byteCount`: spec-level encoding length matches the scalar length class
- `wellFormed_encode`: any value produced by `encode` is well-formed UTF-8
- `decodeNext_encode`: decoding the canonical encoding of one scalar returns the same scalar
- `decodeAll_encodeAll`: spec-level decode after encode returns the original scalar list
- `encodedLength_eq_spec`: executable encoded length agrees with the spec
- `decodeBytes_encodeScalars`: operation-layer decode after encode returns the original scalar list
- `scalarCount_encodeScalars`: operation-layer scalar counting matches the encoded list length
- `isWellFormed_encodeScalar`: operation-layer encodings are always accepted by the decoder
- `isWellFormed_encodeScalars`: full operation-layer scalar sequences are always accepted by the decoder

## Examples

```lean
import Radix.UTF8

def euro : IO Radix.UTF8.Scalar := do
  match Radix.UTF8.ofNat? 0x20AC with
  | some scalar => pure scalar
  | none => throw (IO.userError "invalid scalar")

def demo : IO Unit := do
  let scalar ← euro
  let bytes := Radix.UTF8.encodeScalar scalar
  IO.println s!"encoded: {bytes.toList}"
  IO.println s!"well formed: {Radix.UTF8.isWellFormed bytes}"
```

## Related Documents

- [Bytes](bytes.md) — byte-level helpers used by downstream codecs
- [Binary](binary.md) — binary parsers and serializers that can consume UTF-8 payloads
