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
def decodeNextStep? : List UInt8 → Option DecodeStep
def decodeAll? (bytes : List UInt8) : Option (List Scalar)
def decodeAllReplacingMaximalSubparts (bytes : List UInt8) : List Scalar
def maximalSubpartLength (bytes : List UInt8) : Nat
def firstDecodeError? (bytes : List UInt8) : Option DecodeError
def WellFormed (bytes : List UInt8) : Prop
```

```lean
inductive DecodeErrorKind
  | invalidStartByte
  | unexpectedContinuationByte
  | invalidContinuationByte
  | overlongSequence
  | surrogateSequence
  | outOfRangeSequence
  | truncatedSequence

structure DecodeError where
  kind : DecodeErrorKind
  expectedLength : Nat
  consumed : Nat

inductive DecodeStep where
  | scalar (scalar : Scalar) (consumed : Nat)
  | error (error : DecodeError)
```

### Semantics

- `Scalar.ofNat?` rejects surrogate code points and values outside the Unicode range.
- `decodeNext?` rejects overlong encodings and malformed continuation bytes.
- `decodeAll?` succeeds only when the full byte sequence is valid UTF-8.
- `decodeNextStep?` classifies malformed input and reports the Unicode maximal subpart length from the current offset.
- `decodeAllReplacingMaximalSubparts` follows the Unicode 17 Chapter 3 maximal-subpart substitution examples (Tables 3-8 through 3-11).

## Operations (`UTF8.Ops`)

Executable helpers over `ByteArray`:

```lean
abbrev Scalar := Spec.Scalar

def encodeScalar (s : Scalar) : ByteArray
def encodeScalars (scalars : List Scalar) : ByteArray
def decodeNextBytes? (bytes : ByteArray) : Option (Scalar × Nat)
def decodeNextBytesStep? (bytes : ByteArray) : Option DecodeStep
def decodeBytes? (bytes : ByteArray) : Option (List Scalar)
def decodeBytesReplacing (bytes : ByteArray) : List Scalar
def decodeBytesReplacingMaximalSubparts (bytes : ByteArray) : List Scalar
def isWellFormed (bytes : ByteArray) : Bool
def encodedLength (s : Scalar) : Nat
def scalarCount? (bytes : ByteArray) : Option Nat
def firstDecodeErrorBytes? (bytes : ByteArray) : Option DecodeError
```

### Streaming API

```lean
inductive ReplacementMode
  | perByte
  | maximalSubpart

structure StreamDecoder where
  pending : List UInt8

structure StreamChunk where
  scalars : List Scalar
  decoder : StreamDecoder

structure StreamError where
  scalars : List Scalar
  error : DecodeError
  offset : Nat

def StreamDecoder.init : StreamDecoder
def StreamDecoder.feed? (decoder : StreamDecoder) (chunk : ByteArray)
  : Except StreamError StreamChunk
def StreamDecoder.feedReplacing (decoder : StreamDecoder) (mode : ReplacementMode)
  (chunk : ByteArray) : StreamChunk
def StreamDecoder.finish? (decoder : StreamDecoder) : Except StreamError (List Scalar)
def StreamDecoder.finishReplacing (decoder : StreamDecoder) (mode : ReplacementMode)
  : List Scalar

def decodeChunks? (chunks : List ByteArray) : Except StreamError (List Scalar)
def decodeChunksReplacing (mode : ReplacementMode) (chunks : List ByteArray)
  : List Scalar
```

### Replacement Modes

- `decodeBytesReplacing` preserves the legacy one-replacement-per-invalid-byte behavior.
- `decodeBytesReplacingMaximalSubparts` consumes malformed prefixes according to Unicode maximal subparts, while never consuming adjacent well-formed subsequences.
- `StreamDecoder.feed?` carries incomplete UTF-8 prefixes across chunk boundaries instead of misclassifying them as malformed.
- `StreamDecoder.finish?` turns any remaining pending prefix into a truncated-sequence error.
- `StreamDecoder.feedReplacing` and `decodeChunksReplacing` provide the same recovery policies for chunked byte streams.

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

## Conformance Coverage

- Unicode 17 Chapter 3 Table 3-7 well-formed boundary rows are covered in execution tests.
- Unicode 17 Chapter 3 Tables 3-8 through 3-11 are encoded as official maximal-subpart replacement vectors.
- Comprehensive tests exhaustively round-trip every Unicode scalar value from U+0000 through U+10FFFF excluding surrogates.
- Property and comprehensive tests cover chunked strict decode, chunked replacement decode, and end-of-stream truncation semantics.

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

def streamingDemo : IO Unit := do
  let chunk1 := ByteArray.mk #[0xF0, 0x9F]
  let chunk2 := ByteArray.mk #[0x99, 0x82, 0x21]
  match Radix.UTF8.StreamDecoder.feed? Radix.UTF8.StreamDecoder.init chunk1 with
  | Except.ok step1 =>
    match Radix.UTF8.StreamDecoder.feed? step1.decoder chunk2 with
    | Except.ok step2 =>
      IO.println s!"decoded: {step2.scalars.map (·.val)}"
    | Except.error err =>
      IO.println s!"streaming error: {reprStr err}"
  | Except.error err =>
    IO.println s!"streaming error: {reprStr err}"
```

## Related Documents

- [Bytes](bytes.md) — byte-level helpers used by downstream codecs
- [Binary](binary.md) — binary parsers and serializers that can consume UTF-8 payloads
