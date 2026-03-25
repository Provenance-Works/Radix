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

### UTF-16 API

```lean
abbrev UTF16CodeUnit := UInt16

def utf16ArrayToList (units : Array UTF16CodeUnit) : List UTF16CodeUnit
def listToUTF16Array (units : List UTF16CodeUnit) : Array UTF16CodeUnit

inductive UTF16DecodeErrorKind
  | unexpectedLowSurrogate
  | invalidLowSurrogate
  | truncatedHighSurrogate

structure UTF16DecodeError where
  kind : UTF16DecodeErrorKind
  expectedLength : Nat
  consumed : Nat

inductive UTF16DecodeStep where
  | scalar (scalar : Scalar) (consumed : Nat)
  | error (error : UTF16DecodeError)

def encodeScalarToUTF16List (s : Scalar) : List UTF16CodeUnit
def encodeScalarToUTF16 (s : Scalar) : Array UTF16CodeUnit
def encodeScalarsToUTF16List (scalars : List Scalar) : List UTF16CodeUnit
def encodeScalarsToUTF16 (scalars : List Scalar) : Array UTF16CodeUnit

def decodeNextUTF16ListStep? (units : List UTF16CodeUnit) : Option UTF16DecodeStep
def decodeNextUTF16Step? (units : Array UTF16CodeUnit) : Option UTF16DecodeStep
def decodeUTF16List? (units : List UTF16CodeUnit) : Option (List Scalar)
def decodeUTF16? (units : Array UTF16CodeUnit) : Option (List Scalar)
def decodeUTF16ListReplacing (units : List UTF16CodeUnit) : List Scalar
def decodeUTF16Replacing (units : Array UTF16CodeUnit) : List Scalar
def firstUTF16DecodeErrorList? (units : List UTF16CodeUnit) : Option UTF16DecodeError
def firstUTF16DecodeError? (units : Array UTF16CodeUnit) : Option UTF16DecodeError
def utf16ScalarCount? (units : Array UTF16CodeUnit) : Option Nat

def transcodeUTF16ToUTF8? (units : Array UTF16CodeUnit) : Option ByteArray
def transcodeUTF16ToUTF8Replacing (units : Array UTF16CodeUnit) : ByteArray
def transcodeUTF8ToUTF16? (bytes : ByteArray) : Option (Array UTF16CodeUnit)
def transcodeUTF8ToUTF16Replacing (mode : ReplacementMode) (bytes : ByteArray)
  : Array UTF16CodeUnit
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

### Cursor API

```lean
structure Cursor where
  bytes : ByteArray
  offset : Nat

def Cursor.init (bytes : ByteArray) : Cursor
def Cursor.atOffset? (bytes : ByteArray) (offset : Nat) : Option Cursor
def Cursor.byteOffset (cursor : Cursor) : Nat
def Cursor.remainingByteCount (cursor : Cursor) : Nat
def Cursor.isAtEnd (cursor : Cursor) : Bool
def Cursor.currentStep? (cursor : Cursor) : Option DecodeStep
def Cursor.current? (cursor : Cursor) : Option Scalar
def Cursor.currentError? (cursor : Cursor) : Option DecodeError
def Cursor.advance? (cursor : Cursor) : Option (Scalar × Cursor)
def Cursor.advanceReplacing (mode : ReplacementMode) (cursor : Cursor)
  : Option (Scalar × Cursor)
def Cursor.decodeRemaining? (cursor : Cursor) : Option (List Scalar)
def Cursor.decodeRemainingReplacing (mode : ReplacementMode) (cursor : Cursor)
  : List Scalar

def decodeWithCursor? (bytes : ByteArray) : Option (List Scalar)
def decodeWithCursorReplacing (mode : ReplacementMode) (bytes : ByteArray)
  : List Scalar
```

### Grapheme API

```lean
structure Grapheme where
  scalars : List Scalar
  startOffset : Nat
  endOffset : Nat

def Grapheme.byteLength (grapheme : Grapheme) : Nat
def Grapheme.scalarCount (grapheme : Grapheme) : Nat
def Grapheme.isEmpty (grapheme : Grapheme) : Bool

def Cursor.advanceGrapheme? (cursor : Cursor) : Option (Grapheme × Cursor)
def Cursor.advanceGraphemeReplacing (mode : ReplacementMode) (cursor : Cursor)
  : Option (Grapheme × Cursor)
def Cursor.currentGrapheme? (cursor : Cursor) : Option Grapheme
def Cursor.currentGraphemeReplacing (mode : ReplacementMode) (cursor : Cursor)
  : Option Grapheme
def Cursor.decodeRemainingGraphemes? (cursor : Cursor) : Option (List Grapheme)
def Cursor.decodeRemainingGraphemesReplacing (mode : ReplacementMode) (cursor : Cursor)
  : List Grapheme

def decodeGraphemes? (bytes : ByteArray) : Option (List Grapheme)
def decodeGraphemesReplacing (mode : ReplacementMode) (bytes : ByteArray)
  : List Grapheme
def graphemeCount? (bytes : ByteArray) : Option Nat
```

### Normalization API

```lean
abbrev CombiningClass := Nat

structure DecompositionEntry where
  source : Nat
  target : List Nat

inductive NormalizationForm where
  | nfd
  | nfc
  | nfkd
  | nfkc

def isStarter (ccc : CombiningClass) : Bool
def isCombining (ccc : CombiningClass) : Bool
def canonicalCombiningClass (s : Scalar) : CombiningClass
def supportsNormalizationForm (form : NormalizationForm) : Bool

def canonicalDecomposition? (s : Scalar) : Option (List Scalar)
def canonicalComposePair? (starter mark : Scalar) : Option Scalar

def normalizeScalarsNFD (scalars : List Scalar) : List Scalar
def normalizeScalarsNFC (scalars : List Scalar) : List Scalar
def normalizeScalars? (form : NormalizationForm) (scalars : List Scalar)
  : Option (List Scalar)

def isNormalizedNFD (scalars : List Scalar) : Bool
def isNormalizedNFC (scalars : List Scalar) : Bool
def canonicallyEquivalent (left right : List Scalar) : Bool

def normalizeBytesNFD? (bytes : ByteArray) : Option ByteArray
def normalizeBytesNFC? (bytes : ByteArray) : Option ByteArray
def normalizeListNFD? (bytes : List UInt8) : Option (List UInt8)
def normalizeListNFC? (bytes : List UInt8) : Option (List UInt8)
def normalizeBytes? (form : NormalizationForm) (bytes : ByteArray) : Option ByteArray
def normalizeList? (form : NormalizationForm) (bytes : List UInt8) : Option (List UInt8)
def isNormalizedBytesNFD? (bytes : ByteArray) : Option Bool
def isNormalizedBytesNFC? (bytes : ByteArray) : Option Bool
def canonicallyEquivalentBytes? (left right : ByteArray) : Bool
```

### Case Mapping API

```lean
def simpleLowerNat? (n : Nat) : Option Nat
def simpleUpperNat? (n : Nat) : Option Nat

def Scalar.isUppercase (s : Scalar) : Bool
def Scalar.isLowercase (s : Scalar) : Bool
def Scalar.toLowerAscii? (s : Scalar) : Option Scalar
def Scalar.toUpperAscii? (s : Scalar) : Option Scalar
def Scalar.toLowerSimple (s : Scalar) : Scalar
def Scalar.toUpperSimple (s : Scalar) : Scalar
def Scalar.caseFoldSimple (s : Scalar) : Scalar

def lowercaseScalarsSimple (scalars : List Scalar) : List Scalar
def uppercaseScalarsSimple (scalars : List Scalar) : List Scalar
def caseFoldScalarsSimple (scalars : List Scalar) : List Scalar
def caselessEquivalentSimple (left right : List Scalar) : Bool

def lowercaseBytesSimple? (bytes : ByteArray) : Option ByteArray
def uppercaseBytesSimple? (bytes : ByteArray) : Option ByteArray
def caseFoldBytesSimple? (bytes : ByteArray) : Option ByteArray
def lowercaseListSimple? (bytes : List UInt8) : Option (List UInt8)
def uppercaseListSimple? (bytes : List UInt8) : Option (List UInt8)
def caseFoldListSimple? (bytes : List UInt8) : Option (List UInt8)
def equalsCaseFoldSimpleBytes? (left right : ByteArray) : Bool
```

### Text Operations API

```lean
def scalarBoundaryOffsets? (bytes : ByteArray) : Option (List Nat)
def graphemeBoundaryOffsets? (bytes : ByteArray) : Option (List Nat)

def byteOffsetOfScalarIndex? (bytes : ByteArray) (index : Nat) : Option Nat
def byteOffsetOfGraphemeIndex? (bytes : ByteArray) (index : Nat) : Option Nat

def scalarAtIndex? (bytes : ByteArray) (index : Nat) : Option Scalar
def graphemeAtIndex? (bytes : ByteArray) (index : Nat) : Option Grapheme

def sliceBytes? (bytes : ByteArray) (startOffset endOffset : Nat) : Option ByteArray
def sliceScalars? (bytes : ByteArray) (startIndex endIndex : Nat) : Option ByteArray
def sliceGraphemes? (bytes : ByteArray) (startIndex endIndex : Nat) : Option ByteArray

def startsWithScalars (bytes : ByteArray) (prefixBytes : ByteArray) : Bool
def endsWithScalars (bytes : ByteArray) (suffixBytes : ByteArray) : Bool
def findScalars? (bytes : ByteArray) (needleBytes : ByteArray) : Option Nat
def containsScalars (bytes : ByteArray) (needleBytes : ByteArray) : Bool

def startsWithGraphemes (bytes : ByteArray) (prefixBytes : ByteArray) : Bool
def endsWithGraphemes (bytes : ByteArray) (suffixBytes : ByteArray) : Bool
def findGraphemes? (bytes : ByteArray) (needleBytes : ByteArray) : Option Nat
def containsGraphemes (bytes : ByteArray) (needleBytes : ByteArray) : Bool
```

### Replacement Modes

- `decodeBytesReplacing` preserves the legacy one-replacement-per-invalid-byte behavior.
- `decodeBytesReplacingMaximalSubparts` consumes malformed prefixes according to Unicode maximal subparts, while never consuming adjacent well-formed subsequences.
- `StreamDecoder.feed?` carries incomplete UTF-8 prefixes across chunk boundaries instead of misclassifying them as malformed.
- `StreamDecoder.finish?` turns any remaining pending prefix into a truncated-sequence error.
- `StreamDecoder.feedReplacing` and `decodeChunksReplacing` provide the same recovery policies for chunked byte streams.
- `Cursor.atOffset?` accepts only scalar boundaries, rejecting offsets in the middle of continuation-byte sequences.
- `Cursor.advance?` gives byte-accurate scalar stepping over well-formed buffers.
- `Cursor.advanceReplacing` provides replacement-aware cursor traversal for malformed buffers.
- `decodeGraphemes?` segments well-formed UTF-8 into grapheme clusters using the repository's simplified UAX #29 model.
- `decodeGraphemesReplacing` applies the same cluster segmentation after malformed prefixes have been replaced.
- Regional-indicator sequences are paired during grapheme traversal so flag-style two-scalar clusters stay intact.
- `normalizeScalarsNFD` performs canonical decomposition together with canonical combining-class ordering for the supported normalization subset.
- `normalizeScalarsNFC` adds canonical composition on top of NFD, including algorithmic Hangul composition and a supported Latin precomposed subset.
- `normalizeScalars?` and `normalizeBytes?` currently support `nfd` and `nfc`; `nfkd` and `nfkc` report `none` until compatibility mappings are added.
- `canonicallyEquivalent` and `canonicallyEquivalentBytes?` compare inputs through canonical decomposition, so precomposed and decomposed forms match.
- `toLowerSimple`, `toUpperSimple`, and `caseFoldSimple` cover ASCII plus the same supported Latin precomposed subset used by the current normalization tables.
- `caseFoldScalarsSimple` and `caseFoldBytesSimple?` lower the supported subset and then canonicalize through NFD, so decomposed and precomposed forms compare consistently.
- `scalarBoundaryOffsets?` and `graphemeBoundaryOffsets?` expose byte-accurate cut points and always include both `0` and the total byte length.
- `sliceBytes?` rejects offsets that are not aligned to UTF-8 scalar boundaries.
- `sliceScalars?` and `sliceGraphemes?` turn scalar or grapheme index ranges back into well-formed UTF-8 slices.
- `findScalars?` and `findGraphemes?` return the byte offset of the first aligned match, so the result can be fed back into cursor or slicing APIs.
- `startsWithScalars`, `endsWithScalars`, `containsScalars`, and their grapheme counterparts require the compared regions to align to the corresponding text boundaries.

### UTF-16 Notes

- UTF-16 strict decoding accepts BMP scalars directly and supplementary scalars through validated surrogate pairs.
- Malformed surrogate usage is classified as `unexpectedLowSurrogate`, `invalidLowSurrogate`, or `truncatedHighSurrogate`.
- UTF-16 replacement decoding consumes one malformed code unit at a time so decoding can resynchronize on the next valid code unit.
- `transcodeUTF16ToUTF8Replacing` always emits well-formed UTF-8 because malformed surrogate usage is replaced before re-encoding.

### Grapheme Notes

- Grapheme segmentation is intentionally simplified: it uses `classifyGraphemeBreak` and `isGraphemeBreak` from `UTF8.Spec`, plus regional-indicator pairing and emoji-ZWJ bridging in the executable traversal layer.
- Precomposed Hangul LV/LVT syllables are classified explicitly, so both Jamo sequences and precomposed Hangul cluster as expected under the supported rules.
- Common emoji modifier sequences, variation-selector emoji presentation, and `Extended_Pictographic Extend* ZWJ Extended_Pictographic` chains are preserved as single grapheme clusters.
- This is still not a complete UAX #29 implementation for the full Unicode grapheme-break property tables.

### Normalization Notes

- Canonical normalization currently covers algorithmic Hangul decomposition/composition plus a supported set of Latin precomposed characters and combining marks.
- Canonical ordering is stable within each starter segment, so combining-mark order is normalized without crossing starter boundaries.
- Compatibility normalization (`nfkd`/`nfkc`) is intentionally not implemented yet because it requires a much larger compatibility-mapping table.

### Case Mapping Notes

- Case mapping is currently a supported simple subset, not the full Unicode SpecialCasing or CaseFolding tables.
- The implemented subset covers ASCII plus the same Latin precomposed characters already handled by canonical normalization.
- `equalsCaseFoldSimpleBytes?` is therefore suitable for common Latin caseless comparison, but not for locale-sensitive or full-Unicode caseless matching.

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
- Property and comprehensive tests cover cursor traversal, valid boundary seeking, and cursor replacement semantics.
- Property and comprehensive tests cover grapheme clustering for combining marks, CRLF, Hangul sequences, regional indicators, emoji modifier sequences, emoji ZWJ sequences, and replacement-aware malformed input.
- Property and comprehensive tests cover UTF-16 surrogate-pair encoding, strict/replacement UTF-16 decoding, and UTF-8/UTF-16 transcoding.
- Property and comprehensive tests cover canonical decomposition/composition for supported Latin precomposed characters, canonical ordering, Hangul normalization, and canonical-equivalence checks.
- Property and comprehensive tests cover supported simple lower/upper mappings, case-fold idempotence, byte/scalar API agreement, and caseless comparison across precomposed/decomposed forms.
- Property and comprehensive tests cover scalar boundary discovery, scalar-aligned slicing, and byte-offset search for scalar subsequences.

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

def cursorDemo : IO Unit := do
  let bytes := ByteArray.mk #[0x41, 0xE2, 0x82, 0xAC]
  let cursor := Radix.UTF8.Cursor.init bytes
  match Radix.UTF8.Cursor.advance? cursor with
  | some (scalar, nextCursor) =>
    IO.println s!"first scalar: {scalar.val}, next offset: {nextCursor.byteOffset}"
  | none =>
    IO.println "cursor error"

def graphemeDemo : IO Unit := do
  let bytes := ByteArray.mk #[0x41, 0xCC, 0x81, 0x42]
  match Radix.UTF8.decodeGraphemes? bytes with
  | some graphemes =>
    IO.println s!"graphemes: {graphemes.map (fun grapheme => grapheme.scalars.map (·.val))}"
  | none =>
    IO.println "grapheme decode error"

def emojiGraphemeDemo : IO Unit := do
  let bytes := ByteArray.mk #[0xF0, 0x9F, 0x91, 0xA8, 0xE2, 0x80, 0x8D, 0xF0, 0x9F, 0x91, 0xA9]
  match Radix.UTF8.decodeGraphemes? bytes with
  | some graphemes =>
    IO.println s!"emoji graphemes: {graphemes.map (fun grapheme => grapheme.scalars.map (·.val))}"
  | none =>
    IO.println "emoji grapheme decode error"

def utf16Demo : IO Unit := do
  let units := Radix.UTF8.encodeScalarsToUTF16 [⟨0x41, by decide⟩, ⟨0x1F642, by decide⟩]
  IO.println s!"utf16 units: {units.toList.map UInt16.toNat}"
  match Radix.UTF8.decodeUTF16? units with
  | some scalars =>
    IO.println s!"decoded scalars: {scalars.map (·.val)}"
  | none =>
    IO.println "utf16 decode error"

def textOpDemo : IO Unit := do
  let bytes := ByteArray.mk #[0x41, 0xCC, 0x81, 0x42, 0xE2, 0x82, 0xAC]
  IO.println s!"scalar boundaries: {Radix.UTF8.scalarBoundaryOffsets? bytes}"
  IO.println s!"grapheme boundaries: {Radix.UTF8.graphemeBoundaryOffsets? bytes}"
  IO.println s!"slice scalars [1, 3): {Radix.UTF8.sliceScalars? bytes 1 3 |>.map ByteArray.toList}"
  IO.println s!"find scalar subsequence: {Radix.UTF8.findScalars? bytes (ByteArray.mk #[0x42, 0xE2, 0x82, 0xAC])}"

def normalizationDemo : IO Unit := do
  let composed := ByteArray.mk #[0xC3, 0x81]
  let decomposed := ByteArray.mk #[0x41, 0xCC, 0x81]
  IO.println s!"nfd(composed): {Radix.UTF8.normalizeBytesNFD? composed |>.map ByteArray.toList}"
  IO.println s!"nfc(decomposed): {Radix.UTF8.normalizeBytesNFC? decomposed |>.map ByteArray.toList}"
  IO.println s!"canonically equivalent: {Radix.UTF8.canonicallyEquivalentBytes? composed decomposed}"

def caseMappingDemo : IO Unit := do
  let upper := ByteArray.mk #[0xC3, 0x81, 0xC3, 0x87]
  let lowerDecomposed := ByteArray.mk #[0x61, 0xCC, 0x81, 0x63, 0xCC, 0xA7]
  IO.println s!"lowercase(simple): {Radix.UTF8.lowercaseBytesSimple? upper |>.map ByteArray.toList}"
  IO.println s!"casefold(simple): {Radix.UTF8.caseFoldBytesSimple? upper |>.map ByteArray.toList}"
  IO.println s!"caseless equal: {Radix.UTF8.equalsCaseFoldSimpleBytes? upper lowerDecomposed}"
```

## Related Documents

- [Bytes](bytes.md) — byte-level helpers used by downstream codecs
- [Binary](binary.md) — binary parsers and serializers that can consume UTF-8 payloads
