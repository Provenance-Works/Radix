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
             CombiningClass DecompositionEntry NormalizationForm
             simpleLowerNat? simpleUpperNat?
             isStarter isCombining canonicalCombiningClass supportsNormalizationForm
             canonicalDecomposition? compatibilityDecomposition? canonicalComposePair?
             normalizeScalarsNFD normalizeScalarsNFC normalizeScalarsNFKD normalizeScalarsNFKC normalizeScalars?
             isNormalizedNFD isNormalizedNFC isNormalizedNFKD isNormalizedNFKC canonicallyEquivalent
             lowercaseScalarsSimple uppercaseScalarsSimple caseFoldScalarsSimple
             caseFoldScalarsCompatibility caselessEquivalentSimple caselessEquivalentCompatibility
             GraphemeBreakProperty classifyGraphemeBreak isGraphemeBreak
             decodeNextStep? maximalSubpartLength firstDecodeError?
             toSurrogatePair fromSurrogatePair?)
export Spec.Scalar (isUppercase isLowercase toLowerAscii? toUpperAscii? toLowerSimple toUpperSimple caseFoldSimple)

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
-- UTF-16 Interop
-- ════════════════════════════════════════════════════════════════════

/-- UTF-16 code unit. -/
abbrev UTF16CodeUnit := UInt16

/-- Convert a UTF-16 array to a list of code units in order. -/
def utf16ArrayToList (units : Array UTF16CodeUnit) : List UTF16CodeUnit :=
  units.toList

/-- Convert a UTF-16 code-unit list to an array. -/
def listToUTF16Array (units : List UTF16CodeUnit) : Array UTF16CodeUnit :=
  units.toArray

/-- Detailed UTF-16 decoding error kind. -/
inductive UTF16DecodeErrorKind where
  | unexpectedLowSurrogate
  | invalidLowSurrogate
  | truncatedHighSurrogate
  deriving DecidableEq, Repr

/-- Detailed UTF-16 decoding error. -/
structure UTF16DecodeError where
  kind : UTF16DecodeErrorKind
  expectedLength : Nat
  consumed : Nat
  deriving DecidableEq, Repr

/-- Detailed UTF-16 decode step. -/
inductive UTF16DecodeStep where
  | scalar (scalar : Scalar) (consumed : Nat)
  | error (error : UTF16DecodeError)
  deriving DecidableEq, Repr

/-- Encode one scalar to a UTF-16 code-unit list. -/
def encodeScalarToUTF16List (s : Scalar) : List UTF16CodeUnit :=
  if h : 0x10000 ≤ s.val then
    let pair := Spec.toSurrogatePair s h
    [pair.1.toUInt16, pair.2.toUInt16]
  else
    [s.val.toUInt16]

/-- Encode one scalar to a UTF-16 array. -/
def encodeScalarToUTF16 (s : Scalar) : Array UTF16CodeUnit :=
  (encodeScalarToUTF16List s).toArray

/-- Encode a scalar list to a UTF-16 code-unit list. -/
def encodeScalarsToUTF16List (scalars : List Scalar) : List UTF16CodeUnit :=
  scalars.foldr (fun scalar acc => encodeScalarToUTF16List scalar ++ acc) []

/-- Encode a scalar list to a UTF-16 array. -/
def encodeScalarsToUTF16 (scalars : List Scalar) : Array UTF16CodeUnit :=
  (encodeScalarsToUTF16List scalars).toArray

/-- Decode the next UTF-16 scalar or error from a code-unit list. -/
def decodeNextUTF16ListStep? (units : List UTF16CodeUnit) : Option UTF16DecodeStep :=
  match units with
  | [] => none
  | unit :: rest =>
    let value := unit.toNat
    if 0xD800 ≤ value && value ≤ 0xDBFF then
      match rest with
      | [] =>
        some (.error { kind := .truncatedHighSurrogate, expectedLength := 2, consumed := 1 })
      | next :: _ =>
        let nextValue := next.toNat
        if 0xDC00 ≤ nextValue && nextValue ≤ 0xDFFF then
          match Spec.fromSurrogatePair? value nextValue with
          | some scalar => some (.scalar scalar 2)
          | none => some (.error { kind := .invalidLowSurrogate, expectedLength := 2, consumed := 1 })
        else
          some (.error { kind := .invalidLowSurrogate, expectedLength := 2, consumed := 1 })
    else if 0xDC00 ≤ value && value ≤ 0xDFFF then
      some (.error { kind := .unexpectedLowSurrogate, expectedLength := 1, consumed := 1 })
    else
      match Spec.Scalar.ofNat? value with
      | some scalar => some (.scalar scalar 1)
      | none => none

/-- Decode the next UTF-16 scalar or error from a code-unit array. -/
def decodeNextUTF16Step? (units : Array UTF16CodeUnit) : Option UTF16DecodeStep :=
  decodeNextUTF16ListStep? (utf16ArrayToList units)

/-- Decode a UTF-16 code-unit list strictly. -/
def decodeUTF16List? (units : List UTF16CodeUnit) : Option (List Scalar) :=
  go (units.length + 1) units []
where
  go (fuel : Nat) (remaining : List UTF16CodeUnit) (acc : List Scalar) : Option (List Scalar) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match decodeNextUTF16ListStep? remaining with
      | none => some acc.reverse
      | some (.scalar scalar consumed) =>
        go fuel (remaining.drop consumed) (scalar :: acc)
      | some (.error _) => none

/-- Decode a UTF-16 code-unit array strictly. -/
def decodeUTF16? (units : Array UTF16CodeUnit) : Option (List Scalar) :=
  decodeUTF16List? (utf16ArrayToList units)

/-- Decode a UTF-16 code-unit list with U+FFFD replacement for malformed surrogate usage. -/
def decodeUTF16ListReplacing (units : List UTF16CodeUnit) : List Scalar :=
  go (units.length + 1) units []
where
  go (fuel : Nat) (remaining : List UTF16CodeUnit) (acc : List Scalar) : List Scalar :=
    match fuel with
    | 0 => acc.reverse
    | fuel + 1 =>
      match decodeNextUTF16ListStep? remaining with
      | none => acc.reverse
      | some (.scalar scalar consumed) =>
        go fuel (remaining.drop consumed) (scalar :: acc)
      | some (.error err) =>
        go fuel (remaining.drop err.consumed) (Spec.Scalar.replacement :: acc)

/-- Decode a UTF-16 code-unit array with U+FFFD replacement for malformed surrogate usage. -/
def decodeUTF16Replacing (units : Array UTF16CodeUnit) : List Scalar :=
  decodeUTF16ListReplacing (utf16ArrayToList units)

/-- Return the first UTF-16 decoding error from a code-unit list, if any. -/
def firstUTF16DecodeErrorList? (units : List UTF16CodeUnit) : Option UTF16DecodeError :=
  go (units.length + 1) units
where
  go : Nat → List UTF16CodeUnit → Option UTF16DecodeError
    | 0, _ => none
    | _ + 1, [] => none
    | fuel + 1, remaining =>
      match decodeNextUTF16ListStep? remaining with
      | none => none
      | some (.error err) => some err
      | some (.scalar _ consumed) => go fuel (remaining.drop consumed)

/-- Return the first UTF-16 decoding error from a code-unit array, if any. -/
def firstUTF16DecodeError? (units : Array UTF16CodeUnit) : Option UTF16DecodeError :=
  firstUTF16DecodeErrorList? (utf16ArrayToList units)

/-- Count the number of scalars represented by a well-formed UTF-16 array. -/
def utf16ScalarCount? (units : Array UTF16CodeUnit) : Option Nat :=
  (decodeUTF16? units).map List.length

/-- Transcode UTF-16 code units to UTF-8 strictly. -/
def transcodeUTF16ToUTF8? (units : Array UTF16CodeUnit) : Option ByteArray :=
  (decodeUTF16? units).map encodeScalars

/-- Transcode UTF-16 code units to UTF-8 with replacement recovery. -/
def transcodeUTF16ToUTF8Replacing (units : Array UTF16CodeUnit) : ByteArray :=
  encodeScalars (decodeUTF16Replacing units)

/-- Transcode UTF-8 bytes to UTF-16 strictly. -/
def transcodeUTF8ToUTF16? (bytes : ByteArray) : Option (Array UTF16CodeUnit) :=
  (decodeBytes? bytes).map encodeScalarsToUTF16

-- ════════════════════════════════════════════════════════════════════
-- Streaming Decoding
-- ════════════════════════════════════════════════════════════════════

/-- Error recovery policy for streaming UTF-8 decoding. -/
inductive ReplacementMode where
  | perByte
  | maximalSubpart
  deriving DecidableEq, Repr

/-- Transcode UTF-8 bytes to UTF-16 with the selected UTF-8 replacement policy. -/
def transcodeUTF8ToUTF16Replacing (mode : ReplacementMode) (bytes : ByteArray) : Array UTF16CodeUnit :=
  match mode with
  | .perByte => encodeScalarsToUTF16 (decodeBytesReplacing bytes)
  | .maximalSubpart => encodeScalarsToUTF16 (decodeBytesReplacingMaximalSubparts bytes)

/-- Incremental UTF-8 decoder state.

The decoder stores a pending suffix that is a valid prefix of a UTF-8 scalar but
still needs more input before it can be decided. -/
structure StreamDecoder where
  pending : List UInt8 := []
  deriving DecidableEq, Repr

/-- Result of decoding a UTF-8 chunk incrementally. -/
structure StreamChunk where
  scalars : List Scalar
  decoder : StreamDecoder
  deriving DecidableEq, Repr

/-- Detailed failure from strict streaming decoding.

`offset` is measured in bytes from the start of the buffered view processed by
that call, including any pending prefix carried from earlier chunks. -/
structure StreamError where
  scalars : List Scalar
  error : Spec.DecodeError
  offset : Nat
  deriving DecidableEq, Repr

/-- Empty streaming decoder state. -/
def StreamDecoder.init : StreamDecoder :=
  {}

/-- Number of bytes currently buffered as an incomplete suffix. -/
def StreamDecoder.pendingByteCount (decoder : StreamDecoder) : Nat :=
  decoder.pending.length

/-- Whether the decoder is waiting for more bytes to complete a scalar. -/
def StreamDecoder.hasPending (decoder : StreamDecoder) : Bool :=
  !decoder.pending.isEmpty

/-- Buffered incomplete suffix as a `ByteArray`. -/
def StreamDecoder.pendingBytes (decoder : StreamDecoder) : ByteArray :=
  listToByteArray decoder.pending

/-- Consume as many strict UTF-8 scalars as possible from the buffered view.

Malformed subsequences produce an error immediately. Truncated suffixes are left
pending so that later chunks may complete them. -/
private def consumeStrict : Nat → Nat → List UInt8 → List Scalar → Except StreamError (List Scalar × List UInt8)
  | 0, _, bytes, acc => Except.ok (acc.reverse, bytes)
  | _ + 1, _, [], acc => Except.ok (acc.reverse, [])
  | fuel + 1, offset, bytes, acc =>
    match Spec.decodeNextStep? bytes with
    | none => Except.ok (acc.reverse, [])
    | some (.scalar scalar consumed) =>
      consumeStrict fuel (offset + consumed) (bytes.drop consumed) (scalar :: acc)
    | some (.error err) =>
      if err.kind == .truncatedSequence then
        Except.ok (acc.reverse, bytes)
      else
        Except.error
          { scalars := acc.reverse
          , error := err
          , offset := offset
          }

/-- Consume as many scalars or replacement markers as possible from the buffered
view, leaving only an incomplete suffix pending. -/
private def consumeReplacing : Nat → ReplacementMode → List UInt8 → List Scalar → (List Scalar × List UInt8)
  | 0, _, bytes, acc => (acc.reverse, bytes)
  | _ + 1, _, [], acc => (acc.reverse, [])
  | fuel + 1, mode, bytes, acc =>
    match Spec.decodeNextStep? bytes with
    | none => (acc.reverse, [])
    | some (.scalar scalar consumed) =>
      consumeReplacing fuel mode (bytes.drop consumed) (scalar :: acc)
    | some (.error err) =>
      if err.kind == .truncatedSequence then
        (acc.reverse, bytes)
      else
        let consumed :=
          match mode with
          | .perByte => 1
          | .maximalSubpart => err.consumed
        consumeReplacing fuel mode (bytes.drop consumed) (Spec.Scalar.replacement :: acc)

/-- Decode one chunk strictly, preserving an incomplete suffix across chunk boundaries. -/
def StreamDecoder.feed? (decoder : StreamDecoder) (chunk : ByteArray) : Except StreamError StreamChunk :=
  let bytes := decoder.pending ++ byteArrayToList chunk
  match consumeStrict (bytes.length + 1) 0 bytes [] with
  | Except.ok (scalars, pending) =>
    Except.ok
      { scalars := scalars
      , decoder := { pending := pending }
      }
  | Except.error err => Except.error err

/-- Decode one chunk with replacement recovery, preserving an incomplete suffix
across chunk boundaries. -/
def StreamDecoder.feedReplacing (decoder : StreamDecoder) (mode : ReplacementMode)
    (chunk : ByteArray) : StreamChunk :=
  let bytes := decoder.pending ++ byteArrayToList chunk
  let (scalars, pending) := consumeReplacing (bytes.length + 1) mode bytes []
  { scalars := scalars
  , decoder := { pending := pending }
  }

/-- Finish a strict incremental decode.

Any buffered incomplete suffix becomes a truncated-sequence error. -/
def StreamDecoder.finish? (decoder : StreamDecoder) : Except StreamError (List Scalar) :=
  let bytes := decoder.pending
  match consumeStrict (bytes.length + 1) 0 bytes [] with
  | Except.error err => Except.error err
  | Except.ok (scalars, []) => Except.ok scalars
  | Except.ok (scalars, pending) =>
    match Spec.firstDecodeError? pending with
    | some err =>
      Except.error
        { scalars := scalars
        , error := err
        , offset := bytes.length - pending.length
        }
    | none => Except.ok scalars

/-- Finish an incremental decode with replacement recovery. -/
def StreamDecoder.finishReplacing (decoder : StreamDecoder) (mode : ReplacementMode) : List Scalar :=
  match mode with
  | .perByte => Spec.decodeAllReplacing decoder.pending
  | .maximalSubpart => Spec.decodeAllReplacingMaximalSubparts decoder.pending

/-- Decode a sequence of chunks strictly. -/
def decodeChunks? (chunks : List ByteArray) : Except StreamError (List Scalar) :=
  go StreamDecoder.init [] chunks
where
  go (decoder : StreamDecoder) (acc : List Scalar) : List ByteArray → Except StreamError (List Scalar)
    | [] =>
      match decoder.finish? with
      | Except.ok tail => Except.ok (acc.reverse ++ tail)
      | Except.error err => Except.error { err with scalars := acc.reverse ++ err.scalars }
    | chunk :: rest =>
      match decoder.feed? chunk with
      | Except.ok result => go result.decoder (result.scalars.reverse ++ acc) rest
      | Except.error err => Except.error { err with scalars := acc.reverse ++ err.scalars }

/-- Decode a sequence of chunks with replacement recovery. -/
def decodeChunksReplacing (mode : ReplacementMode) (chunks : List ByteArray) : List Scalar :=
  go StreamDecoder.init [] chunks
where
  go (decoder : StreamDecoder) (acc : List Scalar) : List ByteArray → List Scalar
    | [] => acc.reverse ++ decoder.finishReplacing mode
    | chunk :: rest =>
      let result := decoder.feedReplacing mode chunk
      go result.decoder (result.scalars.reverse ++ acc) rest

-- ════════════════════════════════════════════════════════════════════
-- Cursor Traversal
-- ════════════════════════════════════════════════════════════════════

/-- UTF-8 cursor over a byte array.

The cursor offset is measured in bytes from the start of the original buffer. -/
structure Cursor where
  bytes : ByteArray
  offset : Nat := 0
  deriving DecidableEq

/-- Cursor positioned at the start of a byte array. -/
def Cursor.init (bytes : ByteArray) : Cursor :=
  { bytes := bytes }

/-- Current byte offset from the start of the original buffer. -/
def Cursor.byteOffset (cursor : Cursor) : Nat :=
  cursor.offset

/-- Number of bytes remaining from the cursor to the end of the buffer. -/
def Cursor.remainingByteCount (cursor : Cursor) : Nat :=
  cursor.bytes.size - cursor.offset

/-- Whether the cursor has reached the end of the buffer. -/
def Cursor.isAtEnd (cursor : Cursor) : Bool :=
  cursor.offset == cursor.bytes.size

/-- Remaining suffix starting at the cursor position. -/
def Cursor.remainingBytes (cursor : Cursor) : ByteArray :=
  listToByteArray ((byteArrayToList cursor.bytes).drop cursor.offset)

/-- Construct a cursor only if the requested offset is a well-formed scalar boundary. -/
def Cursor.atOffset? (bytes : ByteArray) (offset : Nat) : Option Cursor :=
  if offset ≤ bytes.size then
    match decodeList? ((byteArrayToList bytes).take offset) with
    | some _ =>
      some { bytes := bytes, offset := offset }
    | none =>
      none
  else
    none

/-- Detailed decode step at the current cursor position. -/
def Cursor.currentStep? (cursor : Cursor) : Option Spec.DecodeStep :=
  if cursor.offset ≤ cursor.bytes.size then
    decodeNextBytesStep? cursor.remainingBytes
  else
    none

/-- Current scalar at the cursor position, if the remaining suffix starts with a valid scalar. -/
def Cursor.current? (cursor : Cursor) : Option Scalar :=
  match cursor.currentStep? with
  | some (.scalar scalar _) => some scalar
  | _ => none

/-- Current detailed decoding error at the cursor position, if any. -/
def Cursor.currentError? (cursor : Cursor) : Option Spec.DecodeError :=
  match cursor.currentStep? with
  | some (.error err) => some err
  | _ => none

/-- Advance the cursor by one valid scalar. -/
def Cursor.advance? (cursor : Cursor) : Option (Scalar × Cursor) :=
  match cursor.currentStep? with
  | some (.scalar scalar consumed) =>
    some (scalar, { cursor with offset := cursor.offset + consumed })
  | _ => none

/-- Advance the cursor by one scalar or replacement marker using the selected recovery mode. -/
def Cursor.advanceReplacing (mode : ReplacementMode) (cursor : Cursor) : Option (Scalar × Cursor) :=
  if cursor.offset ≤ cursor.bytes.size then
    if cursor.offset == cursor.bytes.size then
      none
    else
      match cursor.currentStep? with
      | some (.scalar scalar consumed) =>
        some (scalar, { cursor with offset := cursor.offset + consumed })
      | some (.error err) =>
        let consumed :=
          match mode with
          | .perByte => 1
          | .maximalSubpart => err.consumed
        some (Spec.Scalar.replacement, { cursor with offset := cursor.offset + consumed })
      | none => none
  else
    none

/-- Decode all remaining scalars from the cursor position strictly. -/
def Cursor.decodeRemaining? (cursor : Cursor) : Option (List Scalar) :=
  decodeBytes? cursor.remainingBytes

/-- Decode all remaining scalars from the cursor position with replacement recovery. -/
def Cursor.decodeRemainingReplacing (mode : ReplacementMode) (cursor : Cursor) : List Scalar :=
  match mode with
  | .perByte => decodeBytesReplacing cursor.remainingBytes
  | .maximalSubpart => decodeBytesReplacingMaximalSubparts cursor.remainingBytes

/-- Walk the entire buffer with a strict cursor. Returns `none` on the first malformed subsequence. -/
def decodeWithCursor? (bytes : ByteArray) : Option (List Scalar) :=
  go bytes.size (Cursor.init bytes) []
where
  go (fuel : Nat) (cursor : Cursor) (acc : List Scalar) : Option (List Scalar) :=
    match fuel with
    | 0 =>
      if cursor.isAtEnd then
        some acc.reverse
      else
        match cursor.decodeRemaining? with
        | some tail => some (acc.reverse ++ tail)
        | none => none
    | fuel + 1 =>
      if cursor.isAtEnd then
        some acc.reverse
      else
        match cursor.advance? with
        | some (scalar, nextCursor) => go fuel nextCursor (scalar :: acc)
        | none => none

/-- Walk the entire buffer with a replacement-aware cursor. -/
def decodeWithCursorReplacing (mode : ReplacementMode) (bytes : ByteArray) : List Scalar :=
  go bytes.size (Cursor.init bytes) []
where
  go (fuel : Nat) (cursor : Cursor) (acc : List Scalar) : List Scalar :=
    match fuel with
    | 0 =>
      if cursor.isAtEnd then
        acc.reverse
      else
        acc.reverse ++ cursor.decodeRemainingReplacing mode
    | fuel + 1 =>
      if cursor.isAtEnd then
        acc.reverse
      else
        match cursor.advanceReplacing mode with
        | some (scalar, nextCursor) => go fuel nextCursor (scalar :: acc)
        | none => acc.reverse

-- ════════════════════════════════════════════════════════════════════
-- Grapheme Traversal
-- ════════════════════════════════════════════════════════════════════

/-- A grapheme cluster represented as a scalar slice with byte offsets into the original buffer.

The cluster uses the Unicode default extended grapheme segmentation model backed by
`Spec.classifyGraphemeBreak`, regional-indicator pairing, GB11 emoji ZWJ state, and GB9c Indic conjunct state.
-/
structure Grapheme where
  scalars : List Scalar
  startOffset : Nat
  endOffset : Nat
  deriving DecidableEq, Repr

/-- Number of bytes covered by a grapheme cluster. -/
def Grapheme.byteLength (grapheme : Grapheme) : Nat :=
  grapheme.endOffset - grapheme.startOffset

/-- Number of scalars contained in a grapheme cluster. -/
def Grapheme.scalarCount (grapheme : Grapheme) : Nat :=
  grapheme.scalars.length

/-- Whether a grapheme cluster is empty. Valid decoded clusters are never empty. -/
def Grapheme.isEmpty (grapheme : Grapheme) : Bool :=
  grapheme.scalars.isEmpty

/-- Decide whether a grapheme boundary exists before `right`, given the trailing RI run. -/
private def hasGraphemeBreak
    (leftProp rightProp : Spec.GraphemeBreakProperty)
    (regionalIndicatorRun : Nat) : Bool :=
  if leftProp == .regionalIndicator && rightProp == .regionalIndicator then
    regionalIndicatorRun % 2 == 0
  else
    Spec.isGraphemeBreak leftProp rightProp

/-- Update the trailing regional-indicator run length after appending a scalar. -/
private def nextRegionalIndicatorRun
    (leftProp rightProp : Spec.GraphemeBreakProperty)
    (regionalIndicatorRun : Nat) : Nat :=
  if rightProp == .regionalIndicator then
    if leftProp == .regionalIndicator then regionalIndicatorRun + 1 else 1
  else
    0

/-- State for the GB11 emoji ZWJ rule: `Extended_Pictographic Extend* ZWJ × Extended_Pictographic`. -/
private inductive EmojiZWJState where
  | none
  | extendedPictographicSequence
  | zwjBridgeReady
  deriving DecidableEq, Repr

/-- Update the GB11 emoji ZWJ state after appending one grapheme-break property. -/
private def nextEmojiZWJState
    (state : EmojiZWJState)
    (prop : Spec.GraphemeBreakProperty) : EmojiZWJState :=
  match prop with
  | .extendedPictographic => .extendedPictographicSequence
  | .extend =>
    match state with
    | .extendedPictographicSequence => .extendedPictographicSequence
    | _ => .none
  | .zwj =>
    match state with
    | .extendedPictographicSequence => .zwjBridgeReady
    | _ => .none
  | _ => .none

/-- State for the GB9c Indic conjunct rule:
    `InCB=Consonant [InCB=Extend | InCB=Linker]* InCB=Linker [InCB=Extend | InCB=Linker]* × InCB=Consonant`. -/
private inductive IndicConjunctState where
  | none
  | consonantSequence
  | linkerBridgeReady
  deriving DecidableEq, Repr

/-- Update the GB9c Indic conjunct state after appending one scalar. -/
private def nextIndicConjunctState
    (state : IndicConjunctState)
    (scalar : Scalar) : IndicConjunctState :=
  match Spec.classifyIndicConjunctBreak scalar with
  | .consonant =>
    .consonantSequence
  | .extend =>
    match state with
    | .consonantSequence => .consonantSequence
    | .linkerBridgeReady => .linkerBridgeReady
    | .none => .none
  | .linker =>
    match state with
    | .consonantSequence => .linkerBridgeReady
    | .linkerBridgeReady => .linkerBridgeReady
    | .none => .none
  | .other => .none

/-- Continue collecting a strict grapheme cluster after consuming its first scalar. -/
private def collectGraphemeStrict
    (fuel : Nat)
    (startOffset : Nat)
    (cursor : Cursor)
    (scalarsRev : List Scalar)
    (leftProp : Spec.GraphemeBreakProperty)
    (regionalIndicatorRun : Nat)
    (emojiZWJState : EmojiZWJState)
    (indicConjunctState : IndicConjunctState) : Grapheme × Cursor :=
  match fuel with
  | 0 =>
    ({ scalars := scalarsRev.reverse, startOffset := startOffset, endOffset := cursor.offset }, cursor)
  | fuel + 1 =>
    match cursor.advance? with
    | some (rightScalar, nextCursor) =>
      let rightProp := Spec.classifyGraphemeBreak rightScalar
      let hasBreak :=
        if emojiZWJState == .zwjBridgeReady && rightProp == .extendedPictographic then
          false
        else if indicConjunctState == .linkerBridgeReady &&
          Spec.classifyIndicConjunctBreak rightScalar == .consonant then
          false
        else
          hasGraphemeBreak leftProp rightProp regionalIndicatorRun
      if hasBreak then
        ({ scalars := scalarsRev.reverse, startOffset := startOffset, endOffset := cursor.offset }, cursor)
      else
        let nextRun := nextRegionalIndicatorRun leftProp rightProp regionalIndicatorRun
        let nextEmojiState := nextEmojiZWJState emojiZWJState rightProp
        let nextIndicState := nextIndicConjunctState indicConjunctState rightScalar
        collectGraphemeStrict fuel startOffset nextCursor (rightScalar :: scalarsRev)
          rightProp nextRun nextEmojiState nextIndicState
    | none =>
      ({ scalars := scalarsRev.reverse, startOffset := startOffset, endOffset := cursor.offset }, cursor)

/-- Continue collecting a replacement-aware grapheme cluster after consuming its first scalar. -/
private def collectGraphemeReplacing
    (fuel : Nat)
    (mode : ReplacementMode)
    (startOffset : Nat)
    (cursor : Cursor)
    (scalarsRev : List Scalar)
    (leftProp : Spec.GraphemeBreakProperty)
    (regionalIndicatorRun : Nat)
    (emojiZWJState : EmojiZWJState)
    (indicConjunctState : IndicConjunctState) : Grapheme × Cursor :=
  match fuel with
  | 0 =>
    ({ scalars := scalarsRev.reverse, startOffset := startOffset, endOffset := cursor.offset }, cursor)
  | fuel + 1 =>
    match cursor.advanceReplacing mode with
    | some (rightScalar, nextCursor) =>
      let rightProp := Spec.classifyGraphemeBreak rightScalar
      let hasBreak :=
        if emojiZWJState == .zwjBridgeReady && rightProp == .extendedPictographic then
          false
        else if indicConjunctState == .linkerBridgeReady &&
          Spec.classifyIndicConjunctBreak rightScalar == .consonant then
          false
        else
          hasGraphemeBreak leftProp rightProp regionalIndicatorRun
      if hasBreak then
        ({ scalars := scalarsRev.reverse, startOffset := startOffset, endOffset := cursor.offset }, cursor)
      else
        let nextRun := nextRegionalIndicatorRun leftProp rightProp regionalIndicatorRun
        let nextEmojiState := nextEmojiZWJState emojiZWJState rightProp
        let nextIndicState := nextIndicConjunctState indicConjunctState rightScalar
        collectGraphemeReplacing fuel mode startOffset nextCursor (rightScalar :: scalarsRev)
          rightProp nextRun nextEmojiState nextIndicState
    | none =>
      ({ scalars := scalarsRev.reverse, startOffset := startOffset, endOffset := cursor.offset }, cursor)

/-- Advance the cursor by one grapheme cluster on well-formed UTF-8 input. -/
def Cursor.advanceGrapheme? (cursor : Cursor) : Option (Grapheme × Cursor) :=
  match cursor.advance? with
  | some (scalar, nextCursor) =>
    let property := Spec.classifyGraphemeBreak scalar
    let regionalIndicatorRun := if property == .regionalIndicator then 1 else 0
    let emojiZWJState := nextEmojiZWJState .none property
    let indicConjunctState := nextIndicConjunctState .none scalar
    some (collectGraphemeStrict cursor.remainingByteCount cursor.offset nextCursor [scalar]
      property regionalIndicatorRun emojiZWJState indicConjunctState)
  | none => none

/-- Advance the cursor by one grapheme cluster using the selected replacement policy. -/
def Cursor.advanceGraphemeReplacing (mode : ReplacementMode) (cursor : Cursor) : Option (Grapheme × Cursor) :=
  match cursor.advanceReplacing mode with
  | some (scalar, nextCursor) =>
    let property := Spec.classifyGraphemeBreak scalar
    let regionalIndicatorRun := if property == .regionalIndicator then 1 else 0
    let emojiZWJState := nextEmojiZWJState .none property
    let indicConjunctState := nextIndicConjunctState .none scalar
    some (collectGraphemeReplacing cursor.remainingByteCount mode cursor.offset nextCursor [scalar]
      property regionalIndicatorRun emojiZWJState indicConjunctState)
  | none => none

/-- Inspect the grapheme cluster at the current cursor position without advancing. -/
def Cursor.currentGrapheme? (cursor : Cursor) : Option Grapheme :=
  cursor.advanceGrapheme?.map Prod.fst

/-- Inspect the replacement-aware grapheme cluster at the current cursor position without advancing. -/
def Cursor.currentGraphemeReplacing (mode : ReplacementMode) (cursor : Cursor) : Option Grapheme :=
  (cursor.advanceGraphemeReplacing mode).map Prod.fst

/-- Decode all remaining grapheme clusters from the cursor position strictly. -/
def Cursor.decodeRemainingGraphemes? (cursor : Cursor) : Option (List Grapheme) :=
  go cursor.remainingByteCount cursor []
where
  go (fuel : Nat) (current : Cursor) (acc : List Grapheme) : Option (List Grapheme) :=
    match fuel with
    | 0 =>
      if current.isAtEnd then
        some acc.reverse
      else
        none
    | fuel + 1 =>
      if current.isAtEnd then
        some acc.reverse
      else
        match current.advanceGrapheme? with
        | some (grapheme, nextCursor) => go fuel nextCursor (grapheme :: acc)
        | none => none

/-- Decode all remaining grapheme clusters from the cursor position with replacement recovery. -/
def Cursor.decodeRemainingGraphemesReplacing (mode : ReplacementMode) (cursor : Cursor) : List Grapheme :=
  go cursor.remainingByteCount cursor []
where
  go (fuel : Nat) (current : Cursor) (acc : List Grapheme) : List Grapheme :=
    match fuel with
    | 0 => acc.reverse
    | fuel + 1 =>
      if current.isAtEnd then
        acc.reverse
      else
        match current.advanceGraphemeReplacing mode with
        | some (grapheme, nextCursor) => go fuel nextCursor (grapheme :: acc)
        | none => acc.reverse

/-- Decode a full byte array into grapheme clusters using the Unicode default
  extended grapheme rules. -/
def decodeGraphemes? (bytes : ByteArray) : Option (List Grapheme) :=
  (Cursor.init bytes).decodeRemainingGraphemes?

/-- Decode a full byte array into grapheme clusters with replacement recovery. -/
def decodeGraphemesReplacing (mode : ReplacementMode) (bytes : ByteArray) : List Grapheme :=
  (Cursor.init bytes).decodeRemainingGraphemesReplacing mode

/-- Count grapheme clusters in a well-formed byte array. -/
def graphemeCount? (bytes : ByteArray) : Option Nat :=
  (decodeGraphemes? bytes).map List.length

-- ════════════════════════════════════════════════════════════════════
-- Normalization
-- ════════════════════════════════════════════════════════════════════

/-- Normalize a well-formed UTF-8 byte array to NFD. -/
def normalizeBytesNFD? (bytes : ByteArray) : Option ByteArray :=
  (decodeBytes? bytes).map (fun scalars => encodeScalars (Spec.normalizeScalarsNFD scalars))

/-- Normalize a well-formed UTF-8 byte array to NFC. -/
def normalizeBytesNFC? (bytes : ByteArray) : Option ByteArray :=
  (decodeBytes? bytes).map (fun scalars => encodeScalars (Spec.normalizeScalarsNFC scalars))

/-- Normalize a well-formed UTF-8 byte list to NFD. -/
def normalizeListNFD? (bytes : List UInt8) : Option (List UInt8) :=
  (decodeList? bytes).map (fun scalars => encodeAllToList (Spec.normalizeScalarsNFD scalars))

/-- Normalize a well-formed UTF-8 byte list to NFC. -/
def normalizeListNFC? (bytes : List UInt8) : Option (List UInt8) :=
  (decodeList? bytes).map (fun scalars => encodeAllToList (Spec.normalizeScalarsNFC scalars))

/-- Normalize a well-formed UTF-8 byte array to NFKD. -/
def normalizeBytesNFKD? (bytes : ByteArray) : Option ByteArray :=
  (decodeBytes? bytes).map (fun scalars => encodeScalars (Spec.normalizeScalarsNFKD scalars))

/-- Normalize a well-formed UTF-8 byte array to NFKC. -/
def normalizeBytesNFKC? (bytes : ByteArray) : Option ByteArray :=
  (decodeBytes? bytes).map (fun scalars => encodeScalars (Spec.normalizeScalarsNFKC scalars))

/-- Normalize a well-formed UTF-8 byte list to NFKD. -/
def normalizeListNFKD? (bytes : List UInt8) : Option (List UInt8) :=
  (decodeList? bytes).map (fun scalars => encodeAllToList (Spec.normalizeScalarsNFKD scalars))

/-- Normalize a well-formed UTF-8 byte list to NFKC. -/
def normalizeListNFKC? (bytes : List UInt8) : Option (List UInt8) :=
  (decodeList? bytes).map (fun scalars => encodeAllToList (Spec.normalizeScalarsNFKC scalars))

/-- Normalize a well-formed UTF-8 byte array when the requested form is supported. -/
def normalizeBytes? (form : NormalizationForm) (bytes : ByteArray) : Option ByteArray := do
  let scalars ← decodeBytes? bytes
  let normalized ← Spec.normalizeScalars? form scalars
  pure (encodeScalars normalized)

/-- Normalize a well-formed UTF-8 byte list when the requested form is supported. -/
def normalizeList? (form : NormalizationForm) (bytes : List UInt8) : Option (List UInt8) := do
  let scalars ← decodeList? bytes
  let normalized ← Spec.normalizeScalars? form scalars
  pure (encodeAllToList normalized)

/-- Whether a well-formed UTF-8 byte array is already in NFD. -/
def isNormalizedBytesNFD? (bytes : ByteArray) : Option Bool :=
  (decodeBytes? bytes).map Spec.isNormalizedNFD

/-- Whether a well-formed UTF-8 byte array is already in NFC. -/
def isNormalizedBytesNFC? (bytes : ByteArray) : Option Bool :=
  (decodeBytes? bytes).map Spec.isNormalizedNFC

/-- Whether a well-formed UTF-8 byte array is already in NFKD. -/
def isNormalizedBytesNFKD? (bytes : ByteArray) : Option Bool :=
  (decodeBytes? bytes).map Spec.isNormalizedNFKD

/-- Whether a well-formed UTF-8 byte array is already in NFKC. -/
def isNormalizedBytesNFKC? (bytes : ByteArray) : Option Bool :=
  (decodeBytes? bytes).map Spec.isNormalizedNFKC

/-- Whether two well-formed UTF-8 byte arrays are canonically equivalent. -/
def canonicallyEquivalentBytes? (left right : ByteArray) : Bool :=
  match decodeBytes? left, decodeBytes? right with
  | some leftScalars, some rightScalars => Spec.canonicallyEquivalent leftScalars rightScalars
  | _, _ => false

-- ════════════════════════════════════════════════════════════════════
-- Case Mapping
-- ════════════════════════════════════════════════════════════════════

/-- Apply supported simple lowercase mapping to a well-formed UTF-8 byte array. -/
def lowercaseBytesSimple? (bytes : ByteArray) : Option ByteArray :=
  (decodeBytes? bytes).map (fun scalars => encodeScalars (Spec.lowercaseScalarsSimple scalars))

/-- Apply supported simple uppercase mapping to a well-formed UTF-8 byte array. -/
def uppercaseBytesSimple? (bytes : ByteArray) : Option ByteArray :=
  (decodeBytes? bytes).map (fun scalars => encodeScalars (Spec.uppercaseScalarsSimple scalars))

/-- Apply supported simple case folding to a well-formed UTF-8 byte array. -/
def caseFoldBytesSimple? (bytes : ByteArray) : Option ByteArray :=
  (decodeBytes? bytes).map (fun scalars => encodeScalars (Spec.caseFoldScalarsSimple scalars))

/-- Apply compatibility-aware simple case folding to a well-formed UTF-8 byte array. -/
def caseFoldBytesCompatibility? (bytes : ByteArray) : Option ByteArray :=
  (decodeBytes? bytes).map (fun scalars => encodeScalars (Spec.caseFoldScalarsCompatibility scalars))

/-- Apply supported simple lowercase mapping to a well-formed UTF-8 byte list. -/
def lowercaseListSimple? (bytes : List UInt8) : Option (List UInt8) :=
  (decodeList? bytes).map (fun scalars => encodeAllToList (Spec.lowercaseScalarsSimple scalars))

/-- Apply supported simple uppercase mapping to a well-formed UTF-8 byte list. -/
def uppercaseListSimple? (bytes : List UInt8) : Option (List UInt8) :=
  (decodeList? bytes).map (fun scalars => encodeAllToList (Spec.uppercaseScalarsSimple scalars))

/-- Apply supported simple case folding to a well-formed UTF-8 byte list. -/
def caseFoldListSimple? (bytes : List UInt8) : Option (List UInt8) :=
  (decodeList? bytes).map (fun scalars => encodeAllToList (Spec.caseFoldScalarsSimple scalars))

/-- Apply compatibility-aware simple case folding to a well-formed UTF-8 byte list. -/
def caseFoldListCompatibility? (bytes : List UInt8) : Option (List UInt8) :=
  (decodeList? bytes).map (fun scalars => encodeAllToList (Spec.caseFoldScalarsCompatibility scalars))

/-- Whether two well-formed UTF-8 byte arrays are equal under the supported simple case-folding subset. -/
def equalsCaseFoldSimpleBytes? (left right : ByteArray) : Bool :=
  match decodeBytes? left, decodeBytes? right with
  | some leftScalars, some rightScalars => Spec.caselessEquivalentSimple leftScalars rightScalars
  | _, _ => false

/-- Whether two well-formed UTF-8 byte arrays are equal under the supported compatibility-aware case-folding subset. -/
def equalsCaseFoldCompatibilityBytes? (left right : ByteArray) : Bool :=
  match decodeBytes? left, decodeBytes? right with
  | some leftScalars, some rightScalars => Spec.caselessEquivalentCompatibility leftScalars rightScalars
  | _, _ => false

-- ════════════════════════════════════════════════════════════════════
-- Text Search and Slicing
-- ════════════════════════════════════════════════════════════════════

/-- Compute cumulative boundary offsets from a list of widths, including both 0 and the final end offset. -/
private def boundaryOffsetsFromWidths (widths : List Nat) : List Nat :=
  go 0 widths []
where
  go (offset : Nat) (remaining : List Nat) (acc : List Nat) : List Nat :=
    match remaining with
    | [] => (offset :: acc).reverse
    | width :: rest => go (offset + width) rest (offset :: acc)

/-- Whether `prefix` is a prefix of `xs`. -/
private def startsWithList {α : Type} [DecidableEq α] : List α → List α → Bool
  | _, [] => true
  | [], _ :: _ => false
  | x :: xs, y :: ys => x == y && startsWithList xs ys

/-- Find the first index where `needle` appears as a contiguous sublist of `haystack`. -/
private def findSublistIndex? {α : Type} [DecidableEq α] (haystack needle : List α) : Option Nat :=
  if needle.isEmpty then
    some 0
  else
    go 0 haystack
where
  go (index : Nat) (remaining : List α) : Option Nat :=
    if startsWithList remaining needle then
      some index
    else
      match remaining with
      | [] => none
      | _ :: rest => go (index + 1) rest

/-- Safe list indexing helper used by executable text operations. -/
private def listGet? {α : Type} (xs : List α) (index : Nat) : Option α :=
  match xs.drop index with
  | [] => none
  | x :: _ => some x

/-- Start offsets of all UTF-8 scalars plus the final end offset, if the buffer is well-formed. -/
def scalarBoundaryOffsets? (bytes : ByteArray) : Option (List Nat) :=
  (decodeBytes? bytes).map (fun scalars => boundaryOffsetsFromWidths (scalars.map Spec.Scalar.byteCount))

/-- Start offsets of all grapheme clusters plus the final end offset, if the buffer is well-formed. -/
def graphemeBoundaryOffsets? (bytes : ByteArray) : Option (List Nat) :=
  (decodeGraphemes? bytes).map (fun graphemes => boundaryOffsetsFromWidths (graphemes.map Grapheme.byteLength))

/-- Byte offset for the scalar boundary at the requested scalar index. The index may equal the scalar count. -/
def byteOffsetOfScalarIndex? (bytes : ByteArray) (index : Nat) : Option Nat :=
  (scalarBoundaryOffsets? bytes).bind (fun offsets => listGet? offsets index)

/-- Byte offset for the grapheme boundary at the requested grapheme index. The index may equal the grapheme count. -/
def byteOffsetOfGraphemeIndex? (bytes : ByteArray) (index : Nat) : Option Nat :=
  (graphemeBoundaryOffsets? bytes).bind (fun offsets => listGet? offsets index)

/-- Scalar at the requested scalar index, if the buffer is well-formed and the index is in range. -/
def scalarAtIndex? (bytes : ByteArray) (index : Nat) : Option Scalar :=
  (decodeBytes? bytes).bind (fun scalars => listGet? scalars index)

/-- Grapheme cluster at the requested grapheme index, if the buffer is well-formed and the index is in range. -/
def graphemeAtIndex? (bytes : ByteArray) (index : Nat) : Option Grapheme :=
  (decodeGraphemes? bytes).bind (fun graphemes => listGet? graphemes index)

/-- Extract a byte slice only when both offsets are valid UTF-8 scalar boundaries and `startOffset ≤ endOffset`. -/
def sliceBytes? (bytes : ByteArray) (startOffset endOffset : Nat) : Option ByteArray :=
  if startOffset ≤ endOffset then
    match Cursor.atOffset? bytes startOffset, Cursor.atOffset? bytes endOffset with
    | some _, some _ =>
      some <| listToByteArray (((byteArrayToList bytes).drop startOffset).take (endOffset - startOffset))
    | _, _ => none
  else
    none

/-- Extract the UTF-8 byte slice covering scalar indices `[startIndex, endIndex)`. -/
def sliceScalars? (bytes : ByteArray) (startIndex endIndex : Nat) : Option ByteArray := do
  let startOffset ← byteOffsetOfScalarIndex? bytes startIndex
  let endOffset ← byteOffsetOfScalarIndex? bytes endIndex
  sliceBytes? bytes startOffset endOffset

/-- Extract the UTF-8 byte slice covering grapheme indices `[startIndex, endIndex)`. -/
def sliceGraphemes? (bytes : ByteArray) (startIndex endIndex : Nat) : Option ByteArray := do
  let startOffset ← byteOffsetOfGraphemeIndex? bytes startIndex
  let endOffset ← byteOffsetOfGraphemeIndex? bytes endIndex
  sliceBytes? bytes startOffset endOffset

/-- Whether a well-formed UTF-8 buffer starts with the scalar sequence of another well-formed buffer. -/
def startsWithScalars (bytes : ByteArray) (prefixBytes : ByteArray) : Bool :=
  match decodeBytes? bytes, decodeBytes? prefixBytes with
  | some scalars, some prefixScalars => startsWithList scalars prefixScalars
  | _, _ => false

/-- Whether a well-formed UTF-8 buffer ends with the scalar sequence of another well-formed buffer. -/
def endsWithScalars (bytes : ByteArray) (suffixBytes : ByteArray) : Bool :=
  match decodeBytes? bytes, decodeBytes? suffixBytes with
  | some scalars, some suffixScalars => startsWithList scalars.reverse suffixScalars.reverse
  | _, _ => false

/-- Find the byte offset of the first scalar-aligned occurrence of a well-formed UTF-8 needle inside a well-formed UTF-8 haystack. -/
def findScalars? (bytes : ByteArray) (needleBytes : ByteArray) : Option Nat :=
  match decodeBytes? bytes, decodeBytes? needleBytes with
  | some scalars, some needleScalars =>
    let offsets := boundaryOffsetsFromWidths (scalars.map Spec.Scalar.byteCount)
    match findSublistIndex? scalars needleScalars with
    | some index => listGet? offsets index
    | none => none
  | _, _ => none

/-- Whether a well-formed UTF-8 buffer contains the scalar sequence of another well-formed buffer. -/
def containsScalars (bytes : ByteArray) (needleBytes : ByteArray) : Bool :=
  (findScalars? bytes needleBytes).isSome

/-- Whether a well-formed UTF-8 buffer starts with the grapheme sequence of another well-formed buffer. -/
def startsWithGraphemes (bytes : ByteArray) (prefixBytes : ByteArray) : Bool :=
  match decodeGraphemes? bytes, decodeGraphemes? prefixBytes with
  | some graphemes, some prefixGraphemes =>
    startsWithList (graphemes.map (·.scalars)) (prefixGraphemes.map (·.scalars))
  | _, _ => false

/-- Whether a well-formed UTF-8 buffer ends with the grapheme sequence of another well-formed buffer. -/
def endsWithGraphemes (bytes : ByteArray) (suffixBytes : ByteArray) : Bool :=
  match decodeGraphemes? bytes, decodeGraphemes? suffixBytes with
  | some graphemes, some suffixGraphemes =>
    startsWithList (graphemes.map (·.scalars) |>.reverse) (suffixGraphemes.map (·.scalars) |>.reverse)
  | _, _ => false

/-- Find the byte offset of the first grapheme-aligned occurrence of a well-formed UTF-8 needle inside a well-formed UTF-8 haystack. -/
def findGraphemes? (bytes : ByteArray) (needleBytes : ByteArray) : Option Nat :=
  match decodeGraphemes? bytes, decodeGraphemes? needleBytes with
  | some graphemes, some needleGraphemes =>
    let graphemeScalars := graphemes.map (·.scalars)
    let needleScalars := needleGraphemes.map (·.scalars)
    let offsets := boundaryOffsetsFromWidths (graphemes.map Grapheme.byteLength)
    match findSublistIndex? graphemeScalars needleScalars with
    | some index => listGet? offsets index
    | none => none
  | _, _ => none

/-- Whether a well-formed UTF-8 buffer contains the grapheme sequence of another well-formed buffer. -/
def containsGraphemes (bytes : ByteArray) (needleBytes : ByteArray) : Bool :=
  (findGraphemes? bytes needleBytes).isSome

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
