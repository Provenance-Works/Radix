/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Radix.UTF8.GraphemeTables

/-!
# UTF-8 Specification (Layer 3)

Formal UTF-8 scalar encoding and decoding over raw bytes.

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 1 or Layer 2 modules.
- Defines canonical UTF-8 semantics over `List UInt8`.

## References

- v0.3.0 Roadmap: Verified UTF-8 Model
- Unicode Standard, Chapter 3 (Conformance)
- RFC 3629 (UTF-8)
-/

set_option autoImplicit false

namespace Radix.UTF8.Spec

/-- Valid Unicode scalar values exclude surrogate code points. -/
def IsScalar (n : Nat) : Prop :=
  n < 0x110000 ∧ ¬ (0xD800 ≤ n ∧ n ≤ 0xDFFF)

instance (n : Nat) : Decidable (IsScalar n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A Unicode scalar value. -/
abbrev Scalar := { n : Nat // IsScalar n }

-- ════════════════════════════════════════════════════════════════════
-- Scalar Value Predicates
-- ════════════════════════════════════════════════════════════════════

/-- Whether a code point is in the ASCII range [0, 0x7F]. -/
def IsAscii (n : Nat) : Prop := n < 0x80

instance (n : Nat) : Decidable (IsAscii n) :=
  inferInstanceAs (Decidable (n < 0x80))

/-- Whether a code point falls in the BMP (Basic Multilingual Plane). -/
def IsBMP (n : Nat) : Prop := n < 0x10000

instance (n : Nat) : Decidable (IsBMP n) :=
  inferInstanceAs (Decidable (n < 0x10000))

/-- Whether a code point is in the supplementary planes. -/
def IsSupplementary (n : Nat) : Prop := 0x10000 ≤ n ∧ n < 0x110000

instance (n : Nat) : Decidable (IsSupplementary n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether a code point is a surrogate (invalid for scalar values). -/
def IsSurrogate (n : Nat) : Prop := 0xD800 ≤ n ∧ n ≤ 0xDFFF

instance (n : Nat) : Decidable (IsSurrogate n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether a code point is a high surrogate. -/
def IsHighSurrogate (n : Nat) : Prop := 0xD800 ≤ n ∧ n ≤ 0xDBFF

instance (n : Nat) : Decidable (IsHighSurrogate n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether a code point is a low surrogate. -/
def IsLowSurrogate (n : Nat) : Prop := 0xDC00 ≤ n ∧ n ≤ 0xDFFF

instance (n : Nat) : Decidable (IsLowSurrogate n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether a code point is a noncharacter (U+FDD0..U+FDEF, or last two
    code points of each plane). -/
def IsNoncharacter (n : Nat) : Prop :=
  (0xFDD0 ≤ n ∧ n ≤ 0xFDEF) ∨
  (n % 0x10000 = 0xFFFE ∨ n % 0x10000 = 0xFFFF) ∧ n < 0x110000

instance (n : Nat) : Decidable (IsNoncharacter n) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ _))

namespace Scalar

/-- Construct a scalar value when the input is valid. -/
def ofNat? (n : Nat) : Option Scalar :=
  if h : IsScalar n then some ⟨n, h⟩ else none

/-- The Unicode replacement character U+FFFD. -/
def replacement : Scalar :=
  ⟨0xFFFD, by
    constructor
    · omega
    · intro h
      omega⟩

/-- The null scalar U+0000. -/
def null : Scalar :=
  ⟨0, by constructor <;> omega⟩

/-- The maximum scalar value U+10FFFF. -/
def maxScalar : Scalar :=
  ⟨0x10FFFF, by constructor <;> omega⟩

/-- Whether the scalar is in the ASCII range. -/
def isAscii (s : Scalar) : Bool := s.val < 0x80

/-- Whether the scalar is in the BMP. -/
def isBMP (s : Scalar) : Bool := s.val < 0x10000

/-- Whether the scalar is supplementary (above BMP). -/
def isSupplementary (s : Scalar) : Bool := 0x10000 ≤ s.val

/-- Whether the scalar is a noncharacter. -/
def isNoncharacter (s : Scalar) : Bool :=
  decide (IsNoncharacter s.val)

/-- Number of bytes required to encode the scalar in UTF-8. -/
def byteCount (s : Scalar) : Nat :=
  let n := s.val
  if n < 0x80 then 1
  else if n < 0x800 then 2
  else if n < 0x10000 then 3
  else 4

/-- The Unicode plane number (0–16). -/
def plane (s : Scalar) : Nat := s.val / 0x10000

end Scalar

/-- A byte is a UTF-8 continuation byte iff it is in `[0x80, 0xBF]`. -/
def isContinuationByte (b : UInt8) : Bool :=
  0x80 ≤ b.toNat && b.toNat < 0xC0

/-- The payload carried by a continuation byte. -/
def continuationPayload (b : UInt8) : Nat :=
  b.toNat - 0x80

-- ════════════════════════════════════════════════════════════════════
-- Byte Classification
-- ════════════════════════════════════════════════════════════════════

/-- Classification of a single byte in a UTF-8 stream. -/
inductive ByteClass where
  | ascii          -- 0x00..0x7F: single-byte character
  | leadTwo        -- 0xC2..0xDF: lead byte of 2-byte sequence
  | leadThree      -- 0xE0..0xEF: lead byte of 3-byte sequence
  | leadFour       -- 0xF0..0xF4: lead byte of 4-byte sequence
  | continuation   -- 0x80..0xBF: continuation byte
  | invalid        -- 0xC0, 0xC1, 0xF5..0xFF: invalid lead bytes
  deriving DecidableEq, Repr

/-- Classify a byte in a UTF-8 stream. -/
def classifyByte (b : UInt8) : ByteClass :=
  let n := b.toNat
  if n < 0x80 then .ascii
  else if n < 0xC0 then .continuation
  else if n < 0xC2 then .invalid       -- C0, C1: overlong 2-byte
  else if n < 0xE0 then .leadTwo
  else if n < 0xF0 then .leadThree
  else if n < 0xF5 then .leadFour
  else .invalid                          -- F5..FF

/-- Whether a byte is a valid UTF-8 lead byte. -/
def isLeadByte (b : UInt8) : Bool :=
  match classifyByte b with
  | .ascii | .leadTwo | .leadThree | .leadFour => true
  | _ => false

/-- Whether a byte is an ASCII byte. -/
def isAsciiByte (b : UInt8) : Bool := b.toNat < 0x80

/-- Number of bytes in the UTF-8 sequence starting with the given lead byte,
    or 0 if the byte is not a valid lead byte. -/
def sequenceLength (b : UInt8) : Nat :=
  match classifyByte b with
  | .ascii => 1
  | .leadTwo => 2
  | .leadThree => 3
  | .leadFour => 4
  | _ => 0

-- ════════════════════════════════════════════════════════════════════
-- BOM (Byte Order Mark)
-- ════════════════════════════════════════════════════════════════════

/-- The UTF-8 BOM sequence: EF BB BF. -/
def bom : List UInt8 := [0xEF, 0xBB, 0xBF]

/-- Whether a byte list starts with a UTF-8 BOM. -/
def hasBOM (bytes : List UInt8) : Bool :=
  bytes.take 3 == bom

/-- Strip a leading BOM if present. -/
def stripBOM (bytes : List UInt8) : List UInt8 :=
  if hasBOM bytes then bytes.drop 3 else bytes

-- ════════════════════════════════════════════════════════════════════
-- Overlong Encoding Detection
-- ════════════════════════════════════════════════════════════════════

/-- Whether a code point is overlongly encoded for a given sequence length.
    A code point is overlong if it could be represented in a shorter sequence. -/
def isOverlong (codePoint : Nat) (seqLen : Nat) : Bool :=
  match seqLen with
  | 1 => false                      -- 1-byte: 0x00..0x7F always valid
  | 2 => codePoint < 0x80           -- should be 1-byte
  | 3 => codePoint < 0x800          -- should be ≤2-byte
  | 4 => codePoint < 0x10000        -- should be ≤3-byte
  | _ => true                       -- invalid length

/-- Encode a scalar as UTF-8 bytes. -/
def encode (s : Scalar) : List UInt8 :=
  let n := s.val
  if n < 0x80 then
    [n.toUInt8]
  else if n < 0x800 then
    [((0xC0 + n / 0x40).toUInt8), ((0x80 + n % 0x40).toUInt8)]
  else if n < 0x10000 then
    [ ((0xE0 + n / 0x1000).toUInt8)
    , ((0x80 + (n / 0x40) % 0x40).toUInt8)
    , ((0x80 + n % 0x40).toUInt8)
    ]
  else
    [ ((0xF0 + n / 0x40000).toUInt8)
    , ((0x80 + (n / 0x1000) % 0x40).toUInt8)
    , ((0x80 + (n / 0x40) % 0x40).toUInt8)
    , ((0x80 + n % 0x40).toUInt8)
    ]

/-- Encode a list of scalars by concatenating the UTF-8 bytes. -/
def encodeAll : List Scalar → List UInt8
  | [] => []
  | s :: rest => encode s ++ encodeAll rest

/-- Decode the next UTF-8 scalar from the input, returning the scalar and the
    number of bytes consumed. -/
def decodeNext? : List UInt8 → Option (Scalar × Nat)
  | [] => none
  | b0 :: rest =>
    let lead := b0.toNat
    if hAscii : lead < 0x80 then
      some (⟨lead, by
        constructor
        · omega
        · intro h
          omega⟩, 1)
    else if h2 : 0xC2 ≤ lead ∧ lead < 0xE0 then
      match rest with
      | b1 :: _ =>
        if hCont : isContinuationByte b1 then
          let code := (lead - 0xC0) * 0x40 + continuationPayload b1
          if hScalar : IsScalar code then
            some (⟨code, hScalar⟩, 2)
          else none
        else none
      | [] => none
    else if h3 : 0xE0 ≤ lead ∧ lead < 0xF0 then
      match rest with
      | b1 :: b2 :: _ =>
        if hCont1 : isContinuationByte b1 then
          if hCont2 : isContinuationByte b2 then
            let code :=
              (lead - 0xE0) * 0x1000 +
              continuationPayload b1 * 0x40 +
              continuationPayload b2
            if hMin : 0x800 ≤ code then
              if hScalar : IsScalar code then
                some (⟨code, hScalar⟩, 3)
              else none
            else none
          else none
        else none
      | _ => none
    else if h4 : 0xF0 ≤ lead ∧ lead < 0xF5 then
      match rest with
      | b1 :: b2 :: b3 :: _ =>
        if hCont1 : isContinuationByte b1 then
          if hCont2 : isContinuationByte b2 then
            if hCont3 : isContinuationByte b3 then
              let code :=
                (lead - 0xF0) * 0x40000 +
                continuationPayload b1 * 0x1000 +
                continuationPayload b2 * 0x40 +
                continuationPayload b3
              if hMin : 0x10000 ≤ code then
                if hScalar : IsScalar code then
                  some (⟨code, hScalar⟩, 4)
                else none
              else none
            else none
          else none
        else none
      | _ => none
    else none

/-- Fuel-bounded UTF-8 decoding. The fuel is typically `bytes.length`. -/
def decodeAllAux : Nat → List UInt8 → Option (List Scalar)
  | 0, [] => some []
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, bytes =>
    match decodeNext? bytes with
    | none => none
    | some (scalar, consumed) =>
      match decodeAllAux fuel (bytes.drop consumed) with
      | none => none
      | some rest => some (scalar :: rest)

/-- Decode a full UTF-8 byte sequence. -/
def decodeAll? (bytes : List UInt8) : Option (List Scalar) :=
  decodeAllAux bytes.length bytes

/-- A byte sequence is well-formed UTF-8 iff it is the encoding of some scalar list. -/
def WellFormed (bytes : List UInt8) : Prop :=
  ∃ scalars, encodeAll scalars = bytes

/-- Decode with U+FFFD replacement for invalid sequences.
    Each invalid byte is replaced with a single U+FFFD. -/
def decodeReplacing : Nat → List UInt8 → List Scalar
  | 0, [] => []
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, bytes =>
    match decodeNext? bytes with
    | some (scalar, consumed) => scalar :: decodeReplacing fuel (bytes.drop consumed)
    | none => Scalar.replacement :: decodeReplacing fuel (bytes.drop 1)

/-- Decode a byte list with replacement for invalid bytes. -/
def decodeAllReplacing (bytes : List UInt8) : List Scalar :=
  decodeReplacing bytes.length bytes

-- ════════════════════════════════════════════════════════════════════
-- Detailed Decoding and Unicode Conformance Helpers
-- ════════════════════════════════════════════════════════════════════

/-- Classification of the first malformed UTF-8 subsequence. -/
inductive DecodeErrorKind where
  | invalidStartByte
  | unexpectedContinuationByte
  | invalidContinuationByte
  | overlongSequence
  | surrogateSequence
  | outOfRangeSequence
  | truncatedSequence
  deriving DecidableEq, Repr

/-- Information about the first malformed UTF-8 subsequence.

`consumed` is the Unicode maximal subpart length from the current offset, as
described in Unicode Standard Chapter 3, D93b. -/
structure DecodeError where
  kind : DecodeErrorKind
  expectedLength : Nat
  consumed : Nat
  deriving DecidableEq, Repr

/-- Result of decoding the next UTF-8 chunk from a byte stream. -/
inductive DecodeStep where
  | scalar (scalar : Scalar) (consumed : Nat)
  | error (error : DecodeError)
  deriving DecidableEq, Repr

/-- Construct a detailed decoding error. -/
private def mkDecodeError (kind : DecodeErrorKind) (expectedLength consumed : Nat) : DecodeError :=
  { kind := kind, expectedLength := expectedLength, consumed := consumed }

/-- Whether the second byte satisfies the Unicode 17 Table 3-7 bounds for the given lead byte. -/
private def secondBytePermitted (lead second : Nat) : Bool :=
  if lead == 0xE0 then 0xA0 ≤ second && second < 0xC0
  else if lead == 0xED then 0x80 ≤ second && second < 0xA0
  else if lead == 0xF0 then 0x90 ≤ second && second < 0xC0
  else if lead == 0xF4 then 0x80 ≤ second && second < 0x90
  else 0x80 ≤ second && second < 0xC0

/-- Explain why the second byte is not permitted for the given lead byte. -/
private def secondByteErrorKind (lead second : Nat) : DecodeErrorKind :=
  if second < 0x80 || 0xC0 ≤ second then .invalidContinuationByte
  else if lead == 0xE0 && second < 0xA0 then .overlongSequence
  else if lead == 0xED && 0xA0 ≤ second then .surrogateSequence
  else if lead == 0xF0 && second < 0x90 then .overlongSequence
  else if lead == 0xF4 && 0x90 ≤ second then .outOfRangeSequence
  else .invalidContinuationByte

/-- Classify the first malformed UTF-8 subsequence in a non-empty byte list. -/
private def classifyDecodeError : List UInt8 → DecodeError
  | [] => mkDecodeError .truncatedSequence 1 0
  | b0 :: rest =>
    let lead := b0.toNat
    if lead < 0x80 then
      mkDecodeError .invalidStartByte 1 1
    else if lead < 0xC0 then
      mkDecodeError .unexpectedContinuationByte 1 1
    else if lead < 0xC2 then
      mkDecodeError .overlongSequence 2 1
    else if lead < 0xE0 then
      match rest with
      | [] => mkDecodeError .truncatedSequence 2 1
      | b1 :: _ =>
        if isContinuationByte b1 then
          mkDecodeError .invalidStartByte 2 1
        else
          mkDecodeError .invalidContinuationByte 2 1
    else if lead < 0xF0 then
      match rest with
      | [] => mkDecodeError .truncatedSequence 3 1
      | [b1] =>
        if secondBytePermitted lead b1.toNat then
          mkDecodeError .truncatedSequence 3 2
        else
          mkDecodeError (secondByteErrorKind lead b1.toNat) 3 1
      | b1 :: b2 :: _ =>
        if secondBytePermitted lead b1.toNat then
          if isContinuationByte b2 then
            mkDecodeError .invalidStartByte 3 2
          else
            mkDecodeError .invalidContinuationByte 3 2
        else
          mkDecodeError (secondByteErrorKind lead b1.toNat) 3 1
    else if lead < 0xF5 then
      match rest with
      | [] => mkDecodeError .truncatedSequence 4 1
      | [b1] =>
        if secondBytePermitted lead b1.toNat then
          mkDecodeError .truncatedSequence 4 2
        else
          mkDecodeError (secondByteErrorKind lead b1.toNat) 4 1
      | [b1, b2] =>
        if secondBytePermitted lead b1.toNat then
          if isContinuationByte b2 then
            mkDecodeError .truncatedSequence 4 3
          else
            mkDecodeError .invalidContinuationByte 4 2
        else
          mkDecodeError (secondByteErrorKind lead b1.toNat) 4 1
      | b1 :: b2 :: b3 :: _ =>
        if secondBytePermitted lead b1.toNat then
          if isContinuationByte b2 then
            if isContinuationByte b3 then
              mkDecodeError .invalidStartByte 4 3
            else
              mkDecodeError .invalidContinuationByte 4 3
          else
            mkDecodeError .invalidContinuationByte 4 2
        else
          mkDecodeError (secondByteErrorKind lead b1.toNat) 4 1
    else
      mkDecodeError .invalidStartByte 1 1

/-- Decode the next UTF-8 chunk, returning either a scalar or a detailed error.

On malformed input, the returned error reports the Unicode maximal subpart
length starting at the current offset. -/
def decodeNextStep? (bytes : List UInt8) : Option DecodeStep :=
  match decodeNext? bytes with
  | some (scalar, consumed) => some (.scalar scalar consumed)
  | none =>
    match bytes with
    | [] => none
    | _ => some (.error (classifyDecodeError bytes))

/-- Unicode maximal subpart length at the current offset.

Returns `0` for the empty input, the scalar byte width for well-formed input,
and the maximal subpart length for malformed input. -/
def maximalSubpartLength (bytes : List UInt8) : Nat :=
  match decodeNextStep? bytes with
  | none => 0
  | some (.scalar _ consumed) => consumed
  | some (.error err) => err.consumed

/-- Return the first UTF-8 decoding error, if any. -/
def firstDecodeError? (bytes : List UInt8) : Option DecodeError :=
  match decodeNextStep? bytes with
  | some (.error err) => some err
  | _ => none

/-- Decode with U+FFFD replacement using Unicode maximal subparts.

This follows the Unicode Standard Chapter 3 replacement guidance instead of the
legacy one-replacement-per-invalid-byte policy. -/
def decodeReplacingMaximalSubparts : Nat → List UInt8 → List Scalar
  | 0, [] => []
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, bytes =>
    match decodeNextStep? bytes with
    | none => []
    | some (.scalar scalar consumed) =>
      scalar :: decodeReplacingMaximalSubparts fuel (bytes.drop consumed)
    | some (.error err) =>
      Scalar.replacement :: decodeReplacingMaximalSubparts fuel (bytes.drop err.consumed)

/-- Decode a byte list with Unicode maximal-subpart replacement semantics. -/
def decodeAllReplacingMaximalSubparts (bytes : List UInt8) : List Scalar :=
  decodeReplacingMaximalSubparts bytes.length bytes

-- ════════════════════════════════════════════════════════════════════
-- Validation Helpers
-- ════════════════════════════════════════════════════════════════════

/-- Whether all bytes in a list are ASCII (< 0x80). -/
def allAscii (bytes : List UInt8) : Bool :=
  bytes.all isAsciiByte

/-- Count the number of continuation bytes in a byte list. -/
def countContinuation (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => if isContinuationByte b then acc + 1 else acc) 0

/-- Count the number of lead bytes (including ASCII) in a byte list.
    For well-formed UTF-8 this equals the number of scalar values. -/
def countLeadBytes (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc b => if isLeadByte b then acc + 1 else acc) 0

/-- Total byte length needed to encode a list of scalars. -/
def encodedByteLength (scalars : List Scalar) : Nat :=
  scalars.foldl (fun acc s => acc + Scalar.byteCount s) 0

/-- Encoded UTF-8 for a valid scalar is never empty. -/
theorem encode_ne_nil (s : Scalar) : encode s ≠ [] := by
  rcases s with ⟨n, hn⟩
  unfold encode
  by_cases h1 : n < 0x80
  · simp [h1]
  · simp [h1]
    by_cases h2 : n < 0x800
    · simp [h2]
    · simp [h2]
      by_cases h3 : n < 0x10000
      · simp [h3]
      · simp [h3]

/-- Encoded length matches the UTF-8 length class. -/
theorem encode_length_eq_byteCount (s : Scalar) :
    (encode s).length = Scalar.byteCount s := by
  rcases s with ⟨n, hn⟩
  unfold encode Scalar.byteCount
  by_cases h1 : n < 0x80
  · simp [h1]
  · simp [h1]
    by_cases h2 : n < 0x800
    · simp [h2]
    · simp [h2]
      by_cases h3 : n < 0x10000
      · simp [h3]
      · simp [h3]

/-- Any UTF-8 encoding produced by `encode` is well-formed. -/
theorem wellFormed_encode (s : Scalar) : WellFormed (encode s) := by
  exact ⟨[s], by simp [encodeAll]⟩

-- ════════════════════════════════════════════════════════════════════
-- Additional Specification Theorems
-- ════════════════════════════════════════════════════════════════════

/-- The byte count is always at least 1. -/
theorem byteCount_pos (s : Scalar) : 1 ≤ Scalar.byteCount s := by
  rcases s with ⟨n, _⟩
  unfold Scalar.byteCount
  by_cases h1 : n < 0x80
  · simp [h1]
  · simp [h1]
    by_cases h2 : n < 0x800
    · simp [h2]
    · simp [h2]
      by_cases h3 : n < 0x10000
      · simp [h3]
      · simp [h3]

/-- The byte count is always at most 4. -/
theorem byteCount_le_four (s : Scalar) : Scalar.byteCount s ≤ 4 := by
  rcases s with ⟨n, _⟩
  unfold Scalar.byteCount
  by_cases h1 : n < 0x80
  · simp [h1]
  · simp [h1]
    by_cases h2 : n < 0x800
    · simp [h2]
    · simp [h2]
      by_cases h3 : n < 0x10000
      · simp [h3]
      · simp [h3]

/-- ASCII scalars always encode to exactly 1 byte. -/
theorem byteCount_ascii (s : Scalar) (h : s.val < 0x80) :
    Scalar.byteCount s = 1 := by
  unfold Scalar.byteCount; simp [h]

/-- Two-byte scalars encode to exactly 2 bytes. -/
theorem byteCount_two (s : Scalar) (h1 : 0x80 ≤ s.val) (h2 : s.val < 0x800) :
    Scalar.byteCount s = 2 := by
  have : ¬ s.val < 0x80 := by omega
  unfold Scalar.byteCount; simp [this, h2]

/-- Three-byte scalars encode to exactly 3 bytes. -/
theorem byteCount_three (s : Scalar) (h1 : 0x800 ≤ s.val) (h2 : s.val < 0x10000) :
    Scalar.byteCount s = 3 := by
  have : ¬ s.val < 0x80 := by omega
  have : ¬ s.val < 0x800 := by omega
  unfold Scalar.byteCount; simp [*]

/-- Supplementary scalars always encode to exactly 4 bytes. -/
theorem byteCount_supplementary (s : Scalar) (h : 0x10000 ≤ s.val) :
    Scalar.byteCount s = 4 := by
  have h1 : ¬ s.val < 0x80 := by omega
  have h2 : ¬ s.val < 0x800 := by omega
  have h3 : ¬ s.val < 0x10000 := by omega
  unfold Scalar.byteCount; simp [h1, h2, h3]

/-- The encode length is at least 1. -/
theorem encode_length_pos (s : Scalar) : 0 < (encode s).length := by
  rw [encode_length_eq_byteCount]
  exact byteCount_pos s

/-- Empty byte list is trivially well-formed. -/
theorem wellFormed_nil : WellFormed [] := ⟨[], rfl⟩

/-- Concatenation of well-formed sequences is well-formed. -/
theorem wellFormed_append (a b : List UInt8) (ha : WellFormed a) (hb : WellFormed b) :
    WellFormed (a ++ b) := by
  rcases ha with ⟨sa, hsa⟩
  rcases hb with ⟨sb, hsb⟩
  refine ⟨sa ++ sb, ?_⟩
  subst hsa; subst hsb
  induction sa with
  | nil => simp [encodeAll]
  | cons s rest ih => simp [encodeAll, List.append_assoc, ih]

/-- encodeAll distributes over list concatenation. -/
theorem encodeAll_append (a b : List Scalar) :
    encodeAll (a ++ b) = encodeAll a ++ encodeAll b := by
  induction a with
  | nil => simp [encodeAll]
  | cons s rest ih => simp [encodeAll, List.append_assoc, ih]

/-- encodeAll of an empty list is empty. -/
theorem encodeAll_nil : encodeAll [] = [] := rfl

/-- encodeAll of a singleton is just encode. -/
theorem encodeAll_singleton (s : Scalar) : encodeAll [s] = encode s := by
  simp [encodeAll]

/-- The total encoding length is at least one byte per scalar. -/
theorem encodeAll_length_ge (scalars : List Scalar) :
    scalars.length ≤ (encodeAll scalars).length := by
  induction scalars with
  | nil => simp [encodeAll]
  | cons s rest ih =>
      have hpos : 1 ≤ (encode s).length := by
        rw [encode_length_eq_byteCount]; exact byteCount_pos s
      simp [encodeAll, List.length_append]
      omega

/-- The total encoding length is at most 4 bytes per scalar. -/
theorem encodeAll_length_le (scalars : List Scalar) :
    (encodeAll scalars).length ≤ 4 * scalars.length := by
  induction scalars with
  | nil => simp [encodeAll]
  | cons s rest ih =>
      have hle : (encode s).length ≤ 4 := by
        rw [encode_length_eq_byteCount]; exact byteCount_le_four s
      simp [encodeAll, List.length_append]
      omega

/-- All-ASCII encoding preserves the byte count exactly. -/
theorem encodeAll_ascii_length (scalars : List Scalar)
    (h : ∀ s ∈ scalars, s.val < 0x80) :
    (encodeAll scalars).length = scalars.length := by
  induction scalars with
  | nil => simp [encodeAll]
  | cons s rest ih =>
    simp [encodeAll, List.length_append]
    have hs := h s (by simp)
    have hLen : (encode s).length = 1 := by
      rw [encode_length_eq_byteCount, byteCount_ascii s hs]
    rw [hLen]
    have := ih (fun x hx => h x (by simp [hx]))
    omega

/-- BOM is exactly 3 bytes. -/
theorem bom_length : bom.length = 3 := rfl

/-- BOM is well-formed UTF-8 (it encodes U+FEFF). -/
theorem wellFormed_bom : WellFormed bom := by
  refine ⟨[⟨0xFEFF, ?_⟩], ?_⟩
  · constructor <;> omega
  · decide

/-- Stripping a BOM from a BOM-prefixed list removes exactly 3 bytes. -/
theorem stripBOM_bom_prefix (rest : List UInt8) :
    stripBOM (bom ++ rest) = rest := by
  simp [stripBOM, hasBOM, bom]

/-- Surrogates are never valid scalars. -/
theorem not_isScalar_surrogate (n : Nat) (h : IsSurrogate n) : ¬ IsScalar n := by
  intro ⟨_, hns⟩
  exact hns h

/-- High surrogates are surrogates. -/
theorem isHighSurrogate_isSurrogate (n : Nat) (h : IsHighSurrogate n) : IsSurrogate n := by
  exact ⟨h.1, by have := h.2; omega⟩

/-- Low surrogates are surrogates. -/
theorem isLowSurrogate_isSurrogate (n : Nat) (h : IsLowSurrogate n) : IsSurrogate n := by
  exact ⟨by have := h.1; omega, h.2⟩

/-- ASCII values are always valid scalars. -/
theorem isScalar_of_isAscii (n : Nat) (h : IsAscii n) : IsScalar n := by
  unfold IsAscii at h
  exact ⟨by omega, fun ⟨hl, _⟩ => by omega⟩

/-- The null scalar is ASCII. -/
theorem null_isAscii : Scalar.null.val < 0x80 := by decide

/-- The replacement character is in the BMP. -/
theorem replacement_isBMP : Scalar.replacement.val < 0x10000 := by decide

/-- sequenceLength returns 0 for continuation bytes. -/
theorem sequenceLength_continuation (b : UInt8) (h : isContinuationByte b = true) :
    sequenceLength b = 0 := by
  unfold isContinuationByte at h
  simp at h
  have hClassify : classifyByte b = .continuation := by
    unfold classifyByte
    have := h.1; have := h.2
    simp_all
  simp [sequenceLength, hClassify]

/-- allAscii of an empty list is true. -/
theorem allAscii_nil : allAscii [] = true := by rfl

/-- Overlong 2-byte sequences are rejected (C0, C1 lead bytes). -/
theorem overlong_two_byte_rejected (b0 : UInt8) (h : b0.toNat < 0xC2) (h2 : 0xC0 ≤ b0.toNat)
    (rest : List UInt8) :
    decodeNext? (b0 :: rest) = none := by
  unfold decodeNext?
  have hAscii : ¬ b0.toNat < 0x80 := by omega
  have hh2 : ¬ (0xC2 ≤ b0.toNat ∧ b0.toNat < 0xE0) := by omega
  have hh3 : ¬ (0xE0 ≤ b0.toNat ∧ b0.toNat < 0xF0) := by omega
  have hh4 : ¬ (0xF0 ≤ b0.toNat ∧ b0.toNat < 0xF5) := by omega
  simp [hAscii, hh2, hh3, hh4]

/-- Bytes ≥ 0xF5 are rejected as lead bytes. -/
theorem high_lead_byte_rejected (b0 : UInt8) (h : 0xF5 ≤ b0.toNat)
    (rest : List UInt8) :
    decodeNext? (b0 :: rest) = none := by
  unfold decodeNext?
  have hAscii : ¬ b0.toNat < 0x80 := by omega
  have hh2 : ¬ (0xC2 ≤ b0.toNat ∧ b0.toNat < 0xE0) := by omega
  have hh3 : ¬ (0xE0 ≤ b0.toNat ∧ b0.toNat < 0xF0) := by omega
  have hh4 : ¬ (0xF0 ≤ b0.toNat ∧ b0.toNat < 0xF5) := by omega
  simp [hAscii, hh2, hh3, hh4]

/-! ## Unicode Category Classification -/

/-- Unicode general category (simplified). Only the categories needed for
    binary-level UTF-8 processing. -/
inductive GeneralCategory where
  | letter
  | mark
  | number
  | punctuation
  | symbol
  | separator
  | other
  deriving DecidableEq, Repr

/-- Classify a scalar into a general category based on code point range.
    This is a rough approximation — full UCD data is not included. -/
def classifyCategory (s : Scalar) : GeneralCategory :=
  let v := s.val
  if v < 0x20 then .other          -- C0 controls
  else if v < 0x7F then
    if v ≥ 0x41 && v ≤ 0x5A then .letter      -- A-Z
    else if v ≥ 0x61 && v ≤ 0x7A then .letter  -- a-z
    else if v ≥ 0x30 && v ≤ 0x39 then .number  -- 0-9
    else if v == 0x20 then .separator
    else .punctuation
  else if v < 0xA0 then .other     -- C1 controls + DEL
  else if v < 0x0300 then .letter  -- Latin Extended etc.
  else if v < 0x0370 then .mark    -- Combining diacriticals
  else .letter                     -- Simplified: treat rest as letter

/-! ## UTF-8 Validation State Machine

A DFA-based approach to validating UTF-8 byte streams.
States track which bytes are expected in a multi-byte sequence. -/

/-- State of the UTF-8 validation DFA. -/
inductive ValidationState where
  /-- Expecting a new code point (lead byte or ASCII). -/
  | accept
  /-- Expecting 1 more continuation byte. -/
  | need1
  /-- Expecting 2 more continuation bytes, with range check on first. -/
  | need2 (lo hi : UInt8)
  /-- Expecting 3 more continuation bytes, with range check on first. -/
  | need3 (lo hi : UInt8)
  /-- Expecting 2 more continuation bytes (no special range check). -/
  | tail2
  /-- Expecting 1 more continuation byte after need2. -/
  | tail1
  /-- Invalid byte encountered. Terminal error state. -/
  | reject
  deriving Repr

/-- Advance the validation DFA by one byte. -/
def validationStep : ValidationState → UInt8 → ValidationState
  | .accept, b =>
    let v := b.toNat
    if v < 0x80 then .accept
    else if v < 0xC2 then .reject            -- continuation or overlong
    else if v < 0xE0 then .need1             -- 2-byte
    else if v == 0xE0 then .need2 0xA0 0xBF  -- 3-byte, min continuation
    else if v == 0xED then .need2 0x80 0x9F  -- 3-byte, avoid surrogates
    else if v < 0xF0 then .need2 0x80 0xBF   -- 3-byte, normal
    else if v == 0xF0 then .need3 0x90 0xBF  -- 4-byte, min continuation
    else if v == 0xF4 then .need3 0x80 0x8F  -- 4-byte, max U+10FFFF
    else if v < 0xF5 then .need3 0x80 0xBF   -- 4-byte, normal
    else .reject                              -- ≥ 0xF5
  | .need1, b =>
    if 0x80 ≤ b.toNat && b.toNat ≤ 0xBF then .accept else .reject
  | .need2 lo hi, b =>
    if lo.toNat ≤ b.toNat && b.toNat ≤ hi.toNat then .tail1 else .reject
  | .need3 lo hi, b =>
    if lo.toNat ≤ b.toNat && b.toNat ≤ hi.toNat then .tail2 else .reject
  | .tail2, b =>
    if 0x80 ≤ b.toNat && b.toNat ≤ 0xBF then .tail1 else .reject
  | .tail1, b =>
    if 0x80 ≤ b.toNat && b.toNat ≤ 0xBF then .accept else .reject
  | .reject, _ => .reject

/-- Validate a byte list using the DFA. -/
def validateUTF8 (bytes : List UInt8) : Bool :=
  let finalState := bytes.foldl validationStep .accept
  match finalState with
  | .accept => true
  | _ => false

/-- The empty byte sequence is valid UTF-8. -/
theorem validateUTF8_nil : validateUTF8 [] = true := rfl

/-- Any ASCII byte alone is valid UTF-8. -/
theorem validateUTF8_ascii (b : UInt8) (h : b.toNat < 0x80) :
    validateUTF8 [b] = true := by
  simp [validateUTF8, List.foldl, validationStep, h]

/-! ## Code Point Range Invariants -/

/-- Maximum Unicode code point value. -/
def maxCodePoint : Nat := 0x10FFFF

/-- The number of Unicode planes. -/
def numPlanes : Nat := 17

/-- Maximum scalar value equals maxCodePoint. -/
theorem maxScalar_val : Scalar.maxScalar.val = maxCodePoint := by decide

/-- Every scalar value is ≤ maxCodePoint. -/
theorem scalar_le_maxCodePoint (s : Scalar) : s.val ≤ maxCodePoint := by
  have ⟨h1, _⟩ := s.property
  unfold maxCodePoint; omega

/-- Every scalar's plane is < numPlanes. -/
theorem scalar_plane_lt (s : Scalar) : Scalar.plane s < numPlanes := by
  unfold Scalar.plane numPlanes
  have hval := scalar_le_maxCodePoint s
  unfold maxCodePoint at hval
  exact Nat.div_lt_of_lt_mul (by omega)

-- ════════════════════════════════════════════════════════════════════
-- Code Point Properties
-- ════════════════════════════════════════════════════════════════════

/-- Whether a code point is a C0 or C1 control character. -/
def IsControl (n : Nat) : Prop := n ≤ 0x1F ∨ (0x7F ≤ n ∧ n ≤ 0x9F)

instance (n : Nat) : Decidable (IsControl n) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Whether a code point is whitespace per Unicode White_Space property. -/
def IsWhitespace (n : Nat) : Prop :=
  n == 0x20 ∨ n == 0x09 ∨ n == 0x0A ∨ n == 0x0B ∨ n == 0x0C ∨ n == 0x0D ∨
  n == 0x85 ∨ n == 0xA0 ∨ n == 0x1680 ∨
  (0x2000 ≤ n ∧ n ≤ 0x200A) ∨
  n == 0x2028 ∨ n == 0x2029 ∨ n == 0x202F ∨ n == 0x205F ∨ n == 0x3000

instance (n : Nat) : Decidable (IsWhitespace n) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Whether a code point is an ASCII digit 0-9. -/
def IsDigit (n : Nat) : Prop := 0x30 ≤ n ∧ n ≤ 0x39

instance (n : Nat) : Decidable (IsDigit n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether a code point is an ASCII uppercase letter. -/
def IsUppercase (n : Nat) : Prop := 0x41 ≤ n ∧ n ≤ 0x5A

instance (n : Nat) : Decidable (IsUppercase n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether a code point is an ASCII lowercase letter. -/
def IsLowercase (n : Nat) : Prop := 0x61 ≤ n ∧ n ≤ 0x7A

instance (n : Nat) : Decidable (IsLowercase n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether a code point is an ASCII letter (uppercase or lowercase). -/
def IsAlpha (n : Nat) : Prop := IsUppercase n ∨ IsLowercase n

instance (n : Nat) : Decidable (IsAlpha n) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Whether a code point is an ASCII alphanumeric character. -/
def IsAlphanumeric (n : Nat) : Prop := IsAlpha n ∨ IsDigit n

instance (n : Nat) : Decidable (IsAlphanumeric n) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Whether a code point is a printable ASCII character (0x20..0x7E). -/
def IsPrintable (n : Nat) : Prop := 0x20 ≤ n ∧ n ≤ 0x7E

instance (n : Nat) : Decidable (IsPrintable n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether a code point is a C0 control (0x00..0x1F). -/
def IsC0Control (n : Nat) : Prop := n ≤ 0x1F

instance (n : Nat) : Decidable (IsC0Control n) :=
  inferInstanceAs (Decidable (n ≤ 0x1F))

/-- Whether a code point is a C1 control (0x80..0x9F). -/
def IsC1Control (n : Nat) : Prop := 0x80 ≤ n ∧ n ≤ 0x9F

instance (n : Nat) : Decidable (IsC1Control n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Supported simple uppercase-to-lowercase mapping over ASCII and selected Latin precomposed scalars. -/
def simpleLowerNat? (n : Nat) : Option Nat :=
  match n with
  | 0x41 => some 0x61
  | 0x42 => some 0x62
  | 0x43 => some 0x63
  | 0x44 => some 0x64
  | 0x45 => some 0x65
  | 0x46 => some 0x66
  | 0x47 => some 0x67
  | 0x48 => some 0x68
  | 0x49 => some 0x69
  | 0x4A => some 0x6A
  | 0x4B => some 0x6B
  | 0x4C => some 0x6C
  | 0x4D => some 0x6D
  | 0x4E => some 0x6E
  | 0x4F => some 0x6F
  | 0x50 => some 0x70
  | 0x51 => some 0x71
  | 0x52 => some 0x72
  | 0x53 => some 0x73
  | 0x54 => some 0x74
  | 0x55 => some 0x75
  | 0x56 => some 0x76
  | 0x57 => some 0x77
  | 0x58 => some 0x78
  | 0x59 => some 0x79
  | 0x5A => some 0x7A
  | 0x00C0 => some 0x00E0
  | 0x00C1 => some 0x00E1
  | 0x00C2 => some 0x00E2
  | 0x00C3 => some 0x00E3
  | 0x00C4 => some 0x00E4
  | 0x00C5 => some 0x00E5
  | 0x00C7 => some 0x00E7
  | 0x00C8 => some 0x00E8
  | 0x00C9 => some 0x00E9
  | 0x00CA => some 0x00EA
  | 0x00CB => some 0x00EB
  | 0x00CC => some 0x00EC
  | 0x00CD => some 0x00ED
  | 0x00CE => some 0x00EE
  | 0x00CF => some 0x00EF
  | 0x00D1 => some 0x00F1
  | 0x00D2 => some 0x00F2
  | 0x00D3 => some 0x00F3
  | 0x00D4 => some 0x00F4
  | 0x00D5 => some 0x00F5
  | 0x00D6 => some 0x00F6
  | 0x00D9 => some 0x00F9
  | 0x00DA => some 0x00FA
  | 0x00DB => some 0x00FB
  | 0x00DC => some 0x00FC
  | 0x00DD => some 0x00FD
  | 0x0178 => some 0x00FF
  | _ => none

/-- Supported simple lowercase-to-uppercase mapping over ASCII and selected Latin precomposed scalars. -/
def simpleUpperNat? (n : Nat) : Option Nat :=
  match n with
  | 0x61 => some 0x41
  | 0x62 => some 0x42
  | 0x63 => some 0x43
  | 0x64 => some 0x44
  | 0x65 => some 0x45
  | 0x66 => some 0x46
  | 0x67 => some 0x47
  | 0x68 => some 0x48
  | 0x69 => some 0x49
  | 0x6A => some 0x4A
  | 0x6B => some 0x4B
  | 0x6C => some 0x4C
  | 0x6D => some 0x4D
  | 0x6E => some 0x4E
  | 0x6F => some 0x4F
  | 0x70 => some 0x50
  | 0x71 => some 0x51
  | 0x72 => some 0x52
  | 0x73 => some 0x53
  | 0x74 => some 0x54
  | 0x75 => some 0x55
  | 0x76 => some 0x56
  | 0x77 => some 0x57
  | 0x78 => some 0x58
  | 0x79 => some 0x59
  | 0x7A => some 0x5A
  | 0x00E0 => some 0x00C0
  | 0x00E1 => some 0x00C1
  | 0x00E2 => some 0x00C2
  | 0x00E3 => some 0x00C3
  | 0x00E4 => some 0x00C4
  | 0x00E5 => some 0x00C5
  | 0x00E7 => some 0x00C7
  | 0x00E8 => some 0x00C8
  | 0x00E9 => some 0x00C9
  | 0x00EA => some 0x00CA
  | 0x00EB => some 0x00CB
  | 0x00EC => some 0x00CC
  | 0x00ED => some 0x00CD
  | 0x00EE => some 0x00CE
  | 0x00EF => some 0x00CF
  | 0x00F1 => some 0x00D1
  | 0x00F2 => some 0x00D2
  | 0x00F3 => some 0x00D3
  | 0x00F4 => some 0x00D4
  | 0x00F5 => some 0x00D5
  | 0x00F6 => some 0x00D6
  | 0x00F9 => some 0x00D9
  | 0x00FA => some 0x00DA
  | 0x00FB => some 0x00DB
  | 0x00FC => some 0x00DC
  | 0x00FD => some 0x00DD
  | 0x00FF => some 0x0178
  | _ => none

namespace Scalar

/-- Whether the scalar is a control character. -/
def isControl (s : Scalar) : Bool := decide (IsControl s.val)

/-- Whether the scalar is whitespace. -/
def isWhitespace (s : Scalar) : Bool := decide (IsWhitespace s.val)

/-- Whether the scalar is an ASCII digit. -/
def isDigit (s : Scalar) : Bool := decide (IsDigit s.val)

/-- Whether the scalar is an ASCII letter. -/
def isAlpha (s : Scalar) : Bool := decide (IsAlpha s.val)

/-- Whether the scalar is printable. -/
def isPrintable (s : Scalar) : Bool := decide (IsPrintable s.val)

/-- Whether the scalar is an ASCII uppercase letter. -/
def isUppercase (s : Scalar) : Bool := decide (IsUppercase s.val)

/-- Whether the scalar is an ASCII lowercase letter. -/
def isLowercase (s : Scalar) : Bool := decide (IsLowercase s.val)

/-- Simple ASCII uppercase → lowercase mapping. Returns None for non-uppercase. -/
def toLowerAscii? (s : Scalar) : Option Scalar :=
  if h : IsUppercase s.val then
    some ⟨s.val + 0x20, by
      unfold IsUppercase at h
      constructor
      · omega
      · intro ⟨hl, hr⟩; omega⟩
  else none

/-- Simple ASCII lowercase → uppercase mapping. Returns None for non-lowercase. -/
def toUpperAscii? (s : Scalar) : Option Scalar :=
  if h : IsLowercase s.val then
    some ⟨s.val - 0x20, by
      unfold IsLowercase at h
      constructor
      · omega
      · intro ⟨hl, hr⟩; omega⟩
  else none

/-- Supported simple uppercase → lowercase mapping. Returns the original scalar when no mapping is defined. -/
def toLowerSimple (s : Scalar) : Scalar :=
  match simpleLowerNat? s.val with
  | some lower =>
    match ofNat? lower with
    | some lowered => lowered
    | none => s
  | none => s

/-- Supported simple lowercase → uppercase mapping. Returns the original scalar when no mapping is defined. -/
def toUpperSimple (s : Scalar) : Scalar :=
  match simpleUpperNat? s.val with
  | some upper =>
    match ofNat? upper with
    | some uppered => uppered
    | none => s
  | none => s

/-- Supported simple case folding. This currently follows the lowercase mapping subset. -/
def caseFoldSimple (s : Scalar) : Scalar :=
  toLowerSimple s

/-- Successor scalar (next valid scalar, skipping surrogates). -/
def succ? (s : Scalar) : Option Scalar :=
  let next := s.val + 1
  if next == 0xD800 then
    some ⟨0xE000, by constructor <;> omega⟩
  else if h : IsScalar next then
    some ⟨next, h⟩
  else none

/-- Predecessor scalar (previous valid scalar, skipping surrogates). -/
def pred? (s : Scalar) : Option Scalar :=
  if s.val == 0 then none
  else if s.val == 0xE000 then
    some ⟨0xD7FF, by constructor <;> omega⟩
  else
    let prev := s.val - 1
    if h : IsScalar prev then some ⟨prev, h⟩ else none

/-- Distance between two scalars (counting only valid scalars). -/
def distance (s1 s2 : Scalar) : Nat :=
  let a := min s1.val s2.val
  let b := max s1.val s2.val
  -- Subtract surrogate gap if the range spans it
  let rawDist := b - a
  if a < 0xD800 && b > 0xDFFF then rawDist - 0x800
  else rawDist

end Scalar

-- ════════════════════════════════════════════════════════════════════
-- UTF-16 Surrogate Pair Conversion
-- ════════════════════════════════════════════════════════════════════

/-- Encode a supplementary scalar as a UTF-16 surrogate pair.
    Returns (high_surrogate, low_surrogate) as raw Nat values. -/
def toSurrogatePair (s : Scalar) (_h : 0x10000 ≤ s.val) : Nat × Nat :=
  let u := s.val - 0x10000
  let hi := 0xD800 + u / 0x400
  let lo := 0xDC00 + u % 0x400
  (hi, lo)

/-- Decode a UTF-16 surrogate pair back to a scalar. -/
def fromSurrogatePair? (hi lo : Nat) : Option Scalar :=
  if 0xD800 ≤ hi && hi ≤ 0xDBFF && 0xDC00 ≤ lo && lo ≤ 0xDFFF then
    let code := 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)
    if h : IsScalar code then some ⟨code, h⟩ else none
  else none

-- ════════════════════════════════════════════════════════════════════
-- Normalization Forms (Canonical Decomposition Framework)
-- ════════════════════════════════════════════════════════════════════

/-- Unicode Canonical Combining Class (CCC). Value 0 means Starter. -/
abbrev CombiningClass := Nat

/-- A decomposition mapping for a single code point. -/
structure DecompositionEntry where
  source : Nat
  target : List Nat
  deriving DecidableEq, Repr

/-- Normalization form tag. -/
inductive NormalizationForm where
  | nfd   -- Canonical Decomposition
  | nfc   -- Canonical Decomposition + Canonical Composition
  | nfkd  -- Compatibility Decomposition
  | nfkc  -- Compatibility Decomposition + Canonical Composition
  deriving DecidableEq, Repr

/-- Whether a scalar is a "Starter" (CCC = 0). Most characters are starters. -/
def isStarter (ccc : CombiningClass) : Bool := ccc == 0

/-- Whether a scalar is a combining mark (CCC > 0). -/
def isCombining (ccc : CombiningClass) : Bool := ccc > 0

/-- Canonical combining class for the supported normalization subset. -/
def canonicalCombiningClass (s : Scalar) : CombiningClass :=
  match s.val with
  | 0x0327 => 202 -- COMBINING CEDILLA
  | 0x0300 => 230 -- COMBINING GRAVE ACCENT
  | 0x0301 => 230 -- COMBINING ACUTE ACCENT
  | 0x0302 => 230 -- COMBINING CIRCUMFLEX ACCENT
  | 0x0303 => 230 -- COMBINING TILDE
  | 0x0304 => 230 -- COMBINING MACRON
  | 0x0308 => 230 -- COMBINING DIAERESIS
  | 0x030A => 230 -- COMBINING RING ABOVE
  | _ => 0

/-- Insert a combining-mark entry into a stable ascending CCC order. -/
private def insertByCombiningClass (entry : Scalar × CombiningClass) :
    List (Scalar × CombiningClass) → List (Scalar × CombiningClass)
  | [] => [entry]
  | head :: tail =>
    if entry.2 < head.2 then
      entry :: head :: tail
    else
      head :: insertByCombiningClass entry tail

/-- Flush one canonical-order segment into the accumulated output. -/
private def flushCanonicalSegment
    (starter? : Option (Scalar × CombiningClass))
    (marks : List (Scalar × CombiningClass)) : List (Scalar × CombiningClass) :=
  match starter? with
  | some starter => starter :: marks
  | none => marks

/-- Canonical ordering: reorder combining marks by their CCC values.
    This is a specification-level sort by CCC for the Canonical Ordering Algorithm. -/
def canonicalOrder (chars : List (Scalar × CombiningClass)) : List (Scalar × CombiningClass) :=
  go chars none []
where
  go (remaining : List (Scalar × CombiningClass))
      (starter? : Option (Scalar × CombiningClass))
      (marks : List (Scalar × CombiningClass)) : List (Scalar × CombiningClass) :=
    match remaining with
    | [] => flushCanonicalSegment starter? marks
    | char :: rest =>
      if isStarter char.2 then
        flushCanonicalSegment starter? marks ++ go rest (some char) []
      else
        go rest starter? (insertByCombiningClass char marks)

/-- Whether a normalization form is currently implemented by the executable model. -/
def supportsNormalizationForm (form : NormalizationForm) : Bool :=
  match form with
  | .nfd | .nfc | .nfkd | .nfkc => true

/-- Convert a Nat list to scalars, failing if any element is not a valid scalar. -/
private def scalarListFromNats? (ns : List Nat) : Option (List Scalar) :=
  ns.mapM Scalar.ofNat?

/-- Canonical decomposition mappings for the supported precomposed subset. -/
private def canonicalDecompositionNats? (n : Nat) : Option (List Nat) :=
  match n with
  | 0x00C0 => some [0x0041, 0x0300]
  | 0x00C1 => some [0x0041, 0x0301]
  | 0x00C2 => some [0x0041, 0x0302]
  | 0x00C3 => some [0x0041, 0x0303]
  | 0x00C4 => some [0x0041, 0x0308]
  | 0x00C5 => some [0x0041, 0x030A]
  | 0x00C7 => some [0x0043, 0x0327]
  | 0x00C8 => some [0x0045, 0x0300]
  | 0x00C9 => some [0x0045, 0x0301]
  | 0x00CA => some [0x0045, 0x0302]
  | 0x00CB => some [0x0045, 0x0308]
  | 0x00CC => some [0x0049, 0x0300]
  | 0x00CD => some [0x0049, 0x0301]
  | 0x00CE => some [0x0049, 0x0302]
  | 0x00CF => some [0x0049, 0x0308]
  | 0x00D1 => some [0x004E, 0x0303]
  | 0x00D2 => some [0x004F, 0x0300]
  | 0x00D3 => some [0x004F, 0x0301]
  | 0x00D4 => some [0x004F, 0x0302]
  | 0x00D5 => some [0x004F, 0x0303]
  | 0x00D6 => some [0x004F, 0x0308]
  | 0x00D9 => some [0x0055, 0x0300]
  | 0x00DA => some [0x0055, 0x0301]
  | 0x00DB => some [0x0055, 0x0302]
  | 0x00DC => some [0x0055, 0x0308]
  | 0x00DD => some [0x0059, 0x0301]
  | 0x00E0 => some [0x0061, 0x0300]
  | 0x00E1 => some [0x0061, 0x0301]
  | 0x00E2 => some [0x0061, 0x0302]
  | 0x00E3 => some [0x0061, 0x0303]
  | 0x00E4 => some [0x0061, 0x0308]
  | 0x00E5 => some [0x0061, 0x030A]
  | 0x00E7 => some [0x0063, 0x0327]
  | 0x00E8 => some [0x0065, 0x0300]
  | 0x00E9 => some [0x0065, 0x0301]
  | 0x00EA => some [0x0065, 0x0302]
  | 0x00EB => some [0x0065, 0x0308]
  | 0x00EC => some [0x0069, 0x0300]
  | 0x00ED => some [0x0069, 0x0301]
  | 0x00EE => some [0x0069, 0x0302]
  | 0x00EF => some [0x0069, 0x0308]
  | 0x00F1 => some [0x006E, 0x0303]
  | 0x00F2 => some [0x006F, 0x0300]
  | 0x00F3 => some [0x006F, 0x0301]
  | 0x00F4 => some [0x006F, 0x0302]
  | 0x00F5 => some [0x006F, 0x0303]
  | 0x00F6 => some [0x006F, 0x0308]
  | 0x00F9 => some [0x0075, 0x0300]
  | 0x00FA => some [0x0075, 0x0301]
  | 0x00FB => some [0x0075, 0x0302]
  | 0x00FC => some [0x0075, 0x0308]
  | 0x00FD => some [0x0079, 0x0301]
  | 0x00FF => some [0x0079, 0x0308]
  | 0x0178 => some [0x0059, 0x0308]
  | _ => none

/-- Compatibility decomposition mappings for the supported practical subset. -/
private def compatibilityDecompositionNats? (n : Nat) : Option (List Nat) :=
  if n == 0x3000 then
    some [0x0020]
  else if 0xFF01 ≤ n && n ≤ 0xFF5E then
    some [n - 0xFEE0]
  else
    match n with
    | 0x00A0 => some [0x0020]
    | 0x00A8 => some [0x0020, 0x0308]
    | 0x00AA => some [0x0061]
    | 0x00AF => some [0x0020, 0x0304]
    | 0x00B2 => some [0x0032]
    | 0x00B3 => some [0x0033]
    | 0x00B4 => some [0x0020, 0x0301]
    | 0x00B5 => some [0x03BC]
    | 0x00B8 => some [0x0020, 0x0327]
    | 0x00B9 => some [0x0031]
    | 0x00BA => some [0x006F]
    | 0x00BC => some [0x0031, 0x2044, 0x0034]
    | 0x00BD => some [0x0031, 0x2044, 0x0032]
    | 0x00BE => some [0x0033, 0x2044, 0x0034]
    | 0x2126 => some [0x03A9]
    | 0x212A => some [0x004B]
    | 0x212B => some [0x00C5]
    | 0xFB00 => some [0x0066, 0x0066]
    | 0xFB01 => some [0x0066, 0x0069]
    | 0xFB02 => some [0x0066, 0x006C]
    | 0xFB03 => some [0x0066, 0x0066, 0x0069]
    | 0xFB04 => some [0x0066, 0x0066, 0x006C]
    | 0xFB05 => some [0x0073, 0x0074]
    | 0xFB06 => some [0x0073, 0x0074]
    | _ => none

/-- Canonical composition mappings for the supported precomposed subset. -/
private def canonicalCompositionNat? (starter mark : Nat) : Option Nat :=
  match starter, mark with
  | 0x0041, 0x0300 => some 0x00C0
  | 0x0041, 0x0301 => some 0x00C1
  | 0x0041, 0x0302 => some 0x00C2
  | 0x0041, 0x0303 => some 0x00C3
  | 0x0041, 0x0308 => some 0x00C4
  | 0x0041, 0x030A => some 0x00C5
  | 0x0043, 0x0327 => some 0x00C7
  | 0x0045, 0x0300 => some 0x00C8
  | 0x0045, 0x0301 => some 0x00C9
  | 0x0045, 0x0302 => some 0x00CA
  | 0x0045, 0x0308 => some 0x00CB
  | 0x0049, 0x0300 => some 0x00CC
  | 0x0049, 0x0301 => some 0x00CD
  | 0x0049, 0x0302 => some 0x00CE
  | 0x0049, 0x0308 => some 0x00CF
  | 0x004E, 0x0303 => some 0x00D1
  | 0x004F, 0x0300 => some 0x00D2
  | 0x004F, 0x0301 => some 0x00D3
  | 0x004F, 0x0302 => some 0x00D4
  | 0x004F, 0x0303 => some 0x00D5
  | 0x004F, 0x0308 => some 0x00D6
  | 0x0055, 0x0300 => some 0x00D9
  | 0x0055, 0x0301 => some 0x00DA
  | 0x0055, 0x0302 => some 0x00DB
  | 0x0055, 0x0308 => some 0x00DC
  | 0x0059, 0x0301 => some 0x00DD
  | 0x0059, 0x0308 => some 0x0178
  | 0x0061, 0x0300 => some 0x00E0
  | 0x0061, 0x0301 => some 0x00E1
  | 0x0061, 0x0302 => some 0x00E2
  | 0x0061, 0x0303 => some 0x00E3
  | 0x0061, 0x0308 => some 0x00E4
  | 0x0061, 0x030A => some 0x00E5
  | 0x0063, 0x0327 => some 0x00E7
  | 0x0065, 0x0300 => some 0x00E8
  | 0x0065, 0x0301 => some 0x00E9
  | 0x0065, 0x0302 => some 0x00EA
  | 0x0065, 0x0308 => some 0x00EB
  | 0x0069, 0x0300 => some 0x00EC
  | 0x0069, 0x0301 => some 0x00ED
  | 0x0069, 0x0302 => some 0x00EE
  | 0x0069, 0x0308 => some 0x00EF
  | 0x006E, 0x0303 => some 0x00F1
  | 0x006F, 0x0300 => some 0x00F2
  | 0x006F, 0x0301 => some 0x00F3
  | 0x006F, 0x0302 => some 0x00F4
  | 0x006F, 0x0303 => some 0x00F5
  | 0x006F, 0x0308 => some 0x00F6
  | 0x0075, 0x0300 => some 0x00F9
  | 0x0075, 0x0301 => some 0x00FA
  | 0x0075, 0x0302 => some 0x00FB
  | 0x0075, 0x0308 => some 0x00FC
  | 0x0079, 0x0301 => some 0x00FD
  | 0x0079, 0x0308 => some 0x00FF
  | _, _ => none

private def hangulSBase : Nat := 0xAC00
private def hangulLBase : Nat := 0x1100
private def hangulVBase : Nat := 0x1161
private def hangulTBase : Nat := 0x11A7
private def hangulLCount : Nat := 19
private def hangulVCount : Nat := 21
private def hangulTCount : Nat := 28
private def hangulNCount : Nat := hangulVCount * hangulTCount
private def hangulSCount : Nat := hangulLCount * hangulNCount

/-- Algorithmic canonical decomposition for Hangul syllables. -/
private def decomposeHangul? (s : Scalar) : Option (List Scalar) :=
  if hangulSBase ≤ s.val && s.val < hangulSBase + hangulSCount then
    let sIndex := s.val - hangulSBase
    let lIndex := sIndex / hangulNCount
    let vIndex := (sIndex % hangulNCount) / hangulTCount
    let tIndex := sIndex % hangulTCount
    match Scalar.ofNat? (hangulLBase + lIndex), Scalar.ofNat? (hangulVBase + vIndex) with
    | some l, some v =>
      if tIndex == 0 then
        some [l, v]
      else
        match Scalar.ofNat? (hangulTBase + tIndex) with
        | some t => some [l, v, t]
        | none => none
    | _, _ => none
  else
    none

/-- One-step canonical decomposition for the supported normalization subset. -/
def canonicalDecomposition? (s : Scalar) : Option (List Scalar) :=
  match decomposeHangul? s with
  | some decomposed => some decomposed
  | none =>
    match canonicalDecompositionNats? s.val with
    | some ns => scalarListFromNats? ns
    | none => none

/-- One-step compatibility decomposition for the supported normalization subset. -/
def compatibilityDecomposition? (s : Scalar) : Option (List Scalar) :=
  match compatibilityDecompositionNats? s.val with
  | some ns => scalarListFromNats? ns
  | none => none

/-- The supported decomposition tables are shallow, so a small total recursion bound is enough. -/
private def normalizationDecompositionFuel : Nat := 4

/-- Recursively decompose one scalar under the selected normalization regime. -/
private def decomposeScalarRecursive (compatibility : Bool) (fuel : Nat) (s : Scalar) : List Scalar :=
  match fuel with
  | 0 => [s]
  | fuel + 1 =>
    let step? :=
      if compatibility then
        match compatibilityDecomposition? s with
        | some decomposed => some decomposed
        | none => canonicalDecomposition? s
      else
        canonicalDecomposition? s
    match step? with
    | some decomposed =>
      decomposed.foldr
        (fun scalar acc => decomposeScalarRecursive compatibility fuel scalar ++ acc)
        []
    | none => [s]

/-- Algorithmic Hangul composition for L+V and LV+T pairs. -/
private def composeHangulPair? (starter mark : Scalar) : Option Scalar :=
  if hangulLBase ≤ starter.val && starter.val < hangulLBase + hangulLCount &&
      hangulVBase ≤ mark.val && mark.val < hangulVBase + hangulVCount then
    let lIndex := starter.val - hangulLBase
    let vIndex := mark.val - hangulVBase
    Scalar.ofNat? (hangulSBase + (lIndex * hangulVCount + vIndex) * hangulTCount)
  else if hangulSBase ≤ starter.val && starter.val < hangulSBase + hangulSCount &&
      (starter.val - hangulSBase) % hangulTCount == 0 &&
      hangulTBase < mark.val && mark.val < hangulTBase + hangulTCount then
    Scalar.ofNat? (starter.val + (mark.val - hangulTBase))
  else
    none

/-- Canonical composition for the supported normalization subset. -/
def canonicalComposePair? (starter mark : Scalar) : Option Scalar :=
  match composeHangulPair? starter mark with
  | some composed => some composed
  | none =>
    match canonicalCompositionNat? starter.val mark.val with
    | some n => Scalar.ofNat? n
    | none => none

/-- Full canonical decomposition without canonical ordering. -/
def canonicalDecomposeScalars (scalars : List Scalar) : List Scalar :=
  scalars.foldr
    (fun scalar acc => decomposeScalarRecursive false normalizationDecompositionFuel scalar ++ acc)
    []

/-- Full compatibility decomposition without canonical ordering. -/
def compatibilityDecomposeScalars (scalars : List Scalar) : List Scalar :=
  scalars.foldr
    (fun scalar acc => decomposeScalarRecursive true normalizationDecompositionFuel scalar ++ acc)
    []

/-- Canonical decomposition followed by canonical ordering (NFD). -/
def normalizeScalarsNFD (scalars : List Scalar) : List Scalar :=
  let decomposed := canonicalDecomposeScalars scalars
  let annotated := decomposed.map (fun scalar => (scalar, canonicalCombiningClass scalar))
  (canonicalOrder annotated).map Prod.fst

/-- Compatibility decomposition followed by canonical ordering (NFKD). -/
def normalizeScalarsNFKD (scalars : List Scalar) : List Scalar :=
  let decomposed := compatibilityDecomposeScalars scalars
  let annotated := decomposed.map (fun scalar => (scalar, canonicalCombiningClass scalar))
  (canonicalOrder annotated).map Prod.fst

/-- Compose one canonically ordered scalar list segment. -/
private def composeCanonicalOrdered (scalars : List Scalar) : List Scalar :=
  go scalars none [] 0
where
  flush (starter? : Option Scalar) (marksRev : List Scalar) : List Scalar :=
    match starter? with
    | some starter => starter :: marksRev.reverse
    | none => marksRev.reverse

  go (remaining : List Scalar) (starter? : Option Scalar) (marksRev : List Scalar)
      (lastCCC : CombiningClass) : List Scalar :=
    match remaining with
    | [] => flush starter? marksRev
    | scalar :: rest =>
      let ccc := canonicalCombiningClass scalar
      if ccc == 0 then
        match starter? with
        | some starter =>
          if marksRev.isEmpty then
            match canonicalComposePair? starter scalar with
            | some composed => go rest (some composed) [] 0
            | none => flush starter? marksRev ++ go rest (some scalar) [] 0
          else
            flush starter? marksRev ++ go rest (some scalar) [] 0
        | none =>
          flush starter? marksRev ++ go rest (some scalar) [] 0
      else
        match starter? with
        | some starter =>
          if lastCCC < ccc then
            match canonicalComposePair? starter scalar with
            | some composed => go rest (some composed) marksRev lastCCC
            | none => go rest starter? (scalar :: marksRev) ccc
          else
            go rest starter? (scalar :: marksRev) ccc
        | none =>
          go rest none (scalar :: marksRev) ccc

/-- Canonical decomposition, canonical ordering, and canonical composition (NFC). -/
def normalizeScalarsNFC (scalars : List Scalar) : List Scalar :=
  composeCanonicalOrdered (normalizeScalarsNFD scalars)

/-- Compatibility decomposition, canonical ordering, and canonical composition (NFKC). -/
def normalizeScalarsNFKC (scalars : List Scalar) : List Scalar :=
  composeCanonicalOrdered (normalizeScalarsNFKD scalars)

/-- Normalize a scalar list when the requested form is currently supported. -/
def normalizeScalars? (form : NormalizationForm) (scalars : List Scalar) : Option (List Scalar) :=
  match form with
  | .nfd => some (normalizeScalarsNFD scalars)
  | .nfc => some (normalizeScalarsNFC scalars)
  | .nfkd => some (normalizeScalarsNFKD scalars)
  | .nfkc => some (normalizeScalarsNFKC scalars)

/-- Whether a scalar list is already in NFD. -/
def isNormalizedNFD (scalars : List Scalar) : Bool :=
  normalizeScalarsNFD scalars == scalars

/-- Whether a scalar list is already in NFC. -/
def isNormalizedNFC (scalars : List Scalar) : Bool :=
  normalizeScalarsNFC scalars == scalars

/-- Whether a scalar list is already in NFKD. -/
def isNormalizedNFKD (scalars : List Scalar) : Bool :=
  normalizeScalarsNFKD scalars == scalars

/-- Whether a scalar list is already in NFKC. -/
def isNormalizedNFKC (scalars : List Scalar) : Bool :=
  normalizeScalarsNFKC scalars == scalars

/-- Whether two scalar lists are canonically equivalent under NFD. -/
def canonicallyEquivalent (left right : List Scalar) : Bool :=
  normalizeScalarsNFD left == normalizeScalarsNFD right

/-- Apply supported simple lowercase mapping to a scalar list. -/
def lowercaseScalarsSimple (scalars : List Scalar) : List Scalar :=
  scalars.map Scalar.toLowerSimple

/-- Apply supported simple uppercase mapping to a scalar list. -/
def uppercaseScalarsSimple (scalars : List Scalar) : List Scalar :=
  scalars.map Scalar.toUpperSimple

/-- Apply supported simple case folding and canonical decomposition to a scalar list. -/
def caseFoldScalarsSimple (scalars : List Scalar) : List Scalar :=
  normalizeScalarsNFD (scalars.map Scalar.caseFoldSimple)

/-- Whether two scalar lists are equal under the supported simple case-folding subset. -/
def caselessEquivalentSimple (left right : List Scalar) : Bool :=
  caseFoldScalarsSimple left == caseFoldScalarsSimple right

/-- Extended case-fold mappings for a practical Unicode subset, including
    multi-scalar folds and Greek sigma normalization. -/
private def extendedCaseFoldNats? (n : Nat) : Option (List Nat) :=
  match n with
  | 0x00DF => some [0x0073, 0x0073]          -- LATIN SMALL LETTER SHARP S
  | 0x0130 => some [0x0069, 0x0307]          -- LATIN CAPITAL LETTER I WITH DOT ABOVE
  | 0x017F => some [0x0073]                  -- LATIN SMALL LETTER LONG S
  | 0x0386 => some [0x03AC]                  -- GREEK CAPITAL LETTER ALPHA WITH TONOS
  | 0x0388 => some [0x03AD]                  -- GREEK CAPITAL LETTER EPSILON WITH TONOS
  | 0x0389 => some [0x03AE]                  -- GREEK CAPITAL LETTER ETA WITH TONOS
  | 0x038A => some [0x03AF]                  -- GREEK CAPITAL LETTER IOTA WITH TONOS
  | 0x038C => some [0x03CC]                  -- GREEK CAPITAL LETTER OMICRON WITH TONOS
  | 0x038E => some [0x03CD]                  -- GREEK CAPITAL LETTER UPSILON WITH TONOS
  | 0x038F => some [0x03CE]                  -- GREEK CAPITAL LETTER OMEGA WITH TONOS
  | 0x0391 => some [0x03B1]
  | 0x0392 => some [0x03B2]
  | 0x0393 => some [0x03B3]
  | 0x0394 => some [0x03B4]
  | 0x0395 => some [0x03B5]
  | 0x0396 => some [0x03B6]
  | 0x0397 => some [0x03B7]
  | 0x0398 => some [0x03B8]
  | 0x0399 => some [0x03B9]
  | 0x039A => some [0x03BA]
  | 0x039B => some [0x03BB]
  | 0x039C => some [0x03BC]
  | 0x039D => some [0x03BD]
  | 0x039E => some [0x03BE]
  | 0x039F => some [0x03BF]
  | 0x03A0 => some [0x03C0]
  | 0x03A1 => some [0x03C1]
  | 0x03A3 => some [0x03C3]
  | 0x03A4 => some [0x03C4]
  | 0x03A5 => some [0x03C5]
  | 0x03A6 => some [0x03C6]
  | 0x03A7 => some [0x03C7]
  | 0x03A8 => some [0x03C8]
  | 0x03A9 => some [0x03C9]
  | 0x03AA => some [0x03CA]
  | 0x03AB => some [0x03CB]
  | 0x03C2 => some [0x03C3]                  -- GREEK SMALL LETTER FINAL SIGMA
  | 0x1E9E => some [0x0073, 0x0073]          -- LATIN CAPITAL LETTER SHARP S
  | _ =>
    match simpleLowerNat? n with
    | some lower => some [lower]
    | none => none

/-- Fold one scalar under the practical extended Unicode case-fold subset. -/
private def extendedCaseFoldScalar (s : Scalar) : List Scalar :=
  match extendedCaseFoldNats? s.val with
  | some ns =>
    match scalarListFromNats? ns with
    | some scalars => scalars
    | none => [s]
  | none => [s]

/-- Apply compatibility decomposition plus supported simple case folding to a scalar list.
    This is a practical approximation of compatibility-aware caseless matching. -/
def caseFoldScalarsCompatibility (scalars : List Scalar) : List Scalar :=
  let compatibilityDecomposed := normalizeScalarsNFKD scalars
  let folded := compatibilityDecomposed.foldr
    (fun scalar acc => extendedCaseFoldScalar scalar ++ acc)
    []
  normalizeScalarsNFKD folded

/-- Whether two scalar lists are equal under the supported compatibility-aware case-folding subset. -/
def caselessEquivalentCompatibility (left right : List Scalar) : Bool :=
  caseFoldScalarsCompatibility left == caseFoldScalarsCompatibility right

-- ════════════════════════════════════════════════════════════════════
-- Grapheme Cluster Break Properties
-- ════════════════════════════════════════════════════════════════════

/-- Grapheme cluster break property for Unicode default extended grapheme segmentation. -/
inductive GraphemeBreakProperty where
  | cr             -- Carriage return
  | lf             -- Line feed
  | control        -- Control characters
  | extend         -- Combining marks, variation selectors, emoji modifiers
  | zwj            -- Zero-width joiner U+200D
  | regionalIndicator -- Regional indicator symbols
  | prepend        -- Prepend characters
  | spacingMark    -- Spacing combining marks
  | hangulL        -- Hangul leading jamo
  | hangulV        -- Hangul vowel jamo
  | hangulT        -- Hangul trailing jamo
  | hangulLV       -- Hangul LV syllable
  | hangulLVT      -- Hangul LVT syllable
  | extendedPictographic -- Emoji and pictographic bases used by GB11
  | other          -- Everything else (usually a grapheme base)
  deriving DecidableEq, Repr

/-- Indic_Conjunct_Break property values needed by GB9c. -/
inductive IndicConjunctBreakProperty where
  | consonant
  | extend
  | linker
  | other
  deriving DecidableEq, Repr

/-- Classify a scalar into its grapheme break property using Unicode 17 tables. -/
def classifyGraphemeBreak (s : Scalar) : GraphemeBreakProperty :=
  let v := s.val
  if v == 0x000D then .cr
  else if v == 0x000A then .lf
  else if GraphemeTables.isControl v then .control
  else if v == 0x200D then .zwj
  else if GraphemeTables.isExtend v then .extend
  else if 0x1F1E6 ≤ v && v ≤ 0x1F1FF then .regionalIndicator
  else if GraphemeTables.isPrepend v then .prepend
  else if GraphemeTables.isSpacingMark v then .spacingMark
  else if (0x1100 ≤ v && v ≤ 0x115F) || (0xA960 ≤ v && v ≤ 0xA97C) then .hangulL
  else if (0x1160 ≤ v && v ≤ 0x11A7) || (0xD7B0 ≤ v && v ≤ 0xD7C6) then .hangulV
  else if (0x11A8 ≤ v && v ≤ 0x11FF) || (0xD7CB ≤ v && v ≤ 0xD7FB) then .hangulT
  else if 0xAC00 ≤ v && v ≤ 0xD7A3 then
    if (v - 0xAC00) % 28 == 0 then .hangulLV else .hangulLVT
  else if GraphemeTables.isExtendedPictographic v then .extendedPictographic
  else .other

/-- Classify a scalar into the Indic_Conjunct_Break property values used by GB9c. -/
def classifyIndicConjunctBreak (s : Scalar) : IndicConjunctBreakProperty :=
  let v := s.val
  if GraphemeTables.isIndicConsonant v then .consonant
  else if GraphemeTables.isIndicLinker v then .linker
  else if GraphemeTables.isIndicExtend v then .extend
  else .other

/-- Whether a grapheme cluster boundary exists between two adjacent scalars
  under the pairwise Unicode default extended grapheme rules. -/
def isGraphemeBreak (left right : GraphemeBreakProperty) : Bool :=
  match left, right with
  | .cr, .lf => false                       -- GB3: Do not break between CR and LF
  | .cr, _ => true                          -- GB4: Break after CR
  | .lf, _ => true                          -- GB4: Break after LF
  | .control, _ => true                     -- GB4: Break after Control
  | _, .cr => true                          -- GB5: Break before CR
  | _, .lf => true                          -- GB5: Break before LF
  | _, .control => true                     -- GB5: Break before Control
  | .hangulL, .hangulL => false             -- GB6: L × L
  | .hangulL, .hangulV => false             -- GB6: L × V
  | .hangulL, .hangulLV => false            -- GB6: L × LV
  | .hangulL, .hangulLVT => false           -- GB6: L × LVT
  | .hangulLV, .hangulV => false            -- GB7: (LV | V) × V
  | .hangulV, .hangulV => false             -- GB7: (LV | V) × V
  | .hangulLV, .hangulT => false            -- GB7: (LV | V) × T
  | .hangulV, .hangulT => false             -- GB7: (LV | V) × T
  | .hangulLVT, .hangulT => false           -- GB8: (LVT | T) × T
  | .hangulT, .hangulT => false             -- GB8: (LVT | T) × T
  | _, .extend => false                     -- GB9: × Extend
  | _, .zwj => false                        -- GB9: × ZWJ
  | _, .spacingMark => false                -- GB9a: × SpacingMark
  | .prepend, _ => false                    -- GB9b: Prepend ×
  | _, _ => true                            -- GB999: Otherwise, break

-- ════════════════════════════════════════════════════════════════════
-- String Distance (Levenshtein Specification)
-- ════════════════════════════════════════════════════════════════════

/-- Levenshtein edit distance between two scalar lists (specification level). -/
def levenshteinDistance : List Scalar → List Scalar → Nat
  | [], t => t.length
  | s, [] => s.length
  | s :: ss, t :: ts =>
    let cost := if s.val == t.val then 0 else 1
    min (min (levenshteinDistance ss (t :: ts) + 1)   -- deletion
             (levenshteinDistance (s :: ss) ts + 1))  -- insertion
        (levenshteinDistance ss ts + cost)            -- substitution

/-- Levenshtein distance is zero for identical lists. -/
theorem levenshteinDistance_self (xs : List Scalar) : levenshteinDistance xs xs = 0 := by
  induction xs with
  | nil => simp [levenshteinDistance]
  | cons x rest ih =>
    simp only [levenshteinDistance, beq_self_eq_true, ite_true]
    simp [ih]

-- ════════════════════════════════════════════════════════════════════
-- Additional Scalar Invariant Theorems
-- ════════════════════════════════════════════════════════════════════

/-- Control characters below 0x20 are always valid scalars. -/
theorem isScalar_c0_control (n : Nat) (h : n ≤ 0x1F) : IsScalar n :=
  ⟨by omega, fun ⟨hl, _⟩ => by omega⟩

/-- Printable ASCII characters are always valid scalars. -/
theorem isScalar_printable (n : Nat) (h : IsPrintable n) : IsScalar n :=
  ⟨by have := h.1; have := h.2; omega, fun ⟨hl, _⟩ => by have := h.2; omega⟩

/-- BMP scalars have a byte count of 1, 2, or 3. -/
theorem byteCount_bmp (s : Scalar) (h : s.val < 0x10000) :
    Scalar.byteCount s ≤ 3 := by
  unfold Scalar.byteCount
  by_cases h1 : s.val < 0x80
  · simp [h1]
  · simp [h1]
    by_cases h2 : s.val < 0x800
    · simp [h2]
    · simp [h2, h]

/-- The replacement character is not a noncharacter. -/
theorem replacement_not_noncharacter :
    ¬ IsNoncharacter Scalar.replacement.val := by decide

/-- BMP scalars have plane 0. -/
theorem plane_zero_of_bmp (s : Scalar) (h : s.val < 0x10000) :
    Scalar.plane s = 0 := by
  unfold Scalar.plane
  exact Nat.div_eq_of_lt (by omega)

/-- Supplementary scalars have plane > 0. -/
theorem plane_pos_of_supplementary (s : Scalar) (h : 0x10000 ≤ s.val) :
    0 < Scalar.plane s := by
  unfold Scalar.plane
  omega

/-- Digits are always ASCII. -/
theorem digit_isAscii (n : Nat) (h : IsDigit n) : IsAscii n := by
  unfold IsDigit at h; unfold IsAscii; omega

/-- Letters are always ASCII. -/
theorem alpha_isAscii (n : Nat) (h : IsAlpha n) : IsAscii n := by
  cases h with
  | inl hu => unfold IsUppercase at hu; unfold IsAscii; omega
  | inr hl => unfold IsLowercase at hl; unfold IsAscii; omega

/-- toLower on 'A' gives 'a'. -/
theorem toLowerAscii_A :
    Scalar.toLowerAscii? ⟨0x41, by decide⟩ = some ⟨0x61, by decide⟩ := by native_decide

/-- toLower on 'Z' gives 'z'. -/
theorem toLowerAscii_Z :
    Scalar.toLowerAscii? ⟨0x5A, by decide⟩ = some ⟨0x7A, by decide⟩ := by native_decide

/-- toUpper on 'a' gives 'A'. -/
theorem toUpperAscii_a :
    Scalar.toUpperAscii? ⟨0x61, by decide⟩ = some ⟨0x41, by decide⟩ := by native_decide

/-- toUpper on 'z' gives 'Z'. -/
theorem toUpperAscii_z :
    Scalar.toUpperAscii? ⟨0x7A, by decide⟩ = some ⟨0x5A, by decide⟩ := by native_decide

/-- UTF-16 surrogate pair for U+10000. -/
theorem surrogatePair_U10000 :
    toSurrogatePair ⟨0x10000, by decide⟩ (by decide) = (0xD800, 0xDC00) := by native_decide

/-- UTF-16 surrogate pair for U+10FFFF. -/
theorem surrogatePair_U10FFFF :
    toSurrogatePair ⟨0x10FFFF, by decide⟩ (by decide) = (0xDBFF, 0xDFFF) := by native_decide

/-- UTF-16 surrogate pair for U+1F600 (😀). -/
theorem surrogatePair_U1F600 :
    toSurrogatePair ⟨0x1F600, by decide⟩ (by decide) = (0xD83D, 0xDE00) := by native_decide

/-- fromSurrogatePair? round-trips for U+10000. -/
theorem fromSurrogatePair_U10000 :
    fromSurrogatePair? 0xD800 0xDC00 = some ⟨0x10000, by decide⟩ := by native_decide

/-- fromSurrogatePair? round-trips for U+10FFFF. -/
theorem fromSurrogatePair_U10FFFF :
    fromSurrogatePair? 0xDBFF 0xDFFF = some ⟨0x10FFFF, by decide⟩ := by native_decide

/-- fromSurrogatePair? round-trips for U+1F600 (😀). -/
theorem fromSurrogatePair_U1F600 :
    fromSurrogatePair? 0xD83D 0xDE00 = some ⟨0x1F600, by decide⟩ := by native_decide

/-- fromSurrogatePair? rejects invalid hi surrogate. -/
theorem fromSurrogatePair_invalid_hi :
    fromSurrogatePair? 0x0041 0xDC00 = none := by native_decide

/-- fromSurrogatePair? rejects invalid lo surrogate. -/
theorem fromSurrogatePair_invalid_lo :
    fromSurrogatePair? 0xD800 0x0041 = none := by native_decide

/-- isGraphemeBreak: CR+LF is not a break point. -/
theorem graphemeBreak_crLf : isGraphemeBreak .cr .lf = false := rfl

/-- isGraphemeBreak: break after CR for other. -/
theorem graphemeBreak_cr_other : isGraphemeBreak .cr .other = true := rfl

/-- isGraphemeBreak: other + extend is not a break (GB9). -/
theorem graphemeBreak_other_extend : isGraphemeBreak .other .extend = false := rfl

/-- isGraphemeBreak: extend + extend is not a break (GB9). -/
theorem graphemeBreak_extend_extend : isGraphemeBreak .extend .extend = false := rfl

/-- isGraphemeBreak: Hangul L + V is not a break (GB6). -/
theorem graphemeBreak_hangulLV : isGraphemeBreak .hangulL .hangulV = false := rfl

/-- isGraphemeBreak: break between two 'other' categories. -/
theorem graphemeBreak_other_other : isGraphemeBreak .other .other = true := rfl

/-- isGraphemeBreak: ZWJ never causes a break on the right. -/
theorem graphemeBreak_other_zwj : isGraphemeBreak .other .zwj = false := rfl

/-- Successor of null is U+0001. -/
theorem succ_null : Scalar.succ? Scalar.null = some ⟨1, by decide⟩ := by native_decide

/-- Successor of U+D7FF skips surrogates to U+E000. -/
theorem succ_D7FF : Scalar.succ? ⟨0xD7FF, by decide⟩ = some ⟨0xE000, by decide⟩ := by native_decide

/-- Successor of U+10FFFF is none (end of Unicode). -/
theorem succ_max : Scalar.succ? Scalar.maxScalar = none := by native_decide

/-- Predecessor of U+E000 skips surrogates back to U+D7FF. -/
theorem pred_E000 : Scalar.pred? ⟨0xE000, by decide⟩ = some ⟨0xD7FF, by decide⟩ := by native_decide

/-- Predecessor of null is none. -/
theorem pred_null : Scalar.pred? Scalar.null = none := by native_decide

end Radix.UTF8.Spec
