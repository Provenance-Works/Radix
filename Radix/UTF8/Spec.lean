/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

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

end Radix.UTF8.Spec
