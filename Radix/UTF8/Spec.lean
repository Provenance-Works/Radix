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

/-- Number of bytes required to encode the scalar in UTF-8. -/
def byteCount (s : Scalar) : Nat :=
  let n := s.val
  if n < 0x80 then 1
  else if n < 0x800 then 2
  else if n < 0x10000 then 3
  else 4

end Scalar

/-- A byte is a UTF-8 continuation byte iff it is in `[0x80, 0xBF]`. -/
def isContinuationByte (b : UInt8) : Bool :=
  0x80 ≤ b.toNat && b.toNat < 0xC0

/-- The payload carried by a continuation byte. -/
def continuationPayload (b : UInt8) : Nat :=
  b.toNat - 0x80

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

end Radix.UTF8.Spec
