/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.UTF8.Spec
import Radix.UTF8.Ops

/-!
# UTF-8 Proofs (Layer 3)

Basic correctness lemmas for the UTF-8 model.
-/

set_option autoImplicit false

namespace Radix.UTF8

open Spec

private theorem byteCount_pos (s : Scalar) : 1 ≤ Spec.Scalar.byteCount s := by
  rcases s with ⟨n, hs⟩
  unfold Spec.Scalar.byteCount
  by_cases h1 : n < 0x80
  · simp [h1]
  · simp [h1]
    by_cases h2 : n < 0x800
    · simp [h2]
    · simp [h2]
      by_cases h3 : n < 0x10000
      · simp [h3]
      · simp [h3]

private theorem byte_toNat_eq (n : Nat) (h : n < 256) :
    (n.toUInt8).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

private theorem continuationByte_true (payload : Nat) (h : payload < 0x40) :
    Spec.isContinuationByte ((0x80 + payload).toUInt8) = true := by
  unfold Spec.isContinuationByte
  rw [byte_toNat_eq (0x80 + payload) (by omega)]
  simp
  omega

private theorem continuationPayload_eq (payload : Nat) (h : payload < 0x40) :
    Spec.continuationPayload ((0x80 + payload).toUInt8) = payload := by
  unfold Spec.continuationPayload
  rw [byte_toNat_eq (0x80 + payload) (by omega)]
  omega

private theorem encodeAll_length_ge_scalars (scalars : List Scalar) :
    scalars.length ≤ (Spec.encodeAll scalars).length := by
  induction scalars with
  | nil => simp [Spec.encodeAll]
  | cons s rest ih =>
      have hpos : 1 ≤ (Spec.encode s).length := by
        rw [Spec.encode_length_eq_byteCount]
        exact byteCount_pos s
      simp [Spec.encodeAll, List.length_append]
      omega

/-- Decoding an encoded scalar is unaffected by trailing bytes. -/
private theorem decodeNext_encode_prefix (s : Scalar) (tail : List UInt8) :
    Spec.decodeNext? (Spec.encode s ++ tail) = some (s, Spec.Scalar.byteCount s) := by
  rcases s with ⟨n, hs⟩
  by_cases h1 : n < 0x80
  · have h256 : n < 256 := by omega
    simp [Spec.encode, Spec.decodeNext?, Spec.Scalar.byteCount, h1, Nat.mod_eq_of_lt h256]
  · by_cases h2 : n < 0x800
    · have hLead : 0xC0 + n / 0x40 < 256 := by omega
      have hCont : Spec.isContinuationByte ((0x80 + n % 0x40).toUInt8) = true :=
        continuationByte_true _ (Nat.mod_lt _ (by decide))
      have hPayload : Spec.continuationPayload ((0x80 + n % 0x40).toUInt8) = n % 0x40 :=
        continuationPayload_eq _ (Nat.mod_lt _ (by decide))
      have hCont' : Spec.isContinuationByte (0x80 + UInt8.ofNat (n % 0x40)) = true := by
        simpa using hCont
      have hPayload' : Spec.continuationPayload (0x80 + UInt8.ofNat (n % 0x40)) = n % 0x40 := by
        simpa using hPayload
      have hCode : n / 0x40 * 0x40 + n % 0x40 = n := by
        simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm] using Nat.div_add_mod n 0x40
      have hNotAscii : ¬ 0xC0 + n / 0x40 < 0x80 := by omega
      have hTwoRange : 0xC2 ≤ 0xC0 + n / 0x40 ∧ 0xC0 + n / 0x40 < 0xE0 := by omega
      simp [Spec.encode, Spec.decodeNext?, Spec.Scalar.byteCount, h1, h2, hNotAscii, hTwoRange,
        Nat.mod_eq_of_lt hLead, hCont', hPayload']
      constructor
      · simpa [hCode] using hs
      · exact hCode
    · by_cases h3 : n < 0x10000
      · have hLead : 0xE0 + n / 0x1000 < 256 := by omega
        have hCont1 : Spec.isContinuationByte ((0x80 + (n / 0x40) % 0x40).toUInt8) = true :=
          continuationByte_true _ (Nat.mod_lt _ (by decide))
        have hCont2 : Spec.isContinuationByte ((0x80 + n % 0x40).toUInt8) = true :=
          continuationByte_true _ (Nat.mod_lt _ (by decide))
        have hPayload1 :
            Spec.continuationPayload ((0x80 + (n / 0x40) % 0x40).toUInt8) = (n / 0x40) % 0x40 :=
          continuationPayload_eq _ (Nat.mod_lt _ (by decide))
        have hPayload2 : Spec.continuationPayload ((0x80 + n % 0x40).toUInt8) = n % 0x40 :=
          continuationPayload_eq _ (Nat.mod_lt _ (by decide))
        have hCont1' : Spec.isContinuationByte (0x80 + UInt8.ofNat (n / 0x40 % 0x40)) = true := by
          simpa using hCont1
        have hCont2' : Spec.isContinuationByte (0x80 + UInt8.ofNat (n % 0x40)) = true := by
          simpa using hCont2
        have hPayload1' :
            Spec.continuationPayload (0x80 + UInt8.ofNat (n / 0x40 % 0x40)) = n / 0x40 % 0x40 := by
          simpa using hPayload1
        have hPayload2' : Spec.continuationPayload (0x80 + UInt8.ofNat (n % 0x40)) = n % 0x40 := by
          simpa using hPayload2
        have hCode :
            n / 0x1000 * 0x1000 + (n / 0x40) % 0x40 * 0x40 + n % 0x40 = n := by
          have hsplit0 := Nat.div_add_mod n 0x40
          have hsplit1 := Nat.div_add_mod (n / 0x40) 0x40
          have hdiv : n / 0x40 / 0x40 = n / 0x1000 := by
            simpa [show 0x40 * 0x40 = 0x1000 by decide] using Nat.div_div_eq_div_mul n 0x40 0x40
          omega
        have hNotAscii : ¬ 0xE0 + n / 0x1000 < 0x80 := by omega
        have hLeadThree : 0xE0 + n / 0x1000 < 0xF0 := by omega
        have hMinCode : 0x800 ≤ n / 0x1000 * 0x1000 + (n / 0x40) % 0x40 * 0x40 + n % 0x40 := by
          rw [hCode]
          omega
        simp [Spec.encode, Spec.decodeNext?, Spec.Scalar.byteCount, h1, h2, h3, hNotAscii,
          Nat.mod_eq_of_lt hLead, hCont1', hCont2', hPayload1', hPayload2', hLeadThree, hMinCode]
        constructor
        · simpa [hCode] using hs
        · exact hCode
      · have hUpper : n < 0x110000 := hs.1
        have hLeadRange : 0xF0 ≤ 0xF0 + n / 0x40000 ∧ 0xF0 + n / 0x40000 < 0xF5 := by
          omega
        have hLead : 0xF0 + n / 0x40000 < 256 := by omega
        have hCont1 : Spec.isContinuationByte ((0x80 + (n / 0x1000) % 0x40).toUInt8) = true :=
          continuationByte_true _ (Nat.mod_lt _ (by decide))
        have hCont2 : Spec.isContinuationByte ((0x80 + (n / 0x40) % 0x40).toUInt8) = true :=
          continuationByte_true _ (Nat.mod_lt _ (by decide))
        have hCont3 : Spec.isContinuationByte ((0x80 + n % 0x40).toUInt8) = true :=
          continuationByte_true _ (Nat.mod_lt _ (by decide))
        have hPayload1 :
            Spec.continuationPayload ((0x80 + (n / 0x1000) % 0x40).toUInt8) = (n / 0x1000) % 0x40 :=
          continuationPayload_eq _ (Nat.mod_lt _ (by decide))
        have hPayload2 :
            Spec.continuationPayload ((0x80 + (n / 0x40) % 0x40).toUInt8) = (n / 0x40) % 0x40 :=
          continuationPayload_eq _ (Nat.mod_lt _ (by decide))
        have hPayload3 : Spec.continuationPayload ((0x80 + n % 0x40).toUInt8) = n % 0x40 :=
          continuationPayload_eq _ (Nat.mod_lt _ (by decide))
        have hCont1' : Spec.isContinuationByte (0x80 + UInt8.ofNat (n / 0x1000 % 0x40)) = true := by
          simpa using hCont1
        have hCont2' : Spec.isContinuationByte (0x80 + UInt8.ofNat (n / 0x40 % 0x40)) = true := by
          simpa using hCont2
        have hCont3' : Spec.isContinuationByte (0x80 + UInt8.ofNat (n % 0x40)) = true := by
          simpa using hCont3
        have hPayload1' :
            Spec.continuationPayload (0x80 + UInt8.ofNat (n / 0x1000 % 0x40)) = n / 0x1000 % 0x40 := by
          simpa using hPayload1
        have hPayload2' :
            Spec.continuationPayload (0x80 + UInt8.ofNat (n / 0x40 % 0x40)) = n / 0x40 % 0x40 := by
          simpa using hPayload2
        have hPayload3' : Spec.continuationPayload (0x80 + UInt8.ofNat (n % 0x40)) = n % 0x40 := by
          simpa using hPayload3
        have hCode :
            n / 0x40000 * 0x40000 + (n / 0x1000) % 0x40 * 0x1000
              + (n / 0x40) % 0x40 * 0x40 + n % 0x40 = n := by
          have hsplit0 := Nat.div_add_mod n 0x40
          have hsplit1 := Nat.div_add_mod (n / 0x40) 0x40
          have hsplit2 := Nat.div_add_mod (n / 0x1000) 0x40
          have hdiv1 : n / 0x40 / 0x40 = n / 0x1000 := by
            simpa [show 0x40 * 0x40 = 0x1000 by decide] using Nat.div_div_eq_div_mul n 0x40 0x40
          have hdiv2 : n / 0x1000 / 0x40 = n / 0x40000 := by
            simpa [show 0x1000 * 0x40 = 0x40000 by decide, Nat.mul_comm] using Nat.div_div_eq_div_mul n 0x1000 0x40
          omega
        have hNotAscii : ¬ 0xF0 + n / 0x40000 < 0x80 := by omega
        have hNotTwo : ¬ (0xC2 ≤ 0xF0 + n / 0x40000 ∧ 0xF0 + n / 0x40000 < 0xE0) := by omega
        have hMinCode :
            0x10000 ≤ n / 0x40000 * 0x40000 + (n / 0x1000) % 0x40 * 0x1000 + (n / 0x40) % 0x40 * 0x40 + n % 0x40 := by
          rw [hCode]
          omega
        simp [Spec.encode, Spec.decodeNext?, Spec.Scalar.byteCount, h1, h2, h3, hNotAscii, hNotTwo,
          Nat.mod_eq_of_lt hLead, hCont1', hCont2', hCont3', hPayload1', hPayload2', hPayload3', hLeadRange, hMinCode]
        constructor
        · simpa [hCode] using hs
        · exact hCode

/-- Decoding the canonical encoding of a scalar returns the original scalar and
    the number of bytes consumed by the UTF-8 length class. -/
theorem decodeNext_encode (s : Scalar) :
    Spec.decodeNext? (Spec.encode s) = some (s, Spec.Scalar.byteCount s) := by
  simpa using decodeNext_encode_prefix s []

/-- Fuel bounded by the number of scalars is sufficient to decode an encoded list. -/
theorem decodeAllAux_encodeAll (scalars : List Scalar) (fuel : Nat)
    (h : scalars.length ≤ fuel) :
    Spec.decodeAllAux fuel (Spec.encodeAll scalars) = some scalars := by
  induction scalars generalizing fuel with
  | nil =>
      cases fuel <;> simp [Spec.decodeAllAux, Spec.encodeAll]
  | cons s rest ih =>
      cases fuel with
      | zero => cases h
      | succ fuel =>
          have hrest : rest.length ≤ fuel := by
            simpa using Nat.succ_le_succ_iff.mp (by simpa using h)
          have hdecode := decodeNext_encode_prefix s (Spec.encodeAll rest)
          have hdrop :
              (Spec.encode s ++ Spec.encodeAll rest).drop (Spec.Scalar.byteCount s) = Spec.encodeAll rest := by
            rw [← Spec.encode_length_eq_byteCount s]
            simp
          change Spec.decodeAllAux (fuel + 1) (Spec.encode s ++ Spec.encodeAll rest) = some (s :: rest)
          cases henc : Spec.encode s with
          | nil => cases (Spec.encode_ne_nil s henc)
          | cons b bs =>
              have hne : ((b :: bs) ++ Spec.encodeAll rest) = [] → False := by
                intro hnil
                cases hnil
              simp [henc] at hdecode hdrop
              rw [Spec.decodeAllAux.eq_4 ((b :: bs) ++ Spec.encodeAll rest) fuel hne]
              change (match Spec.decodeNext? (b :: (bs ++ Spec.encodeAll rest)) with
                | none => none
                | some (scalar, consumed) =>
                    match Spec.decodeAllAux fuel ((b :: (bs ++ Spec.encodeAll rest)).drop consumed) with
                    | none => none
                    | some decodedRest => some (scalar :: decodedRest)) = some (s :: rest)
              rw [hdecode]
              simp [hdrop, ih fuel hrest]

/-- Decoding a fully encoded scalar list returns the original list. -/
theorem decodeAll_encodeAll (scalars : List Scalar) :
    Spec.decodeAll? (Spec.encodeAll scalars) = some scalars := by
  unfold Spec.decodeAll?
  exact decodeAllAux_encodeAll scalars (Spec.encodeAll scalars).length (encodeAll_length_ge_scalars scalars)

/-- Layer 2 encoded length agrees with the specification. -/
theorem encodedLength_eq_spec (s : Scalar) :
    encodedLength s = Spec.Scalar.byteCount s := by
  unfold encodedLength
  simpa using Spec.encode_length_eq_byteCount s

/-- Operation-layer decoding round-trips encoded scalar lists. -/
theorem decodeBytes_encodeScalars (scalars : List Scalar) :
    decodeBytes? (encodeScalars scalars) = some scalars := by
  have hList : byteArrayToList (encodeScalars scalars) = Spec.encodeAll scalars := by
    simp [byteArrayToList, encodeScalars]
  simp [decodeBytes?, hList, decodeAll_encodeAll]

/-- Operation-layer scalar counting matches the encoded input list. -/
theorem scalarCount_encodeScalars (scalars : List Scalar) :
    scalarCount? (encodeScalars scalars) = some scalars.length := by
  simp [scalarCount?, decodeBytes_encodeScalars]

/-- Encoded UTF-8 bytes satisfy the specification-level well-formedness predicate. -/
theorem isWellFormed_encodeScalar (s : Scalar) :
    Spec.WellFormed (Spec.encode s) := by
  exact Spec.wellFormed_encode s

/-- Operation-layer encodings are always accepted by the decoder. -/
theorem isWellFormed_encodeScalars (scalars : List Scalar) :
    isWellFormed (encodeScalars scalars) = true := by
  simp [isWellFormed, decodeBytes_encodeScalars]

-- ════════════════════════════════════════════════════════════════════
-- Additional Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- Decoding an empty byte array yields an empty scalar list. -/
theorem decodeBytes_empty : decodeBytes? (ByteArray.mk #[]) = some [] := by
  simp [decodeBytes?, byteArrayToList, Spec.decodeAll?, Spec.decodeAllAux]

/-- An empty byte array is well-formed. -/
theorem isWellFormed_empty : isWellFormed (ByteArray.mk #[]) = true := by
  simp [isWellFormed, decodeBytes_empty]

/-- Operation-layer list decoding round-trips. -/
theorem decodeList_encodeAll (scalars : List Scalar) :
    decodeList? (Spec.encodeAll scalars) = some scalars := by
  simp [decodeList?, decodeAll_encodeAll]

/-- An empty list is well-formed (operation layer). -/
theorem isWellFormedList_nil : isWellFormedList [] = true := by
  simp [isWellFormedList, decodeList?, Spec.decodeAll?, Spec.decodeAllAux]

/-- Scalar.isAscii agrees with the bound check. -/
theorem scalar_isAscii_iff (s : Scalar) :
    Spec.Scalar.isAscii s = true ↔ s.val < 0x80 := by
  simp [Spec.Scalar.isAscii]

/-- Scalar.isBMP agrees with the bound check. -/
theorem scalar_isBMP_iff (s : Scalar) :
    Spec.Scalar.isBMP s = true ↔ s.val < 0x10000 := by
  simp [Spec.Scalar.isBMP]

/-- ASCII scalars are always in the BMP. -/
theorem ascii_implies_bmp (s : Scalar) (h : Spec.Scalar.isAscii s = true) :
    Spec.Scalar.isBMP s = true := by
  rw [scalar_isAscii_iff] at h
  rw [scalar_isBMP_iff]
  omega

/-- Supplementary scalars are never in the BMP. -/
theorem supplementary_not_bmp (s : Scalar) (h : Spec.Scalar.isSupplementary s = true) :
    Spec.Scalar.isBMP s = false := by
  unfold Spec.Scalar.isSupplementary at h
  unfold Spec.Scalar.isBMP
  simp at h ⊢
  omega

/-- The null scalar encodes to a single zero byte. -/
theorem encode_null : Spec.encode Spec.Scalar.null = [0] := by
  decide

/-- The replacement character encodes to EF BF BD. -/
theorem encode_replacement :
    Spec.encode Spec.Scalar.replacement = [0xEF, 0xBF, 0xBD] := by
  decide

/-- The plane of an ASCII scalar is 0. -/
theorem plane_ascii (s : Scalar) (h : s.val < 0x80) :
    Spec.Scalar.plane s = 0 := by
  unfold Spec.Scalar.plane
  exact Nat.div_eq_of_lt (by omega)

/-- Encoding is injective: distinct scalars produce distinct byte sequences. -/
theorem encode_injective (s1 s2 : Scalar) (h : Spec.encode s1 = Spec.encode s2) :
    s1 = s2 := by
  have hd1 := decodeNext_encode s1
  have hd2 := decodeNext_encode s2
  rw [h] at hd1
  rw [hd1] at hd2
  have heq := congr_arg Prod.fst (Option.some.inj hd2)
  simp at heq
  exact heq

/-- encodeAll is injective: distinct scalar lists produce distinct byte sequences. -/
theorem encodeAll_injective (s1 s2 : List Scalar)
    (h : Spec.encodeAll s1 = Spec.encodeAll s2) : s1 = s2 := by
  have h1 := decodeAll_encodeAll s1
  have h2 := decodeAll_encodeAll s2
  rw [h] at h1
  rw [h1] at h2
  exact Option.some_injective _ h2

/-- The total byte length function agrees with actual encoding length. -/
theorem totalByteLength_eq_encodeAll_length (scalars : List Scalar) :
    totalByteLength scalars = (Spec.encodeAll scalars).length := by
  -- Generalize the accumulator for the foldl induction
  suffices h : ∀ (acc : Nat),
      scalars.foldl (fun a s => a + Scalar.byteCount s) acc =
      acc + (Spec.encodeAll scalars).length by
    simpa [totalByteLength] using h 0
  induction scalars with
  | nil => simp [Spec.encodeAll]
  | cons s rest ih =>
    intro acc
    simp only [List.foldl_cons, Spec.encodeAll, List.length_append,
               Spec.encode_length_eq_byteCount]
    rw [ih]
    omega

/-- An empty list has no BOM. -/
theorem hasBOM_nil : Spec.hasBOM [] = false := by rfl

/-- BOM detection is correct on the BOM itself. -/
theorem hasBOM_bom : Spec.hasBOM Spec.bom = true := by decide

/-- stripBOM on a list without BOM is identity. -/
theorem stripBOM_no_bom (bytes : List UInt8) (h : Spec.hasBOM bytes = false) :
    Spec.stripBOM bytes = bytes := by
  unfold Spec.stripBOM
  rw [h]
  simp

/-- allAscii on an empty byte array is true. -/
theorem allAscii_empty : allAscii (ByteArray.mk #[]) = true := by
  simp [allAscii, byteArrayToList, Spec.allAscii]

/-- Encoding all-ASCII scalars produces an all-ASCII byte stream. -/
theorem allAscii_encode_of_ascii (s : Scalar) (h : s.val < 0x80) :
    Spec.allAscii (Spec.encode s) = true := by
  have h256 : s.val < 256 := by omega
  simp [Spec.allAscii, Spec.encode, h, List.all_cons, Spec.isAsciiByte,
        Nat.mod_eq_of_lt h256]

end Radix.UTF8
