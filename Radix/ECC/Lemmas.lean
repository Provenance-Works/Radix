/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.ECC.Spec
import Radix.ECC.Ops

/-!
# Error Correction Proofs (Layer 3)
-/

set_option autoImplicit false

namespace Radix.ECC

/-- Freshly encoded codewords satisfy all parity equations. -/
theorem check_encodeNibble (n : Nibble) :
  check (encodeNibble n) = true := by
  fin_cases n <;> decide

/-- Decoding an encoded nibble returns the original data bits. -/
theorem decode_encodeNibble (n : Nibble) :
  decode (encodeNibble n) = some n.val.toUInt8 := by
  fin_cases n <;> decide

/-- Encoded nibbles are classified as already clean. -/
theorem status?_encodeNibble (n : Nibble) :
  Radix.ECC.status? (encodeNibble n) = some Radix.ECC.Status.clean := by
  fin_cases n <;> decide

/-- Encoded nibbles require no correction index. -/
theorem errorIndex?_encodeNibble (n : Nibble) :
  Radix.ECC.errorIndex? (encodeNibble n) = none := by
  fin_cases n <;> decide

/-- Correcting a clean codeword leaves it unchanged. -/
theorem correct_encodeNibble (n : Nibble) :
    correct (encodeNibble n) = some (encodeNibble n) := by
  fin_cases n <;> decide

/-- Decoding after correction agrees with decoding a clean encoded nibble. -/
theorem decodeAfterCorrect_encodeNibble (n : Nibble) :
  Radix.ECC.decodeAfterCorrect (encodeNibble n) = some n.val.toUInt8 := by
  fin_cases n <;> decide

/-- Single-bit corruption is classified at the flipped bit position. -/
theorem status?_single_bit (n : Nibble) (idx : Fin 7) :
  Radix.ECC.status? (toByte (Spec.flipAt (Spec.ofNibble n) idx)) = some (Radix.ECC.Status.corrected idx) := by
  fin_cases n <;> fin_cases idx <;> decide

/-- Correcting any single-bit error preserves the encoded payload. -/
theorem decode_correct_single_bit (n : Nibble) (idx : Fin 7) :
  (match (correct (toByte (Spec.flipAt (Spec.ofNibble n) idx)) : Option UInt8) with
  | some corrected => decode corrected
  | none => none) = some n.val.toUInt8 := by
  fin_cases n <;> fin_cases idx <;> decide

/-- Decoding after correction succeeds for any single-bit corruption. -/
theorem decodeAfterCorrect_single_bit (n : Nibble) (idx : Fin 7) :
  Radix.ECC.decodeAfterCorrect (toByte (Spec.flipAt (Spec.ofNibble n) idx)) = some n.val.toUInt8 := by
  fin_cases n <;> fin_cases idx <;> decide

-- ════════════════════════════════════════════════════════════════════
-- Additional Correctness Lemmas
-- ════════════════════════════════════════════════════════════════════

set_option maxHeartbeats 800000 in
/-- Encoding is injective: distinct nibbles produce distinct codeword bytes. -/
theorem encodeNibble_injective (n1 n2 : Nibble) (h : encodeNibble n1 = encodeNibble n2) :
    n1 = n2 := by
  fin_cases n1 <;> fin_cases n2 <;> simp_all [encodeNibble, toByte, Spec.ofNibble,
    Spec.xor3, Spec.bitVal]

/-- Encoding followed by decoding is a round-trip for all nibbles. -/
theorem decode_encodeNibble_roundtrip (n : Nibble) :
    ∃ v, decode (encodeNibble n) = some v ∧ v.toNat = n.val := by
  fin_cases n <;> decide

/-- The syndrome of a fresh encoding is None (no error detected). -/
theorem syndrome_encodeNibble_zero (n : Nibble) :
    Radix.ECC.syndrome (encodeNibble n) = some 0 := by
  fin_cases n <;> decide

/-- isCodewordByte holds for all encoded nibbles. -/
theorem isCodewordByte_encodeNibble (n : Nibble) :
    isCodewordByte (encodeNibble n) = true := by
  fin_cases n <;> decide

/-- Encoding nibbles and decoding produces the original list (clean channel). -/
theorem decodeNibbles_encodeNibbles (ns : List Nibble) :
    decodeNibbles (encodeNibbles ns) = ns.map (fun n => some n.val.toUInt8) := by
  simp [decodeNibbles, encodeNibbles, List.map_map, Function.comp_def, decode_encodeNibble]

/-- countClean on a list of freshly encoded nibbles equals the list length. -/
theorem countClean_encodeNibbles (ns : List Nibble) :
    countClean (encodeNibbles ns) = ns.length := by
  suffices h : ∀ (acc : Nat),
      (encodeNibbles ns).foldl (fun a b => a + if check b then 1 else 0) acc =
      acc + ns.length by
    simpa [countClean] using h 0
  induction ns with
  | nil => simp [encodeNibbles]
  | cons n rest ih =>
    intro acc
    simp only [encodeNibbles, List.map_cons, List.foldl_cons, check_encodeNibble, ite_true]
    simp only [encodeNibbles] at ih
    rw [ih]
    simp [List.length_cons]
    omega

/-- errorRate for a clean channel is (0, length). -/
theorem errorRate_clean (ns : List Nibble) :
    errorRate (encodeNibbles ns) = (0, ns.length) := by
  unfold errorRate
  rw [countClean_encodeNibbles]
  simp [encodeNibbles]

/-- correctAll on clean codewords returns all Some. -/
theorem correctAll_clean (ns : List Nibble) :
    correctAll (encodeNibbles ns) = ns.map (fun n => some (encodeNibble n)) := by
  simp [correctAll, encodeNibbles, List.map_map, Function.comp_def, correct_encodeNibble]

/-- SECDED freshly encoded codewords are classified as noError. -/
theorem classifySECDED_fresh (n : Nibble) :
    classifySECDED (encodeNibbleSECDED n) = Spec.SECDEDResult.noError := by
  fin_cases n <;> decide

/-- toBitList always returns a list of length 7. -/
theorem toBitList_length (c : Spec.Codeword74) :
    (Radix.ECC.toBitList c).length = 7 := by
  simp [Radix.ECC.toBitList, Spec.toBitList]

/-- Codeword weight of valid codewords is in {0,3,4,7}. -/
theorem valid_codeword_weight (n : Nibble) :
    codewordWeight (Spec.ofNibble n) ∈ ({0, 3, 4, 7} : Finset Nat) := by
  fin_cases n <;> decide

/-- Codeword distance is symmetric for valid codewords. -/
theorem codewordDist_comm_valid (n1 n2 : Nibble) :
    codewordDist (Spec.ofNibble n1) (Spec.ofNibble n2) =
    codewordDist (Spec.ofNibble n2) (Spec.ofNibble n1) := by
  fin_cases n1 <;> fin_cases n2 <;> decide

/-- Codeword distance from a codeword to itself is zero. -/
theorem codewordDist_self (n : Nibble) :
    codewordDist (Spec.ofNibble n) (Spec.ofNibble n) = 0 := by
  fin_cases n <;> decide

/-- flipAt applied twice at the same index is the identity. -/
theorem flipAt_flipAt_eq (n : Nibble) (idx : Fin 7) :
    Spec.flipAt (Spec.flipAt (Spec.ofNibble n) idx) idx = Spec.ofNibble n := by
  fin_cases n <;> fin_cases idx <;> decide

/-- Flipping any bit in a valid codeword makes the syndrome nonzero. -/
theorem syndrome_flipAt_ne_zero (n : Nibble) (idx : Fin 7) :
    Spec.syndrome (Spec.flipAt (Spec.ofNibble n) idx) ≠ 0 := by
  fin_cases n <;> fin_cases idx <;> decide

/-- bitVal is bounded by 1. -/
theorem bitVal_le_one (b : Bool) : Spec.bitVal b ≤ 1 := by
  cases b <;> simp [Spec.bitVal]

end Radix.ECC
