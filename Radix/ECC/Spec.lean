/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
# Error Correction Specification (Layer 3)

Formal parity and Hamming(7,4) coding primitives.

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- v0.3.0 Roadmap: Error Correction Codes
- Hamming, R. W. (1950), Error Detecting and Error Correcting Codes
-/

set_option autoImplicit false

namespace Radix.ECC.Spec

/-- Four-bit data for Hamming(7,4). -/
abbrev Nibble := Fin 16

/-- A structured Hamming(7,4) codeword. -/
structure Codeword74 where
  p1 : Bool
  p2 : Bool
  d0 : Bool
  p4 : Bool
  d1 : Bool
  d2 : Bool
  d3 : Bool
  deriving DecidableEq, Repr

/-- Convert a `Bool` to a single-bit natural number. -/
def bitVal (b : Bool) : Nat :=
  if b then 1 else 0

/-- XOR as parity addition over booleans. -/
def xor3 (a b c : Bool) : Bool :=
  (bitVal a + bitVal b + bitVal c) % 2 = 1

/-- Extract the low four data bits into a nibble. -/
def toNibble (c : Codeword74) : Nibble := by
  refine ⟨bitVal c.d0 + 2 * bitVal c.d1 + 4 * bitVal c.d2 + 8 * bitVal c.d3, ?_⟩
  have hd0 : bitVal c.d0 ≤ 1 := by cases c.d0 <;> simp [bitVal]
  have hd1 : bitVal c.d1 ≤ 1 := by cases c.d1 <;> simp [bitVal]
  have hd2 : bitVal c.d2 ≤ 1 := by cases c.d2 <;> simp [bitVal]
  have hd3 : bitVal c.d3 ≤ 1 := by cases c.d3 <;> simp [bitVal]
  omega

/-- Build a Hamming(7,4) codeword from four data bits. -/
def ofNibble (n : Nibble) : Codeword74 :=
  let d0 := n.val % 2 = 1
  let d1 := (n.val / 2) % 2 = 1
  let d2 := (n.val / 4) % 2 = 1
  let d3 := (n.val / 8) % 2 = 1
  { p1 := xor3 d0 d1 d3
  , p2 := xor3 d0 d2 d3
  , d0 := d0
  , p4 := xor3 d1 d2 d3
  , d1 := d1
  , d2 := d2
  , d3 := d3
  }

/-- Syndrome bit for parity equation 1. -/
def syndrome1 (c : Codeword74) : Bool :=
  xor3 c.p1 c.d0 (c.d1 != c.d3)

/-- Syndrome bit for parity equation 2. -/
def syndrome2 (c : Codeword74) : Bool :=
  xor3 c.p2 c.d0 (c.d2 != c.d3)

/-- Syndrome bit for parity equation 4. -/
def syndrome4 (c : Codeword74) : Bool :=
  xor3 c.p4 c.d1 (c.d2 != c.d3)

/-- Syndrome value in the range `[0, 7]`. Zero means no detectable error. -/
def syndrome (c : Codeword74) : Nat :=
  bitVal (syndrome1 c) + 2 * bitVal (syndrome2 c) + 4 * bitVal (syndrome4 c)

/-- The corrected bit index indicated by the syndrome, if any. -/
def errorIndex? (c : Codeword74) : Option (Fin 7) :=
  let s := syndrome c
  if hs : s = 0 then
    none
  else
    some ⟨s - 1, by
      have hs1 : bitVal (syndrome1 c) ≤ 1 := by
        cases syndrome1 c <;> simp [bitVal]
      have hs2 : bitVal (syndrome2 c) ≤ 1 := by
        cases syndrome2 c <;> simp [bitVal]
      have hs4 : bitVal (syndrome4 c) ≤ 1 := by
        cases syndrome4 c <;> simp [bitVal]
      have hle : s ≤ 7 := by
        unfold s syndrome
        omega
      have hpos : 0 < s := by
        omega
      omega⟩

/-- Flip one of the seven Hamming(7,4) bits, addressed from 0 to 6. -/
def flipAt (c : Codeword74) (idx : Fin 7) : Codeword74 :=
  match idx.val with
  | 0 => { c with p1 := !c.p1 }
  | 1 => { c with p2 := !c.p2 }
  | 2 => { c with d0 := !c.d0 }
  | 3 => { c with p4 := !c.p4 }
  | 4 => { c with d1 := !c.d1 }
  | 5 => { c with d2 := !c.d2 }
  | _ => { c with d3 := !c.d3 }

/-- Correct a single-bit error, if present. -/
def correct (c : Codeword74) : Codeword74 :=
  match errorIndex? c with
  | none => c
  | some idx => flipAt c idx

/-- Parity bit for the low `width` bits of a natural number. -/
def evenParity (n width : Nat) : Bool :=
  ((List.range width).foldl (fun acc i => acc + ((n / (2 ^ i)) % 2)) 0) % 2 = 0

/-- Encoding followed by extraction recovers the original nibble. -/
theorem toNibble_ofNibble (n : Nibble) :
    toNibble (ofNibble n) = n := by
  fin_cases n <;> decide

/-- Correcting a single flipped bit recovers the original nibble. -/
theorem toNibble_correct_single_bit (n : Nibble) (idx : Fin 7) :
    toNibble (correct (flipAt (ofNibble n) idx)) = n := by
  fin_cases n <;> fin_cases idx <;> decide

/-- Error-index classification is empty exactly for clean codewords. -/
theorem errorIndex?_eq_none_iff_syndrome_zero (c : Codeword74) :
    errorIndex? c = none ↔ syndrome c = 0 := by
  unfold errorIndex?
  by_cases hs : syndrome c = 0 <;> simp [hs]

/-- A single flipped bit is classified at the flipped location. -/
theorem errorIndex?_flipAt_ofNibble (n : Nibble) (idx : Fin 7) :
    errorIndex? (flipAt (ofNibble n) idx) = some idx := by
  fin_cases n <;> fin_cases idx <;> decide

-- ════════════════════════════════════════════════════════════════════
-- Hamming Weight and Distance
-- ════════════════════════════════════════════════════════════════════

/-- Convert a `Codeword74` to a list of seven booleans (bit positions 1–7). -/
def toBitList (c : Codeword74) : List Bool :=
  [c.p1, c.p2, c.d0, c.p4, c.d1, c.d2, c.d3]

/-- Hamming weight (number of `true` bits) in a boolean list. -/
def hammingWeight (bits : List Bool) : Nat :=
  bits.foldl (fun acc b => acc + if b then 1 else 0) 0

/-- Hamming weight of a codeword. -/
def codewordWeight (c : Codeword74) : Nat :=
  hammingWeight (toBitList c)

/-- Hamming distance: number of bit positions where two lists differ. -/
def hammingDist (a b : List Bool) : Nat :=
  (a.zip b).foldl (fun acc (x, y) => acc + if x != y then 1 else 0) 0

/-- Hamming distance between two codewords. -/
def codewordDist (c1 c2 : Codeword74) : Nat :=
  hammingDist (toBitList c1) (toBitList c2)

/-- The all-zero codeword (encoding of nibble 0). -/
def zeroCW : Codeword74 := ofNibble 0

-- ════════════════════════════════════════════════════════════════════
-- SECDED: Single Error Correction, Double Error Detection
-- Extends Hamming(7,4) with an overall parity bit → Hamming(8,4)
-- ════════════════════════════════════════════════════════════════════

/-- A SECDED codeword: Hamming(7,4) plus an overall parity bit. -/
structure Codeword84 where
  inner : Codeword74
  overallParity : Bool
  deriving DecidableEq, Repr

/-- Build a SECDED codeword from a nibble (adds overall parity). -/
def ofNibbleSECDED (n : Nibble) : Codeword84 :=
  let cw := ofNibble n
  let bits := toBitList cw
  let parityBit := hammingWeight bits % 2 = 1
  { inner := cw, overallParity := parityBit }

/-- Overall parity of a SECDED codeword (all 8 bits including parity bit). -/
def overallParityCheck (c : Codeword84) : Bool :=
  (hammingWeight (toBitList c.inner) + if c.overallParity then 1 else 0) % 2 = 0

/-- SECDED error detection result. -/
inductive SECDEDResult where
  | noError       : SECDEDResult  -- syndrome=0, parity OK
  | singleError   : Fin 7 → SECDEDResult  -- syndrome≠0, parity bad → correctable
  | doubleError   : SECDEDResult  -- syndrome≠0, parity OK → detected but uncorrectable
  | parityOnly    : SECDEDResult  -- syndrome=0, parity bad → parity bit itself flipped
  deriving DecidableEq, Repr

/-- Classify a SECDED codeword's error status. -/
def classifySECDED (c : Codeword84) : SECDEDResult :=
  let s := syndrome c.inner
  let pOK := overallParityCheck c
  match s == 0, pOK with
  | true,  true  => .noError
  | false, false => match errorIndex? c.inner with
                     | some idx => .singleError idx
                     | none     => .noError  -- shouldn't happen if syndrome ≠ 0
  | false, true  => .doubleError
  | true,  false => .parityOnly

/-- Correct a SECDED codeword if a single-bit error is detected. -/
def correctSECDED (c : Codeword84) : Option Codeword84 :=
  match classifySECDED c with
  | .noError => some c
  | .singleError idx =>
    let correctedInner := flipAt c.inner idx
    some { inner := correctedInner, overallParity := !c.overallParity }
  | .doubleError => none  -- detected but uncorrectable
  | .parityOnly => some { c with overallParity := !c.overallParity }

-- ════════════════════════════════════════════════════════════════════
-- Generator and Parity-Check Matrix (as lists of bit vectors)
-- ════════════════════════════════════════════════════════════════════

/-- The 4×7 generator matrix G for Hamming(7,4) in systematic form.
    Each row encodes one data bit position. Rows represent d0, d1, d2, d3. -/
def generatorMatrix : List (List Bool) :=
  [ [true,  true,  true,  false, false, false, false]  -- d0 → p1, p2, d0
  , [true,  false, false, true,  true,  false, false]  -- d1 → p1, p4, d1
  , [false, true,  false, true,  false, true,  false]  -- d2 → p2, p4, d2
  , [true,  true,  false, true,  false, false, true]   -- d3 → p1, p2, p4, d3
  ]

/-- The 3×7 parity-check matrix H for Hamming(7,4).
    Each row represents one syndrome equation. -/
def parityCheckMatrix : List (List Bool) :=
  [ [true,  false, true,  false, true,  false, true ]  -- positions 1,3,5,7
  , [false, true,  true,  false, false, true,  true ]  -- positions 2,3,6,7
  , [false, false, false, true,  true,  true,  true ]  -- positions 4,5,6,7
  ]

-- ════════════════════════════════════════════════════════════════════
-- Additional Theorems
-- ════════════════════════════════════════════════════════════════════

/-- Encoding and extracting data recovers the nibble (already above),
    repeated here for completeness as a `Prop`. -/
theorem roundtrip_ofNibble_toNibble (n : Nibble) :
    toNibble (ofNibble n) = n := toNibble_ofNibble n

/-- Syndrome of a freshly encoded codeword is always zero. -/
theorem syndrome_ofNibble (n : Nibble) :
    syndrome (ofNibble n) = 0 := by
  fin_cases n <;> decide

/-- A freshly encoded codeword needs no correction. -/
theorem errorIndex?_ofNibble (n : Nibble) :
    errorIndex? (ofNibble n) = none := by
  fin_cases n <;> decide

/-- Flipping the same bit twice recovers the original codeword. -/
theorem flipAt_flipAt_cancel (c : Codeword74) (idx : Fin 7) :
    flipAt (flipAt c idx) idx = c := by
  fin_cases idx <;> simp [flipAt, Bool.not_not]

/-- The zero codeword has weight 0. -/
theorem weight_zeroCW : codewordWeight zeroCW = 0 := by decide

/-- Distance from any codeword to itself is 0. -/
theorem dist_self (c : Codeword74) : codewordDist c c = 0 := by
  simp [codewordDist, hammingDist, toBitList]

set_option maxHeartbeats 800000 in
/-- Hamming(7,4) has minimum distance 3: every distinct pair of valid codewords
    differs in at least 3 bit positions. -/
theorem min_distance_3 (n1 n2 : Nibble) (hne : n1 ≠ n2) :
    3 ≤ codewordDist (ofNibble n1) (ofNibble n2) := by
  fin_cases n1 <;> fin_cases n2 <;> simp_all [codewordDist, hammingDist, toBitList,
    ofNibble, xor3, bitVal]

/-- Hamming weight of a valid codeword is either 0, 3, 4, or 7. -/
theorem valid_weight_values (n : Nibble) :
    codewordWeight (ofNibble n) ∈ ({0, 3, 4, 7} : Finset Nat) := by
  fin_cases n <;> decide

/-- SECDED freshly encoded codewords are classified as noError. -/
theorem classifySECDED_fresh (n : Nibble) :
    classifySECDED (ofNibbleSECDED n) = .noError := by
  fin_cases n <;> decide

/-- SECDED overall parity check passes for freshly encoded codewords. -/
theorem overallParityCheck_fresh (n : Nibble) :
    overallParityCheck (ofNibbleSECDED n) = true := by
  fin_cases n <;> decide

/-- XOR associativity for three booleans. -/
theorem xor_assoc (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- XOR commutativity. -/
theorem xor_comm (a b : Bool) : xor a b = xor b a := by
  cases a <;> cases b <;> decide

/-- XOR with false is identity. -/
theorem xor_false (a : Bool) : xor a false = a := by
  cases a <;> decide

/-- XOR with self is false. -/
theorem xor_self (a : Bool) : xor a a = false := by
  cases a <;> decide

/-- bitVal is bounded by 1. -/
theorem bitVal_le_one (b : Bool) : bitVal b ≤ 1 := by
  cases b <;> simp [bitVal]

/-- Even parity of 0 over any width is true. -/
theorem evenParity_zero (w : Nat) : evenParity 0 w = true := by
  simp [evenParity]

/-- The toBitList of a codeword always has length 7. -/
theorem toBitList_length (c : Codeword74) : (toBitList c).length = 7 := by
  simp [toBitList]

-- ════════════════════════════════════════════════════════════════════
-- Syndrome Properties
-- ════════════════════════════════════════════════════════════════════

/-- Syndrome is bounded by 7 (3-bit value). -/
theorem syndrome_le_7 (c : Codeword74) : syndrome c ≤ 7 := by
  unfold syndrome
  have h1 : bitVal (syndrome1 c) ≤ 1 := bitVal_le_one _
  have h2 : bitVal (syndrome2 c) ≤ 1 := bitVal_le_one _
  have h4 : bitVal (syndrome4 c) ≤ 1 := bitVal_le_one _
  omega

/-- Correct always produces a codeword with syndrome zero. -/
theorem syndrome_correct (n : Nibble) (idx : Fin 7) :
    syndrome (correct (flipAt (ofNibble n) idx)) = 0 := by
  fin_cases n <;> fin_cases idx <;> decide

/-- Syndrome of double-flipped codeword (same bit) is zero. -/
theorem syndrome_double_flip (n : Nibble) (idx : Fin 7) :
    syndrome (flipAt (flipAt (ofNibble n) idx) idx) = 0 := by
  fin_cases n <;> fin_cases idx <;> decide

-- ════════════════════════════════════════════════════════════════════
-- Hamming Distance Properties
-- ════════════════════════════════════════════════════════════════════

/-- Hamming distance between valid codewords is symmetric. -/
theorem codewordDist_comm (n1 n2 : Nibble) :
    codewordDist (ofNibble n1) (ofNibble n2) =
    codewordDist (ofNibble n2) (ofNibble n1) := by
  fin_cases n1 <;> fin_cases n2 <;> decide

/-- Hamming distance from a codeword to itself is always zero. -/
theorem codewordDist_self_any (c : Codeword74) : codewordDist c c = 0 :=
  dist_self c

/-- Codeword weight of allFalse (0x00) is 0. -/
theorem weight_allFalse :
    codewordWeight { p1 := false, p2 := false, d0 := false, p4 := false,
                     d1 := false, d2 := false, d3 := false } = 0 := by decide

/-- Codeword weight of allTrue (0x7F) is 7. -/
theorem weight_allTrue :
    codewordWeight { p1 := true, p2 := true, d0 := true, p4 := true,
                     d1 := true, d2 := true, d3 := true } = 7 := by decide

-- ════════════════════════════════════════════════════════════════════
-- SECDED Extended Properties
-- ════════════════════════════════════════════════════════════════════

/-- SECDED correction recovers original data for single-bit inner errors. -/
theorem correctSECDED_single_inner (n : Nibble) (idx : Fin 7) :
    ∃ c', correctSECDED
      { inner := flipAt (ofNibble n) idx
        overallParity := (ofNibbleSECDED n).overallParity } = some c' ∧
      toNibble c'.inner = n := by
  fin_cases n <;> fin_cases idx <;> decide

/-- SECDED detects double-bit errors (adjacent bits 0 and 1). -/
theorem classifySECDED_double_error_01 (n : Nibble) :
    classifySECDED
      { inner := flipAt (flipAt (ofNibble n) 0) 1
        overallParity := (ofNibbleSECDED n).overallParity } = .doubleError := by
  fin_cases n <;> decide

/-- Generator matrix has exactly 4 rows. -/
theorem generatorMatrix_rows : generatorMatrix.length = 4 := by decide

/-- Parity-check matrix has exactly 3 rows. -/
theorem parityCheckMatrix_rows : parityCheckMatrix.length = 3 := by decide

/-- Each row of the generator matrix has 7 columns. -/
theorem generatorMatrix_cols :
    ∀ row ∈ generatorMatrix, row.length = 7 := by decide

/-- Each row of the parity-check matrix has 7 columns. -/
theorem parityCheckMatrix_cols :
    ∀ row ∈ parityCheckMatrix, row.length = 7 := by decide

end Radix.ECC.Spec
