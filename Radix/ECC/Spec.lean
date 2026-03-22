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
  match syndrome c with
  | 0 => c
  | 1 => flipAt c ⟨0, by decide⟩
  | 2 => flipAt c ⟨1, by decide⟩
  | 3 => flipAt c ⟨2, by decide⟩
  | 4 => flipAt c ⟨3, by decide⟩
  | 5 => flipAt c ⟨4, by decide⟩
  | 6 => flipAt c ⟨5, by decide⟩
  | _ => flipAt c ⟨6, by decide⟩

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

end Radix.ECC.Spec
