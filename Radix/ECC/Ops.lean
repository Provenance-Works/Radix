/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.ECC.Spec

/-!
# Error Correction Operations (Layer 2)

Executable parity and Hamming(7,4) helpers.
-/

set_option autoImplicit false

namespace Radix.ECC

abbrev Nibble := Spec.Nibble
abbrev Codeword74 := Spec.Codeword74

/-- The observable status of a received Hamming(7,4) word. -/
inductive Status where
  | clean
  | corrected (idx : Fin 7)
  deriving DecidableEq, Repr

/-- Low-level codewords are stored in the low seven bits of a byte. -/
def isCodewordByte (b : UInt8) : Bool :=
  b.toNat < 0x80

/-- Pack a codeword into the low 7 bits of a `UInt8`. -/
def toByte (c : Codeword74) : UInt8 :=
  let value :=
    Spec.bitVal c.p1 +
    2 * Spec.bitVal c.p2 +
    4 * Spec.bitVal c.d0 +
    8 * Spec.bitVal c.p4 +
    16 * Spec.bitVal c.d1 +
    32 * Spec.bitVal c.d2 +
    64 * Spec.bitVal c.d3
  value.toUInt8

/-- Unpack a low-7-bit encoded value into a structured codeword. -/
def fromByteUnchecked (b : UInt8) : Codeword74 :=
  let n := b.toNat
  { p1 := n % 2 = 1
  , p2 := (n / 2) % 2 = 1
  , d0 := (n / 4) % 2 = 1
  , p4 := (n / 8) % 2 = 1
  , d1 := (n / 16) % 2 = 1
  , d2 := (n / 32) % 2 = 1
  , d3 := (n / 64) % 2 = 1
  }

/-- Unpack a valid low-7-bit encoded value into a structured codeword. -/
def fromByte? (b : UInt8) : Option Codeword74 :=
  if isCodewordByte b then
    some (fromByteUnchecked b)
  else
    none

/-- Encode a 4-bit nibble into a Hamming(7,4) codeword. -/
def encodeNibble (n : Nibble) : UInt8 :=
  toByte (Spec.ofNibble n)

/-- Encode an arbitrary byte if its high bits are zero. -/
def encodeByte? (b : UInt8) : Option UInt8 :=
  if h : b.toNat < 16 then
    some (encodeNibble ⟨b.toNat, h⟩)
  else
    none

/-- Decode a parity-valid Hamming(7,4) codeword into the represented nibble. -/
def decode (b : UInt8) : Option UInt8 :=
  match fromByte? b with
  | some codeword =>
    if Spec.syndrome codeword == 0 then
      some (Spec.toNibble codeword).val.toUInt8
    else
      none
  | none =>
    none

/-- Compute the Hamming syndrome for a received codeword. -/
def syndrome (b : UInt8) : Option Nat :=
  (fromByte? b).map Spec.syndrome

/-- Recover the bit position indicated by the syndrome, if any. -/
def errorIndex? (b : UInt8) : Option (Fin 7) :=
  (fromByte? b).bind Radix.ECC.Spec.errorIndex?

/-- Check whether the received codeword satisfies all parity equations. -/
def check (b : UInt8) : Bool :=
  match syndrome b with
  | some s => s == 0
  | none => false

/-- Classify whether a codeword is already clean or requires a single-bit correction. -/
def status? (b : UInt8) : Option Status :=
  match fromByte? b with
  | none => none
  | some codeword =>
  some <| match Radix.ECC.Spec.errorIndex? codeword with
      | none => .clean
      | some idx => .corrected idx

/-- Correct a single-bit error in a received codeword. -/
def correct (b : UInt8) : Option UInt8 :=
  (fromByte? b).map fun codeword =>
    toByte (Spec.correct codeword)

/-- Decode a codeword after applying single-bit correction when possible. -/
def decodeAfterCorrect (b : UInt8) : Option UInt8 :=
  (correct b).bind decode

/-- Compute even parity over the low `width` bits. -/
def evenParity (b : UInt8) (width : Nat := 8) : Bool :=
  Spec.evenParity b.toNat width

-- ════════════════════════════════════════════════════════════════════
-- Hamming Weight / Distance (executable)
-- ════════════════════════════════════════════════════════════════════

/-- Hamming weight (popcount) of a byte's low `width` bits. -/
def popcount (b : UInt8) (width : Nat := 8) : Nat :=
  (List.range width).foldl (fun acc i => acc + if (b.toNat / (2 ^ i)) % 2 = 1 then 1 else 0) 0

/-- Hamming distance between two bytes (in their low `width` bits). -/
def byteHammingDist (a b : UInt8) (width : Nat := 8) : Nat :=
  popcount (a ^^^ b) width

/-- Convert a `Codeword74` to a list of its seven bits. -/
def toBitList (c : Codeword74) : List Bool := Spec.toBitList c

/-- Hamming weight of a codeword (number of set bits). -/
def codewordWeight (c : Codeword74) : Nat := Spec.codewordWeight c

/-- Hamming distance between two codewords. -/
def codewordDist (c1 c2 : Codeword74) : Nat := Spec.codewordDist c1 c2

-- ════════════════════════════════════════════════════════════════════
-- SECDED Operations
-- ════════════════════════════════════════════════════════════════════

/-- SECDED error classification result. -/
abbrev SECDEDResult := Spec.SECDEDResult

/-- Encode a nibble as a SECDED codeword (8-bit). -/
def encodeNibbleSECDED (n : Nibble) : Spec.Codeword84 :=
  Spec.ofNibbleSECDED n

/-- Classify a SECDED codeword's error status. -/
def classifySECDED (c : Spec.Codeword84) : SECDEDResult :=
  Spec.classifySECDED c

/-- Correct a SECDED codeword if possible. -/
def correctSECDED (c : Spec.Codeword84) : Option Spec.Codeword84 :=
  Spec.correctSECDED c

-- ════════════════════════════════════════════════════════════════════
-- Batch Operations
-- ════════════════════════════════════════════════════════════════════

/-- Encode a list of nibbles into their Hamming(7,4) byte representations. -/
def encodeNibbles (ns : List Nibble) : List UInt8 :=
  ns.map encodeNibble

/-- Decode a list of encoded bytes back to nibble values. -/
def decodeNibbles (bs : List UInt8) : List (Option UInt8) :=
  bs.map decode

/-- Correct a list of received codeword bytes. -/
def correctAll (bs : List UInt8) : List (Option UInt8) :=
  bs.map correct

/-- Decode all bytes after applying correction. -/
def decodeAllAfterCorrect (bs : List UInt8) : List (Option UInt8) :=
  bs.map decodeAfterCorrect

/-- Count the number of error-free codewords in a list. -/
def countClean (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => acc + if check b then 1 else 0) 0

/-- Count the number of corrected codewords in a list. -/
def countCorrected (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b =>
    acc + match status? b with
          | some (.corrected _) => 1
          | _ => 0) 0

/-- Compute error rate as (errors, total) pair. -/
def errorRate (bs : List UInt8) : Nat × Nat :=
  let total := bs.length
  let clean := countClean bs
  (total - clean, total)

-- ════════════════════════════════════════════════════════════════════
-- Hamming(15,11) Operations
-- ════════════════════════════════════════════════════════════════════

abbrev Word11 := Spec.Word11
abbrev Codeword1511 := Spec.Codeword1511

/-- Encode an 11-bit word to a Hamming(15,11) codeword. -/
def encode1511 (w : Word11) : Codeword1511 :=
  Spec.Codeword1511.encode w

/-- Decode a Hamming(15,11) codeword to the 11-bit data word. -/
def decode1511 (c : Codeword1511) : Word11 :=
  Spec.Codeword1511.decode c

/-- Compute the syndrome of a Hamming(15,11) codeword. -/
def syndrome1511 (c : Codeword1511) : Fin 16 :=
  Spec.Codeword1511.syndrome c

/-- Correct a single-bit error in a Hamming(15,11) codeword. -/
def correct1511 (c : Codeword1511) : Codeword1511 :=
  Spec.Codeword1511.correct c

/-- Encode, transmit, correct, and decode a Hamming(15,11) word. -/
def roundtrip1511 (w : Word11) (corrupt : Codeword1511 → Codeword1511 := id) : Word11 :=
  decode1511 (correct1511 (corrupt (encode1511 w)))

/-- Pack a Hamming(15,11) codeword into a UInt16 (low 15 bits). -/
def toUInt16 (c : Codeword1511) : UInt16 :=
  c.bits.val.toUInt16

/-- Unpack a UInt16 (low 15 bits) into a Hamming(15,11) codeword. -/
def fromUInt16 (v : UInt16) : Codeword1511 :=
  ⟨⟨v.toNat % 32768, by omega⟩⟩

/-- Encode a list of 11-bit words into Hamming(15,11) codewords. -/
def encodeWords (ws : List Word11) : List Codeword1511 :=
  ws.map encode1511

/-- Decode a list of Hamming(15,11) codewords. -/
def decodeWords (cs : List Codeword1511) : List Word11 :=
  cs.map decode1511

/-- Correct and decode a list of Hamming(15,11) codewords. -/
def correctAndDecodeWords (cs : List Codeword1511) : List Word11 :=
  cs.map (fun c => decode1511 (correct1511 c))

-- ════════════════════════════════════════════════════════════════════
-- SECDED Batch Operations
-- ════════════════════════════════════════════════════════════════════

/-- Encode a list of nibbles as SECDED codewords. -/
def encodeSECDED (ns : List Nibble) : List Spec.Codeword84 :=
  ns.map encodeNibbleSECDED

/-- Classify errors for a list of SECDED codewords. -/
def classifyAllSECDED (cs : List Spec.Codeword84) : List SECDEDResult :=
  cs.map classifySECDED

/-- Count double errors detected in a list of SECDED codewords. -/
def countDoubleErrors (cs : List Spec.Codeword84) : Nat :=
  cs.foldl (fun acc c =>
    acc + if classifySECDED c == .doubleError then 1 else 0) 0

end Radix.ECC
