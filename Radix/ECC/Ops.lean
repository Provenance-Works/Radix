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

/-- Decode a Hamming(7,4) codeword into the represented nibble. -/
def decode (b : UInt8) : Option UInt8 :=
  (fromByte? b).map fun codeword =>
    (Spec.toNibble codeword).val.toUInt8

/-- Compute the Hamming syndrome for a received codeword. -/
def syndrome (b : UInt8) : Option Nat :=
  (fromByte? b).map Spec.syndrome

/-- Check whether the received codeword satisfies all parity equations. -/
def check (b : UInt8) : Bool :=
  match syndrome b with
  | some s => s == 0
  | none => false

/-- Correct a single-bit error in a received codeword. -/
def correct (b : UInt8) : Option UInt8 :=
  (fromByte? b).map fun codeword =>
    toByte (Spec.correct codeword)

/-- Compute even parity over the low `width` bits. -/
def evenParity (b : UInt8) (width : Nat := 8) : Bool :=
  Spec.evenParity b.toNat width

end Radix.ECC
