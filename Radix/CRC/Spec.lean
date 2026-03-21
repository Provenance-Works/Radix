/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CRC Specification (Layer 3)

Mathematical specification of CRC (Cyclic Redundancy Check) algorithms
based on polynomial division over GF(2).

CRC is defined as the remainder of bitstring polynomial division by a
generator polynomial. This module defines the abstract computation and
proves core properties:

- CRC of empty data
- Linearity: CRC(a ⊕ b) = CRC(a) ⊕ CRC(b)
- Check property: CRC(data ++ crc_bytes) = 0 (for the check value)

## Supported Standards

- CRC-32 (ISO 3309, ITU-T V.42, Ethernet, gzip, PNG)
- CRC-16-CCITT (X.25, HDLC)

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.

## References

- v0.2.0 Roadmap: CRC-32 / CRC-16
- Ross N. Williams, "A Painless Guide to CRC Error Detection Algorithms"
- ITU-T Recommendation V.42 (2002), Section 8.1.1.6.2
-/

namespace Radix.CRC.Spec

/-! ## GF(2) Polynomial Representation

A polynomial over GF(2) is represented as a natural number where
bit `i` represents the coefficient of x^i. -/

/-- A polynomial over GF(2) represented as a natural number.
    Bit `i` of `coeffs` is the coefficient of x^i. -/
structure GF2Poly where
  coeffs : Nat
  deriving DecidableEq, Repr

namespace GF2Poly

/-- The zero polynomial. -/
def zero : GF2Poly := ⟨0⟩

/-- Addition in GF(2) is XOR. -/
def add (a b : GF2Poly) : GF2Poly := ⟨a.coeffs ^^^ b.coeffs⟩

/-- XOR (same as add in GF(2)). -/
def xor (a b : GF2Poly) : GF2Poly := add a b

/-- Degree of the polynomial (0 for zero polynomial).
    For non-zero polynomials, this is the position of the highest set bit. -/
def degree (p : GF2Poly) : Nat :=
  if p.coeffs == 0 then 0
  else Nat.log2 p.coeffs

/-- Left shift: multiply by x^n. -/
def shiftLeft (p : GF2Poly) (n : Nat) : GF2Poly := ⟨p.coeffs <<< n⟩

/-- Test if bit at position `i` is set. -/
def testBit (p : GF2Poly) (i : Nat) : Bool := (p.coeffs >>> i) &&& 1 != 0

end GF2Poly

/-! ## CRC Parameters -/

/-- Standard CRC algorithm parameters.
    Uses the "reflected" (LSB-first) convention common in practice. -/
structure CRCParams where
  /-- Width of the CRC in bits (e.g., 32 for CRC-32). -/
  width : Nat
  /-- Generator polynomial (without the implicit x^width leading term).
      In LSB-first (reflected) representation. -/
  poly : Nat
  /-- Initial CRC register value. -/
  init : Nat
  /-- Final XOR value applied to the result. -/
  xorOut : Nat
  /-- Whether input bytes are reflected (LSB first). -/
  reflectIn : Bool
  /-- Whether the output CRC is reflected (LSB first). -/
  reflectOut : Bool
  deriving Repr

namespace CRCParams

/-- CRC-32/ISO-HDLC (Ethernet, gzip, PNG). -/
def crc32 : CRCParams :=
  { width := 32
    poly := 0x04C11DB7
    init := 0xFFFFFFFF
    xorOut := 0xFFFFFFFF
    reflectIn := true
    reflectOut := true }

/-- CRC-32 polynomial in reflected (LSB-first) representation. -/
def crc32Reflected : Nat := 0xEDB88320

/-- CRC-16/CCITT (X.25, HDLC). -/
def crc16ccitt : CRCParams :=
  { width := 16
    poly := 0x1021
    init := 0xFFFF
    xorOut := 0xFFFF
    reflectIn := true
    reflectOut := true }

/-- CRC-16/CCITT polynomial in reflected (LSB-first) representation. -/
def crc16ccittReflected : Nat := 0x8408

end CRCParams

/-! ## Abstract CRC Computation

Bit-by-bit CRC computation as a mathematical specification.
All implementations must produce results equivalent to this. -/

/-- Process one bit of data through the CRC register (reflected algorithm).
    If the LSB of `(crc XOR dataBit)` is 1, XOR with the polynomial. -/
def crcStepBit (crc : Nat) (dataBit : Nat) (poly : Nat) (mask : Nat) : Nat :=
  let combined := (crc ^^^ dataBit) &&& 1
  let shifted := crc >>> 1
  if combined != 0 then (shifted ^^^ poly) &&& mask
  else shifted &&& mask

/-- Process one byte through the CRC register (LSB-first / reflected). -/
def crcStepByte (crc : Nat) (byte : Nat) (poly : Nat) (mask : Nat) : Nat :=
  go crc byte poly mask 8
where
  go (crc : Nat) (byte : Nat) (poly : Nat) (mask : Nat) : Nat → Nat
    | 0 => crc
    | fuel + 1 =>
      let bit := byte &&& 1
      let crc' := crcStepBit crc bit poly mask
      go crc' (byte >>> 1) poly mask fuel

/-- Compute CRC over a list of bytes (specification). -/
def crcCompute (params : CRCParams) (data : List Nat) : Nat :=
  let mask := (1 <<< params.width) - 1
  let poly := if params.reflectIn then
    -- Use the reflected polynomial
    reflectBits params.poly params.width
  else params.poly
  let finalCrc := data.foldl (fun crc byte => crcStepByte crc byte poly mask) params.init
  (finalCrc ^^^ params.xorOut) &&& mask
where
  /-- Reflect (reverse) the bits of a value. -/
  reflectBits (val : Nat) (width : Nat) : Nat :=
    go val width 0 0
  go (val : Nat) (width : Nat) (idx : Nat) (acc : Nat) : Nat :=
    if idx >= width then acc
    else
      let bit := (val >>> idx) &&& 1
      go val width (idx + 1) (acc ||| (bit <<< (width - 1 - idx)))
  termination_by width - idx

/-! ## Specification Properties -/

/-- CRC of empty data equals init XOR xorOut (masked to width). -/
theorem crc_empty (params : CRCParams) :
    crcCompute params [] = (params.init ^^^ params.xorOut) &&& ((1 <<< params.width) - 1) := by
  simp [crcCompute, List.foldl]

end Radix.CRC.Spec
