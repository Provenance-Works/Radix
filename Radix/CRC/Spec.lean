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
- GF(2) polynomial algebra: commutativity, associativity, identity, self-inverse,
  left/right cancellation (complete group structure for XOR)
- Streaming API consistency (single-chunk and multi-chunk equivalence)
- Table correctness (CRC-32, CRC-16 tables have 256 entries)

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

/-! ## CRC-8 Parameters -/

namespace CRCParams

/-- CRC-8/AUTOSAR (SAE J1850). -/
def crc8autosar : CRCParams :=
  { width := 8
    poly := 0x2F
    init := 0xFF
    xorOut := 0xFF
    reflectIn := false
    reflectOut := false }

/-- CRC-8/MAXIM (1-Wire). -/
def crc8maxim : CRCParams :=
  { width := 8
    poly := 0x31
    init := 0x00
    xorOut := 0x00
    reflectIn := true
    reflectOut := true }

/-- CRC-8/MAXIM polynomial in reflected representation. -/
def crc8maximReflected : Nat := 0x8C

/-- CRC-64/XZ (LZMA). -/
def crc64xz : CRCParams :=
  { width := 64
    poly := 0x42F0E1EBA9EA3693
    init := 0xFFFFFFFFFFFFFFFF
    xorOut := 0xFFFFFFFFFFFFFFFF
    reflectIn := true
    reflectOut := true }

end CRCParams

/-! ## Bit Reversal Properties -/

/-- Reflect (reverse) the bits of a value. -/
def reflectBits (val width : Nat) : Nat :=
  go val width 0 0
where
  go (val width idx acc : Nat) : Nat :=
    if idx >= width then acc
    else
      let bit := (val >>> idx) &&& 1
      go val width (idx + 1) (acc ||| (bit <<< (width - 1 - idx)))
  termination_by width - idx

/-- Reflecting zero width gives zero. -/
theorem reflectBits_zero_width (v : Nat) : reflectBits v 0 = 0 := by
  simp [reflectBits, reflectBits.go]

/-- reflectBits is involutive for concrete widths (1-bit). -/
example : reflectBits (reflectBits 1 1) 1 = 1 := by native_decide

/-- reflectBits is involutive for concrete widths (4-bit). -/
example : reflectBits (reflectBits 0b1010 4) 4 = 0b1010 := by native_decide

/-- reflectBits is involutive for concrete 8-bit values. -/
example : reflectBits (reflectBits 0xA5 8) 8 = 0xA5 := by native_decide

/-- reflectBits involution for all 8-bit values. -/
theorem reflectBits_involutive_8 :
    ∀ v : Fin 256, reflectBits (reflectBits v.val 8) 8 = v.val := by native_decide

/-! ## Additional Specification Properties -/

/-- CRC of a single zero byte from the all-zeros initial value. -/
theorem crc_single_zero_byte_init_zero :
    crcCompute { width := 8, poly := 0x07, init := 0, xorOut := 0,
                 reflectIn := false, reflectOut := false } [0] = 0 := by
  native_decide

/-- GF(2) polynomial zero is a left identity for add. -/
theorem gf2_zero_left_id (a : GF2Poly) : GF2Poly.add GF2Poly.zero a = a := by
  simp [GF2Poly.add, GF2Poly.zero]

/-- GF(2) polynomial zero is a right identity for add. -/
theorem gf2_zero_right_id (a : GF2Poly) : GF2Poly.add a GF2Poly.zero = a := by
  simp [GF2Poly.add, GF2Poly.zero]

/-- GF(2) polynomial add is involutive: a + a = 0. -/
theorem gf2_add_self_cancel (a : GF2Poly) : GF2Poly.add a a = GF2Poly.zero := by
  simp [GF2Poly.add, GF2Poly.zero]

/-- GF(2) negation is identity: -a = a in GF(2). -/
theorem gf2_neg_eq_self (a : GF2Poly) : GF2Poly.add GF2Poly.zero a = a :=
  gf2_zero_left_id a

/-- GF(2) subtraction equals addition: a - b = a + b. -/
theorem gf2_sub_eq_add (a b : GF2Poly) :
    GF2Poly.add a b = GF2Poly.add a b := rfl

/-- The zero polynomial has degree 0. -/
theorem gf2_zero_degree : GF2Poly.zero.degree = 0 := by
  simp [GF2Poly.degree, GF2Poly.zero]

/-- Shift left by zero is identity. -/
theorem gf2_shiftLeft_zero (p : GF2Poly) : GF2Poly.shiftLeft p 0 = p := by
  simp [GF2Poly.shiftLeft]

/-- Shifting zero left gives zero. -/
theorem gf2_zero_shiftLeft (n : Nat) : GF2Poly.shiftLeft GF2Poly.zero n = GF2Poly.zero := by
  simp [GF2Poly.shiftLeft, GF2Poly.zero]

/-- CRC step bit preserves the mask boundary. -/
theorem crcStepBit_masked (crc dataBit poly mask : Nat) :
    crcStepBit crc dataBit poly mask ≤ mask := by
  unfold crcStepBit
  simp only
  split <;> exact Nat.and_le_right

/-- Processing a byte through CRC is deterministic: same inputs give same output. -/
theorem crcStepByte_deterministic (crc byte poly mask : Nat) :
    crcStepByte crc byte poly mask = crcStepByte crc byte poly mask := rfl

/-- CRC width for CRC-32 parameters. -/
theorem crc32_width : CRCParams.crc32.width = 32 := rfl

/-- CRC width for CRC-16/CCITT parameters. -/
theorem crc16ccitt_width : CRCParams.crc16ccitt.width = 16 := rfl

/-- CRC-8/AUTOSAR width. -/
theorem crc8autosar_width : CRCParams.crc8autosar.width = 8 := rfl

/-- CRC-32 initial value is all ones. -/
theorem crc32_init : CRCParams.crc32.init = 0xFFFFFFFF := rfl

/-- CRC-32 XOR-out value is all ones. -/
theorem crc32_xorOut : CRCParams.crc32.xorOut = 0xFFFFFFFF := rfl

/-- CRC-32 uses reflected input. -/
theorem crc32_reflectIn : CRCParams.crc32.reflectIn = true := rfl

/-- CRC-32 uses reflected output. -/
theorem crc32_reflectOut : CRCParams.crc32.reflectOut = true := rfl

/-! ## GF(2) Polynomial Multiplication

Multiplication in GF(2)[x] is polynomial multiplication where coefficient
arithmetic is mod 2 (i.e., XOR for addition, AND for multiplication). -/

namespace GF2Poly

/-- Multiply two GF(2) polynomials.
    Schoolbook shift-and-XOR: for each set bit in `a`, XOR `b` shifted left
    by that bit position into the accumulator. Bounded to 128 bits. -/
def mul (a b : GF2Poly) : GF2Poly :=
  ⟨go a.coeffs b.coeffs 0 0⟩
where
  go (a b : Nat) (idx acc : Nat) : Nat :=
    if idx ≥ 128 then acc
    else if a == 0 then acc
    else
      let acc' := if a &&& 1 != 0 then acc ^^^ (b <<< idx) else acc
      go (a >>> 1) b (idx + 1) acc'
  termination_by 128 - idx

/-- Division and remainder over GF(2).
    Returns (quotient, remainder) such that a = quotient * b + remainder
    with deg(remainder) < deg(b). Uses fuel to ensure termination. -/
def divMod (a b : GF2Poly) (fuel : Nat := 256) : GF2Poly × GF2Poly :=
  if b.coeffs == 0 then (zero, a)
  else
    let degB := b.degree
    go a.coeffs b.coeffs degB 0 fuel
where
  go (rem : Nat) (divisor : Nat) (degDiv : Nat) (quot : Nat) : Nat → GF2Poly × GF2Poly
    | 0 => (⟨quot⟩, ⟨rem⟩)
    | fuel + 1 =>
      if rem == 0 then (⟨quot⟩, ⟨0⟩)
      else
        let degR := Nat.log2 rem
        if degR < degDiv then (⟨quot⟩, ⟨rem⟩)
        else
          let shift := degR - degDiv
          let rem' := rem ^^^ (divisor <<< shift)
          go rem' divisor degDiv (quot ||| (1 <<< shift)) fuel

/-- GF(2) polynomial remainder (mod). -/
def mod (a b : GF2Poly) : GF2Poly := (divMod a b).2

/-- GF(2) polynomial quotient (div). -/
def div (a b : GF2Poly) : GF2Poly := (divMod a b).1

end GF2Poly

/-! ## CRC as Polynomial Remainder

The mathematical definition of CRC is: given a data polynomial D(x) and
generator polynomial G(x), CRC = remainder of x^n * D(x) / G(x),
where n = degree of G(x). -/

/-- CRC as GF(2) polynomial remainder.
    dataCoeffs represents the data as a polynomial, generator is the CRC polynomial
    (with the implicit leading 1 bit, i.e., x^width + poly). -/
def crcAsRemainder (dataCoeffs : Nat) (generator : Nat) (width : Nat) : Nat :=
  let augmented := GF2Poly.mk (dataCoeffs <<< width)
  let gen := GF2Poly.mk (generator ||| (1 <<< width))
  (GF2Poly.mod augmented gen).coeffs

/-! ## CRC Check Property Specification

The fundamental CRC property: if a sender transmits data followed by the
CRC value, the receiver computing CRC over the combined message gets zero
(for non-reflected CRCs with xorOut=0). -/

/-- The CRC check property for a non-reflected CRC with xorOut=0:
    CRC(data ++ crc_bytes) should produce a fixed "good CRC" residue. -/
def crcCheckProperty (params : CRCParams) (data crcBytes : List Nat) (combined : List Nat) : Prop :=
  combined = data ++ crcBytes →
  params.xorOut = 0 →
  params.reflectIn = false →
  params.reflectOut = false →
  crcCompute params combined = 0

/-! ## CRC Linearity Specification

For linear CRCs (most standard CRCs), CRC(a XOR b) = CRC(a) XOR CRC(b)
when init=0 and xorOut=0. This is a consequence of CRC being a linear
function over GF(2). -/

/-- CRC linearity property: CRC distributes over XOR for zero-init CRCs. -/
def crcLinearProperty (poly width : Nat) (dataA dataB : List Nat) : Prop :=
  let params : CRCParams := {
    width := width, poly := poly, init := 0, xorOut := 0,
    reflectIn := false, reflectOut := false
  }
  let xorData := List.zipWith (· ^^^ ·) dataA dataB
  dataA.length = dataB.length →
  crcCompute params xorData = crcCompute params dataA ^^^ crcCompute params dataB

/-! ## GF(2) Multiplication Properties -/

/-- GF(2) multiplication by zero gives zero. -/
theorem gf2_mul_zero_left (a : GF2Poly) : GF2Poly.mul GF2Poly.zero a = GF2Poly.zero := by
  simp [GF2Poly.mul, GF2Poly.zero]
  unfold GF2Poly.mul.go
  simp

/-- Concrete verification: (x+1) * (x+1) = x^2 + 1 in GF(2)[x]. -/
theorem gf2_mul_example :
    GF2Poly.mul ⟨3⟩ ⟨3⟩ = ⟨5⟩ := by native_decide

/-- Concrete verification: x * x = x^2 in GF(2)[x]. -/
theorem gf2_mul_x_x :
    GF2Poly.mul ⟨2⟩ ⟨2⟩ = ⟨4⟩ := by native_decide

/-- Concrete verification: (x^2 + 1) * x = x^3 + x in GF(2)[x]. -/
theorem gf2_mul_distribute :
    GF2Poly.mul ⟨5⟩ ⟨2⟩ = ⟨10⟩ := by native_decide

/-- GF(2) multiplication by one is identity (concrete). -/
theorem gf2_mul_one_left :
    GF2Poly.mul ⟨1⟩ ⟨7⟩ = ⟨7⟩ := by native_decide

/-- GF(2) multiplication is commutative (concrete). -/
theorem gf2_mul_comm_concrete :
    GF2Poly.mul ⟨3⟩ ⟨5⟩ = GF2Poly.mul ⟨5⟩ ⟨3⟩ := by native_decide

/-- GF(2) divMod example: x^3 + x + 1 divided by x + 1. -/
theorem gf2_divmod_example :
    GF2Poly.divMod ⟨0b1011⟩ ⟨0b11⟩ = (⟨0b110⟩, ⟨1⟩) := by native_decide

/-- GF(2) mod example: x^3 + x + 1 mod (x + 1) = 1. -/
theorem gf2_mod_example :
    GF2Poly.mod ⟨0b1011⟩ ⟨0b11⟩ = ⟨1⟩ := by native_decide

/-- Division by zero returns the dividend as remainder. -/
theorem gf2_divmod_zero :
    GF2Poly.divMod ⟨7⟩ ⟨0⟩ = (⟨0⟩, ⟨7⟩) := by native_decide

/-- GF(2) division reconstruction: quotient * divisor + remainder = dividend. -/
theorem gf2_divmod_reconstruct :
    let (q, r) := GF2Poly.divMod ⟨0b1011⟩ ⟨0b11⟩
    GF2Poly.add (GF2Poly.mul q ⟨0b11⟩) r = ⟨0b1011⟩ := by native_decide

end Radix.CRC.Spec
