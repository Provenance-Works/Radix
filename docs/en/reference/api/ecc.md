# ECC Module API Reference

> **Module**: `Radix.ECC`
> **Source**: `Radix/ECC/`

## Overview

Provides a compact algebraic model for parity and Hamming(7,4) error-correcting codes. The module is intended for low-level storage, firmware image, and transport encodings that need lightweight single-bit error correction.

## Specification (`ECC.Spec`)

Mathematical model of a Hamming(7,4) codeword:

```lean
abbrev Nibble := Fin 16

structure Codeword74 where
  p1 : Bool
  p2 : Bool
  d0 : Bool
  p4 : Bool
  d1 : Bool
  d2 : Bool
  d3 : Bool

def bitVal (b : Bool) : Nat
def xor3 (a b c : Bool) : Bool
def toNibble (c : Codeword74) : Nibble
def ofNibble (n : Nibble) : Codeword74
def syndrome (c : Codeword74) : Nat
def errorIndex? (c : Codeword74) : Option (Fin 7)
def flipAt (c : Codeword74) (idx : Fin 7) : Codeword74
def correct (c : Codeword74) : Codeword74
def evenParity (n width : Nat) : Bool
```

### Semantics

- `syndrome = 0` means the received word satisfies every parity equation.
- `correct` repairs any single-bit error addressed by the Hamming syndrome.
- `evenParity` computes parity over the low `width` bits of a natural number.

### Correction Boundary

- Plain Hamming(7,4) guarantees correction only for clean words and single-bit errors.
- Multi-bit corruption can map to a different valid codeword after `correct`; callers must not treat `correct` as a general integrity check.

## Operations (`ECC.Ops`)

Executable helpers over `UInt8` codewords:

```lean
abbrev Nibble := Spec.Nibble
abbrev Codeword74 := Spec.Codeword74

inductive Status where
  | clean
  | corrected (idx : Fin 7)

def toByte (c : Codeword74) : UInt8
def isCodewordByte (b : UInt8) : Bool
def fromByte? (b : UInt8) : Option Codeword74
def encodeNibble (n : Nibble) : UInt8
def encodeByte? (b : UInt8) : Option UInt8
def decode (b : UInt8) : Option UInt8
def syndrome (b : UInt8) : Option Nat
def errorIndex? (b : UInt8) : Option (Fin 7)
def check (b : UInt8) : Bool
def status? (b : UInt8) : Option Status
def correct (b : UInt8) : Option UInt8
def decodeAfterCorrect (b : UInt8) : Option UInt8
def evenParity (b : UInt8) (width : Nat := 8) : Bool
```

- `isCodewordByte` rejects bytes that use the high bit outside the Hamming(7,4) payload.
- `decode` returns `some` only for low-7-bit inputs whose syndrome is zero; parity-invalid words must be repaired with `correct` before decoding.
- `syndrome`, `errorIndex?`, `status?`, and `correct` are checked APIs and return `none` for invalid 8-bit inputs.
- `status?` distinguishes already-clean words from single-bit-repairable words, while `decodeAfterCorrect` gives the common decode-after-repair path directly.
- `correct` does not detect all multi-bit errors; if the transport requires multi-bit detection, add an outer checksum/parity layer.

## Proofs (`ECC.Lemmas`)

- `toNibble_ofNibble`: spec-level encoding followed by extraction recovers the original nibble
- `toNibble_correct_single_bit`: correcting any one flipped bit recovers the original nibble
- `errorIndex?_eq_none_iff_syndrome_zero`: clean codewords have no correction index
- `errorIndex?_flipAt_ofNibble`: single-bit corruption is classified at the flipped bit
- `decode_encodeNibble`: executable decode after encode returns the original payload bits
- `status?_encodeNibble` / `status?_single_bit`: executable classification matches clean vs corrected codewords
- `decode_correct_single_bit`: executable correction preserves the nibble represented by the codeword
- `decodeAfterCorrect_single_bit`: decode-after-correct succeeds for any single-bit corruption

## Examples

```lean
import Radix.ECC

def demo : Option UInt8 :=
  let nibble : Radix.ECC.Nibble := ⟨0xB, by decide⟩
  let encoded := Radix.ECC.encodeNibble nibble
  let corrupted := encoded ^^^ 0x04
  Radix.ECC.decodeAfterCorrect corrupted
```

## Related Documents

- [Bit](bit.md) — lower-level bit operations used by parity reasoning
- [Bytes](bytes.md) — byte-oriented primitives that pair well with ECC payloads
