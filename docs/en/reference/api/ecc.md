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
def flipAt (c : Codeword74) (idx : Fin 7) : Codeword74
def correct (c : Codeword74) : Codeword74
def evenParity (n width : Nat) : Bool
```

### Semantics

- `syndrome = 0` means the received word satisfies every parity equation.
- `correct` repairs any single-bit error addressed by the Hamming syndrome.
- `evenParity` computes parity over the low `width` bits of a natural number.

## Operations (`ECC.Ops`)

Executable helpers over `UInt8` codewords:

```lean
abbrev Nibble := Spec.Nibble
abbrev Codeword74 := Spec.Codeword74

def toByte (c : Codeword74) : UInt8
def isCodewordByte (b : UInt8) : Bool
def fromByte? (b : UInt8) : Option Codeword74
def encodeNibble (n : Nibble) : UInt8
def encodeByte? (b : UInt8) : Option UInt8
def decode (b : UInt8) : Option UInt8
def syndrome (b : UInt8) : Option Nat
def check (b : UInt8) : Bool
def correct (b : UInt8) : Option UInt8
def evenParity (b : UInt8) (width : Nat := 8) : Bool
```

- `isCodewordByte` rejects bytes that use the high bit outside the Hamming(7,4) payload.
- `decode`, `syndrome`, and `correct` are checked APIs and return `none` for invalid 8-bit inputs.

## Proofs (`ECC.Lemmas`)

- `toNibble_ofNibble`: spec-level encoding followed by extraction recovers the original nibble
- `toNibble_correct_single_bit`: correcting any one flipped bit recovers the original nibble
- `decode_encodeNibble`: executable decode after encode returns the original payload bits
- `decode_correct_single_bit`: executable correction preserves the nibble represented by the codeword

## Examples

```lean
import Radix.ECC

def demo : Option UInt8 :=
  let nibble : Radix.ECC.Nibble := ⟨0xB, by decide⟩
  let encoded := Radix.ECC.encodeNibble nibble
  let corrupted := encoded ^^^ 0x04
  Radix.ECC.correct corrupted
```

## Related Documents

- [Bit](bit.md) — lower-level bit operations used by parity reasoning
- [Bytes](bytes.md) — byte-oriented primitives that pair well with ECC payloads
