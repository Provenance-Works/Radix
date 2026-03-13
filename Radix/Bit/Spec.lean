/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.BitVec

/-!
# Bit Operations Specification (Layer 3)

This module defines the formal specification of all bitwise operations
using Mathlib's `BitVec n`.

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 1 or Layer 2 modules.

## References

- FR-002: Bitwise Operations
- FR-002.1: Basic operations (AND, OR, XOR, NOT)
- FR-002.1a: Shift/rotate edge cases (count >= bitWidth => count % bitWidth)
- FR-002.2: Bit scanning (clz, ctz, popcount, bitReverse)
-/

namespace Radix.Bit.Spec

open BitVec

variable {n : Nat}

/-! ## 1. Basic Bitwise Operations Specification -/

/-- Bitwise AND specification. -/
def band (x y : BitVec n) : BitVec n := x &&& y

/-- Bitwise OR specification. -/
def bor (x y : BitVec n) : BitVec n := x ||| y

/-- Bitwise XOR specification. -/
def bxor (x y : BitVec n) : BitVec n := x ^^^ y

/-- Bitwise NOT specification. -/
def bnot (x : BitVec n) : BitVec n := ~~~x

/-! ## 2. Shift Operations Specification

All shift operations normalize the count by `count % bitWidth`
when `count >= bitWidth` (FR-002.1a: Rust semantics). -/

/-- Logical left shift: `x << (count % n)`.
    When `count >= n`, the shift amount wraps (FR-002.1a). -/
def shl (x : BitVec n) (count : Nat) : BitVec n :=
  x <<< (count % n)

/-- Logical right shift: `x >>> (count % n)`.
    When `count >= n`, the shift amount wraps (FR-002.1a). -/
def shrLogical (x : BitVec n) (count : Nat) : BitVec n :=
  x >>> (count % n)

/-- Arithmetic right shift: preserves sign bit.
    When `count >= n`, the shift amount wraps (FR-002.1a). -/
def shrArith (x : BitVec n) (count : Nat) : BitVec n :=
  BitVec.sshiftRight x (count % n)

/-! ## 3. Rotate Operations Specification -/

/-- Rotate left by `count % n` positions. -/
def rotl (x : BitVec n) (count : Nat) : BitVec n :=
  let c := count % n
  (x <<< c) ||| (x >>> (n - c))

/-- Rotate right by `count % n` positions. -/
def rotr (x : BitVec n) (count : Nat) : BitVec n :=
  let c := count % n
  (x >>> c) ||| (x <<< (n - c))

/-! ## 4. Bit Scanning Specifications -/

/-- Count leading zeros: number of consecutive 0-bits from the MSB.
    Uses fuel-based recursion to check bits from MSB down. -/
def clz (x : BitVec n) : Nat :=
  go n 0
where
  go : Nat → Nat → Nat
    | 0, count => count
    | fuel + 1, count =>
      if count >= n then count
      else if x.getLsbD (n - 1 - count) then count
      else go fuel (count + 1)

/-- Count trailing zeros: number of consecutive 0-bits from the LSB. -/
def ctz (x : BitVec n) : Nat :=
  go n 0
where
  go : Nat → Nat → Nat
    | 0, count => count
    | fuel + 1, count =>
      if count >= n then count
      else if x.getLsbD count then count
      else go fuel (count + 1)

/-- Population count: number of 1-bits (Hamming weight). -/
def popcount (x : BitVec n) : Nat :=
  go n 0 0
where
  go : Nat → Nat → Nat → Nat
    | 0, _, acc => acc
    | fuel + 1, idx, acc =>
      if idx >= n then acc
      else go fuel (idx + 1) (if x.getLsbD idx then acc + 1 else acc)

/-- Bit reversal: reverse the order of all bits. -/
def bitReverse (x : BitVec n) : BitVec n :=
  go n 0 (0#n)
where
  go : Nat → Nat → BitVec n → BitVec n
    | 0, _, acc => acc
    | fuel + 1, idx, acc =>
      if idx >= n then acc
      else
        let acc' := if x.getLsbD idx then acc ||| ((1#n) <<< (n - 1 - idx)) else acc
        go fuel (idx + 1) acc'

/-! ## 5. Bit Field Specifications -/

/-- Extract bits `[lo, hi)` from `x`, shifted to the bottom. -/
def extractBits (x : BitVec n) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ n) : BitVec n :=
  (x >>> lo) &&& (BitVec.allOnes n >>> (n - (hi - lo)))

/-- Insert `bits` into `x` at positions `[lo, hi)`. -/
def insertBits (x bits : BitVec n) (lo hi : Nat) (_h : lo ≤ hi ∧ hi ≤ n) : BitVec n :=
  let width := hi - lo
  let mask := (BitVec.allOnes n >>> (n - width)) <<< lo
  (x &&& ~~~mask) ||| ((bits <<< lo) &&& mask)

/-! ## 6. Hamming Distance Specification -/

/-- Hamming distance: number of bit positions where two vectors differ.
    Equals popcount of their XOR (FR-002.3). -/
def hammingDistance (x y : BitVec n) : Nat := popcount (bxor x y)

end Radix.Bit.Spec
