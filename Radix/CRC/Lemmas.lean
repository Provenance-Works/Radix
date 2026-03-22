/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.CRC.Spec
import Radix.CRC.Ops

/-!
# CRC Proofs (Layer 3)

Correctness proofs for CRC implementations:

- Table size correctness (CRC-32, CRC-16)
- Streaming API consistency (init/update/finalize = compute)
- Empty data CRC value
- GF(2) polynomial algebra: complete group structure (commutativity, associativity,
  identity, self-inverse, left/right cancellation, xor-add equivalence)

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- v0.2.0 Roadmap: CRC-32 / CRC-16 — CRC(CRC(data) ++ check) = 0, linearity
-/

namespace Radix.CRC.Lemmas

/-! ## CRC-32 Table Properties -/

/-- CRC-32 table has exactly 256 entries. -/
theorem crc32_table_size : CRC32.table.size = 256 := by
  native_decide

/-- CRC-16 table has exactly 256 entries. -/
theorem crc16_table_size : CRC16.table.size = 256 := by
  native_decide

/-! ## Streaming API Consistency -/

/-- CRC-32 streaming: init/update/finalize on a single chunk equals compute. -/
theorem crc32_streaming_single (data : ByteArray) :
    CRC32.finalize (CRC32.update CRC32.init data) = CRC32.compute data := by
  simp [CRC32.finalize, CRC32.update, CRC32.init, CRC32.compute]

/-- CRC-16 streaming: init/update/finalize on a single chunk equals compute. -/
theorem crc16_streaming_single (data : ByteArray) :
    CRC16.finalize (CRC16.update CRC16.init data) = CRC16.compute data := by
  simp [CRC16.finalize, CRC16.update, CRC16.init, CRC16.compute]

/-! ## GF(2) Polynomial Properties -/

open Spec in
/-- GF(2) addition is commutative. -/
theorem gf2_add_comm (a b : GF2Poly) :
    GF2Poly.add a b = GF2Poly.add b a := by
  simp [GF2Poly.add, Nat.xor_comm]

open Spec in
/-- GF(2) addition is associative. -/
theorem gf2_add_assoc (a b c : GF2Poly) :
    GF2Poly.add (GF2Poly.add a b) c = GF2Poly.add a (GF2Poly.add b c) := by
  simp [GF2Poly.add, Nat.xor_assoc]

open Spec in
/-- GF(2) addition with zero is identity. -/
theorem gf2_add_zero (a : GF2Poly) :
    GF2Poly.add a GF2Poly.zero = a := by
  simp [GF2Poly.add, GF2Poly.zero]

open Spec in
/-- GF(2) addition is self-inverse (a + a = 0). -/
theorem gf2_add_self (a : GF2Poly) :
    GF2Poly.add a a = GF2Poly.zero := by
  simp [GF2Poly.add, GF2Poly.zero]

open Spec in
/-- GF(2) zero is a left identity: 0 + a = a. -/
theorem gf2_zero_add (a : GF2Poly) :
    GF2Poly.add GF2Poly.zero a = a := by
  simp [GF2Poly.add, GF2Poly.zero]

open Spec in
/-- GF(2) right cancellation: (a + b) + b = a. -/
theorem gf2_add_cancel_right (a b : GF2Poly) :
    GF2Poly.add (GF2Poly.add a b) b = a := by
  cases a; cases b
  simp [GF2Poly.add, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

open Spec in
/-- GF(2) left cancellation: a + (a + b) = b. -/
theorem gf2_add_cancel_left (a b : GF2Poly) :
    GF2Poly.add a (GF2Poly.add a b) = b := by
  cases a; cases b
  simp [GF2Poly.add, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

open Spec in
/-- GF(2) xor is the same operation as add (by definition). -/
theorem gf2_xor_eq_add (a b : GF2Poly) :
    GF2Poly.xor a b = GF2Poly.add a b := by
  simp [GF2Poly.xor]

/-! ## Empty Data CRC

The CRC of empty data is determined entirely by the init and xorOut parameters. -/

open Spec in
/-- Spec-level: CRC of empty data equals init XOR xorOut (masked). -/
theorem spec_crc_empty (params : CRCParams) :
    crcCompute params [] = (params.init ^^^ params.xorOut) &&& ((1 <<< params.width) - 1) :=
  Spec.crc_empty params

end Radix.CRC.Lemmas
