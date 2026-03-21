/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.CRC.Spec
import Radix.CRC.Ops

/-!
# CRC Proofs (Layer 3)

Correctness proofs for CRC implementations:

- Table size correctness
- Streaming API consistency (init/update/finalize = compute)
- Empty data CRC value
- Spec-level properties (empty data, linearity of GF(2) operations)

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

/-! ## Empty Data CRC

The CRC of empty data is determined entirely by the init and xorOut parameters. -/

open Spec in
/-- Spec-level: CRC of empty data equals init XOR xorOut (masked). -/
theorem spec_crc_empty (params : CRCParams) :
    crcCompute params [] = (params.init ^^^ params.xorOut) &&& ((1 <<< params.width) - 1) :=
  Spec.crc_empty params

end Radix.CRC.Lemmas
