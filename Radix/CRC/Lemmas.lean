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
  simp [CRC32.table]

/-- CRC-16 table has exactly 256 entries. -/
theorem crc16_table_size : CRC16.table.size = 256 := by
  simp [CRC16.table]

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

open Spec in
/-- GF(2) add distributes over triple: (a + b) + c = a + (b + c). -/
theorem gf2_add_right_comm (a b c : GF2Poly) :
    GF2Poly.add (GF2Poly.add a b) c = GF2Poly.add (GF2Poly.add a c) b := by
  rw [gf2_add_assoc, gf2_add_comm b c, ← gf2_add_assoc]

open Spec in
/-- GF(2) double negation: (a + b) + b = a. -/
theorem gf2_add_cancel_right' (a b : GF2Poly) :
    GF2Poly.add (GF2Poly.add a b) b = a := by
  cases a; cases b
  simp [GF2Poly.add, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

open Spec in
/-- GF(2) add/xor equivalence: xor inherits all algebraic properties. -/
theorem gf2_xor_comm (a b : GF2Poly) :
    GF2Poly.xor a b = GF2Poly.xor b a := by
  simp [GF2Poly.xor, gf2_add_comm]

open Spec in
/-- GF(2) xor is associative. -/
theorem gf2_xor_assoc (a b c : GF2Poly) :
    GF2Poly.xor (GF2Poly.xor a b) c = GF2Poly.xor a (GF2Poly.xor b c) := by
  simp [GF2Poly.xor, gf2_add_assoc]

open Spec in
/-- GF(2) xor with zero is identity. -/
theorem gf2_xor_zero (a : GF2Poly) :
    GF2Poly.xor a GF2Poly.zero = a := by
  simp [GF2Poly.xor, gf2_add_zero]

open Spec in
/-- GF(2) xor is self-inverse. -/
theorem gf2_xor_self (a : GF2Poly) :
    GF2Poly.xor a a = GF2Poly.zero := by
  simp [GF2Poly.xor, gf2_add_self]

/-! ## Empty Data CRC

The CRC of empty data is determined entirely by the init and xorOut parameters. -/

open Spec in
/-- Spec-level: CRC of empty data equals init XOR xorOut (masked). -/
theorem spec_crc_empty (params : CRCParams) :
    crcCompute params [] = (params.init ^^^ params.xorOut) &&& ((1 <<< params.width) - 1) :=
  Spec.crc_empty params

/-! ## CRC-32 Known-Answer Tests (RFC 3720 / ITU-T V.42)

These theorems verify the implementation against standard test vectors.
The canonical check string is "123456789" (ASCII), CRC-32 = 0xCBF43926. -/

/-- CRC-32 of an empty byte array is 0x00000000.
    (init=0xFFFFFFFF XOR xorOut=0xFFFFFFFF = 0) -/
theorem crc32_empty :
    CRC32.compute ByteArray.empty = ⟨0⟩ := by native_decide

/-- CRC-16 of an empty byte array is 0x0000.
    (init=0xFFFF XOR xorOut=0xFFFF = 0) -/
theorem crc16_empty :
    CRC16.compute ByteArray.empty = ⟨0⟩ := by native_decide

/-- CRC-32 of the single byte 0x00. -/
theorem crc32_single_zero :
    CRC32.compute (ByteArray.mk #[0x00]) = ⟨0xD202EF8D⟩ := by native_decide

/-- CRC-32 of the single byte 0xFF. -/
theorem crc32_single_ff :
    CRC32.compute (ByteArray.mk #[0xFF]) = ⟨0xFF000000⟩ := by native_decide

/-- CRC-32 of "123456789" (ASCII 0x31..0x39) equals 0xCBF43926.
    This is the standard ITU-T V.42 check value. -/
theorem crc32_check_value :
    CRC32.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
      = ⟨0xCBF43926⟩ := by native_decide

/-- CRC-16/CCITT of "123456789" equals 0x906E.
    Standard check value for CRC-16/CCITT. -/
theorem crc16_check_value :
    CRC16.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
      = ⟨0x906E⟩ := by native_decide

/-! ## Streaming Multi-Chunk Consistency

Processing data in chunks via init/update/finalize produces the same
result as processing the full data in one shot. -/

/-- CRC-32 two-chunk streaming: splitting "123456789" into "12345" + "6789"
    produces the same CRC. -/
theorem crc32_streaming_two_chunks :
    CRC32.finalize (CRC32.update (CRC32.update CRC32.init
      (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35]))
      (ByteArray.mk #[0x36, 0x37, 0x38, 0x39]))
    = CRC32.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) := by
  native_decide

/-- CRC-16 two-chunk streaming consistency. -/
theorem crc16_streaming_two_chunks :
    CRC16.finalize (CRC16.update (CRC16.update CRC16.init
      (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35]))
      (ByteArray.mk #[0x36, 0x37, 0x38, 0x39]))
    = CRC16.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) := by
  native_decide

/-- CRC-32 byte-at-a-time streaming consistency:
    update(update(init, [0x31]), [0x32]) = update(init, [0x31, 0x32]). -/
theorem crc32_streaming_byte_at_a_time :
    CRC32.update (CRC32.update CRC32.init (ByteArray.mk #[0x31])) (ByteArray.mk #[0x32])
    = CRC32.update CRC32.init (ByteArray.mk #[0x31, 0x32]) := by native_decide

/-- CRC-32 naive (bit-by-bit) reference matches table-driven for "123456789". -/
theorem crc32_naive_matches_table :
    CRC32.computeNaive (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
    = CRC32.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) := by
  native_decide

/-- CRC-16 naive reference matches table-driven for "123456789". -/
theorem crc16_naive_matches_table :
    CRC16.computeNaive (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
    = CRC16.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) := by
  native_decide

/-! ## Table Entry Verification -/

/-- CRC-32 table entry 0 is 0x00000000. -/
theorem crc32_table_entry_0 : CRC32.table[0]! = 0x00000000 := by native_decide

/-- CRC-32 table entry 255 (0xFF) is 0x2D02EF8D. -/
theorem crc32_table_entry_255 : CRC32.table[255]! = 0x2D02EF8D := by native_decide

/-- CRC-16 table entry 0 is 0x0000. -/
theorem crc16_table_entry_0 : CRC16.table[0]! = 0x0000 := by native_decide

/-- CRC-16 table entry 255 is 0x0F78. -/
theorem crc16_table_entry_255 : CRC16.table[255]! = 0x0F78 := by native_decide

/-- CRC-32 init and finalize cancel: finalize(init) = 0. -/
theorem crc32_finalize_init :
    CRC32.finalize CRC32.init = ⟨0⟩ := by native_decide

/-- CRC-16 init and finalize cancel: finalize(init) = 0. -/
theorem crc16_finalize_init :
    CRC16.finalize CRC16.init = ⟨0⟩ := by native_decide

/-! ## GF(2) Polynomial Structural Properties -/

open Spec in
/-- GF(2) zero polynomial has coefficients 0. -/
theorem gf2_zero_coeffs : GF2Poly.zero.coeffs = 0 := rfl

open Spec in
/-- GF(2) add preserves structural equality. -/
theorem gf2_add_left_cancel (a b c : GF2Poly) (h : GF2Poly.add a b = GF2Poly.add a c) :
    b = c := by
  have h1 := gf2_add_cancel_left a b
  have h2 := gf2_add_cancel_left a c
  rw [h] at h1
  rw [h1] at h2
  exact h2

open Spec in
/-- GF(2) add right cancellation. -/
theorem gf2_add_right_cancel (a b c : GF2Poly) (h : GF2Poly.add a c = GF2Poly.add b c) :
    a = b := by
  have h1 := gf2_add_cancel_right' a c
  have h2 := gf2_add_cancel_right' b c
  rw [h] at h1
  rw [h1] at h2
  exact h2

end Radix.CRC.Lemmas
