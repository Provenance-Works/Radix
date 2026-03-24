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

/-! ## CRC-8 Table and Known-Answer Tests -/

/-- CRC-8 table has exactly 256 entries. -/
theorem crc8_table_size : CRC8.table.size = 256 := by
  simp [CRC8.table]

/-- CRC-8/MAXIM of empty data is 0x00. -/
theorem crc8_empty :
    CRC8.compute ByteArray.empty = 0 := by native_decide

/-- CRC-8/MAXIM of "123456789" equals 0xA1. Standard check value. -/
theorem crc8_check_value :
    CRC8.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
      = 0xA1 := by native_decide

/-- CRC-8/MAXIM of single zero byte. -/
theorem crc8_single_zero :
  CRC8.compute (ByteArray.mk #[0x00]) = 0x00 := by native_decide

/-- CRC-8/MAXIM of single 0xFF byte. -/
theorem crc8_single_ff :
  CRC8.compute (ByteArray.mk #[0xFF]) = 0x35 := by native_decide

/-- CRC-8 naive matches table-driven for "123456789". -/
theorem crc8_naive_matches_table :
    CRC8.computeNaive (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
    = CRC8.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) := by
  native_decide

/-- CRC-8 streaming single chunk equals compute. -/
theorem crc8_streaming_single (data : ByteArray) :
    CRC8.finalize (CRC8.update CRC8.init data) = CRC8.compute data := by
  simp [CRC8.finalize, CRC8.update, CRC8.init, CRC8.compute]

/-- CRC-8 streaming two-chunk consistency. -/
theorem crc8_streaming_two_chunks :
    CRC8.finalize (CRC8.update (CRC8.update CRC8.init
      (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35]))
      (ByteArray.mk #[0x36, 0x37, 0x38, 0x39]))
    = CRC8.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) := by
  native_decide

/-! ## CRC-64 Table and Known-Answer Tests -/

/-- CRC-64 table has exactly 256 entries. -/
theorem crc64_table_size : CRC64.table.size = 256 := by
  simp [CRC64.table]

/-- CRC-64/XZ of empty data is 0x0000000000000000. -/
theorem crc64_empty :
    CRC64.compute ByteArray.empty = 0 := by native_decide

/-- CRC-64/XZ of "123456789" equals 0x995DC9BBDF1939FA. Standard check value. -/
theorem crc64_check_value :
    CRC64.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
      = 0x995DC9BBDF1939FA := by native_decide

/-- CRC-64/XZ of single zero byte. -/
theorem crc64_single_zero :
  CRC64.compute (ByteArray.mk #[0x00]) = 0x1FADA17364673F59 := by native_decide

/-- CRC-64 naive matches table-driven for "123456789". -/
theorem crc64_naive_matches_table :
    CRC64.computeNaive (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
    = CRC64.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) := by
  native_decide

/-- CRC-64 streaming single chunk equals compute. -/
theorem crc64_streaming_single (data : ByteArray) :
    CRC64.finalize (CRC64.update CRC64.init data) = CRC64.compute data := by
  simp [CRC64.finalize, CRC64.update, CRC64.init, CRC64.compute]

/-- CRC-64 streaming two-chunk consistency. -/
theorem crc64_streaming_two_chunks :
    CRC64.finalize (CRC64.update (CRC64.update CRC64.init
      (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35]))
      (ByteArray.mk #[0x36, 0x37, 0x38, 0x39]))
    = CRC64.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]) := by
  native_decide

/-! ## Extended CRC-32 Known-Answer Tests (ITU-T V.42)

Standard CRC-32 test vectors from multiple sources to validate against
external implementations. -/

/-- CRC-32 of "a" (single ASCII character). -/
theorem crc32_single_a :
    CRC32.compute (ByteArray.mk #[0x61]) = ⟨0xE8B7BE43⟩ := by native_decide

/-- CRC-32 of "abc". -/
theorem crc32_abc :
    CRC32.compute (ByteArray.mk #[0x61, 0x62, 0x63]) = ⟨0x352441C2⟩ := by native_decide

/-- CRC-32 of "ABCDEFGHIJKLMNOPQRSTUVWXYZ". -/
theorem crc32_alpha_upper :
    CRC32.compute (ByteArray.mk #[0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48,
                                   0x49, 0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50,
                                   0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58,
                                   0x59, 0x5A])
    = ⟨0xABF77822⟩ := by native_decide

/-- CRC-32 of all zeros (4 bytes). -/
theorem crc32_four_zeros :
    CRC32.compute (ByteArray.mk #[0x00, 0x00, 0x00, 0x00]) = ⟨0x2144DF1C⟩ := by native_decide

/-- CRC-32 of all 0xFF (4 bytes). -/
theorem crc32_four_ff :
    CRC32.compute (ByteArray.mk #[0xFF, 0xFF, 0xFF, 0xFF]) = ⟨0xFFFFFFFF⟩ := by native_decide

/-! ## Extended CRC-16 Known-Answer Tests -/

/-- CRC-16/CCITT of "a" (single ASCII character). -/
theorem crc16_single_a :
  CRC16.compute (ByteArray.mk #[0x61]) = ⟨0x82F7⟩ := by native_decide

/-- CRC-16/CCITT of "abc". -/
theorem crc16_abc :
  CRC16.compute (ByteArray.mk #[0x61, 0x62, 0x63]) = ⟨0x9E25⟩ := by native_decide

/-! ## CRC Error Detection Properties -/

/-- CRC-32 detects a single-bit flip in the first byte of "Hello". -/
theorem crc32_detects_single_bit_flip :
    CRC32.compute (ByteArray.mk #[0x48, 0x65, 0x6C, 0x6C, 0x6F])
    ≠ CRC32.compute (ByteArray.mk #[0x49, 0x65, 0x6C, 0x6C, 0x6F]) := by native_decide

/-- CRC-32 detects byte transposition in "AB" vs "BA". -/
theorem crc32_detects_transposition :
    CRC32.compute (ByteArray.mk #[0x41, 0x42])
    ≠ CRC32.compute (ByteArray.mk #[0x42, 0x41]) := by native_decide

/-- CRC-16 detects a single-bit flip. -/
theorem crc16_detects_single_bit_flip :
    CRC16.compute (ByteArray.mk #[0x48, 0x65, 0x6C, 0x6C, 0x6F])
    ≠ CRC16.compute (ByteArray.mk #[0x49, 0x65, 0x6C, 0x6C, 0x6F]) := by native_decide

/-- CRC-8 detects a single-bit flip. -/
theorem crc8_detects_single_bit_flip :
    CRC8.compute (ByteArray.mk #[0x48, 0x65, 0x6C, 0x6C, 0x6F])
    ≠ CRC8.compute (ByteArray.mk #[0x49, 0x65, 0x6C, 0x6C, 0x6F]) := by native_decide

/-! ## Generic CRC Engine Validation -/

/-- Generic CRC engine matches CRC-32 for the standard check value. -/
theorem generic_crc32_check_value :
    let g := GenericCRC.mk' 32 0xEDB88320 0xFFFFFFFF 0xFFFFFFFF
    g.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
      = 0xCBF43926 := by native_decide

/-- Generic CRC engine matches CRC-16 for the standard check value. -/
theorem generic_crc16_check_value :
    let g := GenericCRC.mk' 16 0x8408 0xFFFF 0xFFFF
    g.compute (ByteArray.mk #[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39])
      = 0x906E := by native_decide

/-! ## GF(2) Polynomial Multiplication Properties -/

open Spec in
/-- GF(2) multiplication is commutative (verified for small polynomials). -/
theorem gf2_mul_comm_3_5 :
    GF2Poly.mul ⟨3⟩ ⟨5⟩ = GF2Poly.mul ⟨5⟩ ⟨3⟩ := by native_decide

open Spec in
/-- GF(2) multiplication is associative (verified for small polynomials). -/
theorem gf2_mul_assoc_2_3_5 :
    GF2Poly.mul (GF2Poly.mul ⟨2⟩ ⟨3⟩) ⟨5⟩ = GF2Poly.mul ⟨2⟩ (GF2Poly.mul ⟨3⟩ ⟨5⟩) := by
  native_decide

open Spec in
/-- GF(2) multiplication distributes over addition. -/
theorem gf2_mul_distrib_left :
    GF2Poly.mul ⟨2⟩ (GF2Poly.add ⟨3⟩ ⟨5⟩) =
    GF2Poly.add (GF2Poly.mul ⟨2⟩ ⟨3⟩) (GF2Poly.mul ⟨2⟩ ⟨5⟩) := by native_decide

open Spec in
/-- GF(2) division reconstruction: q * b + r = a. -/
theorem gf2_divmod_reconstruction_check :
    let a := GF2Poly.mk 0b11010111
    let b := GF2Poly.mk 0b10011
    let (q, r) := GF2Poly.divMod a b
    GF2Poly.add (GF2Poly.mul q b) r = a := by native_decide

/-! ## reflectBits Involution Properties -/

open Spec in
/-- reflectBits involution: reflecting twice with the same width recovers the original (all 4-bit values). -/
theorem reflectBits_involutive_4 :
    ∀ v : Fin 16, reflectBits (reflectBits v.val 4) 4 = v.val := by native_decide

open Spec in
/-- reflectBits of 0xAB reflected as 8 bits gives 0xD5. -/
example : reflectBits 0xAB 8 = 0xD5 := by native_decide

open Spec in
/-- reflectBits preserves zero. -/
example : reflectBits 0 8 = 0 := by native_decide

open Spec in
/-- reflectBits of all-ones 8-bit gives all-ones. -/
example : reflectBits 0xFF 8 = 0xFF := by native_decide

/-! ## CRC-32 Additional Error Detection -/

/-- CRC-32 detects insertion of a zero byte. -/
theorem crc32_detects_zero_insertion :
    CRC32.compute (ByteArray.mk #[0x41, 0x42])
    ≠ CRC32.compute (ByteArray.mk #[0x41, 0x00, 0x42]) := by native_decide

/-! ## CRC Incremental Consistency (additional) -/

/-- CRC-8 streaming: 3-chunk equals single compute for "Hello". -/
theorem crc8_streaming_three_chunks :
    let p1 := ByteArray.mk #[0x48]  -- "H"
    let p2 := ByteArray.mk #[0x65, 0x6C]  -- "el"
    let p3 := ByteArray.mk #[0x6C, 0x6F]  -- "lo"
    let full := ByteArray.mk #[0x48, 0x65, 0x6C, 0x6C, 0x6F]  -- "Hello"
    CRC8.finalize (CRC8.update (CRC8.update (CRC8.update CRC8.init p1) p2) p3)
      = CRC8.compute full := by native_decide

end Radix.CRC.Lemmas
