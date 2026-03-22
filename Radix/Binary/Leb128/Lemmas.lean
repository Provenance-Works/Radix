/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Binary.Leb128
import Radix.Binary.Leb128.Spec
import Mathlib.Tactic.IntervalCases

/-!
# LEB128 Correctness Proofs (Layer 3)

Round-trip properties and encoding size bounds for LEB128.

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- docs/design/wasm-support-plan.md, Section 3.3
-/

namespace Radix.Binary.Leb128

/-! ================================================================ -/
/-! ## Helper Lemmas                                                  -/
/-! ================================================================ -/

private theorem ba_size_push (a : ByteArray) (v : _root_.UInt8) :
    (a.push v).size = a.size + 1 := by
  unfold ByteArray.push ByteArray.size; simp [Array.size_push]

private theorem ba_empty_size : ByteArray.empty.size = 0 := by
  decide

/-! ================================================================ -/
/-! ## encodeUnsigned Bounds                                          -/
/-! ================================================================ -/

/-- `encodeUnsigned` always adds at least one byte. -/
theorem encodeUnsigned_size_pos (n : Nat) (acc : ByteArray) :
    acc.size < (encodeUnsigned n acc).size := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    rw [encodeUnsigned]
    split
    · rw [ba_size_push]; omega
    · have hlt : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
      simp only at *
      exact lt_trans (by rw [ba_size_push]; omega) (ih (n / 128) hlt _)

/-- `encodeUnsigned` size is bounded by `acc.size + fuel` when `n < 128^fuel`. -/
theorem encodeUnsigned_size_le (n : Nat) (acc : ByteArray) (fuel : Nat)
    (hn : n < 128 ^ fuel) (hfuel : 0 < fuel) :
    (encodeUnsigned n acc).size ≤ acc.size + fuel := by
  induction fuel generalizing n acc with
  | zero => omega
  | succ k ih =>
    rw [encodeUnsigned]
    split
    · rw [ba_size_push]; omega
    · rename_i hge
      push_neg at hge
      have hk : 0 < k := by
        by_contra hc; push_neg at hc
        have := Nat.le_zero.mp hc; subst this; simp at hn; omega
      have hdiv : n / 128 < 128 ^ k := by
        have hpow := Nat.pow_succ 128 k
        rw [hpow] at hn
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hn)
      simp only at *
      exact le_trans (ih _ _ hdiv hk) (by rw [ba_size_push]; omega)

/-! ================================================================ -/
/-! ## encodeSigned Bounds                                            -/
/-! ================================================================ -/

/-- `encodeSigned` size is bounded by `acc.size + fuel`. -/
theorem encodeSigned_size_le (n : Int) (acc : ByteArray) (fuel : Nat) :
    (encodeSigned n acc fuel).size ≤ acc.size + fuel := by
  induction fuel generalizing n acc with
  | zero => simp [encodeSigned]
  | succ k ih =>
    unfold encodeSigned; dsimp only []
    split_ifs
    · rw [ba_size_push]; omega
    · specialize ih (n.shiftRight 7) (acc.push ((n % 128).toNat ||| 0x80).toUInt8)
      rw [ba_size_push] at ih; omega

/-- `encodeSigned` with positive fuel always adds at least one byte. -/
theorem encodeSigned_size_pos (n : Int) (acc : ByteArray) (fuel : Nat)
    (hfuel : 0 < fuel) :
    acc.size < (encodeSigned n acc fuel).size := by
  induction fuel generalizing n acc with
  | zero => omega
  | succ k ih =>
    unfold encodeSigned; dsimp only []
    split_ifs
    · rw [ba_size_push]; omega
    · match k with
      | 0 => simp [encodeSigned]
      | k' + 1 =>
        have := ih (n.shiftRight 7) (acc.push ((n % 128).toNat ||| 0x80).toUInt8) (by omega)
        rw [ba_size_push] at this; omega

/-! ================================================================ -/
/-! ## Encoding Size Bounds                                           -/
/-! ================================================================ -/

/-- Unsigned 32-bit LEB128 encoding uses at most 5 bytes. -/
theorem encodeU32_size_le (x : Radix.UInt32) :
    (encodeU32 x).size ≤ 5 := by
  unfold encodeU32
  have hx : x.toNat < 4294967296 := by
    unfold Radix.UInt32.toNat; exact UInt32.toNat_lt x.val
  have : (4294967296 : Nat) ≤ 128 ^ 5 := by decide
  have := encodeUnsigned_size_le x.toNat ByteArray.empty 5 (by omega) (by omega)
  rw [ba_empty_size] at this; omega

/-- Unsigned 64-bit LEB128 encoding uses at most 10 bytes. -/
theorem encodeU64_size_le (x : Radix.UInt64) :
    (encodeU64 x).size ≤ 10 := by
  unfold encodeU64
  have hx : x.toNat < 18446744073709551616 := by
    unfold Radix.UInt64.toNat; exact UInt64.toNat_lt x.val
  have : (18446744073709551616 : Nat) ≤ 128 ^ 10 := by decide
  have := encodeUnsigned_size_le x.toNat ByteArray.empty 10 (by omega) (by omega)
  rw [ba_empty_size] at this; omega

/-- Signed 32-bit LEB128 encoding uses at most 5 bytes. -/
theorem encodeS32_size_le (x : Radix.Int32) :
    (encodeS32 x).size ≤ 5 := by
  unfold encodeS32
  have := encodeSigned_size_le x.toInt ByteArray.empty 5
  rw [ba_empty_size] at this; omega

/-- Signed 64-bit LEB128 encoding uses at most 10 bytes. -/
theorem encodeS64_size_le (x : Radix.Int64) :
    (encodeS64 x).size ≤ 10 := by
  unfold encodeS64
  have := encodeSigned_size_le x.toInt ByteArray.empty 10
  rw [ba_empty_size] at this; omega

/-! ================================================================ -/
/-! ## Encoding Produces at Least 1 Byte                             -/
/-! ================================================================ -/

/-- Unsigned 32-bit LEB128 encoding always produces at least one byte. -/
theorem encodeU32_size_pos (x : Radix.UInt32) :
    0 < (encodeU32 x).size := by
  unfold encodeU32
  have := encodeUnsigned_size_pos x.toNat ByteArray.empty
  rw [ba_empty_size] at this; omega

/-- Unsigned 64-bit LEB128 encoding always produces at least one byte. -/
theorem encodeU64_size_pos (x : Radix.UInt64) :
    0 < (encodeU64 x).size := by
  unfold encodeU64
  have := encodeUnsigned_size_pos x.toNat ByteArray.empty
  rw [ba_empty_size] at this; omega

/-- Signed 32-bit LEB128 encoding always produces at least one byte. -/
theorem encodeS32_size_pos (x : Radix.Int32) :
    0 < (encodeS32 x).size := by
  unfold encodeS32
  have := encodeSigned_size_pos x.toInt ByteArray.empty 5 (by omega)
  rw [ba_empty_size] at this; omega

/-- Signed 64-bit LEB128 encoding always produces at least one byte. -/
theorem encodeS64_size_pos (x : Radix.Int64) :
    0 < (encodeS64 x).size := by
  unfold encodeS64
  have := encodeSigned_size_pos x.toInt ByteArray.empty 10 (by omega)
  rw [ba_empty_size] at this; omega

/-! ================================================================ -/
/-! ## ByteArray Access Helpers                                       -/
/-! ================================================================ -/

/-- Accessing a prefix element of a pushed ByteArray returns the original. -/
private theorem ba_push_getElem_lt (acc : ByteArray) (v : _root_.UInt8) (j : Nat)
    (hj : j < acc.size) :
    (acc.push v)[j]'(by rw [ByteArray.size_push]; omega) = acc[j] := by
  unfold ByteArray.push
  show (acc.data.push v)[j]'_ = acc[j]
  rw [Array.getElem_push]
  split
  case isTrue => rfl
  case isFalse h => exfalso; exact h hj

/-- Accessing the last element of a pushed ByteArray returns the pushed value. -/
private theorem ba_push_getElem_eq (acc : ByteArray) (v : _root_.UInt8) :
    (acc.push v)[acc.size]'(by rw [ByteArray.size_push]; omega) = v := by
  unfold ByteArray.push
  show (acc.data.push v)[acc.data.size]'_ = v
  rw [Array.getElem_push]
  split
  case isTrue h => exfalso; omega
  case isFalse => rfl

/-! ================================================================ -/
/-! ## encodeUnsigned Prefix Preservation                             -/
/-! ================================================================ -/

/-- `encodeUnsigned` only appends bytes; it never modifies existing elements. -/
theorem encodeUnsigned_prefix (n : Nat) (acc : ByteArray) (j : Nat)
    (hj : j < acc.size) (hj2 : j < (encodeUnsigned n acc).size) :
    (encodeUnsigned n acc)[j] = acc[j] := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    by_cases h128 : n < 128
    · have heq : encodeUnsigned n acc = acc.push n.toUInt8 := by
        rw [encodeUnsigned.eq_1]; exact if_pos h128
      simp only [heq]; exact ba_push_getElem_lt acc n.toUInt8 j hj
    · push_neg at h128
      have hlt : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
      have heq : encodeUnsigned n acc =
          encodeUnsigned (n / 128) (acc.push (n % 128 ||| 128).toUInt8) := by
        rw [encodeUnsigned.eq_1]; exact if_neg (by omega)
      have hj' : j < (acc.push (n % 128 ||| 128).toUInt8).size := by
        rw [ByteArray.size_push]; omega
      simp only [heq]
      rw [ih _ hlt _ hj' (by simp only [← heq]; exact hj2)]
      exact ba_push_getElem_lt acc _ j hj

/-! ================================================================ -/
/-! ## Bitwise Helpers                                                -/
/-! ================================================================ -/

/-- `n &&& (2^k - 1) = n % 2^k` — bitwise AND with low-bit mask equals modulo. -/
private theorem nat_and_two_pow_sub_one (n k : Nat) :
    n &&& (2 ^ k - 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  exact Bool.and_comm _ _

/-! ================================================================ -/
/-! ## Round-Trip Properties                                          -/
/-! ================================================================ -/

/-
**Proof strategy** (applies to all four round-trip theorems):

The round-trip `decode(encode(x)) = (x, size)` is proved by strong induction
on `x.toNat` (unsigned) or by induction on fuel (signed), establishing a
general invariant for the decode loop `go`:

  After reading byte `i` (= `acc.size`) from `encodeUnsigned n acc`, with
  accumulated `result` and `shift = 7*i`, the go loop returns
  `some (fromBitVec (ofNat w (result ||| (n <<< shift))), totalSize)`.

Key sub-lemmas needed:
1. `encodeUnsigned_prefix` (proven above): prefix bytes are preserved
2. `ba_push_getElem_eq`: the byte at position `acc.size` is the just-pushed byte
3. Bitwise identities: `n &&& 0x7F = n % 128`, `n < 128 → n &&& 0x80 = 0`,
   `(n%128 ||| 0x80) &&& 0x7F = n%128`, continuation bit detection
4. OR-shift decomposition: `(n%128) <<< (7*i) ||| (n/128) <<< (7*(i+1)) = n <<< (7*i)`
   (proven via `Nat.eq_of_testBit_eq` with `Nat.testBit_mod_two_pow`, `Nat.testBit_div_two_pow`)
5. Type roundtrip: `fromBitVec (ofNat w x.toNat) = x`

The base case (n < 128) unfolds `encodeUnsigned` once (push final byte) and
`decodeU32.go` once (read byte, check no continuation, return result).
The recursive case (n ≥ 128) unfolds both once, reads the continuation byte,
and applies the IH with `n' = n/128`, `i' = i+1`, `result' = result ||| (n%128 <<< shift)`.
-/

/-- Low 7 bits via AND 0x7F equals mod 128. -/
private theorem and_0x7F_eq (n : Nat) : n &&& 0x7F = n % 128 := by
  rw [show (0x7F : Nat) = 2 ^ 7 - 1 from by decide]; exact nat_and_two_pow_sub_one n 7

/-- If `n < 128`, then bit 7 is clear. -/
private theorem and_0x80_eq_zero_of_lt_128 {n : Nat} (h : n < 128) :
    n &&& 0x80 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff]
  rw [show (0x80 : Nat) = 2 ^ 7 from by decide, Nat.testBit_two_pow]
  by_cases hj : 7 = j
  · subst hj; left; exact Nat.testBit_lt_two_pow (by omega : n < 2 ^ 7)
  · right; simp [hj]

/-- For `n < 128`, `(n ||| 0x80) &&& 0x7F = n`. -/
private theorem or_0x80_and_0x7F_eq {n : Nat} (h : n < 128) :
    (n ||| 0x80) &&& 0x7F = n := by
  rw [Nat.and_or_distrib_right,
      show (0x80 : Nat) &&& 0x7F = 0 from by decide, Nat.or_zero]
  rw [show (0x7F : Nat) = 2 ^ 7 - 1 from by decide,
      Nat.and_two_pow_sub_one_of_lt_two_pow (by omega)]

/-- `n ||| 0x80 < 256` when `n < 128`. -/
private theorem or_0x80_lt_256' {n : Nat} (h : n < 128) : n ||| 0x80 < 256 :=
  Nat.lt_of_lt_of_le (Nat.or_lt_two_pow (by omega) (by decide : 0x80 < 2 ^ 8))
    (by decide)

/-- The continuation bit is set for `n ||| 0x80`. -/
private theorem or_0x80_and_0x80_ne_zero' {n : Nat} :
    ¬((n ||| 0x80) &&& 0x80 == 0) := by
  rw [beq_iff_eq, Nat.and_or_distrib_right,
      show (0x80 : Nat) &&& 0x80 = 0x80 from by decide]
  intro h
  have : 0x80 ≤ n &&& 0x80 ||| 0x80 := Nat.right_le_or
  omega

/-- Decomposition: `(n%128) ||| ((n/128) <<< 7) = n`. -/
private theorem mod128_or_div128_shiftLeft' (n : Nat) :
    n % 128 ||| ((n / 128) <<< 7) = n := by
  have h128 : (128 : Nat) = 2 ^ 7 := by decide
  rw [h128]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow]
  by_cases hi7 : i < 7
  · simp [show ¬(7 ≤ i) from by omega, hi7]
  · have hi7' : 7 ≤ i := by omega
    simp only [hi7, hi7', decide_true, Bool.true_and]
    rw [Nat.testBit_div_two_pow]
    have : i - 7 + 7 = i := by omega
    simp [this]

/-- Reassemble shifted OR: the low chunk and high chunk reconstruct the original shift. -/
private theorem or_shift_reassemble (n shift : Nat) :
    ((n % 128) <<< shift) ||| ((n / 128) <<< (shift + 7)) = n <<< shift := by
  have h128 : (128 : Nat) = 2 ^ 7 := by decide
  rw [h128]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
      Nat.testBit_mod_two_pow]
  by_cases his : shift ≤ i
  · simp only [his, decide_true, Bool.true_and]
    by_cases hi7 : i - shift < 7
    · simp only [show ¬(shift + 7 ≤ i) from by omega, decide_false, Bool.false_and,
                  hi7]
      simp
    · simp only [show ¬(i - shift < 7) from by omega,
                  show shift + 7 ≤ i from by omega, decide_true, Bool.true_and]
      rw [Nat.testBit_div_two_pow]
      have : i - (shift + 7) + 7 = i - shift := by omega
      simp [this]
  · simp [show ¬(shift ≤ i) from by omega, show ¬(shift + 7 ≤ i) from by omega]

/-- `encodeUnsigned n acc` with `n < 128` reduces to a single push. -/
private theorem encodeUnsigned_base {n : Nat} (h : n < 128) (acc : ByteArray) :
    encodeUnsigned n acc = acc.push n.toUInt8 := by
  rw [encodeUnsigned.eq_1]; exact if_pos h

/-- `encodeUnsigned n acc` with `n ≥ 128` recurses. -/
private theorem encodeUnsigned_step {n : Nat} (h : ¬(n < 128)) (acc : ByteArray) :
    encodeUnsigned n acc =
      encodeUnsigned (n / 128) (acc.push (n % 128 ||| 0x80).toUInt8) := by
  rw [encodeUnsigned.eq_1]; exact if_neg h

/-- Core invariant for unsigned 32-bit roundtrip:
    `decodeU32.go` applied to the output of `encodeUnsigned n acc` at byte
    position `acc.size` with accumulated `result` and `shift = 7 * acc.size`
    returns the fully reconstructed value. -/
private theorem decodeU32_go_encodeUnsigned_inv
    (n : Nat) (acc : ByteArray) (result : Nat)
    (hn : n < 2 ^ 32)
    (hle : acc.size ≤ 4)
    (hresult : result < 2 ^ (7 * acc.size))
    (htotal : result ||| (n <<< (7 * acc.size)) < 2 ^ 32) :
    decodeU32.go (encodeUnsigned n acc) 0 result (7 * acc.size) acc.size =
      some (Radix.UInt32.fromBitVec
              (BitVec.ofNat 32 (result ||| (n <<< (7 * acc.size)))),
            (encodeUnsigned n acc).size) := by
  induction n using Nat.strongRecOn generalizing acc result with
  | _ n ih =>
    if h128 : n < 128 then
      -- ─── Base case: n fits in one byte ───
      rw [encodeUnsigned_base h128]
      unfold decodeU32.go
      -- acc.size < 5
      simp only [show ¬(acc.size ≥ 5) from by omega, ite_false,
                 show 0 + acc.size = acc.size from by omega]
      -- Position is valid
      simp only [show acc.size < (acc.push n.toUInt8).size from by
        rw [ByteArray.size_push]; omega, dite_true]
      -- Read the byte
      rw [ba_push_getElem_eq]
      have htoNat : n.toUInt8.toNat = n :=
        UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega)
      simp only [htoNat]
      rw [and_0x7F_eq, Nat.mod_eq_of_lt (by omega : n < 128)]
      -- Overflow check on byte 4
      by_cases hov : (acc.size == 4 && decide (n > 15)) = true
      · -- acc.size = 4 and n > 0x0F → contradiction with htotal
        exfalso
        simp [beq_iff_eq] at hov
        obtain ⟨h4, hovf⟩ := hov
        have h1 : n <<< 28 ≤ result ||| (n <<< 28) := Nat.right_le_or
        have h2 : n <<< 28 = n * 2 ^ 28 := Nat.shiftLeft_eq n 28
        have h3 : 16 * 2 ^ 28 ≤ n * 2 ^ 28 := by omega
        have h5 : (16 : Nat) * 2 ^ 28 = 2 ^ 32 := by decide
        have h6 : 7 * acc.size = 28 := by omega
        rw [h6] at htotal
        omega
      · -- No overflow
        simp only [hov]
        rw [and_0x80_eq_zero_of_lt_128 h128]
        simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
        simp [ByteArray.size_push]
    else
      -- ─── Inductive case: n ≥ 128 ───
      push_neg at h128
      have hlt : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
      rw [encodeUnsigned_step (by omega : ¬(n < 128))]
      set acc' := acc.push (n % 128 ||| 0x80).toUInt8 with hacc'_def
      have hacc'_size : acc'.size = acc.size + 1 := ByteArray.size_push
      -- acc.size ≤ 3 (n ≥ 128 so n uses at least 2 bytes, total ≤ 5)
      have hacc_le3 : acc.size ≤ 3 := by
        by_contra hc; push_neg at hc
        have h4 : acc.size = 4 := by omega
        -- With acc.size = 4, shift = 28, n ≥ 128, so n <<< 28 ≥ 128 * 2^28 = 2^35 > 2^32
        have : 128 * 2 ^ 28 ≤ n <<< (7 * acc.size) := by
          rw [h4, Nat.shiftLeft_eq]; omega
        have : n <<< (7 * acc.size) ≤ result ||| (n <<< (7 * acc.size)) := Nat.right_le_or
        have : (128 : Nat) * 2 ^ 28 = 2 ^ 35 := by decide
        omega
      -- Unfold one step of decode
      unfold decodeU32.go
      simp only [show ¬(acc.size ≥ 5) from by omega, ite_false,
                 show 0 + acc.size = acc.size from by omega]
      -- Position valid in the encoded output
      have hpos : acc.size < (encodeUnsigned (n / 128) acc').size := by
        have := encodeUnsigned_size_pos (n / 128) acc'
        rw [hacc'_size] at this; omega
      simp only [hpos, dite_true]
      -- Read the continuation byte
      have hbyte : (encodeUnsigned (n / 128) acc')[acc.size]'hpos =
          (n % 128 ||| 0x80).toUInt8 := by
        rw [encodeUnsigned_prefix (n / 128) acc' acc.size
              (by rw [hacc'_size]; omega) hpos]
        exact ba_push_getElem_eq acc (n % 128 ||| 0x80).toUInt8
      rw [hbyte]
      have hmod : n % 128 < 128 := Nat.mod_lt n (by omega)
      have htoNat2 : (n % 128 ||| 0x80).toUInt8.toNat = n % 128 ||| 0x80 :=
        UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; exact or_0x80_lt_256' hmod)
      simp only [htoNat2]
      rw [or_0x80_and_0x7F_eq hmod]
      -- Overflow check passes (acc.size ≤ 3)
      by_cases hov : (acc.size == 4 && decide (n % 128 > 15)) = true
      · exfalso; simp [beq_iff_eq] at hov; omega
      · simp only [hov]
        -- Continuation bit is set
        simp only [or_0x80_and_0x80_ne_zero']
        -- Show shift' = 7 * acc'.size
        have hshift' : 7 * acc.size + 7 = 7 * acc'.size := by
          rw [hacc'_size]; omega
        -- Bound on result'
        have hresult' : result ||| ((n % 128) <<< (7 * acc.size)) <
            2 ^ (7 * acc'.size) := by
          rw [hacc'_size, show 7 * (acc.size + 1) = 7 * acc.size + 7 from by omega]
          exact Nat.or_lt_two_pow
            (Nat.lt_of_lt_of_le hresult (Nat.pow_le_pow_right (by omega) (by omega)))
            (by rw [Nat.shiftLeft_eq]; calc
                (n % 128) * 2 ^ (7 * acc.size) < 128 * 2 ^ (7 * acc.size) :=
                  Nat.mul_lt_mul_of_pos_right (Nat.mod_lt n (by omega)) (Nat.two_pow_pos _)
                _ = 2 ^ (7 * acc.size + 7) := by
                  rw [show (128 : Nat) = 2 ^ 7 from by decide, ← Nat.pow_add]
                  congr 1; omega)
        -- Reconstruct total
        have hrec : (result ||| ((n % 128) <<< (7 * acc.size))) |||
            ((n / 128) <<< (7 * acc'.size)) =
            result ||| (n <<< (7 * acc.size)) := by
          rw [hacc'_size, show 7 * (acc.size + 1) = 7 * acc.size + 7 from by omega,
              Nat.or_assoc, or_shift_reassemble]
        rw [hshift']
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show acc.size + 1 = acc'.size from hacc'_size.symm]
        -- Rewrite the goal's RHS to match what IH produces
        conv_rhs => rw [show result ||| (n <<< (7 * acc.size)) =
            (result ||| ((n % 128) <<< (7 * acc.size))) |||
            ((n / 128) <<< (7 * acc'.size)) from hrec.symm]
        exact ih (n / 128) hlt acc'
          (result ||| ((n % 128) <<< (7 * acc.size)))
          (by omega)
          (by omega)
          hresult'
          (by rw [hrec]; exact htotal)

/-- Type-level roundtrip: `fromBitVec (ofNat 32 x.toNat) = x`. -/
private theorem fromBitVec32_roundtrip (x : Radix.UInt32) :
    Radix.UInt32.fromBitVec (BitVec.ofNat 32 x.toNat) = x := by
  simp [Radix.UInt32.fromBitVec, Radix.UInt32.toNat]

/-- Decoding an encoded unsigned 32-bit value yields the original value. -/
theorem decodeU32_encodeU32_roundtrip (x : Radix.UInt32) :
    decodeU32 (encodeU32 x) 0 = some (x, (encodeU32 x).size) := by
  unfold encodeU32 decodeU32
  have hx : x.toNat < 2 ^ 32 := by
    unfold Radix.UInt32.toNat; exact UInt32.toNat_lt x.val
  have := decodeU32_go_encodeUnsigned_inv x.toNat ByteArray.empty 0
    hx (by rw [ba_empty_size]; omega)
    (by rw [ba_empty_size]; omega)
    (by rw [ba_empty_size]; simp; omega)
  rw [ba_empty_size, show 7 * 0 = 0 from by omega] at this
  simp at this; rw [this]; congr 1; congr 1
  exact fromBitVec32_roundtrip x

/-! ================================================================ -/
/-! ## U64 Round-Trip                                                 -/
/-! ================================================================ -/

/-- Core invariant for unsigned 64-bit roundtrip. -/
private theorem decodeU64_go_encodeUnsigned_inv
    (n : Nat) (acc : ByteArray) (result : Nat)
    (hn : n < 2 ^ 64)
    (hle : acc.size ≤ 9)
    (hresult : result < 2 ^ (7 * acc.size))
    (htotal : result ||| (n <<< (7 * acc.size)) < 2 ^ 64) :
    decodeU64.go (encodeUnsigned n acc) 0 result (7 * acc.size) acc.size =
      some (Radix.UInt64.fromBitVec
              (BitVec.ofNat 64 (result ||| (n <<< (7 * acc.size)))),
            (encodeUnsigned n acc).size) := by
  induction n using Nat.strongRecOn generalizing acc result with
  | _ n ih =>
    if h128 : n < 128 then
      -- ─── Base case: n fits in one byte ───
      rw [encodeUnsigned_base h128]
      unfold decodeU64.go
      simp only [show ¬(acc.size ≥ 10) from by omega, ite_false,
                 show 0 + acc.size = acc.size from by omega]
      simp only [show acc.size < (acc.push n.toUInt8).size from by
        rw [ByteArray.size_push]; omega, dite_true]
      rw [ba_push_getElem_eq]
      have htoNat : n.toUInt8.toNat = n :=
        UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega)
      simp only [htoNat]
      rw [and_0x7F_eq, Nat.mod_eq_of_lt (by omega : n < 128)]
      -- Overflow check on byte 9
      by_cases hov : (acc.size == 9 && decide (n > 1)) = true
      · exfalso
        simp [beq_iff_eq] at hov
        obtain ⟨h9, hovf⟩ := hov
        have h1 : n <<< 63 ≤ result ||| (n <<< 63) := Nat.right_le_or
        have h2 : n <<< 63 = n * 2 ^ 63 := Nat.shiftLeft_eq n 63
        have h3 : 2 * 2 ^ 63 ≤ n * 2 ^ 63 := by omega
        have h5 : (2 : Nat) * 2 ^ 63 = 2 ^ 64 := by decide
        have h6 : 7 * acc.size = 63 := by omega
        rw [h6] at htotal
        omega
      · simp only [hov]
        rw [and_0x80_eq_zero_of_lt_128 h128]
        simp only [beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
        simp [ByteArray.size_push]
    else
      -- ─── Inductive case: n ≥ 128 ───
      push_neg at h128
      have hlt : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
      rw [encodeUnsigned_step (by omega : ¬(n < 128))]
      set acc' := acc.push (n % 128 ||| 0x80).toUInt8 with hacc'_def
      have hacc'_size : acc'.size = acc.size + 1 := ByteArray.size_push
      have hacc_le8 : acc.size ≤ 8 := by
        by_contra hc; push_neg at hc
        have h9 : acc.size = 9 := by omega
        have : 128 * 2 ^ 63 ≤ n <<< (7 * acc.size) := by
          rw [h9, Nat.shiftLeft_eq]; omega
        have : n <<< (7 * acc.size) ≤ result ||| (n <<< (7 * acc.size)) := Nat.right_le_or
        have : (128 : Nat) * 2 ^ 63 = 2 ^ 70 := by decide
        omega
      unfold decodeU64.go
      simp only [show ¬(acc.size ≥ 10) from by omega, ite_false,
                 show 0 + acc.size = acc.size from by omega]
      have hpos : acc.size < (encodeUnsigned (n / 128) acc').size := by
        have := encodeUnsigned_size_pos (n / 128) acc'
        rw [hacc'_size] at this; omega
      simp only [hpos, dite_true]
      have hbyte : (encodeUnsigned (n / 128) acc')[acc.size]'hpos =
          (n % 128 ||| 0x80).toUInt8 := by
        rw [encodeUnsigned_prefix (n / 128) acc' acc.size
              (by rw [hacc'_size]; omega) hpos]
        exact ba_push_getElem_eq acc (n % 128 ||| 0x80).toUInt8
      rw [hbyte]
      have hmod : n % 128 < 128 := Nat.mod_lt n (by omega)
      have htoNat2 : (n % 128 ||| 0x80).toUInt8.toNat = n % 128 ||| 0x80 :=
        UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; exact or_0x80_lt_256' hmod)
      simp only [htoNat2]
      rw [or_0x80_and_0x7F_eq hmod]
      by_cases hov : (acc.size == 9 && decide (n % 128 > 1)) = true
      · exfalso; simp [beq_iff_eq] at hov; omega
      · simp only [hov]
        simp only [or_0x80_and_0x80_ne_zero']
        have hshift' : 7 * acc.size + 7 = 7 * acc'.size := by
          rw [hacc'_size]; omega
        have hresult' : result ||| ((n % 128) <<< (7 * acc.size)) <
            2 ^ (7 * acc'.size) := by
          rw [hacc'_size, show 7 * (acc.size + 1) = 7 * acc.size + 7 from by omega]
          exact Nat.or_lt_two_pow
            (Nat.lt_of_lt_of_le hresult (Nat.pow_le_pow_right (by omega) (by omega)))
            (by rw [Nat.shiftLeft_eq]; calc
                (n % 128) * 2 ^ (7 * acc.size) < 128 * 2 ^ (7 * acc.size) :=
                  Nat.mul_lt_mul_of_pos_right (Nat.mod_lt n (by omega)) (Nat.two_pow_pos _)
                _ = 2 ^ (7 * acc.size + 7) := by
                  rw [show (128 : Nat) = 2 ^ 7 from by decide, ← Nat.pow_add]
                  congr 1; omega)
        have hrec : (result ||| ((n % 128) <<< (7 * acc.size))) |||
            ((n / 128) <<< (7 * acc'.size)) =
            result ||| (n <<< (7 * acc.size)) := by
          rw [hacc'_size, show 7 * (acc.size + 1) = 7 * acc.size + 7 from by omega,
              Nat.or_assoc, or_shift_reassemble]
        rw [hshift']
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show acc.size + 1 = acc'.size from hacc'_size.symm]
        conv_rhs => rw [show result ||| (n <<< (7 * acc.size)) =
            (result ||| ((n % 128) <<< (7 * acc.size))) |||
            ((n / 128) <<< (7 * acc'.size)) from hrec.symm]
        exact ih (n / 128) hlt acc'
          (result ||| ((n % 128) <<< (7 * acc.size)))
          (by omega)
          (by omega)
          hresult'
          (by rw [hrec]; exact htotal)

/-- Type-level roundtrip: `fromBitVec (ofNat 64 x.toNat) = x`. -/
private theorem fromBitVec64_roundtrip (x : Radix.UInt64) :
    Radix.UInt64.fromBitVec (BitVec.ofNat 64 x.toNat) = x := by
  simp [Radix.UInt64.fromBitVec, Radix.UInt64.toNat]

/-- Decoding an encoded unsigned 64-bit value yields the original value. -/
theorem decodeU64_encodeU64_roundtrip (x : Radix.UInt64) :
    decodeU64 (encodeU64 x) 0 = some (x, (encodeU64 x).size) := by
  unfold encodeU64 decodeU64
  have hx : x.toNat < 2 ^ 64 := by
    unfold Radix.UInt64.toNat; exact UInt64.toNat_lt x.val
  have := decodeU64_go_encodeUnsigned_inv x.toNat ByteArray.empty 0
    hx (by rw [ba_empty_size]; omega)
    (by rw [ba_empty_size]; omega)
    (by rw [ba_empty_size]; simp; omega)
  rw [ba_empty_size, show 7 * 0 = 0 from by omega] at this
  simp at this; rw [this]; congr 1; congr 1
  exact fromBitVec64_roundtrip x

/-! ================================================================ -/
/-! ## S32 Round-Trip                                                 -/
/-! ================================================================ -/

/-! ### Signed encoder helpers -/

/-- The done condition for the signed LEB128 encoder. -/
private def signedDone (v : Int) : Bool :=
  (v.shiftRight 7 == 0 && (v % 128).toNat / 64 == 0) ||
  (v.shiftRight 7 == -1 && (v % 128).toNat / 64 != 0)

private theorem encodeSigned_base' (v : Int) (acc : ByteArray) (fuel : Nat)
    (hdone : signedDone v = true) :
    encodeSigned v acc (fuel + 1) = acc.push (v % 128).toNat.toUInt8 := by
  rw [encodeSigned.eq_2]; exact if_pos hdone

private theorem encodeSigned_step' (v : Int) (acc : ByteArray) (fuel : Nat)
    (hcont : signedDone v = false) :
    encodeSigned v acc (fuel + 1) =
      encodeSigned (v.shiftRight 7) (acc.push ((v % 128).toNat ||| 0x80).toUInt8) fuel := by
  rw [encodeSigned.eq_2]
  have : ¬(signedDone v = true) := by simp [hcont]
  exact if_neg this

private theorem encodeSigned_prefix' (v : Int) (acc : ByteArray) (fuel : Nat) (j : Nat)
    (hj : j < acc.size) (hj2 : j < (encodeSigned v acc fuel).size) :
    (encodeSigned v acc fuel)[j] = acc[j] := by
  induction fuel generalizing v acc with
  | zero => simp only [encodeSigned.eq_1]
  | succ k ih =>
    match hdone : signedDone v with
    | true =>
      simp only [encodeSigned_base' v acc k hdone]
      exact ba_push_getElem_lt acc _ j hj
    | false =>
      have heq := encodeSigned_step' v acc k hdone
      have hj' : j < (acc.push ((v % 128).toNat ||| 0x80).toUInt8).size := by
        rw [ByteArray.size_push]; omega
      simp only [heq]
      rw [ih _ _ hj' (by simp only [← heq]; exact hj2)]
      exact ba_push_getElem_lt acc _ j hj

/-! ### Modular arithmetic helpers for signed proofs -/

private theorem emod128_toNat_lt' (v : Int) : (v % 128).toNat < 128 := by
  have := Int.emod_nonneg v (by decide : (128 : Int) ≠ 0)
  have := Int.emod_lt_of_pos v (by decide : (0 : Int) < 128); omega

/-- Combine low `shift` bits with next 7 bits via OR. -/
private theorem or_shift_mod_eq' (a shift : Nat) :
    (a % 2^shift) ||| (((a / 2^shift) % 128) <<< shift) =
    a % 2^(shift + 7) := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
             Nat.testBit_div_two_pow,
             show (128 : Nat) = 2^7 from by decide, Nat.testBit_mod_two_pow]
  by_cases h1 : k < shift
  · simp [h1, show ¬(shift ≤ k) from by omega, show k < shift + 7 from by omega]
  · by_cases h2 : k < shift + 7
    · simp [h1, h2, show shift ≤ k from by omega,
            show k - shift < 7 from by omega,
            show k - shift + shift = k from by omega]
    · simp [*, show ¬(k - shift < 7) from by omega]

/-- Connection (positive): Int shift+mod → Nat div+mod. -/
private theorem conn_pos (n k : Nat) :
    ((Int.ofNat n).shiftRight k % 128).toNat = n / 2^k % 128 := by
  simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
  exact Int.toNat_emod (Int.natCast_nonneg _) (by decide)

private theorem or_div2 (a b : Nat) : (a ||| b) / 2 = (a / 2) ||| (b / 2) := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_div_two, Nat.testBit_or, Nat.testBit_or,
      Nat.testBit_div_two, Nat.testBit_div_two]

private theorem and_div2 (a b : Nat) : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_div_two, Nat.testBit_and, Nat.testBit_and,
      Nat.testBit_div_two, Nat.testBit_div_two]

private theorem or_mod2_eq (a b : Nat) (h : a &&& b = 0) :
    (a ||| b) % 2 = a % 2 + b % 2 := by
  have tor : (a ||| b).testBit 0 = (a.testBit 0 || b.testBit 0) := Nat.testBit_or a b 0
  have tand : (a.testBit 0 && b.testBit 0) = (a &&& b).testBit 0 := (Nat.testBit_and a b 0).symm
  rw [h] at tand; simp only [Nat.testBit_zero] at tand
  simp only [Nat.testBit_zero] at tor
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  rcases Nat.mod_two_eq_zero_or_one (a ||| b) with hor | hor <;>
  simp_all

/-- `a ||| b = a + b` when bits are disjoint. -/
private theorem or_eq_add_of_and_eq_zero (a b : Nat) (h : a &&& b = 0) :
    a ||| b = a + b := by
  induction a using Nat.strongRecOn generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with ha0 | ha0
    · subst ha0; simp
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0; simp
    have hmod := or_mod2_eq a b h
    have hdiv : (a ||| b) / 2 = a / 2 + b / 2 := by
      rw [or_div2]
      apply ih (a / 2) (Nat.div_lt_self ha0 (by omega))
      rw [← and_div2, h]
    have ha2 := Nat.div_add_mod a 2
    have hb2 := Nat.div_add_mod b 2
    have hab2 := Nat.div_add_mod (a ||| b) 2
    omega

/-! ### Int.shiftRight composition -/

private theorem int_shiftRight_add (a : Int) (m n : Nat) :
    (a.shiftRight m).shiftRight n = a.shiftRight (m + n) := by
  rcases a with k | k <;> simp only [Int.shiftRight, Nat.shiftRight_add]

/-! ### Unsigned value conversion -/

private theorem uval_pos (n : Nat) (hn : n < 2^31) :
    (BitVec.ofInt 32 (Int.ofNat n)).toNat = n := by
  rw [BitVec.toNat_ofInt]; push_cast; exact Nat.mod_eq_of_lt (by omega)

private theorem uval_neg (m : Nat) (hm : m < 2^31) :
    (BitVec.ofInt 32 (Int.negSucc m)).toNat = 2^32 - (m + 1) := by
  rw [BitVec.toNat_ofInt, Int.negSucc_emod _ (by positivity : (0 : Int) < ↑(2^32 : Nat))]
  simp; omega

/-! ### Connection lemma for negative (S32) -/

private theorem conn_neg_s32 (m : Nat) (k : Nat) (hm : m < 2^31)
    (hk : k ≤ 21) (hk7 : 7 ∣ k) :
    ((Int.negSucc m).shiftRight k % 128).toNat = (2^32 - (m + 1)) / 2^k % 128 := by
  simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
  rw [Int.negSucc_emod _ (show (0 : Int) < 128 from by decide)]
  interval_cases k <;> simp_all <;> omega

/-! ### Unified connection lemma (S32) -/

set_option maxHeartbeats 400000 in
private theorem conn_signed_s32 (v_orig : Int) (shift : Nat)
    (hv_range : -(2^31 : Int) ≤ v_orig ∧ v_orig < 2^31)
    (hshift : shift ≤ 21) (hshift7 : 7 ∣ shift) :
    (v_orig.shiftRight shift % 128).toNat =
    (BitVec.ofInt 32 v_orig).toNat / 2^shift % 128 := by
  rcases v_orig with n | m
  · have hn : n < 2^31 := by
      have := hv_range.2
      simp only [show Int.ofNat n = (↑n : Int) from rfl] at this; omega
    rw [conn_pos n shift, uval_pos n hn]
  · have hm : m < 2^31 := by
      have := hv_range.1
      simp only [show Int.negSucc m = -(↑m + 1 : Int) from rfl] at this; omega
    rw [conn_neg_s32 m shift hm hshift hshift7, uval_neg m hm]

/-! ### signedDone at byte 4 -/

private theorem signedDone_at_byte4 (v_orig : Int)
    (hv_range : -(2^31 : Int) ≤ v_orig ∧ v_orig < 2^31) :
    signedDone (v_orig.shiftRight 28) = true := by
  rcases v_orig with n | m
  · have : n < 2^31 := by
      have := hv_range.2
      simp only [show Int.ofNat n = (↑n : Int) from rfl] at this; omega
    simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    set v := n / 2^28; have : v ≤ 7 := by omega
    interval_cases v <;> decide
  · have : m < 2^31 := by
      have := hv_range.1
      simp only [show Int.negSucc m = -(↑m + 1 : Int) from rfl] at this; omega
    simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    set v := m / 2^28; have : v ≤ 7 := by omega
    interval_cases v <;> decide

/-! ### Sign extension helpers -/

/-- `(a % 2^k) &&& (b <<< k) = 0`: low mod and shifted value are disjoint. -/
private theorem mod_and_shiftLeft_zero (a b k : Nat) :
    (a % 2^k) &&& (b <<< k) = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
             Nat.zero_testBit]
  by_cases hi : k ≤ i
  · simp [show ¬(i < k) from by omega, hi]
  · simp [hi]

private theorem neg_terminal_upper_s32 (m shift' : Nat) (hm : m < 2^shift')
    (hshift' : shift' ≤ 28) (h7 : 7 ∣ shift') (hsp : 0 < shift') :
    (2^32 - (m + 1)) / 2^shift' = 2^(32 - shift') - 1 := by
  interval_cases shift' <;> omega

private theorem sign_ext_arith_s32 (uval shift' : Nat) (_huval : uval < 2^32)
    (hshift' : shift' ≤ 28) (h7 : 7 ∣ shift') (hsp : 0 < shift')
    (h_upper : uval / 2^shift' = 2^(32 - shift') - 1) :
    uval % 2^shift' + (2^32 - 2^shift') = uval := by
  have := Nat.div_add_mod uval (2^shift')
  interval_cases shift' <;> omega

/-! ### SignBit / 0x40 helpers -/

private theorem signBit_zero_implies_and_0x40_eq_zero (byte : Nat) (_h : byte < 128)
    (hsb : (byte / 64 == 0) = true) :
    byte &&& 0x40 = 0 := by
  simp [beq_iff_eq] at hsb
  apply Nat.eq_of_testBit_eq; intro j
  simp only [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff]
  rw [show (0x40 : Nat) = 2^6 from by decide, Nat.testBit_two_pow]
  by_cases hj : 6 = j
  · subst hj; left; exact Nat.testBit_lt_two_pow (by omega)
  · right; simp [hj]

private theorem signBit_ne_implies_and_0x40_ne_zero (byte : Nat) (h : byte < 128)
    (hsb : (byte / 64 != 0) = true) :
    byte &&& 0x40 ≠ 0 := by
  simp [bne_iff_ne] at hsb
  intro heq
  have hbit6 : byte.testBit 6 = true := by
    rw [Nat.testBit]; simp [Nat.shiftRight_eq_div_pow]; omega
  have : (byte &&& 0x40).testBit 6 = true := by
    rw [Nat.testBit_and, hbit6]
    rw [show (0x40 : Nat) = 2^6 from by decide, Nat.testBit_two_pow]; simp
  rw [heq] at this; simp at this

/-! ### Overflow check for byte 4 (S32) -/

set_option maxHeartbeats 800000 in
private theorem overflow_check_byte4_s32 (v_orig : Int)
    (hv : -(2^31 : Int) ≤ v_orig ∧ v_orig < 2^31) :
    let v := v_orig.shiftRight 28
    let byte := (v % 128).toNat
    let value := byte &&& 0x7F
    ¬(value > 0x07 ∧ value < 0x78) := by
  rcases v_orig with n | m
  · simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    have hn : n < 2^31 := by simp at hv; omega
    set b := n / 2^28; have : b ≤ 7 := by omega
    intro ⟨h1, h2⟩
    have hb : (Int.ofNat b % 128).toNat = b := by
      rw [show (128 : Int) = ↑(128 : Nat) from rfl]; simp; omega
    rw [hb] at h1 h2
    have : b &&& 0x7F = b := by
      rw [show (0x7F : Nat) = 2^7 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]; omega
    rw [this] at h1 h2; omega
  · simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    have hm : m < 2^31 := by simp [Int.negSucc_eq] at hv; omega
    set b := m / 2^28; have : b ≤ 7 := by omega
    intro ⟨h1, h2⟩
    have hb : (Int.negSucc b % 128).toNat = 128 - (b + 1) := by
      simp only [Int.negSucc_emod _ (show (0:Int) < 128 from by decide)]; omega
    rw [hb] at h1 h2
    have hval : (128 - (b + 1)) &&& 0x7F = 128 - (b + 1) := by
      rw [show (0x7F : Nat) = 2^7 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]; omega
    rw [hval] at h1 h2; omega

/-! ### Terminal rest conditions -/

private theorem terminal_rest_zero' (n_orig : Int) (s : Nat)
    (hn : -2 ^ 31 ≤ n_orig ∧ n_orig < 2 ^ 31) (_hs : s ≤ 35)
    (hrest : (n_orig.shiftRight s == 0) = true) :
    (BitVec.ofInt 32 n_orig).toNat / 2 ^ s = 0 := by
  rcases n_orig with a | m
  · simp only [Int.shiftRight, beq_iff_eq] at hrest
    have hshift : a >>> s = 0 := by
      cases h : a >>> s with
      | zero => rfl
      | succ n => exfalso; rw [h] at hrest; simp only [Int.ofNat_eq_natCast] at hrest; omega
    have ha_div : a / 2 ^ s = 0 := by omega
    have ha_lt : a < 2 ^ 32 := by simp only [Int.ofNat_eq_natCast] at hn; omega
    rw [BitVec.toNat_ofInt]; simp only [Int.ofNat_eq_natCast]
    have h1 : (↑a : Int) % (↑(2 ^ 32 : Nat) : Int) = ↑a := by omega
    simp only [h1, Int.toNat_natCast]; exact ha_div
  · simp only [Int.shiftRight, beq_iff_eq] at hrest
    exact absurd hrest Int.noConfusion

private theorem terminal_rest_neg_one' (n_orig : Int) (s : Nat)
    (hn : -2 ^ 31 ≤ n_orig ∧ n_orig < 2 ^ 31) (hs : s < 32)
    (hrest : (n_orig.shiftRight s == -1) = true) :
    (BitVec.ofInt 32 n_orig).toNat / 2 ^ s = 2 ^ (32 - s) - 1 := by
  rcases n_orig with a | m
  · simp only [Int.shiftRight, beq_iff_eq] at hrest
    have : (0 : Int) ≤ Int.ofNat (a >>> s) := Int.natCast_nonneg _; omega
  · simp only [Int.shiftRight, beq_iff_eq] at hrest
    have hms : m >>> s = 0 := by
      have h : Int.negSucc (m >>> s) = Int.negSucc 0 := by
        simp only [Int.negSucc_eq] at hrest ⊢; omega
      exact Int.negSucc.inj h
    have hm_div : m / 2 ^ s = 0 := by omega
    have hm_bound : m < 2 ^ 31 := by simp only [Int.negSucc_eq] at hn; omega
    have hm_lt : m + 1 ≤ 2 ^ s := by
      have := Nat.div_add_mod m (2 ^ s); rw [hm_div] at this; omega
    rw [BitVec.toNat_ofInt]; simp only [Int.negSucc_eq]
    show (-(↑m + 1 : Int) % (↑(2 ^ 32 : Nat) : Int)).toNat / 2 ^ s = 2 ^ (32 - s) - 1
    have hmod : (-(↑m + 1 : Int)) % (↑(2 ^ 32 : Nat) : Int) = ↑(2 ^ 32 - (m + 1) : Nat) := by
      omega
    rw [hmod, Int.toNat_natCast]
    interval_cases s <;> omega

private theorem mask_helper_s32 (shift' : Nat) (hsp : shift' ≤ 28) (hsp0 : 0 < shift') (hsp7 : 7 ∣ shift') :
    0xFFFFFFFF - ((1 <<< shift') - 1) = 2^32 - 2^shift' := by
  rw [Nat.shiftLeft_eq, show 0xFFFFFFFF = 2^32 - 1 from by decide]
  interval_cases shift' <;> omega

/-! ### S32 type-level roundtrip -/

private theorem fromBitVec32_signed_roundtrip (x : Radix.Int32) :
    Radix.Int32.fromBitVec (BitVec.ofInt 32 x.toInt) = x := by
  simp [Radix.Int32.fromBitVec, Radix.Int32.toInt, BitVec.ofInt_toInt]

set_option maxHeartbeats 1600000 in
/-- Terminal byte 4 (acc.size = 4, shift = 28): the combined result mod 2^32 equals uval.
    This handles the case where conn_signed_s32 cannot be used (shift = 28 > 21). -/
private theorem terminal_byte4_result_mod (v_orig : Int)
    (hv_range : -(2^31 : Int) ≤ v_orig ∧ v_orig < 2^31)
    (result : Nat) (hresult : result = (BitVec.ofInt 32 v_orig).toNat % 2^28) :
    (result ||| ((v_orig.shiftRight 28 % 128).toNat <<< 28)) % 2^32 =
    (BitVec.ofInt 32 v_orig).toNat := by
  set uval := (BitVec.ofInt 32 v_orig).toNat with huval_def
  set byte := (v_orig.shiftRight 28 % 128).toNat with hbyte_def
  have huval_lt : uval < 2^32 := BitVec.isLt _
  rw [hresult]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi32 : i < 32 <;> by_cases hi28 : i < 28
  · -- i < 28, i < 32: low bits only
    have : ¬(28 ≤ i) := by omega
    simp [hi32, hi28, this]
  · -- 28 ≤ i < 32: high bits (byte)
    have h28 : 28 ≤ i := by omega
    simp only [hi32, hi28, h28, decide_true, decide_false, Bool.true_and,
               Bool.false_and, Bool.false_or, Bool.true_and]
    rcases v_orig with n | m
    · -- Positive case
      have hn : n < 2^31 := by have := hv_range.2; simp at this; omega
      simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow, Int.ofNat_eq_natCast] at hbyte_def huval_def
      have hbyte_simp : byte = n / 2^28 := by rw [hbyte_def]; push_cast; omega
      have huval_simp : uval = n := by
        rw [huval_def, BitVec.toNat_ofInt]; push_cast; exact Nat.mod_eq_of_lt (by omega)
      rw [hbyte_simp, huval_simp]
      conv_rhs => rw [show i = i - 28 + 28 from by omega]
      exact @Nat.testBit_div_two_pow 28 n (i - 28)
    · -- Negative case
      have hm : m < 2^31 := by have := hv_range.1; simp at this; omega
      set q := m / 2^28 with hq_def
      have hq_le : q ≤ 7 := by omega
      have hbyte_eq : byte = 127 - q := by
        rw [hbyte_def]; simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
        rw [Int.negSucc_emod _ (show (0 : Int) < 128 from by decide)]
        have : (↑q : Int) % 128 = ↑q := by omega
        rw [this]; push_cast; omega
      have huval_eq : uval = 2^32 - (m+1) := by
        rw [huval_def, BitVec.toNat_ofInt,
          Int.negSucc_emod _ (by positivity : (0 : Int) < ↑(2^32 : Nat))]
        simp; omega
      have huval_div : uval / 2^28 = 15 - q := by rw [huval_eq]; omega
      rw [hbyte_eq]
      conv_rhs => rw [show i = i - 28 + 28 from by omega]
      rw [← @Nat.testBit_div_two_pow 28 uval (i - 28)]
      rw [huval_div]
      set j := i - 28; have hj : j < 4 := by omega
      interval_cases q <;> interval_cases j <;> decide
  · -- i ≥ 32 but i < 28: impossible
    omega
  · -- i ≥ 32: both sides zero
    simp [hi32]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le huval_lt (Nat.pow_le_pow_right (by omega) (by omega)))

set_option maxHeartbeats 3200000 in
/-- Core invariant for signed 32-bit roundtrip. -/
private theorem decodeS32_go_encodeSigned_inv
    (v v_orig : Int) (acc : ByteArray) (result : Nat) (fuel : Nat)
    (hle : acc.size ≤ 4)
    (hfuel : fuel + acc.size ≥ 5)
    (hv_range : -(2^31 : Int) ≤ v_orig ∧ v_orig < 2^31)
    (hv : v = v_orig.shiftRight (7 * acc.size))
    (huval : (BitVec.ofInt 32 v_orig).toNat < 2^32)
    (hresult : result = (BitVec.ofInt 32 v_orig).toNat % 2^(7 * acc.size)) :
    decodeS32.go (encodeSigned v acc fuel) 0 result (7 * acc.size) acc.size =
      some (Radix.Int32.fromBitVec (BitVec.ofInt 32 v_orig),
            (encodeSigned v acc fuel).size) := by
  induction fuel generalizing v acc result with
  | zero => exfalso; omega
  | succ k ih =>
    have hbyte_lt : (v % 128).toNat < 128 := emod128_toNat_lt' v
    match hdone : signedDone v with
    | true =>
      -- ─── Terminal case ───
      rw [encodeSigned_base' v acc k hdone]
      set byte := (v % 128).toNat with hbyte_def
      set uval := (BitVec.ofInt 32 v_orig).toNat with huval_def
      set shift := 7 * acc.size with hshift_def
      -- Unfold decoder one step
      unfold decodeS32.go
      simp only [show ¬(acc.size ≥ 5) from by omega, ite_false,
                 show 0 + acc.size = acc.size from by omega]
      simp only [show acc.size < (acc.push byte.toUInt8).size from by
        rw [ByteArray.size_push]; omega, dite_true]
      rw [ba_push_getElem_eq]
      have htoNat : byte.toUInt8.toNat = byte :=
        UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega)
      simp only [htoNat]
      rw [and_0x7F_eq byte, Nat.mod_eq_of_lt (by omega : byte < 128)]
      -- Overflow check: actual decoder form is (i == 4 && value > 0x07 && value < 0x78)
      by_cases hov_byte4 : (acc.size == 4 && decide (byte > 0x07) && decide (byte < 0x78)) = true
      · -- byte 4 overflow: contradiction with valid range
        exfalso
        simp [beq_iff_eq] at hov_byte4
        obtain ⟨⟨h4, hgt⟩, hlt⟩ := hov_byte4
        rw [h4] at hshift_def
        rw [show 7 * 4 = 28 from by omega] at hshift_def
        rw [hshift_def] at hv
        have hbv : byte = (v_orig.shiftRight 28 % 128).toNat := by rw [hbyte_def, hv]
        -- overflow_check_byte4_s32 uses value := byte &&& 0x7F; since byte < 128, &&& 0x7F is identity
        have hid : (v_orig.shiftRight 28 % 128).toNat &&& 0x7F =
                   (v_orig.shiftRight 28 % 128).toNat := by
          rw [show (0x7F : Nat) = 2^7 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
          exact Nat.mod_eq_of_lt (by rw [← hbv]; omega)
        have hovf' : (v_orig.shiftRight 28 % 128).toNat &&& 0x7F > 0x07 ∧
                     (v_orig.shiftRight 28 % 128).toNat &&& 0x7F < 0x78 := by
          rw [hid, ← hbv]; exact ⟨hgt, hlt⟩
        exact overflow_check_byte4_s32 v_orig hv_range hovf'
      · -- Overflow check passed
        -- No continuation bit (byte < 128)
        rw [and_0x80_eq_zero_of_lt_128 hbyte_lt]
        simp only [beq_self_eq_true, ↓reduceIte]
        -- Eliminate overflow check if
        have hov_cond : (acc.size == 4 && decide (byte > 0x07) && decide (byte < 0x78)) = false := by
          exact Bool.eq_false_iff.mpr (fun h => hov_byte4 h)
        simp only [hov_cond, Bool.false_eq_true, ↓reduceIte]
        -- Split on acc.size = 4 (shift = 28) vs acc.size ≤ 3 (shift ≤ 21)
        by_cases h4 : acc.size = 4
        · -- ─── Byte 4 case (acc.size = 4, shift = 28, shift' = 35 ≥ 32) ───
          have hshift28 : shift = 28 := by rw [hshift_def, h4]
          set shift' := shift + 7 with hshift'_def
          have hsp32 : ¬(shift' < 32) := by omega
          rw [ByteArray.size_push]
          -- Sign extension if: shift' ≥ 32 → condition is false
          have hse_cond : (decide (shift' < 32) && (byte &&& 0x40 != 0)) = false := by
            simp [decide_eq_false hsp32]
          simp only [hse_cond, Bool.false_eq_true, ↓reduceIte]
          -- Goal: some (fromBitVec (BitVec.ofNat 32 (result ||| byte <<< shift)), ...) = ...
          have hbyte_v : byte = (v_orig.shiftRight 28 % 128).toNat := by
            rw [hbyte_def, hv, hshift_def, h4]
          have hresult28 : result = uval % 2^28 := by
            rw [hresult, hshift_def, h4]
          congr 1; congr 1; congr 1
          rw [hshift28, hbyte_v]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ofNat]
          exact terminal_byte4_result_mod v_orig hv_range result hresult28
        · -- ─── Byte 0-3 case (acc.size ≤ 3, shift ≤ 21) ───
          have hacc_le3 : acc.size ≤ 3 := by omega
          -- Connection: byte comes from uval
          have hconn : byte = uval / 2^shift % 128 := by
            rw [hbyte_def, hv, hshift_def]
            exact conn_signed_s32 v_orig (7 * acc.size) hv_range (by omega)
              (dvd_mul_right 7 acc.size)
          -- result' = uval % 2^(shift + 7)
          have hresult' : result ||| (byte <<< shift) = uval % 2^(shift + 7) := by
            rw [hresult, hconn, hshift_def]
            exact or_shift_mod_eq' uval (7 * acc.size)
          -- signedDone case split
          have hcases := Bool.or_eq_true_iff.mp hdone
          set shift' := shift + 7 with hshift'_def
          rw [ByteArray.size_push]
          -- Now the goal involves: if shift' < 32 && (byte &&& 0x40 != 0) then sign_ext else no_sign_ext
          rcases hcases with hcase_pos | hcase_neg
          · -- Case A: rest == 0 && signBit == 0
            have hrest_eq := Bool.and_eq_true_iff.mp hcase_pos
            have hrest0 := hrest_eq.1
            have hsb0 := hrest_eq.2
            -- signBit == 0 → byte &&& 0x40 = 0
            have h0x40 : byte &&& 0x40 = 0 :=
              signBit_zero_implies_and_0x40_eq_zero byte hbyte_lt hsb0
            -- No sign extension (byte &&& 0x40 = 0 → the condition is false)
            simp only [h0x40, show (0 != 0 : Bool) = false from rfl, Bool.and_false,
                       Bool.false_eq_true, ↓reduceIte]
            -- result' = uval
            rw [hresult']
            have hupper : uval / 2^shift' = 0 := by
              rw [hshift'_def, hshift_def]
              exact terminal_rest_zero' v_orig (7 * acc.size + 7) hv_range (by omega)
                (by rw [show 7 * acc.size + 7 = (7 * acc.size) + 7 from by omega,
                         ← int_shiftRight_add, ← hv]; exact hrest0)
            have : uval % 2^shift' = uval :=
              Nat.mod_eq_of_lt (by have := Nat.div_add_mod uval (2^shift'); rw [hupper] at this; omega)
            rw [this]
            congr 1; congr 1; congr 1; apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_ofNat, huval_def, Nat.mod_eq_of_lt (BitVec.isLt _)]
          · -- Case B: rest == -1 && signBit != 0
            have hrest_eq := Bool.and_eq_true_iff.mp hcase_neg
            have hrestn1 := hrest_eq.1
            have hsb1 := hrest_eq.2
            -- signBit != 0 → byte &&& 0x40 ≠ 0
            have h0x40_ne : byte &&& 0x40 ≠ 0 :=
              signBit_ne_implies_and_0x40_ne_zero byte hbyte_lt hsb1
            -- Need to split on shift' < 32
            by_cases hsp32 : shift' < 32
            · -- shift' < 32: sign extension
              have hse_true : (decide (shift' < 32) && (byte &&& 0x40 != 0)) = true := by
                simp [hsp32, bne_iff_ne.mpr h0x40_ne]
              simp only [hse_true, ↓reduceIte]
              -- result' ||| mask = uval
              rw [hresult']
              have hshift'_le : shift' ≤ 28 := by rw [hshift'_def, hshift_def]; omega
              have hshift'_pos : 0 < shift' := by rw [hshift'_def]; omega
              have hshift'_div7 : 7 ∣ shift' := by
                rw [hshift'_def, hshift_def]; exact dvd_mul_right 7 (acc.size + 1)
              rw [mask_helper_s32 shift' hshift'_le hshift'_pos hshift'_div7]
              have hupper : uval / 2^shift' = 2^(32 - shift') - 1 := by
                rw [hshift'_def, hshift_def]
                exact terminal_rest_neg_one' v_orig (7 * acc.size + 7) hv_range (by omega)
                  (by rw [show 7 * acc.size + 7 = (7 * acc.size) + 7 from by omega,
                           ← int_shiftRight_add, ← hv]; exact hrestn1)
              -- Combine: uval % 2^shift' ||| (2^32 - 2^shift') = uval
              have hand_zero : (uval % 2^shift') &&& (2^32 - 2^shift') = 0 := by
                apply Nat.eq_of_testBit_eq; intro i
                simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.zero_testBit]
                by_cases hi : i < shift'
                · simp only [hi, decide_true, Bool.true_and]
                  have hsub : 2^32 - 2^shift' = (2^(32 - shift') - 1) <<< shift' := by
                    rw [Nat.shiftLeft_eq]; interval_cases shift' <;> omega
                  rw [hsub, Nat.testBit_shiftLeft]
                  simp [show ¬(shift' ≤ i) from by omega]
                · simp [hi]
              have := or_eq_add_of_and_eq_zero (uval % 2^shift') (2^32 - 2^shift') hand_zero
              rw [this]
              have hcombine := sign_ext_arith_s32 uval shift' huval hshift'_le hshift'_div7 hshift'_pos hupper
              rw [hcombine]
              congr 1; congr 1; congr 1; apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_ofNat, huval_def, Nat.mod_eq_of_lt (BitVec.isLt _)]
            · -- shift' ≥ 32: impossible since acc.size ≤ 3 → shift' ≤ 28
              exfalso; rw [hshift'_def, hshift_def] at hsp32; omega
    | false =>
      -- ─── Continuation case ───
      have hacc_le3 : acc.size ≤ 3 := by
        by_contra hc; push_neg at hc
        have h4 : acc.size = 4 := by omega
        rw [h4, show 7 * 4 = 28 from by omega] at hv
        have := signedDone_at_byte4 v_orig hv_range
        rw [← hv] at this; exact absurd this (by rw [hdone]; decide)
      rw [encodeSigned_step' v acc k hdone]
      set acc' := acc.push ((v % 128).toNat ||| 0x80).toUInt8 with hacc'_def
      have hacc'_size : acc'.size = acc.size + 1 := ByteArray.size_push
      unfold decodeS32.go
      simp only [show ¬(acc.size ≥ 5) from by omega, ite_false,
                 show 0 + acc.size = acc.size from by omega]
      have hpos : acc.size < (encodeSigned (v.shiftRight 7) acc' k).size := by
        have := encodeSigned_size_pos (v.shiftRight 7) acc' k (by omega)
        rw [hacc'_size] at this; omega
      simp only [show (acc.size < (encodeSigned (v.shiftRight 7) acc' k).size) = True from
        propext ⟨fun _ => trivial, fun _ => hpos⟩, dite_true]
      have hbyte_read : (encodeSigned (v.shiftRight 7) acc' k)[acc.size]'hpos =
          ((v % 128).toNat ||| 0x80).toUInt8 := by
        rw [encodeSigned_prefix' (v.shiftRight 7) acc' k acc.size
              (by rw [hacc'_size]; omega) hpos]
        exact ba_push_getElem_eq acc ((v % 128).toNat ||| 0x80).toUInt8
      rw [hbyte_read]
      have hmod : (v % 128).toNat < 128 := hbyte_lt
      have htoNat2 : ((v % 128).toNat ||| 0x80).toUInt8.toNat = (v % 128).toNat ||| 0x80 :=
        UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; exact or_0x80_lt_256' hmod)
      simp only [htoNat2]
      rw [or_0x80_and_0x7F_eq hmod]
      -- Overflow check: acc.size ≤ 3, so acc.size == 4 is false
      simp only [show ¬(acc.size == 4) from by rw [beq_iff_eq]; omega,
                 Bool.false_and]
      -- Continuation bit is set
      simp only [or_0x80_and_0x80_ne_zero']
      have hshift' : 7 * acc.size + 7 = 7 * acc'.size := by rw [hacc'_size]; omega
      have hconn : (v % 128).toNat =
          (BitVec.ofInt 32 v_orig).toNat / 2^(7 * acc.size) % 128 := by
        rw [hv]
        exact conn_signed_s32 v_orig (7 * acc.size) hv_range (by omega)
          (dvd_mul_right 7 acc.size)
      have hresult' : result ||| ((v % 128).toNat <<< (7 * acc.size)) =
          (BitVec.ofInt 32 v_orig).toNat % 2^(7 * acc'.size) := by
        rw [hresult, hconn, hacc'_size,
            show 7 * (acc.size + 1) = 7 * acc.size + 7 from by omega]
        exact or_shift_mod_eq' (BitVec.ofInt 32 v_orig).toNat (7 * acc.size)
      rw [hshift']
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show acc.size + 1 = acc'.size from hacc'_size.symm]
      exact ih (v.shiftRight 7) acc'
        (result ||| ((v % 128).toNat <<< (7 * acc.size)))
        (by rw [hacc'_size]; omega)
        (by rw [hacc'_size]; omega)
        (by rw [hacc'_size, show 7 * (acc.size + 1) = 7 * acc.size + 7 from by omega,
                ← int_shiftRight_add, ← hv])
        hresult'

/-- Decoding an encoded signed 32-bit value yields the original value. -/
theorem decodeS32_encodeS32_roundtrip (x : Radix.Int32) :
    decodeS32 (encodeS32 x) 0 = some (x, (encodeS32 x).size) := by
  unfold encodeS32 decodeS32
  set v := x.toInt with hv_def
  have hv_range : -(2^31 : Int) ≤ v ∧ v < 2^31 := by
    constructor
    · exact BitVec.le_toInt (w := 32) x.val.toBitVec
    · exact BitVec.toInt_lt (w := 32)
  have := decodeS32_go_encodeSigned_inv v v ByteArray.empty 0 5
    (by rw [ba_empty_size]; omega)
    (by rw [ba_empty_size])
    hv_range
    (by rw [ba_empty_size, show 7 * 0 = 0 from by omega]; exact Int.shiftRight_zero v |>.symm)
    (BitVec.isLt _)
    (by rw [ba_empty_size, show 7 * 0 = 0 from by omega]; simp [Nat.mod_one])
  rw [ba_empty_size, show 7 * 0 = 0 from by omega] at this
  convert this using 1
  congr 1; congr 1
  exact (fromBitVec32_signed_roundtrip x).symm

/-! ================================================================ -/
/-! ## S64 Round-Trip                                                 -/
/-! ================================================================ -/

/-! ### Unsigned value conversion (S64) -/

private theorem uval_pos_s64 (n : Nat) (hn : n < 2^63) :
    (BitVec.ofInt 64 (Int.ofNat n)).toNat = n := by
  rw [BitVec.toNat_ofInt]; push_cast; exact Nat.mod_eq_of_lt (by omega)

private theorem uval_neg_s64 (m : Nat) (hm : m < 2^63) :
    (BitVec.ofInt 64 (Int.negSucc m)).toNat = 2^64 - (m + 1) := by
  rw [BitVec.toNat_ofInt, Int.negSucc_emod _ (by positivity : (0 : Int) < ↑(2^64 : Nat))]
  simp; omega

/-! ### Connection lemma for negative (S64) -/

set_option maxHeartbeats 1600000 in
private theorem conn_neg_s64 (m : Nat) (k : Nat) (hm : m < 2^63)
    (hk : k ≤ 56) (hk7 : 7 ∣ k) :
    ((Int.negSucc m).shiftRight k % 128).toNat = (2^64 - (m + 1)) / 2^k % 128 := by
  simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
  rw [Int.negSucc_emod _ (show (0 : Int) < 128 from by decide)]
  interval_cases k <;> simp_all <;> omega

/-! ### Unified connection lemma (S64) -/

set_option maxHeartbeats 1600000 in
private theorem conn_signed_s64 (v_orig : Int) (shift : Nat)
    (hv_range : -(2^63 : Int) ≤ v_orig ∧ v_orig < 2^63)
    (hshift : shift ≤ 56) (hshift7 : 7 ∣ shift) :
    (v_orig.shiftRight shift % 128).toNat =
    (BitVec.ofInt 64 v_orig).toNat / 2^shift % 128 := by
  rcases v_orig with n | m
  · have hn : n < 2^63 := by
      have := hv_range.2
      simp only [show Int.ofNat n = (↑n : Int) from rfl] at this; omega
    rw [conn_pos n shift, uval_pos_s64 n hn]
  · have hm : m < 2^63 := by
      have := hv_range.1
      simp only [show Int.negSucc m = -(↑m + 1 : Int) from rfl] at this; omega
    rw [conn_neg_s64 m shift hm hshift hshift7, uval_neg_s64 m hm]

/-! ### signedDone at byte 9 -/

private theorem signedDone_at_byte9 (v_orig : Int)
    (hv_range : -(2^63 : Int) ≤ v_orig ∧ v_orig < 2^63) :
    signedDone (v_orig.shiftRight 63) = true := by
  rcases v_orig with n | m
  · have : n < 2^63 := by
      have := hv_range.2
      simp only [show Int.ofNat n = (↑n : Int) from rfl] at this; omega
    simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    set v := n / 2^63; have : v ≤ 0 := by omega
    interval_cases v; decide
  · have : m < 2^63 := by
      have := hv_range.1
      simp only [show Int.negSucc m = -(↑m + 1 : Int) from rfl] at this; omega
    simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    set v := m / 2^63; have : v ≤ 0 := by omega
    interval_cases v; decide

/-! ### Terminal rest conditions (S64) -/

private theorem terminal_rest_zero_s64 (n_orig : Int) (s : Nat)
    (hn : -2 ^ 63 ≤ n_orig ∧ n_orig < 2 ^ 63) (_hs : s ≤ 70)
    (hrest : (n_orig.shiftRight s == 0) = true) :
    (BitVec.ofInt 64 n_orig).toNat / 2 ^ s = 0 := by
  rcases n_orig with a | m
  · simp only [Int.shiftRight, beq_iff_eq] at hrest
    have hshift : a >>> s = 0 := by
      cases h : a >>> s with
      | zero => rfl
      | succ n => exfalso; rw [h] at hrest; simp only [Int.ofNat_eq_natCast] at hrest; omega
    have ha_div : a / 2 ^ s = 0 := by omega
    have ha_lt : a < 2 ^ 64 := by simp only [Int.ofNat_eq_natCast] at hn; omega
    rw [BitVec.toNat_ofInt]; simp only [Int.ofNat_eq_natCast]
    have h1 : (↑a : Int) % (↑(2 ^ 64 : Nat) : Int) = ↑a := by omega
    simp only [h1, Int.toNat_natCast]; exact ha_div
  · simp only [Int.shiftRight, beq_iff_eq] at hrest
    exact absurd hrest Int.noConfusion

set_option maxHeartbeats 6400000 in
private theorem terminal_rest_neg_one_s64 (n_orig : Int) (s : Nat)
    (hn : -2 ^ 63 ≤ n_orig ∧ n_orig < 2 ^ 63) (hs : s < 64)
    (hrest : (n_orig.shiftRight s == -1) = true) :
    (BitVec.ofInt 64 n_orig).toNat / 2 ^ s = 2 ^ (64 - s) - 1 := by
  rcases n_orig with a | m
  · simp only [Int.shiftRight, beq_iff_eq] at hrest
    have : (0 : Int) ≤ Int.ofNat (a >>> s) := Int.natCast_nonneg _; omega
  · simp only [Int.shiftRight, beq_iff_eq] at hrest
    have hms : m >>> s = 0 := by
      have h : Int.negSucc (m >>> s) = Int.negSucc 0 := by
        simp only [Int.negSucc_eq] at hrest ⊢; omega
      exact Int.negSucc.inj h
    have hm_div : m / 2 ^ s = 0 := by omega
    have hm_bound : m < 2 ^ 63 := by simp only [Int.negSucc_eq] at hn; omega
    have hm_lt : m + 1 ≤ 2 ^ s := by
      have := Nat.div_add_mod m (2 ^ s); rw [hm_div] at this; omega
    rw [BitVec.toNat_ofInt]; simp only [Int.negSucc_eq]
    show (-(↑m + 1 : Int) % (↑(2 ^ 64 : Nat) : Int)).toNat / 2 ^ s = 2 ^ (64 - s) - 1
    have hmod : (-(↑m + 1 : Int)) % (↑(2 ^ 64 : Nat) : Int) = ↑(2 ^ 64 - (m + 1) : Nat) := by
      omega
    rw [hmod, Int.toNat_natCast]
    interval_cases s <;> omega

/-! ### Sign extension helpers (S64) -/

private theorem neg_terminal_upper_s64 (m shift' : Nat) (hm : m < 2^shift')
    (hshift' : shift' ≤ 63) (h7 : 7 ∣ shift') (hsp : 0 < shift') :
    (2^64 - (m + 1)) / 2^shift' = 2^(64 - shift') - 1 := by
  interval_cases shift' <;> omega

private theorem sign_ext_arith_s64 (uval shift' : Nat) (_huval : uval < 2^64)
    (hshift' : shift' ≤ 63) (h7 : 7 ∣ shift') (hsp : 0 < shift')
    (h_upper : uval / 2^shift' = 2^(64 - shift') - 1) :
    uval % 2^shift' + (2^64 - 2^shift') = uval := by
  have := Nat.div_add_mod uval (2^shift')
  interval_cases shift' <;> omega

private theorem mask_helper_s64 (shift' : Nat) (hsp : shift' ≤ 63) (hsp0 : 0 < shift') (hsp7 : 7 ∣ shift') :
    0xFFFFFFFFFFFFFFFF - ((1 <<< shift') - 1) = 2^64 - 2^shift' := by
  rw [Nat.shiftLeft_eq, show 0xFFFFFFFFFFFFFFFF = 2^64 - 1 from by decide]
  interval_cases shift' <;> omega

/-! ### Overflow check for byte 9 (S64) -/

/-- At byte 9 (shift=63), the overflow check `value != 0x00 && value != 0x7F` is false
    for valid 64-bit signed values. The valid byte values are exactly 0 (positive) or 127 (negative). -/
private theorem overflow_check_byte9_s64 (v_orig : Int)
    (hv : -(2^63 : Int) ≤ v_orig ∧ v_orig < 2^63) :
    let v := v_orig.shiftRight 63
    let byte := (v % 128).toNat
    let value := byte &&& 0x7F
    ¬(value != 0x00 ∧ value != 0x7F) := by
  rcases v_orig with n | m
  · simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    have hn : n < 2^63 := by simp at hv; omega
    have hb : n / 2^63 = 0 := by omega
    simp only [hb]; decide
  · simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
    have hm : m < 2^63 := by simp [Int.negSucc_eq] at hv; omega
    have hb : m / 2^63 = 0 := by omega
    simp only [hb]; decide

/-! ### Terminal byte 9 result mod (S64) -/

set_option maxHeartbeats 1600000 in
/-- Terminal byte 9 (acc.size = 9, shift = 63): the combined result mod 2^64 equals uval. -/
private theorem terminal_byte9_result_mod (v_orig : Int)
    (hv_range : -(2^63 : Int) ≤ v_orig ∧ v_orig < 2^63)
    (result : Nat) (hresult : result = (BitVec.ofInt 64 v_orig).toNat % 2^63) :
    (result ||| ((v_orig.shiftRight 63 % 128).toNat <<< 63)) % 2^64 =
    (BitVec.ofInt 64 v_orig).toNat := by
  set uval := (BitVec.ofInt 64 v_orig).toNat with huval_def
  set byte := (v_orig.shiftRight 63 % 128).toNat with hbyte_def
  have huval_lt : uval < 2^64 := BitVec.isLt _
  rw [hresult]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi64 : i < 64 <;> by_cases hi63 : i < 63
  · -- i < 63: low bits only
    have : ¬(63 ≤ i) := by omega
    simp [hi64, hi63, this]
  · -- i = 63: high bit (byte)
    have h63 : 63 ≤ i := by omega
    have hi_eq : i = 63 := by omega
    simp only [hi64, hi63, h63, decide_true, decide_false, Bool.true_and,
               Bool.false_and, Bool.false_or, Bool.true_and]
    rcases v_orig with n | m
    · -- Positive case
      have hn : n < 2^63 := by have := hv_range.2; simp at this; omega
      simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow, Int.ofNat_eq_natCast] at hbyte_def huval_def
      have hbyte_simp : byte = n / 2^63 := by
        rw [hbyte_def]; push_cast; omega
      have huval_simp : uval = n := by
        rw [huval_def, BitVec.toNat_ofInt]; push_cast; exact Nat.mod_eq_of_lt (by omega)
      rw [hbyte_simp, huval_simp, hi_eq]
      show (n / 2 ^ 63).testBit 0 = n.testBit 63
      rw [← @Nat.testBit_div_two_pow 63 n 0]
    · -- Negative case
      have hm : m < 2^63 := by have := hv_range.1; simp at this; omega
      have hm_div : m / 2^63 = 0 := by omega
      have hbyte_eq : byte = 127 := by
        rw [hbyte_def]; simp only [Int.shiftRight, Nat.shiftRight_eq_div_pow]
        simp only [hm_div]
        decide
      have huval_eq : uval = 2^64 - (m+1) := by
        rw [huval_def, BitVec.toNat_ofInt,
          Int.negSucc_emod _ (by positivity : (0 : Int) < ↑(2^64 : Nat))]
        simp; omega
      rw [hbyte_eq, huval_eq, hi_eq]
      -- Need: (127).testBit 0 = (2^64 - (m+1)).testBit 63
      -- 127.testBit 0 = true
      -- (2^64 - (m+1)).testBit 63 = true since m < 2^63, so 2^64-(m+1) ≥ 2^63
      simp only [show Nat.testBit 127 0 = true from by decide]
      symm; rw [Nat.testBit]; simp only [Nat.shiftRight_eq_div_pow]
      have : (2^64 - (m+1)) / 2^63 = 1 := by omega
      rw [this]; rfl
  · omega
  · simp [hi64]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le huval_lt (Nat.pow_le_pow_right (by omega) (by omega)))

set_option maxHeartbeats 3200000 in
/-- Core invariant for signed 64-bit roundtrip. -/
private theorem decodeS64_go_encodeSigned_inv
    (v v_orig : Int) (acc : ByteArray) (result : Nat) (fuel : Nat)
    (hle : acc.size ≤ 9)
    (hfuel : fuel + acc.size ≥ 10)
    (hv_range : -(2^63 : Int) ≤ v_orig ∧ v_orig < 2^63)
    (hv : v = v_orig.shiftRight (7 * acc.size))
    (huval : (BitVec.ofInt 64 v_orig).toNat < 2^64)
    (hresult : result = (BitVec.ofInt 64 v_orig).toNat % 2^(7 * acc.size)) :
    decodeS64.go (encodeSigned v acc fuel) 0 result (7 * acc.size) acc.size =
      some (Radix.Int64.fromBitVec (BitVec.ofInt 64 v_orig),
            (encodeSigned v acc fuel).size) := by
  induction fuel generalizing v acc result with
  | zero => exfalso; omega
  | succ k ih =>
    have hbyte_lt : (v % 128).toNat < 128 := emod128_toNat_lt' v
    match hdone : signedDone v with
    | true =>
      -- ─── Terminal case ───
      rw [encodeSigned_base' v acc k hdone]
      set byte := (v % 128).toNat with hbyte_def
      set uval := (BitVec.ofInt 64 v_orig).toNat with huval_def
      set shift := 7 * acc.size with hshift_def
      -- Unfold decoder one step
      unfold decodeS64.go
      simp only [show ¬(acc.size ≥ 10) from by omega, ite_false,
                 show 0 + acc.size = acc.size from by omega]
      simp only [show acc.size < (acc.push byte.toUInt8).size from by
        rw [ByteArray.size_push]; omega, dite_true]
      rw [ba_push_getElem_eq]
      have htoNat : byte.toUInt8.toNat = byte :=
        UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; omega)
      simp only [htoNat]
      rw [and_0x7F_eq byte, Nat.mod_eq_of_lt (by omega : byte < 128)]
      -- Overflow check: actual decoder form is (i == 9 && value != 0x00 && value != 0x7F)
      -- We need to eliminate: if acc.size == 9 && decide (byte ≠ 0) && decide (byte ≠ 127) then none else ...
      by_cases hov_byte9 : (acc.size == 9 && (byte != 0x00) && (byte != 0x7F)) = true
      · -- byte 9 overflow: contradiction with valid range
        exfalso
        simp only [Bool.and_eq_true] at hov_byte9
        obtain ⟨⟨h9, hne0⟩, hne7f⟩ := hov_byte9
        rw [beq_iff_eq] at h9
        rw [h9] at hshift_def
        rw [show 7 * 9 = 63 from by omega] at hshift_def
        rw [hshift_def] at hv
        have hbv : byte = (v_orig.shiftRight 63 % 128).toNat := by rw [hbyte_def, hv]
        have hid : (v_orig.shiftRight 63 % 128).toNat &&& 0x7F =
                   (v_orig.shiftRight 63 % 128).toNat := by
          rw [show (0x7F : Nat) = 2^7 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod]
          exact Nat.mod_eq_of_lt (by rw [← hbv]; omega)
        have hovf' : ¬(((v_orig.shiftRight 63 % 128).toNat &&& 0x7F != 0x00) = true ∧
                       ((v_orig.shiftRight 63 % 128).toNat &&& 0x7F != 0x7F) = true) :=
          overflow_check_byte9_s64 v_orig hv_range
        rw [hid] at hovf'
        rw [← hbv] at hovf'
        exact hovf' ⟨hne0, hne7f⟩
      · -- Overflow check passed
        rw [and_0x80_eq_zero_of_lt_128 hbyte_lt]
        simp only [beq_self_eq_true, ↓reduceIte]
        -- Eliminate overflow check if
        have hov_cond : (acc.size == 9 && (byte != 0x00) && (byte != 0x7F)) = false := by
          exact Bool.eq_false_iff.mpr (fun h => hov_byte9 h)
        simp only [hov_cond, Bool.false_eq_true, ↓reduceIte]
        -- Split on acc.size = 9 (shift = 63) vs acc.size ≤ 8 (shift ≤ 56)
        by_cases h9 : acc.size = 9
        · -- ─── Byte 9 case (acc.size = 9, shift = 63, shift' = 70 ≥ 64) ───
          have hshift63 : shift = 63 := by rw [hshift_def, h9]
          set shift' := shift + 7 with hshift'_def
          have hsp64 : ¬(shift' < 64) := by omega
          rw [ByteArray.size_push]
          -- Sign extension if: shift' ≥ 64 → condition is false
          have hse_cond : (decide (shift' < 64) && (byte &&& 0x40 != 0)) = false := by
            simp [decide_eq_false hsp64]
          simp only [hse_cond, Bool.false_eq_true, ↓reduceIte]
          -- Goal: some (fromBitVec (BitVec.ofNat 64 (result ||| byte <<< shift)), ...) = ...
          have hbyte_v : byte = (v_orig.shiftRight 63 % 128).toNat := by
            rw [hbyte_def, hv, hshift_def, h9]
          have hresult63 : result = uval % 2^63 := by
            rw [hresult, hshift_def, h9]
          congr 1; congr 1; congr 1
          rw [hshift63, hbyte_v]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ofNat]
          exact terminal_byte9_result_mod v_orig hv_range result hresult63
        · -- ─── Byte 0-8 case (acc.size ≤ 8, shift ≤ 56) ───
          have hacc_le8 : acc.size ≤ 8 := by omega
          -- Connection: byte comes from uval
          have hconn : byte = uval / 2^shift % 128 := by
            rw [hbyte_def, hv, hshift_def]
            exact conn_signed_s64 v_orig (7 * acc.size) hv_range (by omega)
              (dvd_mul_right 7 acc.size)
          -- result' = uval % 2^(shift + 7)
          have hresult' : result ||| (byte <<< shift) = uval % 2^(shift + 7) := by
            rw [hresult, hconn, hshift_def]
            exact or_shift_mod_eq' uval (7 * acc.size)
          -- signedDone case split
          have hcases := Bool.or_eq_true_iff.mp hdone
          set shift' := shift + 7 with hshift'_def
          rw [ByteArray.size_push]
          rcases hcases with hcase_pos | hcase_neg
          · -- Case A: rest == 0 && signBit == 0
            have hrest_eq := Bool.and_eq_true_iff.mp hcase_pos
            have hrest0 := hrest_eq.1
            have hsb0 := hrest_eq.2
            have h0x40 : byte &&& 0x40 = 0 :=
              signBit_zero_implies_and_0x40_eq_zero byte hbyte_lt hsb0
            simp only [h0x40, show (0 != 0 : Bool) = false from rfl, Bool.and_false,
                       Bool.false_eq_true, ↓reduceIte]
            rw [hresult']
            have hupper : uval / 2^shift' = 0 := by
              rw [hshift'_def, hshift_def]
              exact terminal_rest_zero_s64 v_orig (7 * acc.size + 7) hv_range (by omega)
                (by rw [show 7 * acc.size + 7 = (7 * acc.size) + 7 from by omega,
                         ← int_shiftRight_add, ← hv]; exact hrest0)
            have : uval % 2^shift' = uval :=
              Nat.mod_eq_of_lt (by have := Nat.div_add_mod uval (2^shift'); rw [hupper] at this; omega)
            rw [this]
            congr 1; congr 1; congr 1; apply BitVec.eq_of_toNat_eq
            simp only [BitVec.toNat_ofNat, huval_def, Nat.mod_eq_of_lt (BitVec.isLt _)]
          · -- Case B: rest == -1 && signBit != 0
            have hrest_eq := Bool.and_eq_true_iff.mp hcase_neg
            have hrestn1 := hrest_eq.1
            have hsb1 := hrest_eq.2
            have h0x40_ne : byte &&& 0x40 ≠ 0 :=
              signBit_ne_implies_and_0x40_ne_zero byte hbyte_lt hsb1
            by_cases hsp64 : shift' < 64
            · -- shift' < 64: sign extension
              have hse_true : (decide (shift' < 64) && (byte &&& 0x40 != 0)) = true := by
                simp [hsp64, bne_iff_ne.mpr h0x40_ne]
              simp only [hse_true, ↓reduceIte]
              rw [hresult']
              have hshift'_le : shift' ≤ 63 := by omega
              have hshift'_pos : 0 < shift' := by rw [hshift'_def]; omega
              have hshift'_div7 : 7 ∣ shift' := by
                rw [hshift'_def, hshift_def]; exact dvd_mul_right 7 (acc.size + 1)
              rw [mask_helper_s64 shift' hshift'_le hshift'_pos hshift'_div7]
              have hupper : uval / 2^shift' = 2^(64 - shift') - 1 := by
                rw [hshift'_def, hshift_def]
                exact terminal_rest_neg_one_s64 v_orig (7 * acc.size + 7) hv_range (by omega)
                  (by rw [show 7 * acc.size + 7 = (7 * acc.size) + 7 from by omega,
                           ← int_shiftRight_add, ← hv]; exact hrestn1)
              have hand_zero : (uval % 2^shift') &&& (2^64 - 2^shift') = 0 := by
                apply Nat.eq_of_testBit_eq; intro i
                simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.zero_testBit]
                by_cases hi : i < shift'
                · simp only [hi, decide_true, Bool.true_and]
                  have hsub : 2^64 - 2^shift' = (2^(64 - shift') - 1) <<< shift' := by
                    rw [Nat.shiftLeft_eq]; interval_cases shift' <;> omega
                  rw [hsub, Nat.testBit_shiftLeft]
                  simp [show ¬(shift' ≤ i) from by omega]
                · simp [hi]
              have := or_eq_add_of_and_eq_zero (uval % 2^shift') (2^64 - 2^shift') hand_zero
              rw [this]
              have hcombine := sign_ext_arith_s64 uval shift' huval hshift'_le hshift'_div7 hshift'_pos hupper
              rw [hcombine]
              congr 1; congr 1; congr 1; apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_ofNat, huval_def, Nat.mod_eq_of_lt (BitVec.isLt _)]
            · -- shift' ≥ 64: impossible since acc.size ≤ 8 → shift' ≤ 63
              exfalso; rw [hshift'_def, hshift_def] at hsp64; omega
    | false =>
      -- ─── Continuation case ───
      have hacc_le8 : acc.size ≤ 8 := by
        by_contra hc; push_neg at hc
        have h9 : acc.size = 9 := by omega
        rw [h9, show 7 * 9 = 63 from by omega] at hv
        have := signedDone_at_byte9 v_orig hv_range
        rw [← hv] at this; exact absurd this (by rw [hdone]; decide)
      rw [encodeSigned_step' v acc k hdone]
      set acc' := acc.push ((v % 128).toNat ||| 0x80).toUInt8 with hacc'_def
      have hacc'_size : acc'.size = acc.size + 1 := ByteArray.size_push
      unfold decodeS64.go
      simp only [show ¬(acc.size ≥ 10) from by omega, ite_false,
                 show 0 + acc.size = acc.size from by omega]
      have hpos : acc.size < (encodeSigned (v.shiftRight 7) acc' k).size := by
        have := encodeSigned_size_pos (v.shiftRight 7) acc' k (by omega)
        rw [hacc'_size] at this; omega
      simp only [show (acc.size < (encodeSigned (v.shiftRight 7) acc' k).size) = True from
        propext ⟨fun _ => trivial, fun _ => hpos⟩, dite_true]
      have hbyte_read : (encodeSigned (v.shiftRight 7) acc' k)[acc.size]'hpos =
          ((v % 128).toNat ||| 0x80).toUInt8 := by
        rw [encodeSigned_prefix' (v.shiftRight 7) acc' k acc.size
              (by rw [hacc'_size]; omega) hpos]
        exact ba_push_getElem_eq acc ((v % 128).toNat ||| 0x80).toUInt8
      rw [hbyte_read]
      have hmod : (v % 128).toNat < 128 := hbyte_lt
      have htoNat2 : ((v % 128).toNat ||| 0x80).toUInt8.toNat = (v % 128).toNat ||| 0x80 :=
        UInt8.toNat_ofNat_of_lt' (by unfold UInt8.size; exact or_0x80_lt_256' hmod)
      simp only [htoNat2]
      rw [or_0x80_and_0x7F_eq hmod]
      -- Overflow check: acc.size ≤ 8, so acc.size == 9 is false
      simp only [show ¬(acc.size == 9) from by rw [beq_iff_eq]; omega,
                 Bool.false_and]
      -- Continuation bit is set
      simp only [or_0x80_and_0x80_ne_zero']
      have hshift' : 7 * acc.size + 7 = 7 * acc'.size := by rw [hacc'_size]; omega
      have hconn : (v % 128).toNat =
          (BitVec.ofInt 64 v_orig).toNat / 2^(7 * acc.size) % 128 := by
        rw [hv]
        exact conn_signed_s64 v_orig (7 * acc.size) hv_range (by omega)
          (dvd_mul_right 7 acc.size)
      have hresult' : result ||| ((v % 128).toNat <<< (7 * acc.size)) =
          (BitVec.ofInt 64 v_orig).toNat % 2^(7 * acc'.size) := by
        rw [hresult, hconn, hacc'_size,
            show 7 * (acc.size + 1) = 7 * acc.size + 7 from by omega]
        exact or_shift_mod_eq' (BitVec.ofInt 64 v_orig).toNat (7 * acc.size)
      rw [hshift']
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show acc.size + 1 = acc'.size from hacc'_size.symm]
      exact ih (v.shiftRight 7) acc'
        (result ||| ((v % 128).toNat <<< (7 * acc.size)))
        (by rw [hacc'_size]; omega)
        (by rw [hacc'_size]; omega)
        (by rw [hacc'_size, show 7 * (acc.size + 1) = 7 * acc.size + 7 from by omega,
                ← int_shiftRight_add, ← hv])
        hresult'

private theorem fromBitVec64_signed_roundtrip (x : Radix.Int64) :
    Radix.Int64.fromBitVec (BitVec.ofInt 64 x.toInt) = x := by
  simp [Radix.Int64.fromBitVec, Radix.Int64.toInt, BitVec.ofInt_toInt]

/-- Decoding an encoded signed 64-bit value yields the original value. -/
theorem decodeS64_encodeS64_roundtrip (x : Radix.Int64) :
    decodeS64 (encodeS64 x) 0 = some (x, (encodeS64 x).size) := by
  unfold encodeS64 decodeS64
  set v := x.toInt with hv_def
  have hv_range : -(2^63 : Int) ≤ v ∧ v < 2^63 := by
    constructor
    · exact BitVec.le_toInt (w := 64) x.val.toBitVec
    · exact BitVec.toInt_lt (w := 64)
  have := decodeS64_go_encodeSigned_inv v v ByteArray.empty 0 10
    (by rw [ba_empty_size]; omega)
    (by rw [ba_empty_size])
    hv_range
    (by rw [ba_empty_size, show 7 * 0 = 0 from by omega]; exact Int.shiftRight_zero v |>.symm)
    (BitVec.isLt _)
    (by rw [ba_empty_size, show 7 * 0 = 0 from by omega]; simp [Nat.mod_one])
  rw [ba_empty_size, show 7 * 0 = 0 from by omega] at this
  convert this using 1
  congr 1; congr 1
  exact (fromBitVec64_signed_roundtrip x).symm

end Radix.Binary.Leb128
