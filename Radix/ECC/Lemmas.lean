/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.ECC.Spec
import Radix.ECC.Ops

/-!
# Error Correction Proofs (Layer 3)
-/

set_option autoImplicit false

namespace Radix.ECC

/-- Freshly encoded codewords satisfy all parity equations. -/
theorem check_encodeNibble (n : Nibble) :
  check (encodeNibble n) = true := by
  fin_cases n <;> decide

/-- Decoding an encoded nibble returns the original data bits. -/
theorem decode_encodeNibble (n : Nibble) :
  decode (encodeNibble n) = some n.val.toUInt8 := by
  fin_cases n <;> decide

/-- Encoded nibbles are classified as already clean. -/
theorem status?_encodeNibble (n : Nibble) :
  Radix.ECC.status? (encodeNibble n) = some Radix.ECC.Status.clean := by
  fin_cases n <;> decide

/-- Encoded nibbles require no correction index. -/
theorem errorIndex?_encodeNibble (n : Nibble) :
  Radix.ECC.errorIndex? (encodeNibble n) = none := by
  fin_cases n <;> decide

/-- Correcting a clean codeword leaves it unchanged. -/
theorem correct_encodeNibble (n : Nibble) :
    correct (encodeNibble n) = some (encodeNibble n) := by
  fin_cases n <;> decide

/-- Decoding after correction agrees with decoding a clean encoded nibble. -/
theorem decodeAfterCorrect_encodeNibble (n : Nibble) :
  Radix.ECC.decodeAfterCorrect (encodeNibble n) = some n.val.toUInt8 := by
  fin_cases n <;> decide

/-- Single-bit corruption is classified at the flipped bit position. -/
theorem status?_single_bit (n : Nibble) (idx : Fin 7) :
  Radix.ECC.status? (toByte (Spec.flipAt (Spec.ofNibble n) idx)) = some (Radix.ECC.Status.corrected idx) := by
  fin_cases n <;> fin_cases idx <;> decide

/-- Correcting any single-bit error preserves the encoded payload. -/
theorem decode_correct_single_bit (n : Nibble) (idx : Fin 7) :
  (match (correct (toByte (Spec.flipAt (Spec.ofNibble n) idx)) : Option UInt8) with
  | some corrected => decode corrected
  | none => none) = some n.val.toUInt8 := by
  fin_cases n <;> fin_cases idx <;> decide

/-- Decoding after correction succeeds for any single-bit corruption. -/
theorem decodeAfterCorrect_single_bit (n : Nibble) (idx : Fin 7) :
  Radix.ECC.decodeAfterCorrect (toByte (Spec.flipAt (Spec.ofNibble n) idx)) = some n.val.toUInt8 := by
  fin_cases n <;> fin_cases idx <;> decide

end Radix.ECC
