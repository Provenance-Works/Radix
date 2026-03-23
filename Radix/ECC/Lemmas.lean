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

/-- Correcting a clean codeword leaves it unchanged. -/
theorem correct_encodeNibble (n : Nibble) :
    correct (encodeNibble n) = some (encodeNibble n) := by
  fin_cases n <;> decide

/-- Correcting any single-bit error preserves the encoded payload. -/
theorem decode_correct_single_bit (n : Nibble) (idx : Fin 7) :
  (match (correct (toByte (Spec.flipAt (Spec.ofNibble n) idx)) : Option UInt8) with
  | some corrected => decode corrected
  | none => none) = some n.val.toUInt8 := by
  fin_cases n <;> fin_cases idx <;> decide

end Radix.ECC
