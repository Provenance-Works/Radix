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

/-- Encoded Hamming(7,4) values always fit in the low seven bits. -/
theorem encodeNibble_isCodewordByte (n : Nibble) :
  Radix.ECC.isCodewordByte (Radix.ECC.encodeNibble n) = true := by
  fin_cases n <;> decide

/-- Decoding an encoded nibble returns the original data bits. -/
theorem decode_encodeNibble (n : Nibble) :
  Radix.ECC.decode (Radix.ECC.encodeNibble n) = some n.val.toUInt8 := by
  fin_cases n <;> decide

/-- Correcting any single-bit error preserves the encoded payload. -/
theorem decode_correct_single_bit (n : Nibble) (idx : Fin 7) :
    Option.bind (Radix.ECC.correct (Radix.ECC.toByte (Spec.flipAt (Spec.ofNibble n) idx)))
      Radix.ECC.decode = some n.val.toUInt8 := by
  fin_cases n <;> fin_cases idx <;> decide

end Radix.ECC
