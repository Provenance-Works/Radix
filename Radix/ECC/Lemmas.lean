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

open Spec

/-- Decoding an encoded nibble returns the original data bits. -/
theorem decode_encodeNibble (n : Nibble) :
    decode (encodeNibble n) = n.val.toUInt8 := by
  fin_cases n <;> decide

/-- Correcting any single-bit error preserves the encoded payload. -/
theorem decode_correct_single_bit (n : Nibble) (idx : Fin 7) :
    decode (toByte (Spec.flipAt (Spec.ofNibble n) idx) |> correct) = n.val.toUInt8 := by
  fin_cases n <;> fin_cases idx <;> decide

end Radix.ECC
