/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.UTF8.Spec
import Radix.UTF8.Ops

/-!
# UTF-8 Proofs (Layer 3)

Basic correctness lemmas for the UTF-8 model.
-/

set_option autoImplicit false

namespace Radix.UTF8

open Spec

/-- Layer 2 encoded length agrees with the specification. -/
theorem encodedLength_eq_spec (s : Scalar) :
    encodedLength s = Spec.Scalar.byteCount s := by
  unfold encodedLength
  simpa using Spec.encode_length_eq_byteCount s

/-- Encoded UTF-8 bytes satisfy the specification-level well-formedness predicate. -/
theorem isWellFormed_encodeScalar (s : Scalar) :
    Spec.WellFormed (Spec.encode s) := by
  exact Spec.wellFormed_encode s

end Radix.UTF8
