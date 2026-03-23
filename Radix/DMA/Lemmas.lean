/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.DMA.Spec
import Radix.DMA.Ops

/-!
# DMA Transfer Proofs (Layer 3)
-/

set_option autoImplicit false

namespace Radix.DMA

open Spec

/-- Layer 2 validity agrees with the specification. -/
theorem isValid_iff_valid (d : Descriptor) :
    isValid d = true ↔ d.valid := by
  rcases d with ⟨source, destination, order, coherence, atomicity⟩
  cases coherence <;> cases atomicity <;>
    simp [isValid, Spec.Descriptor.valid, Spec.atomicityValid, Spec.fenceOrderSufficient,
      Bool.and_eq_true, and_assoc, and_left_comm, and_comm]

/-- Valid DMA descriptors always move a positive number of bytes. -/
theorem bytesMoved_pos (d : Descriptor) (h : d.valid) :
    0 < bytesMoved d := by
  rcases h with ⟨_, hsize, _, _⟩
  simpa [bytesMoved] using hsize

/-- Valid DMA descriptors require at least one visibility step. -/
theorem stepCount_pos (d : Descriptor) (h : d.valid) :
    0 < stepCount d := by
  simpa [stepCount] using Spec.Descriptor.stepCount_pos d h

/-- Successful simulation returns the executable splice of source bytes into the
    destination buffer. -/
theorem simulateCopy_eq_some (src dst : ByteArray) (d : Descriptor)
    (hvalid : isValid d = true)
    (hsrc : d.source.endOffset ≤ src.size)
    (hdst : d.destination.endOffset ≤ dst.size) :
    simulateCopy src dst d = some
      (ByteArray.mk (((byteArrayToList dst).take d.destination.start ++
        ((byteArrayToList src).drop d.source.start).take d.source.size ++
        (byteArrayToList dst).drop d.destination.endOffset).toArray)) := by
  simp [simulateCopy, hvalid, hsrc, hdst, byteArrayToList]

end Radix.DMA
