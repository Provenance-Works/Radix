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

/-- Simulation preconditions are exactly boolean validity plus buffer bounds. -/
theorem canSimulate_eq_true_iff (src dst : ByteArray) (d : Descriptor) :
    Radix.DMA.canSimulate src dst d = true ↔
      d.valid ∧ d.source.endOffset ≤ src.size ∧ d.destination.endOffset ≤ dst.size := by
  unfold Radix.DMA.canSimulate
  constructor
  · intro h
    rw [Bool.and_eq_true] at h
    rcases h with ⟨hleft, hdst⟩
    rw [Bool.and_eq_true] at hleft
    rcases hleft with ⟨hvalid, hsrc⟩
    rcases (isValid_iff_valid d).mp hvalid with hspec
    exact ⟨hspec, by simpa using hsrc, by simpa using hdst⟩
  · rintro ⟨hvalid, hsrc, hdst⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, by simpa using hdst⟩
    rw [Bool.and_eq_true]
    exact ⟨(isValid_iff_valid d).mpr hvalid, by simpa using hsrc⟩

/-- Valid DMA descriptors always move a positive number of bytes. -/
theorem bytesMoved_pos (d : Descriptor) (h : d.valid) :
    0 < bytesMoved d := by
  rcases h with ⟨_, hsize, _, _⟩
  simpa [bytesMoved] using hsize

/-- Valid DMA descriptors require at least one visibility step. -/
theorem stepCount_pos (d : Descriptor) (h : d.valid) :
    0 < stepCount d := by
  simpa [stepCount] using Spec.Descriptor.stepCount_pos d h

/-- Successful step simulation returns the executable splice for the step chunk. -/
theorem stepCopy_eq_some (src dst : ByteArray) (d : Descriptor) (step : Nat)
    (hcan : Radix.DMA.canSimulate src dst d = true)
    (hstep : step < stepCount d) :
    Radix.DMA.stepCopy src dst d step = some
      (ByteArray.mk (((byteArrayToList dst).take (Radix.DMA.destinationChunk d step).start ++
        ((byteArrayToList src).drop (Radix.DMA.sourceChunk d step).start).take (Radix.DMA.sourceChunk d step).size ++
        (byteArrayToList dst).drop (Radix.DMA.destinationChunk d step).endOffset).toArray)) := by
        rw [Radix.DMA.stepCopy, if_pos hcan]
        simp [hstep, byteArrayToList, Radix.DMA.sourceChunk, Radix.DMA.destinationChunk]

/-- Successful simulation returns the executable splice of source bytes into the
    destination buffer. -/
theorem simulateCopy_eq_some (src dst : ByteArray) (d : Descriptor)
    (hvalid : Radix.DMA.canSimulate src dst d = true) :
    Radix.DMA.simulateCopy src dst d = some
      (ByteArray.mk (((byteArrayToList dst).take d.destination.start ++
        ((byteArrayToList src).drop d.source.start).take d.source.size ++
        (byteArrayToList dst).drop d.destination.endOffset).toArray)) := by
  have hspec : d.valid ∧ d.source.endOffset ≤ src.size ∧ d.destination.endOffset ≤ dst.size :=
    (canSimulate_eq_true_iff src dst d).mp hvalid
  have hisValid : isValid d = true := (isValid_iff_valid d).mpr hspec.1
  have hsrc : decide (d.source.endOffset ≤ src.size) = true := by
    simpa using hspec.2.1
  have hdst : decide (d.destination.endOffset ≤ dst.size) = true := by
    simpa using hspec.2.2
  simp [Radix.DMA.simulateCopy, Radix.DMA.canSimulate, hisValid, hsrc, hdst, byteArrayToList]

-- ════════════════════════════════════════════════════════════════════
-- Alignment Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- Alignment check agrees with the spec predicate. -/
theorem isAligned_iff (r : Radix.Memory.Spec.Region) (align : Nat) :
    Radix.DMA.isAligned r align = true ↔ Spec.isAligned r align := by
  simp [Radix.DMA.isAligned]

/-- Descriptor alignment check agrees with the spec predicate. -/
theorem isDescriptorAligned_iff (d : Descriptor) (align : Nat) :
    isDescriptorAligned d align = true ↔ d.isAligned align := by
  simp [isDescriptorAligned, Radix.DMA.isAligned, Spec.Descriptor.isAligned,
        Bool.and_eq_true]

-- ════════════════════════════════════════════════════════════════════
-- Chain Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- An empty chain is always valid. -/
theorem isChainValid_nil : isChainValid [] = true := by
  simp [isChainValid]

/-- An empty chain has zero total bytes. -/
theorem chainTotalBytes_nil : chainTotalBytes [] = 0 := by
  simp [chainTotalBytes, Spec.chainTotalBytes]

/-- An empty chain has zero steps. -/
theorem chainStepCount_nil : chainStepCount [] = 0 := by
  simp [chainStepCount]

/-- Simple memory-to-memory descriptor is valid when size > 0. -/
theorem mkMemToMem_valid (srcStart dstStart size : Nat) (hpos : 0 < size) :
    (mkMemToMem srcStart dstStart size).valid := by
  simp [mkMemToMem, Spec.Descriptor.valid, Spec.atomicityValid, Spec.fenceOrderSufficient, hpos]

/-- A whole-atomicity descriptor has exactly 1 step. -/
theorem stepCount_whole (d : Descriptor) (hw : d.atomicity = .whole) :
    stepCount d = 1 := by
  simp [stepCount, hw]

/-- Burst transfer with burstSize = size has exactly 1 step. -/
theorem stepCount_burst_eq_size (d : Descriptor) (hb : d.atomicity = .burst d.source.size)
    (hpos : 0 < d.source.size) :
    stepCount d = 1 := by
  simp [stepCount, hb]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- Chain source/destination regions lists have length equal to chain length. -/
theorem chainSourceRegions_length (chain : List Descriptor) :
    (chainSourceRegions chain).length = chain.length := by
  simp [chainSourceRegions]

theorem chainDestinationRegions_length (chain : List Descriptor) :
    (chainDestinationRegions chain).length = chain.length := by
  simp [chainDestinationRegions]

end Radix.DMA
