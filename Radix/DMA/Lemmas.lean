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

-- ════════════════════════════════════════════════════════════════════
-- Layer 2 / Layer 3 Agreement
-- ════════════════════════════════════════════════════════════════════

/-- Layer 2 `bytesMoved` agrees with the Spec definition. -/
theorem bytesMoved_eq_spec (d : Descriptor) :
    bytesMoved d = d.bytesMoved := by
  rfl

/-- Layer 2 `stepCount` agrees with the Spec definition. -/
theorem stepCount_eq_spec (d : Descriptor) :
    stepCount d = d.stepCount := by
  rfl

-- ════════════════════════════════════════════════════════════════════
-- Chain Bridge Lemmas
-- ════════════════════════════════════════════════════════════════════

private theorem foldl_stepCount_shift (l : List Descriptor) (a b : Nat) :
    l.foldl (fun acc d => acc + stepCount d) (a + b) =
    a + l.foldl (fun acc d => acc + stepCount d) b := by
  induction l generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl]
    rw [show a + b + stepCount x = a + (b + stepCount x) from by omega]
    exact ih (b + stepCount x)

/-- Chain step count distributes over cons. -/
theorem ops_chainStepCount_cons (d : Descriptor) (rest : List Descriptor) :
    chainStepCount (d :: rest) = stepCount d + chainStepCount rest := by
  simp only [chainStepCount, List.foldl, Nat.zero_add]
  rw [show stepCount d = stepCount d + 0 from by omega]
  exact foldl_stepCount_shift rest (stepCount d) 0

/-- Chain validity implies every element is valid. -/
theorem ops_isChainValid_forall (chain : List Descriptor)
    (h : isChainValid chain = true) (d : Descriptor) (hd : d ∈ chain) :
    isValid d = true := by
  simp [isChainValid] at h
  exact h d hd

/-- A single-element chain is valid iff the descriptor is valid. -/
theorem ops_isChainValid_singleton (d : Descriptor) :
    isChainValid [d] = isValid d := by
  simp [isChainValid]

-- ════════════════════════════════════════════════════════════════════
-- Constructor Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- mkBurstTransfer produces a valid descriptor when size and burst
    parameters are positive and burst ≤ size. -/
theorem mkBurstTransfer_valid (srcStart dstStart size burstSize : Nat)
    (hsize : 0 < size) (hburst : 0 < burstSize) (hle : burstSize ≤ size) :
    (Radix.DMA.mkBurstTransfer srcStart dstStart size burstSize).valid := by
  simp [Radix.DMA.mkBurstTransfer, Spec.Descriptor.valid, Spec.atomicityValid,
        Spec.fenceOrderSufficient, hsize, hburst, hle]

/-- mkMemToMem creates a whole-atomicity descriptor. -/
theorem mkMemToMem_atomicity (srcStart dstStart size : Nat) :
    (Radix.DMA.mkMemToMem srcStart dstStart size).atomicity = .whole := by
  rfl

/-- mkMemToMem produces exactly 1 step. -/
theorem mkMemToMem_stepCount (srcStart dstStart size : Nat) :
    stepCount (Radix.DMA.mkMemToMem srcStart dstStart size) = 1 := by
  rfl

-- ════════════════════════════════════════════════════════════════════
-- Completion Bridge Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- A valid descriptor that has completed all steps has zero remaining bytes
    (Layer 2 bridge to Spec.bytesRemaining_zero_of_complete). -/
theorem bytesRemaining_zero (d : Descriptor) (steps : Nat)
    (hvalid : d.valid) (hcomplete : Spec.Descriptor.stepCount d ≤ steps) :
    Spec.Descriptor.bytesRemaining d steps = 0 := by
  exact Spec.Descriptor.bytesRemaining_zero_of_complete d steps hvalid.2.2.1 hcomplete

/-- Bytes completed is monotonically nondecreasing with steps. -/
theorem bytesCompleted_mono (d : Descriptor) (s1 s2 : Nat) (h : s1 ≤ s2) :
    Spec.Descriptor.bytesCompleted d s1 ≤ Spec.Descriptor.bytesCompleted d s2 := by
  simp only [Spec.Descriptor.bytesCompleted]
  exact min_le_min_right _ (Nat.mul_le_mul_right _ h)

/-- Simulation of an empty chain is the identity on the destination buffer. -/
theorem simulateChain_nil (src dst : ByteArray) :
    simulateChain src dst [] = some dst := by
  simp [simulateChain]

-- ════════════════════════════════════════════════════════════════════
-- Additional Transfer Properties
-- ════════════════════════════════════════════════════════════════════

/-- Burst transfer step count is at least 1 for valid descriptors with burst atomicity. -/
theorem stepCount_burst_pos (d : Descriptor) (bytes : Nat)
    (hb : d.atomicity = .burst bytes) (hbpos : 0 < bytes) (hsize : 0 < d.source.size) :
    0 < stepCount d := by
  simp [stepCount, hb]
  exact ⟨hbpos, by omega⟩

/-- Chain total bytes distributes over cons (Layer 2 bridge). -/
theorem chainTotalBytes_cons (d : Descriptor) (rest : List Descriptor) :
    chainTotalBytes (d :: rest) = bytesMoved d + chainTotalBytes rest := by
  simp [chainTotalBytes, Spec.chainTotalBytes_cons, bytesMoved, Descriptor.bytesMoved]

/-- Valid chain implies each element is valid (via spec bridge). -/
theorem chainValid_forall (chain : List Descriptor)
    (h : isChainValid chain = true) (d : Descriptor) (hd : d ∈ chain) :
    d.valid := by
  exact (isValid_iff_valid d).mp (ops_isChainValid_forall chain h d hd)

/-- bytesMoved of a valid descriptor is positive. -/
theorem bytesMoved_pos_of_valid (d : Descriptor) (h : isValid d = true) :
    0 < bytesMoved d := by
  exact bytesMoved_pos d ((isValid_iff_valid d).mp h)

/-- Chain total bytes of append (Layer 2 bridge). -/
theorem chainTotalBytes_append (c1 c2 : List Descriptor) :
    chainTotalBytes (c1 ++ c2) = chainTotalBytes c1 + chainTotalBytes c2 := by
  simp [chainTotalBytes, Spec.chainTotalBytes_append]

/-- (Spec) Bytes completed plus remaining equals total for any step count. -/
theorem spec_bytesCompleted_add_remaining (d : Descriptor) (steps : Nat) :
    Spec.Descriptor.bytesCompleted d steps + Spec.Descriptor.bytesRemaining d steps = d.bytesMoved :=
  Spec.Descriptor.bytesCompleted_add_remaining d steps

/-- (Spec) Completion is stable: once complete, always complete. -/
theorem spec_isComplete_mono (d : Descriptor) (s1 s2 : Nat)
    (h : s1 ≤ s2) (hc : Spec.Descriptor.isComplete d s1) :
    Spec.Descriptor.isComplete d s2 :=
  Spec.Descriptor.isComplete_mono d s1 s2 h hc

/-- (Spec) Chain validity is preserved under reversal. -/
theorem spec_chainValid_reverse (c : List Descriptor) :
    Spec.chainValid c.reverse ↔ Spec.chainValid c :=
  Spec.chainValid_reverse c

-- ════════════════════════════════════════════════════════════════════
-- SimulateCopy Properties
-- ════════════════════════════════════════════════════════════════════

/-- SimulateCopy on invalid descriptor returns none. -/
theorem simulateCopy_invalid (src dst : ByteArray) (d : Descriptor)
    (h : canSimulate src dst d = false) :
    simulateCopy src dst d = none := by
  simp [simulateCopy, h]

/-- SimulateChain preserves result on cons. -/
theorem simulateChain_cons (src dst : ByteArray) (d : Descriptor) (rest : List Descriptor) :
    simulateChain src dst (d :: rest) =
      match simulateCopy src dst d with
      | some dst' => simulateChain src dst' rest
      | none => none := by
  simp [simulateChain, List.foldlM]
  cases simulateCopy src dst d with
  | none => rfl
  | some dst' => rfl

-- ════════════════════════════════════════════════════════════════════
-- Concrete Test Vectors
-- ════════════════════════════════════════════════════════════════════

/-- mkMemToMem 0 0 16 is valid. -/
example : isValid (mkMemToMem 0 0 16) = true := by native_decide

/-- mkMemToMem creates coherent descriptor. -/
example : (mkMemToMem 0 0 16).coherence = .coherent := by rfl

/-- mkBurstTransfer 0 0 64 16 is valid. -/
example : isValid (mkBurstTransfer 0 0 64 16) = true := by native_decide

/-- mkBurstTransfer 0 0 64 16 has 4 steps. -/
example : stepCount (mkBurstTransfer 0 0 64 16) = 4 := by native_decide

/-- An empty chain has zero step count. -/
example : chainStepCount [] = 0 := by rfl

end Radix.DMA
