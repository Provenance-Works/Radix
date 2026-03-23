/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Radix.Memory.Spec
import Radix.Concurrency.Spec

/-!
# DMA Transfer Specification (Layer 3)

Formal model for DMA descriptors over source and destination regions.

## References

- v0.3.0 Roadmap: DMA Transfer Model
-/

set_option autoImplicit false

namespace Radix.DMA.Spec

open Radix.Memory.Spec
open Radix.Concurrency.Spec

/-- Cache coherence contract for a DMA transfer. -/
inductive Coherence where
  | coherent
  | nonCoherent
  deriving DecidableEq, Repr

/-- Atomicity model for completion visibility. -/
inductive Atomicity where
  | whole
  | burst (bytes : Nat)
  deriving DecidableEq, Repr

/-- A DMA transfer descriptor. -/
structure Descriptor where
  source : Region
  destination : Region
  order : MemoryOrder
  coherence : Coherence
  atomicity : Atomicity
  deriving Repr

/-- Fence requirements for cache-incoherent transfers. -/
def fenceOrderSufficient (d : Descriptor) : Prop :=
  match d.coherence with
  | .coherent => True
  | .nonCoherent => d.order = .seqCst

instance (d : Descriptor) : Decidable (fenceOrderSufficient d) := by
  unfold fenceOrderSufficient
  cases d.coherence <;> infer_instance

/-- Atomicity configuration is internally consistent. -/
def atomicityValid (d : Descriptor) : Prop :=
  match d.atomicity with
  | .whole => True
  | .burst bytes => 0 < bytes ∧ bytes ≤ d.source.size

instance (d : Descriptor) : Decidable (atomicityValid d) := by
  unfold atomicityValid
  cases d.atomicity <;> infer_instance

/-- A descriptor is valid when it copies a positive number of bytes between
    equally sized regions and satisfies the coherence contract. The
    source and destination offsets are interpreted relative to separate
    buffers in the executable simulator. -/
def Descriptor.valid (d : Descriptor) : Prop :=
  d.source.size = d.destination.size
  ∧ 0 < d.source.size
  ∧ atomicityValid d
  ∧ fenceOrderSufficient d

instance (d : Descriptor) : Decidable d.valid :=
  inferInstanceAs
    (Decidable
      (d.source.size = d.destination.size
        ∧ 0 < d.source.size
        ∧ atomicityValid d
        ∧ fenceOrderSufficient d))

/-- Number of bytes transferred. -/
def Descriptor.bytesMoved (d : Descriptor) : Nat :=
  d.source.size

/-- Number of bytes made visible by each transfer step. -/
def Descriptor.burstBytes (d : Descriptor) : Nat :=
  match d.atomicity with
  | .whole => d.source.size
  | .burst bytes => bytes

/-- Byte offset from the start of the transfer at a given step. -/
def Descriptor.stepOffset (d : Descriptor) (step : Nat) : Nat :=
  step * d.burstBytes

/-- Number of bytes covered by a particular visibility step. The value
    saturates to zero once the step offset moves past the transfer size. -/
def Descriptor.stepByteCount (d : Descriptor) (step : Nat) : Nat :=
  min d.burstBytes (d.bytesMoved - d.stepOffset step)

/-- Source chunk visible at a particular step. -/
def Descriptor.sourceChunk (d : Descriptor) (step : Nat) : Region :=
  { start := d.source.start + d.stepOffset step
  , size := d.stepByteCount step
  }

/-- Destination chunk visible at a particular step. -/
def Descriptor.destinationChunk (d : Descriptor) (step : Nat) : Region :=
  { start := d.destination.start + d.stepOffset step
  , size := d.stepByteCount step
  }

/-- Number of visibility steps required to complete the transfer. -/
def Descriptor.stepCount (d : Descriptor) : Nat :=
  match d.atomicity with
  | .whole => 1
  | .burst bytes => (d.source.size + bytes - 1) / bytes

theorem Descriptor.stepByteCount_le_burstBytes (d : Descriptor) (step : Nat) :
    d.stepByteCount step ≤ d.burstBytes := by
  unfold Descriptor.stepByteCount
  exact Nat.min_le_left _ _

theorem Descriptor.sourceChunk_size_eq (d : Descriptor) (step : Nat) :
    (d.sourceChunk step).size = d.stepByteCount step := by
  rfl

theorem Descriptor.destinationChunk_size_eq (d : Descriptor) (step : Nat) :
    (d.destinationChunk step).size = d.stepByteCount step := by
  rfl

theorem Descriptor.stepCount_pos (d : Descriptor) (h : d.valid) :
    0 < d.stepCount := by
  rcases h with ⟨_, hsize, hatomic, _⟩
  cases hAtomicity : d.atomicity with
  | whole =>
      simp [Descriptor.stepCount, hAtomicity]
  | burst bytes =>
      have hatomic' : 0 < bytes ∧ bytes ≤ d.source.size := by
        simpa [atomicityValid, hAtomicity] using hatomic
      rcases hatomic' with ⟨hbytes, _⟩
      have : 0 < (d.source.size + bytes - 1) / bytes := by
        have hsum : bytes ≤ d.source.size + bytes - 1 := by omega
        have := Nat.div_pos hsum hbytes
        simpa using this
      simpa [Descriptor.stepCount, hAtomicity] using this

-- ════════════════════════════════════════════════════════════════════
-- Transfer Direction
-- ════════════════════════════════════════════════════════════════════

/-- Direction of a DMA transfer relative to the device. -/
inductive Direction where
  | memToMem
  | memToDev
  | devToMem
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════════
-- Alignment Requirements
-- ════════════════════════════════════════════════════════════════════

/-- Alignment constraint: start address and size must both be multiples of `align`. -/
def isAligned (r : Region) (align : Nat) : Prop :=
  0 < align ∧ r.start % align = 0 ∧ r.size % align = 0

instance (r : Region) (align : Nat) : Decidable (isAligned r align) :=
  inferInstanceAs (Decidable (0 < align ∧ r.start % align = 0 ∧ r.size % align = 0))

/-- A descriptor is aligned when both source and destination satisfy
    the given alignment constraint. -/
def Descriptor.isAligned (d : Descriptor) (align : Nat) : Prop :=
  Spec.isAligned d.source align ∧ Spec.isAligned d.destination align

instance (d : Descriptor) (align : Nat) : Decidable (d.isAligned align) :=
  inferInstanceAs (Decidable (Spec.isAligned d.source align ∧ Spec.isAligned d.destination align))

-- ════════════════════════════════════════════════════════════════════
-- Scatter-Gather DMA Chain
-- ════════════════════════════════════════════════════════════════════

/-- A chain is valid when every descriptor is valid. -/
def chainValid (c : List Descriptor) : Prop :=
  ∀ d ∈ c, d.valid

/-- Total bytes transferred by a chain. -/
def chainTotalBytes (c : List Descriptor) : Nat :=
  c.foldl (fun acc d => acc + d.bytesMoved) 0

/-- Source regions must not overlap within the chain (prevents read conflicts). -/
def chainSourcesDisjoint (c : List Descriptor) : Prop :=
  ∀ i j : Fin c.length,
    i ≠ j → Region.disjoint (c.get i).source (c.get j).source

/-- Destination regions must not overlap within the chain (prevents write conflicts). -/
def chainDestinationsDisjoint (c : List Descriptor) : Prop :=
  ∀ i j : Fin c.length,
    i ≠ j → Region.disjoint (c.get i).destination (c.get j).destination

-- ════════════════════════════════════════════════════════════════════
-- DMA Channel Status
-- ════════════════════════════════════════════════════════════════════

/-- Runtime status of a DMA channel. -/
inductive ChannelStatus where
  | idle
  | running (descriptorIdx : Nat) (stepIdx : Nat)
  | completed
  | error (msg : String)
  deriving DecidableEq, Repr

/-- A DMA channel with a descriptor chain and a status. -/
structure Channel where
  chain : List Descriptor
  status : ChannelStatus
  deriving Repr

-- ════════════════════════════════════════════════════════════════════
-- Additional Theorems
-- ════════════════════════════════════════════════════════════════════

/-- Byte count at step 0 of a whole-atomicity descriptor equals the transfer size. -/
theorem Descriptor.stepByteCount_zero_whole (d : Descriptor)
    (hw : d.atomicity = .whole) :
    d.stepByteCount 0 = d.bytesMoved := by
  simp [Descriptor.stepByteCount, Descriptor.burstBytes, Descriptor.bytesMoved,
        Descriptor.stepOffset, hw]

/-- A whole-atomicity descriptor always has exactly 1 step. -/
theorem Descriptor.stepCount_whole (d : Descriptor)
    (hw : d.atomicity = .whole) :
    d.stepCount = 1 := by
  simp [Descriptor.stepCount, hw]

/-- Source and destination chunks have the same size at each step. -/
theorem Descriptor.chunks_same_size (d : Descriptor) (step : Nat) :
    (d.sourceChunk step).size = (d.destinationChunk step).size := by
  simp [Descriptor.sourceChunk, Descriptor.destinationChunk]

/-- An empty chain transfers zero bytes. -/
theorem chainTotalBytes_nil : chainTotalBytes [] = 0 := by
  simp [chainTotalBytes]

/-- An empty chain is vacuously valid. -/
theorem chainValid_nil : chainValid [] := by
  intro _ hd; simp at hd

/-- A single-descriptor chain's total bytes equal the descriptor's transfer size. -/
theorem chainTotalBytes_singleton (d : Descriptor) :
    chainTotalBytes [d] = d.bytesMoved := by
  simp [chainTotalBytes, Descriptor.bytesMoved]

/-- Alignment at 1 is trivially satisfied for any region. -/
theorem isAligned_one (r : Region) : isAligned r 1 := by
  refine ⟨by omega, ?_, ?_⟩ <;> omega

/-- If a region is aligned to `n`, it is also aligned to 1. -/
theorem isAligned_implies_one (r : Region) (n : Nat) (_ : isAligned r n) :
    isAligned r 1 := isAligned_one r

/-- A zero-size region at offset 0 is aligned to any positive alignment. -/
theorem isAligned_zero_region (align : Nat) (hpos : 0 < align) :
    isAligned { start := 0, size := 0 } align := by
  simp [isAligned, hpos]

end Radix.DMA.Spec
