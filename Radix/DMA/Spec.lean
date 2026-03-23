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

/-- Number of visibility steps required to complete the transfer. -/
def Descriptor.stepCount (d : Descriptor) : Nat :=
  match d.atomicity with
  | .whole => 1
  | .burst bytes => (d.source.size + bytes - 1) / bytes

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

end Radix.DMA.Spec
