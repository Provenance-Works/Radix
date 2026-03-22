/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.DMA.Spec

/-!
# DMA Transfer Operations (Layer 2)

Executable validation and simulation helpers for DMA descriptors.
-/

set_option autoImplicit false

namespace Radix.DMA

open Radix.DMA.Spec

abbrev Descriptor := Spec.Descriptor
abbrev Coherence := Spec.Coherence
abbrev Atomicity := Spec.Atomicity

/-- Convert a `ByteArray` into a list of bytes. -/
def byteArrayToList (bytes : ByteArray) : List UInt8 :=
  bytes.toList

/-- Checked validity for a DMA descriptor. -/
def isValid (d : Descriptor) : Bool :=
  (d.source.size == d.destination.size)
    && decide (0 < d.source.size)
    && decide (Radix.Memory.Spec.Region.disjoint d.source d.destination)
    && (match d.atomicity with
      | .whole => true
      | .burst bytes => decide (0 < bytes ∧ bytes ≤ d.source.size))
    && (match d.coherence with
      | .coherent => true
      | .nonCoherent => d.order == .seqCst)

/-- Number of bytes moved by the descriptor. -/
def bytesMoved (d : Descriptor) : Nat :=
  d.bytesMoved

/-- Number of transfer visibility steps. -/
def stepCount (d : Descriptor) : Nat :=
  d.stepCount

/-- Simulate a DMA copy from `src` into `dst` using the descriptor's offsets.
    The destination size is preserved. -/
def simulateCopy (src dst : ByteArray) (d : Descriptor) : Option ByteArray :=
  if isValid d then
    if _ : d.source.endOffset ≤ src.size then
      if _ : d.destination.endOffset ≤ dst.size then
        let srcBytes := byteArrayToList src
        let dstBytes := byteArrayToList dst
        let copied := (srcBytes.drop d.source.start).take d.source.size
        let result :=
          dstBytes.take d.destination.start ++ copied ++
          dstBytes.drop d.destination.endOffset
        some (ByteArray.mk result.toArray)
      else
        none
    else
      none
  else
    none

end Radix.DMA
