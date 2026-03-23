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
    && (match d.atomicity with
      | .whole => true
      | .burst bytes => decide (0 < bytes ∧ bytes ≤ d.source.size))
    && (match d.coherence with
      | .coherent => true
      | .nonCoherent => d.order == .seqCst)

/-- Check whether a descriptor can be simulated against the provided buffers. -/
def canSimulate (src dst : ByteArray) (d : Descriptor) : Bool :=
  isValid d
    && decide (d.source.endOffset ≤ src.size)
    && decide (d.destination.endOffset ≤ dst.size)

/-- Number of bytes moved by the descriptor. -/
def bytesMoved (d : Descriptor) : Nat :=
  d.source.size

/-- Number of bytes made visible by each transfer step. -/
def burstBytes (d : Descriptor) : Nat :=
  match d.atomicity with
  | .whole => d.source.size
  | .burst bytes => bytes

/-- Byte count for an individual visibility step. -/
def stepByteCount (d : Descriptor) (step : Nat) : Nat :=
  min (burstBytes d) (bytesMoved d - step * burstBytes d)

/-- Source region covered by a particular step. -/
def sourceChunk (d : Descriptor) (step : Nat) : Radix.Memory.Spec.Region :=
  { start := d.source.start + step * burstBytes d
  , size := stepByteCount d step
  }

/-- Destination region covered by a particular step. -/
def destinationChunk (d : Descriptor) (step : Nat) : Radix.Memory.Spec.Region :=
  { start := d.destination.start + step * burstBytes d
  , size := stepByteCount d step
  }

/-- Number of transfer visibility steps. -/
def stepCount (d : Descriptor) : Nat :=
  match d.atomicity with
  | .whole => 1
  | .burst bytes => (d.source.size + bytes - 1) / bytes

/-- Simulate a single DMA visibility step. -/
def stepCopy (src dst : ByteArray) (d : Descriptor) (step : Nat) : Option ByteArray :=
  if canSimulate src dst d then
    if _ : step < stepCount d then
      let srcChunk := sourceChunk d step
      let dstChunk := destinationChunk d step
      let srcBytes := byteArrayToList src
      let dstBytes := byteArrayToList dst
      let copied := (srcBytes.drop srcChunk.start).take srcChunk.size
      let result :=
        dstBytes.take dstChunk.start ++ copied ++
        dstBytes.drop dstChunk.endOffset
      some (ByteArray.mk result.toArray)
    else
      none
  else
    none

private def simulateStepsAux (src : ByteArray) (d : Descriptor)
    (step remaining : Nat) (current : ByteArray) (acc : Array ByteArray) : Option (Array ByteArray) :=
  match remaining with
  | 0 => some acc
  | remaining + 1 =>
      match stepCopy src current d step with
      | some next => simulateStepsAux src d (step + 1) remaining next (acc.push next)
      | none => none

/-- Simulate the intermediate destination states that become visible after
    each DMA step. -/
def simulateSteps (src dst : ByteArray) (d : Descriptor) : Option (Array ByteArray) :=
  if canSimulate src dst d then
    simulateStepsAux src d 0 (stepCount d) dst #[]
  else
    none

/-- Simulate a DMA copy from `src` into `dst` using the descriptor's offsets.
    The destination size is preserved. -/
def simulateCopy (src dst : ByteArray) (d : Descriptor) : Option ByteArray :=
  if canSimulate src dst d then
        let srcBytes := byteArrayToList src
        let dstBytes := byteArrayToList dst
        let copied := (srcBytes.drop d.source.start).take d.source.size
        let result :=
          dstBytes.take d.destination.start ++ copied ++
          dstBytes.drop d.destination.endOffset
        some (ByteArray.mk result.toArray)
  else
    none

end Radix.DMA
