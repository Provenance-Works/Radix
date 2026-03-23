import tests.ComprehensiveTests.Framework
import Radix.DMA

/-!
# DMA Tests
-/

open ComprehensiveTests

def runDMATests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    DMA tests..."

  let valid : Radix.DMA.Descriptor :=
    { source := { start := 0, size := 3 }
    , destination := { start := 0, size := 3 }
    , order := .seqCst
    , coherence := .nonCoherent
    , atomicity := .whole
    }
  assert (Radix.DMA.isValid valid) "valid non-coherent descriptor"
  assert (Radix.DMA.stepCount valid == 1) "whole transfer is one step"

  let src := ByteArray.mk #[10, 20, 30, 40, 50, 60, 70]
  let dst := ByteArray.mk #[0, 0, 0, 0, 0, 0, 0]
  match Radix.DMA.simulateCopy src dst valid with
  | some bytes =>
    assert (bytes.toList == [10, 20, 30, 0, 0, 0, 0]) "simulate copy"
    assert (bytes.size == dst.size) "simulate copy preserves destination size"
  | none => assert false "simulate copy failed"

  let burst : Radix.DMA.Descriptor :=
    { valid with atomicity := .burst 2, coherence := .coherent }
  assert (Radix.DMA.isValid burst) "burst descriptor valid"
  assert (Radix.DMA.canSimulate src dst burst) "burst descriptor fits buffers"
  assert (Radix.DMA.burstBytes burst == 2) "burst byte width"
  assert (Radix.DMA.stepCount burst == 2) "burst step count"
  assert (Radix.DMA.stepByteCount burst 0 == 2) "first step copies full burst"
  assert (Radix.DMA.stepByteCount burst 1 == 1) "final step copies trailing byte"
  assert ((Radix.DMA.sourceChunk burst 1).start == 2) "second source chunk start"
  assert ((Radix.DMA.destinationChunk burst 1).size == 1) "second destination chunk size"
  match Radix.DMA.stepCopy src dst burst 0 with
  | some bytes =>
    assert (bytes.toList == [10, 20, 0, 0, 0, 0, 0]) "first DMA visibility step"
  | none => assert false "first DMA visibility step failed"
  match Radix.DMA.simulateSteps src dst burst with
  | some steps =>
    match Array.toList steps with
    | [step0, step1] =>
      assert (ByteArray.toList step0 == [10, 20, 0, 0, 0, 0, 0]) "step 0 state"
      assert (ByteArray.toList step1 == [10, 20, 30, 0, 0, 0, 0]) "step 1 state"
    | _ =>
      assert false "burst simulation exposes two intermediate states"
  | none => assert false "burst step simulation failed"

  let shifted : Radix.DMA.Descriptor :=
    { valid with source := { start := 2, size := 3 }, destination := { start := 3, size := 3 }, coherence := .coherent }
  match Radix.DMA.simulateCopy src dst shifted with
  | some bytes =>
    assert (bytes.toList == [0, 0, 0, 30, 40, 50, 0]) "simulate copy with offsets"
  | none => assert false "simulate copy with offsets failed"

  let invalid : Radix.DMA.Descriptor :=
    { valid with order := .release }
  assert (!Radix.DMA.isValid invalid) "non-coherent transfer needs seqCst"

  let invalidBurst : Radix.DMA.Descriptor :=
    { valid with atomicity := .burst 0, coherence := .coherent }
  assert (!Radix.DMA.isValid invalidBurst) "zero-sized burst invalid"

  let outOfBounds : Radix.DMA.Descriptor :=
    { valid with destination := { start := 5, size := 3 }, coherence := .coherent }
  assert (!Radix.DMA.canSimulate src dst outOfBounds) "out-of-bounds descriptor rejected before simulation"
  match Radix.DMA.simulateCopy src dst outOfBounds with
  | none => assert true "out-of-bounds destination rejected"
  | some _ => assert false "out-of-bounds destination should fail"

  c.get
