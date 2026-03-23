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

  -- ── Spec-level chain tests ──
  let specDesc1 : Radix.DMA.Spec.Descriptor :=
    { source := { start := 0x1000, size := 256 }
    , destination := { start := 0x2000, size := 256 }
    , order := .seqCst
    , coherence := .coherent
    , atomicity := .burst 4
    }
  let specDesc2 : Radix.DMA.Spec.Descriptor :=
    { source := { start := 0x3000, size := 128 }
    , destination := { start := 0x4000, size := 128 }
    , order := .seqCst
    , coherence := .coherent
    , atomicity := .burst 4
    }
  let chain := [specDesc1, specDesc2]
  assert (Radix.DMA.Spec.chainTotalBytes chain == 384)
    "chain total bytes"
  assert (Radix.DMA.Spec.chainTotalBytes ([] : List Radix.DMA.Spec.Descriptor) == 0)
    "empty chain total bytes"
  -- chainValid is a Prop (proven by chainValid_nil theorem)
  have _ := Radix.DMA.Spec.chainValid_nil

  -- ── Ops-level chain tests ──
  assert (Radix.DMA.chainTotalBytes chain == 384) "Ops chain total bytes"
  assert (Radix.DMA.isChainValid []) "Ops empty chain is valid"
  assert (Radix.DMA.chainStepCount [] == 0) "Ops empty chain step count"
  let regions_src := Radix.DMA.chainSourceRegions chain
  assert (regions_src.length == 2) "chain source regions length"
  let regions_dst := Radix.DMA.chainDestinationRegions chain
  assert (regions_dst.length == 2) "chain destination regions length"

  -- ── Alignment tests ──
  assert (Radix.DMA.isAligned { start := 0x1000, size := 256 } 4)
    "region 0x1000/256 aligned to 4"
  assert (Radix.DMA.isAligned { start := 0, size := 1 } 1) "region 0/1 aligned to 1"
  assert (!Radix.DMA.isAligned { start := 3, size := 4 } 4) "region 3/4 not aligned to 4"
  assert (Radix.DMA.isDescriptorAligned specDesc1 4) "descriptor aligned to 4"

  -- ── Constructor tests ──
  let memToMem := Radix.DMA.mkMemToMem 0x100 0x200 64
  assert (memToMem.source.start == 0x100) "mkMemToMem source start"
  assert (memToMem.destination.start == 0x200) "mkMemToMem destination start"
  assert (memToMem.source.size == 64) "mkMemToMem size"

  c.get
