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
    , destination := { start := 4, size := 3 }
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
    assert (bytes.toList == [0, 0, 0, 0, 10, 20, 30]) "simulate copy"
  | none => assert false "simulate copy failed"

  let burst : Radix.DMA.Descriptor :=
    { valid with atomicity := .burst 2, coherence := .coherent }
  assert (Radix.DMA.isValid burst) "burst descriptor valid"
  assert (Radix.DMA.stepCount burst == 2) "burst step count"

  let invalid : Radix.DMA.Descriptor :=
    { valid with order := .release }
  assert (!Radix.DMA.isValid invalid) "non-coherent transfer needs seqCst"

  c.get
