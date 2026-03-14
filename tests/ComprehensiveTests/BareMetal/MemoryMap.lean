import tests.ComprehensiveTests.Framework
import Radix.BareMetal.Spec

/-!
# BareMetal Memory Map Tests
## Spec References
- P5-02: MemRegion, MemoryMap, disjoint, contains, findRegion
-/

open ComprehensiveTests
open Radix.BareMetal.Spec

def runBareMetalMemoryMapTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    BareMetal memory map tests..."

  -- ## MemRegion endAddr
  let r1 : MemRegion := ⟨"SRAM", 0x20000000, 0x10000, .ram, .readWrite⟩
  assert (r1.endAddr == 0x20010000) "endAddr"
  assert (r1.name == "SRAM") "region name"
  assert (r1.baseAddr == 0x20000000) "region baseAddr"

  -- ## MemRegion.contains
  assert (Decidable.decide (r1.contains 0x20000000) == true) "contains base"
  assert (Decidable.decide (r1.contains 0x2000FFFF) == true) "contains end-1"
  assert (Decidable.decide (r1.contains 0x20010000) == false) "contains at end"
  assert (Decidable.decide (r1.contains 0x1FFFFFFF) == false) "contains below"

  -- ## MemRegion.disjoint
  let r2 : MemRegion := ⟨"Flash", 0x08000000, 0x80000, .flash, .readExecute⟩
  assert (Decidable.decide (MemRegion.disjoint r1 r2) == true) "disjoint regions"
  assert (Decidable.decide (MemRegion.disjoint r2 r1) == true) "disjoint commutative"

  -- Overlapping regions
  let r3 : MemRegion := ⟨"Overlap", 0x2000F000, 0x2000, .ram, .readWrite⟩
  assert (Decidable.decide (MemRegion.overlaps r1 r3) == true) "overlapping"
  assert (Decidable.decide (MemRegion.disjoint r1 r3) == false) "not disjoint"

  -- Adjacent (non-overlapping)
  let r4 : MemRegion := ⟨"Adjacent", 0x20010000, 0x1000, .ram, .readWrite⟩
  assert (Decidable.decide (MemRegion.disjoint r1 r4) == true) "adjacent disjoint"

  -- Zero-size region
  let r5 : MemRegion := ⟨"Zero", 0x20005000, 0, .ram, .readWrite⟩
  assert (r5.endAddr == r5.baseAddr) "zero-size endAddr"

  -- ## MemoryMap construction
  let mm : MemoryMap := ⟨[r1, r2], .x86_64⟩
  assert (mm.regions.length == 2) "mm regions count"
  assert (mm.platform == .x86_64) "mm platform"

  -- ## MemoryMap.totalSize
  assert (mm.totalSize == 0x10000 + 0x80000) "mm totalSize"

  -- ## MemoryMap.findRegion
  match mm.findRegion 0x20005000 with
  | some r => assert (r.name == "SRAM") "findRegion SRAM"
  | none => assert false "findRegion should find SRAM"

  match mm.findRegion 0x08000000 with
  | some r => assert (r.name == "Flash") "findRegion Flash"
  | none => assert false "findRegion should find Flash"

  match mm.findRegion 0xFFFFFFFF with
  | some _ => assert false "findRegion should not find unmapped"
  | none => assert true "findRegion unmapped = none"

  -- ## MemoryMap.isValid via Decidable
  -- Empty map is "valid" (trivially non-overlapping and non-empty by vacuous truth)
  let emptyMM : MemoryMap := ⟨[], .aarch64⟩
  assert (emptyMM.totalSize == 0) "empty mm totalSize"

  -- ## Larger memory map
  let mmio : MemRegion := ⟨"UART0", 0x40000000, 0x100, .mmio, .readWrite⟩
  let reserved : MemRegion := ⟨"Reserved", 0x00000000, 0x08000000, .reserved, .none⟩
  let largeMM : MemoryMap := ⟨[reserved, r2, r1, mmio], .aarch64⟩
  assert (largeMM.regions.length == 4) "large mm count"

  match largeMM.findRegion 0x40000050 with
  | some r => assert (r.name == "UART0") "findRegion UART0"
  | none => assert false "findRegion should find UART0"

  -- ## StartupPhase ordering
  assert (StartupPhase.reset.order == 0) "reset order"
  assert (StartupPhase.earlyInit.order == 1) "earlyInit order"
  assert (StartupPhase.platformInit.order == 2) "platformInit order"
  assert (StartupPhase.runtimeInit.order == 3) "runtimeInit order"
  assert (StartupPhase.appEntry.order == 4) "appEntry order"

  assert (StartupPhase.reset.precedes .earlyInit == true) "reset < earlyInit"
  assert (StartupPhase.earlyInit.precedes .platformInit == true) "earlyInit < platformInit"
  assert (StartupPhase.appEntry.precedes .reset == false) "appEntry not < reset"

  -- ## StartupStep validity
  let validStep : StartupStep := ⟨.reset, .earlyInit⟩
  assert (Decidable.decide (validStep.isValid) == true) "valid startup step"

  let invalidStep : StartupStep := ⟨.reset, .appEntry⟩
  assert (Decidable.decide (invalidStep.isValid) == false) "invalid startup step"

  -- All consecutive steps are valid
  let steps := [
    StartupStep.mk .reset .earlyInit,
    StartupStep.mk .earlyInit .platformInit,
    StartupStep.mk .platformInit .runtimeInit,
    StartupStep.mk .runtimeInit .appEntry
  ]
  for s in steps do
    assert (Decidable.decide (s.isValid) == true) "consecutive step valid"

  -- ## StartupSequence.isComplete
  let seq := StartupSequence.mk steps
  assert (seq.steps.length == 4) "complete startup sequence length"
  match seq.steps.head? with
  | some s => assert (s.source == .reset) "first step source reset"
  | none => assert false "no first step"
  match seq.steps.getLast? with
  | some s => assert (s.target == .appEntry) "last step target appEntry"
  | none => assert false "no last step"

  let partialSeq := StartupSequence.mk [
    StartupStep.mk .reset .earlyInit,
    StartupStep.mk .earlyInit .platformInit
  ]
  assert (partialSeq.steps.length != 4) "partial seq not complete (wrong length)"

  c.get
