import tests.ComprehensiveTests.Framework
import Radix.BareMetal.Spec

/-!
# BareMetal Platform Tests
## Spec References
- P5-02: Platform wordBits, naturalAlign, Permissions, RegionKind
-/

open ComprehensiveTests
open Radix.BareMetal.Spec

def runBareMetalPlatformTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    BareMetal platform tests..."

  -- ## Platform wordBits
  assert (Platform.x86_64.wordBits == 64) "x86_64 wordBits"
  assert (Platform.aarch64.wordBits == 64) "aarch64 wordBits"
  assert (Platform.riscv64.wordBits == 64) "riscv64 wordBits"

  -- ## Platform naturalAlign
  assert (Platform.x86_64.naturalAlign == 8) "x86_64 naturalAlign"
  assert (Platform.aarch64.naturalAlign == 8) "aarch64 naturalAlign"
  assert (Platform.riscv64.naturalAlign == 8) "riscv64 naturalAlign"

  -- ## Platform BEq
  assert (Platform.x86_64 == Platform.x86_64) "platform self-eq"
  assert (!(Platform.x86_64 == Platform.aarch64)) "platform neq"
  assert (!(Platform.aarch64 == Platform.riscv64)) "platform neq 2"

  -- ## Permissions
  let ro := Permissions.readOnly
  assert (ro.read == true) "readOnly read"
  assert (ro.write == false) "readOnly write"
  assert (ro.execute == false) "readOnly execute"

  let rw := Permissions.readWrite
  assert (rw.read == true) "readWrite read"
  assert (rw.write == true) "readWrite write"
  assert (rw.execute == false) "readWrite execute"

  let rx := Permissions.readExecute
  assert (rx.read == true) "readExecute read"
  assert (rx.write == false) "readExecute write"
  assert (rx.execute == true) "readExecute execute"

  let no := Permissions.none
  assert (no.read == false) "none read"
  assert (no.write == false) "none write"
  assert (no.execute == false) "none execute"

  -- ## RegionKind
  assert (RegionKind.flash != RegionKind.ram) "flash ≠ ram"
  assert (RegionKind.mmio != RegionKind.reserved) "mmio ≠ reserved"

  -- ## AllocStrategy isGCFree
  assert (AllocStrategy.static.isGCFree == true) "static isGCFree"
  assert (AllocStrategy.stack.isGCFree == true) "stack isGCFree"
  assert (AllocStrategy.arena.isGCFree == true) "arena isGCFree"
  assert (AllocStrategy.none.isGCFree == true) "none isGCFree"
  assert (AllocStrategy.heap.isGCFree == false) "heap not isGCFree"

  -- ## AllocProfile
  let prof := AllocProfile.mk "testFn" .stack (some 256)
  assert (prof.name == "testFn") "profile name"
  assert (prof.isGCFreeCompatible == true) "profile GCFreeCompat"

  c.get
