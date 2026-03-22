import tests.ComprehensiveTests.Framework
import Radix.Memory

/-!
# Memory Region Algebra Tests
-/

open ComprehensiveTests

def runMemoryRegionTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Memory region algebra tests..."

  let a : Radix.Memory.Spec.Region := { start := 10, size := 6 }
  let b : Radix.Memory.Spec.Region := { start := 14, size := 8 }
  let c1 : Radix.Memory.Spec.Region := { start := 16, size := 4 }

  let inter := Radix.Memory.Spec.Region.intersection a b
  assert (inter.start == 14 && inter.size == 2) "intersection"

  let span := Radix.Memory.Spec.Region.span a b
  assert (span.start == 10 && span.size == 12) "span"

  assert ((Radix.Memory.Spec.Region.union? a c1).isSome) "adjacent union"
  assert ((Radix.Memory.Spec.Region.union? a { start := 30, size := 2 }).isSome == false)
    "non-mergeable union"

  let diff := Radix.Memory.Spec.Region.difference a b
  assert (diff == [{ start := 10, size := 4 }]) "difference left remainder"

  c.get
