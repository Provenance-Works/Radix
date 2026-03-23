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
  assert (diff.all (fun piece => piece.start == 10 || piece.start == 14 || piece.start == 16))
    "difference pieces remain in source interval"

  let emptyInter := Radix.Memory.Spec.Region.intersection a { start := 30, size := 2 }
  assert (emptyInter == Radix.Memory.Spec.Region.empty) "disjoint intersection canonical empty"

  let emptyDiff := Radix.Memory.Spec.Region.difference Radix.Memory.Spec.Region.empty a
  assert (emptyDiff == []) "empty left difference"

  let selfDiff := Radix.Memory.Spec.Region.difference a a
  assert (selfDiff == []) "self difference empty"

  let split := Radix.Memory.Spec.Region.difference { start := 10, size := 10 } { start := 13, size := 2 }
  assert (split == [{ start := 10, size := 3 }, { start := 15, size := 5 }]) "difference can split into two pieces"

  let zeroInside : Radix.Memory.Spec.Region := { start := 12, size := 0 }
  assert (!decide (Radix.Memory.Spec.Region.intersects zeroInside a)) "zero-sized region does not intersect"
  assert (Radix.Memory.Spec.Region.union? zeroInside a == some a) "empty left union returns right"
  assert (Radix.Memory.Spec.Region.union? a zeroInside == some a) "empty right union returns left"
  assert (Radix.Memory.Spec.Region.difference a zeroInside == [a]) "difference by empty region preserves source"

  c.get
