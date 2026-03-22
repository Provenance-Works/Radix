import Radix.Memory

/-!
# Example: Region Algebra
-/

namespace Examples.RegionAlgebraDemo

def main : IO Unit := do
  IO.println "━━━ Region Algebra Example ━━━"
  let a : Radix.Memory.Spec.Region := { start := 8, size := 8 }
  let b : Radix.Memory.Spec.Region := { start := 12, size := 8 }
  let inter := Radix.Memory.Spec.Region.intersection a b
  let span := Radix.Memory.Spec.Region.span a b
  let diff := Radix.Memory.Spec.Region.difference a b
  IO.println s!"  Intersection: start={inter.start} size={inter.size}"
  IO.println s!"  Span:         start={span.start} size={span.size}"
  IO.println s!"  Difference:   {reprStr diff}"

end Examples.RegionAlgebraDemo
