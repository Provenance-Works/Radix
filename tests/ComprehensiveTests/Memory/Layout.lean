import tests.ComprehensiveTests.Framework
import Radix.Memory.Layout
import Radix.Memory.Spec

/-!
# Memory Layout Tests
## Spec References
- FR-004: LayoutDesc construction, field append, alignment, validity
-/

open ComprehensiveTests

def runMemoryLayoutTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Memory layout tests..."

  -- ## Empty layout
  let empty := Radix.Memory.LayoutDesc.empty
  assert (empty.totalSize == 0) "empty totalSize"
  assert (empty.fields.length == 0) "empty fields"
  assert (empty.isNonOverlapping == true) "empty non-overlapping"
  assert (empty.allFieldsFit == true) "empty all fields fit"

  -- ## Single field
  let l1 := empty.appendField "x" 4
  assert (l1.totalSize == 4) "single field totalSize"
  assert (l1.fields.length == 1) "single field count"
  match l1.findField "x" with
  | some f =>
    assert (f.offset == 0) "field x offset"
    assert (f.size == 4) "field x size"
    assert (f.name == "x") "field x name"
  | none => assert false "field x not found"
  assert (l1.isNonOverlapping == true) "single field non-overlapping"
  assert (l1.allFieldsFit == true) "single field fits"

  -- ## Multiple fields
  let l2 := l1.appendField "y" 2
  assert (l2.totalSize == 6) "two fields totalSize"
  assert (l2.fields.length == 2) "two fields count"
  match l2.findField "y" with
  | some f =>
    assert (f.offset == 4) "field y offset"
    assert (f.size == 2) "field y size"
  | none => assert false "field y not found"

  let l3 := l2.appendField "z" 8
  assert (l3.totalSize == 14) "three fields totalSize"
  assert (l3.isNonOverlapping == true) "three fields non-overlapping"
  assert (l3.allFieldsFit == true) "three fields fit"

  -- ## Field lookup miss
  assert (l1.findField "nonexistent" == none) "lookup miss"
  assert (empty.findField "x" == none) "lookup empty"

  -- ## Aligned append
  let al := empty.appendAligned "a" 1 4 (by omega)
  assert (al.totalSize ≥ 1) "aligned field totalSize ≥ 1"
  match al.findField "a" with
  | some f =>
    assert (f.size == 1) "aligned field size"
    -- offset should be 0 (start of empty layout, aligned to 4)
    assert (f.offset == 0) "aligned field offset"
  | none => assert false "aligned field not found"

  -- Add another aligned field
  let al2 := al.appendAligned "b" 2 4 (by omega)
  match al2.findField "b" with
  | some f =>
    -- Should be at offset aligned to 4
    assert (f.offset % 4 == 0) "second aligned field offset"
    assert (f.size == 2) "second aligned field size"
  | none => assert false "second aligned field not found"

  -- ## Zero-size fields
  let lz := empty.appendField "empty" 0
  assert (lz.totalSize == 0) "zero-size field totalSize"

  -- ## Large layout
  let mut large := empty
  for i in [:20] do
    large := large.appendField s!"field_{i}" 4
  assert (large.totalSize == 80) "20 fields × 4 bytes"
  assert (large.fields.length == 20) "20 fields count"
  assert (large.isNonOverlapping == true) "20 fields non-overlapping"
  assert (large.allFieldsFit == true) "20 fields fit"

  -- ## Region spec
  let r := Radix.Memory.Spec.Region.empty
  assert (r.start == 0) "Region empty start"
  assert (r.size == 0) "Region empty size"
  assert (r.endOffset == 0) "Region empty endOffset"

  let r1 : Radix.Memory.Spec.Region := ⟨10, 20⟩
  assert (r1.endOffset == 30) "Region endOffset"

  -- Disjoint regions
  let r2 : Radix.Memory.Spec.Region := ⟨40, 10⟩
  assert (Decidable.decide (Radix.Memory.Spec.Region.disjoint r1 r2) == true) "disjoint regions"

  -- Overlapping regions
  let r3 : Radix.Memory.Spec.Region := ⟨25, 10⟩
  assert (Decidable.decide (Radix.Memory.Spec.Region.disjoint r1 r3) == false) "overlapping regions"

  -- Contains
  assert (Decidable.decide (Radix.Memory.Spec.Region.inBounds r1 15) == true) "inBounds"
  assert (Decidable.decide (Radix.Memory.Spec.Region.inBounds r1 5) == false) "not inBounds"

  -- ## Alignment spec
  assert (Decidable.decide (Radix.Memory.Spec.isAligned 0 4) == true) "aligned 0 to 4"
  assert (Decidable.decide (Radix.Memory.Spec.isAligned 8 4) == true) "aligned 8 to 4"
  assert (Decidable.decide (Radix.Memory.Spec.isAligned 16 8) == true) "aligned 16 to 8"
  assert (Decidable.decide (Radix.Memory.Spec.isAligned 3 4) == false) "not aligned 3 to 4"
  assert (Decidable.decide (Radix.Memory.Spec.isAligned 7 4) == false) "not aligned 7 to 4"

  c.get
