/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Memory.Model
import Radix.Memory.Spec

/-!
# Packed Struct Layout (Layer 2)

This module provides data types for describing the layout of packed
binary structures (field offsets, sizes, alignment) and functions to
compute layout properties.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- FR-004.3: Memory layout computation
- P2-08 specification
-/

namespace Radix.Memory

/-! ## Field Descriptor -/

/-- Describes a single field in a packed structure. -/
structure FieldDesc where
  /-- Human-readable field name. -/
  name   : String
  /-- Byte offset from the start of the structure. -/
  offset : Nat
  /-- Size of the field in bytes. -/
  size   : Nat
  deriving DecidableEq, Repr

/-! ## Layout Descriptor -/

/-- Describes the complete layout of a packed binary structure. -/
structure LayoutDesc where
  /-- Ordered list of field descriptors. -/
  fields    : List FieldDesc
  /-- Total size of the structure in bytes (including any tail padding). -/
  totalSize : Nat
  deriving Repr

namespace LayoutDesc

/-- An empty layout. -/
def empty : LayoutDesc := ⟨[], 0⟩

/-- Look up a field by name. -/
def findField (desc : LayoutDesc) (name : String) : Option FieldDesc :=
  desc.fields.find? (·.name == name)

/-- Append a field to the layout. The field is placed at the current end. -/
def appendField (desc : LayoutDesc) (name : String) (size : Nat) : LayoutDesc :=
  let field : FieldDesc := ⟨name, desc.totalSize, size⟩
  ⟨desc.fields ++ [field], desc.totalSize + size⟩

/-- Append a field with explicit alignment padding.
    Inserts padding bytes so that the field starts at an aligned offset.
    The proof `_hAlign` is reserved for future alignment correctness
    proofs (e.g., ensuring the aligned offset is valid). -/
def appendAligned (desc : LayoutDesc) (name : String) (size align : Nat)
    (_hAlign : align > 0) : LayoutDesc :=
  let padding := (align - desc.totalSize % align) % align
  let offset := desc.totalSize + padding
  let field : FieldDesc := ⟨name, offset, size⟩
  ⟨desc.fields ++ [field], offset + size⟩

/-- Check that no two fields overlap.
    Note: O(n^2) in the number of fields due to pairwise comparison.
    Sufficient for typical binary format field counts (<50 fields). -/
def isNonOverlapping (desc : LayoutDesc) : Bool :=
  desc.fields.all fun a =>
    desc.fields.all fun b =>
      a == b || a.offset + a.size ≤ b.offset || b.offset + b.size ≤ a.offset

/-- Check that all fields fit within the total size. -/
def allFieldsFit (desc : LayoutDesc) : Bool :=
  desc.fields.all (fun f => f.offset + f.size ≤ desc.totalSize)

end LayoutDesc

/-! ## Layout Correctness Properties -/

/-- Empty layout has no fields. -/
theorem LayoutDesc.empty_fields : LayoutDesc.empty.fields = [] := rfl

/-- Empty layout has zero total size. -/
theorem LayoutDesc.empty_totalSize : LayoutDesc.empty.totalSize = 0 := rfl

/-- Empty layout is non-overlapping. -/
theorem LayoutDesc.empty_isNonOverlapping : LayoutDesc.empty.isNonOverlapping = true := by
  native_decide

/-- Empty layout has all fields fit. -/
theorem LayoutDesc.empty_allFieldsFit : LayoutDesc.empty.allFieldsFit = true := by
  native_decide

/-- appendField increases totalSize by the field size. -/
theorem LayoutDesc.appendField_totalSize (desc : LayoutDesc) (name : String) (size : Nat) :
    (desc.appendField name size).totalSize = desc.totalSize + size := by
  simp [LayoutDesc.appendField]

/-- appendField places field at current end. -/
theorem LayoutDesc.appendField_last_offset (desc : LayoutDesc) (name : String) (size : Nat) :
    let desc' := desc.appendField name size
    desc'.fields.getLast? = some ⟨name, desc.totalSize, size⟩ := by
  simp [LayoutDesc.appendField, List.getLast?_append]

/-- appendAligned totalSize is at least appendField totalSize. -/
theorem LayoutDesc.appendAligned_totalSize_ge (desc : LayoutDesc) (name : String)
    (size align : Nat) (hAlign : align > 0) :
    (desc.appendAligned name size align hAlign).totalSize ≥ desc.totalSize + size := by
  simp [LayoutDesc.appendAligned]

-- ════════════════════════════════════════════════════════════════════
-- Concrete Test Vectors
-- ════════════════════════════════════════════════════════════════════

private def layout1 : LayoutDesc :=
  LayoutDesc.empty
    |>.appendField "magic" 4
    |>.appendField "version" 2
    |>.appendField "length" 4

/-- layout1 has 3 fields. -/
example : layout1.fields.length = 3 := by native_decide

/-- layout1 total size is 10. -/
example : layout1.totalSize = 10 := by native_decide

/-- layout1 is non-overlapping. -/
example : layout1.isNonOverlapping = true := by native_decide

/-- layout1 all fields fit. -/
example : layout1.allFieldsFit = true := by native_decide

/-- layout1 magic field is at offset 0. -/
example : (layout1.findField "magic") = some ⟨"magic", 0, 4⟩ := by native_decide

/-- layout1 version field is at offset 4. -/
example : (layout1.findField "version") = some ⟨"version", 4, 2⟩ := by native_decide

/-- layout1 length field is at offset 6. -/
example : (layout1.findField "length") = some ⟨"length", 6, 4⟩ := by native_decide

end Radix.Memory
