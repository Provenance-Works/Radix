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

end Radix.Memory
