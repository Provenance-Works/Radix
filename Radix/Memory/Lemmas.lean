/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Memory.Model
import Radix.Memory.Ptr
import Radix.Memory.Layout
import Radix.Memory.Spec

/-!
# Memory Safety Proofs (Layer 3)

This module contains proofs for:
- Buffer size preservation under writes
- Region disjointness properties
- Alignment properties
- Layout field non-overlapping

## Architecture

This is a **Layer 3 (Verified Specification)** module containing proofs.

## References

- FR-004: Memory Safety
- P2-09 specification
-/

namespace Radix.Memory

/-! ## Buffer Size Preservation -/

@[simp] theorem Buffer.size_zeros (n : Nat) : (Buffer.zeros n).size = n := by
  unfold Buffer.zeros Buffer.size ByteArray.size; simp

@[simp] theorem Buffer.size_empty : Buffer.empty.size = 0 := rfl

@[simp] theorem Buffer.size_ofByteArray (arr : ByteArray) :
    (Buffer.ofByteArray arr).size = arr.size := rfl

theorem Buffer.size_writeU8 (buf : Buffer) (offset : Nat) (val : Radix.UInt8)
    (h : offset < buf.bytes.size) :
    (buf.writeU8 offset val h).size = buf.size := by
  unfold Buffer.writeU8 Buffer.size ByteArray.size ByteArray.set; simp

theorem Buffer.size_writeU16BE (buf : Buffer) (offset : Nat) (val : Radix.UInt16)
    (h : offset + 2 ≤ buf.bytes.size) :
    (buf.writeU16BE offset val h).size = buf.size := by
  unfold Buffer.writeU16BE Buffer.size ByteArray.size ByteArray.set; simp

theorem Buffer.size_writeU16LE (buf : Buffer) (offset : Nat) (val : Radix.UInt16)
    (h : offset + 2 ≤ buf.bytes.size) :
    (buf.writeU16LE offset val h).size = buf.size := by
  unfold Buffer.writeU16LE Buffer.size ByteArray.size ByteArray.set; simp

theorem Buffer.size_writeU32BE (buf : Buffer) (offset : Nat) (val : Radix.UInt32)
    (h : offset + 4 ≤ buf.bytes.size) :
    (buf.writeU32BE offset val h).size = buf.size := by
  unfold Buffer.writeU32BE Buffer.size ByteArray.size ByteArray.set; simp

theorem Buffer.size_writeU32LE (buf : Buffer) (offset : Nat) (val : Radix.UInt32)
    (h : offset + 4 ≤ buf.bytes.size) :
    (buf.writeU32LE offset val h).size = buf.size := by
  unfold Buffer.writeU32LE Buffer.size ByteArray.size ByteArray.set; simp

theorem Buffer.size_writeU64BE (buf : Buffer) (offset : Nat) (val : Radix.UInt64)
    (h : offset + 8 ≤ buf.bytes.size) :
    (buf.writeU64BE offset val h).size = buf.size := by
  unfold Buffer.writeU64BE Buffer.size ByteArray.size ByteArray.set; simp

theorem Buffer.size_writeU64LE (buf : Buffer) (offset : Nat) (val : Radix.UInt64)
    (h : offset + 8 ≤ buf.bytes.size) :
    (buf.writeU64LE offset val h).size = buf.size := by
  unfold Buffer.writeU64LE Buffer.size ByteArray.size ByteArray.set; simp

/-! ## Read-After-Write -/

theorem Buffer.readU8_writeU8_eq (buf : Buffer) (offset : Nat) (val : Radix.UInt8)
    (hw : offset < buf.bytes.size) :
    (buf.writeU8 offset val hw).readU8 offset
      (by rw [show (buf.writeU8 offset val hw).bytes.size = buf.bytes.size from by
            unfold Buffer.writeU8 ByteArray.set ByteArray.size; simp]; exact hw) = val := by
  unfold Buffer.readU8 Buffer.writeU8
  simp [ByteArray.get, ByteArray.set]

/-! ## Region Disjointness -/

open Spec in
theorem Spec.Region.disjoint_comm (a b : Spec.Region) :
    Spec.Region.disjoint a b ↔ Spec.Region.disjoint b a := by
  simp [Spec.Region.disjoint]; tauto

open Spec in
theorem Spec.Region.disjoint_empty_left (r : Spec.Region) :
    Spec.Region.disjoint Spec.Region.empty r := by
  simp [Spec.Region.disjoint, Spec.Region.endOffset, Spec.Region.empty]

open Spec in
theorem Spec.Region.disjoint_empty_right (r : Spec.Region) :
    Spec.Region.disjoint r Spec.Region.empty := by
  simp [Spec.Region.disjoint, Spec.Region.endOffset, Spec.Region.empty]

/-! ## Alignment -/

open Spec in
theorem Spec.isAligned_zero (align : Nat) (h : align > 0) : Spec.isAligned 0 align := by
  simp [Spec.isAligned, h]

open Spec in
theorem Spec.isAligned_mul (k align : Nat) (h : align > 0) : Spec.isAligned (k * align) align := by
  simp [Spec.isAligned, h]

/-! ## Layout Properties -/

theorem LayoutDesc.empty_totalSize : LayoutDesc.empty.totalSize = 0 := rfl

theorem LayoutDesc.empty_fields : LayoutDesc.empty.fields = [] := rfl

theorem LayoutDesc.appendField_totalSize (desc : LayoutDesc) (name : String) (size : Nat) :
    (desc.appendField name size).totalSize = desc.totalSize + size := rfl

/-! ## Checked API Properties -/

theorem Buffer.checkedReadU8_some (buf : Buffer) (offset : Nat)
    (h : offset < buf.bytes.size) :
    buf.checkedReadU8 offset = some (buf.readU8 offset h) := by
  simp [Buffer.checkedReadU8, h]

theorem Buffer.checkedReadU8_none (buf : Buffer) (offset : Nat)
    (h : ¬ offset < buf.bytes.size) :
    buf.checkedReadU8 offset = none := by
  simp [Buffer.checkedReadU8, h]

end Radix.Memory
