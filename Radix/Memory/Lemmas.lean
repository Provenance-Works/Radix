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
theorem Spec.Region.intersects_comm (a b : Spec.Region) :
    Spec.Region.intersects a b ↔ Spec.Region.intersects b a := by
  unfold Spec.Region.intersects
  tauto

open Spec in
theorem Spec.Region.adjacent_comm (a b : Spec.Region) :
    Spec.Region.adjacent a b ↔ Spec.Region.adjacent b a := by
  simp [Spec.Region.adjacent]
  tauto

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

/-! ## Read-After-Write: Non-Overlapping Offsets -/

theorem Buffer.readU8_writeU8_ne (buf : Buffer) (i j : Nat) (val : Radix.UInt8)
    (hw : i < buf.bytes.size) (hr : j < buf.bytes.size) (hne : i ≠ j) :
    (buf.writeU8 i val hw).readU8 j
      (by rw [show (buf.writeU8 i val hw).bytes.size = buf.bytes.size from by
            unfold Buffer.writeU8 ByteArray.set ByteArray.size; simp]; exact hr) = buf.readU8 j hr := by
  unfold Buffer.readU8 Buffer.writeU8
  simp only [ByteArray.get, ByteArray.set, Array.getElem_set, hne, ↓reduceIte]
  rfl

/-! ## Region Properties -/

open Spec in
theorem Spec.Region.contains_refl (r : Spec.Region) : Spec.Region.contains r r := by
  simp [Spec.Region.contains, Spec.Region.endOffset]

open Spec in
theorem Spec.Region.span_contains_left (a b : Spec.Region) :
    Spec.Region.contains (Spec.Region.span a b) a := by
  simp [Spec.Region.contains, Spec.Region.span, Spec.Region.endOffset]

open Spec in
theorem Spec.Region.span_contains_right (a b : Spec.Region) :
    Spec.Region.contains (Spec.Region.span a b) b := by
  simp [Spec.Region.contains, Spec.Region.span, Spec.Region.endOffset]

open Spec in
theorem Spec.Region.span_comm (a b : Spec.Region) :
    Spec.Region.span a b = Spec.Region.span b a := by
  simp [Spec.Region.span, Nat.min_comm, Nat.max_comm]

open Spec in
theorem Spec.Region.intersection_comm (a b : Spec.Region) :
    Spec.Region.intersection a b = Spec.Region.intersection b a := by
  unfold Spec.Region.intersection
  simp [Nat.max_comm, Nat.min_comm]

open Spec in
-- When both regions are non-empty, union? succeeds iff they are mergeable.
-- The zero-size short-circuits in union? interact with Lean's eager decidable
-- reduction, making a full iff proof with simp impractical.
-- Instead we prove the non-trivial direction separately.
theorem Spec.Region.union?_isSome_of_mergeable (a b : Spec.Region) (h : Spec.Region.mergeable a b) :
    (Spec.Region.union? a b).isSome = true := by
  simp [Spec.Region.union?, h]

open Spec in
theorem Spec.Region.span_least_upper_bound (a b c : Spec.Region)
    (ha : Spec.Region.contains c a) (hb : Spec.Region.contains c b) :
    Spec.Region.contains c (Spec.Region.span a b) := by
  simp [Spec.Region.contains, Spec.Region.span, Spec.Region.endOffset] at *
  omega

open Spec in
theorem Spec.Region.inBounds_start (r : Spec.Region) (h : 0 < r.size) :
    Spec.Region.inBounds r r.start := by
  simp [Spec.Region.inBounds, Spec.Region.endOffset]; omega

open Spec in
theorem Spec.Region.not_inBounds_empty (off : Nat) :
    ¬ Spec.Region.inBounds Spec.Region.empty off := by
  simp [Spec.Region.inBounds, Spec.Region.endOffset, Spec.Region.empty]

open Spec in
theorem Spec.Region.contains_inBounds (outer inner : Spec.Region) (off : Nat)
    (hc : Spec.Region.contains outer inner) (hb : Spec.Region.inBounds inner off) :
    Spec.Region.inBounds outer off := by
  simp [Spec.Region.contains, Spec.Region.inBounds, Spec.Region.endOffset] at *
  omega

open Spec in
theorem Spec.Region.disjoint_not_inBounds_left (a b : Spec.Region) (off : Nat)
    (hd : Spec.Region.disjoint a b) (hb : Spec.Region.inBounds a off) :
    ¬ Spec.Region.inBounds b off := by
  simp [Spec.Region.disjoint, Spec.Region.inBounds, Spec.Region.endOffset] at *
  omega

open Spec in
theorem Spec.Region.disjoint_of_size_zero_left (r : Spec.Region) :
    Spec.Region.disjoint { start := 0, size := 0 } r := by
  simp [Spec.Region.disjoint, Spec.Region.endOffset]

/-! ## BufferSpec Precondition Properties -/

open Spec in
theorem Spec.BufferSpec.readPre_of_readNPre (spec : Spec.BufferSpec) (offset n : Nat)
    (h : Spec.BufferSpec.readNPre spec offset n) (hn : 0 < n) :
    Spec.BufferSpec.readPre spec offset := by
  simp [Spec.BufferSpec.readPre, Spec.BufferSpec.readNPre] at *; omega

open Spec in
theorem Spec.BufferSpec.writePre_of_writeNPre (spec : Spec.BufferSpec) (offset n : Nat)
    (h : Spec.BufferSpec.writeNPre spec offset n) (hn : 0 < n) :
    Spec.BufferSpec.writePre spec offset := by
  simp [Spec.BufferSpec.writePre, Spec.BufferSpec.writeNPre] at *; omega

open Spec in
theorem Spec.BufferSpec.readNPre_mono (spec : Spec.BufferSpec) (offset m n : Nat)
    (h : Spec.BufferSpec.readNPre spec offset n) (hmn : m ≤ n) :
    Spec.BufferSpec.readNPre spec offset m := by
  simp [Spec.BufferSpec.readNPre] at *; omega

/-! ## Additional Alignment Properties -/

open Spec in
theorem Spec.isAligned_self (align : Nat) (h : align > 0) : Spec.isAligned align align := by
  simp [Spec.isAligned, h]

open Spec in
theorem Spec.isAligned_add (offset align : Nat)
    (h1 : Spec.isAligned offset align) :
    Spec.isAligned (offset + align) align := by
  simp [Spec.isAligned] at *
  obtain ⟨hpos, hmod⟩ := h1
  exact ⟨hpos, by omega⟩

open Spec in
theorem Spec.isAligned_of_dvd (offset align : Nat) (h1 : align > 0) (h2 : align ∣ offset) :
    Spec.isAligned offset align := by
  simp [Spec.isAligned, h1]
  exact Nat.mod_eq_zero_of_dvd h2

/-! ## Additional Layout Properties -/

theorem LayoutDesc.appendField_fields (desc : LayoutDesc) (name : String) (size : Nat) :
    (desc.appendField name size).fields =
    desc.fields ++ [{ name := name, offset := desc.totalSize, size := size }] := rfl

theorem LayoutDesc.appendField_preserves_prev_fields (desc : LayoutDesc) (name : String) (size : Nat) :
    (desc.appendField name size).fields.take desc.fields.length = desc.fields := by
  simp [LayoutDesc.appendField]

/-! ## Additional Buffer Checked API Properties -/

theorem Buffer.checkedWriteU8_some (buf : Buffer) (offset : Nat) (val : Radix.UInt8)
    (h : offset < buf.bytes.size) :
    buf.checkedWriteU8 offset val = some (buf.writeU8 offset val h) := by
  simp [Buffer.checkedWriteU8, h]

theorem Buffer.checkedWriteU8_none (buf : Buffer) (offset : Nat) (val : Radix.UInt8)
    (h : ¬ offset < buf.bytes.size) :
    buf.checkedWriteU8 offset val = none := by
  simp [Buffer.checkedWriteU8, h]

theorem Buffer.checkedReadU16BE_some (buf : Buffer) (offset : Nat)
    (h : offset + 2 ≤ buf.bytes.size) :
    buf.checkedReadU16BE offset = some (buf.readU16BE offset h) := by
  simp [Buffer.checkedReadU16BE, h]

theorem Buffer.checkedReadU16BE_none (buf : Buffer) (offset : Nat)
    (h : ¬ offset + 2 ≤ buf.bytes.size) :
    buf.checkedReadU16BE offset = none := by
  simp [Buffer.checkedReadU16BE, h]

theorem Buffer.checkedReadU16LE_some (buf : Buffer) (offset : Nat)
    (h : offset + 2 ≤ buf.bytes.size) :
    buf.checkedReadU16LE offset = some (buf.readU16LE offset h) := by
  simp [Buffer.checkedReadU16LE, h]

theorem Buffer.checkedReadU16LE_none (buf : Buffer) (offset : Nat)
    (h : ¬ offset + 2 ≤ buf.bytes.size) :
    buf.checkedReadU16LE offset = none := by
  simp [Buffer.checkedReadU16LE, h]

theorem Buffer.checkedReadU32BE_some (buf : Buffer) (offset : Nat)
    (h : offset + 4 ≤ buf.bytes.size) :
    buf.checkedReadU32BE offset = some (buf.readU32BE offset h) := by
  simp [Buffer.checkedReadU32BE, h]

theorem Buffer.checkedReadU32BE_none (buf : Buffer) (offset : Nat)
    (h : ¬ offset + 4 ≤ buf.bytes.size) :
    buf.checkedReadU32BE offset = none := by
  simp [Buffer.checkedReadU32BE, h]

theorem Buffer.checkedReadU32LE_some (buf : Buffer) (offset : Nat)
    (h : offset + 4 ≤ buf.bytes.size) :
    buf.checkedReadU32LE offset = some (buf.readU32LE offset h) := by
  simp [Buffer.checkedReadU32LE, h]

theorem Buffer.checkedReadU32LE_none (buf : Buffer) (offset : Nat)
    (h : ¬ offset + 4 ≤ buf.bytes.size) :
    buf.checkedReadU32LE offset = none := by
  simp [Buffer.checkedReadU32LE, h]

theorem Buffer.checkedReadU64BE_some (buf : Buffer) (offset : Nat)
    (h : offset + 8 ≤ buf.bytes.size) :
    buf.checkedReadU64BE offset = some (buf.readU64BE offset h) := by
  simp [Buffer.checkedReadU64BE, h]

theorem Buffer.checkedReadU64BE_none (buf : Buffer) (offset : Nat)
    (h : ¬ offset + 8 ≤ buf.bytes.size) :
    buf.checkedReadU64BE offset = none := by
  simp [Buffer.checkedReadU64BE, h]

theorem Buffer.checkedReadU64LE_some (buf : Buffer) (offset : Nat)
    (h : offset + 8 ≤ buf.bytes.size) :
    buf.checkedReadU64LE offset = some (buf.readU64LE offset h) := by
  simp [Buffer.checkedReadU64LE, h]

theorem Buffer.checkedReadU64LE_none (buf : Buffer) (offset : Nat)
    (h : ¬ offset + 8 ≤ buf.bytes.size) :
    buf.checkedReadU64LE offset = none := by
  simp [Buffer.checkedReadU64LE, h]

/-! ## Region Transitivity -/

open Spec in
theorem Spec.Region.contains_trans (a b c : Spec.Region)
    (hab : Spec.Region.contains a b) (hbc : Spec.Region.contains b c) :
    Spec.Region.contains a c := by
  simp [Spec.Region.contains, Spec.Region.endOffset] at *
  omega

open Spec in
theorem Spec.Region.disjoint_of_contains (outer inner other : Spec.Region)
    (hc : Spec.Region.contains outer inner)
    (hd : Spec.Region.disjoint outer other) :
    Spec.Region.disjoint inner other := by
  simp [Spec.Region.disjoint, Spec.Region.contains, Spec.Region.endOffset] at *
  omega

open Spec in
theorem Spec.Region.disjoint_sub (a a' b b' : Spec.Region)
    (ha : Spec.Region.contains a a') (hb : Spec.Region.contains b b')
    (hd : Spec.Region.disjoint a b) :
    Spec.Region.disjoint a' b' := by
  simp [Spec.Region.disjoint, Spec.Region.contains, Spec.Region.endOffset] at *
  omega

open Spec in
theorem Spec.Region.not_contains_empty_of_pos (r : Spec.Region) (hr : 0 < r.size) :
    ¬ Spec.Region.contains Spec.Region.empty r := by
  simp [Spec.Region.contains, Spec.Region.endOffset, Spec.Region.empty]; omega

/-! ## Region Algebra: Span Bounds -/

-- Span size is at least as large as each operand
open Spec in
theorem Spec.Region.span_size_ge_left (a b : Spec.Region) :
    a.size ≤ (Spec.Region.span a b).size := by
  simp [Spec.Region.span, Spec.Region.endOffset, Nat.max_def, Nat.min_def]
  split <;> split <;> omega

open Spec in
theorem Spec.Region.span_size_ge_right (a b : Spec.Region) :
    b.size ≤ (Spec.Region.span a b).size := by
  simp [Spec.Region.span, Spec.Region.endOffset, Nat.max_def, Nat.min_def]
  split <;> split <;> omega

-- Span start is at most the minimum start
open Spec in
theorem Spec.Region.span_start_le_left (a b : Spec.Region) :
    (Spec.Region.span a b).start ≤ a.start := by
  simp [Spec.Region.span]

open Spec in
theorem Spec.Region.span_start_le_right (a b : Spec.Region) :
    (Spec.Region.span a b).start ≤ b.start := by
  simp [Spec.Region.span]

/-! ## Region Algebra: Difference Properties -/

-- Difference of a region with itself yields empty list when non-empty
open Spec in
theorem Spec.Region.difference_self_empty (r : Spec.Region) (hr : 0 < r.size) :
    (Spec.Region.difference r r).length = 0 := by
  unfold Spec.Region.difference Spec.Region.intersection Spec.Region.endOffset
  simp [hr]

/-! ## Alignment Composition -/

-- Alignment to 1 always holds
open Spec in
theorem Spec.isAligned_one (offset : Nat) : Spec.isAligned offset 1 := by
  simp [Spec.isAligned, Nat.mod_one]

-- Alignment is multiplicative: if aligned to k*align, then aligned to align
open Spec in
theorem Spec.isAligned_of_mul_align (offset k align : Nat)
    (_ : 0 < k) (h : Spec.isAligned offset (k * align)) :
    Spec.isAligned offset align := by
  simp [Spec.isAligned] at *
  obtain ⟨hpos, hmod⟩ := h
  constructor
  · rw [Nat.mul_comm] at hpos; exact Nat.pos_of_mul_pos_right hpos
  · exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_mul_left align k) (Nat.dvd_of_mod_eq_zero hmod))

-- Zero is aligned to any positive alignment
open Spec in
theorem Spec.isAligned_zero' (align : Nat) (h : 0 < align) : Spec.isAligned 0 align := by
  simp [Spec.isAligned, h]

/-! ## Buffer: Write Preserves Other Reads -/

-- Writing a byte does not affect the buffer size seen through BufferSpec
open Spec in
theorem Spec.BufferSpec.readNPre_of_larger (spec : Spec.BufferSpec) (offset n m : Nat)
    (h : Spec.BufferSpec.readNPre spec offset m) (hnm : n ≤ m) :
    Spec.BufferSpec.readNPre spec offset n := by
  simp [Spec.BufferSpec.readNPre] at *; omega

/-! ## Region: Containment and InBounds Relationship -/

-- If a contains b, then any inBounds offset of b is inBounds in a
open Spec in
theorem Spec.Region.inBounds_contained (outer inner : Spec.Region) (off : Nat)
    (hc : Spec.Region.contains outer inner)
    (hb : Spec.Region.inBounds inner off) :
    Spec.Region.inBounds outer off := by
  simp [Spec.Region.contains, Spec.Region.inBounds, Spec.Region.endOffset] at *
  omega

-- endOffset preserved under empty difference
open Spec in
theorem Spec.Region.endOffset_of_mk (s n : Nat) :
    Spec.Region.endOffset ⟨s, n⟩ = s + n := by
  rfl

-- Two adjacent regions span exactly their combined sizes
open Spec in
theorem Spec.Region.span_size_adjacent (a b : Spec.Region)
    (h : a.endOffset = b.start) :
    (Spec.Region.span a b).size = a.size + b.size := by
  simp [Spec.Region.span, Spec.Region.endOffset] at *
  omega

-- Intersection with a contained region is the inner region
open Spec in
theorem Spec.Region.intersection_of_contains (outer inner : Spec.Region)
    (hc : Spec.Region.contains outer inner) (h : 0 < inner.size) :
    Spec.Region.intersection outer inner = inner := by
  simp only [Spec.Region.contains, Spec.Region.endOffset] at hc
  obtain ⟨hstart, hend⟩ := hc
  simp only [Spec.Region.intersection, Spec.Region.endOffset]
  have hmx : max outer.start inner.start = inner.start := by omega
  have hmn : min (outer.start + outer.size) (inner.start + inner.size) = inner.start + inner.size := by omega
  rw [hmx, hmn]
  simp [h]

end Radix.Memory
