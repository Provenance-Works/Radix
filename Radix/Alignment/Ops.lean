/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Alignment.Spec
import Radix.Word.UInt

/-!
# Alignment Operations (Layer 2)

Concrete alignment utility functions operating on `Nat` and Radix integer
types. All operations are `@[inline]` for zero-cost abstraction.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- v0.2.0 Roadmap: Alignment Utilities
- FR-004: Memory Safety
-/

namespace Radix.Alignment

open Radix.Alignment.Spec

/-! ## Nat-Level Operations -/

/-- Check if `offset` is aligned to `align`. Returns `false` when `align = 0`. -/
@[inline] def isAligned (offset align : Nat) : Bool :=
  align > 0 && offset % align == 0

/-- Round `offset` up to the nearest multiple of `align`.
    Returns `offset` when `align = 0`. -/
@[inline] def alignUp (offset align : Nat) : Nat :=
  if align == 0 then offset
  else ((offset + align - 1) / align) * align

/-- Round `offset` down to the nearest multiple of `align`.
    Returns `offset` when `align = 0`. -/
@[inline] def alignDown (offset align : Nat) : Nat :=
  if align == 0 then offset
  else (offset / align) * align

/-- Compute the padding bytes needed to align `offset`. -/
@[inline] def alignPadding (offset align : Nat) : Nat :=
  if align == 0 then 0
  else (align - offset % align) % align

/-- Check if `n` is a power of two (> 0 and exactly one bit set). -/
@[inline] def isPowerOfTwo (n : Nat) : Bool :=
  n > 0 && n &&& (n - 1) == 0

/-! ## Power-of-Two Fast Paths

When `align` is a power of two, alignment operations can use bit masks
instead of division. These are the preferred implementations at runtime. -/

/-- Fast `alignUp` for power-of-two alignment via bit mask.
    Requires: `align` is a power of two. -/
@[inline] def alignUpPow2 (offset align : Nat) : Nat :=
  (offset + align - 1) &&& (0 - align)

/-- Fast `alignDown` for power-of-two alignment via bit mask.
    Requires: `align` is a power of two. -/
@[inline] def alignDownPow2 (offset align : Nat) : Nat :=
  offset &&& (0 - align)

/-- Fast `isAligned` check for power-of-two alignment.
    Requires: `align` is a power of two. -/
@[inline] def isAlignedPow2 (offset align : Nat) : Bool :=
  offset &&& (align - 1) == 0

/-! ## Type-Specific Alignment Functions -/

/-- Alignment of a `UInt8` has alignment 1. -/
@[inline] def alignmentOfU8 : Nat := 1

/-- Alignment of a `UInt16` value. -/
@[inline] def alignmentOfU16 : Nat := 2

/-- Alignment of a `UInt32` value. -/
@[inline] def alignmentOfU32 : Nat := 4

/-- Alignment of a `UInt64` value. -/
@[inline] def alignmentOfU64 : Nat := 8

/-- Typeclass for types with known natural alignment. -/
class HasAlignment (α : Type) where
  alignment : Nat
  alignment_pos : alignment > 0
  alignment_pow2 : isPowerOfTwo alignment = true

instance : HasAlignment Radix.UInt8 where
  alignment := 1
  alignment_pos := by decide
  alignment_pow2 := by native_decide

instance : HasAlignment Radix.UInt16 where
  alignment := 2
  alignment_pos := by decide
  alignment_pow2 := by native_decide

instance : HasAlignment Radix.UInt32 where
  alignment := 4
  alignment_pos := by decide
  alignment_pow2 := by native_decide

instance : HasAlignment Radix.UInt64 where
  alignment := 8
  alignment_pos := by decide
  alignment_pow2 := by native_decide

/-- Get the natural alignment for a type. -/
@[inline] def alignmentOf (α : Type) [HasAlignment α] : Nat :=
  HasAlignment.alignment (α := α)

end Radix.Alignment
