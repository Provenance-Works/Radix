/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Memory Model Specification (Layer 3)

This module defines the abstract specification for the Memory subsystem:
- Memory regions with start address and size
- Disjointness conditions for safe non-overlapping access
- Abstract typed-access specification

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.
- Defines the formal contracts that implementations must satisfy.

## References

- FR-004: Memory Safety
- ADR C-001: No FFI -- all memory is managed by Lean GC
-/

namespace Radix.Memory.Spec

/-! ## Memory Region -/

/-- A `Region` represents a contiguous memory region defined by a start offset
    and a size (in bytes). Both are `Nat` to keep the spec layer independent
    of word width. -/
structure Region where
  start : Nat
  size  : Nat
  deriving DecidableEq, Repr

namespace Region

/-- The end offset (exclusive) of the region. -/
@[inline] def endOffset (r : Region) : Nat := r.start + r.size

/-- Whether two regions overlap at any byte. -/
def intersects (a b : Region) : Prop :=
  0 < a.size ∧ 0 < b.size ∧ a.start < b.endOffset ∧ b.start < a.endOffset

instance (a b : Region) : Decidable (intersects a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether two regions are disjoint (non-overlapping). -/
def disjoint (a b : Region) : Prop :=
  a.endOffset ≤ b.start ∨ b.endOffset ≤ a.start

instance (a b : Region) : Decidable (disjoint a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Whether two regions are exactly adjacent with no gap. -/
def adjacent (a b : Region) : Prop :=
  a.endOffset = b.start ∨ b.endOffset = a.start

instance (a b : Region) : Decidable (adjacent a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Regions can be unioned into a single interval when they overlap or touch. -/
def mergeable (a b : Region) : Prop :=
  intersects a b ∨ adjacent a b

instance (a b : Region) : Decidable (mergeable a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Whether a region fully contains another. -/
def contains (outer inner : Region) : Prop :=
  outer.start ≤ inner.start ∧ inner.endOffset ≤ outer.endOffset

instance (outer inner : Region) : Decidable (contains outer inner) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether an offset falls within the region. -/
def inBounds (r : Region) (offset : Nat) : Prop :=
  r.start ≤ offset ∧ offset < r.endOffset

instance (r : Region) (offset : Nat) : Decidable (inBounds r offset) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The empty region at offset 0. -/
def empty : Region := ⟨0, 0⟩

/-- The smallest interval containing both regions. -/
def span (a b : Region) : Region :=
  let start := min a.start b.start
  let finish := max a.endOffset b.endOffset
  ⟨start, finish - start⟩

/-- The overlapping portion of two regions, or the empty region when disjoint. -/
def intersection (a b : Region) : Region :=
  let start := max a.start b.start
  let finish := min a.endOffset b.endOffset
  if start < finish then
    ⟨start, finish - start⟩
  else
    empty

/-- Exact interval union, defined only when the result remains a single interval.
    Empty regions are neutral and return the other operand. -/
def union? (a b : Region) : Option Region :=
  if a.size = 0 then
    some b
  else if b.size = 0 then
    some a
  else if mergeable a b then
    some (span a b)
  else
    none

/-- Set difference of `a \ b`, represented as up to two residual intervals. -/
def difference (a b : Region) : List Region :=
  let inter := intersection a b
  let rawPieces :=
    if inter.size = 0 then
      [a]
    else
      let left : Option Region :=
        if a.start < inter.start then
          some ⟨a.start, inter.start - a.start⟩
        else
          none
      let right : Option Region :=
        if inter.endOffset < a.endOffset then
          some ⟨inter.endOffset, a.endOffset - inter.endOffset⟩
        else
          none
      match left, right with
      | some l, some r => [l, r]
      | some l, none => [l]
      | none, some r => [r]
      | none, none => []
  rawPieces.filter fun piece => decide (0 < piece.size)

end Region

/-! ## Buffer Spec -/

/-- Abstract specification of a memory buffer. A buffer is a finite sequence of
    bytes indexed by natural number offsets. -/
structure BufferSpec where
  /-- The number of bytes in the buffer. -/
  size : Nat

/-- Precondition for a single-byte read at `offset`. -/
def BufferSpec.readPre (spec : BufferSpec) (offset : Nat) : Prop :=
  offset < spec.size

/-- Precondition for reading `n` bytes starting at `offset`. -/
def BufferSpec.readNPre (spec : BufferSpec) (offset n : Nat) : Prop :=
  offset + n ≤ spec.size

/-- Precondition for a single-byte write at `offset`. -/
def BufferSpec.writePre (spec : BufferSpec) (offset : Nat) : Prop :=
  offset < spec.size

/-- Precondition for writing `n` bytes starting at `offset`. -/
def BufferSpec.writeNPre (spec : BufferSpec) (offset n : Nat) : Prop :=
  offset + n ≤ spec.size

/-! ## Alignment -/

/-- Whether `offset` is aligned to a power-of-two boundary `align`. -/
def isAligned (offset align : Nat) : Prop :=
  align > 0 ∧ offset % align = 0

instance (offset align : Nat) : Decidable (isAligned offset align) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ════════════════════════════════════════════════════════════════════
-- Region Algebra: Additional Properties
-- ════════════════════════════════════════════════════════════════════

/-- A zero-size region is always disjoint with any region. -/
theorem Region.disjoint_of_empty_left (b : Region) :
    Region.disjoint Region.empty b := by
  simp [Region.disjoint, Region.empty, Region.endOffset]

/-- A zero-size region contains no offsets. -/
theorem Region.not_inBounds_empty (n : Nat) :
    ¬Region.inBounds Region.empty n := by
  simp [Region.inBounds, Region.empty, Region.endOffset]

/-- Disjointness is symmetric. -/
theorem Region.disjoint_comm (a b : Region) :
    Region.disjoint a b ↔ Region.disjoint b a := by
  simp [Region.disjoint]; omega

/-- Containment is reflexive. -/
theorem Region.contains_refl (r : Region) :
    Region.contains r r := by
  simp [Region.contains]

/-- A region starting at 0 with size 0 is contained in any region starting at 0. -/
theorem Region.empty_contained_at_zero (r : Region) (hr : r.start = 0) :
    Region.contains r Region.empty := by
  simp [Region.contains, Region.empty, Region.endOffset, hr]

/-- If region a contains region b and b contains offset n, then a contains n. -/
theorem Region.inBounds_of_contains (a b : Region) (n : Nat)
    (hc : Region.contains a b) (hn : Region.inBounds b n) :
    Region.inBounds a n := by
  simp [Region.inBounds, Region.contains, Region.endOffset] at *
  omega

/-- span is commutative (the resulting region is the same). -/
theorem Region.span_comm (a b : Region) :
    Region.span a b = Region.span b a := by
  simp [Region.span]
  constructor
  · exact Nat.min_comm a.start b.start
  · rw [Nat.min_comm, Nat.max_comm]

/-- intersection of a region with itself is the region when non-empty. -/
theorem Region.intersection_self (r : Region) (h : 0 < r.size) :
    Region.intersection r r = r := by
  simp [Region.intersection, Region.endOffset]
  intro h'
  omega

/-- A zero-size region doesn't intersect with anything. -/
theorem Region.not_intersects_of_zero_size_left (a b : Region)
    (h : a.size = 0) : ¬Region.intersects a b := by
  simp [Region.intersects, h]

/-- Disjoint regions have zero intersection. -/
theorem Region.intersection_size_zero_of_disjoint (a b : Region)
    (h : Region.disjoint a b) :
    (Region.intersection a b).size = 0 := by
  simp [Region.intersection, Region.empty, Region.endOffset, Region.disjoint] at *
  split
  · omega
  · rfl

/-- A region contains itself plus any offset within its bounds. -/
theorem Region.inBounds_start (r : Region) (h : 0 < r.size) :
    Region.inBounds r r.start := by
  simp [Region.inBounds, Region.endOffset]
  omega

/-- Containment is transitive. -/
theorem Region.contains_trans (a b c : Region)
    (hab : Region.contains a b) (hbc : Region.contains b c) :
    Region.contains a c := by
  simp [Region.contains, Region.endOffset] at *
  omega

/-- Disjoint regions cannot share any offset. -/
theorem Region.disjoint_not_inBounds (a b : Region) (n : Nat)
    (hd : Region.disjoint a b) (ha : Region.inBounds a n) :
    ¬Region.inBounds b n := by
  simp [Region.disjoint, Region.inBounds, Region.endOffset] at *
  omega

/-- Two disjoint regions don't intersect (when both non-empty). -/
theorem Region.not_intersects_of_disjoint (a b : Region)
    (h : Region.disjoint a b) : ¬Region.intersects a b := by
  simp [Region.disjoint, Region.intersects, Region.endOffset] at *
  omega

end Radix.Memory.Spec
