/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Alignment Specification (Layer 3)

Formal specification of alignment operations used throughout the Memory
and BareMetal subsystems.

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.
- Defines the canonical semantics for alignment operations.

## References

- v0.2.0 Roadmap: Alignment Utilities
- FR-004: Memory Safety
-/

namespace Radix.Alignment.Spec

/-! ## Core Definitions -/

/-- An address/offset is aligned to `align` when `align > 0` and
    `offset` is a multiple of `align`. -/
def isAligned (offset align : Nat) : Prop :=
  align > 0 ∧ offset % align = 0

instance (offset align : Nat) : Decidable (isAligned offset align) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Round `offset` up to the next multiple of `align`.
    Requires `align > 0`. Result is the smallest `m ≥ offset` such that
    `align ∣ m`. -/
def alignUp (offset align : Nat) : Nat :=
  if align == 0 then offset
  else ((offset + align - 1) / align) * align

/-- Round `offset` down to the previous multiple of `align`.
    Requires `align > 0`. Result is the largest `m ≤ offset` such that
    `align ∣ m`. -/
def alignDown (offset align : Nat) : Nat :=
  if align == 0 then offset
  else (offset / align) * align

/-- Check whether `align` is a power of two. Power-of-two alignment
    enables efficient bit-mask operations. -/
def isPowerOfTwo (n : Nat) : Prop := n > 0 ∧ n &&& (n - 1) = 0

instance (n : Nat) : Decidable (isPowerOfTwo n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The alignment padding needed to reach the next aligned offset. -/
def alignPadding (offset align : Nat) : Nat :=
  if align == 0 then 0
  else (align - offset % align) % align

end Radix.Alignment.Spec
