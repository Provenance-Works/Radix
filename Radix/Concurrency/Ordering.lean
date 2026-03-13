/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Concurrency.Spec

/-!
# Memory Ordering Operations (Layer 2)

This module provides operations on memory orderings:
- Ordering strength comparison and classification
- Strengthening and weakening operations
- Fence ordering semantics
- Validity checks for load/store/RMW orderings

## Architecture

This is a **Layer 2 (Implementation)** module.
- Builds on Spec layer definitions.
- Provides operational functions for working with memory orderings.

## References

- FR-008.1: Memory Ordering
- C11 Standard, Section 7.17.3 (Memory order)
-/

set_option autoImplicit false

namespace Radix.Concurrency.Ordering

open Radix.Concurrency.Spec

/-! ## Ordering Comparison -/

/-- Total ordering on memory orders by strength.
    relaxed < acquire = release < acqRel < seqCst -/
def compare (a b : MemoryOrder) : Ordering :=
  Ord.compare a.strength b.strength

/-- Whether ordering `a` is strictly stronger than `b`. -/
def isStrongerThan (a b : MemoryOrder) : Bool :=
  a.strength > b.strength

/-! ## Strengthening and Weakening -/

/-- Strengthen an ordering to at least the given level.
    Returns the stronger of the two orderings. -/
def strengthen (current target : MemoryOrder) : MemoryOrder :=
  if target.strength > current.strength then target else current

/-- The weakest ordering that satisfies both acquire and release
    semantics. Used for RMW operations that need both. -/
def combineLoadStore (loadOrder storeOrder : MemoryOrder) : MemoryOrder :=
  match loadOrder, storeOrder with
  | .seqCst, _       => .seqCst
  | _, .seqCst        => .seqCst
  | .acquire, .release => .acqRel
  | .acqRel, _        => .acqRel
  | _, .acqRel         => .acqRel
  | .acquire, _       => .acquire
  | _, .release        => .release
  | _, _               => .relaxed

/-! ## Ordering Classification -/

/-- Whether an ordering provides acquire semantics. -/
def hasAcquireSemantics : MemoryOrder → Bool
  | .acquire => true
  | .acqRel  => true
  | .seqCst  => true
  | _        => false

/-- Whether an ordering provides release semantics. -/
def hasReleaseSemantics : MemoryOrder → Bool
  | .release => true
  | .acqRel  => true
  | .seqCst  => true
  | _        => false

/-- Whether an ordering participates in the global SeqCst total order. -/
def isSequentiallyConsistent : MemoryOrder → Bool
  | .seqCst => true
  | _       => false

/-! ## Fence Semantics -/

/-- A fence with acquire semantics prevents subsequent memory operations
    from being reordered before the fence.

    Returns true if the fence ordering provides acquire. -/
def fenceAcquires (order : MemoryOrder) : Bool :=
  hasAcquireSemantics order

/-- A fence with release semantics prevents preceding memory operations
    from being reordered after the fence.

    Returns true if the fence ordering provides release. -/
def fenceReleases (order : MemoryOrder) : Bool :=
  hasReleaseSemantics order

/-- An acquire fence followed by a relaxed load effectively forms
    an acquire load. This returns the effective ordering. -/
def effectiveLoadOrder (loadOrder fenceOrder : MemoryOrder) : MemoryOrder :=
  strengthen loadOrder fenceOrder

/-- A relaxed store followed by a release fence effectively forms
    a release store. This returns the effective ordering. -/
def effectiveStoreOrder (storeOrder fenceOrder : MemoryOrder) : MemoryOrder :=
  strengthen storeOrder fenceOrder

/-! ## CAS Failure Ordering -/

/-- The failure ordering for a CAS must not be stronger than the
    success ordering, and must not be release or acqRel.
    SeqCst is allowed as a failure ordering per C11 7.17.7.4.
    Returns true if the failure ordering is valid given the success ordering. -/
def validCASFailureOrder (success failure : MemoryOrder) : Bool :=
  failure.strength ≤ success.strength &&
  match failure with
  | .release => false
  | .acqRel  => false
  | _        => true

/-- Compute a valid failure ordering from a success ordering.
    Strips release semantics per C11 rules. -/
def defaultFailureOrder : MemoryOrder → MemoryOrder
  | .relaxed => .relaxed
  | .acquire => .acquire
  | .release => .relaxed
  | .acqRel  => .acquire
  | .seqCst  => .seqCst

end Radix.Concurrency.Ordering
