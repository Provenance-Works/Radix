/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Concurrency.Spec
import Radix.Concurrency.Ordering

/-!
# Atomic Operations Model (Layer 2)

This module defines the abstract operational semantics for atomic
memory operations:

- `AtomicCell`: Abstract model of an atomic memory location
- Load, Store, CAS operations with state transitions
- Fetch-and-modify operations (fetchAdd, fetchSub, fetchAnd, fetchOr, fetchXor)
- Operation results with success/failure indication

## Architecture

This is a **Layer 2 (Implementation)** module.
- Models atomic operations as pure state transitions.
- No actual hardware interaction (pure Lean 4).

## References

- FR-008.1: Memory Ordering (atomic load/store/CAS)
- C11 Standard, Section 7.17.7 (Atomic operations)
-/

set_option autoImplicit false

namespace Radix.Concurrency.Atomic

open Radix.Concurrency.Spec
open Radix.Concurrency.Ordering

/-! ## Atomic Cell -/

/-- An abstract atomic memory cell holding a natural number value.
    In a real implementation, this would be backed by hardware atomics.
    Here we model it as a pure value with ordering annotations. -/
structure AtomicCell where
  /-- The current stored value. -/
  val : Nat
  deriving DecidableEq, Repr

/-- Create an atomic cell with an initial value. -/
def AtomicCell.new (v : Nat) : AtomicCell :=
  { val := v }

/-! ## Operation Results -/

/-- Result of an atomic load operation. -/
structure LoadResult where
  /-- The value read from the cell. -/
  value : Nat
  deriving Repr

/-- Result of an atomic store operation.
    The store always succeeds in a valid model. -/
structure StoreResult where
  deriving Repr

/-- Result of a compare-and-swap operation. -/
structure CASResult where
  /-- Whether the CAS succeeded (expected value matched). -/
  success  : Bool
  /-- The value that was in the cell before the operation.
      On success, this equals the expected value.
      On failure, this is the current (unexpected) value. -/
  previous : Nat
  deriving Repr

/-- Result of a fetch-and-modify operation (fetchAdd, fetchSub, etc.). -/
structure FetchResult where
  /-- The value that was in the cell before the modification. -/
  previous : Nat
  deriving Repr

/-! ## Atomic Load -/

/-- Atomic load: read the current value of a cell.

    Precondition: ordering must be valid for loads
    (relaxed, acquire, or seqCst). -/
def atomicLoad (cell : AtomicCell) (_order : MemoryOrder)
    (_hValid : validLoadOrder _order = true := by decide) :
    LoadResult × AtomicCell :=
  ({ value := cell.val }, cell)

/-! ## Atomic Store -/

/-- Atomic store: write a new value to a cell.

    Precondition: ordering must be valid for stores
    (relaxed, release, or seqCst). -/
def atomicStore (_cell : AtomicCell) (newVal : Nat) (_order : MemoryOrder)
    (_hValid : validStoreOrder _order = true := by decide) :
    StoreResult × AtomicCell :=
  ({}, { val := newVal })

/-! ## Compare-and-Swap (CAS) -/

/-- Atomic compare-and-swap: if the cell's current value equals
    `expected`, replace it with `desired` and report success.
    Otherwise, report failure with the current value.

    Uses `successOrder` on success and `failureOrder` on failure.
    The failure ordering must be valid per C11 rules. -/
def atomicCAS (cell : AtomicCell) (expected desired : Nat)
    (_successOrder : MemoryOrder)
    (_failureOrder : MemoryOrder := defaultFailureOrder _successOrder) :
    CASResult × AtomicCell :=
  if cell.val == expected then
    ({ success := true, previous := cell.val },
     { val := desired })
  else
    ({ success := false, previous := cell.val },
     cell)

/-- Strong CAS: guaranteed to succeed if value matches.
    (Weak CAS may spuriously fail; we model strong CAS here.) -/
abbrev atomicCompareExchangeStrong := @atomicCAS

/-! ## Fetch-and-Modify Operations -/

/-- Atomic fetch-and-add: atomically adds `delta` to the cell value
    and returns the previous value. -/
def fetchAdd (cell : AtomicCell) (delta : Nat) (_order : MemoryOrder) :
    FetchResult × AtomicCell :=
  ({ previous := cell.val },
   { val := cell.val + delta })

/-- Atomic fetch-and-sub: atomically subtracts `delta` from the cell
    value and returns the previous value. -/
def fetchSub (cell : AtomicCell) (delta : Nat) (_order : MemoryOrder) :
    FetchResult × AtomicCell :=
  ({ previous := cell.val },
   { val := cell.val - delta })

/-- Atomic fetch-and-and: atomically performs bitwise AND with `mask`
    on the cell value and returns the previous value. -/
def fetchAnd (cell : AtomicCell) (mask : Nat) (_order : MemoryOrder) :
    FetchResult × AtomicCell :=
  ({ previous := cell.val },
   { val := cell.val &&& mask })

/-- Atomic fetch-and-or: atomically performs bitwise OR with `bits`
    on the cell value and returns the previous value. -/
def fetchOr (cell : AtomicCell) (bits : Nat) (_order : MemoryOrder) :
    FetchResult × AtomicCell :=
  ({ previous := cell.val },
   { val := cell.val ||| bits })

/-- Atomic fetch-and-xor: atomically performs bitwise XOR with `bits`
    on the cell value and returns the previous value. -/
def fetchXor (cell : AtomicCell) (bits : Nat) (_order : MemoryOrder) :
    FetchResult × AtomicCell :=
  ({ previous := cell.val },
   { val := cell.val ^^^ bits })

/-! ## Atomic Exchange -/

/-- Atomic exchange: atomically replaces the cell value with `newVal`
    and returns the previous value. Equivalent to a CAS loop that
    always succeeds. -/
def atomicExchange (cell : AtomicCell) (newVal : Nat) (_order : MemoryOrder) :
    FetchResult × AtomicCell :=
  ({ previous := cell.val },
   { val := newVal })

/-! ## Event Generation -/

/-- Generate a load event for a trace. -/
def mkLoadEvent (tid : ThreadId) (seqNo : Nat)
    (loc : LocationId) (result : LoadResult) (order : MemoryOrder) :
    MemoryEvent :=
  { id       := { thread := tid, seqNo := seqNo }
    kind     := .load
    location := some loc
    readVal  := result.value
    writeVal := 0
    order    := order }

/-- Generate a store event for a trace. -/
def mkStoreEvent (tid : ThreadId) (seqNo : Nat)
    (loc : LocationId) (value : Nat) (order : MemoryOrder) :
    MemoryEvent :=
  { id       := { thread := tid, seqNo := seqNo }
    kind     := .store
    location := some loc
    readVal  := 0
    writeVal := value
    order    := order }

/-- Generate a CAS event for a trace (as an RMW). -/
def mkCASEvent (tid : ThreadId) (seqNo : Nat)
    (loc : LocationId) (result : CASResult) (newVal : Nat)
    (order : MemoryOrder) :
    MemoryEvent :=
  { id       := { thread := tid, seqNo := seqNo }
    kind     := .rmw
    location := some loc
    readVal  := result.previous
    writeVal := if result.success then newVal else result.previous
    order    := order }

/-- Generate a fence event for a trace. -/
def mkFenceEvent (tid : ThreadId) (seqNo : Nat)
    (order : MemoryOrder) :
    MemoryEvent :=
  { id       := { thread := tid, seqNo := seqNo }
    kind     := .fence
    location := none
    readVal  := 0
    writeVal := 0
    order    := order }

end Radix.Concurrency.Atomic
