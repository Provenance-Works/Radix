/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Concurrency Specification (Layer 3)

This module defines the formal model for concurrent atomic operations
and memory ordering, following the C11/C++11 memory model:

- Memory ordering levels (Relaxed through SeqCst)
- Abstract thread and event model
- Happens-before partial order
- Linearizability definition
- Data-race-freedom definition

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.
- Defines the formal contracts for Concurrency.Atomic to satisfy.

## References

- FR-008: Atomicity and Memory Ordering
- FR-008.1: Memory Ordering
- FR-008.2: Proofs (linearizability, data-race freedom)
- C11 Standard, Section 7.17.3 (Memory order)
- C++11 Standard, Section 29.3 (Order and consistency)
-/

set_option autoImplicit false

namespace Radix.Concurrency.Spec

/-! ## Memory Ordering -/

/-- Memory ordering levels following C11/C++11 semantics.

    Ordered from weakest to strongest:
    - `relaxed`:  No inter-thread ordering guarantees
    - `acquire`:  Subsequent reads/writes cannot move before this load
    - `release`:  Previous reads/writes cannot move after this store
    - `acqRel`:   Both acquire and release semantics (for RMW)
    - `seqCst`:   Total global ordering across all threads -/
inductive MemoryOrder where
  | relaxed
  | acquire
  | release
  | acqRel
  | seqCst
  deriving DecidableEq, Repr

/-- Numeric strength of a memory ordering (0 = weakest, 4 = strongest). -/
def MemoryOrder.strength : MemoryOrder → Nat
  | .relaxed => 0
  | .acquire => 1
  | .release => 1
  | .acqRel  => 2
  | .seqCst  => 3

/-- Whether ordering `a` is at least as strong as ordering `b`. -/
def MemoryOrder.isAtLeast (a b : MemoryOrder) : Bool :=
  a.strength ≥ b.strength

/-! ## Thread and Location Identifiers -/

/-- A thread identifier. -/
structure ThreadId where
  val : Nat
  deriving DecidableEq, Repr

/-- A memory location identifier. -/
structure LocationId where
  val : Nat
  deriving DecidableEq, Repr

/-! ## Atomic Operation Types -/

/-- The kind of an atomic memory access. -/
inductive AccessKind where
  /-- Atomic read. -/
  | load
  /-- Atomic write. -/
  | store
  /-- Atomic read-modify-write (CAS, fetch_add, etc.). -/
  | rmw
  /-- Memory fence (no location). -/
  | fence
  deriving DecidableEq, Repr

/-- Whether an access kind performs a read. -/
def AccessKind.isRead : AccessKind → Bool
  | .load  => true
  | .store => false
  | .rmw   => true
  | .fence => false

/-- Whether an access kind performs a write. -/
def AccessKind.isWrite : AccessKind → Bool
  | .load  => false
  | .store => true
  | .rmw   => true
  | .fence => false

/-! ## Memory Events -/

/-- A unique identifier for an event in an execution trace. -/
structure EventId where
  thread : ThreadId
  seqNo  : Nat
  deriving DecidableEq, Repr

/-- A single memory event in an execution trace. -/
structure MemoryEvent where
  /-- Unique event identifier. -/
  id       : EventId
  /-- Access kind (load, store, RMW, fence). -/
  kind     : AccessKind
  /-- Target memory location (none for fences). -/
  location : Option LocationId
  /-- Value read (for load/RMW). -/
  readVal  : Nat
  /-- Value written (for store/RMW). -/
  writeVal : Nat
  /-- Memory ordering used. -/
  order    : MemoryOrder
  deriving Repr

/-! ## Execution Trace -/

/-- An execution trace is a sequence of memory events. -/
structure Trace where
  events : List MemoryEvent
  deriving Repr

/-- Events in a trace belonging to a specific thread. -/
def Trace.threadEvents (t : Trace) (tid : ThreadId) : List MemoryEvent :=
  t.events.filter (fun e => e.id.thread == tid)

/-- Events in a trace accessing a specific location. -/
def Trace.locationEvents (t : Trace) (loc : LocationId) : List MemoryEvent :=
  t.events.filter (fun e => e.location == some loc)

/-! ## Ordering Validity -/

/-- A memory ordering is valid for a load operation.
    Stores and fences are not permitted with acquire-only orderings
    on store operations, etc. -/
def validLoadOrder : MemoryOrder → Bool
  | .relaxed => true
  | .acquire => true
  | .release => false
  | .acqRel  => false
  | .seqCst  => true

/-- A memory ordering is valid for a store operation. -/
def validStoreOrder : MemoryOrder → Bool
  | .relaxed => true
  | .acquire => false
  | .release => true
  | .acqRel  => false
  | .seqCst  => true

/-- A memory ordering is valid for a read-modify-write operation. -/
def validRMWOrder : MemoryOrder → Bool
  | .relaxed => true
  | .acquire => true
  | .release => true
  | .acqRel  => true
  | .seqCst  => true

/-- Whether a memory ordering is valid for a given access kind. -/
def validOrderForAccess (kind : AccessKind) (order : MemoryOrder) : Bool :=
  match kind with
  | .load  => validLoadOrder order
  | .store => validStoreOrder order
  | .rmw   => validRMWOrder order
  | .fence => true

/-! ## Happens-Before Relation -/

/-- Program order: event `a` happens before event `b` in the same thread
    if `a` has a smaller sequence number. -/
def programOrder (a b : MemoryEvent) : Prop :=
  a.id.thread = b.id.thread ∧ a.id.seqNo < b.id.seqNo

instance (a b : MemoryEvent) : Decidable (programOrder a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Synchronizes-with: a release store to location `l` synchronizes with
    an acquire load from `l` that reads the stored value. -/
def synchronizesWith (a b : MemoryEvent) : Prop :=
  a.kind.isWrite ∧ b.kind.isRead
  ∧ a.location = b.location ∧ a.location.isSome
  ∧ a.writeVal = b.readVal
  ∧ (a.order = .release ∨ a.order = .acqRel ∨ a.order = .seqCst)
  ∧ (b.order = .acquire ∨ b.order = .acqRel ∨ b.order = .seqCst)

/-- Happens-before: the transitive closure of program-order and
    synchronizes-with. For this specification, we define single-step
    happens-before (the relation itself); the transitive closure is
    formed in proofs as needed. -/
def happensBefore (a b : MemoryEvent) : Prop :=
  programOrder a b ∨ synchronizesWith a b

/-! ## Data Race Definition -/

/-- Two events conflict if they access the same location and at least
    one is a write. -/
def conflicting (a b : MemoryEvent) : Prop :=
  a.id ≠ b.id
  ∧ a.location = b.location ∧ a.location.isSome
  ∧ (a.kind.isWrite ∨ b.kind.isWrite)

/-- A data race exists between two conflicting events that are not
    ordered by happens-before. -/
def isDataRace (a b : MemoryEvent) : Prop :=
  conflicting a b
  ∧ a.id.thread ≠ b.id.thread
  ∧ ¬happensBefore a b
  ∧ ¬happensBefore b a

/-- An execution trace is data-race-free if no pair of events
    constitutes a data race. -/
def Trace.isDataRaceFree (t : Trace) : Prop :=
  ∀ (a b : MemoryEvent), a ∈ t.events → b ∈ t.events → ¬isDataRace a b

/-! ## Linearizability -/

/-- Position of an event in a list by EventId (returns list length if not found). -/
def eventPosition (xs : List MemoryEvent) (e : MemoryEvent) : Nat :=
  go xs 0
where
  go : List MemoryEvent → Nat → Nat
  | [], n => n
  | x :: rest, n => if x.id == e.id then n else go rest (n + 1)

/-- A sequential history is a list of events where each event from
    thread T_i appears in program order. -/
def isSequentialHistory (events : List MemoryEvent) : Prop :=
  ∀ (a b : MemoryEvent), a ∈ events → b ∈ events →
    a.id.thread = b.id.thread → a.id.seqNo < b.id.seqNo →
    eventPosition events a < eventPosition events b

/-- A sequential history is valid if each read sees the most recent
    write to the same location. -/
def isValidSequentialHistory (events : List MemoryEvent) : Prop :=
  ∀ (r : MemoryEvent), r ∈ events → r.kind.isRead →
    ∀ (loc : LocationId), r.location = some loc →
    ∃ (w : MemoryEvent), w ∈ events ∧ w.kind.isWrite
      ∧ w.location = some loc
      ∧ w.writeVal = r.readVal
      ∧ eventPosition events w < eventPosition events r

/-- An execution trace is linearizable if there exists a valid
    sequential history that is a permutation of the trace events
    and preserves happens-before ordering. -/
def Trace.isLinearizable (t : Trace) : Prop :=
  ∃ (seq : List MemoryEvent),
    seq.length = t.events.length
    ∧ (∀ e, e ∈ seq ↔ e ∈ t.events)
    ∧ isSequentialHistory seq
    ∧ isValidSequentialHistory seq
    ∧ (∀ a b, a ∈ t.events → b ∈ t.events →
        happensBefore a b → eventPosition seq a < eventPosition seq b)

/-! ## Well-Formed Trace -/

/-- A trace is well-formed if all events use valid orderings for
    their access kinds. -/
def Trace.isWellFormed (t : Trace) : Prop :=
  ∀ (e : MemoryEvent), e ∈ t.events → validOrderForAccess e.kind e.order

/-- A trace has unique event identifiers. -/
def Trace.hasUniqueIds (t : Trace) : Prop :=
  ∀ (a b : MemoryEvent), a ∈ t.events → b ∈ t.events → a.id = b.id → a = b

/-- A fully valid trace is well-formed with unique IDs. -/
def Trace.isValid (t : Trace) : Prop :=
  t.isWellFormed ∧ t.hasUniqueIds

end Radix.Concurrency.Spec
