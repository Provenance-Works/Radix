/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Memory Pool Specification (Layer 3)

Abstract specification of memory pool allocators:

- **Bump Allocator**: Linear allocation with O(1) alloc, bulk-free only.
  Models arena-style allocation where all allocations are freed at once.

- **Slab Allocator**: Fixed-size block allocation with O(1) alloc/free.
  Models pool-of-pools for uniform-size objects.

## Safety Properties (proven in Lemmas)

- No double-free: freeing an already-freed block is detected/prevented
- No use-after-free: accessing freed memory is prevented by state tracking
- Capacity tracking: allocation fails predictably when pool is exhausted
- No overlapping allocations: each alloc returns a disjoint region

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.

## References

- v0.2.0 Roadmap: Memory Pool Model
- FR-004: Memory Safety
-/

namespace Radix.MemoryPool.Spec

/-! ================================================================ -/
/-! ## Allocation Handle                                              -/
/-! ================================================================ -/

/-- Unique identifier for an allocation within a pool.
    Monotonically increasing to prevent ABA problems. -/
structure AllocId where
  id : Nat
  deriving DecidableEq, Repr, Inhabited

/-- State of an individual allocation. -/
inductive AllocState where
  /-- Block is currently allocated and in use. -/
  | allocated
  /-- Block has been freed and is available for reuse. -/
  | freed
  deriving DecidableEq, Repr

/-- Metadata for a single allocation. -/
structure AllocInfo where
  /-- Unique allocation identifier. -/
  allocId : AllocId
  /-- Start offset within the pool's memory region. -/
  offset : Nat
  /-- Size of the allocation in bytes. -/
  size : Nat
  /-- Current state (allocated or freed). -/
  state : AllocState
  deriving Repr

/-! ================================================================ -/
/-! ## Bump Allocator Specification                                   -/
/-! ================================================================ -/

/-- Abstract state of a bump allocator.
    Allocations advance a cursor through a fixed-size backing region.
    All allocations are freed at once via `reset`. -/
structure BumpState where
  /-- Total capacity in bytes. -/
  capacity : Nat
  /-- Current allocation cursor (bytes used so far). -/
  cursor : Nat
  /-- Number of allocations made since last reset. -/
  allocCount : Nat
  /-- Next allocation ID to issue. -/
  nextId : Nat
  /-- Log of all allocation records (for verification). -/
  allocLog : List AllocInfo
  deriving Repr

namespace BumpState

/-- Create a fresh bump allocator with given capacity. -/
def new (capacity : Nat) : BumpState :=
  { capacity := capacity
    cursor := 0
    allocCount := 0
    nextId := 0
    allocLog := [] }

/-- Remaining free bytes. -/
def remaining (s : BumpState) : Nat := s.capacity - s.cursor

/-- Attempt to allocate `size` bytes. Returns the new state and allocation
    info on success, or `none` if insufficient capacity. -/
def alloc (s : BumpState) (size : Nat) : Option (BumpState × AllocInfo) :=
  if size == 0 then none  -- Zero-size allocations are not allowed
  else if s.cursor + size > s.capacity then none
  else
    let info : AllocInfo :=
      { allocId := ⟨s.nextId⟩
        offset := s.cursor
        size := size
        state := .allocated }
    some
      ({ s with
         cursor := s.cursor + size
         allocCount := s.allocCount + 1
         nextId := s.nextId + 1
         allocLog := s.allocLog ++ [info] },
       info)

/-- Reset the bump allocator: free ALL allocations at once.
    This is the only way to reclaim memory from a bump allocator. -/
def reset (s : BumpState) : BumpState :=
  { s with
    cursor := 0
    allocCount := 0
    allocLog := s.allocLog.map fun info =>
      { info with state := .freed } }

/-- Invariant: cursor never exceeds capacity. -/
def isValid (s : BumpState) : Prop := s.cursor ≤ s.capacity

end BumpState

/-! ================================================================ -/
/-! ## Slab Allocator Specification                                   -/
/-! ================================================================ -/

/-- Abstract state of a slab allocator.
    All blocks have the same fixed size. Free blocks are tracked in a free list. -/
structure SlabState where
  /-- Size of each block in bytes. -/
  blockSize : Nat
  /-- Total number of blocks in the slab. -/
  blockCount : Nat
  /-- Set of free block indices (available for allocation). -/
  freeBlocks : List Nat
  /-- Set of allocated block indices. -/
  allocatedBlocks : List Nat
  /-- Next allocation ID to issue. -/
  nextId : Nat
  /-- Log of all allocation records (for verification). -/
  allocLog : List AllocInfo
  deriving Repr

namespace SlabState

/-- Create a fresh slab allocator. All blocks start free. -/
def new (blockSize : Nat) (blockCount : Nat) : SlabState :=
  { blockSize := blockSize
    blockCount := blockCount
    freeBlocks := List.range blockCount
    allocatedBlocks := []
    nextId := 0
    allocLog := [] }

/-- Number of currently free blocks. -/
def freeCount (s : SlabState) : Nat := s.freeBlocks.length

/-- Number of currently allocated blocks. -/
def allocatedCount (s : SlabState) : Nat := s.allocatedBlocks.length

/-- Total capacity in blocks. -/
def totalBlocks (s : SlabState) : Nat := s.blockCount

/-- Attempt to allocate one block. Returns the new state and allocation
    info on success, or `none` if no free blocks remain. -/
def alloc (s : SlabState) : Option (SlabState × AllocInfo) :=
  match s.freeBlocks with
  | [] => none
  | blockIdx :: rest =>
    let info : AllocInfo :=
      { allocId := ⟨s.nextId⟩
        offset := blockIdx * s.blockSize
        size := s.blockSize
        state := .allocated }
    some
      ({ s with
         freeBlocks := rest
         allocatedBlocks := blockIdx :: s.allocatedBlocks
         nextId := s.nextId + 1
         allocLog := s.allocLog ++ [info] },
       info)

/-- Free a block by its index. Returns `none` if the block was not allocated
    (double-free prevention). -/
def free (s : SlabState) (blockIdx : Nat) : Option SlabState :=
  if s.allocatedBlocks.contains blockIdx then
    some
      { s with
        freeBlocks := blockIdx :: s.freeBlocks
        allocatedBlocks := s.allocatedBlocks.filter (· != blockIdx)
        allocLog := s.allocLog.map fun info =>
          if info.offset == blockIdx * s.blockSize ∧ info.state == .allocated then
            { info with state := .freed }
          else info }
  else none  -- Block was not allocated: double-free detected

/-- Invariant: no block appears in both free and allocated lists,
    and all indices are within bounds. -/
def isValid (s : SlabState) : Prop :=
  -- Disjointness: free and allocated lists have no common elements
  (∀ idx, idx ∈ s.freeBlocks → idx ∉ s.allocatedBlocks) ∧
  -- All free blocks are in range
  (∀ idx, idx ∈ s.freeBlocks → idx < s.blockCount) ∧
  -- All allocated blocks are in range
  (∀ idx, idx ∈ s.allocatedBlocks → idx < s.blockCount) ∧
  -- Conservation: free + allocated = total
  (s.freeBlocks.length + s.allocatedBlocks.length = s.blockCount)

end SlabState

/-! ================================================================ -/
/-! ## Specification Properties                                       -/
/-! ================================================================ -/

/-! ### Bump Allocator Properties -/

/-- Fresh bump allocator is valid. -/
theorem bump_new_isValid (cap : Nat) : (BumpState.new cap).isValid := by
  simp [BumpState.new, BumpState.isValid]

/-- Fresh bump allocator has full capacity. -/
theorem bump_new_remaining (cap : Nat) :
    (BumpState.new cap).remaining = cap := by
  simp [BumpState.new, BumpState.remaining]

/-- Allocation preserves validity. -/
theorem bump_alloc_preserves_valid (s : BumpState) (size : Nat) (s' : BumpState)
    (info : AllocInfo)
    (hAlloc : s.alloc size = some (s', info))
    (_hValid : s.isValid) :
    s'.isValid := by
  unfold BumpState.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · contradiction
    · rename_i hSize hCap; simp at hCap
      injection hAlloc with hAlloc
      have := congrArg Prod.fst hAlloc; simp at this; subst this
      simp [BumpState.isValid] at *; omega

/-- Allocation decreases remaining capacity. -/
theorem bump_alloc_decreases_remaining (s : BumpState) (size : Nat) (s' : BumpState)
    (info : AllocInfo) (hAlloc : s.alloc size = some (s', info)) :
    s'.remaining = s.remaining - size := by
  unfold BumpState.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · contradiction
    · injection hAlloc with hAlloc
      have := congrArg Prod.fst hAlloc; simp at this; subst this
      simp [BumpState.remaining]; omega

/-- Reset restores full capacity. -/
theorem bump_reset_remaining (s : BumpState) :
    (s.reset).remaining = s.capacity := by
  simp [BumpState.reset, BumpState.remaining]

/-- Reset produces a valid state. -/
theorem bump_reset_isValid (s : BumpState) :
    (s.reset).isValid := by
  simp [BumpState.reset, BumpState.isValid]

/-- Allocation returns a non-overlapping region with the cursor. -/
theorem bump_alloc_offset_eq_cursor (s : BumpState) (size : Nat) (s' : BumpState)
    (info : AllocInfo) (hAlloc : s.alloc size = some (s', info)) :
    info.offset = s.cursor := by
  unfold BumpState.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · contradiction
    · injection hAlloc with hAlloc
      have := congrArg Prod.snd hAlloc; simp at this; rw [← this]

/-- Allocation returns an `allocated` state. -/
theorem bump_alloc_state (s : BumpState) (size : Nat) (s' : BumpState)
    (info : AllocInfo) (hAlloc : s.alloc size = some (s', info)) :
    info.state = .allocated := by
  unfold BumpState.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · contradiction
    · injection hAlloc with hAlloc
      have := congrArg Prod.snd hAlloc; simp at this; rw [← this]

/-- Zero-size allocation always fails. -/
theorem bump_alloc_zero_fails (s : BumpState) :
    s.alloc 0 = none := by
  unfold BumpState.alloc; simp

/-! ### Slab Allocator Properties -/

/-- Fresh slab allocator is valid. -/
theorem slab_new_isValid (bs bc : Nat) : (SlabState.new bs bc).isValid := by
  unfold SlabState.new SlabState.isValid
  simp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro idx hMem hContra
    simp at hContra
  · intro idx hMem
    simp [List.mem_range] at hMem
    exact hMem
  · intro idx hMem; simp at hMem
  · simp [List.length_range]

/-- Fresh slab has all blocks free. -/
theorem slab_new_freeCount (bs bc : Nat) :
    (SlabState.new bs bc).freeCount = bc := by
  simp [SlabState.new, SlabState.freeCount, List.length_range]

/-- Allocation from empty slab fails. -/
theorem slab_alloc_empty_fails (s : SlabState) (h : s.freeBlocks = []) :
    s.alloc = none := by
  simp [SlabState.alloc, h]

/-- Double-free is detected and returns none. -/
theorem slab_double_free_fails (s : SlabState) (idx : Nat)
    (h : idx ∉ s.allocatedBlocks) :
    s.free idx = none := by
  simp [SlabState.free, h]

end Radix.MemoryPool.Spec
