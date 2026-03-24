/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.MemoryPool.Spec
import Radix.MemoryPool.Model

/-!
# Memory Pool Proofs (Layer 3)

Correctness proofs for memory pool implementations:

- **No double-free**: freeing an already-freed block returns `none`
- **No use-after-free**: freed blocks tracked by state
- **Capacity tracking**: remaining capacity is always correct
- **Allocation safety**: offsets are always within bounds

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- Bridges Layer 2 (`MemoryPool.Model`) to Layer 3 (`MemoryPool.Spec`).

## References

- v0.2.0 Roadmap: Memory Pool Model — no double-free, no use-after-free, capacity tracking
-/

namespace Radix.MemoryPool.Lemmas

open Radix.MemoryPool

/-! ================================================================ -/
/-! ## Bump Pool Properties                                           -/
/-! ================================================================ -/

/-- Fresh bump pool has full capacity. -/
theorem bump_new_remaining (cap : Nat) :
    (BumpPool.new cap).remaining = cap := by
  simp [BumpPool.new, BumpPool.remaining]

/-- Fresh bump pool cursor is at 0. -/
theorem bump_new_cursor (cap : Nat) :
    (BumpPool.new cap).cursor = 0 := by
  rfl

/-- Allocation returns an offset equal to the current cursor. -/
theorem bump_alloc_offset (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    off = pool.cursor := by
  unfold BumpPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · simp at hAlloc; exact hAlloc.1.symm
    · contradiction

/-- Allocation advances the cursor by exactly `size`. -/
theorem bump_alloc_cursor (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    pool'.cursor = pool.cursor + size := by
  unfold BumpPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · simp at hAlloc; obtain ⟨_, h⟩ := hAlloc; subst h; rfl
    · contradiction

/-- Allocation preserves capacity. -/
theorem bump_alloc_capacity (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    pool'.capacity = pool.capacity := by
  unfold BumpPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · simp at hAlloc; obtain ⟨_, h⟩ := hAlloc; subst h; rfl
    · contradiction

/-- Allocation decreases remaining capacity. -/
theorem bump_alloc_remaining (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    pool'.remaining = pool.remaining - size := by
  have hCur := bump_alloc_cursor pool size off pool' hAlloc
  have hCap := bump_alloc_capacity pool size off pool' hAlloc
  simp [BumpPool.remaining, hCur, hCap]
  omega

/-- Allocation returns an in-bounds offset. -/
theorem bump_alloc_offset_in_bounds (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    off + size ≤ pool.capacity := by
  have hOff := bump_alloc_offset pool size off pool' hAlloc
  unfold BumpPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · rename_i hSize hCap
      subst hOff
      exact hCap
    · contradiction

/-- Zero-size allocation always fails. -/
theorem bump_alloc_zero_fails (pool : BumpPool) :
    pool.alloc 0 = none := by
  simp [BumpPool.alloc]

/-- Reset restores full remaining capacity. -/
theorem bump_reset_remaining (pool : BumpPool) :
    pool.reset.remaining = pool.capacity := by
  simp [BumpPool.reset, BumpPool.remaining]

/-- Reset sets cursor to 0. -/
theorem bump_reset_cursor (pool : BumpPool) :
    pool.reset.cursor = 0 := by
  rfl

/-- Reset preserves capacity. -/
theorem bump_reset_capacity (pool : BumpPool) :
    pool.reset.capacity = pool.capacity := by
  rfl

/-- After reset, pool can allocate up to full capacity. -/
theorem bump_reset_canAlloc (pool : BumpPool) (size : Nat)
    (_hSize : size > 0) (hFit : size ≤ pool.capacity) :
    pool.reset.canAlloc size = true := by
  simp [BumpPool.reset, BumpPool.canAlloc]
  omega

/-! ================================================================ -/
/-! ## Slab Pool Properties                                           -/
/-! ================================================================ -/

/-- Fresh slab pool has all blocks free. -/
theorem slab_new_freeCount (bs bc : Nat) (h : bs > 0) :
    (SlabPool.new bs bc h).freeCount = bc := by
  simp [SlabPool.new, SlabPool.freeCount, List.length_reverse, List.length_range]

/-- Fresh slab pool has no allocated blocks. -/
theorem slab_new_allocatedCount (bs bc : Nat) (h : bs > 0) :
    (SlabPool.new bs bc h).allocatedCount = 0 := by
  rfl

/-- Double-free detection: freeing an unallocated block returns none. -/
theorem slab_free_unallocated (pool : SlabPool) (idx : Nat)
    (h : ¬ pool.allocated.contains idx) :
    pool.free idx = none := by
  unfold SlabPool.free
  split
  · next h' => exact absurd h' h
  · rfl

/-- Allocation from empty pool fails. -/
theorem slab_alloc_empty (pool : SlabPool) (h : pool.freeList = []) :
    pool.alloc = none := by
  simp [SlabPool.alloc, h]

/-- Allocation returns a valid block offset. -/
theorem slab_alloc_offset (pool : SlabPool) (blockIdx off : Nat) (pool' : SlabPool)
    (hAlloc : pool.alloc = some (blockIdx, off, pool')) :
    off = blockIdx * pool.blockSize := by
  unfold SlabPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · next head rest =>
    simp at hAlloc
    obtain ⟨h1, h2, _⟩ := hAlloc
    subst h1; exact h2.symm

/-- Allocation preserves block size. -/
theorem slab_alloc_blockSize (pool : SlabPool) (blockIdx off : Nat) (pool' : SlabPool)
    (hAlloc : pool.alloc = some (blockIdx, off, pool')) :
    pool'.blockSize = pool.blockSize := by
  unfold SlabPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · next head rest =>
    simp at hAlloc
    obtain ⟨_, _, h3⟩ := hAlloc
    subst h3; rfl

/-- Allocation preserves block count. -/
theorem slab_alloc_blockCount (pool : SlabPool) (blockIdx off : Nat) (pool' : SlabPool)
    (hAlloc : pool.alloc = some (blockIdx, off, pool')) :
    pool'.blockCount = pool.blockCount := by
  unfold SlabPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · next head rest =>
    simp at hAlloc
    obtain ⟨_, _, h3⟩ := hAlloc
    subst h3; rfl

/-! ## Spec-Level Properties

The abstract specification has complete safety proofs. -/

/-- (Spec) Fresh bump allocator is valid. -/
theorem spec_bump_new_isValid (cap : Nat) :
    (Spec.BumpState.new cap).isValid :=
  Spec.bump_new_isValid cap

/-- (Spec) Fresh slab allocator is valid. -/
theorem spec_slab_new_isValid (bs bc : Nat) :
    (Spec.SlabState.new bs bc).isValid :=
  Spec.slab_new_isValid bs bc

/-- (Spec) Zero-size bump allocation always fails. -/
theorem spec_bump_alloc_zero (s : Spec.BumpState) :
    s.alloc 0 = none :=
  Spec.bump_alloc_zero_fails s

/-- (Spec) Double-free detection in slab allocator. -/
theorem spec_slab_double_free (s : Spec.SlabState) (idx : Nat)
    (h : idx ∉ s.allocatedBlocks) :
    s.free idx = none :=
  Spec.slab_double_free_fails s idx h

/-! ================================================================ -/
/-! ## Additional Bump Pool Properties                                -/
/-! ================================================================ -/

/-- Bump allocation preserves the buffer. -/
theorem bump_alloc_buf (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    pool'.buf = pool.buf := by
  unfold BumpPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · simp at hAlloc; obtain ⟨_, h⟩ := hAlloc; subst h; rfl
    · contradiction

/-- Allocated offset is strictly less than capacity. -/
theorem bump_alloc_offset_lt_capacity (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    off < pool.capacity := by
  have hOff := bump_alloc_offset pool size off pool' hAlloc
  have hBound := bump_alloc_offset_in_bounds pool size off pool' hAlloc
  unfold BumpPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · rename_i hSize _
      subst hOff
      simp [beq_iff_eq] at hSize
      omega
    · contradiction

/-- Consecutive allocations return non-overlapping regions. -/
theorem bump_alloc_nonoverlapping (pool : BumpPool) (s1 s2 : Nat)
    (off1 : Nat) (pool1 : BumpPool)
    (off2 : Nat) (pool2 : BumpPool)
    (hAlloc1 : pool.alloc s1 = some (off1, pool1))
    (hAlloc2 : pool1.alloc s2 = some (off2, pool2)) :
    off1 + s1 ≤ off2 := by
  have h1 := bump_alloc_offset pool s1 off1 pool1 hAlloc1
  have h2 := bump_alloc_cursor pool s1 off1 pool1 hAlloc1
  have h3 := bump_alloc_offset pool1 s2 off2 pool2 hAlloc2
  subst h1; subst h3; omega

/-- Allocation returns cursor strictly within capacity. -/
theorem bump_alloc_cursor_le (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (_hAlloc : pool.alloc size = some (off, pool')) :
    pool'.cursor ≤ pool'.capacity := pool'.hCursor

/-- After reset, canAlloc returns true for any fitting size. -/
theorem bump_reset_alloc_succeeds (pool : BumpPool) (size : Nat)
    (hSize : size > 0) (hFit : size ≤ pool.capacity) :
    (pool.reset.alloc size).isSome := by
  have hNonzero : ¬ size == 0 := by
    simp [beq_iff_eq]
    omega
  simp [BumpPool.reset, BumpPool.alloc, hNonzero, hFit]

/-! ================================================================ -/
/-! ## Additional Slab Pool Properties                                -/
/-! ================================================================ -/

/-- Slab allocation decreases free count by one. -/
theorem slab_alloc_freeCount (pool : SlabPool) (blockIdx off : Nat) (pool' : SlabPool)
    (hAlloc : pool.alloc = some (blockIdx, off, pool')) :
    pool'.freeCount = pool.freeCount - 1 := by
  unfold SlabPool.alloc at hAlloc
  match hfl : pool.freeList with
  | [] => simp [hfl] at hAlloc
  | blockIdx' :: rest =>
    simp [hfl] at hAlloc
    obtain ⟨rfl, rfl, rfl⟩ := hAlloc
    simp [SlabPool.freeCount, hfl]

/-- Slab allocation increases allocated count by one. -/
theorem slab_alloc_allocatedCount (pool : SlabPool) (blockIdx off : Nat) (pool' : SlabPool)
    (hAlloc : pool.alloc = some (blockIdx, off, pool')) :
    pool'.allocatedCount = pool.allocatedCount + 1 := by
  unfold SlabPool.alloc at hAlloc
  split at hAlloc
  · contradiction
  · next head rest =>
    simp at hAlloc
    obtain ⟨_, _, h3⟩ := hAlloc
    subst h3
    simp [SlabPool.allocatedCount]

/-- Slab free preserves block size. -/
theorem slab_free_blockSize (pool : SlabPool) (idx : Nat) (pool' : SlabPool)
    (hFree : pool.free idx = some pool') :
    pool'.blockSize = pool.blockSize := by
  unfold SlabPool.free at hFree
  split at hFree
  · simp at hFree; subst hFree; rfl
  · contradiction

/-- Slab free preserves block count. -/
theorem slab_free_blockCount (pool : SlabPool) (idx : Nat) (pool' : SlabPool)
    (hFree : pool.free idx = some pool') :
    pool'.blockCount = pool.blockCount := by
  unfold SlabPool.free at hFree
  split at hFree
  · simp at hFree; subst hFree; rfl
  · contradiction

/-- Fresh slab pool can allocate if blockCount > 0. -/
theorem slab_new_canAlloc (bs bc : Nat) (hBS : bs > 0) (hBC : bc > 0) :
    (SlabPool.new bs bc hBS).canAlloc = true := by
  cases bc with
  | zero => omega
  | succ n => simp [SlabPool.new, SlabPool.canAlloc]

/-- (Spec) Bump reset produces a valid state. -/
theorem spec_bump_reset_valid (s : Spec.BumpState) :
    s.reset.isValid :=
  Spec.bump_reset_valid s

/-- (Spec) Bump alloc returns allocated state. -/
theorem spec_bump_alloc_info_state (s : Spec.BumpState) (size : Nat)
    (s' : Spec.BumpState) (info : Spec.AllocInfo)
    (hAlloc : s.alloc size = some (s', info)) :
    info.state = .allocated :=
  Spec.bump_alloc_info_state s size s' info hAlloc

/-- (Spec) Bump alloc offset is in bounds. -/
theorem spec_bump_alloc_offset_lt (s : Spec.BumpState) (size : Nat)
    (s' : Spec.BumpState) (info : Spec.AllocInfo)
    (hAlloc : s.alloc size = some (s', info)) :
    info.offset < s.capacity :=
  Spec.bump_alloc_offset_lt s size s' info hAlloc

/-! ================================================================ -/
/-! ## Slab Conservation Properties                                   -/
/-! ================================================================ -/

/-- (Spec) Slab alloc preserves blockCount. -/
theorem spec_slab_alloc_blockCount (s s' : Spec.SlabState) (info : Spec.AllocInfo)
    (hAlloc : s.alloc = some (s', info)) :
    s'.blockCount = s.blockCount :=
  Spec.slab_alloc_blockCount s s' info hAlloc

/-- (Spec) Slab alloc decrements freeCount. -/
theorem spec_slab_alloc_decrements_freeCount (s s' : Spec.SlabState) (info : Spec.AllocInfo)
    (hAlloc : s.alloc = some (s', info)) :
    s'.freeCount + 1 = s.freeCount :=
  Spec.slab_alloc_decrements_freeCount s s' info hAlloc

/-- (Spec) Slab free preserves blockSize. -/
theorem spec_slab_free_blockSize (s : Spec.SlabState) (idx : Nat)
    (s' : Spec.SlabState) (hFree : s.free idx = some s') :
    s'.blockSize = s.blockSize :=
  Spec.slab_free_blockSize s idx s' hFree

/-- (Spec) Slab alloc+free conservation: freeCount + allocatedBlocks.length. -/
theorem spec_slab_alloc_conservation (s s' : Spec.SlabState) (info : Spec.AllocInfo)
    (hAlloc : s.alloc = some (s', info)) :
    s'.freeCount + s'.allocatedBlocks.length =
    s.freeCount + s.allocatedBlocks.length :=
  Spec.slab_alloc_conservation s s' info hAlloc

/-! ================================================================ -/
/-! ## Concrete Test Vectors                                          -/
/-! ================================================================ -/

private def testPool : BumpPool := BumpPool.new 256

/-- Fresh bump pool of 256 bytes has 256 remaining. -/
example : testPool.remaining = 256 := by native_decide

/-- Fresh bump pool has cursor at 0. -/
example : testPool.cursor = 0 := by native_decide

/-- Allocating 64 bytes from testPool succeeds. -/
example : (testPool.alloc 64).isSome = true := by native_decide

/-- Allocating 0 bytes fails. -/
example : (testPool.alloc 0).isNone = true := by native_decide

/-- Reset pool has full remaining. -/
example : testPool.reset.remaining = 256 := by native_decide

private def testSlabPool : SlabPool := SlabPool.new 32 4 (by omega)

/-- Fresh slab pool has 4 free blocks. -/
example : testSlabPool.freeCount = 4 := by native_decide

/-- Fresh slab pool has 0 allocated. -/
example : testSlabPool.allocatedCount = 0 := by native_decide

/-- Fresh slab pool can allocate. -/
example : testSlabPool.canAlloc = true := by native_decide

/-- Slab pool allocation succeeds. -/
example : testSlabPool.alloc.isSome = true := by native_decide

end Radix.MemoryPool.Lemmas
