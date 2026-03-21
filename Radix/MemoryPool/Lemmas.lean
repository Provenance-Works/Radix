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
  simp [BumpPool.alloc] at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · simp at hAlloc; exact hAlloc.1
    · contradiction

/-- Allocation advances the cursor by exactly `size`. -/
theorem bump_alloc_cursor (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    pool'.cursor = pool.cursor + size := by
  simp [BumpPool.alloc] at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · simp at hAlloc; exact hAlloc.2.1
    · contradiction

/-- Allocation preserves capacity. -/
theorem bump_alloc_capacity (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    pool'.capacity = pool.capacity := by
  simp [BumpPool.alloc] at hAlloc
  split at hAlloc
  · contradiction
  · split at hAlloc
    · simp at hAlloc; exact hAlloc.2.2
    · contradiction

/-- Allocation decreases remaining capacity. -/
theorem bump_alloc_remaining (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    pool'.remaining = pool.remaining - size := by
  have hCur := bump_alloc_cursor pool size off pool' hAlloc
  have hCap := bump_alloc_capacity pool size off pool' hAlloc
  simp [BumpPool.remaining, hCur, hCap]

/-- Allocation returns an in-bounds offset. -/
theorem bump_alloc_offset_in_bounds (pool : BumpPool) (size : Nat) (off : Nat) (pool' : BumpPool)
    (hAlloc : pool.alloc size = some (off, pool')) :
    off + size ≤ pool.capacity := by
  have hOff := bump_alloc_offset pool size off pool' hAlloc
  simp [BumpPool.alloc] at hAlloc
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
    (hSize : size > 0) (hFit : size ≤ pool.capacity) :
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
  simp [SlabPool.free, h]

/-- Allocation from empty pool fails. -/
theorem slab_alloc_empty (pool : SlabPool) (h : pool.freeList = []) :
    pool.alloc = none := by
  simp [SlabPool.alloc, h]

/-- Allocation returns a valid block offset. -/
theorem slab_alloc_offset (pool : SlabPool) (blockIdx off : Nat) (pool' : SlabPool)
    (hAlloc : pool.alloc = some (blockIdx, off, pool')) :
    off = blockIdx * pool.blockSize := by
  simp [SlabPool.alloc] at hAlloc
  match pool.freeList, hAlloc with
  | _ :: _, h => simp at h; exact h.2.1

/-- Allocation preserves block size. -/
theorem slab_alloc_blockSize (pool : SlabPool) (blockIdx off : Nat) (pool' : SlabPool)
    (hAlloc : pool.alloc = some (blockIdx, off, pool')) :
    pool'.blockSize = pool.blockSize := by
  simp [SlabPool.alloc] at hAlloc
  match pool.freeList, hAlloc with
  | _ :: _, h => simp at h; exact h.2.2.1

/-- Allocation preserves block count. -/
theorem slab_alloc_blockCount (pool : SlabPool) (blockIdx off : Nat) (pool' : SlabPool)
    (hAlloc : pool.alloc = some (blockIdx, off, pool')) :
    pool'.blockCount = pool.blockCount := by
  simp [SlabPool.alloc] at hAlloc
  match pool.freeList, hAlloc with
  | _ :: _, h => simp at h; exact h.2.2.2.1

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

end Radix.MemoryPool.Lemmas
