/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Memory.Model
import Radix.MemoryPool.Spec

/-!
# Memory Pool Model (Layer 2)

Concrete implementations of memory pool allocators backed by `Memory.Buffer`:

- **BumpPool**: Arena-style bump allocator.
  O(1) allocation, O(1) bulk reset. No individual free.

- **SlabPool**: Fixed-size block pool allocator.
  O(1) allocation and deallocation via free list.

Both models are pure functional — no mutation, no FFI.
All memory is managed by Lean's GC (ADR C-001).

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- v0.2.0 Roadmap: Memory Pool Model
- FR-004: Memory Safety
- NFR-002: Zero-cost abstractions
-/

namespace Radix.MemoryPool

open Radix.Memory

/-! ================================================================ -/
/-! ## Bump Pool                                                      -/
/-! ================================================================ -/

/-- A bump allocator backed by a `Memory.Buffer`.
    Allocations advance a cursor; all are freed at once via `reset`. -/
structure BumpPool where
  /-- Backing memory buffer. -/
  buf : Buffer
  /-- Total capacity in bytes. -/
  capacity : Nat
  /-- Current allocation cursor (offset of next allocation). -/
  cursor : Nat
  /-- Invariant: cursor never exceeds capacity. -/
  hCursor : cursor ≤ capacity
  /-- Invariant: buffer size equals capacity. -/
  hBufSize : buf.size = capacity
  deriving Repr

namespace BumpPool

/-- Create a new bump pool with the given capacity (zero-initialized). -/
@[inline] def new (capacity : Nat) : BumpPool :=
  { buf := Buffer.zeros capacity
    capacity := capacity
    cursor := 0
    hCursor := Nat.zero_le capacity
    hBufSize := by simp [Buffer.zeros, Buffer.size, ByteArray.size, Array.size_replicate] }

/-- Remaining free bytes in the pool. -/
@[inline] def remaining (pool : BumpPool) : Nat := pool.capacity - pool.cursor

/-- Check if the pool has enough space for `size` bytes. -/
@[inline] def canAlloc (pool : BumpPool) (size : Nat) : Bool := pool.cursor + size ≤ pool.capacity

/-- Attempt to allocate `size` bytes from the pool.
    Returns the offset of the allocation and the updated pool,
    or `none` if insufficient capacity. -/
def alloc (pool : BumpPool) (size : Nat) : Option (Nat × BumpPool) :=
  if h : size == 0 then none
  else if h2 : pool.cursor + size ≤ pool.capacity then
    let offset := pool.cursor
    some (offset,
      { pool with
        cursor := pool.cursor + size
        hCursor := h2
        hBufSize := pool.hBufSize })
  else none

/-- Attempt to allocate `size` bytes with alignment.
    The returned offset is guaranteed to be a multiple of `align`. -/
def allocAligned (pool : BumpPool) (size : Nat) (align : Nat) : Option (Nat × BumpPool) :=
  if align == 0 then none
  else
    let alignedCursor := ((pool.cursor + align - 1) / align) * align
    let totalNeeded := alignedCursor + size
    if h : totalNeeded ≤ pool.capacity ∧ size > 0 then
      some (alignedCursor,
        { pool with
          cursor := alignedCursor + size
          hCursor := by omega
          hBufSize := pool.hBufSize })
    else none

/-- Reset the pool: reclaim all allocated memory.
    The cursor returns to 0; the buffer content is not zeroed
    (callers should not rely on buffer content after reset). -/
@[inline] def reset (pool : BumpPool) : BumpPool :=
  { pool with
    cursor := 0
    hCursor := Nat.zero_le pool.capacity }

/-- Write a byte into an allocated region of the pool. -/
def writeU8 (pool : BumpPool) (offset : Nat) (val : Radix.UInt8)
    (h : offset < pool.capacity) : BumpPool :=
  let hBuf : offset < pool.buf.size := by rw [pool.hBufSize]; exact h
  { pool with
    buf := pool.buf.writeU8 offset val hBuf
    hBufSize := by
      simp [Buffer.writeU8, Buffer.size, ByteArray.size]
      rw [Buffer.set_size_eq]
      exact pool.hBufSize }

/-- Read a byte from the pool. -/
@[inline] def readU8 (pool : BumpPool) (offset : Nat) (h : offset < pool.capacity) : Radix.UInt8 :=
  pool.buf.readU8 offset (by rw [pool.hBufSize]; exact h)

end BumpPool

/-! ================================================================ -/
/-! ## Slab Pool                                                      -/
/-! ================================================================ -/

/-- A slab allocator with fixed-size blocks.
    Free blocks are tracked via an index-based free list. -/
structure SlabPool where
  /-- Backing memory buffer. -/
  buf : Buffer
  /-- Size of each block in bytes. Must be > 0. -/
  blockSize : Nat
  /-- Total number of blocks. -/
  blockCount : Nat
  /-- Stack of free block indices (most recent at head). -/
  freeList : List Nat
  /-- Set of allocated block indices. -/
  allocated : List Nat
  /-- Invariant: blockSize > 0. -/
  hBlockSize : blockSize > 0
  /-- Invariant: buffer size equals blockSize * blockCount. -/
  hBufSize : buf.size = blockSize * blockCount
  deriving Repr

namespace SlabPool

/-- Create a new slab pool with the given block size and count. -/
def new (blockSize : Nat) (blockCount : Nat) (hBS : blockSize > 0) : SlabPool :=
  let totalSize := blockSize * blockCount
  { buf := Buffer.zeros totalSize
    blockSize := blockSize
    blockCount := blockCount
    freeList := (List.range blockCount).reverse  -- LIFO order
    allocated := []
    hBlockSize := hBS
    hBufSize := by simp [Buffer.zeros, Buffer.size, ByteArray.size, Array.size_replicate] }

/-- Number of free blocks available. -/
@[inline] def freeCount (pool : SlabPool) : Nat := pool.freeList.length

/-- Number of allocated blocks. -/
@[inline] def allocatedCount (pool : SlabPool) : Nat := pool.allocated.length

/-- Check if the pool has any free blocks. -/
@[inline] def canAlloc (pool : SlabPool) : Bool := !pool.freeList.isEmpty

/-- Attempt to allocate one block from the pool.
    Returns the block index (0-based) and offset within the buffer. -/
def alloc (pool : SlabPool) : Option (Nat × Nat × SlabPool) :=
  match pool.freeList with
  | [] => none
  | blockIdx :: rest =>
    let offset := blockIdx * pool.blockSize
    some (blockIdx, offset,
      { pool with
        freeList := rest
        allocated := blockIdx :: pool.allocated })

/-- Free a block by its index. Returns `none` on double-free attempt. -/
def free (pool : SlabPool) (blockIdx : Nat) : Option SlabPool :=
  if pool.allocated.contains blockIdx then
    some
      { pool with
        freeList := blockIdx :: pool.freeList
        allocated := pool.allocated.filter (· != blockIdx) }
  else none

/-- Write a byte within a specific block. -/
def writeBlockU8 (pool : SlabPool) (blockIdx : Nat) (byteOffset : Nat) (val : Radix.UInt8)
    (hBlock : blockIdx < pool.blockCount) (hByte : byteOffset < pool.blockSize) : SlabPool :=
  let offset := blockIdx * pool.blockSize + byteOffset
  have hOff : offset < pool.buf.size := by
    rw [pool.hBufSize]; omega
  { pool with
    buf := pool.buf.writeU8 offset val hOff
    hBufSize := by
      simp [Buffer.writeU8, Buffer.size, ByteArray.size]
      rw [Buffer.set_size_eq]
      exact pool.hBufSize }

/-- Read a byte within a specific block. -/
@[inline] def readBlockU8 (pool : SlabPool) (blockIdx : Nat) (byteOffset : Nat)
    (hBlock : blockIdx < pool.blockCount) (hByte : byteOffset < pool.blockSize) : Radix.UInt8 :=
  let offset := blockIdx * pool.blockSize + byteOffset
  pool.buf.readU8 offset (by rw [pool.hBufSize]; omega)

end SlabPool

end Radix.MemoryPool
