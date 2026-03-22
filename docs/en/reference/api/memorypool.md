# MemoryPool Module API Reference

> **Module**: `Radix.MemoryPool`
> **Source**: `Radix/MemoryPool/`

## Overview

Provides two verified memory pool allocators: a linear bump allocator and a fixed-size slab allocator. Both are backed by `Memory.Buffer` and designed for bare-metal or embedded contexts where dynamic heap allocation is unavailable. The spec layer provides abstract safety proofs, while the model layer gives concrete implementations with proof-carrying invariants.

## Specification (`MemoryPool.Spec`)

Abstract state machines for verification:

```lean
structure BumpState where
  capacity : Nat
  cursor   : Nat

structure SlabState where
  blockSize  : Nat
  blockCount : Nat
  allocated  : Finset Nat
```

Safety properties proven at the spec level:
- Bump allocations never exceed capacity
- Slab allocations track which blocks are in use
- Double-free is statically prevented

## Bump Pool (`MemoryPool.Model`)

A linear bump allocator that hands out contiguous regions from a single buffer. Allocation is O(1). Memory can only be reclaimed in bulk via `reset`.

### Structure

```lean
structure BumpPool where
  buf      : Memory.Buffer
  capacity : Nat
  cursor   : Nat
```

- `buf` — underlying memory buffer
- `capacity` — total size in bytes
- `cursor` — next free byte offset (monotonically increasing until reset)

### Construction

```lean
def BumpPool.new (capacity : Nat) : BumpPool
```

Creates a zero-initialized pool with `cursor = 0`.

### Queries

```lean
def BumpPool.remaining (pool : BumpPool) : Nat       -- capacity - cursor
def BumpPool.canAlloc (pool : BumpPool) (size : Nat) : Bool
```

### Allocation

```lean
def BumpPool.alloc (pool : BumpPool) (size : Nat) : Option (Nat × BumpPool)
def BumpPool.allocAligned (pool : BumpPool) (size align : Nat) : Option (Nat × BumpPool)
```

- `alloc` returns the starting offset and updated pool, or `none` if insufficient space.
- `allocAligned` first advances the cursor to the next aligned offset, then allocates.

### Reset

```lean
def BumpPool.reset (pool : BumpPool) : BumpPool
```

Resets the cursor to 0, effectively freeing all allocations. Buffer contents are not zeroed.

### Read/Write

```lean
def BumpPool.writeU8 (pool : BumpPool) (offset : Nat) (val : UInt8)
    (h : offset < pool.capacity) : BumpPool
def BumpPool.readU8 (pool : BumpPool) (offset : Nat)
    (h : offset < pool.capacity) : UInt8
```

## Slab Pool (`MemoryPool.Model`)

A fixed-size block allocator that manages a pool of identically sized blocks. Supports individual block allocation and deallocation with double-free prevention.

### Structure

```lean
structure SlabPool where
  buf        : Memory.Buffer
  blockSize  : Nat
  blockCount : Nat
  freeList   : List Nat
  allocated  : List Nat
```

- `buf` — underlying memory buffer of size `blockSize * blockCount`
- `blockSize` — size of each block in bytes
- `blockCount` — total number of blocks
- `freeList` — indices of available blocks
- `allocated` — indices of blocks currently in use

### Construction

```lean
def SlabPool.new (blockSize blockCount : Nat) : SlabPool
```

Creates a pool with all blocks on the free list.

### Queries

```lean
def SlabPool.freeCount (pool : SlabPool) : Nat           -- freeList.length
def SlabPool.allocatedCount (pool : SlabPool) : Nat      -- allocated.length
def SlabPool.canAlloc (pool : SlabPool) : Bool            -- freeList is non-empty
```

### Allocation and Deallocation

```lean
def SlabPool.alloc (pool : SlabPool) : Option (Nat × Nat × SlabPool)
def SlabPool.free (pool : SlabPool) (blockIdx : Nat) : Option SlabPool
```

- `alloc` returns `(blockIdx, byteOffset, updatedPool)` by popping from the free list, or `none` if no blocks are available.
- `free` returns the block to the free list. Returns `none` if `blockIdx` is not in `allocated` (prevents double-free).

### Block Read/Write

```lean
def SlabPool.writeBlockU8 (pool : SlabPool) (blockIdx offset : Nat) (val : UInt8)
    (hBlock : blockIdx ∈ pool.allocated)
    (hOffset : offset < pool.blockSize) : SlabPool
def SlabPool.readBlockU8 (pool : SlabPool) (blockIdx offset : Nat)
    (hBlock : blockIdx ∈ pool.allocated)
    (hOffset : offset < pool.blockSize) : UInt8
```

Both operations require proof that the block is currently allocated and the offset is within the block.

## Proofs (`MemoryPool.Lemmas`)

### Bump Pool

- `bump_cursor_le_capacity`: after `alloc`, `cursor ≤ capacity`
- `bump_alloc_offset_valid`: returned offset satisfies `offset + size ≤ capacity`
- `bump_reset_cursor`: `(pool.reset).cursor = 0`
- `bump_capacity_preserved`: all operations preserve `pool.capacity`

### Slab Pool

- `slab_no_double_free`: `free` fails if block is not in `allocated`
- `slab_alloc_free_roundtrip`: `alloc` then `free` returns pool to equivalent state
- `slab_count_invariant`: `freeCount + allocatedCount = blockCount`
- `slab_capacity_preserved`: `blockSize` and `blockCount` are immutable

## Examples

```lean
-- Bump allocator
let pool := BumpPool.new 1024
let (off1, pool) := pool.alloc 64 |>.get!       -- allocate 64 bytes at offset 0
let (off2, pool) := pool.alloc 128 |>.get!      -- allocate 128 bytes at offset 64
#eval pool.remaining                              -- 832
let pool := pool.reset                            -- free everything
#eval pool.remaining                              -- 1024

-- Slab allocator with 32-byte blocks
let pool := SlabPool.new 32 16                    -- 16 blocks of 32 bytes
let (blk, off, pool) := pool.alloc.get!
#eval pool.freeCount                              -- 15
let pool := pool.free blk |>.get!
#eval pool.freeCount                              -- 16
```

## Related Documents

- [Memory](memory.md) — Underlying `Buffer` used by both allocators
- [Alignment](alignment.md) — Aligned allocation support
