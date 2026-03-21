import Radix.MemoryPool

/-!
# Example: Memory Pool Allocators

Demonstrates the `Radix.MemoryPool` module with two allocator models:

1. **Bump Allocator** — Linear allocation with O(1) alloc, bulk reset
2. **Slab Allocator** — Fixed-size block allocation with free/reuse

Practical use cases:
- Embedded systems without heap allocator
- Arena-style allocation for request processing
- Pool allocation for fixed-size objects (network packets, buffers)
-/

namespace Examples.MemoryPoolDemo

open Radix.MemoryPool in

/-- Demonstrate bump allocator operations. -/
def exampleBumpAllocator : IO Unit := do
  IO.println "=== Memory Pool: Bump Allocator ==="

  -- Create a bump pool with 1024 bytes capacity
  let pool0 := BumpPool.new 1024
  IO.println s!"Created pool: capacity = {pool0.capacity}, remaining = {pool0.remaining}"

  -- Allocate 64 bytes
  match pool0.alloc 64 with
  | some (offset1, pool1) =>
    IO.println s!"Allocated 64 bytes at offset {offset1}, remaining = {pool1.remaining}"

    -- Allocate another 128 bytes
    match pool1.alloc 128 with
    | some (offset2, pool2) =>
      IO.println s!"Allocated 128 bytes at offset {offset2}, remaining = {pool2.remaining}"

      -- Allocate 256 bytes
      match pool2.alloc 256 with
      | some (offset3, pool3) =>
        IO.println s!"Allocated 256 bytes at offset {offset3}, remaining = {pool3.remaining}"

        -- Try to allocate more than remaining
        let big := pool3.remaining + 1
        match pool3.alloc big with
        | some _ => IO.println "  ERROR: should fail for oversized alloc"
        | none =>
          IO.println s!"Correctly rejected alloc of {big} bytes (only {pool3.remaining} free)"

          -- Reset reclaims all memory
          let pool4 := pool3.reset
          IO.println s!"After reset: remaining = {pool4.remaining}"

          -- Can allocate again after reset
          match pool4.alloc 512 with
          | some (offset5, pool5) =>
            IO.println s!"Post-reset alloc: 512 bytes at offset {offset5}, remaining = {pool5.remaining}"
          | none => IO.println "  Post-reset alloc failed"
      | none => IO.println "  Third alloc failed"
    | none => IO.println "  Second allocation failed"
  | none => IO.println "  First allocation failed"

  IO.println ""

open Radix.MemoryPool in

/-- Demonstrate aligned bump allocation. -/
def exampleAlignedAlloc : IO Unit := do
  IO.println "=== Memory Pool: Aligned Allocation ==="

  let pool0 := BumpPool.new 512

  -- Allocate 1 byte (cursor moves to 1)
  match pool0.alloc 1 with
  | some (off1, pool1) =>
    IO.println s!"1 byte at offset {off1}"

    -- Allocate 4 bytes, aligned to 4-byte boundary
    match pool1.allocAligned 4 4 with
    | some (off2, pool2) =>
      IO.println s!"4 bytes (align 4) at offset {off2}"

      -- Allocate 8 bytes, aligned to 8-byte boundary
      match pool2.allocAligned 8 8 with
      | some (off3, pool3) =>
        IO.println s!"8 bytes (align 8) at offset {off3}"
        IO.println s!"Remaining: {pool3.remaining}"
      | none => IO.println "  Aligned alloc 8 failed"
    | none => IO.println "  Aligned alloc 4 failed"
  | none => IO.println "  First alloc failed"

  IO.println ""

open Radix.MemoryPool in

/-- Demonstrate slab allocator operations. -/
def exampleSlabAllocator : IO Unit := do
  IO.println "=== Memory Pool: Slab Allocator ==="

  -- Create a slab pool: 64-byte blocks, 8 blocks total
  let pool0 := SlabPool.new 64 8 (by omega)
  IO.println s!"Created slab pool: {pool0.blockCount} blocks x {pool0.blockSize} bytes"
  IO.println s!"Free blocks: {pool0.freeCount}, allocated: {pool0.allocatedCount}"

  -- Allocate 3 blocks
  match pool0.alloc with
  | some (blk0, _off0, pool1) =>
    match pool1.alloc with
    | some (blk1, _off1, pool2) =>
      match pool2.alloc with
      | some (blk2, _off2, pool3) =>
        IO.println s!"Allocated blocks: {blk0}, {blk1}, {blk2}"
        IO.println s!"Free: {pool3.freeCount}, allocated: {pool3.allocatedCount}"

        -- Free block 1
        match pool3.free blk1 with
        | some pool4 =>
          IO.println s!"Freed block {blk1}: free = {pool4.freeCount}"

          -- Allocate again — should reuse freed slot
          match pool4.alloc with
          | some (blkNew, _offNew, pool5) =>
            IO.println s!"Reallocated block: {blkNew}"
            IO.println s!"Free: {pool5.freeCount}, allocated: {pool5.allocatedCount}"

            -- Cannot free an invalid/non-allocated block
            match pool5.free 999 with
            | some _ => IO.println "  ERROR: should not free invalid block"
            | none => IO.println "  Correctly rejected invalid block free"

          | none => IO.println "  Reallocation failed"
        | none => IO.println "  Free failed"
      | none => IO.println "  Third alloc failed"
    | none => IO.println "  Second alloc failed"
  | none => IO.println "  First alloc failed"

  IO.println ""

open Radix.MemoryPool in

/-- Practical example: arena-style allocation for batch processing.
    Allocate a bunch of objects, process them, then reset everything. -/
def exampleArenaPattern : IO Unit := do
  IO.println "=== Memory Pool: Arena Pattern ==="

  let arenaSize := 4096
  let mut arena := BumpPool.new arenaSize
  IO.println s!"Arena: {arenaSize} bytes"

  -- Simulate request processing: allocate structs of various sizes
  let sizes : List Nat := [32, 64, 16, 128, 48, 256, 32]
  let mut offsets : List Nat := []

  for size in sizes do
    match arena.alloc size with
    | some (off, arena') =>
      arena := arena'
      offsets := offsets ++ [off]
    | none =>
      IO.println s!"Arena exhausted at size {size}"

  IO.println s!"Allocated {offsets.length} objects: {offsets}"
  IO.println s!"Used: {arenaSize - arena.remaining}/{arenaSize} bytes"

  -- Process complete — reset arena in O(1)
  arena := arena.reset
  IO.println s!"After reset: used = {arenaSize - arena.remaining}/{arenaSize}"
  IO.println s!"Ready for next batch!"

  IO.println ""

/-- Main entry point for memory pool examples. -/
def main : IO Unit := do
  IO.println "━━━ Memory Pool Examples ━━━"
  IO.println ""
  exampleBumpAllocator
  exampleAlignedAlloc
  exampleSlabAllocator
  exampleArenaPattern
  IO.println "Memory pool examples complete."

end Examples.MemoryPoolDemo
