import tests.ComprehensiveTests.Framework
import Radix.MemoryPool

/-!
# Memory Pool Tests
## Spec References
- v0.2.0: Bump allocator and slab allocator model
-/

open ComprehensiveTests
open Radix.MemoryPool

def runMemoryPoolTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Memory pool tests..."

  -- ============================================
  -- Bump Pool Tests
  -- ============================================
  IO.println "      Bump pool..."

  -- ## Construction
  let bp := BumpPool.new 256
  assert (bp.capacity == 256) "bump new capacity"
  assert (bp.cursor == 0) "bump new cursor"
  assert (bp.remaining == 256) "bump new remaining"

  -- ## Allocation
  match bp.alloc 32 with
  | none => assert false "bump alloc 32 should succeed"
  | some (off, bp1) =>
    assert (off == 0) "bump first alloc offset = 0"
    assert (bp1.cursor == 32) "bump cursor after alloc 32"
    assert (bp1.remaining == 224) "bump remaining after alloc 32"
    assert (bp1.capacity == 256) "bump capacity preserved"

    -- Second allocation
    match bp1.alloc 64 with
    | none => assert false "bump alloc 64 should succeed"
    | some (off2, bp2) =>
      assert (off2 == 32) "bump second alloc offset"
      assert (bp2.cursor == 96) "bump cursor after 32+64"
      assert (bp2.remaining == 160) "bump remaining after 96"

      -- ## Read/Write
      let bp3 := bp2.writeU8 0 ⟨42⟩ (by omega)
      let v := bp3.readU8 0 (by omega)
      assert (v.toNat == 42) "bump write/read round-trip"

      -- ## Reset
      let bpReset := bp2.reset
      assert (bpReset.cursor == 0) "bump reset cursor"
      assert (bpReset.remaining == 256) "bump reset remaining"
      assert (bpReset.capacity == 256) "bump reset capacity"

      -- After reset, can allocate again
      match bpReset.alloc 100 with
      | none => assert false "bump alloc after reset should succeed"
      | some (off3, _) =>
        assert (off3 == 0) "bump after reset: offset 0"

  -- ## Zero-size allocation fails
  assert (bp.alloc 0 == none) "bump alloc 0 fails"

  -- ## Exhaust capacity
  match bp.alloc 256 with
  | none => assert false "bump alloc full capacity should work"
  | some (_, bpFull) =>
    assert (bpFull.remaining == 0) "bump full remaining"
    assert (bpFull.alloc 1 == none) "bump alloc when full fails"

  -- ## Overflow: allocate more than capacity
  assert (bp.alloc 257 == none) "bump alloc > capacity fails"

  -- ## Aligned allocation
  match bp.allocAligned 32 8 with
  | none => assert false "bump allocAligned should succeed"
  | some (off, bp1) =>
    assert (off % 8 == 0) s!"bump aligned offset {off} mod 8 = 0"
    -- Allocate at non-aligned cursor, then aligned
    match bp1.alloc 3 with
    | none => assert false "bump alloc 3 should succeed"
    | some (_, bp2) =>
      -- cursor is now at 35, next aligned to 8 is 40
      match bp2.allocAligned 16 8 with
      | none => assert false "bump allocAligned after 35 should succeed"
      | some (off2, _) =>
        assert (off2 % 8 == 0) s!"bump aligned offset {off2} mod 8 = 0"

  -- ## canAlloc
  assert (bp.canAlloc 100 == true) "bump canAlloc 100"
  assert (bp.canAlloc 256 == true) "bump canAlloc 256"
  assert (bp.canAlloc 257 == false) "bump canAlloc 257"

  -- ============================================
  -- Slab Pool Tests
  -- ============================================
  IO.println "      Slab pool..."

  -- ## Construction
  let sp := SlabPool.new 64 8 (by omega)
  assert (sp.blockSize == 64) "slab blockSize"
  assert (sp.blockCount == 8) "slab blockCount"
  assert (sp.freeCount == 8) "slab initial freeCount"
  assert (sp.allocatedCount == 0) "slab initial allocatedCount"

  -- ## Allocation
  match sp.alloc with
  | none => assert false "slab alloc should succeed"
  | some (blockIdx, off, sp1) =>
    assert (off == blockIdx * 64) "slab alloc offset = blockIdx * blockSize"
    assert (sp1.freeCount == 7) "slab freeCount after alloc"
    assert (sp1.allocatedCount == 1) "slab allocatedCount after alloc"

    -- ## Free
    match sp1.free blockIdx with
    | none => assert false "slab free should succeed"
    | some sp2 =>
      assert (sp2.freeCount == 8) "slab freeCount after free"
      assert (sp2.allocatedCount == 0) "slab allocatedCount after free"

    -- ## Double-free detection
    match sp1.free blockIdx with
    | none => assert false "first free should work"
    | some sp2 =>
      assert (sp2.free blockIdx == none) "slab double-free detected"

  -- ## Exhaust all blocks
  let mut spEx := sp
  let mut allocatedIndices : List Nat := []
  for _ in [:8] do
    match spEx.alloc with
    | none => assert false "slab alloc should succeed (not exhausted)"
    | some (idx, _, sp') =>
      allocatedIndices := idx :: allocatedIndices
      spEx := sp'
  assert (spEx.freeCount == 0) "slab all allocated: freeCount 0"
  assert (spEx.allocatedCount == 8) "slab all allocated: allocatedCount 8"
  assert (spEx.alloc == none) "slab alloc when exhausted fails"

  -- ## Free all blocks
  for idx in allocatedIndices do
    match spEx.free idx with
    | none => assert false s!"slab free [{idx}] should succeed"
    | some sp' => spEx := sp'
  assert (spEx.freeCount == 8) "slab all freed: freeCount 8"
  assert (spEx.allocatedCount == 0) "slab all freed: allocatedCount 0"

  -- ## Read/Write block
  match sp.alloc with
  | none => assert false "slab alloc for write test"
  | some (blockIdx, _, sp1) =>
    let sp2 := sp1.writeBlockU8 blockIdx 0 ⟨0xAB⟩
      (by omega) (by omega)
    let v := sp2.readBlockU8 blockIdx 0 (by omega) (by omega)
    assert (v.toNat == 0xAB) "slab write/read round-trip"

  -- ## canAlloc
  assert (sp.canAlloc == true) "slab canAlloc on fresh"

  c.get
