import Radix.Bitmap

/-!
# Example: Bitmap / Bitset Operations

Demonstrates the `Radix.Bitmap` module for dense bit-level operations:

- Bitmap creation (zeros, ones)
- Individual bit set/clear/test/toggle
- Population count and find-first-set
- Bulk boolean operations (union, intersection, difference, complement)
- Practical use case: simple page frame allocator
-/

namespace Examples.BitmapDemo

open Radix.Bitmap in

/-- Demonstrate basic bitmap operations. -/
def exampleBasicBitmap : IO Unit := do
  IO.println "=== Bitmap: Basic Operations ==="

  -- Create a 128-bit bitmap initialized to all zeros
  let bm := Bitmap.zeros 128
  IO.println s!"  Created 128-bit bitmap, popcount = {bm.popcount}"

  -- Set bits 0, 7, 42, 127
  let bm := bm.set 0
  let bm := bm.set 7
  let bm := bm.set 42
  let bm := bm.set 127
  IO.println s!"  After setting bits 0, 7, 42, 127: popcount = {bm.popcount}"

  -- Test individual bits
  IO.println s!"  bit 0 = {bm.test 0}"   -- true
  IO.println s!"  bit 1 = {bm.test 1}"   -- false
  IO.println s!"  bit 42 = {bm.test 42}" -- true

  -- Clear a bit
  let bm := bm.clear 7
  IO.println s!"  After clearing bit 7: popcount = {bm.popcount}"
  IO.println s!"  bit 7 = {bm.test 7}"   -- false

  -- Toggle (flip) a bit
  let bm := bm.toggle 1
  IO.println s!"  After toggling bit 1: bit 1 = {bm.test 1}"  -- true
  let bm := bm.toggle 1
  IO.println s!"  After toggling bit 1 again: bit 1 = {bm.test 1}"  -- false

  -- Find first set bit
  match bm.findFirstSet with
  | some idx => IO.println s!"  First set bit = {idx}"  -- 0
  | none => IO.println "  No bits set"

  -- Find first clear bit
  let full := Bitmap.ones 8
  let full := full.clear 5
  match full.findFirstClear with
  | some idx => IO.println s!"  First clear bit in 8-bit bitmap = {idx}"  -- 5
  | none => IO.println "  All bits set"

  IO.println ""

open Radix.Bitmap in

/-- Demonstrate bulk boolean operations on bitmaps. -/
def exampleBulkOps : IO Unit := do
  IO.println "=== Bitmap: Bulk Boolean Operations ==="

  -- Create two 64-bit bitmaps
  let a := (((Bitmap.zeros 64).set 0).set 1).set 2   -- bits 0,1,2
  let b := (((Bitmap.zeros 64).set 1).set 2).set 3   -- bits 1,2,3

  IO.println s!"  A: bits 0,1,2 (popcount = {a.popcount})"
  IO.println s!"  B: bits 1,2,3 (popcount = {b.popcount})"

  -- Union: A ∪ B = {0,1,2,3}
  let u := Bitmap.union a b rfl
  IO.println s!"  A ∪ B: popcount = {u.popcount}"  -- 4

  -- Intersection: A ∩ B = {1,2}
  let i := Bitmap.intersection a b rfl
  IO.println s!"  A ∩ B: popcount = {i.popcount}"  -- 2

  -- Difference: A \ B = {0}
  let d := Bitmap.difference a b rfl
  IO.println s!"  A \\ B: popcount = {d.popcount}"  -- 1
  IO.println s!"  A \\ B bit 0 = {d.test 0}"         -- true

  -- Complement: ~A
  let c := Bitmap.complement a
  IO.println s!"  ~A: popcount = {c.popcount}"  -- 61

  -- Disjoint check
  let disjoint := Bitmap.isDisjoint d (Bitmap.difference b a rfl) rfl
  IO.println s!"  (A\\B) disjoint (B\\A)? {disjoint}"  -- true

  IO.println ""

open Radix.Bitmap in

/-- Practical example: simple page frame allocator using bitmaps.
    Each bit represents one 4 KB page frame. -/
def examplePageAllocator : IO Unit := do
  IO.println "=== Bitmap: Page Frame Allocator ==="

  let numPages := 256  -- 256 pages × 4 KB = 1 MB of memory
  let pageSize := 4096

  -- Initialize: all pages free (bits = 0 means free)
  let mut pages := Bitmap.zeros numPages
  IO.println s!"  Total pages: {numPages} ({numPages * pageSize / 1024} KB)"
  IO.println s!"  Free pages: {numPages - pages.popcount}"

  -- Allocate pages by finding first free (clear) bit
  let mut allocated : List Nat := []
  for _ in [:5] do
    match pages.findFirstClear with
    | some idx =>
      pages := pages.set idx
      allocated := allocated ++ [idx]
    | none =>
      IO.println "  Out of memory!"

  IO.println s!"  Allocated pages: {allocated}"
  IO.println s!"  Free pages: {numPages - pages.popcount}"

  -- Free pages 1 and 3
  pages := pages.clear 1
  pages := pages.clear 3
  IO.println s!"  After freeing pages 1, 3: free = {numPages - pages.popcount}"

  -- Allocate again — should reuse freed pages
  match pages.findFirstClear with
  | some idx =>
    pages := pages.set idx
    IO.println s!"  Reallocated page: {idx}"  -- Should be 1
  | none => IO.println "  Out of memory!"

  IO.println ""

/-- Main entry point for bitmap examples. -/
def main : IO Unit := do
  IO.println "━━━ Bitmap Examples ━━━"
  IO.println ""
  exampleBasicBitmap
  exampleBulkOps
  examplePageAllocator
  IO.println "Bitmap examples complete."

end Examples.BitmapDemo
