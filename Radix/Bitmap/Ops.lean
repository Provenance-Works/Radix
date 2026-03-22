/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bitmap.Spec

/-!
# Bitmap/Bitset Implementation (Layer 2)

Dense bit-array backed by an `Array UInt64` for compact storage and
fast bulk operations. Each UInt64 word holds 64 bits.

Operations:
- O(1) `set`, `clear`, `test`, `toggle`
- O(n/64) `popcount`, `findFirstSet`, `findFirstClear`
- Bulk `union`, `intersection`, `difference`, `complement`

All operations are `@[inline]` for zero-cost abstraction (NFR-002).

## Architecture

This is a **Layer 2 (Verified Implementation)** module.
- Imports Layer 3 (`Bitmap.Spec`) for specification reference.

## References

- v0.2.0 Roadmap: Bitmap / Bitset
- FR-002: Bitwise Operations
- NFR-002: Zero-cost abstractions
-/

set_option linter.dupNamespace false

namespace Radix.Bitmap

/-- Number of bits per word in the backing store. -/
@[inline] private def bitsPerWord : Nat := 64

/-- Compute the number of UInt64 words needed for `n` bits. -/
@[inline] def wordsNeeded (n : Nat) : Nat :=
  (n + bitsPerWord - 1) / bitsPerWord

/-- Dense bitmap backed by an array of UInt64 words.
    Stores `numBits` bits in ⌈numBits/64⌉ words.

    **Internal invariant**: Bits beyond `numBits` in the last word are kept at zero.
    This is maintained by all constructors (`zeros` fills with 0, `ones` masks the
    last word) and single-bit operations (`set`/`clear`/`toggle` are no-ops for
    out-of-range indices). The invariant ensures that `popcount` correctly counts
    only valid bits. The `test` function independently returns `false` for
    out-of-range indices regardless of the invariant (see `test_out_of_bounds`). -/
structure Bitmap where
  /-- Total number of bits in the bitmap. -/
  numBits : Nat
  /-- Backing store: array of UInt64 words. -/
  words : Array Radix.UInt64
  /-- Invariant: the array has exactly the right number of words. -/
  hSize : words.size = wordsNeeded numBits
  deriving Repr

namespace Bitmap

/-! ## Construction -/

/-- Create a bitmap of `n` bits, all initialized to 0. -/
@[inline] def zeros (n : Nat) : Bitmap :=
  let nWords := wordsNeeded n
  { numBits := n
    words := Array.replicate nWords ⟨0⟩
    hSize := Array.size_replicate }

/-- Create a bitmap of `n` bits, all initialized to 1.
    Bits beyond `numBits` in the last word are masked off. -/
def ones (n : Nat) : Bitmap :=
  let nWords := wordsNeeded n
  let allOnes : Radix.UInt64 := ⟨0xFFFFFFFFFFFFFFFF⟩
  let arr := Array.replicate nWords allOnes
  -- Mask off extra bits in the last word
  let remainder := n % bitsPerWord
  if h : nWords > 0 ∧ remainder > 0 then
    let mask : Radix.UInt64 := ⟨(1 <<< remainder.toUInt64) - 1⟩
    let lastIdx := nWords - 1
    have hIdx : lastIdx < arr.size := by
      have : arr.size = nWords := Array.size_replicate
      omega
    let arr' := arr.set lastIdx (⟨arr[lastIdx].val &&& mask.val⟩)
    { numBits := n
      words := arr'
      hSize := by
        have h1 : arr'.size = arr.size := Array.size_set hIdx
        have h2 : arr.size = nWords := Array.size_replicate
        omega }
  else
    { numBits := n
      words := arr
      hSize := Array.size_replicate }

/-! ## Index Helpers -/

/-- Word index for bit position `idx`. -/
@[inline] private def wordIndex (idx : Nat) : Nat := idx / bitsPerWord

/-- Bit offset within a word for bit position `idx`. -/
@[inline] private def bitOffset (idx : Nat) : Nat := idx % bitsPerWord

/-- Create a UInt64 mask with a single bit set at position `offset`. -/
@[inline] private def bitMask (offset : Nat) : Radix.UInt64 :=
  ⟨(1 : _root_.UInt64) <<< offset.toUInt64⟩

/-! ## Single-Bit Operations -/

/-- Test whether bit at `idx` is set. Returns `false` for out-of-range. -/
@[inline] def test (bm : Bitmap) (idx : Nat) : Bool :=
  if h : idx < bm.numBits then
    let wi := wordIndex idx
    let bo := bitOffset idx
    have hWi : wi < bm.words.size := by
      show wordIndex idx < bm.words.size
      rw [bm.hSize]; unfold wordsNeeded wordIndex bitsPerWord; omega
    let word := bm.words[wi]
    (word.val >>> bo.toUInt64) &&& 1 != 0
  else false

/-- Set bit at `idx` to 1. No-op for out-of-range. -/
@[inline] def set (bm : Bitmap) (idx : Nat) : Bitmap :=
  if h : idx < bm.numBits then
    let wi := wordIndex idx
    let bo := bitOffset idx
    have hWi : wi < bm.words.size := by
      show wordIndex idx < bm.words.size
      rw [bm.hSize]; unfold wordsNeeded wordIndex bitsPerWord; omega
    let word := bm.words[wi]
    let newWord : Radix.UInt64 := ⟨word.val ||| (bitMask bo).val⟩
    { bm with
      words := bm.words.set wi newWord
      hSize := by simp [Array.size_set, bm.hSize] }
  else bm

/-- Clear bit at `idx` to 0. No-op for out-of-range. -/
@[inline] def clear (bm : Bitmap) (idx : Nat) : Bitmap :=
  if h : idx < bm.numBits then
    let wi := wordIndex idx
    let bo := bitOffset idx
    have hWi : wi < bm.words.size := by
      show wordIndex idx < bm.words.size
      rw [bm.hSize]; unfold wordsNeeded wordIndex bitsPerWord; omega
    let word := bm.words[wi]
    let newWord : Radix.UInt64 := ⟨word.val &&& ~~~(bitMask bo).val⟩
    { bm with
      words := bm.words.set wi newWord
      hSize := by simp [Array.size_set, bm.hSize] }
  else bm

/-- Toggle bit at `idx`. No-op for out-of-range. -/
@[inline] def toggle (bm : Bitmap) (idx : Nat) : Bitmap :=
  if h : idx < bm.numBits then
    let wi := wordIndex idx
    let bo := bitOffset idx
    have hWi : wi < bm.words.size := by
      show wordIndex idx < bm.words.size
      rw [bm.hSize]; unfold wordsNeeded wordIndex bitsPerWord; omega
    let word := bm.words[wi]
    let newWord : Radix.UInt64 := ⟨word.val ^^^ (bitMask bo).val⟩
    { bm with
      words := bm.words.set wi newWord
      hSize := by simp [Array.size_set, bm.hSize] }
  else bm

/-! ## Bulk Operations -/

/-- Population count: total number of set bits across all words. -/
def popcount (bm : Bitmap) : Nat :=
  go bm.words 0 0
where
  go (arr : Array Radix.UInt64) (idx : Nat) (acc : Nat) : Nat :=
    if h : idx < arr.size then
      let word := arr[idx]
      -- Use UInt64 popcount from Bit.Scan and extract as Nat
      let wordPop := (Radix.UInt64.popcount word).val.toNat
      go arr (idx + 1) (acc + wordPop)
    else acc
  termination_by arr.size - idx

/-- Find the first set bit (lowest index). Returns `none` if all clear. -/
def findFirstSet (bm : Bitmap) : Option Nat :=
  go bm.words 0
where
  go (arr : Array Radix.UInt64) (wordIdx : Nat) : Option Nat :=
    if h : wordIdx < arr.size then
      let word := arr[wordIdx]
      if word.val != 0 then
        -- Count trailing zeros to find the lowest set bit within this word
        let bitPos := (Radix.UInt64.ctz word).val.toNat
        let globalIdx := wordIdx * bitsPerWord + bitPos
        if globalIdx < bm.numBits then some globalIdx else none
      else go arr (wordIdx + 1)
    else none
  termination_by arr.size - wordIdx

/-- Find the first clear bit (lowest index). Returns `none` if all set. -/
def findFirstClear (bm : Bitmap) : Option Nat :=
  go bm.words 0
where
  go (arr : Array Radix.UInt64) (wordIdx : Nat) : Option Nat :=
    if h : wordIdx < arr.size then
      let word := arr[wordIdx]
      let inverted := ~~~word.val
      if inverted != 0 then
        let bitPos := (Radix.UInt64.ctz ⟨inverted⟩).val.toNat
        let globalIdx := wordIdx * bitsPerWord + bitPos
        if globalIdx < bm.numBits then some globalIdx else none
      else go arr (wordIdx + 1)
    else none
  termination_by arr.size - wordIdx

/-! ## Set Operations -/

/-- Bitwise union (OR) of two bitmaps of the same size. -/
def union (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bitmap :=
  { numBits := a.numBits
    words := Array.zipWith (fun x y => ⟨x.val ||| y.val⟩) a.words b.words
    hSize := by simp [Array.size_zipWith, a.hSize, b.hSize, hSize] }

/-- Bitwise intersection (AND) of two bitmaps of the same size. -/
def intersection (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bitmap :=
  { numBits := a.numBits
    words := Array.zipWith (fun x y => ⟨x.val &&& y.val⟩) a.words b.words
    hSize := by simp [Array.size_zipWith, a.hSize, b.hSize, hSize] }

/-- Bitwise difference (AND NOT) of two bitmaps of the same size.
    Result has bits set in `a` but not in `b`. -/
def difference (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bitmap :=
  { numBits := a.numBits
    words := Array.zipWith (fun x y => ⟨x.val &&& ~~~y.val⟩) a.words b.words
    hSize := by simp [Array.size_zipWith, a.hSize, b.hSize, hSize] }

/-- Bitwise complement (NOT) of a bitmap.
    Bits beyond `numBits` in the last word are masked off. -/
def complement (bm : Bitmap) : Bitmap :=
  let nWords := wordsNeeded bm.numBits
  let inverted := bm.words.map (fun w => (⟨~~~w.val⟩ : Radix.UInt64))
  -- Mask off extra bits in the last word
  let remainder := bm.numBits % bitsPerWord
  if h : nWords > 0 ∧ remainder > 0 then
    let mask : Radix.UInt64 := ⟨(1 <<< remainder.toUInt64) - 1⟩
    let lastIdx := nWords - 1
    have hIdx : lastIdx < inverted.size := by
      have : inverted.size = bm.words.size := Array.size_map
      rw [this, bm.hSize]; omega
    let inverted' := inverted.set lastIdx (⟨inverted[lastIdx].val &&& mask.val⟩)
    { numBits := bm.numBits
      words := inverted'
      hSize := by
        have h1 : inverted'.size = inverted.size := Array.size_set hIdx
        have h2 : inverted.size = bm.words.size := Array.size_map
        rw [h1, h2]; exact bm.hSize }
  else
    { numBits := bm.numBits
      words := inverted
      hSize := by
        have : inverted.size = bm.words.size := Array.size_map
        rw [this]; exact bm.hSize }

/-! ## Query Operations -/

/-- Check if bitmap has no bits set. -/
def isEmpty (bm : Bitmap) : Bool :=
  bm.words.all (fun w => w.val == 0)

/-- Check if bitmap has all bits set.
    Note: only checks bits within `numBits`. -/
def isFull (bm : Bitmap) : Bool :=
  popcount bm == bm.numBits

/-- Check if two bitmaps of the same size are disjoint (no common set bits). -/
def isDisjoint (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bool :=
  go 0
where
  go (idx : Nat) : Bool :=
    if h : idx < a.words.size then
      have hy : idx < b.words.size := by
        have := a.hSize; have := b.hSize; rw [hSize] at *; omega
      if a.words[idx].val &&& b.words[idx].val != 0 then false
      else go (idx + 1)
    else true
  termination_by a.words.size - idx

/-- Check if `a` is a subset of `b` (every bit set in `a` is also set in `b`). -/
def isSubsetOf (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bool :=
  go 0
where
  go (idx : Nat) : Bool :=
    if h : idx < a.words.size then
      have hy : idx < b.words.size := by
        have := a.hSize; have := b.hSize; rw [hSize] at *; omega
      let xw := a.words[idx].val
      let yw := b.words[idx].val
      if xw &&& ~~~yw != 0 then false
      else go (idx + 1)
    else true
  termination_by a.words.size - idx

/-! ## Conversion -/

/-- Convert bitmap to a list of set bit indices. -/
def toList (bm : Bitmap) : List Nat :=
  go bm 0 []
where
  go (bm : Bitmap) (idx : Nat) (acc : List Nat) : List Nat :=
    if idx < bm.numBits then
      let acc' := if bm.test idx then acc ++ [idx] else acc
      go bm (idx + 1) acc'
    else acc
  termination_by bm.numBits - idx

/-- Create a bitmap from a list of bit indices to set. -/
def ofList (n : Nat) (indices : List Nat) : Bitmap :=
  indices.foldl (fun bm idx => bm.set idx) (zeros n)

end Bitmap

end Radix.Bitmap
