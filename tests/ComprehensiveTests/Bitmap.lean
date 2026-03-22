import tests.ComprehensiveTests.Framework
import Radix.Bitmap

/-!
# Bitmap/Bitset Tests
## Spec References
- v0.2.0: Dense bit-array backed by UInt64 array
-/

open ComprehensiveTests
open Radix.Bitmap

def runBitmapTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Bitmap tests..."

  -- ## Construction
  let bm0 := Bitmap.zeros 64
  assert (bm0.numBits == 64) "zeros 64 numBits"
  assert (bm0.words.size == 1) "zeros 64 word count"

  let bm128 := Bitmap.zeros 128
  assert (bm128.numBits == 128) "zeros 128 numBits"
  assert (bm128.words.size == 2) "zeros 128 word count"

  let bm100 := Bitmap.zeros 100
  assert (bm100.numBits == 100) "zeros 100 numBits"
  assert (bm100.words.size == 2) "zeros 100 word count (100/64 ceil)"

  -- ## Zeros: all bits false
  for i in [:64] do
    assert (bm0.test i == false) s!"zeros test [{i}] = false"

  -- ## Set and test
  let bm1 := bm0.set 0
  assert (bm1.test 0 == true) "set 0 then test 0"
  assert (bm1.test 1 == false) "set 0 unaffected 1"

  let bm2 := bm0.set 63
  assert (bm2.test 63 == true) "set 63 then test 63"
  assert (bm2.test 0 == false) "set 63 unaffected 0"

  -- Set in second word (for multi-word bitmap)
  let bm3 := bm128.set 65
  assert (bm3.test 65 == true) "set 65 in 128-bit"
  assert (bm3.test 64 == false) "set 65 unaffected 64"
  assert (bm3.test 0 == false) "set 65 unaffected 0"

  -- ## Clear
  let bm4 := bm1.clear 0
  assert (bm4.test 0 == false) "clear 0 after set 0"

  -- ## Toggle
  let bm5 := bm0.toggle 10
  assert (bm5.test 10 == true) "toggle 10 (0->1)"
  let bm6 := bm5.toggle 10
  assert (bm6.test 10 == false) "toggle 10 (1->0)"

  -- ## Out-of-bounds safety
  assert (bm0.test 64 == false) "test OOB returns false"
  assert (bm0.test 1000 == false) "test far OOB returns false"
  let bmOOB := bm0.set 64
  assert (bmOOB.numBits == 64) "set OOB preserves numBits"

  -- ## Population count
  let bmPop := bm0.set 0 |>.set 10 |>.set 20 |>.set 63
  assert (bmPop.popcount == 4) "popcount 4 bits set"
  assert (bm0.popcount == 0) "popcount zeros"

  -- ## isEmpty / isFull
  assert (bm0.isEmpty == true) "zeros isEmpty"
  assert (bm1.isEmpty == false) "set 0 not isEmpty"

  -- ## findFirstSet
  assert (bm0.findFirstSet == none) "FFS zeros"
  assert (bm1.findFirstSet == some 0) "FFS after set 0"
  let bm7 := bm0.set 42
  assert (bm7.findFirstSet == some 42) "FFS after set 42"
  let bm8 := bm7.set 10
  assert (bm8.findFirstSet == some 10) "FFS prefers lower"

  -- ## findFirstClear
  let bmAll := Bitmap.ones 64
  assert (bmAll.findFirstClear == none) "FFC on all-ones"
  let bmCleared := bmAll.clear 30
  assert (bmCleared.findFirstClear == some 30) "FFC after clear 30"

  -- ## Set operations
  let bmA := Bitmap.zeros 64 |>.set 0 |>.set 1 |>.set 2
  let bmB := Bitmap.zeros 64 |>.set 1 |>.set 2 |>.set 3

  -- Union
  let bmUnion := Bitmap.union bmA bmB rfl
  assert (bmUnion.test 0 == true) "union bit 0"
  assert (bmUnion.test 1 == true) "union bit 1"
  assert (bmUnion.test 3 == true) "union bit 3"
  assert (bmUnion.popcount == 4) "union popcount"

  -- Intersection
  let bmInter := Bitmap.intersection bmA bmB rfl
  assert (bmInter.test 0 == false) "intersection bit 0"
  assert (bmInter.test 1 == true) "intersection bit 1"
  assert (bmInter.test 2 == true) "intersection bit 2"
  assert (bmInter.test 3 == false) "intersection bit 3"

  -- Difference
  let bmDiff := Bitmap.difference bmA bmB rfl
  assert (bmDiff.test 0 == true) "difference bit 0"
  assert (bmDiff.test 1 == false) "difference bit 1"

  -- ## Complement
  let bmComp := bm0.complement
  assert (bmComp.test 0 == true) "complement zeros -> all ones bit 0"
  assert (bmComp.test 63 == true) "complement zeros -> all ones bit 63"

  -- ## isDisjoint
  let bmX := Bitmap.zeros 64 |>.set 0 |>.set 1
  let bmY := Bitmap.zeros 64 |>.set 2 |>.set 3
  assert (Bitmap.isDisjoint bmX bmY rfl == true) "disjoint sets"
  let bmZ := Bitmap.zeros 64 |>.set 1 |>.set 2
  assert (Bitmap.isDisjoint bmX bmZ rfl == false) "non-disjoint sets"

  -- ## isSubsetOf
  let bmSub := Bitmap.zeros 64 |>.set 0
  assert (Bitmap.isSubsetOf bmSub bmA rfl == true) "subset"
  assert (Bitmap.isSubsetOf bmA bmSub rfl == false) "not subset"

  -- ## Conversion
  let bmFrom := Bitmap.ofList 64 [5, 10, 15]
  assert (bmFrom.test 5 == true) "ofList 5"
  assert (bmFrom.test 10 == true) "ofList 10"
  assert (bmFrom.test 15 == true) "ofList 15"
  assert (bmFrom.test 0 == false) "ofList not 0"

  -- ## Property: set/clear round-trip
  let mut rng := PRNG.new
  let mut bmProp := Bitmap.zeros 256
  for _ in [:numIter] do
    let (rng', idx) := rng.nextNat 256
    rng := rng'
    let bmSet := bmProp.set idx
    assert (bmSet.test idx == true) s!"prop: set then test [{idx}]"
    let bmClr := bmSet.clear idx
    assert (bmClr.test idx == false) s!"prop: set+clear then test [{idx}]"
    bmProp := bmSet

  c.get
