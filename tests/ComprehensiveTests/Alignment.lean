import tests.ComprehensiveTests.Framework
import Radix.Alignment

/-!
# Alignment Utilities Tests
## Spec References
- v0.2.0: Alignment utilities (alignUp, alignDown, isAligned, padding)
-/

open ComprehensiveTests
open Radix.Alignment

def runAlignmentTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Alignment tests..."

  -- ## isAligned
  assert (isAligned 0 4 == true) "isAligned 0 4"
  assert (isAligned 4 4 == true) "isAligned 4 4"
  assert (isAligned 8 4 == true) "isAligned 8 4"
  assert (isAligned 1 4 == false) "isAligned 1 4"
  assert (isAligned 3 4 == false) "isAligned 3 4"
  assert (isAligned 5 4 == false) "isAligned 5 4"
  assert (isAligned 16 16 == true) "isAligned 16 16"
  assert (isAligned 0 1 == true) "isAligned 0 1"
  assert (isAligned 7 1 == true) "isAligned 7 1"

  -- ## alignUp
  assert (alignUp 0 4 == 0) "alignUp 0 4"
  assert (alignUp 1 4 == 4) "alignUp 1 4"
  assert (alignUp 3 4 == 4) "alignUp 3 4"
  assert (alignUp 4 4 == 4) "alignUp 4 4"
  assert (alignUp 5 4 == 8) "alignUp 5 4"
  assert (alignUp 0 1 == 0) "alignUp 0 1"
  assert (alignUp 7 1 == 7) "alignUp 7 1"
  assert (alignUp 13 8 == 16) "alignUp 13 8"
  assert (alignUp 16 8 == 16) "alignUp 16 8"
  -- Edge: align=0 returns 0
  assert (alignUp 5 0 == 0) "alignUp align=0"

  -- ## alignDown
  assert (alignDown 0 4 == 0) "alignDown 0 4"
  assert (alignDown 1 4 == 0) "alignDown 1 4"
  assert (alignDown 3 4 == 0) "alignDown 3 4"
  assert (alignDown 4 4 == 4) "alignDown 4 4"
  assert (alignDown 7 4 == 4) "alignDown 7 4"
  assert (alignDown 8 4 == 8) "alignDown 8 4"
  assert (alignDown 15 8 == 8) "alignDown 15 8"
  assert (alignDown 16 8 == 16) "alignDown 16 8"

  -- ## alignPadding
  assert (alignPadding 0 4 == 0) "alignPadding 0 4"
  assert (alignPadding 1 4 == 3) "alignPadding 1 4"
  assert (alignPadding 3 4 == 1) "alignPadding 3 4"
  assert (alignPadding 4 4 == 0) "alignPadding 4 4"
  assert (alignPadding 5 4 == 3) "alignPadding 5 4"

  -- ## isPowerOfTwo
  assert (isPowerOfTwo 1 == true) "isPowerOfTwo 1"
  assert (isPowerOfTwo 2 == true) "isPowerOfTwo 2"
  assert (isPowerOfTwo 4 == true) "isPowerOfTwo 4"
  assert (isPowerOfTwo 8 == true) "isPowerOfTwo 8"
  assert (isPowerOfTwo 16 == true) "isPowerOfTwo 16"
  assert (isPowerOfTwo 0 == false) "isPowerOfTwo 0"
  assert (isPowerOfTwo 3 == false) "isPowerOfTwo 3"
  assert (isPowerOfTwo 6 == false) "isPowerOfTwo 6"
  assert (isPowerOfTwo 15 == false) "isPowerOfTwo 15"

  -- ## Power-of-two fast paths
  assert (isAlignedPow2 0 4 == true) "isAlignedPow2 0 4"
  assert (isAlignedPow2 4 4 == true) "isAlignedPow2 4 4"
  assert (isAlignedPow2 3 4 == false) "isAlignedPow2 3 4"
  assert (alignUpPow2 5 4 == 8) "alignUpPow2 5 4"
  assert (alignUpPow2 8 4 == 8) "alignUpPow2 8 4"
  assert (alignDownPow2 7 4 == 4) "alignDownPow2 7 4"
  assert (alignDownPow2 8 4 == 8) "alignDownPow2 8 4"

  -- ## Property: alignDown ≤ offset ≤ alignUp
  let mut rng := PRNG.new
  for _ in [:numIter] do
    let (rng', offset) := rng.nextNat 1024
    rng := rng'
    let (rng', align') := rng.nextNat 32
    rng := rng'
    let align := align' + 1  -- avoid 0
    let down := alignDown offset align
    let up := alignUp offset align
    assert (down <= offset) s!"alignDown {offset} {align} ≤ offset"
    assert (offset <= up) s!"offset ≤ alignUp {offset} {align}"
    assert (down <= up) s!"sandwich: alignDown ≤ alignUp"

  c.get
