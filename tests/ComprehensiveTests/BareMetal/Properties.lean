import tests.ComprehensiveTests.Framework
import Radix.BareMetal.Spec
import Radix.BareMetal.GCFree
import Radix.BareMetal.Linker
import Radix.BareMetal.Startup

/-!
# BareMetal Property-Based Tests
## Spec References
- P4-08: Alignment, MemRegion, GCFree, Startup properties
-/

open ComprehensiveTests
open Radix.BareMetal.Spec
open Radix.BareMetal.GCFree
open Radix.BareMetal.Linker
open Radix.BareMetal.Startup

def runBareMetalPropertyTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    BareMetal property tests..."
  let mut rng := PRNG.new 55555

  -- ## alignUp property: result >= input and aligned
  let alignments : List Nat := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 4096]
  for _ in [:numIter] do
    let (rng', a) := rng.nextBounded 100000;  rng := rng'
    let a := a.toNat
    for al in alignments do
      let up := alignUp a al
      assert (up ≥ a) "alignUp >= addr prop"
      assert (isAligned up al == true) "alignUp aligned prop"
      -- alignUp is the smallest aligned value >= a
      if up > 0 && al > 0 then
        assert (up - al < a ∨ up == 0) "alignUp minimal"

  -- ## alignDown property: result <= input and aligned
  for _ in [:numIter] do
    let (rng', a) := rng.nextBounded 100000;  rng := rng'
    let a := a.toNat
    for al in alignments do
      let down := alignDown a al
      assert (down ≤ a) "alignDown <= addr prop"
      assert (isAligned down al == true) "alignDown aligned prop"
      -- alignDown is the largest aligned value <= a
      assert (down + al > a ∨ down == a) "alignDown maximal"

  -- ## alignUp(alignDown(x)) == alignUp(x) when x is already in range
  for _ in [:numIter] do
    let (rng', a) := rng.nextBounded 100000;  rng := rng'
    let a := a.toNat
    for al in alignments do
      let down := alignDown a al
      let upDown := alignUp down al
      assert (upDown == down) "alignUp(alignDown(x)) == alignDown(x)"

  -- ## isAligned(alignUp(x, a), a) always true
  for _ in [:50] do
    let (rng', a) := rng.nextBounded 50000;  rng := rng'
    let (rng'', alIdx) := rng.nextNat alignments.length;  rng := rng''
    let al := alignments[alIdx % alignments.length]!
    assert (isAligned (alignUp a.toNat al) al == true) "alignUp always aligned"
    assert (isAligned (alignDown a.toNat al) al == true) "alignDown always aligned"

  -- ## MemRegion.disjoint is commutative
  for _ in [:numIter] do
    let (rng', base1) := rng.nextBounded 10000;  rng := rng'
    let (rng'', size1) := rng.nextBounded 1000;  rng := rng''
    let (rng3, base2) := rng.nextBounded 10000;  rng := rng3
    let (rng4, size2) := rng.nextBounded 1000;  rng := rng4
    let r1 : MemRegion := ⟨"a", base1.toNat, size1.toNat, .ram, .readWrite⟩
    let r2 : MemRegion := ⟨"b", base2.toNat, size2.toNat, .ram, .readWrite⟩
    let d12 := Decidable.decide (MemRegion.disjoint r1 r2)
    let d21 := Decidable.decide (MemRegion.disjoint r2 r1)
    assert (d12 == d21) "disjoint commutative"

  -- ## disjoint ↔ ¬overlaps for non-zero size
  for _ in [:numIter] do
    let (rng', base1) := rng.nextBounded 10000;  rng := rng'
    let (rng'', size1) := rng.nextBounded 1000;  rng := rng''
    let size1' := size1.toNat + 1  -- ensure non-zero
    let (rng3, base2) := rng.nextBounded 10000;  rng := rng3
    let (rng4, size2) := rng.nextBounded 1000;  rng := rng4
    let size2' := size2.toNat + 1
    let r1 : MemRegion := ⟨"a", base1.toNat, size1', .ram, .readWrite⟩
    let r2 : MemRegion := ⟨"b", base2.toNat, size2', .ram, .readWrite⟩
    let disj := Decidable.decide (MemRegion.disjoint r1 r2)
    let over := Decidable.decide (MemRegion.overlaps r1 r2)
    assert ((disj && !over) ∨ (!disj && over)) "disjoint xor overlaps"

  -- ## GCFree: default constraint always accepts static/stack/none
  let dflt := GCFreeConstraint.default
  for _ in [:numIter] do
    let (rng', stackSize) := rng.nextBounded 4096;  rng := rng'
    let p1 := AllocProfile.mk "f" .stack (some stackSize.toNat)
    assert (checkProfile dflt p1 == true) "default accepts stack <= 4096"
    let p2 := AllocProfile.mk "f" .static none
    assert (checkProfile dflt p2 == true) "default always accepts static"
    let p3 := AllocProfile.mk "f" .none none
    assert (checkProfile dflt p3 == true) "default always accepts none"

  -- ## GCFree: default rejects arena
  for _ in [:50] do
    let (rng', sz) := rng.nextBounded 100;  rng := rng'
    let p := AllocProfile.mk "f" .arena (some sz.toNat)
    assert (checkProfile dflt p == false) "default rejects arena"

  -- ## StackFrame totalSize is sum
  for _ in [:numIter] do
    let (rng', local_) := rng.nextBounded 1000;  rng := rng'
    let (rng'', saved) := rng.nextBounded 200;  rng := rng''
    let (rng3, pad) := rng.nextBounded 64;  rng := rng3
    let frame := StackFrame.mk "f" local_.toNat saved.toNat pad.toNat
    assert (frame.totalSize == local_.toNat + saved.toNat + pad.toNat) "totalSize = sum"

  -- ## worstCaseStackDepth is sum of frame sizes
  for _ in [:50] do
    let (rng', n) := rng.nextBounded 10;  rng := rng'
    let mut frames : List StackFrame := []
    let mut expectedTotal := 0
    for i in [:n.toNat] do
      let (rng'', sz) := rng.nextBounded 200;  rng := rng''
      let frame := StackFrame.mk s!"fn_{i}" sz.toNat 16 0
      frames := frames ++ [frame]
      expectedTotal := expectedTotal + (sz.toNat + 16)
    assert (worstCaseStackDepth frames == expectedTotal) "worstCase = sum"

  -- ## Startup: all platforms word bits are multiples of 8
  for p in [Platform.x86_64, .aarch64, .riscv64] do
    assert (p.wordBits % 8 == 0) "wordBits mod 8"
    assert (p.naturalAlign > 0) "naturalAlign positive"
    assert (p.wordBits == p.naturalAlign * 8) "wordBits = align * 8"

  -- ## Startup: minimalStartupActions always valid
  for _ in [:50] do
    let (rng', sp) := rng.nextBounded 0x10000;  rng := rng'
    let (rng'', bbas) := rng.nextBounded 0x10000;  rng := rng''
    let (rng3, bsz) := rng.nextBounded 0x1000;  rng := rng3
    let (rng4, dlma) := rng.nextBounded 0x10000;  rng := rng4
    let (rng5, dvma) := rng.nextBounded 0x10000;  rng := rng5
    let (rng6, dsz) := rng.nextBounded 0x1000;  rng := rng6
    let (rng7, entry) := rng.nextBounded 0x10000;  rng := rng7
    let actions := minimalStartupActions sp.toNat bbas.toNat bsz.toNat dlma.toNat dvma.toNat dsz.toNat entry.toNat
    assert (isValidStartupSequence actions == true) "minimal always valid"

  c.get
