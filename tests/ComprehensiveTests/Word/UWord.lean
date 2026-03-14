import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Word.Size
import Radix.Bit.Ops
import Radix.Bit.Scan

/-!
# UWord Comprehensive Tests (platform-width unsigned)
## Spec References
- FR-001.1: UWord, FR-005.1: PlatformWidth
-/

open ComprehensiveTests

def runUWordTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    UWord unit tests..."

  -- UWord defaults to System.Platform.numBits (64 on most systems)
  let zero := (0 : Radix.UWord)
  let one  := (1 : Radix.UWord)
  let two  := (2 : Radix.UWord)
  let max  := Radix.UWord.maxVal

  -- ## Basic value representation
  assert (zero.toNat == 0) "zero"
  assert (one.toNat == 1) "one"
  assert (two.toNat == 2) "two"

  -- ## Wrapping Arithmetic
  assert ((Radix.UWord.wrappingAdd one two).toNat == 3) "wAdd 1+2"
  assert ((Radix.UWord.wrappingAdd max one).toNat == 0) "wAdd MAX+1=0"
  assert ((Radix.UWord.wrappingAdd zero zero).toNat == 0) "wAdd 0+0"
  assert ((Radix.UWord.wrappingSub one two).toNat == max.toNat) "wSub underflow"
  assert ((Radix.UWord.wrappingSub two one).toNat == 1) "wSub 2-1"
  assert ((Radix.UWord.wrappingMul zero max).toNat == 0) "wMul 0*MAX"
  assert ((Radix.UWord.wrappingMul one max).toNat == max.toNat) "wMul 1*MAX"
  assert ((Radix.UWord.wrappingNeg zero).toNat == 0) "wNeg 0"

  -- ## Saturating Arithmetic
  assert ((Radix.UWord.saturatingAdd max one).toNat == max.toNat) "satAdd MAX+1"
  assert ((Radix.UWord.saturatingAdd one two).toNat == 3) "satAdd 1+2"
  assert ((Radix.UWord.saturatingSub zero one).toNat == 0) "satSub 0-1"
  assert ((Radix.UWord.saturatingSub two one).toNat == 1) "satSub 2-1"

  -- ## Checked Arithmetic
  assert (Radix.UWord.checkedAdd max one == none) "chkAdd MAX+1"
  assert (Radix.UWord.checkedAdd one two == some (3 : Radix.UWord)) "chkAdd 1+2"
  assert (Radix.UWord.checkedSub zero one == none) "chkSub 0-1"
  assert (Radix.UWord.checkedSub two one == some one) "chkSub 2-1"
  assert (Radix.UWord.checkedDiv one zero == none) "chkDiv /0"
  assert (Radix.UWord.checkedDiv (10 : Radix.UWord) two == some (5 : Radix.UWord)) "chkDiv 10/2"

  -- ## Overflowing Arithmetic
  let (r1, ov1) := Radix.UWord.overflowingAdd max one
  assert (r1.toNat == 0 && ov1 == true) "ovfAdd MAX+1"
  let (r2, ov2) := Radix.UWord.overflowingAdd one two
  assert (r2.toNat == 3 && ov2 == false) "ovfAdd 1+2"

  -- ## Bitwise
  assert ((Radix.UWord.bnot zero).toNat == max.toNat) "bnot 0=MAX"
  assert ((Radix.UWord.band max zero).toNat == 0) "band MAX&0"
  assert ((Radix.UWord.bor zero max).toNat == max.toNat) "bor 0|MAX"
  assert ((Radix.UWord.bxor max max).toNat == 0) "bxor MAX^MAX"

  -- ## Scan
  assert ((Radix.UWord.clz zero).toNat == System.Platform.numBits) "clz 0"
  assert ((Radix.UWord.clz one).toNat == System.Platform.numBits - 1) "clz 1"
  assert ((Radix.UWord.ctz zero).toNat == System.Platform.numBits) "ctz 0"
  assert ((Radix.UWord.ctz one).toNat == 0) "ctz 1"
  assert ((Radix.UWord.popcount zero).toNat == 0) "popcount 0"
  assert ((Radix.UWord.popcount max).toNat == System.Platform.numBits) "popcount MAX"

  -- ## Identity
  for v in [0, 1, 42, 1000000] do
    let a : Radix.UWord := ⟨BitVec.ofNat _ v⟩
    assert (Radix.UWord.wrappingAdd a zero == a) s!"identity add {v}"
    assert (Radix.UWord.wrappingMul a one == a) s!"identity mul {v}"

  c.get
