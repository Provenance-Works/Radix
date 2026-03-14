import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Word.Size
import Radix.Word.Int
import Radix.Bit.Ops
import Radix.Bit.Scan

/-!
# IWord Comprehensive Tests (platform-width signed)
## Spec References
- FR-001.1: IWord, FR-005.1: PlatformWidth
-/

open ComprehensiveTests

def runIWordTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    IWord unit tests..."

  let zero   := (0 : Radix.IWord)
  let one    := (1 : Radix.IWord)
  let negOne := Radix.IWord.fromBitVec (BitVec.ofInt System.Platform.numBits (-1))
  let max    := Radix.IWord.maxVal
  let min    := Radix.IWord.minVal

  -- ## Value representation
  assert (zero.toInt == 0) "zero"
  assert (one.toInt == 1) "one"
  assert (negOne.toInt == -1) "negOne"

  -- ## Wrapping
  assert ((Radix.IWord.wrappingAdd max one).toInt == min.toInt) "wAdd MAX+1=MIN"
  assert ((Radix.IWord.wrappingAdd min negOne).toInt == max.toInt) "wAdd MIN-1=MAX"
  assert ((Radix.IWord.wrappingAdd (100 : Radix.IWord) (200 : Radix.IWord)).toInt
    == 300) "wAdd normal"
  assert ((Radix.IWord.wrappingSub min one).toInt == max.toInt) "wSub MIN-1"
  assert ((Radix.IWord.wrappingSub max negOne).toInt == min.toInt) "wSub MAX-(-1)"
  assert ((Radix.IWord.wrappingNeg min).toInt == min.toInt) "wNeg MIN=MIN"
  assert ((Radix.IWord.wrappingNeg one).toInt == -1) "wNeg 1=-1"
  assert ((Radix.IWord.wrappingNeg zero).toInt == 0) "wNeg 0=0"

  -- ## Saturating
  assert ((Radix.IWord.saturatingAdd max one).toInt == max.toInt) "satAdd MAX+1"
  assert ((Radix.IWord.saturatingAdd min negOne).toInt == min.toInt) "satAdd MIN-1"
  assert ((Radix.IWord.saturatingSub min one).toInt == min.toInt) "satSub MIN-1"

  -- ## Checked
  assert (Radix.IWord.checkedAdd max one == none) "chkAdd MAX+1"
  assert ((Radix.IWord.checkedAdd (100 : Radix.IWord) (200 : Radix.IWord)).map
    (·.toInt) == some 300) "chkAdd normal"
  assert (Radix.IWord.checkedSub min one == none) "chkSub MIN-1"
  assert (Radix.IWord.checkedDiv zero zero == none) "chkDiv 0/0"
  assert (Radix.IWord.checkedDiv min negOne == none) "chkDiv MIN/(-1)"

  -- ## Overflowing
  let (ra, oa) := Radix.IWord.overflowingAdd max one
  assert (ra.toInt == min.toInt && oa == true) "ovfAdd MAX+1"
  let (rn, on_) := Radix.IWord.overflowingAdd (100 : Radix.IWord) (200 : Radix.IWord)
  assert (rn.toInt == 300 && on_ == false) "ovfAdd normal"

  -- ## Bitwise
  assert ((Radix.IWord.bnot zero).toInt == -1) "bnot 0"
  assert ((Radix.IWord.bnot negOne).toInt == 0) "bnot -1"
  assert ((Radix.IWord.band negOne zero).toInt == 0) "band"

  -- ## Scan
  assert ((Radix.IWord.clz zero).toInt == System.Platform.numBits) "clz 0"
  assert ((Radix.IWord.popcount negOne).toInt == System.Platform.numBits) "popcount -1"
  assert (Radix.IWord.popcount zero == 0) "popcount 0"

  -- ## Identity loop
  for v in [-42, -1, 0, 1, 42, 1000] do
    let a := Radix.IWord.fromBitVec (BitVec.ofInt System.Platform.numBits v)
    assert ((Radix.IWord.wrappingAdd a zero).toInt == v) s!"identity add {v}"
    assert ((Radix.IWord.wrappingMul a one).toInt == v) s!"identity mul {v}"

  c.get
