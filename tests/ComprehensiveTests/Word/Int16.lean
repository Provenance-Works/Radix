import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Word.Int
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# Int16 Comprehensive Tests
## Spec References
- FR-001.1: Int16, FR-001.2: Arithmetic
-/

open ComprehensiveTests

def runInt16Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Int16 unit tests..."

  let zero   := (0 : Radix.Int16)
  let one    := Radix.Int16.fromInt 1
  let negOne := Radix.Int16.fromInt (-1)
  let max    := Radix.Int16.maxVal   -- 32767
  let min    := Radix.Int16.minVal   -- -32768

  -- ## Value representation
  assert (zero.toInt == 0) "zero"
  assert (one.toInt == 1) "one"
  assert (negOne.toInt == -1) "negOne"
  assert (max.toInt == 32767) "maxVal"
  assert (min.toInt == -32768) "minVal"

  -- ## Wrapping
  assert ((Radix.Int16.wrappingAdd max one).toInt == -32768) "wAdd MAX+1=MIN"
  assert ((Radix.Int16.wrappingAdd min negOne).toInt == 32767) "wAdd MIN+(-1)=MAX"
  assert ((Radix.Int16.wrappingAdd (Radix.Int16.fromInt 1000) (Radix.Int16.fromInt 2000)).toInt
    == 3000) "wAdd normal"
  assert ((Radix.Int16.wrappingSub min one).toInt == 32767) "wSub MIN-1=MAX"
  assert ((Radix.Int16.wrappingSub max negOne).toInt == -32768) "wSub MAX-(-1)=MIN"
  assert ((Radix.Int16.wrappingSub (Radix.Int16.fromInt 1000) (Radix.Int16.fromInt 500)).toInt
    == 500) "wSub normal"
  assert ((Radix.Int16.wrappingMul max (Radix.Int16.fromInt 2)).toInt == -2) "wMul MAX*2"
  assert ((Radix.Int16.wrappingMul negOne (Radix.Int16.fromInt 1000)).toInt == -1000)
    "wMul -1*1000"
  assert ((Radix.Int16.wrappingNeg min).toInt == -32768) "wNeg MIN=MIN"
  assert ((Radix.Int16.wrappingNeg one).toInt == -1) "wNeg 1=-1"
  assert ((Radix.Int16.wrappingNeg zero).toInt == 0) "wNeg 0=0"

  -- ## Saturating
  assert ((Radix.Int16.saturatingAdd max one).toInt == 32767) "satAdd MAX+1"
  assert ((Radix.Int16.saturatingAdd min negOne).toInt == -32768) "satAdd MIN-1"
  assert ((Radix.Int16.saturatingAdd (Radix.Int16.fromInt 1000) (Radix.Int16.fromInt 2000)).toInt
    == 3000) "satAdd normal"
  assert ((Radix.Int16.saturatingSub min one).toInt == -32768) "satSub MIN-1"
  assert ((Radix.Int16.saturatingSub max negOne).toInt == 32767) "satSub MAX-(-1)"
  assert ((Radix.Int16.saturatingMul max (Radix.Int16.fromInt 2)).toInt == 32767) "satMul MAX*2"
  assert ((Radix.Int16.saturatingMul min (Radix.Int16.fromInt 2)).toInt == -32768) "satMul MIN*2"

  -- ## Checked
  assert (Radix.Int16.checkedAdd max one == none) "chkAdd MAX+1"
  assert ((Radix.Int16.checkedAdd (Radix.Int16.fromInt 100) (Radix.Int16.fromInt 200)).map
    (·.toInt) == some 300) "chkAdd normal"
  assert (Radix.Int16.checkedSub min one == none) "chkSub MIN-1"
  assert ((Radix.Int16.checkedSub (Radix.Int16.fromInt 500) (Radix.Int16.fromInt 200)).map
    (·.toInt) == some 300) "chkSub normal"
  assert (Radix.Int16.checkedMul max (Radix.Int16.fromInt 2) == none) "chkMul MAX*2"
  assert (Radix.Int16.checkedDiv min negOne == none) "chkDiv MIN/(-1)"
  assert (Radix.Int16.checkedDiv zero zero == none) "chkDiv 0/0"
  assert ((Radix.Int16.checkedDiv (Radix.Int16.fromInt 100) (Radix.Int16.fromInt 10)).map
    (·.toInt) == some 10) "chkDiv normal"
  assert (Radix.Int16.checkedRem zero zero == none) "chkRem 0%0"
  assert ((Radix.Int16.checkedRem (Radix.Int16.fromInt 100) (Radix.Int16.fromInt 30)).map
    (·.toInt) == some 10) "chkRem normal"

  -- ## Overflowing
  let (ra, oa) := Radix.Int16.overflowingAdd max one
  assert (ra.toInt == -32768 && oa == true) "ovfAdd MAX+1"
  let (rs, os) := Radix.Int16.overflowingSub min one
  assert (rs.toInt == 32767 && os == true) "ovfSub MIN-1"
  let (rm, om) := Radix.Int16.overflowingMul max (Radix.Int16.fromInt 2)
  assert (rm.toInt == -2 && om == true) "ovfMul MAX*2"
  let (rn, on_) := Radix.Int16.overflowingAdd (Radix.Int16.fromInt 100) (Radix.Int16.fromInt 200)
  assert (rn.toInt == 300 && on_ == false) "ovfAdd normal"

  -- ## Bitwise
  assert ((Radix.Int16.bnot zero).toInt == -1) "bnot 0"
  assert ((Radix.Int16.bnot negOne).toInt == 0) "bnot -1"
  assert ((Radix.Int16.band negOne zero).toInt == 0) "band"
  assert ((Radix.Int16.bor zero negOne).toInt == -1) "bor"

  -- ## Scan
  assert (Radix.Int16.clz zero == 16) "clz 0"
  assert (Radix.Int16.clz one == 15) "clz 1"
  assert (Radix.Int16.clz negOne == 0) "clz -1"
  assert (Radix.Int16.popcount zero == 0) "popcount 0"
  assert (Radix.Int16.popcount negOne == 16) "popcount -1"

  -- ## Signed↔Unsigned
  assert ((Radix.Int16.toUInt16 negOne).toNat == 65535) "toUInt16 -1"
  assert ((Radix.Int16.toUInt16 min).toNat == 32768) "toUInt16 MIN"
  assert ((Radix.Int16.fromUInt16 ⟨0⟩).toInt == 0) "fromUInt16 0"
  assert ((Radix.Int16.fromUInt16 ⟨65535⟩).toInt == -1) "fromUInt16 65535"

  -- ## Identity loop
  for v in [-32768, -32767, -1, 0, 1, 32766, 32767] do
    let a := Radix.Int16.fromInt v
    assert ((Radix.Int16.wrappingAdd a zero).toInt == v) s!"identity add {v}"
    assert ((Radix.Int16.wrappingMul a one).toInt == v) s!"identity mul {v}"
    assert ((Radix.Int16.wrappingSub a a).toInt == 0) s!"self sub {v}"

  c.get
