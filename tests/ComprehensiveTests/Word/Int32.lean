import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Word.Int
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# Int32 Comprehensive Tests
## Spec References
- FR-001.1: Int32, FR-001.2: Arithmetic
-/

open ComprehensiveTests

def runInt32Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Int32 unit tests..."

  let zero   := (0 : Radix.Int32)
  let one    := Radix.Int32.fromInt 1
  let negOne := Radix.Int32.fromInt (-1)
  let max    := Radix.Int32.maxVal
  let min    := Radix.Int32.minVal

  -- ## Value representation
  assert (max.toInt == 2147483647) "maxVal"
  assert (min.toInt == -2147483648) "minVal"
  assert (negOne.toInt == -1) "negOne"

  -- ## Wrapping
  assert ((Radix.Int32.wrappingAdd max one).toInt == -2147483648) "wAdd MAX+1=MIN"
  assert ((Radix.Int32.wrappingAdd min negOne).toInt == 2147483647) "wAdd MIN-1=MAX"
  assert ((Radix.Int32.wrappingAdd (Radix.Int32.fromInt 100000) (Radix.Int32.fromInt 200000)).toInt
    == 300000) "wAdd normal"
  assert ((Radix.Int32.wrappingSub min one).toInt == 2147483647) "wSub MIN-1"
  assert ((Radix.Int32.wrappingSub max negOne).toInt == -2147483648) "wSub MAX-(-1)"
  assert ((Radix.Int32.wrappingMul max (Radix.Int32.fromInt 2)).toInt == -2) "wMul MAX*2"
  assert ((Radix.Int32.wrappingNeg min).toInt == -2147483648) "wNeg MIN=MIN"
  assert ((Radix.Int32.wrappingNeg one).toInt == -1) "wNeg 1=-1"
  assert ((Radix.Int32.wrappingNeg zero).toInt == 0) "wNeg 0=0"

  -- ## Saturating
  assert ((Radix.Int32.saturatingAdd max one).toInt == 2147483647) "satAdd MAX+1"
  assert ((Radix.Int32.saturatingAdd min negOne).toInt == -2147483648) "satAdd MIN-1"
  assert ((Radix.Int32.saturatingSub min one).toInt == -2147483648) "satSub MIN-1"
  assert ((Radix.Int32.saturatingSub max negOne).toInt == 2147483647) "satSub MAX-(-1)"
  assert ((Radix.Int32.saturatingMul max (Radix.Int32.fromInt 2)).toInt == 2147483647) "satMul MAX*2"
  assert ((Radix.Int32.saturatingMul min (Radix.Int32.fromInt 2)).toInt == -2147483648)
    "satMul MIN*2"

  -- ## Checked
  assert (Radix.Int32.checkedAdd max one == none) "chkAdd MAX+1"
  assert (Radix.Int32.checkedAdd min negOne == none) "chkAdd MIN-1"
  assert ((Radix.Int32.checkedAdd (Radix.Int32.fromInt 1000)
    (Radix.Int32.fromInt 2000)).map (·.toInt) == some 3000) "chkAdd normal"
  assert (Radix.Int32.checkedSub min one == none) "chkSub MIN-1"
  assert (Radix.Int32.checkedMul max (Radix.Int32.fromInt 2) == none) "chkMul MAX*2"
  assert (Radix.Int32.checkedDiv zero zero == none) "chkDiv 0/0"
  assert (Radix.Int32.checkedDiv min negOne == none) "chkDiv MIN/(-1)"
  assert ((Radix.Int32.checkedDiv (Radix.Int32.fromInt 100) (Radix.Int32.fromInt 10)).map
    (·.toInt) == some 10) "chkDiv normal"
  assert (Radix.Int32.checkedRem zero zero == none) "chkRem 0/0"

  -- ## Overflowing
  let (ra, oa) := Radix.Int32.overflowingAdd max one
  assert (ra.toInt == -2147483648 && oa == true) "ovfAdd MAX+1"
  let (rs, os) := Radix.Int32.overflowingSub min one
  assert (rs.toInt == 2147483647 && os == true) "ovfSub MIN-1"
  let (rn, on_) := Radix.Int32.overflowingAdd (Radix.Int32.fromInt 100) (Radix.Int32.fromInt 200)
  assert (rn.toInt == 300 && on_ == false) "ovfAdd normal"

  -- ## Bitwise
  assert ((Radix.Int32.bnot zero).toInt == -1) "bnot 0"
  assert ((Radix.Int32.bnot negOne).toInt == 0) "bnot -1"
  assert ((Radix.Int32.band negOne zero).toInt == 0) "band"

  -- ## Scan
  assert (Radix.Int32.clz zero == 32) "clz 0"
  assert (Radix.Int32.clz one == 31) "clz 1"
  assert (Radix.Int32.popcount negOne == 32) "popcount -1"
  assert (Radix.Int32.popcount zero == 0) "popcount 0"

  -- ## Signed↔Unsigned
  assert ((Radix.Int32.toUInt32 negOne).toNat == 4294967295) "toUInt32 -1"
  assert ((Radix.Int32.toUInt32 min).toNat == 2147483648) "toUInt32 MIN"
  assert ((Radix.Int32.fromUInt32 ⟨0⟩).toInt == 0) "fromUInt32 0"
  assert ((Radix.Int32.fromUInt32 ⟨4294967295⟩).toInt == -1) "fromUInt32 MAX"

  -- ## Wrapping Div with proof
  have hTwo : Radix.Int32.fromInt 2 ≠ ⟨0⟩ := by decide
  have hNeg : negOne ≠ ⟨0⟩ := by decide
  assert ((Radix.Int32.wrappingDiv (Radix.Int32.fromInt 100) (Radix.Int32.fromInt 2) hTwo).toInt
    == 50) "wDiv 100/2"
  assert ((Radix.Int32.wrappingDiv min negOne hNeg).toInt == -2147483648) "wDiv MIN/(-1)"
  assert ((Radix.Int32.saturatingDiv min negOne hNeg).toInt == 2147483647) "satDiv MIN/(-1)=MAX"

  -- ## Identity loop
  for v in [-2147483648, -1, 0, 1, 2147483647] do
    let a := Radix.Int32.fromInt v
    assert ((Radix.Int32.wrappingAdd a zero).toInt == v) s!"identity add {v}"
    assert ((Radix.Int32.wrappingMul a one).toInt == v) s!"identity mul {v}"

  c.get
