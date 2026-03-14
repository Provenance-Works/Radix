import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Word.Int
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# Int64 Comprehensive Tests
## Spec References
- FR-001.1: Int64, FR-001.2: Arithmetic
-/

open ComprehensiveTests

def runInt64Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Int64 unit tests..."

  let zero   := (0 : Radix.Int64)
  let one    := Radix.Int64.fromInt 1
  let negOne := Radix.Int64.fromInt (-1)
  let max    := Radix.Int64.maxVal
  let min    := Radix.Int64.minVal

  -- ## Value representation
  assert (max.toInt == 9223372036854775807) "maxVal"
  assert (min.toInt == -9223372036854775808) "minVal"
  assert (negOne.toInt == -1) "negOne"

  -- ## Wrapping
  assert ((Radix.Int64.wrappingAdd max one).toInt == -9223372036854775808) "wAdd MAX+1=MIN"
  assert ((Radix.Int64.wrappingAdd min negOne).toInt == 9223372036854775807) "wAdd MIN-1=MAX"
  assert ((Radix.Int64.wrappingAdd (Radix.Int64.fromInt 100000) (Radix.Int64.fromInt 200000)).toInt
    == 300000) "wAdd normal"
  assert ((Radix.Int64.wrappingSub min one).toInt == 9223372036854775807) "wSub MIN-1"
  assert ((Radix.Int64.wrappingSub max negOne).toInt == -9223372036854775808) "wSub MAX-(-1)"
  assert ((Radix.Int64.wrappingMul max (Radix.Int64.fromInt 2)).toInt == -2) "wMul MAX*2"
  assert ((Radix.Int64.wrappingNeg min).toInt == -9223372036854775808) "wNeg MIN=MIN"
  assert ((Radix.Int64.wrappingNeg one).toInt == -1) "wNeg 1=-1"
  assert ((Radix.Int64.wrappingNeg zero).toInt == 0) "wNeg 0=0"

  -- ## Saturating
  assert ((Radix.Int64.saturatingAdd max one).toInt == 9223372036854775807) "satAdd MAX+1"
  assert ((Radix.Int64.saturatingAdd min negOne).toInt == -9223372036854775808) "satAdd MIN-1"
  assert ((Radix.Int64.saturatingSub min one).toInt == -9223372036854775808) "satSub MIN-1"
  assert ((Radix.Int64.saturatingSub max negOne).toInt == 9223372036854775807) "satSub MAX-(-1)"
  assert ((Radix.Int64.saturatingMul max (Radix.Int64.fromInt 2)).toInt ==
    9223372036854775807) "satMul MAX*2"

  -- ## Checked
  assert (Radix.Int64.checkedAdd max one == none) "chkAdd MAX+1"
  assert (Radix.Int64.checkedAdd min negOne == none) "chkAdd MIN-1"
  assert ((Radix.Int64.checkedAdd (Radix.Int64.fromInt 1000)
    (Radix.Int64.fromInt 2000)).map (·.toInt) == some 3000) "chkAdd normal"
  assert (Radix.Int64.checkedSub min one == none) "chkSub MIN-1"
  assert (Radix.Int64.checkedMul max (Radix.Int64.fromInt 2) == none) "chkMul MAX*2"
  assert (Radix.Int64.checkedDiv zero zero == none) "chkDiv 0/0"
  assert (Radix.Int64.checkedDiv min negOne == none) "chkDiv MIN/(-1)"
  assert ((Radix.Int64.checkedDiv (Radix.Int64.fromInt 100) (Radix.Int64.fromInt 10)).map
    (·.toInt) == some 10) "chkDiv normal"

  -- ## Overflowing
  let (ra, oa) := Radix.Int64.overflowingAdd max one
  assert (ra.toInt == -9223372036854775808 && oa == true) "ovfAdd MAX+1"
  let (rs, os) := Radix.Int64.overflowingSub min one
  assert (rs.toInt == 9223372036854775807 && os == true) "ovfSub MIN-1"
  let (rn, on_) := Radix.Int64.overflowingAdd (Radix.Int64.fromInt 100) (Radix.Int64.fromInt 200)
  assert (rn.toInt == 300 && on_ == false) "ovfAdd normal"

  -- ## Bitwise
  assert ((Radix.Int64.bnot zero).toInt == -1) "bnot 0"
  assert ((Radix.Int64.bnot negOne).toInt == 0) "bnot -1"
  assert ((Radix.Int64.band negOne zero).toInt == 0) "band"

  -- ## Scan
  assert (Radix.Int64.clz zero == 64) "clz 0"
  assert (Radix.Int64.clz one == 63) "clz 1"
  assert (Radix.Int64.popcount negOne == 64) "popcount -1"
  assert (Radix.Int64.popcount zero == 0) "popcount 0"

  -- ## Signed↔Unsigned
  assert ((Radix.Int64.toUInt64 negOne).toNat == 18446744073709551615) "toUInt64 -1"
  assert ((Radix.Int64.toUInt64 min).toNat == 9223372036854775808) "toUInt64 MIN"
  assert ((Radix.Int64.fromUInt64 ⟨0⟩).toInt == 0) "fromUInt64 0"
  assert ((Radix.Int64.fromUInt64 ⟨18446744073709551615⟩).toInt == -1) "fromUInt64 MAX"

  -- ## Div with proof
  have hTwo : Radix.Int64.fromInt 2 ≠ ⟨0⟩ := by decide
  have hNeg : negOne ≠ ⟨0⟩ := by decide
  assert ((Radix.Int64.wrappingDiv (Radix.Int64.fromInt 100) (Radix.Int64.fromInt 2) hTwo).toInt
    == 50) "wDiv 100/2"
  assert ((Radix.Int64.wrappingDiv min negOne hNeg).toInt ==
    -9223372036854775808) "wDiv MIN/(-1)"
  assert ((Radix.Int64.saturatingDiv min negOne hNeg).toInt ==
    9223372036854775807) "satDiv MIN/(-1)"

  -- ## Identity loop
  for v in [-9223372036854775808, -1, 0, 1, 9223372036854775807] do
    let a := Radix.Int64.fromInt v
    assert ((Radix.Int64.wrappingAdd a zero).toInt == v) s!"identity add"
    assert ((Radix.Int64.wrappingMul a one).toInt == v) s!"identity mul"

  c.get
