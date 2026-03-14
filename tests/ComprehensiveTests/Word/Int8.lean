import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Word.Int
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# Int8 Comprehensive Tests
## Spec References
- FR-001.1: Signed integer types (Int8), FR-001.2: Arithmetic
- Special focus: MIN div -1 overflow, wrapping negation, signed shifts
-/

open ComprehensiveTests

def runInt8Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Int8 unit tests..."

  -- Construct common values
  let zero   := (0 : Radix.Int8)
  let one    := Radix.Int8.fromInt 1
  let negOne := Radix.Int8.fromInt (-1)
  let max    := Radix.Int8.maxVal   -- 127
  let min    := Radix.Int8.minVal   -- -128

  -- ## Value representation
  assert (zero.toInt == 0) "zero.toInt"
  assert (one.toInt == 1) "one.toInt"
  assert (negOne.toInt == -1) "negOne.toInt"
  assert (max.toInt == 127) "maxVal.toInt"
  assert (min.toInt == -128) "minVal.toInt"
  assert ((Radix.Int8.fromInt 42).toInt == 42) "fromInt 42"
  assert ((Radix.Int8.fromInt (-42)).toInt == -42) "fromInt -42"

  -- ## Wrapping Arithmetic
  -- wrappingAdd: normal
  assert ((Radix.Int8.wrappingAdd one one).toInt == 2) "wAdd 1+1=2"
  assert ((Radix.Int8.wrappingAdd (Radix.Int8.fromInt 50) (Radix.Int8.fromInt 30)).toInt == 80)
    "wAdd 50+30"
  assert ((Radix.Int8.wrappingAdd negOne one).toInt == 0) "wAdd -1+1=0"
  assert ((Radix.Int8.wrappingAdd zero zero).toInt == 0) "wAdd 0+0"
  -- wrappingAdd: positive overflow → wraps to negative
  assert ((Radix.Int8.wrappingAdd max one).toInt == -128) "wAdd MAX+1=MIN"
  assert ((Radix.Int8.wrappingAdd max max).toInt == -2) "wAdd MAX+MAX"
  -- wrappingAdd: negative overflow → wraps to positive
  assert ((Radix.Int8.wrappingAdd min negOne).toInt == 127) "wAdd MIN+(-1)=MAX"
  assert ((Radix.Int8.wrappingAdd min min).toInt == 0) "wAdd MIN+MIN=0"
  -- wrappingAdd: identity
  assert ((Radix.Int8.wrappingAdd (Radix.Int8.fromInt (-42)) zero).toInt == -42) "wAdd -42+0"

  -- wrappingSub: normal
  assert ((Radix.Int8.wrappingSub (Radix.Int8.fromInt 50) (Radix.Int8.fromInt 30)).toInt == 20)
    "wSub 50-30"
  assert ((Radix.Int8.wrappingSub zero zero).toInt == 0) "wSub 0-0"
  -- wrappingSub: overflow
  assert ((Radix.Int8.wrappingSub min one).toInt == 127) "wSub MIN-1=MAX"
  assert ((Radix.Int8.wrappingSub max negOne).toInt == -128) "wSub MAX-(-1)=MIN"
  -- wrappingSub: self
  assert ((Radix.Int8.wrappingSub max max).toInt == 0) "wSub MAX-MAX"
  assert ((Radix.Int8.wrappingSub min min).toInt == 0) "wSub MIN-MIN"

  -- wrappingMul: normal
  assert ((Radix.Int8.wrappingMul (Radix.Int8.fromInt 7) (Radix.Int8.fromInt 8)).toInt == 56)
    "wMul 7*8"
  assert ((Radix.Int8.wrappingMul negOne (Radix.Int8.fromInt 42)).toInt == -42) "wMul -1*42"
  assert ((Radix.Int8.wrappingMul negOne negOne).toInt == 1) "wMul -1*-1"
  -- wrappingMul: overflow
  assert ((Radix.Int8.wrappingMul max (Radix.Int8.fromInt 2)).toInt == -2) "wMul MAX*2"
  -- wrappingMul: identity and zero
  assert ((Radix.Int8.wrappingMul (Radix.Int8.fromInt 42) one).toInt == 42) "wMul x*1"
  assert ((Radix.Int8.wrappingMul (Radix.Int8.fromInt 42) zero).toInt == 0) "wMul x*0"

  -- wrappingNeg
  assert ((Radix.Int8.wrappingNeg zero).toInt == 0) "wNeg 0=0"
  assert ((Radix.Int8.wrappingNeg one).toInt == -1) "wNeg 1=-1"
  assert ((Radix.Int8.wrappingNeg negOne).toInt == 1) "wNeg -1=1"
  assert ((Radix.Int8.wrappingNeg max).toInt == -127) "wNeg MAX=-127"
  -- Critical: wrapping negate of MIN wraps to MIN
  assert ((Radix.Int8.wrappingNeg min).toInt == -128) "wNeg MIN=MIN"

  -- ## Saturating Arithmetic
  assert ((Radix.Int8.saturatingAdd max one).toInt == 127) "satAdd MAX+1=MAX"
  assert ((Radix.Int8.saturatingAdd min negOne).toInt == -128) "satAdd MIN+(-1)=MIN"
  assert ((Radix.Int8.saturatingAdd (Radix.Int8.fromInt 50) (Radix.Int8.fromInt 30)).toInt == 80)
    "satAdd normal"
  assert ((Radix.Int8.saturatingAdd max max).toInt == 127) "satAdd MAX+MAX=MAX"
  assert ((Radix.Int8.saturatingAdd min min).toInt == -128) "satAdd MIN+MIN=MIN"

  assert ((Radix.Int8.saturatingSub min one).toInt == -128) "satSub MIN-1=MIN"
  assert ((Radix.Int8.saturatingSub max negOne).toInt == 127) "satSub MAX-(-1)=MAX"
  assert ((Radix.Int8.saturatingSub (Radix.Int8.fromInt 50) (Radix.Int8.fromInt 30)).toInt == 20)
    "satSub normal"

  assert ((Radix.Int8.saturatingMul max (Radix.Int8.fromInt 2)).toInt == 127) "satMul MAX*2=MAX"
  assert ((Radix.Int8.saturatingMul min (Radix.Int8.fromInt 2)).toInt == -128) "satMul MIN*2=MIN"
  assert ((Radix.Int8.saturatingMul negOne (Radix.Int8.fromInt 42)).toInt == -42) "satMul -1*42"

  -- ## Checked Arithmetic
  assert (Radix.Int8.checkedAdd max one == none) "chkAdd MAX+1=none"
  assert ((Radix.Int8.checkedAdd (Radix.Int8.fromInt 50) (Radix.Int8.fromInt 30)).map
    (·.toInt) == some 80) "chkAdd 50+30"
  assert (Radix.Int8.checkedAdd min negOne == none) "chkAdd MIN+(-1)=none"
  assert ((Radix.Int8.checkedAdd zero zero).map (·.toInt) == some 0) "chkAdd 0+0"

  assert (Radix.Int8.checkedSub min one == none) "chkSub MIN-1=none"
  assert ((Radix.Int8.checkedSub (Radix.Int8.fromInt 50) (Radix.Int8.fromInt 30)).map
    (·.toInt) == some 20) "chkSub 50-30"
  assert (Radix.Int8.checkedSub max negOne == none) "chkSub MAX-(-1)=none"

  assert (Radix.Int8.checkedMul max (Radix.Int8.fromInt 2) == none) "chkMul MAX*2=none"
  assert ((Radix.Int8.checkedMul (Radix.Int8.fromInt 7) (Radix.Int8.fromInt 8)).map
    (·.toInt) == some 56) "chkMul 7*8"
  assert ((Radix.Int8.checkedMul negOne (Radix.Int8.fromInt 42)).map
    (·.toInt) == some (-42)) "chkMul -1*42"

  -- checkedDiv: div by zero
  assert (Radix.Int8.checkedDiv zero zero == none) "chkDiv 0/0=none"
  -- checkedDiv: MIN / -1 overflow
  assert (Radix.Int8.checkedDiv min negOne == none) "chkDiv MIN/(-1)=none"
  -- checkedDiv: normal
  assert ((Radix.Int8.checkedDiv (Radix.Int8.fromInt 10) (Radix.Int8.fromInt 2)).map
    (·.toInt) == some 5) "chkDiv 10/2"
  assert ((Radix.Int8.checkedDiv (Radix.Int8.fromInt (-10)) (Radix.Int8.fromInt 3)).map
    (·.toInt) == some (-3)) "chkDiv -10/3"

  -- checkedRem
  assert (Radix.Int8.checkedRem zero zero == none) "chkRem 0%0=none"
  assert ((Radix.Int8.checkedRem (Radix.Int8.fromInt 10) (Radix.Int8.fromInt 3)).map
    (·.toInt) == some 1) "chkRem 10%3"

  -- ## Overflowing Arithmetic
  let (ra1, oa1) := Radix.Int8.overflowingAdd max one
  assert (ra1.toInt == -128 && oa1 == true) "ovfAdd MAX+1"
  let (ra2, oa2) := Radix.Int8.overflowingAdd (Radix.Int8.fromInt 50) (Radix.Int8.fromInt 30)
  assert (ra2.toInt == 80 && oa2 == false) "ovfAdd 50+30"

  let (rs1, os1) := Radix.Int8.overflowingSub min one
  assert (rs1.toInt == 127 && os1 == true) "ovfSub MIN-1"
  let (rs2, os2) := Radix.Int8.overflowingSub (Radix.Int8.fromInt 50) (Radix.Int8.fromInt 30)
  assert (rs2.toInt == 20 && os2 == false) "ovfSub normal"

  let (rm1, om1) := Radix.Int8.overflowingMul max (Radix.Int8.fromInt 2)
  assert (rm1.toInt == -2 && om1 == true) "ovfMul MAX*2"
  let (rm2, om2) := Radix.Int8.overflowingMul (Radix.Int8.fromInt 7) (Radix.Int8.fromInt 8)
  assert (rm2.toInt == 56 && om2 == false) "ovfMul 7*8"

  -- ## Wrapping Div/Rem with nonzero proofs
  have hOne : one ≠ ⟨0⟩ := by decide
  have hNeg : negOne ≠ ⟨0⟩ := by decide
  have hTwo : Radix.Int8.fromInt 2 ≠ ⟨0⟩ := by decide
  have hThree : Radix.Int8.fromInt 3 ≠ ⟨0⟩ := by decide

  assert ((Radix.Int8.wrappingDiv (Radix.Int8.fromInt 10) (Radix.Int8.fromInt 2) hTwo).toInt == 5)
    "wDiv 10/2"
  -- MIN / -1 = MIN (wrapping overflow)
  assert ((Radix.Int8.wrappingDiv min negOne hNeg).toInt == -128) "wDiv MIN/(-1)=MIN"
  assert ((Radix.Int8.wrappingDiv (Radix.Int8.fromInt 10) (Radix.Int8.fromInt 3) hThree).toInt == 3)
    "wDiv 10/3"
  assert ((Radix.Int8.wrappingRem (Radix.Int8.fromInt 10) (Radix.Int8.fromInt 3) hThree).toInt == 1)
    "wRem 10%3"
  assert ((Radix.Int8.wrappingRem min one hOne).toInt == 0) "wRem MIN%1"

  -- ## Saturating Div with nonzero proof
  assert ((Radix.Int8.saturatingDiv min negOne hNeg).toInt == 127) "satDiv MIN/(-1)=MAX"
  assert ((Radix.Int8.saturatingDiv (Radix.Int8.fromInt 10) (Radix.Int8.fromInt 2) hTwo).toInt == 5)
    "satDiv 10/2"

  -- ## Bitwise on Int8
  assert ((Radix.Int8.band negOne zero).toInt == 0) "band -1&0"
  assert ((Radix.Int8.band negOne negOne).toInt == -1) "band -1&-1"
  assert ((Radix.Int8.bor zero negOne).toInt == -1) "bor 0|-1"
  assert ((Radix.Int8.bxor negOne negOne).toInt == 0) "bxor -1^-1"
  assert ((Radix.Int8.bnot zero).toInt == -1) "bnot 0=-1"
  assert ((Radix.Int8.bnot negOne).toInt == 0) "bnot -1=0"

  -- ## Scan on Int8
  assert (Radix.Int8.clz zero == 8) "clz 0"
  assert (Radix.Int8.clz one == 7) "clz 1"
  assert (Radix.Int8.clz negOne == 0) "clz -1"
  assert (Radix.Int8.clz min == 0) "clz MIN"
  assert (Radix.Int8.ctz zero == 8) "ctz 0"
  assert (Radix.Int8.ctz one == 0) "ctz 1"
  assert (Radix.Int8.ctz negOne == 0) "ctz -1"
  assert (Radix.Int8.popcount zero == 0) "popcount 0"
  assert (Radix.Int8.popcount negOne == 8) "popcount -1=8"
  assert (Radix.Int8.popcount one == 1) "popcount 1"

  -- ## Signed/Unsigned conversions
  assert ((Radix.Int8.toUInt8 zero).toNat == 0) "toUInt8 0"
  assert ((Radix.Int8.toUInt8 negOne).toNat == 255) "toUInt8 -1=255"
  assert ((Radix.Int8.toUInt8 min).toNat == 128) "toUInt8 MIN=128"
  assert ((Radix.Int8.toUInt8 max).toNat == 127) "toUInt8 MAX=127"
  assert ((Radix.Int8.fromUInt8 ⟨0⟩).toInt == 0) "fromUInt8 0"
  assert ((Radix.Int8.fromUInt8 ⟨255⟩).toInt == -1) "fromUInt8 255=-1"
  assert ((Radix.Int8.fromUInt8 ⟨128⟩).toInt == -128) "fromUInt8 128=-128"
  assert ((Radix.Int8.fromUInt8 ⟨127⟩).toInt == 127) "fromUInt8 127"

  -- ## Special values loop
  for v in [-128, -127, -1, 0, 1, 126, 127] do
    let a := Radix.Int8.fromInt v
    assert ((Radix.Int8.wrappingAdd a zero).toInt == v) s!"identity add {v}"
    assert ((Radix.Int8.wrappingMul a one).toInt == v) s!"identity mul {v}"
    assert ((Radix.Int8.wrappingSub a a).toInt == 0) s!"self sub {v}"

  c.get
