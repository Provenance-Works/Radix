import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# UInt64 Comprehensive Tests
## Spec References
- FR-001.1: UInt64, FR-001.2: Arithmetic, FR-002: Bitwise
-/

open ComprehensiveTests

def runUInt64Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    UInt64 unit tests..."

  -- ## Wrapping Arithmetic
  assert ((Radix.UInt64.wrappingAdd ⟨18000000000000000000⟩ ⟨2000000000000000000⟩).toNat ==
    (18000000000000000000 + 2000000000000000000) % 2^64) "wrappingAdd overflow"
  assert ((Radix.UInt64.wrappingAdd ⟨18446744073709551615⟩ ⟨1⟩).toNat == 0) "wrappingAdd MAX+1=0"
  assert ((Radix.UInt64.wrappingAdd ⟨0⟩ ⟨0⟩).toNat == 0) "wrappingAdd 0+0"
  assert ((Radix.UInt64.wrappingAdd ⟨9223372036854775808⟩ ⟨9223372036854775808⟩).toNat == 0)
    "wrappingAdd half+half"
  assert ((Radix.UInt64.wrappingAdd ⟨1000⟩ ⟨2000⟩).toNat == 3000) "wrappingAdd normal"
  assert ((Radix.UInt64.wrappingAdd ⟨42⟩ ⟨0⟩).toNat == 42) "wrappingAdd identity"

  assert ((Radix.UInt64.wrappingSub ⟨10⟩ ⟨20⟩).toNat == 18446744073709551606) "wrappingSub under"
  assert ((Radix.UInt64.wrappingSub ⟨0⟩ ⟨1⟩).toNat == 18446744073709551615) "wrappingSub 0-1"
  assert ((Radix.UInt64.wrappingSub ⟨1000⟩ ⟨500⟩).toNat == 500) "wrappingSub normal"

  assert ((Radix.UInt64.wrappingMul ⟨18446744073709551615⟩ ⟨0⟩).toNat == 0) "wrappingMul MAX*0"
  assert ((Radix.UInt64.wrappingMul ⟨18446744073709551615⟩ ⟨1⟩).toNat ==
    18446744073709551615) "wrappingMul MAX*1"
  assert ((Radix.UInt64.wrappingMul ⟨1000000⟩ ⟨2000000⟩).toNat == 2000000000000) "wrappingMul ok"
  assert ((Radix.UInt64.wrappingMul ⟨4294967296⟩ ⟨4294967296⟩).toNat == 0) "wrappingMul 2^32*2^32"

  assert ((Radix.UInt64.wrappingNeg ⟨0⟩).toNat == 0) "wrappingNeg 0"
  assert ((Radix.UInt64.wrappingNeg ⟨1⟩).toNat == 18446744073709551615) "wrappingNeg 1"

  -- ## Saturating Arithmetic
  assert ((Radix.UInt64.saturatingAdd ⟨18446744073709551615⟩ ⟨1⟩).toNat ==
    18446744073709551615) "satAdd MAX+1"
  assert ((Radix.UInt64.saturatingAdd ⟨100⟩ ⟨200⟩).toNat == 300) "satAdd ok"
  assert ((Radix.UInt64.saturatingSub ⟨10⟩ ⟨20⟩).toNat == 0) "satSub under"
  assert ((Radix.UInt64.saturatingSub ⟨1000⟩ ⟨500⟩).toNat == 500) "satSub ok"
  assert ((Radix.UInt64.saturatingMul ⟨18446744073709551615⟩ ⟨2⟩).toNat ==
    18446744073709551615) "satMul ovf"
  assert ((Radix.UInt64.saturatingMul ⟨1000⟩ ⟨2000⟩).toNat == 2000000) "satMul ok"

  -- ## Checked Arithmetic
  assert (Radix.UInt64.checkedAdd ⟨18446744073709551615⟩ ⟨1⟩ == none) "chkAdd MAX+1"
  assert (Radix.UInt64.checkedAdd ⟨100⟩ ⟨200⟩ == some ⟨300⟩) "chkAdd ok"
  assert (Radix.UInt64.checkedSub ⟨10⟩ ⟨20⟩ == none) "chkSub under"
  assert (Radix.UInt64.checkedSub ⟨20⟩ ⟨10⟩ == some ⟨10⟩) "chkSub ok"
  assert (Radix.UInt64.checkedMul ⟨18446744073709551615⟩ ⟨2⟩ == none) "chkMul ovf"
  assert (Radix.UInt64.checkedMul ⟨1000⟩ ⟨2000⟩ == some ⟨2000000⟩) "chkMul ok"
  assert (Radix.UInt64.checkedDiv ⟨100⟩ ⟨0⟩ == none) "chkDiv /0"
  assert (Radix.UInt64.checkedDiv ⟨100⟩ ⟨10⟩ == some ⟨10⟩) "chkDiv ok"
  assert (Radix.UInt64.checkedRem ⟨100⟩ ⟨0⟩ == none) "chkRem /0"
  assert (Radix.UInt64.checkedRem ⟨100⟩ ⟨30⟩ == some ⟨10⟩) "chkRem ok"

  -- ## Overflowing Arithmetic
  let (r1, ov1) := Radix.UInt64.overflowingAdd ⟨18446744073709551615⟩ ⟨1⟩
  assert (r1.toNat == 0 && ov1 == true) "ovfAdd MAX+1"
  let (r2, ov2) := Radix.UInt64.overflowingAdd ⟨100⟩ ⟨200⟩
  assert (r2.toNat == 300 && ov2 == false) "ovfAdd ok"
  let (r3, ov3) := Radix.UInt64.overflowingSub ⟨10⟩ ⟨20⟩
  assert (ov3 == true) "ovfSub under flag"
  let (r4, ov4) := Radix.UInt64.overflowingMul ⟨4294967296⟩ ⟨4294967296⟩
  assert (r4.toNat == 0 && ov4 == true) "ovfMul 2^32*2^32"
  let (r5, ov5) := Radix.UInt64.overflowingMul ⟨1000⟩ ⟨2000⟩
  assert (r5.toNat == 2000000 && ov5 == false) "ovfMul ok"

  -- ## Bitwise
  assert ((Radix.UInt64.band ⟨0xFF00FF00FF00FF00⟩ ⟨0x0F0F0F0F0F0F0F0F⟩).toNat ==
    0x0F000F000F000F00) "band"
  assert ((Radix.UInt64.bor ⟨0xF000000000000000⟩ ⟨0x000000000000000F⟩).toNat ==
    0xF00000000000000F) "bor"
  assert ((Radix.UInt64.bxor ⟨0xFFFFFFFFFFFFFFFF⟩ ⟨0xAAAAAAAAAAAAAAAA⟩).toNat ==
    0x5555555555555555) "bxor"
  assert ((Radix.UInt64.bnot ⟨0⟩).toNat == 0xFFFFFFFFFFFFFFFF) "bnot 0"
  assert ((Radix.UInt64.bnot ⟨0xFFFFFFFFFFFFFFFF⟩).toNat == 0) "bnot MAX"

  -- ## Shifts
  assert ((Radix.UInt64.shl ⟨1⟩ ⟨32⟩).toNat == 4294967296) "shl 1<<32"
  assert ((Radix.UInt64.shl ⟨1⟩ ⟨63⟩).toNat == 9223372036854775808) "shl 1<<63"
  assert ((Radix.UInt64.shrLogical ⟨0x8000000000000000⟩ ⟨63⟩).toNat == 1) "shrL MSB>>63"
  assert ((Radix.UInt64.shrArith ⟨0x8000000000000000⟩ ⟨1⟩).toNat ==
    0xC000000000000000) "shrA sign"
  assert ((Radix.UInt64.shrArith ⟨0x4000000000000000⟩ ⟨1⟩).toNat ==
    0x2000000000000000) "shrA pos"

  -- ## Scan
  assert (Radix.UInt64.clz ⟨0⟩ == 64) "clz 0"
  assert (Radix.UInt64.clz ⟨1⟩ == 63) "clz 1"
  assert (Radix.UInt64.clz ⟨0x8000000000000000⟩ == 0) "clz MSB"
  assert (Radix.UInt64.ctz ⟨0⟩ == 64) "ctz 0"
  assert (Radix.UInt64.ctz ⟨1⟩ == 0) "ctz 1"
  assert (Radix.UInt64.ctz ⟨0x8000000000000000⟩ == 63) "ctz MSB"
  assert (Radix.UInt64.popcount ⟨0⟩ == 0) "popcount 0"
  assert (Radix.UInt64.popcount ⟨0xFFFFFFFFFFFFFFFF⟩ == 64) "popcount MAX"
  assert (Radix.UInt64.popcount ⟨0xAAAAAAAAAAAAAAAA⟩ == 32) "popcount AA"

  -- ## Field / Rotate / bitReverse / hamming
  assert (Radix.UInt64.testBit ⟨0x100⟩ 8 == true) "testBit"
  assert ((Radix.UInt64.setBit ⟨0⟩ 32).toNat == 4294967296) "setBit"
  assert ((Radix.UInt64.clearBit ⟨0xFFFFFFFFFFFFFFFF⟩ 63).toNat ==
    0x7FFFFFFFFFFFFFFF) "clearBit"
  assert ((Radix.UInt64.toggleBit ⟨0⟩ 0).toNat == 1) "toggleBit"
  assert ((Radix.UInt64.rotl ⟨1⟩ ⟨1⟩).toNat == 2) "rotl"
  assert ((Radix.UInt64.rotr ⟨2⟩ ⟨1⟩).toNat == 1) "rotr"
  assert ((Radix.UInt64.rotl ⟨0x8000000000000001⟩ ⟨1⟩).toNat == 0x0000000000000003) "rotl wrap"
  assert ((Radix.UInt64.bitReverse ⟨0x8000000000000000⟩).toNat == 0x0000000000000001) "bitReverse"
  assert ((Radix.UInt64.bitReverse ⟨0⟩).toNat == 0) "bitReverse 0"
  assert ((Radix.UInt64.bitReverse ⟨0xFFFFFFFFFFFFFFFF⟩).toNat ==
    0xFFFFFFFFFFFFFFFF) "bitReverse MAX"
  assert ((Radix.UInt64.hammingDistance ⟨0xFFFFFFFFFFFFFFFF⟩ ⟨0⟩).toNat == 64) "hamming"
  assert ((Radix.UInt64.hammingDistance ⟨0⟩ ⟨0⟩).toNat == 0) "hamming same"

  -- ## Power-of-2 loop
  for i in [:64] do
    let v : UInt64 := (1 <<< i.toUInt64)
    let rv : Radix.UInt64 := ⟨v⟩
    assert (Radix.UInt64.popcount rv == 1) s!"popcount 2^{i}"
    assert ((Radix.UInt64.ctz rv).toNat == i) s!"ctz 2^{i}"

  for v in [0, 1, 255, 65535, 4294967295, 9223372036854775807, 18446744073709551615] do
    let a : Radix.UInt64 := ⟨v.toUInt64⟩
    assert (Radix.UInt64.wrappingAdd a ⟨0⟩ == a) s!"identity add"
    assert (Radix.UInt64.wrappingMul a ⟨1⟩ == a) s!"identity mul"

  c.get
