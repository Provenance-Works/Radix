import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# UInt32 Comprehensive Tests
## Spec References
- FR-001.1: UInt32, FR-001.2: Arithmetic, FR-002: Bitwise
-/

open ComprehensiveTests

def runUInt32Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    UInt32 unit tests..."

  -- ## Wrapping Arithmetic
  assert ((Radix.UInt32.wrappingAdd ⟨4000000000⟩ ⟨1000000000⟩).toNat ==
    (4000000000 + 1000000000) % 2^32) "wrappingAdd overflow"
  assert ((Radix.UInt32.wrappingAdd ⟨4294967295⟩ ⟨1⟩).toNat == 0) "wrappingAdd MAX+1=0"
  assert ((Radix.UInt32.wrappingAdd ⟨0⟩ ⟨0⟩).toNat == 0) "wrappingAdd 0+0"
  assert ((Radix.UInt32.wrappingAdd ⟨2147483648⟩ ⟨2147483648⟩).toNat == 0) "wrappingAdd half+half"
  assert ((Radix.UInt32.wrappingAdd ⟨100⟩ ⟨200⟩).toNat == 300) "wrappingAdd normal"
  assert ((Radix.UInt32.wrappingAdd ⟨42⟩ ⟨0⟩).toNat == 42) "wrappingAdd identity"

  assert ((Radix.UInt32.wrappingSub ⟨10⟩ ⟨20⟩).toNat == 4294967286) "wrappingSub underflow"
  assert ((Radix.UInt32.wrappingSub ⟨0⟩ ⟨1⟩).toNat == 4294967295) "wrappingSub 0-1"
  assert ((Radix.UInt32.wrappingSub ⟨4294967295⟩ ⟨4294967295⟩).toNat == 0) "wrappingSub MAX-MAX"
  assert ((Radix.UInt32.wrappingSub ⟨1000⟩ ⟨500⟩).toNat == 500) "wrappingSub normal"

  assert ((Radix.UInt32.wrappingMul ⟨100000⟩ ⟨100000⟩).toNat ==
    (100000 * 100000) % 2^32) "wrappingMul overflow"
  assert ((Radix.UInt32.wrappingMul ⟨4294967295⟩ ⟨0⟩).toNat == 0) "wrappingMul MAX*0"
  assert ((Radix.UInt32.wrappingMul ⟨4294967295⟩ ⟨1⟩).toNat == 4294967295) "wrappingMul MAX*1"
  assert ((Radix.UInt32.wrappingMul ⟨65536⟩ ⟨65536⟩).toNat == 0) "wrappingMul 2^16*2^16"
  assert ((Radix.UInt32.wrappingMul ⟨1000⟩ ⟨2000⟩).toNat == 2000000) "wrappingMul normal"

  assert ((Radix.UInt32.wrappingNeg ⟨0⟩).toNat == 0) "wrappingNeg 0"
  assert ((Radix.UInt32.wrappingNeg ⟨1⟩).toNat == 4294967295) "wrappingNeg 1"
  assert ((Radix.UInt32.wrappingNeg ⟨2147483648⟩).toNat == 2147483648) "wrappingNeg mid"

  -- ## Saturating Arithmetic
  assert ((Radix.UInt32.saturatingAdd ⟨4000000000⟩ ⟨1000000000⟩).toNat == 4294967295) "satAdd ovf"
  assert ((Radix.UInt32.saturatingAdd ⟨100⟩ ⟨200⟩).toNat == 300) "satAdd ok"
  assert ((Radix.UInt32.saturatingAdd ⟨4294967295⟩ ⟨4294967295⟩).toNat == 4294967295) "satAdd MAX+MAX"
  assert ((Radix.UInt32.saturatingSub ⟨10⟩ ⟨20⟩).toNat == 0) "satSub underflow"
  assert ((Radix.UInt32.saturatingSub ⟨1000⟩ ⟨500⟩).toNat == 500) "satSub ok"
  assert ((Radix.UInt32.saturatingMul ⟨100000⟩ ⟨100000⟩).toNat == 4294967295) "satMul ovf"
  assert ((Radix.UInt32.saturatingMul ⟨1000⟩ ⟨2000⟩).toNat == 2000000) "satMul ok"

  -- ## Checked Arithmetic
  assert (Radix.UInt32.checkedAdd ⟨4000000000⟩ ⟨1000000000⟩ == none) "chkAdd ovf"
  assert (Radix.UInt32.checkedAdd ⟨100⟩ ⟨200⟩ == some ⟨300⟩) "chkAdd ok"
  assert (Radix.UInt32.checkedAdd ⟨4294967295⟩ ⟨1⟩ == none) "chkAdd MAX+1"
  assert (Radix.UInt32.checkedSub ⟨10⟩ ⟨20⟩ == none) "chkSub under"
  assert (Radix.UInt32.checkedSub ⟨20⟩ ⟨10⟩ == some ⟨10⟩) "chkSub ok"
  assert (Radix.UInt32.checkedMul ⟨100000⟩ ⟨100000⟩ == none) "chkMul ovf"
  assert (Radix.UInt32.checkedMul ⟨1000⟩ ⟨2000⟩ == some ⟨2000000⟩) "chkMul ok"
  assert (Radix.UInt32.checkedDiv ⟨100⟩ ⟨0⟩ == none) "chkDiv /0"
  assert (Radix.UInt32.checkedDiv ⟨100⟩ ⟨10⟩ == some ⟨10⟩) "chkDiv ok"
  assert (Radix.UInt32.checkedRem ⟨100⟩ ⟨0⟩ == none) "chkRem /0"
  assert (Radix.UInt32.checkedRem ⟨100⟩ ⟨30⟩ == some ⟨10⟩) "chkRem ok"

  -- ## Overflowing Arithmetic
  let (r1, ov1) := Radix.UInt32.overflowingAdd ⟨4000000000⟩ ⟨1000000000⟩
  assert (ov1 == true) "ovfAdd overflow flag"
  let (r2, ov2) := Radix.UInt32.overflowingAdd ⟨100⟩ ⟨200⟩
  assert (r2.toNat == 300 && ov2 == false) "ovfAdd no overflow"
  let (r3, ov3) := Radix.UInt32.overflowingSub ⟨10⟩ ⟨20⟩
  assert (r3.toNat == 4294967286 && ov3 == true) "ovfSub underflow"
  let (_, ov4) := Radix.UInt32.overflowingMul ⟨100000⟩ ⟨100000⟩
  assert (ov4 == true) "ovfMul overflow flag"
  let (r5, ov5) := Radix.UInt32.overflowingMul ⟨1000⟩ ⟨2000⟩
  assert (r5.toNat == 2000000 && ov5 == false) "ovfMul no overflow"

  -- ## Bitwise
  assert ((Radix.UInt32.band ⟨0xFF00FF00⟩ ⟨0x0F0F0F0F⟩).toNat == 0x0F000F00) "band"
  assert ((Radix.UInt32.bor ⟨0xF0000000⟩ ⟨0x0000000F⟩).toNat == 0xF000000F) "bor"
  assert ((Radix.UInt32.bxor ⟨0xFFFFFFFF⟩ ⟨0xAAAAAAAA⟩).toNat == 0x55555555) "bxor"
  assert ((Radix.UInt32.bnot ⟨0⟩).toNat == 0xFFFFFFFF) "bnot 0"
  assert ((Radix.UInt32.bnot ⟨0xFFFFFFFF⟩).toNat == 0) "bnot MAX"
  assert ((Radix.UInt32.band ⟨0x55555555⟩ ⟨0xAAAAAAAA⟩).toNat == 0) "band alt"
  assert ((Radix.UInt32.bor ⟨0x55555555⟩ ⟨0xAAAAAAAA⟩).toNat == 0xFFFFFFFF) "bor alt"

  -- ## Shifts
  assert ((Radix.UInt32.shl ⟨1⟩ ⟨16⟩).toNat == 65536) "shl 1<<16"
  assert ((Radix.UInt32.shl ⟨1⟩ ⟨31⟩).toNat == 2147483648) "shl 1<<31"
  assert ((Radix.UInt32.shl ⟨0xFF⟩ ⟨24⟩).toNat == 0xFF000000) "shl FF<<24"
  assert ((Radix.UInt32.shrLogical ⟨0x80000000⟩ ⟨31⟩).toNat == 1) "shrL MSB>>31"
  assert ((Radix.UInt32.shrLogical ⟨256⟩ ⟨8⟩).toNat == 1) "shrL 256>>8"
  assert ((Radix.UInt32.shrArith ⟨0x80000000⟩ ⟨1⟩).toNat == 0xC0000000) "shrA sign"
  assert ((Radix.UInt32.shrArith ⟨0x40000000⟩ ⟨1⟩).toNat == 0x20000000) "shrA positive"
  assert ((Radix.UInt32.shrArith ⟨0x80000000⟩ ⟨31⟩).toNat == 0xFFFFFFFF) "shrA 80>>31"

  -- ## Scan
  assert (Radix.UInt32.clz ⟨0⟩ == 32) "clz 0"
  assert (Radix.UInt32.clz ⟨1⟩ == 31) "clz 1"
  assert (Radix.UInt32.clz ⟨0x80000000⟩ == 0) "clz MSB"
  assert (Radix.UInt32.clz ⟨256⟩ == 23) "clz 256"
  assert (Radix.UInt32.clz ⟨0xFFFFFFFF⟩ == 0) "clz MAX"
  assert (Radix.UInt32.ctz ⟨0⟩ == 32) "ctz 0"
  assert (Radix.UInt32.ctz ⟨256⟩ == 8) "ctz 256"
  assert (Radix.UInt32.ctz ⟨1⟩ == 0) "ctz 1"
  assert (Radix.UInt32.ctz ⟨0x80000000⟩ == 31) "ctz MSB"
  assert (Radix.UInt32.popcount ⟨0⟩ == 0) "popcount 0"
  assert (Radix.UInt32.popcount ⟨0xFFFFFFFF⟩ == 32) "popcount MAX"
  assert (Radix.UInt32.popcount ⟨0xAAAAAAAA⟩ == 16) "popcount AA"

  -- ## Field / Rotate / bitReverse / hamming
  assert (Radix.UInt32.testBit ⟨0x100⟩ 8 == true) "testBit"
  assert ((Radix.UInt32.setBit ⟨0⟩ 16).toNat == 65536) "setBit"
  assert ((Radix.UInt32.clearBit ⟨0xFFFFFFFF⟩ 31).toNat == 0x7FFFFFFF) "clearBit"
  assert ((Radix.UInt32.toggleBit ⟨0⟩ 0).toNat == 1) "toggleBit"
  assert ((Radix.UInt32.extractBits ⟨0x12345678⟩ 16 32 ⟨by omega, by omega⟩).toNat == 0x1234)
    "extractBits"
  assert ((Radix.UInt32.insertBits ⟨0⟩ ⟨0xFF⟩ 8 16 ⟨by omega, by omega⟩).toNat == 0xFF00)
    "insertBits"
  assert ((Radix.UInt32.rotl ⟨1⟩ ⟨1⟩).toNat == 2) "rotl"
  assert ((Radix.UInt32.rotr ⟨2⟩ ⟨1⟩).toNat == 1) "rotr"
  assert ((Radix.UInt32.rotl ⟨0xFFFFFFFF⟩ ⟨7⟩).toNat == 0xFFFFFFFF) "rotl ALL"
  assert ((Radix.UInt32.rotl ⟨0x80000001⟩ ⟨1⟩).toNat == 0x00000003) "rotl wrap"
  assert ((Radix.UInt32.bitReverse ⟨0x80000000⟩).toNat == 0x00000001) "bitReverse"
  assert ((Radix.UInt32.bitReverse ⟨0⟩).toNat == 0) "bitReverse 0"
  assert ((Radix.UInt32.bitReverse ⟨0xFFFFFFFF⟩).toNat == 0xFFFFFFFF) "bitReverse MAX"
  assert ((Radix.UInt32.hammingDistance ⟨0xFFFFFFFF⟩ ⟨0x00000000⟩).toNat == 32) "hamming"
  assert ((Radix.UInt32.hammingDistance ⟨0⟩ ⟨0⟩).toNat == 0) "hamming same"

  -- ## Power-of-2 loop
  for i in [:32] do
    let v : UInt32 := (1 <<< i.toUInt32)
    let rv : Radix.UInt32 := ⟨v⟩
    assert (Radix.UInt32.popcount rv == 1) s!"popcount 2^{i}"
    assert ((Radix.UInt32.ctz rv).toNat == i) s!"ctz 2^{i}"

  for v in [0, 1, 255, 65535, 2147483647, 2147483648, 4294967294, 4294967295] do
    let a : Radix.UInt32 := ⟨v.toUInt32⟩
    assert (Radix.UInt32.wrappingAdd a ⟨0⟩ == a) s!"identity add {v}"
    assert (Radix.UInt32.wrappingMul a ⟨1⟩ == a) s!"identity mul {v}"

  c.get
