import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# UInt16 Comprehensive Tests

Exhaustive unit tests for all Radix.UInt16 operations.

## Spec References
- FR-001.1: Unsigned integer types (UInt16)
- FR-001.2: Arithmetic operations
- FR-002: Bitwise operations
-/

open ComprehensiveTests

def runUInt16Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    UInt16 unit tests..."

  -- ## Wrapping Arithmetic
  assert ((Radix.UInt16.wrappingAdd ⟨1000⟩ ⟨2000⟩).toNat == 3000) "wrappingAdd 1000+2000"
  assert ((Radix.UInt16.wrappingAdd ⟨60000⟩ ⟨10000⟩).toNat == 4464) "wrappingAdd overflow"
  assert ((Radix.UInt16.wrappingAdd ⟨65535⟩ ⟨1⟩).toNat == 0) "wrappingAdd MAX+1=0"
  assert ((Radix.UInt16.wrappingAdd ⟨0⟩ ⟨0⟩).toNat == 0) "wrappingAdd 0+0"
  assert ((Radix.UInt16.wrappingAdd ⟨32768⟩ ⟨32768⟩).toNat == 0) "wrappingAdd half+half"
  assert ((Radix.UInt16.wrappingAdd ⟨42⟩ ⟨0⟩).toNat == 42) "wrappingAdd identity"
  assert ((Radix.UInt16.wrappingAdd ⟨65534⟩ ⟨1⟩).toNat == 65535) "wrappingAdd MAX-1+1"
  assert ((Radix.UInt16.wrappingAdd ⟨65535⟩ ⟨65535⟩).toNat == 65534) "wrappingAdd MAX+MAX"

  assert ((Radix.UInt16.wrappingSub ⟨10⟩ ⟨20⟩).toNat == 65526) "wrappingSub underflow"
  assert ((Radix.UInt16.wrappingSub ⟨0⟩ ⟨1⟩).toNat == 65535) "wrappingSub 0-1"
  assert ((Radix.UInt16.wrappingSub ⟨65535⟩ ⟨65535⟩).toNat == 0) "wrappingSub MAX-MAX"
  assert ((Radix.UInt16.wrappingSub ⟨1000⟩ ⟨500⟩).toNat == 500) "wrappingSub normal"
  assert ((Radix.UInt16.wrappingSub ⟨65535⟩ ⟨0⟩).toNat == 65535) "wrappingSub MAX-0"

  assert ((Radix.UInt16.wrappingMul ⟨1000⟩ ⟨100⟩).toNat == 34464) "wrappingMul overflow"
  assert ((Radix.UInt16.wrappingMul ⟨200⟩ ⟨300⟩).toNat == 60000) "wrappingMul normal"
  assert ((Radix.UInt16.wrappingMul ⟨65535⟩ ⟨0⟩).toNat == 0) "wrappingMul MAX*0"
  assert ((Radix.UInt16.wrappingMul ⟨65535⟩ ⟨1⟩).toNat == 65535) "wrappingMul MAX*1"
  assert ((Radix.UInt16.wrappingMul ⟨256⟩ ⟨256⟩).toNat == 0) "wrappingMul 256*256=0"

  assert ((Radix.UInt16.wrappingNeg ⟨0⟩).toNat == 0) "wrappingNeg 0"
  assert ((Radix.UInt16.wrappingNeg ⟨1⟩).toNat == 65535) "wrappingNeg 1"
  assert ((Radix.UInt16.wrappingNeg ⟨32768⟩).toNat == 32768) "wrappingNeg mid"

  -- ## Saturating Arithmetic
  assert ((Radix.UInt16.saturatingAdd ⟨60000⟩ ⟨10000⟩).toNat == 65535) "satAdd overflow"
  assert ((Radix.UInt16.saturatingAdd ⟨100⟩ ⟨200⟩).toNat == 300) "satAdd normal"
  assert ((Radix.UInt16.saturatingAdd ⟨65535⟩ ⟨65535⟩).toNat == 65535) "satAdd MAX+MAX"
  assert ((Radix.UInt16.saturatingAdd ⟨0⟩ ⟨0⟩).toNat == 0) "satAdd 0+0"
  assert ((Radix.UInt16.saturatingSub ⟨10⟩ ⟨20⟩).toNat == 0) "satSub underflow"
  assert ((Radix.UInt16.saturatingSub ⟨0⟩ ⟨65535⟩).toNat == 0) "satSub 0-MAX"
  assert ((Radix.UInt16.saturatingSub ⟨1000⟩ ⟨500⟩).toNat == 500) "satSub normal"
  assert ((Radix.UInt16.saturatingMul ⟨1000⟩ ⟨100⟩).toNat == 65535) "satMul overflow"
  assert ((Radix.UInt16.saturatingMul ⟨100⟩ ⟨100⟩).toNat == 10000) "satMul normal"
  assert ((Radix.UInt16.saturatingMul ⟨0⟩ ⟨65535⟩).toNat == 0) "satMul zero"

  -- ## Checked Arithmetic
  assert (Radix.UInt16.checkedAdd ⟨60000⟩ ⟨10000⟩ == none) "chkAdd overflow"
  assert (Radix.UInt16.checkedAdd ⟨100⟩ ⟨200⟩ == some ⟨300⟩) "chkAdd ok"
  assert (Radix.UInt16.checkedAdd ⟨65535⟩ ⟨0⟩ == some ⟨65535⟩) "chkAdd MAX+0"
  assert (Radix.UInt16.checkedAdd ⟨65535⟩ ⟨1⟩ == none) "chkAdd MAX+1"
  assert (Radix.UInt16.checkedSub ⟨10⟩ ⟨20⟩ == none) "chkSub underflow"
  assert (Radix.UInt16.checkedSub ⟨20⟩ ⟨10⟩ == some ⟨10⟩) "chkSub ok"
  assert (Radix.UInt16.checkedSub ⟨0⟩ ⟨1⟩ == none) "chkSub 0-1"
  assert (Radix.UInt16.checkedMul ⟨60000⟩ ⟨2⟩ == none) "chkMul overflow"
  assert (Radix.UInt16.checkedMul ⟨100⟩ ⟨200⟩ == some ⟨20000⟩) "chkMul ok"
  assert (Radix.UInt16.checkedDiv ⟨100⟩ ⟨0⟩ == none) "chkDiv /0"
  assert (Radix.UInt16.checkedDiv ⟨100⟩ ⟨10⟩ == some ⟨10⟩) "chkDiv ok"
  assert (Radix.UInt16.checkedDiv ⟨65535⟩ ⟨1⟩ == some ⟨65535⟩) "chkDiv MAX/1"
  assert (Radix.UInt16.checkedRem ⟨100⟩ ⟨0⟩ == none) "chkRem /0"
  assert (Radix.UInt16.checkedRem ⟨100⟩ ⟨30⟩ == some ⟨10⟩) "chkRem 100%30"

  -- ## Overflowing Arithmetic
  let (r1, ov1) := Radix.UInt16.overflowingAdd ⟨60000⟩ ⟨10000⟩
  assert (r1.toNat == 4464 && ov1 == true) "ovfAdd overflow"
  let (r2, ov2) := Radix.UInt16.overflowingAdd ⟨100⟩ ⟨200⟩
  assert (r2.toNat == 300 && ov2 == false) "ovfAdd ok"
  let (r3, ov3) := Radix.UInt16.overflowingSub ⟨10⟩ ⟨20⟩
  assert (r3.toNat == 65526 && ov3 == true) "ovfSub underflow"
  let (r4, ov4) := Radix.UInt16.overflowingSub ⟨20⟩ ⟨10⟩
  assert (r4.toNat == 10 && ov4 == false) "ovfSub ok"
  let (r5, ov5) := Radix.UInt16.overflowingMul ⟨1000⟩ ⟨100⟩
  assert (r5.toNat == 34464 && ov5 == true) "ovfMul overflow"
  let (r6, ov6) := Radix.UInt16.overflowingMul ⟨100⟩ ⟨100⟩
  assert (r6.toNat == 10000 && ov6 == false) "ovfMul ok"

  -- ## Bitwise
  assert ((Radix.UInt16.band ⟨0xFF00⟩ ⟨0x0FF0⟩).toNat == 0x0F00) "band"
  assert ((Radix.UInt16.bor ⟨0xF000⟩ ⟨0x00FF⟩).toNat == 0xF0FF) "bor"
  assert ((Radix.UInt16.bxor ⟨0xFFFF⟩ ⟨0xAAAA⟩).toNat == 0x5555) "bxor"
  assert ((Radix.UInt16.bnot ⟨0x0000⟩).toNat == 0xFFFF) "bnot 0"
  assert ((Radix.UInt16.bnot ⟨0xFFFF⟩).toNat == 0x0000) "bnot MAX"
  assert ((Radix.UInt16.bnot ⟨0x00FF⟩).toNat == 0xFF00) "bnot 00FF"
  assert ((Radix.UInt16.band ⟨0x5555⟩ ⟨0xAAAA⟩).toNat == 0x0000) "band alt"
  assert ((Radix.UInt16.bor ⟨0x5555⟩ ⟨0xAAAA⟩).toNat == 0xFFFF) "bor alt"

  -- ## Shifts
  assert ((Radix.UInt16.shl ⟨1⟩ ⟨8⟩).toNat == 256) "shl 1<<8"
  assert ((Radix.UInt16.shl ⟨1⟩ ⟨15⟩).toNat == 32768) "shl 1<<15"
  assert ((Radix.UInt16.shl ⟨0xFF⟩ ⟨8⟩).toNat == 0xFF00) "shl FF<<8"
  assert ((Radix.UInt16.shrLogical ⟨256⟩ ⟨4⟩).toNat == 16) "shrL 256>>4"
  assert ((Radix.UInt16.shrLogical ⟨0x8000⟩ ⟨15⟩).toNat == 1) "shrL MSB>>15"
  assert ((Radix.UInt16.shrArith ⟨0x8000⟩ ⟨1⟩).toNat == 0xC000) "shrA sign ext"
  assert ((Radix.UInt16.shrArith ⟨0x4000⟩ ⟨1⟩).toNat == 0x2000) "shrA positive"

  -- ## Scan
  assert (Radix.UInt16.clz ⟨0⟩ == 16) "clz 0"
  assert (Radix.UInt16.clz ⟨1⟩ == 15) "clz 1"
  assert (Radix.UInt16.clz ⟨0x8000⟩ == 0) "clz MSB"
  assert (Radix.UInt16.clz ⟨0x100⟩ == 7) "clz 0x100"
  assert (Radix.UInt16.ctz ⟨0⟩ == 16) "ctz 0"
  assert (Radix.UInt16.ctz ⟨16⟩ == 4) "ctz 16"
  assert (Radix.UInt16.ctz ⟨0x8000⟩ == 15) "ctz MSB"
  assert (Radix.UInt16.popcount ⟨0⟩ == 0) "popcount 0"
  assert (Radix.UInt16.popcount ⟨0xFFFF⟩ == 16) "popcount MAX"
  assert (Radix.UInt16.popcount ⟨0xAAAA⟩ == 8) "popcount AA"
  assert (Radix.UInt16.popcount ⟨0x5555⟩ == 8) "popcount 55"
  assert (Radix.UInt16.popcount ⟨0x0001⟩ == 1) "popcount 1"

  -- ## Field
  assert (Radix.UInt16.testBit ⟨0x100⟩ 8 == true) "testBit 100[8]"
  assert (Radix.UInt16.testBit ⟨0x100⟩ 7 == false) "testBit 100[7]"
  assert ((Radix.UInt16.setBit ⟨0⟩ 8).toNat == 256) "setBit 0[8]"
  assert ((Radix.UInt16.setBit ⟨0⟩ 15).toNat == 32768) "setBit 0[15]"
  assert ((Radix.UInt16.clearBit ⟨0xFFFF⟩ 0).toNat == 0xFFFE) "clearBit FF[0]"
  assert ((Radix.UInt16.clearBit ⟨0xFFFF⟩ 15).toNat == 0x7FFF) "clearBit FF[15]"
  assert ((Radix.UInt16.toggleBit ⟨0⟩ 8).toNat == 256) "toggleBit 0[8]"
  assert ((Radix.UInt16.toggleBit ⟨256⟩ 8).toNat == 0) "toggleBit 100[8]"

  -- extractBits / insertBits
  assert ((Radix.UInt16.extractBits ⟨0xABCD⟩ 8 16 ⟨by omega, by omega⟩).toNat == 0xAB)
    "extractBits"
  assert ((Radix.UInt16.insertBits ⟨0x00⟩ ⟨0xFF⟩ 8 16 ⟨by omega, by omega⟩).toNat == 0xFF00)
    "insertBits"

  -- ## Rotate, bitReverse, hamming
  assert ((Radix.UInt16.rotl ⟨1⟩ ⟨4⟩).toNat == 16) "rotl"
  assert ((Radix.UInt16.rotr ⟨0x8001⟩ ⟨1⟩).toNat == 0xC000) "rotr"
  assert ((Radix.UInt16.rotl ⟨0xFFFF⟩ ⟨5⟩).toNat == 0xFFFF) "rotl ALL"
  assert ((Radix.UInt16.bitReverse ⟨0x8000⟩).toNat == 0x0001) "bitReverse 8000"
  assert ((Radix.UInt16.bitReverse ⟨0x0001⟩).toNat == 0x8000) "bitReverse 0001"
  assert ((Radix.UInt16.bitReverse ⟨0xFFFF⟩).toNat == 0xFFFF) "bitReverse FFFF"
  assert ((Radix.UInt16.bitReverse ⟨0x0000⟩).toNat == 0x0000) "bitReverse 0000"
  assert ((Radix.UInt16.hammingDistance ⟨0xFFFF⟩ ⟨0x0000⟩).toNat == 16) "hamming"
  assert ((Radix.UInt16.hammingDistance ⟨0x1234⟩ ⟨0x1234⟩).toNat == 0) "hamming same"

  -- ## Power-of-2 boundary loop
  for i in [:16] do
    let v : UInt16 := (1 <<< i.toUInt16)
    let rv : Radix.UInt16 := ⟨v⟩
    assert (Radix.UInt16.popcount rv == 1) s!"popcount 2^{i}"
    assert ((Radix.UInt16.ctz rv).toNat == i) s!"ctz 2^{i}"

  -- Identity for special values
  for v in [0, 1, 255, 256, 32767, 32768, 65534, 65535] do
    let a : Radix.UInt16 := ⟨v.toUInt16⟩
    assert (Radix.UInt16.wrappingAdd a ⟨0⟩ == a) s!"identity add {v}"
    assert (Radix.UInt16.wrappingMul a ⟨1⟩ == a) s!"identity mul {v}"
    assert ((Radix.UInt16.wrappingSub a a).toNat == 0) s!"self sub {v}"

  c.get
