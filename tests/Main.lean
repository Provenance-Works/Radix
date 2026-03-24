import Radix.Word.Arith
import Radix.Word.Int
import Radix.Word.Size
import Radix.Word.Conv
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field
import Radix.Bytes
import Radix.Memory
import Radix.Binary
import Radix.System
import Radix.Concurrency
import Radix.BareMetal
import tests.ComprehensiveTests.Word.Numeric
import tests.ComprehensiveTests.Alignment
import tests.ComprehensiveTests.RingBuffer
import tests.ComprehensiveTests.Bitmap
import tests.ComprehensiveTests.CRC
import tests.ComprehensiveTests.MemoryPool
import tests.ComprehensiveTests.Memory.Region
import tests.ComprehensiveTests.UTF8
import tests.ComprehensiveTests.ECC
import tests.ComprehensiveTests.DMA
import tests.ComprehensiveTests.Timer
import tests.ComprehensiveTests.ProofAutomation

/-! # Radix Execution Tests -/

/-- Assert that a condition holds, throwing an error with the given message if not. -/
private def assert (cond : Bool) (msg : String) : IO Unit :=
  if !cond then throw (IO.userError msg) else pure ()

/-! ## UInt8 Tests -/

private def testUInt8 : IO Unit := do
  IO.println "  UInt8..."
  -- Wrapping
  assert ((Radix.UInt8.wrappingAdd ⟨200⟩ ⟨100⟩).toNat == 44) "UInt8 wrappingAdd"
  assert ((Radix.UInt8.wrappingSub ⟨10⟩ ⟨20⟩).toNat == 246) "UInt8 wrappingSub"
  assert ((Radix.UInt8.wrappingMul ⟨16⟩ ⟨17⟩).toNat == 16) "UInt8 wrappingMul"
  -- Saturating
  assert ((Radix.UInt8.saturatingAdd ⟨200⟩ ⟨100⟩).toNat == 255) "UInt8 saturatingAdd"
  assert ((Radix.UInt8.saturatingSub ⟨10⟩ ⟨20⟩).toNat == 0) "UInt8 saturatingSub"
  -- Checked
  assert (Radix.UInt8.checkedAdd ⟨200⟩ ⟨100⟩ == none) "UInt8 checkedAdd overflow"
  assert (Radix.UInt8.checkedAdd ⟨100⟩ ⟨50⟩ == some ⟨150⟩) "UInt8 checkedAdd ok"
  assert (Radix.UInt8.checkedSub ⟨10⟩ ⟨20⟩ == none) "UInt8 checkedSub underflow"
  -- Overflowing
  let (r, ov) := Radix.UInt8.overflowingAdd ⟨200⟩ ⟨100⟩
  assert (r.toNat == 44 && ov == true) "UInt8 overflowingAdd"
  -- Bitwise
  assert ((Radix.UInt8.band ⟨0xAA⟩ ⟨0x0F⟩).toNat == 0x0A) "UInt8 band"
  assert ((Radix.UInt8.bor ⟨0xA0⟩ ⟨0x0F⟩).toNat == 0xAF) "UInt8 bor"
  assert ((Radix.UInt8.bxor ⟨0xFF⟩ ⟨0xAA⟩).toNat == 0x55) "UInt8 bxor"
  assert ((Radix.UInt8.bnot ⟨0x00⟩).toNat == 0xFF) "UInt8 bnot"
  -- Shifts
  assert ((Radix.UInt8.shl ⟨1⟩ ⟨3⟩).toNat == 8) "UInt8 shl"
  assert ((Radix.UInt8.shrLogical ⟨128⟩ ⟨3⟩).toNat == 16) "UInt8 shrLogical"
  -- Scan
  assert (Radix.UInt8.clz ⟨1⟩ == 7) "UInt8 clz"
  assert (Radix.UInt8.ctz ⟨8⟩ == 3) "UInt8 ctz"
  assert (Radix.UInt8.popcount ⟨0xFF⟩ == 8) "UInt8 popcount"
  assert (Radix.UInt8.popcount ⟨0⟩ == 0) "UInt8 popcount zero"
  -- Field
  assert (Radix.UInt8.testBit ⟨5⟩ 0 == true) "UInt8 testBit 0"
  assert (Radix.UInt8.testBit ⟨5⟩ 1 == false) "UInt8 testBit 1"
  assert ((Radix.UInt8.setBit ⟨0⟩ 3).toNat == 8) "UInt8 setBit"
  assert ((Radix.UInt8.clearBit ⟨0xFF⟩ 0).toNat == 0xFE) "UInt8 clearBit"
  -- Rotate
  assert ((Radix.UInt8.rotl ⟨0x81⟩ ⟨1⟩).toNat == 0x03) "UInt8 rotl"
  assert ((Radix.UInt8.rotr ⟨0x81⟩ ⟨1⟩).toNat == 0xC0) "UInt8 rotr"
  -- extractBits / insertBits
  assert ((Radix.UInt8.extractBits ⟨0xAB⟩ 4 8 ⟨by omega, by omega⟩).toNat == 0x0A)
    "UInt8 extractBits"
  assert ((Radix.UInt8.insertBits ⟨0x00⟩ ⟨0x0F⟩ 4 8 ⟨by omega, by omega⟩).toNat == 0xF0)
    "UInt8 insertBits"
  -- bitReverse
  assert ((Radix.UInt8.bitReverse ⟨0x80⟩).toNat == 0x01) "UInt8 bitReverse 0x80"
  assert ((Radix.UInt8.bitReverse ⟨0x01⟩).toNat == 0x80) "UInt8 bitReverse 0x01"
  -- shrArith
  assert ((Radix.UInt8.shrArith ⟨0x80⟩ ⟨1⟩).toNat == 0xC0) "UInt8 shrArith sign extend"
  assert ((Radix.UInt8.shrArith ⟨0x40⟩ ⟨1⟩).toNat == 0x20) "UInt8 shrArith no sign"
  -- Hamming distance
  assert ((Radix.UInt8.hammingDistance ⟨0xFF⟩ ⟨0x00⟩).toNat == 8) "UInt8 hammingDistance"
  assert ((Radix.UInt8.hammingDistance ⟨0xAA⟩ ⟨0x55⟩).toNat == 8) "UInt8 hammingDistance complement"
  assert ((Radix.UInt8.hammingDistance ⟨0xFF⟩ ⟨0xFF⟩).toNat == 0) "UInt8 hammingDistance same"

/-! ## UInt16 Tests -/

private def testUInt16 : IO Unit := do
  IO.println "  UInt16..."
  assert ((Radix.UInt16.wrappingAdd ⟨60000⟩ ⟨10000⟩).toNat == 4464) "UInt16 wrappingAdd"
  assert ((Radix.UInt16.wrappingSub ⟨10⟩ ⟨20⟩).toNat == 65526) "UInt16 wrappingSub"
  assert ((Radix.UInt16.wrappingMul ⟨1000⟩ ⟨100⟩).toNat == 34464) "UInt16 wrappingMul"
  assert ((Radix.UInt16.saturatingAdd ⟨60000⟩ ⟨10000⟩).toNat == 65535) "UInt16 saturatingAdd"
  assert ((Radix.UInt16.saturatingSub ⟨10⟩ ⟨20⟩).toNat == 0) "UInt16 saturatingSub"
  assert (Radix.UInt16.checkedAdd ⟨60000⟩ ⟨10000⟩ == none) "UInt16 checkedAdd overflow"
  assert (Radix.UInt16.checkedAdd ⟨100⟩ ⟨200⟩ == some ⟨300⟩) "UInt16 checkedAdd ok"
  assert (Radix.UInt16.checkedSub ⟨10⟩ ⟨20⟩ == none) "UInt16 checkedSub underflow"
  assert (Radix.UInt16.checkedSub ⟨20⟩ ⟨10⟩ == some ⟨10⟩) "UInt16 checkedSub ok"
  assert (Radix.UInt16.checkedMul ⟨60000⟩ ⟨2⟩ == none) "UInt16 checkedMul overflow"
  assert (Radix.UInt16.checkedMul ⟨100⟩ ⟨200⟩ == some ⟨20000⟩) "UInt16 checkedMul ok"
  let (r16, ov16) := Radix.UInt16.overflowingAdd ⟨60000⟩ ⟨10000⟩
  assert (r16.toNat == 4464 && ov16 == true) "UInt16 overflowingAdd"
  let (r16s, ov16s) := Radix.UInt16.overflowingSub ⟨10⟩ ⟨20⟩
  assert (r16s.toNat == 65526 && ov16s == true) "UInt16 overflowingSub"
  -- Bitwise
  assert ((Radix.UInt16.band ⟨0xFF00⟩ ⟨0x0FF0⟩).toNat == 0x0F00) "UInt16 band"
  assert ((Radix.UInt16.bor ⟨0xF000⟩ ⟨0x00FF⟩).toNat == 0xF0FF) "UInt16 bor"
  assert ((Radix.UInt16.bxor ⟨0xFFFF⟩ ⟨0xAAAA⟩).toNat == 0x5555) "UInt16 bxor"
  assert ((Radix.UInt16.shl ⟨1⟩ ⟨8⟩).toNat == 256) "UInt16 shl"
  assert ((Radix.UInt16.shrLogical ⟨256⟩ ⟨4⟩).toNat == 16) "UInt16 shrLogical"
  -- Scan
  assert (Radix.UInt16.clz ⟨1⟩ == 15) "UInt16 clz"
  assert (Radix.UInt16.ctz ⟨16⟩ == 4) "UInt16 ctz"
  assert (Radix.UInt16.popcount ⟨0xFFFF⟩ == 16) "UInt16 popcount"
  assert (Radix.UInt16.popcount ⟨0⟩ == 0) "UInt16 popcount zero"
  -- Field
  assert (Radix.UInt16.testBit ⟨0x100⟩ 8 == true) "UInt16 testBit"
  assert ((Radix.UInt16.setBit ⟨0⟩ 8).toNat == 256) "UInt16 setBit"
  assert ((Radix.UInt16.clearBit ⟨0xFF⟩ 0).toNat == 0xFE) "UInt16 clearBit"
  -- Rotate
  assert ((Radix.UInt16.rotl ⟨1⟩ ⟨4⟩).toNat == 16) "UInt16 rotl"
  assert ((Radix.UInt16.rotr ⟨0x8001⟩ ⟨1⟩).toNat == 0xC000) "UInt16 rotr"
  -- extractBits / insertBits
  assert ((Radix.UInt16.extractBits ⟨0xABCD⟩ 8 16 ⟨by omega, by omega⟩).toNat == 0xAB)
    "UInt16 extractBits"
  assert ((Radix.UInt16.insertBits ⟨0x00⟩ ⟨0xFF⟩ 8 16 ⟨by omega, by omega⟩).toNat == 0xFF00)
    "UInt16 insertBits"
  -- bitReverse
  assert ((Radix.UInt16.bitReverse ⟨0x8000⟩).toNat == 0x0001) "UInt16 bitReverse"
  -- shrArith
  assert ((Radix.UInt16.shrArith ⟨0x8000⟩ ⟨1⟩).toNat == 0xC000) "UInt16 shrArith"
  -- hammingDistance
  assert ((Radix.UInt16.hammingDistance ⟨0xFFFF⟩ ⟨0x0000⟩).toNat == 16) "UInt16 hammingDistance"

/-! ## UInt32 Tests -/

private def testUInt32 : IO Unit := do
  IO.println "  UInt32..."
  assert ((Radix.UInt32.wrappingAdd ⟨4000000000⟩ ⟨1000000000⟩).toNat ==
    (4000000000 + 1000000000) % 2^32) "UInt32 wrappingAdd"
  assert ((Radix.UInt32.wrappingSub ⟨10⟩ ⟨20⟩).toNat == 4294967286) "UInt32 wrappingSub"
  assert ((Radix.UInt32.saturatingAdd ⟨4000000000⟩ ⟨1000000000⟩).toNat == 4294967295) "UInt32 saturatingAdd"
  assert ((Radix.UInt32.saturatingSub ⟨10⟩ ⟨20⟩).toNat == 0) "UInt32 saturatingSub"
  assert (Radix.UInt32.checkedAdd ⟨4000000000⟩ ⟨1000000000⟩ == none) "UInt32 checkedAdd overflow"
  assert (Radix.UInt32.checkedAdd ⟨100⟩ ⟨200⟩ == some ⟨300⟩) "UInt32 checkedAdd ok"
  assert (Radix.UInt32.checkedSub ⟨10⟩ ⟨20⟩ == none) "UInt32 checkedSub underflow"
  let (_r32, ov32) := Radix.UInt32.overflowingAdd ⟨4000000000⟩ ⟨1000000000⟩
  assert (ov32 == true) "UInt32 overflowingAdd flag"
  let (r32s, ov32s) := Radix.UInt32.overflowingSub ⟨10⟩ ⟨20⟩
  assert (r32s.toNat == 4294967286 && ov32s == true) "UInt32 overflowingSub"
  -- Bitwise
  assert ((Radix.UInt32.band ⟨0xFF00FF00⟩ ⟨0x0F0F0F0F⟩).toNat == 0x0F000F00) "UInt32 band"
  assert ((Radix.UInt32.shl ⟨1⟩ ⟨16⟩).toNat == 65536) "UInt32 shl"
  -- Scan
  assert (Radix.UInt32.clz ⟨1⟩ == 31) "UInt32 clz"
  assert (Radix.UInt32.ctz ⟨256⟩ == 8) "UInt32 ctz"
  assert (Radix.UInt32.popcount ⟨0⟩ == 0) "UInt32 popcount zero"
  assert (Radix.UInt32.popcount ⟨0xFFFFFFFF⟩ == 32) "UInt32 popcount allOnes"
  -- Field
  assert (Radix.UInt32.testBit ⟨0x100⟩ 8 == true) "UInt32 testBit"
  assert ((Radix.UInt32.setBit ⟨0⟩ 16).toNat == 65536) "UInt32 setBit"
  -- Rotate
  assert ((Radix.UInt32.rotl ⟨1⟩ ⟨1⟩).toNat == 2) "UInt32 rotl"
  assert ((Radix.UInt32.rotr ⟨2⟩ ⟨1⟩).toNat == 1) "UInt32 rotr"
  -- extractBits / insertBits
  assert ((Radix.UInt32.extractBits ⟨0x12345678⟩ 16 32 ⟨by omega, by omega⟩).toNat == 0x1234)
    "UInt32 extractBits"
  assert ((Radix.UInt32.insertBits ⟨0⟩ ⟨0xFF⟩ 8 16 ⟨by omega, by omega⟩).toNat == 0xFF00)
    "UInt32 insertBits"
  -- bitReverse
  assert ((Radix.UInt32.bitReverse ⟨0x80000000⟩).toNat == 0x00000001) "UInt32 bitReverse"
  -- shrArith
  assert ((Radix.UInt32.shrArith ⟨0x80000000⟩ ⟨1⟩).toNat == 0xC0000000) "UInt32 shrArith"
  -- hammingDistance
  assert ((Radix.UInt32.hammingDistance ⟨0xFFFFFFFF⟩ ⟨0x00000000⟩).toNat == 32) "UInt32 hammingDistance"

/-! ## UInt64 Tests -/

private def testUInt64 : IO Unit := do
  IO.println "  UInt64..."
  assert ((Radix.UInt64.wrappingAdd ⟨1⟩ ⟨2⟩).toNat == 3) "UInt64 wrappingAdd"
  assert ((Radix.UInt64.wrappingSub ⟨0⟩ ⟨1⟩).toNat == 18446744073709551615) "UInt64 wrappingSub"
  assert ((Radix.UInt64.wrappingMul ⟨1000000000⟩ ⟨2⟩).toNat == 2000000000) "UInt64 wrappingMul"
  assert ((Radix.UInt64.saturatingAdd ⟨18446744073709551615⟩ ⟨1⟩).toNat == 18446744073709551615) "UInt64 saturatingAdd"
  assert ((Radix.UInt64.saturatingSub ⟨5⟩ ⟨10⟩).toNat == 0) "UInt64 saturatingSub"
  assert (Radix.UInt64.checkedAdd ⟨18446744073709551615⟩ ⟨1⟩ == none) "UInt64 checkedAdd overflow"
  assert (Radix.UInt64.checkedAdd ⟨100⟩ ⟨200⟩ == some ⟨300⟩) "UInt64 checkedAdd ok"
  assert (Radix.UInt64.checkedSub ⟨0⟩ ⟨1⟩ == none) "UInt64 checkedSub underflow"
  let (_, ov64) := Radix.UInt64.overflowingAdd ⟨18446744073709551615⟩ ⟨1⟩
  assert (ov64 == true) "UInt64 overflowingAdd flag"
  -- Bitwise
  assert ((Radix.UInt64.band ⟨0xFF⟩ ⟨0x0F⟩).toNat == 0x0F) "UInt64 band"
  assert ((Radix.UInt64.bor ⟨0xF0⟩ ⟨0x0F⟩).toNat == 0xFF) "UInt64 bor"
  assert ((Radix.UInt64.shl ⟨1⟩ ⟨32⟩).toNat == 4294967296) "UInt64 shl"
  assert ((Radix.UInt64.shrLogical ⟨4294967296⟩ ⟨16⟩).toNat == 65536) "UInt64 shrLogical"
  -- Scan
  assert (Radix.UInt64.clz ⟨1⟩ == 63) "UInt64 clz"
  assert (Radix.UInt64.ctz ⟨0⟩ == 64) "UInt64 ctz zero"
  assert (Radix.UInt64.popcount ⟨0⟩ == 0) "UInt64 popcount zero"
  -- Field
  assert (Radix.UInt64.testBit ⟨1⟩ 0 == true) "UInt64 testBit"
  assert ((Radix.UInt64.setBit ⟨0⟩ 32).toNat == 4294967296) "UInt64 setBit"
  -- Rotate
  assert ((Radix.UInt64.rotl ⟨1⟩ ⟨1⟩).toNat == 2) "UInt64 rotl"
  assert ((Radix.UInt64.rotr ⟨2⟩ ⟨1⟩).toNat == 1) "UInt64 rotr"
  -- extractBits / insertBits
  assert ((Radix.UInt64.extractBits ⟨0xFF⟩ 0 4 ⟨by omega, by omega⟩).toNat == 0x0F)
    "UInt64 extractBits"
  assert ((Radix.UInt64.insertBits ⟨0⟩ ⟨0x0F⟩ 4 8 ⟨by omega, by omega⟩).toNat == 0xF0)
    "UInt64 insertBits"
  -- bitReverse
  assert ((Radix.UInt64.bitReverse ⟨1⟩).toNat == 0x8000000000000000) "UInt64 bitReverse"
  -- shrArith
  assert ((Radix.UInt64.shrArith ⟨0x8000000000000000⟩ ⟨1⟩).toNat == 0xC000000000000000) "UInt64 shrArith"
  -- hammingDistance
  assert ((Radix.UInt64.hammingDistance ⟨0⟩ ⟨0⟩).toNat == 0) "UInt64 hammingDistance zero"

/-! ## Int8 Tests -/

private def testInt8 : IO Unit := do
  IO.println "  Int8..."
  let x : Radix.Int8 := ⟨⟨10⟩⟩
  let zero : Radix.Int8 := ⟨⟨0⟩⟩

  -- Division by zero
  assert (Radix.Int8.checkedDiv x zero == none) "Int8 checkedDiv by zero"

  -- MIN / -1 edge cases
  let min8 := Radix.Int8.minVal  -- -128
  let minus1 : Radix.Int8 := ⟨⟨255⟩⟩

  assert (Radix.Int8.saturatingDiv min8 minus1 (by decide) == Radix.Int8.maxVal)
    "Int8 saturatingDiv MIN/-1"
  assert (Radix.Int8.wrappingDiv min8 minus1 (by decide) == min8)
    "Int8 wrappingDiv MIN/-1"
  assert ((Radix.Int8.overflowingDiv min8 minus1 (by decide)).2 == true)
    "Int8 overflowingDiv MIN/-1 flag"
  assert (Radix.Int8.checkedDiv min8 minus1 == none)
    "Int8 checkedDiv MIN/-1"

  -- MIN % -1 edge cases
  let (q, ov) := Radix.Int8.overflowingRem min8 minus1 (by decide)
  assert (q == ⟨⟨0⟩⟩ && ov == true) "Int8 overflowingRem MIN%-1"
  assert (Radix.Int8.checkedRem min8 minus1 == none) "Int8 checkedRem MIN%-1"
  assert (Radix.Int8.saturatingRem min8 minus1 (by decide) == ⟨⟨0⟩⟩)
    "Int8 saturatingRem MIN%-1"
  assert (Radix.Int8.wrappingRem min8 minus1 (by decide) == ⟨⟨0⟩⟩)
    "Int8 wrappingRem MIN%-1"

  -- Wrapping overflow
  assert (Radix.Int8.wrappingAdd Radix.Int8.maxVal ⟨⟨1⟩⟩ == Radix.Int8.minVal)
    "Int8 wrapping overflow"

  -- Bitwise
  assert (Radix.Int8.testBit ⟨⟨5⟩⟩ 2 == true) "Int8 testBit"
  assert (Radix.Int8.popcount ⟨⟨0xFF⟩⟩ == 8) "Int8 popcount"
  -- Rotate
  assert ((Radix.Int8.rotl ⟨⟨0x81⟩⟩ ⟨⟨1⟩⟩) == ⟨⟨0x03⟩⟩) "Int8 rotl"
  assert ((Radix.Int8.rotr ⟨⟨0x81⟩⟩ ⟨⟨1⟩⟩) == ⟨⟨0xC0⟩⟩) "Int8 rotr"
  -- bitReverse
  assert ((Radix.Int8.bitReverse ⟨⟨0x80⟩⟩) == ⟨⟨0x01⟩⟩) "Int8 bitReverse"
  -- shrArith
  assert ((Radix.Int8.shrArith ⟨⟨0x80⟩⟩ ⟨⟨1⟩⟩).val.toNat == 0xC0) "Int8 shrArith"
  -- hammingDistance
  assert ((Radix.Int8.hammingDistance ⟨⟨0xFF⟩⟩ ⟨⟨0x00⟩⟩).val.toNat == 8) "Int8 hammingDistance"

/-! ## Int16 Tests -/

private def testInt16 : IO Unit := do
  IO.println "  Int16..."
  let min16 := Radix.Int16.minVal
  let minus1 := Radix.Int16.fromInt (-1)
  assert (Radix.Int16.checkedDiv min16 minus1 == none) "Int16 checkedDiv MIN/-1"
  assert (Radix.Int16.checkedRem min16 minus1 == none) "Int16 checkedRem MIN/-1"
  assert ((Radix.Int16.wrappingAdd ⟨⟨100⟩⟩ ⟨⟨200⟩⟩).toInt == 300) "Int16 wrappingAdd"
  assert (Radix.Int16.wrappingAdd Radix.Int16.maxVal ⟨⟨1⟩⟩ == Radix.Int16.minVal)
    "Int16 wrapping overflow"
  assert (Radix.Int16.saturatingDiv min16 minus1 (by decide) == Radix.Int16.maxVal)
    "Int16 saturatingDiv MIN/-1"
  -- Bitwise
  assert (Radix.Int16.testBit ⟨⟨5⟩⟩ 0 == true) "Int16 testBit"
  assert (Radix.Int16.popcount ⟨⟨0xFFFF⟩⟩ == 16) "Int16 popcount"
  -- Scan
  assert (Radix.Int16.clz ⟨⟨1⟩⟩ == 15) "Int16 clz"
  -- Rotate
  assert ((Radix.Int16.rotl ⟨⟨1⟩⟩ ⟨⟨4⟩⟩) == ⟨⟨16⟩⟩) "Int16 rotl"
  -- bitReverse
  assert ((Radix.Int16.bitReverse ⟨⟨0x8000⟩⟩) == ⟨⟨0x0001⟩⟩) "Int16 bitReverse"
  -- shrArith
  assert ((Radix.Int16.shrArith ⟨⟨0x8000⟩⟩ ⟨⟨1⟩⟩).val.toNat == 0xC000) "Int16 shrArith"
  -- hammingDistance
  assert ((Radix.Int16.hammingDistance ⟨⟨0xFFFF⟩⟩ ⟨⟨0⟩⟩).val.toNat == 16) "Int16 hammingDistance"

/-! ## Int32 Tests -/

private def testInt32 : IO Unit := do
  IO.println "  Int32..."
  let min32 := Radix.Int32.minVal
  let minus1 := Radix.Int32.fromInt (-1)
  assert (Radix.Int32.checkedDiv min32 minus1 == none) "Int32 checkedDiv MIN/-1"
  assert (Radix.Int32.checkedRem min32 minus1 == none) "Int32 checkedRem MIN/-1"
  assert (Radix.Int32.wrappingAdd Radix.Int32.maxVal ⟨⟨1⟩⟩ == Radix.Int32.minVal)
    "Int32 wrapping overflow"
  assert (Radix.Int32.saturatingDiv min32 minus1 (by decide) == Radix.Int32.maxVal)
    "Int32 saturatingDiv MIN/-1"
  assert ((Radix.Int32.overflowingDiv min32 minus1 (by decide)).2 == true)
    "Int32 overflowingDiv MIN/-1 flag"
  -- Bitwise
  assert (Radix.Int32.testBit ⟨⟨5⟩⟩ 2 == true) "Int32 testBit"
  assert (Radix.Int32.popcount ⟨⟨0⟩⟩ == 0) "Int32 popcount zero"
  -- Rotate
  assert ((Radix.Int32.rotl ⟨⟨1⟩⟩ ⟨⟨1⟩⟩) == ⟨⟨2⟩⟩) "Int32 rotl"
  -- bitReverse
  assert ((Radix.Int32.bitReverse ⟨⟨0x80000000⟩⟩) == ⟨⟨0x00000001⟩⟩) "Int32 bitReverse"
  -- shrArith
  assert ((Radix.Int32.shrArith ⟨⟨0x80000000⟩⟩ ⟨⟨1⟩⟩).val.toNat == 0xC0000000) "Int32 shrArith"
  -- hammingDistance
  assert ((Radix.Int32.hammingDistance ⟨⟨0⟩⟩ ⟨⟨0⟩⟩).val.toNat == 0) "Int32 hammingDistance"

/-! ## Int64 Tests -/

private def testInt64 : IO Unit := do
  IO.println "  Int64..."
  let min64 := Radix.Int64.minVal
  let minus1 := Radix.Int64.fromInt (-1)
  assert (Radix.Int64.checkedDiv min64 minus1 == none) "Int64 checkedDiv MIN/-1"
  assert (Radix.Int64.checkedRem min64 minus1 == none) "Int64 checkedRem MIN/-1"
  assert (Radix.Int64.wrappingAdd Radix.Int64.maxVal ⟨⟨1⟩⟩ == Radix.Int64.minVal)
    "Int64 wrapping overflow"
  assert (Radix.Int64.saturatingDiv min64 minus1 (by decide) == Radix.Int64.maxVal)
    "Int64 saturatingDiv MIN/-1"
  assert ((Radix.Int64.overflowingDiv min64 minus1 (by decide)).2 == true)
    "Int64 overflowingDiv MIN/-1 flag"
  -- Wrapping arithmetic
  assert ((Radix.Int64.wrappingAdd ⟨⟨100⟩⟩ ⟨⟨200⟩⟩).toInt == 300) "Int64 wrappingAdd"
  -- Bitwise
  assert (Radix.Int64.testBit ⟨⟨1⟩⟩ 0 == true) "Int64 testBit"
  assert (Radix.Int64.popcount ⟨⟨0⟩⟩ == 0) "Int64 popcount zero"
  -- Rotate
  assert ((Radix.Int64.rotl ⟨⟨1⟩⟩ ⟨⟨1⟩⟩) == ⟨⟨2⟩⟩) "Int64 rotl"
  -- bitReverse
  assert ((Radix.Int64.bitReverse ⟨⟨1⟩⟩).val.toNat == 0x8000000000000000) "Int64 bitReverse"
  -- shrArith
  assert ((Radix.Int64.shrArith ⟨⟨0x8000000000000000⟩⟩ ⟨⟨1⟩⟩).val.toNat == 0xC000000000000000) "Int64 shrArith"
  -- hammingDistance
  assert ((Radix.Int64.hammingDistance ⟨⟨0⟩⟩ ⟨⟨0⟩⟩).val.toNat == 0) "Int64 hammingDistance"

/-! ## UWord Tests -/

private def testUWord : IO Unit := do
  IO.println "  UWord..."
  let a : Radix.UWord := ⟨BitVec.ofNat _ 10⟩
  let b : Radix.UWord := ⟨BitVec.ofNat _ 20⟩
  assert ((a + b).toNat == 30) "UWord addition"
  assert ((Radix.UWord.wrappingAdd a b).toNat == 30) "UWord wrappingAdd"
  assert ((Radix.UWord.wrappingSub b a).toNat == 10) "UWord wrappingSub"
  assert ((Radix.UWord.wrappingMul a b).toNat == 200) "UWord wrappingMul"
  assert (Radix.UWord.checkedAdd a b != none) "UWord checkedAdd ok"
  assert (Radix.UWord.checkedSub b a != none) "UWord checkedSub ok"
  assert (Radix.UWord.checkedSub a b == none) "UWord checkedSub underflow"
  -- Saturating
  assert ((Radix.UWord.saturatingAdd a b).toNat == 30) "UWord saturatingAdd"
  assert ((Radix.UWord.saturatingSub a b).toNat == 0) "UWord saturatingSub"
  -- Overflowing
  let (rw, ovw) := Radix.UWord.overflowingAdd a b
  assert (rw.toNat == 30 && ovw == false) "UWord overflowingAdd no overflow"
  let (_rws, ovws) := Radix.UWord.overflowingSub a b
  assert (ovws == true) "UWord overflowingSub underflow"
  -- Bitwise
  let x : Radix.UWord := ⟨BitVec.ofNat _ 0xFF⟩
  let y : Radix.UWord := ⟨BitVec.ofNat _ 0x0F⟩
  assert ((Radix.UWord.band x y).toNat == 0x0F) "UWord band"
  assert ((Radix.UWord.bor x y).toNat == 0xFF) "UWord bor"
  assert ((Radix.UWord.bxor x y).toNat == 0xF0) "UWord bxor"
  -- Shifts
  let one : Radix.UWord := ⟨BitVec.ofNat _ 1⟩
  let four : Radix.UWord := ⟨BitVec.ofNat _ 4⟩
  assert ((Radix.UWord.shl one four).toNat == 16) "UWord shl"
  assert ((Radix.UWord.shrLogical ⟨BitVec.ofNat _ 16⟩ four).toNat == 1) "UWord shrLogical"
  -- Scan
  assert (Radix.UWord.ctz one == 0) "UWord ctz"
  assert (Radix.UWord.popcount (⟨BitVec.ofNat _ 0⟩ : Radix.UWord) == 0) "UWord popcount zero"
  -- Field
  assert (Radix.UWord.testBit (⟨BitVec.ofNat _ 5⟩ : Radix.UWord) 0 == true) "UWord testBit"
  assert (Radix.UWord.testBit (⟨BitVec.ofNat _ 5⟩ : Radix.UWord) 1 == false) "UWord testBit false"
  -- Rotate
  assert ((Radix.UWord.rotl one four).toNat == 16) "UWord rotl"
  assert ((Radix.UWord.rotr (⟨BitVec.ofNat _ 16⟩ : Radix.UWord) four).toNat == 1) "UWord rotr"
  -- extractBits / insertBits
  assert ((Radix.UWord.extractBits (⟨BitVec.ofNat _ 0xFF⟩ : Radix.UWord) 0 4
    ⟨by omega, by
      have h := System.Platform.numBits_eq
      omega⟩).toNat == 0x0F)
    "UWord extractBits"
  assert ((Radix.UWord.insertBits (⟨BitVec.ofNat _ 0⟩ : Radix.UWord) ⟨BitVec.ofNat _ 0x0F⟩ 4 8
    ⟨by omega, by
      have h := System.Platform.numBits_eq
      omega⟩).toNat == 0xF0)
    "UWord insertBits"

/-! ## IWord Tests -/

private def testIWord : IO Unit := do
  IO.println "  IWord..."
  let a : Radix.IWord := ⟨BitVec.ofNat _ 10⟩
  let b : Radix.IWord := ⟨BitVec.ofNat _ 20⟩
  assert ((a + b).val.toNat == 30) "IWord addition"
  assert ((Radix.IWord.wrappingAdd a b).val.toNat == 30) "IWord wrappingAdd"
  assert ((Radix.IWord.wrappingSub b a).val.toNat == 10) "IWord wrappingSub"
  assert ((Radix.IWord.wrappingMul a b).val.toNat == 200) "IWord wrappingMul"
  -- Negation
  let neg_a : Radix.IWord := -a
  assert ((a + neg_a).val.toNat == 0) "IWord negation"
  -- Checked
  assert (Radix.IWord.checkedAdd a b != none) "IWord checkedAdd ok"
  assert (Radix.IWord.checkedSub b a != none) "IWord checkedSub ok"
  -- Overflowing
  let (ri, ovi) := Radix.IWord.overflowingAdd a b
  assert (ri.val.toNat == 30 && ovi == false) "IWord overflowingAdd no overflow"
  -- Bitwise
  let x : Radix.IWord := ⟨BitVec.ofNat _ 0xFF⟩
  let y : Radix.IWord := ⟨BitVec.ofNat _ 0x0F⟩
  assert ((Radix.IWord.band x y).val.toNat == 0x0F) "IWord band"
  assert ((Radix.IWord.bor x y).val.toNat == 0xFF) "IWord bor"
  assert ((Radix.IWord.bxor x y).val.toNat == 0xF0) "IWord bxor"
  -- Shifts
  let one : Radix.IWord := ⟨BitVec.ofNat _ 1⟩
  let four : Radix.IWord := ⟨BitVec.ofNat _ 4⟩
  assert ((Radix.IWord.shl one four).val.toNat == 16) "IWord shl"
  -- Scan
  assert (Radix.IWord.popcount (⟨BitVec.ofNat _ 0⟩ : Radix.IWord) == 0) "IWord popcount zero"
  -- Field
  assert (Radix.IWord.testBit (⟨BitVec.ofNat _ 5⟩ : Radix.IWord) 0 == true) "IWord testBit"
  -- Rotate
  assert ((Radix.IWord.rotl one four).val.toNat == 16) "IWord rotl"
  assert ((Radix.IWord.rotr (⟨BitVec.ofNat _ 16⟩ : Radix.IWord) four).val.toNat == 1) "IWord rotr"

/-! ## Conversion Tests -/

private def testConversions : IO Unit := do
  IO.println "  Conversions..."
  -- Zero-extend
  let u8 : Radix.UInt8 := ⟨200⟩
  let u16 := Radix.UInt8.toUInt16 u8
  assert (u16.toNat == 200) "zeroExtend8to16"
  let u32 := Radix.UInt8.toUInt32 u8
  assert (u32.toNat == 200) "zeroExtend8to32"
  let u64 := Radix.UInt8.toUInt64 u8
  assert (u64.toNat == 200) "zeroExtend8to64"
  let u16v : Radix.UInt16 := ⟨50000⟩
  let u32v := Radix.UInt16.toUInt32 u16v
  assert (u32v.toNat == 50000) "zeroExtend16to32"
  let u64v := Radix.UInt16.toUInt64 u16v
  assert (u64v.toNat == 50000) "zeroExtend16to64"
  let u32w : Radix.UInt32 := ⟨3000000000⟩
  let u64w := Radix.UInt32.toUInt64 u32w
  assert (u64w.toNat == 3000000000) "zeroExtend32to64"
  -- Sign-extend
  let neg : Radix.Int8 := ⟨⟨0x80⟩⟩  -- -128
  let s16 := Radix.Int8.toInt16 neg
  assert (s16.toInt == -128) "signExtend8to16"
  let s32 := Radix.Int8.toInt32 neg
  assert (s32.toInt == -128) "signExtend8to32"
  let s64 := Radix.Int8.toInt64 neg
  assert (s64.toInt == -128) "signExtend8to64"
  let pos : Radix.Int8 := ⟨⟨42⟩⟩  -- 42
  let p16 := Radix.Int8.toInt16 pos
  assert (p16.toInt == 42) "signExtend8to16 positive"
  let neg16 : Radix.Int16 := Radix.Int16.fromInt (-1000)
  let s32v := Radix.Int16.toInt32 neg16
  assert (s32v.toInt == -1000) "signExtend16to32"
  let s64v := Radix.Int16.toInt64 neg16
  assert (s64v.toInt == -1000) "signExtend16to64"
  let neg32 : Radix.Int32 := Radix.Int32.fromInt (-100000)
  let s64w := Radix.Int32.toInt64 neg32
  assert (s64w.toInt == -100000) "signExtend32to64"
  -- Truncate
  let big : Radix.UInt16 := ⟨0x1234⟩
  let trunc := Radix.UInt16.toUInt8 big
  assert (trunc.toNat == 0x34) "truncate16to8"
  let big32 : Radix.UInt32 := ⟨0x12345678⟩
  let trunc16 := Radix.UInt32.toUInt16 big32
  assert (trunc16.toNat == 0x5678) "truncate32to16"
  let big64 : Radix.UInt64 := ⟨0x123456789ABCDEF0⟩
  let trunc32 := Radix.UInt64.toUInt32 big64
  assert (trunc32.toNat == 0x9ABCDEF0) "truncate64to32"
  -- Signed/unsigned round-trip
  let i8 : Radix.Int8 := ⟨⟨200⟩⟩
  assert (Radix.Int8.fromUInt8 (Radix.Int8.toUInt8 i8) == i8) "Int8 signed/unsigned roundtrip"
  let i16 : Radix.Int16 := ⟨⟨50000⟩⟩
  assert (Radix.Int16.fromUInt16 (Radix.Int16.toUInt16 i16) == i16) "Int16 signed/unsigned roundtrip"

/-! ================================================================ -/
/-! ## Phase 2: Byte Order Tests                                      -/
/-! ================================================================ -/

private def testByteOrder : IO Unit := do
  IO.println "  ByteOrder..."
  -- bswap16
  assert ((Radix.UInt16.bswap ⟨0x1234⟩).toNat == 0x3412) "UInt16 bswap"
  assert ((Radix.UInt16.bswap (Radix.UInt16.bswap ⟨0xABCD⟩)).toNat == 0xABCD) "UInt16 bswap involution"
  -- bswap32
  assert ((Radix.UInt32.bswap ⟨0x12345678⟩).toNat == 0x78563412) "UInt32 bswap"
  assert ((Radix.UInt32.bswap (Radix.UInt32.bswap ⟨0xDEADBEEF⟩)).toNat == 0xDEADBEEF) "UInt32 bswap involution"
  -- bswap64
  assert ((Radix.UInt64.bswap ⟨0x0102030405060708⟩).toNat == 0x0807060504030201) "UInt64 bswap"
  -- Big endian round-trip (on little-endian platform)
  assert ((Radix.UInt16.fromBigEndian (Radix.UInt16.toBigEndian ⟨0x1234⟩)).toNat == 0x1234)
    "UInt16 toBE/fromBE roundtrip"
  assert ((Radix.UInt32.fromBigEndian (Radix.UInt32.toBigEndian ⟨0x12345678⟩)).toNat == 0x12345678)
    "UInt32 toBE/fromBE roundtrip"
  -- Little endian round-trip (identity on LE platform)
  assert ((Radix.UInt16.fromLittleEndian (Radix.UInt16.toLittleEndian ⟨0x1234⟩)).toNat == 0x1234)
    "UInt16 toLE/fromLE roundtrip"
  -- Generic endian conversion
  assert ((Radix.UInt32.fromEndian .big (Radix.UInt32.toEndian .big ⟨42⟩)).toNat == 42)
    "UInt32 toEndian/fromEndian big roundtrip"
  assert ((Radix.UInt32.fromEndian .little (Radix.UInt32.toEndian .little ⟨42⟩)).toNat == 42)
    "UInt32 toEndian/fromEndian little roundtrip"

/-! ================================================================ -/
/-! ## Phase 2: ByteSlice Tests                                       -/
/-! ================================================================ -/

private def testByteSlice : IO Unit := do
  IO.println "  ByteSlice..."
  let empty := Radix.ByteSlice.empty
  assert (empty.size == 0) "ByteSlice empty size"
  assert (empty.isEmpty == true) "ByteSlice empty isEmpty"
  let z4 := Radix.ByteSlice.zeros 4
  assert (z4.size == 4) "ByteSlice zeros size"
  let arr := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
  let s := Radix.ByteSlice.ofByteArray arr
  assert (s.size == 8) "ByteSlice ofByteArray size"
  assert (s.checkedReadU8 0 == some 1) "ByteSlice checkedReadU8 0"
  assert (s.checkedReadU8 7 == some 8) "ByteSlice checkedReadU8 7"
  assert (s.checkedReadU8 8 == none) "ByteSlice checkedReadU8 OOB"
  assert (s.checkedReadU16 0 .little == some ⟨0x0201⟩) "ByteSlice checkedReadU16 LE"
  assert (s.checkedReadU16 0 .big == some ⟨0x0102⟩) "ByteSlice checkedReadU16 BE"
  assert (s.checkedReadU32 0 .little == some ⟨0x04030201⟩) "ByteSlice checkedReadU32 LE"
  assert (s.checkedReadU32 0 .big == some ⟨0x01020304⟩) "ByteSlice checkedReadU32 BE"
  assert (s.checkedReadU32 6 .little == none) "ByteSlice checkedReadU32 OOB"
  match s.checkedWriteU8 0 42 with
  | some s' =>
    assert (s'.checkedReadU8 0 == some 42) "ByteSlice write/read U8"
  | none => throw (IO.userError "ByteSlice checkedWriteU8 failed")
  match s.checkedSubslice 2 4 with
  | some sub =>
    assert (sub.size == 4) "ByteSlice subslice size"
    assert (sub.checkedReadU8 0 == some 3) "ByteSlice subslice read"
  | none => throw (IO.userError "ByteSlice checkedSubslice failed")
  assert (s.toList.length == 8) "ByteSlice toList length"

/-! ================================================================ -/
/-! ## Phase 2: Memory Buffer Tests                                   -/
/-! ================================================================ -/

private def testMemoryBuffer : IO Unit := do
  IO.println "  Memory.Buffer..."
  let buf := Radix.Memory.Buffer.zeros 16
  assert (buf.size == 16) "Buffer zeros size"
  let empty := Radix.Memory.Buffer.empty
  assert (empty.size == 0) "Buffer empty size"
  match buf.checkedWriteU8 0 ⟨0xAB⟩ with
  | some buf1 =>
    assert (buf1.checkedReadU8 0 == some ⟨0xAB⟩) "Buffer write/read U8"
  | none => throw (IO.userError "Buffer checkedWriteU8 failed")
  match buf.checkedWriteU32LE 0 ⟨0x12345678⟩ with
  | some buf2 =>
    assert (buf2.checkedReadU32LE 0 == some ⟨0x12345678⟩) "Buffer write/read U32LE"
    assert (buf2.checkedReadU8 0 == some ⟨0x78⟩) "Buffer U32LE byte 0"
    assert (buf2.checkedReadU8 1 == some ⟨0x56⟩) "Buffer U32LE byte 1"
    assert (buf2.checkedReadU8 2 == some ⟨0x34⟩) "Buffer U32LE byte 2"
    assert (buf2.checkedReadU8 3 == some ⟨0x12⟩) "Buffer U32LE byte 3"
  | none => throw (IO.userError "Buffer checkedWriteU32LE failed")
  match buf.checkedWriteU32BE 0 ⟨0x12345678⟩ with
  | some buf3 =>
    assert (buf3.checkedReadU32BE 0 == some ⟨0x12345678⟩) "Buffer write/read U32BE"
    assert (buf3.checkedReadU8 0 == some ⟨0x12⟩) "Buffer U32BE byte 0"
    assert (buf3.checkedReadU8 1 == some ⟨0x34⟩) "Buffer U32BE byte 1"
  | none => throw (IO.userError "Buffer checkedWriteU32BE failed")
  assert (buf.checkedReadU32LE 14 == none) "Buffer checkedReadU32LE OOB"
  assert ((buf.checkedWriteU8 16 ⟨0⟩).isNone) "Buffer checkedWriteU8 OOB"
  match buf.checkedWriteU16LE 0 ⟨0xABCD⟩ with
  | some buf4 =>
    assert (buf4.checkedReadU16LE 0 == some ⟨0xABCD⟩) "Buffer write/read U16LE"
  | none => throw (IO.userError "Buffer checkedWriteU16LE failed")
  match buf.checkedWriteU64LE 0 ⟨0x0102030405060708⟩ with
  | some buf5 =>
    assert (buf5.checkedReadU64LE 0 == some ⟨0x0102030405060708⟩) "Buffer write/read U64LE"
  | none => throw (IO.userError "Buffer checkedWriteU64LE failed")

/-! ================================================================ -/
/-! ## Phase 2: Memory Pointer Tests                                  -/
/-! ================================================================ -/

private def testMemoryPtr : IO Unit := do
  IO.println "  Memory.Ptr..."
  let buf := Radix.Memory.Buffer.zeros 16
  let p := Radix.Memory.Ptr.ofBuffer buf 1 (by decide)
  let p' := p.writeU8 ⟨0x42⟩
  assert (p'.readU8.toNat == 0x42) "Ptr write/read U8"
  let p2 := p.advance 4 (by decide)
  assert (p2.offset == 4) "Ptr advance offset"
  let p32 := Radix.Memory.Ptr.ofBuffer buf 4 (by decide)
  assert (p32.readU32LE.toNat == 0) "Ptr readU32LE zeros"

/-! ================================================================ -/
/-! ## Phase 2: Binary Format Tests                                   -/
/-! ================================================================ -/

private def testBinaryFormat : IO Unit := do
  IO.println "  Binary.Format..."
  let fmt := Radix.Binary.Format.u32le "magic" ++ Radix.Binary.Format.u16le "version" ++ Radix.Binary.Format.align 4
  assert (fmt.fixedSize == some 8) "Format fixedSize"
  assert (fmt.fieldCount == 2) "Format fieldCount"
  let spec := fmt.toFormatSpec
  assert (spec.totalSize == 8) "FormatSpec totalSize"
  let data := ByteArray.mk #[0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00]
  match Radix.Binary.parseFormatExact data fmt with
  | .ok fields =>
    match Radix.Binary.findField "magic" fields with
    | some (Radix.Binary.FieldValue.uint32 _ v) =>
      assert (v.toNat == 1) "parse magic value"
    | _ => throw (IO.userError "parse: missing magic field")
    match Radix.Binary.findField "version" fields with
    | some (Radix.Binary.FieldValue.uint16 _ v) =>
      assert (v.toNat == 2) "parse version value"
    | _ => throw (IO.userError "parse: missing version field")
  | .error e => throw (IO.userError s!"parse error: {e}")
  let fields := [
    Radix.Binary.FieldValue.uint32 "magic" ⟨0xDEAD⟩,
    Radix.Binary.FieldValue.uint16 "version" ⟨1⟩
  ]
  match Radix.Binary.serializeFormat fmt fields with
  | .ok serialized =>
    match Radix.Binary.parseFormatExact serialized fmt with
    | .ok fields2 =>
      match Radix.Binary.findField "magic" fields2 with
      | some (Radix.Binary.FieldValue.uint32 _ v) =>
        assert (v.toNat == 0xDEAD) "serialize/parse roundtrip magic"
      | _ => throw (IO.userError "roundtrip: missing magic")
      match Radix.Binary.findField "version" fields2 with
      | some (Radix.Binary.FieldValue.uint16 _ v) =>
        assert (v.toNat == 1) "serialize/parse roundtrip version"
      | _ => throw (IO.userError "roundtrip: missing version")
    | .error e => throw (IO.userError s!"roundtrip parse error: {e}")
  | .error e => throw (IO.userError s!"serialize error: {e}")

/-! ================================================================ -/
/-! ## Phase 2: LEB128 Tests                                          -/
/-! ================================================================ -/

private def testLeb128 : IO Unit := do
  IO.println "  LEB128..."
  let enc0 := Radix.Binary.Leb128.encodeU32 ⟨0⟩
  assert (enc0.size == 1) "LEB128 encodeU32 0 size"
  let enc127 := Radix.Binary.Leb128.encodeU32 ⟨127⟩
  assert (enc127.size == 1) "LEB128 encodeU32 127 size"
  let enc128 := Radix.Binary.Leb128.encodeU32 ⟨128⟩
  assert (enc128.size == 2) "LEB128 encodeU32 128 size"
  let enc16383 := Radix.Binary.Leb128.encodeU32 ⟨16383⟩
  assert (enc16383.size == 2) "LEB128 encodeU32 16383 size"
  let enc16384 := Radix.Binary.Leb128.encodeU32 ⟨16384⟩
  assert (enc16384.size == 3) "LEB128 encodeU32 16384 size"
  let encMax := Radix.Binary.Leb128.encodeU32 ⟨0xFFFFFFFF⟩
  assert (encMax.size == 5) "LEB128 encodeU32 max size"
  assert (encMax.size ≤ 5) "LEB128 encodeU32 max ≤ 5"
  match Radix.Binary.Leb128.decodeU32 enc0 0 with
  | some (v, n) =>
    assert (v.toNat == 0 && n == 1) "LEB128 decodeU32 0"
  | none => throw (IO.userError "LEB128 decodeU32 0 failed")
  match Radix.Binary.Leb128.decodeU32 enc128 0 with
  | some (v, n) =>
    assert (v.toNat == 128 && n == 2) "LEB128 decodeU32 128"
  | none => throw (IO.userError "LEB128 decodeU32 128 failed")
  match Radix.Binary.Leb128.decodeU32 encMax 0 with
  | some (v, n) =>
    assert (v.toNat == 0xFFFFFFFF && n == 5) "LEB128 decodeU32 max"
  | none => throw (IO.userError "LEB128 decodeU32 max failed")
  let encS0 := Radix.Binary.Leb128.encodeS32 (Radix.Int32.fromInt 0)
  assert (encS0.size == 1) "LEB128 encodeS32 0 size"
  let encSNeg1 := Radix.Binary.Leb128.encodeS32 (Radix.Int32.fromInt (-1))
  assert (encSNeg1.size == 1) "LEB128 encodeS32 -1 size"
  let encSNeg128 := Radix.Binary.Leb128.encodeS32 (Radix.Int32.fromInt (-128))
  assert (encSNeg128.size == 2) "LEB128 encodeS32 -128 size"
  match Radix.Binary.Leb128.decodeS32 encS0 0 with
  | some (v, n) =>
    assert (v.toInt == 0 && n == 1) "LEB128 decodeS32 0"
  | none => throw (IO.userError "LEB128 decodeS32 0 failed")
  match Radix.Binary.Leb128.decodeS32 encSNeg1 0 with
  | some (v, _) =>
    assert (v.toInt == -1) "LEB128 decodeS32 -1"
  | none => throw (IO.userError "LEB128 decodeS32 -1 failed")
  let enc64 := Radix.Binary.Leb128.encodeU64 ⟨0x0102030405060708⟩
  assert (0 < enc64.size) "LEB128 encodeU64 positive size"
  assert (enc64.size ≤ 10) "LEB128 encodeU64 ≤ 10"
  match Radix.Binary.Leb128.decodeU64 enc64 0 with
  | some (v, _) =>
    assert (v.toNat == 0x0102030405060708) "LEB128 decodeU64 roundtrip"
  | none => throw (IO.userError "LEB128 decodeU64 roundtrip failed")
  assert (Radix.Binary.Leb128.decodeU32 (ByteArray.mk #[0x80]) 0 == none) "LEB128 decodeU32 truncated"
  assert (Radix.Binary.Leb128.decodeU32 (ByteArray.mk #[0x01]) 1 == none) "LEB128 decodeU32 offset OOB"

/-! ================================================================ -/
/-! ## System Layer Tests (Phase 3)                                   -/
/-! ================================================================ -/

private def testSystemIO : IO Unit := do
  IO.println "  System I/O..."
  let tmpDir := "/tmp"
  let testFile := s!"{tmpDir}/radix_test_{← IO.monoMsNow}.bin"

  -- Write-then-read roundtrip
  let testData := ByteArray.mk #[0x01, 0x02, 0x03, 0xAB, 0xCD, 0xEF]
  let writeResult ← Radix.System.IO.writeFileBytes testFile testData
  match writeResult with
  | .error e => throw (IO.userError s!"writeFileBytes failed: {e}")
  | .ok () => pure ()

  let readResult ← Radix.System.IO.readFileBytes testFile
  match readResult with
  | .error e => throw (IO.userError s!"readFileBytes failed: {e}")
  | .ok bytes =>
    assert (bytes == testData) "System readFileBytes/writeFileBytes roundtrip"

  -- File metadata
  let metaResult ← Radix.System.IO.sysFileMeta testFile
  match metaResult with
  | .error e => throw (IO.userError s!"sysFileMeta failed: {e}")
  | .ok info =>
    assert (info.size == 6) "System sysFileMeta size"
    assert (info.isFile == true) "System sysFileMeta isFile"
    assert (info.isDir == false) "System sysFileMeta isDir"

  -- File exists
  let existsResult ← Radix.System.IO.sysFileExists testFile
  match existsResult with
  | .error e => throw (IO.userError s!"sysFileExists failed: {e}")
  | .ok exists_ => assert (exists_ == true) "System sysFileExists true"

  let noExistResult ← Radix.System.IO.sysFileExists (testFile ++ ".nonexistent")
  match noExistResult with
  | .error _ => pure ()  -- Expected: file not found is an error
  | .ok exists_ => assert (exists_ == false) "System sysFileExists false"

  -- String write/read roundtrip
  let strFile := testFile ++ ".txt"
  let testStr := "Hello, Radix! 🔧"
  let wsr ← Radix.System.IO.writeFileString strFile testStr
  match wsr with
  | .error e => throw (IO.userError s!"writeFileString failed: {e}")
  | .ok () => pure ()

  let rsr ← Radix.System.IO.readFileString strFile
  match rsr with
  | .error e => throw (IO.userError s!"readFileString failed: {e}")
  | .ok s => assert (s == testStr) "System readFileString/writeFileString roundtrip"

  -- withFile bracket pattern (resource safety)
  let bracketResult ← Radix.System.withFile testFile .read fun fd => do
    Radix.System.IO.sysRead fd 3
  match bracketResult with
  | .error e => throw (IO.userError s!"withFile read failed: {e}")
  | .ok bytes => assert (bytes.size == 3) "System withFile bracket read"

  -- sysSeek SEEK_SET
  let seekResult ← Radix.System.withFile testFile .read fun fd => do
    let sr ← Radix.System.IO.sysSeek fd .set 3
    match sr with
    | .error e => return .error e
    | .ok () => Radix.System.IO.sysRead fd 3
  match seekResult with
  | .error e => throw (IO.userError s!"sysSeek SET failed: {e}")
  | .ok bytes =>
    assert (bytes == ByteArray.mk #[0xAB, 0xCD, 0xEF]) "System sysSeek SEEK_SET"

  -- sysSeek SEEK_CUR (positive)
  let seekCurResult ← Radix.System.withFile testFile .read fun fd => do
    let _ ← Radix.System.IO.sysRead fd 1  -- advance past first byte
    let sr ← Radix.System.IO.sysSeek fd .cur 2
    match sr with
    | .error e => return .error e
    | .ok () => Radix.System.IO.sysRead fd 1
  match seekCurResult with
  | .error e => throw (IO.userError s!"sysSeek CUR failed: {e}")
  | .ok bytes =>
    assert (bytes == ByteArray.mk #[0xAB]) "System sysSeek SEEK_CUR positive"

  -- sysSeek SEEK_CUR (negative) should return unsupported error
  let seekNegResult ← Radix.System.withFile testFile .read fun fd => do
    Radix.System.IO.sysSeek fd .cur (-1)
  match seekNegResult with
  | .error _ => pure ()  -- Expected: unsupported
  | .ok () => throw (IO.userError "sysSeek SEEK_CUR negative should return error")

  -- sysSeek SEEK_END should return unsupported error
  let seekEndResult ← Radix.System.withFile testFile .read fun fd => do
    Radix.System.IO.sysSeek fd .end_ 0
  match seekEndResult with
  | .error _ => pure ()  -- Expected: unsupported
  | .ok () => throw (IO.userError "sysSeek SEEK_END should return error")

  -- Cleanup
  IO.FS.removeFile testFile
  IO.FS.removeFile strFile

private def testSystemError : IO Unit := do
  IO.println "  System Error mapping..."
  -- Test SysError.fromIOError mapping
  let notFoundErr := Radix.System.SysError.fromIOError
    (IO.Error.noFileOrDirectory "test.txt" 0 "not found")
  assert (match notFoundErr with | .notFound _ => true | _ => false) "SysError fromIOError notFound"

  let permErr := Radix.System.SysError.fromIOError
    (IO.Error.permissionDenied (some "forbidden") 0 "permission denied")
  assert (match permErr with | .permissionDenied _ => true | _ => false) "SysError fromIOError permissionDenied"

  let eofErr := Radix.System.SysError.fromIOError IO.Error.unexpectedEof
  assert (match eofErr with | .endOfFile => true | _ => false) "SysError fromIOError endOfFile"

private def testNativeEndian : IO Unit := do
  IO.println "  Native Endian validation..."
  let result ← Radix.validateNativeEndian
  match result with
  | .ok target => IO.println s!"    Platform: {target} (little-endian confirmed)"
  | .error msg => IO.println s!"    Warning: {msg}"

/-! ================================================================ -/
/-! ## Phase 5: Concurrency Tests                                    -/
/-! ================================================================ -/

private def testConcurrency : IO Unit :=
  open Radix.Concurrency.Spec in
  open Radix.Concurrency.Ordering in
  open Radix.Concurrency.Atomic in do
  IO.println "  Concurrency..."

  -- Memory ordering strength
  assert (MemoryOrder.seqCst.strength == 3) "seqCst strength"
  assert (MemoryOrder.relaxed.strength == 0) "relaxed strength"
  assert (MemoryOrder.seqCst.isAtLeast .relaxed) "seqCst >= relaxed"
  assert (MemoryOrder.seqCst.isAtLeast .seqCst) "seqCst >= seqCst"
  assert (!MemoryOrder.relaxed.isAtLeast .seqCst) "relaxed < seqCst"

  -- Ordering classification
  assert (hasAcquireSemantics .acquire) "acquire has acquire"
  assert (hasReleaseSemantics .release) "release has release"
  assert (hasAcquireSemantics .seqCst) "seqCst has acquire"
  assert (hasReleaseSemantics .seqCst) "seqCst has release"
  assert (!hasAcquireSemantics .relaxed) "relaxed no acquire"
  assert (!hasReleaseSemantics .relaxed) "relaxed no release"

  -- Validity for load/store
  assert (validLoadOrder .relaxed) "relaxed valid for load"
  assert (validLoadOrder .acquire) "acquire valid for load"
  assert (!validLoadOrder .release) "release invalid for load"
  assert (validStoreOrder .release) "release valid for store"
  assert (!validStoreOrder .acquire) "acquire invalid for store"
  assert (validRMWOrder .acqRel) "acqRel valid for RMW"

  -- CAS failure ordering
  assert (validCASFailureOrder .seqCst .seqCst) "seqCst/seqCst CAS valid"
  assert (validCASFailureOrder .acqRel .acquire) "acqRel/acquire CAS valid"
  assert (defaultFailureOrder .release == .relaxed) "release -> relaxed failure"
  assert (defaultFailureOrder .acqRel == .acquire) "acqRel -> acquire failure"

  -- Strengthen
  assert (strengthen .relaxed .seqCst == .seqCst) "strengthen relaxed to seqCst"
  assert (strengthen .seqCst .relaxed == .seqCst) "strengthen seqCst stays"

  -- Combine load/store
  assert (combineLoadStore .acquire .release == .acqRel) "combine acq+rel = acqRel"
  assert (combineLoadStore .seqCst .relaxed == .seqCst) "combine seqCst+any = seqCst"

  -- AtomicCell operations
  let cell := AtomicCell.new 42
  assert (cell.val == 42) "AtomicCell.new"

  -- Load
  let (loadRes, cell') := atomicLoad cell .relaxed
  assert (loadRes.value == 42) "atomicLoad value"
  assert (cell'.val == 42) "atomicLoad preserves cell"

  -- Store
  let (_, cell2) := atomicStore cell 100 .release
  assert (cell2.val == 100) "atomicStore sets value"

  -- CAS success
  let (casRes, cell3) := atomicCAS cell 42 99 .seqCst
  assert (casRes.success) "CAS success"
  assert (casRes.previous == 42) "CAS previous on success"
  assert (cell3.val == 99) "CAS updates on success"

  -- CAS failure
  let (casRes2, cell4) := atomicCAS cell 999 0 .seqCst
  assert (!casRes2.success) "CAS failure"
  assert (casRes2.previous == 42) "CAS previous on failure"
  assert (cell4.val == 42) "CAS preserves on failure"

  -- FetchAdd
  let (fetchRes, cell5) := fetchAdd cell 10 .seqCst
  assert (fetchRes.previous == 42) "fetchAdd previous"
  assert (cell5.val == 52) "fetchAdd result"

  -- FetchSub
  let (fetchRes2, cell6) := fetchSub cell 2 .seqCst
  assert (fetchRes2.previous == 42) "fetchSub previous"
  assert (cell6.val == 40) "fetchSub result"

  -- Exchange
  let (exchRes, cell7) := atomicExchange cell 999 .seqCst
  assert (exchRes.previous == 42) "exchange previous"
  assert (cell7.val == 999) "exchange result"

  -- FetchAnd / FetchOr / FetchXor
  let cellBits := AtomicCell.new 0xFF
  let (_, cell8) := fetchAnd cellBits 0x0F .relaxed
  assert (cell8.val == 0x0F) "fetchAnd"
  let (_, cell9) := fetchOr (AtomicCell.new 0x0F) 0xF0 .relaxed
  assert (cell9.val == 0xFF) "fetchOr"
  let (_, cell10) := fetchXor (AtomicCell.new 0xFF) 0x0F .relaxed
  assert (cell10.val == 0xF0) "fetchXor"

  -- Trace construction
  let tid := ThreadId.mk 0
  let loc := LocationId.mk 0
  let storeEvt := mkStoreEvent tid 0 loc 42 .release
  let loadEvt := mkLoadEvent tid 1 loc ⟨42⟩ .acquire
  assert (storeEvt.kind == .store) "store event kind"
  assert (loadEvt.kind == .load) "load event kind"
  assert (storeEvt.writeVal == 42) "store event writeVal"
  assert (loadEvt.readVal == 42) "load event readVal"

  -- Empty trace is data-race free (by definition)
  let emptyTrace := Trace.mk []
  assert (emptyTrace.events.length == 0) "empty trace"

/-! ================================================================ -/
/-! ## Phase 5: Bare Metal Tests                                     -/
/-! ================================================================ -/

private def testBareMetal : IO Unit :=
  open Radix.BareMetal.Spec in
  open Radix.BareMetal.GCFree in
  open Radix.BareMetal.Linker in
  open Radix.BareMetal.Startup in do
  IO.println "  Bare Metal..."

  -- Platform properties
  assert (Platform.x86_64.wordBits == 64) "x86_64 word bits"
  assert (Platform.aarch64.naturalAlign == 8) "aarch64 natural align"
  assert (Platform.riscv64.wordBits == 64) "riscv64 word bits"

  -- Memory region
  let textRegion : MemRegion :=
    { name := ".text", baseAddr := 0x08000000, size := 4096
      kind := .flash, permissions := .readExecute }
  let ramRegion : MemRegion :=
    { name := "SRAM", baseAddr := 0x20000000, size := 65536
      kind := .ram, permissions := .readWrite }
  assert (textRegion.endAddr == 0x08000000 + 4096) "region endAddr"
  assert (decide (MemRegion.disjoint textRegion ramRegion)) "text/ram disjoint"
  assert (decide (MemRegion.contains textRegion 0x08000000)) "region contains base"
  assert (decide (MemRegion.contains textRegion 0x08000FFF)) "region contains last"
  assert (!decide (MemRegion.contains textRegion 0x20000000)) "region not contains other"

  -- Memory map
  let mm : MemoryMap := { regions := [textRegion, ramRegion], platform := .x86_64 }
  assert (mm.totalSize == 4096 + 65536) "memory map total size"
  assert ((mm.findRegion 0x08000100).isSome) "findRegion in text"
  assert ((mm.findRegion 0x20000000).isSome) "findRegion in ram"
  assert ((mm.findRegion 0x00000000).isNone) "findRegion unmapped"

  -- Startup phases
  assert (StartupPhase.reset.order == 0) "reset order"
  assert (StartupPhase.appEntry.order == 4) "appEntry order"
  assert (StartupPhase.precedes .reset .appEntry) "reset precedes appEntry"
  assert (!StartupPhase.precedes .appEntry .reset) "appEntry not precedes reset"

  -- Startup step validity
  let validStep : StartupStep := { source := .reset, target := .earlyInit }
  assert (decide (StartupStep.isValid validStep)) "valid startup step"
  let invalidStep : StartupStep := { source := .reset, target := .appEntry }
  assert (!decide (StartupStep.isValid invalidStep)) "invalid startup step"

  -- GC-free constraints
  let defaultC := GCFreeConstraint.default
  assert (defaultC.maxStackBytes == 4096) "default max stack"
  assert (AllocStrategy.static ∈ defaultC.allowedStrategies) "default allows static"
  assert (AllocStrategy.stack ∈ defaultC.allowedStrategies) "default allows stack"
  assert (!(AllocStrategy.arena ∈ defaultC.allowedStrategies)) "default forbids arena"

  let arenaC := GCFreeConstraint.withArena 8192
  assert (AllocStrategy.arena ∈ arenaC.allowedStrategies) "withArena allows arena"

  -- Profile checking
  let goodProfile : AllocProfile := { name := "foo", strategy := .stack, maxStack := some 1024 }
  assert (checkProfile defaultC goodProfile) "good profile passes"

  let badProfile : AllocProfile := { name := "bar", strategy := .arena, maxStack := none }
  assert (!checkProfile defaultC badProfile) "bad strategy fails"

  let overflowProfile : AllocProfile := { name := "baz", strategy := .stack, maxStack := some 8192 }
  assert (!checkProfile defaultC overflowProfile) "overflow profile fails"

  -- Detailed check
  match checkProfileDetailed defaultC goodProfile with
  | .pass => pure ()
  | _ => throw (IO.userError "detailed check should pass")

  match checkProfileDetailed defaultC badProfile with
  | .failStrategy _ _ => pure ()
  | _ => throw (IO.userError "detailed check should failStrategy")

  -- Module check
  let results := checkModule defaultC [goodProfile, badProfile]
  assert (results.length == 1) "module check finds 1 failure"

  -- Lifetime classification
  assert (Lifetime.static.isBounded) "static bounded"
  assert (Lifetime.stack.isBounded) "stack bounded"
  assert (Lifetime.compileTime.isBounded) "compileTime bounded"
  assert (!Lifetime.heap.isBounded) "heap not bounded"

  -- Stack frames
  let frame : StackFrame := { name := "main", localBytes := 64, savedRegs := 16, padding := 0 }
  assert (frame.totalSize == 80) "frame total size"
  assert (worstCaseStackDepth [] == 0) "empty stack depth"
  assert (worstCaseStackDepth [frame] == 80) "single frame depth"

  -- Linker script
  let textSection : Section :=
    { name := ".text", lma := 0x08000000, vma := 0x08000000, size := 1024
      flags := .text }
  let dataSection : Section :=
    { name := ".data", lma := 0x08001000, vma := 0x20000000, size := 256
      flags := .data }
  let bssSection : Section :=
    { name := ".bss", lma := 0, vma := 0x20000100, size := 512
      flags := .bss }
  let entrySym : Symbol := { name := "_start", addr := 0x08000000, sectionName := ".text" }
  let ls : LinkerScript :=
    { sections := [textSection, dataSection, bssSection]
      symbols := [entrySym]
      entryPoint := "_start"
      platform := .x86_64 }

  assert (ls.totalSize == 1024 + 256 + 512) "linker script total size"
  assert ((ls.findSection ".text").isSome) "find .text section"
  assert ((ls.findSection ".bss").isSome) "find .bss section"
  assert ((ls.findSymbol "_start").isSome) "find _start symbol"
  assert ((ls.entryAddr).isSome) "entry addr exists"
  assert ((ls.entryAddr) == some 0x08000000) "entry addr value"

  -- Section disjointness
  assert (decide (Section.disjoint textSection dataSection)) "text/data disjoint"

  -- Section to region conversion
  let textReg := sectionToRegion textSection
  assert (textReg.kind == .flash) "text -> flash"
  assert (textReg.permissions.execute) "text is executable"
  let dataReg := sectionToRegion dataSection
  assert (dataReg.kind == .ram) "data -> ram"
  assert (dataReg.permissions.write) "data is writable"

  -- Memory map from linker script
  let mmFromLs := toMemoryMap ls
  assert (mmFromLs.regions.length == 3) "memory map has 3 regions"

  -- Address alignment
  assert (alignUp 100 16 == 112) "alignUp 100 16"
  assert (alignUp 128 16 == 128) "alignUp aligned"
  assert (alignDown 100 16 == 96) "alignDown 100 16"
  assert (isAligned 128 16) "isAligned 128 16"
  assert (!isAligned 100 16) "not isAligned 100 16"

  -- Startup sequence generation
  match generateStartup ls with
  | some actions =>
    assert (isValidStartupSequence actions) "generated startup is valid"
  | none => throw (IO.userError "generateStartup should succeed")

  -- Minimal startup validation
  let actions := minimalStartupActions 0x20010000 0x20000100 512
      0x08001000 0x20000000 256 0x08000000
  assert (isValidStartupSequence actions) "minimal startup valid"
  assert (startsWithInterruptsDisabled actions) "starts with interrupts disabled"
  assert (endsWithJump actions) "ends with jump"

  -- Full startup validation
  let fullActions := fullStartupActions 0x20010000 0x20000100 512
      0x08001000 0x20000000 256 0x08000400 0x08000000
  assert (isValidStartupSequence fullActions) "full startup valid"

def main : IO Unit := do
  IO.println "Running Radix Phase 1 tests..."
  testUInt8
  testUInt16
  testUInt32
  testUInt64
  testInt8
  testInt16
  testInt32
  testInt64
  testUWord
  testIWord
  testConversions
  IO.println "All Radix Phase 1 tests passed!"
  IO.println ""
  IO.println "Running Radix Phase 2 tests..."
  testByteOrder
  testByteSlice
  testMemoryBuffer
  testMemoryPtr
  testBinaryFormat
  testLeb128
  IO.println "All Radix Phase 2 tests passed!"
  IO.println ""
  IO.println "Running Radix Phase 3 tests..."
  testSystemIO
  testSystemError
  testNativeEndian
  IO.println "All Radix Phase 3 tests passed!"
  IO.println ""
  IO.println "Running Radix Phase 4 tests..."
  let _ ← runNumericTests
  let _ ← runAlignmentTests
  let _ ← runRingBufferTests
  let _ ← runBitmapTests
  let _ ← runCRCTests
  let _ ← runMemoryPoolTests
  IO.println "All Radix Phase 4 tests passed!"
  IO.println ""
  IO.println "Running Radix Phase 5 tests..."
  let _ ← runMemoryRegionTests
  let _ ← runUTF8Tests
  let _ ← runECCTests
  let _ ← runDMATests
  let _ ← runTimerTests
  let _ ← runProofAutomationTests
  IO.println "All Radix Phase 5 tests passed!"
  IO.println ""
  IO.println "Running Radix Phase 6 tests..."
  testConcurrency
  testBareMetal
  IO.println "All Radix Phase 6 tests passed!"
