import tests.ComprehensiveTests.Framework
import Radix.Bytes.Order
import Radix.Word.Arith
import Radix.Word.Int

/-!
# Bytes Order Tests (bswap, toBigEndian, fromBigEndian, etc.)
## Spec References
- FR-003: Byte ordering and endianness conversion
-/

open ComprehensiveTests

def runBytesOrderTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Bytes order tests..."

  -- ## UInt16 bswap
  assert ((Radix.UInt16.bswap ⟨0x0000⟩).toNat == 0x0000) "u16 bswap 0"
  assert ((Radix.UInt16.bswap ⟨0x0102⟩).toNat == 0x0201) "u16 bswap 0102"
  assert ((Radix.UInt16.bswap ⟨0xFFFF⟩).toNat == 0xFFFF) "u16 bswap FFFF"
  assert ((Radix.UInt16.bswap ⟨0x00FF⟩).toNat == 0xFF00) "u16 bswap 00FF"
  assert ((Radix.UInt16.bswap ⟨0xFF00⟩).toNat == 0x00FF) "u16 bswap FF00"
  assert ((Radix.UInt16.bswap ⟨0xABCD⟩).toNat == 0xCDAB) "u16 bswap ABCD"
  assert ((Radix.UInt16.bswap ⟨0x0001⟩).toNat == 0x0100) "u16 bswap 0001"
  -- Involution: bswap(bswap(x)) == x
  assert (Radix.UInt16.bswap (Radix.UInt16.bswap ⟨0x1234⟩) == ⟨0x1234⟩) "u16 bswap invol"

  -- ## UInt32 bswap
  assert ((Radix.UInt32.bswap ⟨0x00000000⟩).toNat == 0x00000000) "u32 bswap 0"
  assert ((Radix.UInt32.bswap ⟨0x01020304⟩).toNat == 0x04030201) "u32 bswap 01020304"
  assert ((Radix.UInt32.bswap ⟨0xFFFFFFFF⟩).toNat == 0xFFFFFFFF) "u32 bswap FFFFFFFF"
  assert ((Radix.UInt32.bswap ⟨0x12345678⟩).toNat == 0x78563412) "u32 bswap 12345678"
  assert (Radix.UInt32.bswap (Radix.UInt32.bswap ⟨0xDEADBEEF⟩) == ⟨0xDEADBEEF⟩) "u32 bswap invol"

  -- ## UInt64 bswap
  assert ((Radix.UInt64.bswap ⟨0x0000000000000000⟩).toNat == 0x0000000000000000) "u64 bswap 0"
  assert ((Radix.UInt64.bswap ⟨0x0102030405060708⟩).toNat == 0x0807060504030201) "u64 bswap seq"
  assert (Radix.UInt64.bswap (Radix.UInt64.bswap ⟨0xDEADCAFEBEEF0042⟩) == ⟨0xDEADCAFEBEEF0042⟩)
    "u64 bswap invol"

  -- ## Endian Conversions (on little-endian native)
  -- toLittleEndian should be identity on native little-endian
  assert (Radix.UInt16.toLittleEndian ⟨0x1234⟩ == ⟨0x1234⟩) "u16 toLittle identity"
  assert (Radix.UInt32.toLittleEndian ⟨0x12345678⟩ == ⟨0x12345678⟩) "u32 toLittle identity"
  assert (Radix.UInt64.toLittleEndian ⟨0x0102030405060708⟩ == ⟨0x0102030405060708⟩)
    "u64 toLittle identity"

  -- fromLittleEndian should also be identity
  assert (Radix.UInt16.fromLittleEndian ⟨0x1234⟩ == ⟨0x1234⟩) "u16 fromLittle identity"
  assert (Radix.UInt32.fromLittleEndian ⟨0x12345678⟩ == ⟨0x12345678⟩) "u32 fromLittle identity"

  -- toBigEndian == bswap on little-endian
  assert (Radix.UInt16.toBigEndian ⟨0x1234⟩ == Radix.UInt16.bswap ⟨0x1234⟩) "u16 toBig == bswap"
  assert (Radix.UInt32.toBigEndian ⟨0x12345678⟩ == Radix.UInt32.bswap ⟨0x12345678⟩)
    "u32 toBig == bswap"
  assert (Radix.UInt64.toBigEndian ⟨0x0102030405060708⟩ ==
    Radix.UInt64.bswap ⟨0x0102030405060708⟩) "u64 toBig == bswap"

  -- Round-trip: fromBE(toBE(x)) == x
  assert (Radix.UInt16.fromBigEndian (Radix.UInt16.toBigEndian ⟨0xABCD⟩) == ⟨0xABCD⟩)
    "u16 BE round-trip"
  assert (Radix.UInt32.fromBigEndian (Radix.UInt32.toBigEndian ⟨0x12345678⟩) == ⟨0x12345678⟩)
    "u32 BE round-trip"
  assert (Radix.UInt64.fromBigEndian (Radix.UInt64.toBigEndian ⟨0x0102030405060708⟩) ==
    ⟨0x0102030405060708⟩) "u64 BE round-trip"

  -- Round-trip: fromLE(toLE(x)) == x
  assert (Radix.UInt16.fromLittleEndian (Radix.UInt16.toLittleEndian ⟨0xABCD⟩) == ⟨0xABCD⟩)
    "u16 LE round-trip"
  assert (Radix.UInt32.fromLittleEndian (Radix.UInt32.toLittleEndian ⟨0x12345678⟩) ==
    ⟨0x12345678⟩) "u32 LE round-trip"

  -- ## Signed bswap
  -- Int16 bswap
  let si16 := Radix.Int16.fromInt 0x0102
  assert ((Radix.Int16.bswap si16).toUInt16 == Radix.UInt16.bswap si16.toUInt16) "i16 bswap"
  assert (Radix.Int16.fromBigEndian (Radix.Int16.toBigEndian si16) == si16)
    "i16 BE round-trip"
  assert (Radix.Int16.fromLittleEndian (Radix.Int16.toLittleEndian si16) == si16)
    "i16 LE round-trip"

  -- Int32 bswap
  let si32 := Radix.Int32.fromInt 0x01020304
  assert (Radix.Int32.fromBigEndian (Radix.Int32.toBigEndian si32) == si32)
    "i32 BE round-trip"

  -- Int64 bswap
  let si64 := Radix.Int64.fromInt 0x0102030405060708
  assert (Radix.Int64.fromBigEndian (Radix.Int64.toBigEndian si64) == si64)
    "i64 BE round-trip"

  -- ## toEndian / fromEndian on UInt16
  assert (Radix.UInt16.toEndian Radix.Bytes.Spec.Endian.big ⟨0x1234⟩ ==
    Radix.UInt16.toBigEndian ⟨0x1234⟩) "u16 toEndian big"
  assert (Radix.UInt16.toEndian Radix.Bytes.Spec.Endian.little ⟨0x1234⟩ ==
    Radix.UInt16.toLittleEndian ⟨0x1234⟩) "u16 toEndian little"
  assert (Radix.UInt16.fromEndian Radix.Bytes.Spec.Endian.big
    (Radix.UInt16.toEndian Radix.Bytes.Spec.Endian.big ⟨0xABCD⟩) == ⟨0xABCD⟩)
    "u16 fromEndian(toEndian) big"

  c.get
