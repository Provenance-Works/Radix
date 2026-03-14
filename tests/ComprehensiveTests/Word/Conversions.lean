import tests.ComprehensiveTests.Framework
import Radix.Word.Conv
import Radix.Word.Int

/-!
# Word Conversion Tests
## Spec References
- FR-001.3: Type conversions (zero-extend, sign-extend, truncate, signed↔unsigned)
-/

open ComprehensiveTests

def runConversionTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Word conversion tests..."

  -- ## Zero Extension (unsigned widening)
  -- UInt8 → UInt16/32/64
  assert ((Radix.UInt8.toUInt16 ⟨0⟩).toNat == 0) "u8→u16 0"
  assert ((Radix.UInt8.toUInt16 ⟨255⟩).toNat == 255) "u8→u16 255"
  assert ((Radix.UInt8.toUInt16 ⟨128⟩).toNat == 128) "u8→u16 128"
  assert ((Radix.UInt8.toUInt32 ⟨0⟩).toNat == 0) "u8→u32 0"
  assert ((Radix.UInt8.toUInt32 ⟨255⟩).toNat == 255) "u8→u32 255"
  assert ((Radix.UInt8.toUInt64 ⟨0⟩).toNat == 0) "u8→u64 0"
  assert ((Radix.UInt8.toUInt64 ⟨255⟩).toNat == 255) "u8→u64 255"

  -- UInt16 → UInt32/64
  assert ((Radix.UInt16.toUInt32 ⟨0⟩).toNat == 0) "u16→u32 0"
  assert ((Radix.UInt16.toUInt32 ⟨65535⟩).toNat == 65535) "u16→u32 MAX"
  assert ((Radix.UInt16.toUInt64 ⟨65535⟩).toNat == 65535) "u16→u64 MAX"

  -- UInt32 → UInt64
  assert ((Radix.UInt32.toUInt64 ⟨0⟩).toNat == 0) "u32→u64 0"
  assert ((Radix.UInt32.toUInt64 ⟨4294967295⟩).toNat == 4294967295) "u32→u64 MAX"

  -- ## Sign Extension (signed widening)
  -- Positive values
  assert ((Radix.Int8.toInt16 (Radix.Int8.fromInt 42)).toInt == 42) "i8→i16 42"
  assert ((Radix.Int8.toInt32 (Radix.Int8.fromInt 127)).toInt == 127) "i8→i32 127"
  assert ((Radix.Int8.toInt64 (Radix.Int8.fromInt 127)).toInt == 127) "i8→i64 127"
  -- Negative values: sign should be preserved
  assert ((Radix.Int8.toInt16 (Radix.Int8.fromInt (-1))).toInt == -1) "i8→i16 -1"
  assert ((Radix.Int8.toInt16 (Radix.Int8.fromInt (-128))).toInt == -128) "i8→i16 -128"
  assert ((Radix.Int8.toInt32 (Radix.Int8.fromInt (-1))).toInt == -1) "i8→i32 -1"
  assert ((Radix.Int8.toInt32 (Radix.Int8.fromInt (-128))).toInt == -128) "i8→i32 -128"
  assert ((Radix.Int8.toInt64 (Radix.Int8.fromInt (-1))).toInt == -1) "i8→i64 -1"
  assert ((Radix.Int8.toInt64 (Radix.Int8.fromInt (-128))).toInt == -128) "i8→i64 -128"
  -- Int16 → Int32/64
  assert ((Radix.Int16.toInt32 (Radix.Int16.fromInt (-32768))).toInt == -32768) "i16→i32 MIN"
  assert ((Radix.Int16.toInt32 (Radix.Int16.fromInt 32767)).toInt == 32767) "i16→i32 MAX"
  assert ((Radix.Int16.toInt64 (Radix.Int16.fromInt (-1))).toInt == -1) "i16→i64 -1"
  -- Int32 → Int64
  assert ((Radix.Int32.toInt64 (Radix.Int32.fromInt (-2147483648))).toInt == -2147483648)
    "i32→i64 MIN"
  assert ((Radix.Int32.toInt64 (Radix.Int32.fromInt 2147483647)).toInt == 2147483647)
    "i32→i64 MAX"

  -- ## Truncation (narrowing)
  -- UInt16 → UInt8
  assert ((Radix.UInt16.toUInt8 ⟨256⟩).toNat == 0) "u16→u8 256"
  assert ((Radix.UInt16.toUInt8 ⟨255⟩).toNat == 255) "u16→u8 255"
  assert ((Radix.UInt16.toUInt8 ⟨0x1234⟩).toNat == 0x34) "u16→u8 0x1234"
  -- UInt32 → UInt8/UInt16
  assert ((Radix.UInt32.toUInt8 ⟨0xABCD1234⟩).toNat == 0x34) "u32→u8"
  assert ((Radix.UInt32.toUInt16 ⟨0xABCD1234⟩).toNat == 0x1234) "u32→u16"
  -- UInt64 → UInt8/UInt16/UInt32
  assert ((Radix.UInt64.toUInt8 ⟨0x123456789ABCDEF0⟩).toNat == 0xF0) "u64→u8"
  assert ((Radix.UInt64.toUInt16 ⟨0x123456789ABCDEF0⟩).toNat == 0xDEF0) "u64→u16"
  assert ((Radix.UInt64.toUInt32 ⟨0x123456789ABCDEF0⟩).toNat == 0x9ABCDEF0) "u64→u32"
  -- Signed truncation
  assert ((Radix.Int16.toInt8 (Radix.Int16.fromInt (-1))).toInt == -1) "i16→i8 -1"
  assert ((Radix.Int16.toInt8 (Radix.Int16.fromInt 200)).toInt ==
    (Radix.Int8.fromInt 200).toInt) "i16→i8 200 trunc"
  assert ((Radix.Int32.toInt8 (Radix.Int32.fromInt (-1))).toInt == -1) "i32→i8 -1"
  assert ((Radix.Int32.toInt16 (Radix.Int32.fromInt (-1))).toInt == -1) "i32→i16 -1"
  assert ((Radix.Int64.toInt8 (Radix.Int64.fromInt (-1))).toInt == -1) "i64→i8 -1"
  assert ((Radix.Int64.toInt16 (Radix.Int64.fromInt (-1))).toInt == -1) "i64→i16 -1"
  assert ((Radix.Int64.toInt32 (Radix.Int64.fromInt (-1))).toInt == -1) "i64→i32 -1"

  -- ## Signed ↔ Unsigned (bit-pattern preserving)
  -- Int8 ↔ UInt8
  assert ((Radix.Int8.toUInt8 (Radix.Int8.fromInt (-1))).toNat == 255) "i8→u8 -1=255"
  assert ((Radix.Int8.toUInt8 (Radix.Int8.fromInt 0)).toNat == 0) "i8→u8 0"
  assert ((Radix.Int8.toUInt8 (Radix.Int8.fromInt (-128))).toNat == 128) "i8→u8 -128=128"
  assert ((Radix.Int8.fromUInt8 ⟨255⟩).toInt == -1) "u8→i8 255=-1"
  assert ((Radix.Int8.fromUInt8 ⟨128⟩).toInt == -128) "u8→i8 128=-128"
  assert ((Radix.Int8.fromUInt8 ⟨0⟩).toInt == 0) "u8→i8 0"
  -- Int16 ↔ UInt16
  assert ((Radix.Int16.toUInt16 (Radix.Int16.fromInt (-1))).toNat == 65535) "i16→u16 -1"
  assert ((Radix.Int16.fromUInt16 ⟨65535⟩).toInt == -1) "u16→i16 65535=-1"
  -- Int32 ↔ UInt32
  assert ((Radix.Int32.toUInt32 (Radix.Int32.fromInt (-1))).toNat == 4294967295) "i32→u32 -1"
  assert ((Radix.Int32.fromUInt32 ⟨4294967295⟩).toInt == -1) "u32→i32 MAX=-1"
  -- Int64 ↔ UInt64
  assert ((Radix.Int64.toUInt64 (Radix.Int64.fromInt (-1))).toNat == 18446744073709551615)
    "i64→u64 -1"
  assert ((Radix.Int64.fromUInt64 ⟨18446744073709551615⟩).toInt == -1) "u64→i64 MAX=-1"

  -- ## Round-trip tests: signed→unsigned→signed
  for v in [-128, -1, 0, 1, 127] do
    let a := Radix.Int8.fromInt v
    assert ((Radix.Int8.fromUInt8 (Radix.Int8.toUInt8 a)).toInt == v) s!"i8 round-trip {v}"

  for v in [-32768, -1, 0, 1, 32767] do
    let a := Radix.Int16.fromInt v
    assert ((Radix.Int16.fromUInt16 (Radix.Int16.toUInt16 a)).toInt == v) s!"i16 round-trip {v}"

  -- ## Chain extension: UInt8 → UInt16 → UInt32 → UInt64
  let u8 : Radix.UInt8 := ⟨200⟩
  let u16 := Radix.UInt8.toUInt16 u8
  let u32 := Radix.UInt16.toUInt32 u16
  let u64 := Radix.UInt32.toUInt64 u32
  assert (u64.toNat == 200) "chain zero-extend u8→u64"

  -- Chain sign extension: Int8 → Int16 → Int32 → Int64
  let i8 := Radix.Int8.fromInt (-42)
  let i16 := Radix.Int8.toInt16 i8
  let i32 := Radix.Int16.toInt32 i16
  let i64 := Radix.Int32.toInt64 i32
  assert (i64.toInt == -42) "chain sign-extend i8→i64"

  -- ## Truncation with extension round-trip
  -- extend then truncate should give back original
  for v in [0, 1, 127, 128, 255] do
    let orig : Radix.UInt8 := ⟨v.toUInt8⟩
    let extended := Radix.UInt8.toUInt32 orig
    let truncated := Radix.UInt32.toUInt8 extended
    assert (truncated == orig) s!"u8→u32→u8 round-trip {v}"

  -- signed: extend then truncate
  for v in [-128, -1, 0, 1, 127] do
    let orig := Radix.Int8.fromInt v
    let extended := Radix.Int8.toInt32 orig
    let truncated := Radix.Int32.toInt8 extended
    assert (truncated.toInt == v) s!"i8→i32→i8 round-trip {v}"

  c.get
