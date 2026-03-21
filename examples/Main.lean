import Radix.Word.Arith
import Radix.Word.Int
import Radix.Word.Conv
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field
import Radix.Bytes
import Radix.Bytes.Order
import Radix.Binary.Format
import Radix.Binary.Leb128
import Radix.Binary.Parser
import Radix.Binary.Serial
import Radix.Memory
import Radix.System
import Radix.Concurrency
import Radix.BareMetal

-- Individual focused examples
import examples.Crc32
import examples.IPv4Header
import examples.HexDump
import examples.RingBuffer
import examples.BitFlags
import examples.NetworkPacket
import examples.TinyVM
import examples.Varint
import examples.FirmwareImage
import examples.LockFree
import examples.SystemIO
import examples.BitmapDemo
import examples.AlignmentDemo
import examples.MemoryPoolDemo
import examples.NumericDemo

/-!
# Radix Usage Examples (P4-03)

Demonstrates the core capabilities of the Radix library:

1. **Word Arithmetic** — Wrapping, saturating, checked, overflowing operations
2. **Signed Integers** — Two's complement with safe conversions
3. **Bitwise Operations** — AND/OR/XOR/NOT, shifts, rotates
4. **Bit Scanning** — popcount, clz, ctz, bitReverse
5. **Bit Fields** — Test/set/clear/toggle, extract/insert
6. **Width Conversions** — Zero-extend, sign-extend, truncate
7. **Byte Order** — bswap, big/little endian conversions
8. **LEB128** — Variable-length integer encoding/decoding
9. **Binary Format DSL** — Declarative packet parsing/serialization
10. **Memory Buffer** — Bounds-checked read/write with proofs
11. **System I/O** — File read/write with ownership model
-/

open Radix in
open Radix.Binary in
open Radix.Memory in
open Radix.System in
open Radix.System.IO in

/-- Helper: assert with message. -/
private def check (cond : Bool) (msg : String) : IO Unit :=
  if cond then pure ()
  else throw (IO.userError s!"FAIL: {msg}")

/-! ================================================================ -/
/-! ## 1. Word Arithmetic                                            -/
/-! ================================================================ -/

private def exampleWordArith : IO Unit := do
  IO.println "=== 1. Word Arithmetic ==="

  -- Wrapping: overflow silently wraps around
  let a : Radix.UInt8 := ⟨200⟩
  let b : Radix.UInt8 := ⟨100⟩
  let sum := Radix.UInt8.wrappingAdd a b
  IO.println s!"  wrappingAdd 200 100 (u8) = {sum.toNat}"  -- 44
  check (sum.toNat == 44) "u8 wrapping 200+100=44"

  -- Saturating: clamp at boundary
  let sat := Radix.UInt8.saturatingAdd a b
  IO.println s!"  saturatingAdd 200 100 (u8) = {sat.toNat}"  -- 255
  check (sat.toNat == 255) "u8 saturating 200+100=255"

  -- Checked: returns none on overflow
  let chk := Radix.UInt8.checkedAdd a b
  IO.println s!"  checkedAdd 200 100 (u8) = {chk}"  -- none
  check chk.isNone "u8 checked 200+100 overflows"

  -- Checked: returns some when in range
  let c : Radix.UInt8 := ⟨10⟩
  let chk2 := Radix.UInt8.checkedAdd c b
  IO.println s!"  checkedAdd 10 100 (u8) = {chk2}"  -- some 110
  check (match chk2 with | some v => v.toNat == 110 | none => false) "u8 checked 10+100=110"

  -- Overflowing: returns value + overflow flag
  let (v, ov) := Radix.UInt8.overflowingAdd a b
  IO.println s!"  overflowingAdd 200 100 (u8) = ({v.toNat}, {ov})"  -- (44, true)
  check (v.toNat == 44 && ov == true) "u8 overflowing 200+100"

  -- 32-bit wrapping multiplication
  let x : Radix.UInt32 := ⟨0xFFFFFFFF⟩
  let y : Radix.UInt32 := ⟨2⟩
  let prod := Radix.UInt32.wrappingMul x y
  IO.println s!"  wrappingMul 0xFFFFFFFF 2 (u32) = {prod.toNat}"  -- 4294967294
  check (prod.toNat == 4294967294) "u32 wrapping mul"

  IO.println ""

/-! ================================================================ -/
/-! ## 2. Signed Integers                                            -/
/-! ================================================================ -/

private def exampleSignedInts : IO Unit := do
  IO.println "=== 2. Signed Integers ==="

  -- Create from Int
  let neg : Radix.Int8 := Radix.Int8.fromInt (-42)
  IO.println s!"  Int8.fromInt(-42) → toInt = {neg.toInt}"
  check (neg.toInt == -42) "Int8 -42 round trip"

  -- Two's complement boundaries
  let minI8 := Radix.Int8.minVal
  let maxI8 := Radix.Int8.maxVal
  IO.println s!"  Int8.minVal = {minI8.toInt}, maxVal = {maxI8.toInt}"
  check (minI8.toInt == -128) "Int8 min"
  check (maxI8.toInt == 127) "Int8 max"

  -- Signed comparison
  let a := Radix.Int8.fromInt (-1)
  let b := Radix.Int8.fromInt 1
  IO.println s!"  Int8.slt(-1, 1) = {Radix.Int8.slt a b}"
  check (Radix.Int8.slt a b == true) "Int8 -1 < 1"

  -- Wrapping arithmetic on signed
  let c := Radix.Int32.fromInt 2147483647  -- maxVal
  let d := Radix.Int32.fromInt 1
  let e := Radix.Int32.wrappingAdd c d
  IO.println s!"  Int32 maxVal + 1 (wrapping) = {e.toInt}"
  check (e.toInt == -2147483648) "Int32 overflow wraps to min"

  -- isNeg
  IO.println s!"  Int8 -42 isNeg = {Radix.Int8.isNeg neg}"
  check (Radix.Int8.isNeg neg == true) "Int8 -42 is negative"

  IO.println ""

/-! ================================================================ -/
/-! ## 3. Bitwise Operations                                         -/
/-! ================================================================ -/

private def exampleBitwise : IO Unit := do
  IO.println "=== 3. Bitwise Operations ==="

  let a : Radix.UInt8 := ⟨0b11001100⟩
  let b : Radix.UInt8 := ⟨0b10101010⟩

  IO.println s!"  a = 0xCC, b = 0xAA"
  IO.println s!"  band = {(Radix.UInt8.band a b).toNat}"     -- 0x88 = 136
  IO.println s!"  bor  = {(Radix.UInt8.bor a b).toNat}"      -- 0xEE = 238
  IO.println s!"  bxor = {(Radix.UInt8.bxor a b).toNat}"     -- 0x66 = 102
  IO.println s!"  bnot a = {(Radix.UInt8.bnot a).toNat}"     -- 0x33 = 51

  check ((Radix.UInt8.band a b).toNat == 0x88) "band"
  check ((Radix.UInt8.bor a b).toNat == 0xEE) "bor"
  check ((Radix.UInt8.bxor a b).toNat == 0x66) "bxor"
  check ((Radix.UInt8.bnot a).toNat == 0x33) "bnot"

  -- Shifts
  let x : Radix.UInt32 := ⟨1⟩
  let shifted := Radix.UInt32.shl x ⟨16⟩
  IO.println s!"  1 << 16 (u32) = {shifted.toNat}"  -- 65536
  check (shifted.toNat == 65536) "shl"

  -- Rotations
  let y : Radix.UInt8 := ⟨0b10000001⟩
  let rotated := Radix.UInt8.rotl y ⟨1⟩
  IO.println s!"  rotl 0x81 by 1 (u8) = {rotated.toNat}"  -- 0x03 = 3
  check (rotated.toNat == 3) "rotl"

  IO.println ""

/-! ================================================================ -/
/-! ## 4. Bit Scanning                                               -/
/-! ================================================================ -/

private def exampleBitScan : IO Unit := do
  IO.println "=== 4. Bit Scanning ==="

  let x : Radix.UInt32 := ⟨0x00FF00FF⟩
  IO.println s!"  x = 0x00FF00FF"
  IO.println s!"  popcount = {(Radix.UInt32.popcount x).toNat}"   -- 16
  IO.println s!"  clz = {(Radix.UInt32.clz x).toNat}"             -- 8
  IO.println s!"  ctz = {(Radix.UInt32.ctz x).toNat}"             -- 0

  check ((Radix.UInt32.popcount x).toNat == 16) "popcount"
  check ((Radix.UInt32.clz x).toNat == 8) "clz"
  check ((Radix.UInt32.ctz x).toNat == 0) "ctz"

  -- Bit reverse: 0x80000000 → 0x00000001
  let y : Radix.UInt32 := ⟨0x80000000⟩
  let rev := Radix.UInt32.bitReverse y
  IO.println s!"  bitReverse 0x80000000 = {rev.toNat}"
  check (rev.toNat == 1) "bitReverse"

  -- Leading zeros for power-of-2 detection
  let z : Radix.UInt32 := ⟨256⟩  -- 2^8
  let lz := Radix.UInt32.clz z
  IO.println s!"  clz(256) = {lz.toNat} → bit position = {31 - lz.toNat}"
  check (lz.toNat == 23) "clz of 256"

  IO.println ""

/-! ================================================================ -/
/-! ## 5. Bit Fields                                                 -/
/-! ================================================================ -/

private def exampleBitFields : IO Unit := do
  IO.println "=== 5. Bit Fields ==="

  let x : Radix.UInt32 := ⟨0⟩

  -- Set individual bits
  let x1 := Radix.UInt32.setBit x 0     -- bit 0
  let x2 := Radix.UInt32.setBit x1 7    -- bit 7
  let x3 := Radix.UInt32.setBit x2 31   -- bit 31
  IO.println s!"  setBit 0,7,31 → {x3.toNat}"
  check (Radix.UInt32.testBit x3 0 == true) "testBit 0"
  check (Radix.UInt32.testBit x3 7 == true) "testBit 7"
  check (Radix.UInt32.testBit x3 1 == false) "testBit 1"

  -- Clear and toggle
  let x4 := Radix.UInt32.clearBit x3 7
  IO.println s!"  clearBit 7 → testBit 7 = {Radix.UInt32.testBit x4 7}"
  check (Radix.UInt32.testBit x4 7 == false) "clearBit"

  let x5 := Radix.UInt32.toggleBit x4 7
  IO.println s!"  toggleBit 7 → testBit 7 = {Radix.UInt32.testBit x5 7}"
  check (Radix.UInt32.testBit x5 7 == true) "toggleBit"

  -- Extract and insert bit fields
  -- Pack: [31:24]=0xAB, [23:16]=0xCD, [15:8]=0xEF, [7:0]=0x12
  let packed : Radix.UInt32 := ⟨0xABCDEF12⟩
  let low8 := Radix.UInt32.extractBits packed 0 8 ⟨by omega, by omega⟩
  let mid8 := Radix.UInt32.extractBits packed 8 16 ⟨by omega, by omega⟩
  IO.println s!"  extractBits [7:0] of 0xABCDEF12 = {low8.toNat}"
  IO.println s!"  extractBits [15:8] of 0xABCDEF12 = {mid8.toNat}"
  check (low8.toNat == 0x12) "extract low byte"
  check (mid8.toNat == 0xEF) "extract mid byte"

  IO.println ""

/-! ================================================================ -/
/-! ## 6. Width Conversions                                          -/
/-! ================================================================ -/

private def exampleConversions : IO Unit := do
  IO.println "=== 6. Width Conversions ==="

  -- Zero-extend u8 → u32
  let a : Radix.UInt8 := ⟨0xFF⟩
  let a32 := Radix.UInt8.toUInt32 a
  IO.println s!"  u8(0xFF) → u32 = {a32.toNat}"  -- 255
  check (a32.toNat == 255) "zero-extend preserves value"

  -- Truncate u32 → u8
  let b : Radix.UInt32 := ⟨0x1234⟩
  let b8 := Radix.UInt32.toUInt8 b
  IO.println s!"  u32(0x1234) → u8 = {b8.toNat}"  -- 0x34
  check (b8.toNat == 0x34) "truncate keeps low byte"

  -- Sign-extend i8 → i32
  let c := Radix.Int8.fromInt (-1)
  let c32 := Radix.Int8.toInt32 c
  IO.println s!"  i8(-1) → i32.toInt = {c32.toInt}"  -- -1
  check (c32.toInt == -1) "sign-extend -1"

  -- Bit-pattern reinterpretation: signed ↔ unsigned
  let d := Radix.Int8.fromInt (-128)
  let d_u := Radix.Int8.toUInt8 d
  IO.println s!"  i8(-128) → u8 = {d_u.toNat}"  -- 128
  check (d_u.toNat == 128) "bit-pattern reinterpret"

  let e : Radix.UInt8 := ⟨128⟩
  let e_s := Radix.Int8.fromUInt8 e
  IO.println s!"  u8(128) → i8.toInt = {e_s.toInt}"  -- -128
  check (e_s.toInt == -128) "bit-pattern signed"

  IO.println ""

/-! ================================================================ -/
/-! ## 7. Byte Order                                                 -/
/-! ================================================================ -/

private def exampleByteOrder : IO Unit := do
  IO.println "=== 7. Byte Order ==="

  let x : Radix.UInt32 := ⟨0x01020304⟩

  -- bswap reverses byte order
  let swapped := Radix.UInt32.bswap x
  IO.println s!"  bswap 0x01020304 = {swapped.toNat}"
  check (swapped.toNat == 0x04030201) "bswap32"

  -- bswap is its own inverse
  let roundtrip := Radix.UInt32.bswap swapped
  IO.println s!"  bswap(bswap(x)) = {roundtrip.toNat}"
  check (roundtrip.toNat == x.toNat) "bswap involution"

  -- Big-endian conversions (on little-endian platform)
  let be := Radix.UInt32.toBigEndian x
  let back := Radix.UInt32.fromBigEndian be
  IO.println s!"  toBigEndian → fromBigEndian round-trip: {back.toNat == x.toNat}"
  check (back.toNat == x.toNat) "BE round-trip"

  -- Little-endian is identity on LE platforms
  let le := Radix.UInt32.toLittleEndian x
  IO.println s!"  toLittleEndian 0x01020304 = {le.toNat} (identity on LE)"
  check (le.toNat == x.toNat) "LE identity"

  -- 16-bit swap
  let y : Radix.UInt16 := ⟨0xAABB⟩
  let ys := Radix.UInt16.bswap y
  IO.println s!"  bswap16 0xAABB = {ys.toNat}"
  check (ys.toNat == 0xBBAA) "bswap16"

  IO.println ""

/-! ================================================================ -/
/-! ## 8. LEB128 Encoding                                            -/
/-! ================================================================ -/

private def exampleLeb128 : IO Unit := do
  IO.println "=== 8. LEB128 Encoding ==="

  -- Unsigned LEB128
  let val32 : Radix.UInt32 := ⟨624485⟩
  let encoded := Radix.Binary.Leb128.encodeU32 val32
  IO.println s!"  encodeU32(624485) = {encoded.size} bytes: {encoded.toList}"
  -- 624485 → [0xE5, 0x8E, 0x26] (3 bytes)
  check (encoded.size == 3) "LEB128 size"

  -- Decode round-trip
  match Radix.Binary.Leb128.decodeU32 encoded 0 with
  | some (decoded, consumed) =>
    IO.println s!"  decodeU32 → value={decoded.toNat}, consumed={consumed} bytes"
    check (decoded.toNat == 624485) "LEB128 round-trip"
    check (consumed == 3) "LEB128 consumed"
  | none =>
    throw (IO.userError "LEB128 decode failed")

  -- Unsigned: small values are 1 byte
  let small : Radix.UInt32 := ⟨127⟩
  check ((Radix.Binary.Leb128.encodeU32 small).size == 1) "LEB128 small=1byte"
  IO.println s!"  encodeU32(127) = 1 byte"

  let medium : Radix.UInt32 := ⟨128⟩
  check ((Radix.Binary.Leb128.encodeU32 medium).size == 2) "LEB128 128=2bytes"
  IO.println s!"  encodeU32(128) = 2 bytes"

  -- Signed LEB128
  let neg : Radix.Int32 := Radix.Int32.fromInt (-123456)
  let encS := Radix.Binary.Leb128.encodeS32 neg
  IO.println s!"  encodeS32(-123456) = {encS.size} bytes"
  match Radix.Binary.Leb128.decodeS32 encS 0 with
  | some (decoded, _) =>
    IO.println s!"  decodeS32 → value={decoded.toInt}"
    check (decoded.toInt == -123456) "signed LEB128 round-trip"
  | none =>
    throw (IO.userError "signed LEB128 decode failed")

  IO.println ""

/-! ================================================================ -/
/-! ## 9. Binary Format DSL                                          -/
/-! ================================================================ -/

private def exampleBinaryFormat : IO Unit := do
  IO.println "=== 9. Binary Format DSL ==="

  -- Define a simple packet format:
  -- magic: u32le, version: u16be, _padding: 2 bytes, payload_len: u32le
  let packetFmt :=
    Radix.Binary.Format.u32le "magic" ++
    Radix.Binary.Format.u16be "version" ++
    Radix.Binary.Format.pad 2 ++
    Radix.Binary.Format.u32le "payload_len"

  -- Compute expected size
  IO.println s!"  packet format fixed size = {packetFmt.fixedSize}"
  IO.println s!"  field names = {packetFmt.fieldNames}"
  check (packetFmt.fixedSize == some 12) "format size"

  -- Serialize
  let fields : List Radix.Binary.FieldValue := [
    .uint32 "magic" ⟨0xDEADBEEF⟩,
    .uint16 "version" ⟨0x0102⟩,
    .uint32 "payload_len" ⟨256⟩
  ]

  match Radix.Binary.serializeFormat packetFmt fields with
  | .ok bytes =>
    IO.println s!"  serialized {bytes.size} bytes"
    check (bytes.size == 12) "serialized size"

    -- Parse back
    match Radix.Binary.parseFormat bytes packetFmt with
    | .ok parsed =>
      IO.println s!"  parsed {parsed.length} fields"
      -- Find specific field
      match Radix.Binary.findField "magic" parsed with
      | some (.uint32 _ v) =>
        IO.println s!"  magic = {v.toNat}"
        check (v.toNat == 0xDEADBEEF) "parse magic"
      | _ => throw (IO.userError "magic field not found")

      match Radix.Binary.findField "version" parsed with
      | some (.uint16 _ v) =>
        IO.println s!"  version = {v.toNat}"
        check (v.toNat == 0x0102) "parse version"
      | _ => throw (IO.userError "version field not found")

      match Radix.Binary.findField "payload_len" parsed with
      | some (.uint32 _ v) =>
        IO.println s!"  payload_len = {v.toNat}"
        check (v.toNat == 256) "parse payload_len"
      | _ => throw (IO.userError "payload_len field not found")
    | .error e => throw (IO.userError s!"parse error: {e}")
  | .error e => throw (IO.userError s!"serialize error: {e}")

  IO.println ""

/-! ================================================================ -/
/-! ## 10. Memory Buffer                                             -/
/-! ================================================================ -/

private def exampleMemoryBuffer : IO Unit := do
  IO.println "=== 10. Memory Buffer ==="

  -- Create a zeroed buffer
  let buf := Radix.Memory.Buffer.zeros 16
  IO.println s!"  buffer size = {buf.size}"
  check (buf.size == 16) "buffer size"

  -- Write and read using checked (Option) API
  match Radix.Memory.Buffer.checkedWriteU8 buf 0 ⟨0x42⟩ with
  | some buf1 =>
    match Radix.Memory.Buffer.checkedWriteU8 buf1 1 ⟨0xFF⟩ with
    | some buf2 =>
      let v0 := Radix.Memory.Buffer.checkedReadU8 buf2 0
      let v1 := Radix.Memory.Buffer.checkedReadU8 buf2 1
      IO.println s!"  read[0] = {v0}, read[1] = {v1}"
      check (match v0 with | some v => v.toNat == 0x42 | none => false) "read back 0"
      check (match v1 with | some v => v.toNat == 0xFF | none => false) "read back 1"
    | none => throw (IO.userError "write[1] failed")
  | none => throw (IO.userError "write[0] failed")

  -- Multi-byte write/read (u32 big-endian)
  let buf3 := Radix.Memory.Buffer.zeros 8
  match Radix.Memory.Buffer.checkedWriteU32BE buf3 0 ⟨0x01020304⟩ with
  | some buf4 =>
    -- Read individual bytes to see big-endian layout
    let b0 := Radix.Memory.Buffer.checkedReadU8 buf4 0
    let b1 := Radix.Memory.Buffer.checkedReadU8 buf4 1
    let b2 := Radix.Memory.Buffer.checkedReadU8 buf4 2
    let b3 := Radix.Memory.Buffer.checkedReadU8 buf4 3
    IO.println s!"  u32BE 0x01020304 → bytes: [{b0}, {b1}, {b2}, {b3}]"
    check (match b0 with | some v => v.toNat == 0x01 | none => false) "BE byte 0"
    check (match b3 with | some v => v.toNat == 0x04 | none => false) "BE byte 3"

    -- Read back as u32
    match Radix.Memory.Buffer.checkedReadU32BE buf4 0 with
    | some v =>
      IO.println s!"  readU32BE → {v.toNat}"
      check (v.toNat == 0x01020304) "u32BE round-trip"
    | none => throw (IO.userError "readU32BE failed")
  | none => throw (IO.userError "writeU32BE failed")

  -- Out-of-bounds returns none
  let oob := Radix.Memory.Buffer.checkedReadU8 buf3 100
  IO.println s!"  OOB read at offset 100 = {oob}"
  check oob.isNone "OOB returns none"

  IO.println ""

/-! ================================================================ -/
/-! ## 11. System I/O                                                -/
/-! ================================================================ -/

private def exampleSystemIO : IO Unit := do
  IO.println "=== 11. System I/O ==="

  let testDir := "/tmp/radix_examples"
  let testFile := s!"{testDir}/test.bin"
  let testStr := s!"{testDir}/test.txt"

  -- Create directory
  IO.FS.createDirAll testDir

  -- Write and read binary data
  let writeData := ByteArray.mk #[0x01, 0x02, 0x03, 0x04, 0xFF]
  match ← Radix.System.IO.writeFileBytes testFile writeData with
  | .ok () =>
    IO.println s!"  wrote {writeData.size} bytes to {testFile}"
  | .error e => throw (IO.userError s!"write error: {e}")

  match ← Radix.System.IO.readFileBytes testFile with
  | .ok readData =>
    IO.println s!"  read {readData.size} bytes back"
    check (readData.size == 5) "read size"
    check (readData == writeData) "binary round-trip"
  | .error e => throw (IO.userError s!"read error: {e}")

  -- String I/O
  let content := "Hello from Radix! 日本語テスト"
  match ← Radix.System.IO.writeFileString testStr content with
  | .ok () => IO.println s!"  wrote string to {testStr}"
  | .error e => throw (IO.userError s!"write string error: {e}")

  match ← Radix.System.IO.readFileString testStr with
  | .ok readStr =>
    IO.println s!"  read string: \"{readStr}\""
    check (readStr == content) "string round-trip"
  | .error e => throw (IO.userError s!"read string error: {e}")

  -- File existence check
  match ← Radix.System.IO.sysFileExists testFile with
  | .ok doesExist =>
    IO.println s!"  file exists = {doesExist}"
    check (doesExist == true) "file exists"
  | .error e => throw (IO.userError s!"exists error: {e}")

  -- withFile bracket pattern
  match ← Radix.System.withFile testFile .read fun fd => do
    match ← Radix.System.IO.sysRead fd 5 with
    | .ok data => return .ok data.size
    | .error e => return .error e
  with
  | .ok n => IO.println s!"  withFile read {n} bytes"
  | .error e => throw (IO.userError s!"withFile error: {e}")

  -- Cleanup
  IO.FS.removeFile testFile
  IO.FS.removeFile testStr
  IO.FS.removeDirAll testDir
  IO.println "  cleaned up test files"
  IO.println ""

/-! ================================================================ -/
/-! ## Section 12: Concurrency Model                                 -/
/-! ================================================================ -/

private def exampleConcurrency : IO Unit :=
  open Radix.Concurrency.Spec in
  open Radix.Concurrency.Ordering in
  open Radix.Concurrency.Atomic in do
  IO.println "12. Concurrency Model"
  IO.println "---------------------"

  -- Memory ordering levels
  IO.println "  Memory Orderings:"
  IO.println s!"    Relaxed strength: {MemoryOrder.relaxed.strength}"
  IO.println s!"    Acquire strength: {MemoryOrder.acquire.strength}"
  IO.println s!"    SeqCst strength:  {MemoryOrder.seqCst.strength}"

  -- Ordering classification
  IO.println "  SeqCst has acquire: {hasAcquireSemantics .seqCst}"
  IO.println "  SeqCst has release: {hasReleaseSemantics .seqCst}"

  -- Atomic cell: load, store, CAS
  IO.println "  Atomic Operations:"
  let cell := AtomicCell.new 0
  IO.println s!"    Initial: {cell.val}"

  let (_, cell) := atomicStore cell 42 .release
  IO.println s!"    After store 42: {cell.val}"

  let (res, _) := atomicLoad cell .acquire
  IO.println s!"    Load: {res.value}"

  -- CAS: try to swap 42 -> 100
  let (casRes, cell) := atomicCAS cell 42 100 .seqCst
  IO.println s!"    CAS 42->100: success={casRes.success}, prev={casRes.previous}, now={cell.val}"

  -- CAS: try to swap 42 -> 200 (should fail, current is 100)
  let (casRes2, cell) := atomicCAS cell 42 200 .seqCst
  IO.println s!"    CAS 42->200: success={casRes2.success}, prev={casRes2.previous}, now={cell.val}"

  -- Fetch-and-add
  let (fetchRes, cell) := fetchAdd cell 10 .seqCst
  IO.println s!"    FetchAdd +10: prev={fetchRes.previous}, now={cell.val}"

  -- Exchange
  let (exchRes, cell) := atomicExchange cell 999 .seqCst
  IO.println s!"    Exchange 999: prev={exchRes.previous}, now={cell.val}"

  IO.println ""

/-! ================================================================ -/
/-! ## Section 13: Bare Metal Model                                  -/
/-! ================================================================ -/

private def exampleBareMetal : IO Unit :=
  open Radix.BareMetal.Spec in
  open Radix.BareMetal.GCFree in
  open Radix.BareMetal.Linker in
  open Radix.BareMetal.Startup in do
  IO.println "13. Bare Metal Model"
  IO.println "--------------------"

  -- Memory map definition
  IO.println "  Memory Map (STM32-style):"
  let flashRegion : MemRegion :=
    { name := "FLASH", baseAddr := 0x08000000, size := 512 * 1024
      kind := .flash, permissions := .readExecute }
  let sramRegion : MemRegion :=
    { name := "SRAM", baseAddr := 0x20000000, size := 128 * 1024
      kind := .ram, permissions := .readWrite }
  let mmioRegion : MemRegion :=
    { name := "PERIPH", baseAddr := 0x40000000, size := 0x20000000
      kind := .mmio, permissions := .readWrite }
  let mm : MemoryMap := { regions := [flashRegion, sramRegion, mmioRegion], platform := .aarch64 }
  IO.println s!"    Flash: 0x{String.ofList (Nat.toDigits 16 flashRegion.baseAddr)} ({flashRegion.size / 1024}KB)"
  IO.println s!"    SRAM:  0x{String.ofList (Nat.toDigits 16 sramRegion.baseAddr)} ({sramRegion.size / 1024}KB)"
  IO.println s!"    Total mapped: {mm.totalSize / 1024}KB"

  -- Linker script model
  IO.println "  Linker Script:"
  let ls : LinkerScript :=
    { sections := [
        { name := ".text", lma := 0x08000000, vma := 0x08000000, size := 8192, flags := .text }
      , { name := ".rodata", lma := 0x08002000, vma := 0x08002000, size := 1024, flags := .rodata }
      , { name := ".data", lma := 0x08002400, vma := 0x20000000, size := 256, flags := .data }
      , { name := ".bss", lma := 0, vma := 0x20000100, size := 512, flags := .bss }
      ]
      symbols := [
        { name := "_start", addr := 0x08000000, sectionName := ".text" }
      , { name := "__stack_top", addr := 0x20020000, sectionName := "" }
      ]
      entryPoint := "_start"
      platform := .aarch64 }
  IO.println s!"    Total output: {ls.totalSize} bytes"
  IO.println s!"    Entry: 0x{String.ofList (Nat.toDigits 16 (ls.entryAddr.getD 0))}"

  -- Startup sequence
  IO.println "  Startup Sequence:"
  match generateStartup ls with
  | some actions =>
    IO.println s!"    Generated {actions.length} startup actions"
    IO.println s!"    Valid: {isValidStartupSequence actions}"
  | none =>
    IO.println "    (could not generate startup)"

  -- GC-free analysis
  IO.println "  GC-Free Analysis:"
  let constraint := GCFreeConstraint.default
  let profiles : List AllocProfile := [
    { name := "init_hardware", strategy := .none, maxStack := some 0 }
  , { name := "process_data", strategy := .stack, maxStack := some 2048 }
  , { name := "main_loop", strategy := .static, maxStack := some 512 }
  ]
  let failures := checkModule constraint profiles
  IO.println s!"    Profiles checked: {profiles.length}"
  IO.println s!"    Failures: {failures.length}"
  IO.println s!"    All GC-free compatible: {failures.length == 0}"

  -- Stack analysis
  IO.println "  Stack Analysis:"
  let frames : List StackFrame := [
    { name := "main", localBytes := 32, savedRegs := 16, padding := 0 }
  , { name := "process", localBytes := 128, savedRegs := 32, padding := 0 }
  , { name := "handler", localBytes := 64, savedRegs := 16, padding := 0 }
  ]
  let worst := worstCaseStackDepth frames
  IO.println s!"    Worst-case depth: {worst} bytes"
  IO.println s!"    Within budget: {decide (worst ≤ constraint.maxStackBytes)}"

  -- Address alignment
  IO.println "  Alignment:"
  IO.println s!"    alignUp 0x1001 16 = 0x{String.ofList (Nat.toDigits 16 (alignUp 0x1001 16))}"
  IO.println s!"    alignDown 0x1001 16 = 0x{String.ofList (Nat.toDigits 16 (alignDown 0x1001 16))}"
  IO.println s!"    isAligned 0x1000 16 = {isAligned 0x1000 16}"

  IO.println ""

/-! ================================================================ -/
/-! ## Main                                                          -/
/-! ================================================================ -/

def main : IO Unit := do
  IO.println "Radix Library — Usage Examples"
  IO.println "=============================="
  IO.println ""

  -- Core module demos (built-in)
  exampleWordArith
  exampleSignedInts
  exampleBitwise
  exampleBitScan
  exampleBitFields
  exampleConversions
  exampleByteOrder
  exampleLeb128
  exampleBinaryFormat
  exampleMemoryBuffer
  exampleSystemIO
  exampleConcurrency
  exampleBareMetal

  IO.println "=============================="
  IO.println "Focused Application Examples"
  IO.println "=============================="
  IO.println ""

  -- Individual focused examples
  Examples.Crc32.run
  Examples.IPv4Header.run
  Examples.HexDump.run
  Examples.RingBuffer.run
  Examples.BitFlags.run
  Examples.NetworkPacket.run
  Examples.TinyVM.run
  Examples.Varint.run
  Examples.FirmwareImage.run
  Examples.LockFree.run
  Examples.SystemIO.run

  IO.println ""
  IO.println "=============================="
  IO.println "v0.2.0 Feature Examples"
  IO.println "=============================="
  IO.println ""

  Examples.BitmapDemo.main
  Examples.AlignmentDemo.main
  Examples.MemoryPoolDemo.main
  Examples.NumericDemo.main

  IO.println "All examples completed successfully!"
