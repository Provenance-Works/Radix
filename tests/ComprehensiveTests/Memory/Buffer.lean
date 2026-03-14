import tests.ComprehensiveTests.Framework
import Radix.Memory.Model
import Radix.Bytes.Spec

/-!
# Memory Buffer Tests
## Spec References
- FR-004: Buffer construction, checked read/write, buffer size
-/

open ComprehensiveTests

def runMemoryBufferTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Memory buffer tests..."

  -- ## Construction
  let empty := Radix.Memory.Buffer.empty
  assert (empty.size == 0) "empty size 0"

  let z8 := Radix.Memory.Buffer.zeros 8
  assert (z8.size == 8) "zeros 8 size"

  let z0 := Radix.Memory.Buffer.zeros 0
  assert (z0.size == 0) "zeros 0 size"

  let z64 := Radix.Memory.Buffer.zeros 64
  assert (z64.size == 64) "zeros 64 size"

  let arr := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
  let buf := Radix.Memory.Buffer.ofByteArray arr
  assert (buf.size == 8) "ofByteArray size"

  -- ## CheckedReadU8 / CheckedWriteU8
  -- Read from zeros buffer
  for i in [:8] do
    match Radix.Memory.Buffer.checkedReadU8 z8 i with
    | some v => assert (v.toNat == 0) s!"zeros readU8 [{i}] = 0"
    | none   => assert false s!"zeros readU8 [{i}] should succeed"

  -- Read OOB
  assert (Radix.Memory.Buffer.checkedReadU8 z8 8 == none) "readU8 OOB 8"
  assert (Radix.Memory.Buffer.checkedReadU8 z8 100 == none) "readU8 OOB 100"
  assert (Radix.Memory.Buffer.checkedReadU8 empty 0 == none) "readU8 empty"

  -- Write then read back
  match Radix.Memory.Buffer.checkedWriteU8 z8 3 ⟨0x42⟩ with
  | some buf' =>
    assert (buf'.size == 8) "writeU8 preserves size"
    match Radix.Memory.Buffer.checkedReadU8 buf' 3 with
    | some v => assert (v.toNat == 0x42) "writeU8-readU8 round-trip"
    | none   => assert false "readU8 after write failed"
    -- Other bytes unaffected
    match Radix.Memory.Buffer.checkedReadU8 buf' 0 with
    | some v => assert (v.toNat == 0) "writeU8 doesn't affect other"
    | none   => assert false "readU8 [0] failed"
  | none => assert false "writeU8 to valid offset failed"

  -- Write OOB
  assert (Radix.Memory.Buffer.checkedWriteU8 z8 8 ⟨42⟩ |>.isNone) "writeU8 OOB"

  -- ## CheckedReadU16/WriteU16
  let buf16 := Radix.Memory.Buffer.zeros 16
  match Radix.Memory.Buffer.checkedWriteU16LE buf16 0 ⟨0xABCD⟩ with
  | some b' =>
    match Radix.Memory.Buffer.checkedReadU16LE b' 0 with
    | some v => assert (v == ⟨0xABCD⟩) "u16 LE write-read"
    | none   => assert false "u16 LE read failed"
  | none => assert false "u16 LE write failed"

  match Radix.Memory.Buffer.checkedWriteU16BE buf16 4 ⟨0x1234⟩ with
  | some b' =>
    match Radix.Memory.Buffer.checkedReadU16BE b' 4 with
    | some v => assert (v == ⟨0x1234⟩) "u16 BE write-read"
    | none   => assert false "u16 BE read failed"
  | none => assert false "u16 BE write failed"

  -- Boundary: offset 15 needs 2 bytes, only 1 left
  assert (Radix.Memory.Buffer.checkedReadU16LE buf16 15 == none) "u16 LE read OOB"

  -- ## CheckedReadU32/WriteU32
  match Radix.Memory.Buffer.checkedWriteU32LE buf16 0 ⟨0xDEADBEEF⟩ with
  | some b' =>
    match Radix.Memory.Buffer.checkedReadU32LE b' 0 with
    | some v => assert (v == ⟨0xDEADBEEF⟩) "u32 LE write-read"
    | none   => assert false "u32 LE read failed"
  | none => assert false "u32 LE write failed"

  match Radix.Memory.Buffer.checkedWriteU32BE buf16 8 ⟨0x12345678⟩ with
  | some b' =>
    match Radix.Memory.Buffer.checkedReadU32BE b' 8 with
    | some v => assert (v == ⟨0x12345678⟩) "u32 BE write-read"
    | none   => assert false "u32 BE read failed"
  | none => assert false "u32 BE write failed"

  assert (Radix.Memory.Buffer.checkedReadU32LE buf16 13 == none) "u32 LE read OOB"

  -- ## CheckedReadU64/WriteU64
  match Radix.Memory.Buffer.checkedWriteU64LE buf16 0 ⟨0x0102030405060708⟩ with
  | some b' =>
    match Radix.Memory.Buffer.checkedReadU64LE b' 0 with
    | some v => assert (v == ⟨0x0102030405060708⟩) "u64 LE write-read"
    | none   => assert false "u64 LE read failed"
  | none => assert false "u64 LE write failed"

  match Radix.Memory.Buffer.checkedWriteU64BE buf16 8 ⟨0xCAFEBABEDEADFACE⟩ with
  | some b' =>
    match Radix.Memory.Buffer.checkedReadU64BE b' 8 with
    | some v => assert (v == ⟨0xCAFEBABEDEADFACE⟩) "u64 BE write-read"
    | none   => assert false "u64 BE read failed"
  | none => assert false "u64 BE write failed"

  assert (Radix.Memory.Buffer.checkedReadU64LE buf16 9 == none) "u64 LE read OOB"

  -- ## toByteArray / slice
  let ba := Radix.Memory.Buffer.toByteArray buf
  assert (ba.size == 8) "toByteArray size"

  -- ## LE/BE cross-read: write LE, read BE (should be byte-swapped)
  match Radix.Memory.Buffer.checkedWriteU32LE buf16 0 ⟨0x01020304⟩ with
  | some b' =>
    match Radix.Memory.Buffer.checkedReadU32BE b' 0 with
    | some v => assert (v == ⟨0x04030201⟩) "u32 LE→BE cross-read"
    | none   => assert false "cross-read failed"
  | none => assert false "cross-write failed"

  c.get
