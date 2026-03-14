import tests.ComprehensiveTests.Framework
import Radix.Bytes.Slice

/-!
# ByteSlice Tests
## Spec References
- FR-003: ByteSlice construction, checked read/write, slicing
-/

open ComprehensiveTests

def runBytesSliceTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Bytes slice tests..."

  -- ## Construction
  let empty := Radix.ByteSlice.empty
  assert (empty.size == 0) "empty size"
  assert (empty.isEmpty == true) "empty isEmpty"

  let z4 := Radix.ByteSlice.zeros 4
  assert (z4.size == 4) "zeros 4 size"
  assert (z4.isEmpty == false) "zeros 4 not empty"

  let z0 := Radix.ByteSlice.zeros 0
  assert (z0.size == 0) "zeros 0 size"
  assert (z0.isEmpty == true) "zeros 0 isEmpty"

  let arr := ByteArray.mk #[1, 2, 3, 4, 5]
  let sl := Radix.ByteSlice.ofByteArray arr
  assert (sl.size == 5) "ofByteArray size"

  let fromList := Radix.ByteSlice.ofList [10, 20, 30]
  assert (fromList.size == 3) "ofList size"

  -- ## Checked ReadU8 / WriteU8
  -- Read from zeros: all bytes should be 0
  for i in [:4] do
    match Radix.ByteSlice.checkedReadU8 z4 i with
    | some v => assert (v == 0) s!"zeros read [{i}] = 0"
    | none   => assert false s!"zeros read [{i}] should succeed"

  -- Read out-of-bounds: should return none
  assert (Radix.ByteSlice.checkedReadU8 z4 4 == none) "read OOB 4"
  assert (Radix.ByteSlice.checkedReadU8 z4 100 == none) "read OOB 100"
  assert (Radix.ByteSlice.checkedReadU8 empty 0 == none) "read empty"

  -- Write then read back
  match Radix.ByteSlice.checkedWriteU8 z4 0 42 with
  | some s' =>
    assert (s'.size == 4) "write preserves size"
    match Radix.ByteSlice.checkedReadU8 s' 0 with
    | some v => assert (v == 42) "write-read round-trip"
    | none   => assert false "read after write failed"
    -- Other bytes unchanged
    match Radix.ByteSlice.checkedReadU8 s' 1 with
    | some v => assert (v == 0) "write doesn't affect other bytes"
    | none   => assert false "read [1] failed"
  | none => assert false "write to valid offset failed"

  -- Write out-of-bounds
  assert (Radix.ByteSlice.checkedWriteU8 z4 4 42 == none) "write OOB"

  -- ## Checked ReadU16 / WriteU16
  let buf8 := Radix.ByteSlice.zeros 8
  -- Write u16 LE at offset 0
  match Radix.ByteSlice.checkedWriteU16 buf8 0 ⟨0x0102⟩ Radix.Bytes.Spec.Endian.little with
  | some s' =>
    match Radix.ByteSlice.checkedReadU16 s' 0 Radix.Bytes.Spec.Endian.little with
    | some v => assert (v == ⟨0x0102⟩) "u16 LE write-read round-trip"
    | none   => assert false "u16 LE read failed"
  | none => assert false "u16 LE write failed"

  -- Write u16 BE at offset 2
  match Radix.ByteSlice.checkedWriteU16 buf8 2 ⟨0xABCD⟩ Radix.Bytes.Spec.Endian.big with
  | some s' =>
    match Radix.ByteSlice.checkedReadU16 s' 2 Radix.Bytes.Spec.Endian.big with
    | some v => assert (v == ⟨0xABCD⟩) "u16 BE write-read round-trip"
    | none   => assert false "u16 BE read failed"
  | none => assert false "u16 BE write failed"

  -- Boundary: u16 at offset 7 needs 2 bytes but only 1 available
  assert (Radix.ByteSlice.checkedReadU16 buf8 7 Radix.Bytes.Spec.Endian.little == none)
    "u16 read OOB"

  -- ## Checked ReadU32 / WriteU32
  match Radix.ByteSlice.checkedWriteU32 buf8 0 ⟨0xDEADBEEF⟩ Radix.Bytes.Spec.Endian.little with
  | some s' =>
    match Radix.ByteSlice.checkedReadU32 s' 0 Radix.Bytes.Spec.Endian.little with
    | some v => assert (v == ⟨0xDEADBEEF⟩) "u32 LE write-read"
    | none   => assert false "u32 LE read failed"
  | none => assert false "u32 LE write failed"

  match Radix.ByteSlice.checkedWriteU32 buf8 4 ⟨0x12345678⟩ Radix.Bytes.Spec.Endian.big with
  | some s' =>
    match Radix.ByteSlice.checkedReadU32 s' 4 Radix.Bytes.Spec.Endian.big with
    | some v => assert (v == ⟨0x12345678⟩) "u32 BE write-read"
    | none   => assert false "u32 BE read failed"
  | none => assert false "u32 BE write failed"

  assert (Radix.ByteSlice.checkedReadU32 buf8 5 Radix.Bytes.Spec.Endian.little == none)
    "u32 read OOB"

  -- ## Checked ReadU64 / WriteU64
  match Radix.ByteSlice.checkedWriteU64 buf8 0 ⟨0x0102030405060708⟩
    Radix.Bytes.Spec.Endian.little with
  | some s' =>
    match Radix.ByteSlice.checkedReadU64 s' 0 Radix.Bytes.Spec.Endian.little with
    | some v => assert (v == ⟨0x0102030405060708⟩) "u64 LE write-read"
    | none   => assert false "u64 LE read failed"
  | none => assert false "u64 LE write failed"

  assert (Radix.ByteSlice.checkedReadU64 buf8 1 Radix.Bytes.Spec.Endian.little == none)
    "u64 read OOB"

  -- ## Subslicing
  let buf10 := Radix.ByteSlice.zeros 10
  match Radix.ByteSlice.checkedSubslice buf10 2 4 with
  | some sub =>
    assert (sub.size == 4) "subslice size"
  | none => assert false "subslice failed"

  -- Subslice of full range
  match Radix.ByteSlice.checkedSubslice buf10 0 10 with
  | some sub =>
    assert (sub.size == 10) "subslice full range"
  | none => assert false "subslice full range failed"

  -- Subslice empty
  match Radix.ByteSlice.checkedSubslice buf10 5 0 with
  | some sub =>
    assert (sub.size == 0) "subslice empty"
    assert (sub.isEmpty == true) "subslice empty isEmpty"
  | none => assert false "subslice empty failed"

  -- Subslice OOB
  assert (Radix.ByteSlice.checkedSubslice buf10 8 5 == none) "subslice OOB"

  -- ## toByteArray / toList conversion
  let conv := Radix.ByteSlice.ofList [10, 20, 30]
  let ba := Radix.ByteSlice.toByteArray conv
  assert (ba.size == 3) "toByteArray size"
  let lst := Radix.ByteSlice.toList conv
  assert (lst.length == 3) "toList length"

  -- ## BEq instance
  let a := Radix.ByteSlice.ofList [1, 2, 3]
  let b := Radix.ByteSlice.ofList [1, 2, 3]
  let d := Radix.ByteSlice.ofList [1, 2, 4]
  assert (a == b) "BEq equal"
  assert (!(a == d)) "BEq not equal"

  -- ## Multi-write with different endians
  let buf16 := Radix.ByteSlice.zeros 16
  -- Write u32 LE, then read as BE (should differ for non-palindrome values)
  match Radix.ByteSlice.checkedWriteU32 buf16 0 ⟨0x01020304⟩ Radix.Bytes.Spec.Endian.little with
  | some s' =>
    match Radix.ByteSlice.checkedReadU32 s' 0 Radix.Bytes.Spec.Endian.big with
    | some v => assert (v == ⟨0x04030201⟩) "u32 LE→BE cross-read"
    | none   => assert false "cross-read failed"
  | none => assert false "cross-write failed"

  c.get
