import tests.ComprehensiveTests.Framework
import Radix.Binary.Leb128
import Radix.Word.Arith
import Radix.Word.Int

/-!
# LEB128 Encoding/Decoding Tests
## Spec References
- FR-005: LEB128 unsigned and signed encode/decode round-trips
-/

open ComprehensiveTests

def runBinaryLeb128Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Binary LEB128 tests..."

  -- ## Unsigned U32 encode/decode round-trip
  -- Zero
  let enc0 := Radix.Binary.Leb128.encodeU32 ⟨0⟩
  assert (enc0.size ≥ 1) "encU32(0) size ≥ 1"
  assert (enc0.size ≤ 5) "encU32(0) size ≤ 5"
  match Radix.Binary.Leb128.decodeU32 enc0 0 with
  | some (v, consumed) =>
    assert (v.toNat == 0) "decU32(encU32(0)) = 0"
    assert (consumed == enc0.size) "consumed == encoded size"
  | none => assert false "decU32(encU32(0)) failed"

  -- Small values: 1-byte encoding
  for n in [1, 42, 127] do
    let enc := Radix.Binary.Leb128.encodeU32 ⟨n.toUInt32⟩
    assert (enc.size == 1) s!"encU32({n}) size 1"
    match Radix.Binary.Leb128.decodeU32 enc 0 with
    | some (v, _) => assert (v.toNat == n) s!"U32 rt {n}"
    | none => assert false s!"decU32({n}) failed"

  -- 128: should need 2 bytes
  let enc128 := Radix.Binary.Leb128.encodeU32 ⟨128⟩
  assert (enc128.size == 2) "encU32(128) size 2"
  match Radix.Binary.Leb128.decodeU32 enc128 0 with
  | some (v, _) => assert (v.toNat == 128) "U32 rt 128"
  | none => assert false "decU32(128) failed"

  -- Larger values
  for n in [255, 256, 1000, 16384, 65535, 1000000] do
    let enc := Radix.Binary.Leb128.encodeU32 ⟨n.toUInt32⟩
    assert (enc.size ≤ 5) s!"encU32({n}) ≤ 5"
    match Radix.Binary.Leb128.decodeU32 enc 0 with
    | some (v, _) => assert (v.toNat == n) s!"U32 rt {n}"
    | none => assert false s!"decU32({n}) failed"

  -- Max U32
  let encMax := Radix.Binary.Leb128.encodeU32 ⟨0xFFFFFFFF⟩
  assert (encMax.size == 5) "encU32(MAX) size 5"
  match Radix.Binary.Leb128.decodeU32 encMax 0 with
  | some (v, _) => assert (v.toNat == 0xFFFFFFFF) "U32 rt MAX"
  | none => assert false "decU32(MAX) failed"

  -- ## Unsigned U64 encode/decode round-trip
  for n in [0, 1, 127, 128, 255, 65535, 0xFFFFFFFF] do
    let enc := Radix.Binary.Leb128.encodeU64 ⟨n.toUInt64⟩
    assert (enc.size ≤ 10) s!"encU64({n}) ≤ 10"
    match Radix.Binary.Leb128.decodeU64 enc 0 with
    | some (v, _) => assert (v.toNat == n) s!"U64 rt {n}"
    | none => assert false s!"decU64({n}) failed"

  -- Max U64
  let encMax64 := Radix.Binary.Leb128.encodeU64 ⟨0xFFFFFFFFFFFFFFFF⟩
  assert (encMax64.size == 10) "encU64(MAX) size 10"
  match Radix.Binary.Leb128.decodeU64 encMax64 0 with
  | some (v, _) => assert (v.toNat == 0xFFFFFFFFFFFFFFFF) "U64 rt MAX"
  | none => assert false "decU64(MAX) failed"

  -- ## Signed S32 encode/decode round-trip
  -- Zero
  let sEnc0 := Radix.Binary.Leb128.encodeS32 (0 : Radix.Int32)
  match Radix.Binary.Leb128.decodeS32 sEnc0 0 with
  | some (v, _) => assert (v.toInt == 0) "S32 rt 0"
  | none => assert false "decS32(0) failed"

  -- Positive
  for n in [1, 42, 127, 128, 1000, 32767] do
    let enc := Radix.Binary.Leb128.encodeS32 (Radix.Int32.fromInt n)
    assert (enc.size ≤ 5) s!"encS32({n}) ≤ 5"
    match Radix.Binary.Leb128.decodeS32 enc 0 with
    | some (v, _) => assert (v.toInt == n) s!"S32 rt {n}"
    | none => assert false s!"decS32({n}) failed"

  -- Negative
  for n in [(-1 : Int), -42, -128, -129, -1000, -32768] do
    let enc := Radix.Binary.Leb128.encodeS32 (Radix.Int32.fromInt n)
    assert (enc.size ≤ 5) s!"encS32({n}) ≤ 5"
    match Radix.Binary.Leb128.decodeS32 enc 0 with
    | some (v, _) => assert (v.toInt == n) s!"S32 rt {n}"
    | none => assert false s!"decS32({n}) failed"

  -- Min S32: -2147483648
  let sEncMin := Radix.Binary.Leb128.encodeS32 (Radix.Int32.fromInt (-2147483648))
  match Radix.Binary.Leb128.decodeS32 sEncMin 0 with
  | some (v, _) => assert (v.toInt == -2147483648) "S32 rt MIN"
  | none => assert false "decS32(MIN) failed"

  -- Max S32: 2147483647
  let sEncMax := Radix.Binary.Leb128.encodeS32 (Radix.Int32.fromInt 2147483647)
  match Radix.Binary.Leb128.decodeS32 sEncMax 0 with
  | some (v, _) => assert (v.toInt == 2147483647) "S32 rt MAX"
  | none => assert false "decS32(MAX) failed"

  -- ## Signed S64 encode/decode round-trip
  for n in [(0 : Int), 1, -1, 127, -128, 32767, -32768, 2147483647, -2147483648] do
    let enc := Radix.Binary.Leb128.encodeS64 (Radix.Int64.fromInt n)
    assert (enc.size ≤ 10) s!"encS64({n}) ≤ 10"
    match Radix.Binary.Leb128.decodeS64 enc 0 with
    | some (v, _) => assert (v.toInt == n) s!"S64 rt {n}"
    | none => assert false s!"decS64({n}) failed"

  -- ## Decode with offset
  -- Prepend garbage bytes and decode at correct offset
  let enc42 := Radix.Binary.Leb128.encodeU32 ⟨42⟩
  let withPrefix := ByteArray.mk #[0xFF, 0xFF] ++ enc42
  match Radix.Binary.Leb128.decodeU32 withPrefix 2 with
  | some (v, _) => assert (v.toNat == 42) "U32 decode at offset"
  | none => assert false "U32 decode at offset failed"

  -- ## Decode from empty / truncated data
  assert (Radix.Binary.Leb128.decodeU32 ByteArray.empty 0 == none) "decU32 empty"
  assert (Radix.Binary.Leb128.decodeU32 (ByteArray.mk #[0x80]) 0 == none) "decU32 truncated"

  c.get
