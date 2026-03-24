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

  -- Canonical external ULEB128 example: 624485 -> E5 8E 26
  let enc624485 := Radix.Binary.Leb128.encodeU32 ⟨624485⟩
  assert (enc624485 == ByteArray.mk #[0xE5, 0x8E, 0x26])
    "ULEB128 canonical encoding for 624485"
  match Radix.Binary.Leb128.decodeU32 (ByteArray.mk #[0xE5, 0x8E, 0x26]) 0 with
  | some (v, consumed) =>
    assert (v.toNat == 624485) "ULEB128 canonical decode for 624485"
    assert (consumed == 3) "ULEB128 canonical byte count for 624485"
  | none => assert false "ULEB128 canonical decode for 624485 failed"

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

  -- WebAssembly permits trailing-zero variants within the byte bound.
  match Radix.Binary.Leb128.decodeU32 (ByteArray.mk #[0x03]) 0 with
  | some (v, consumed) =>
    assert (v.toNat == 3) "U32 canonical short encoding for 3"
    assert (consumed == 1) "U32 short encoding byte count for 3"
  | none => assert false "U32 canonical short encoding for 3 failed"
  match Radix.Binary.Leb128.decodeU32 (ByteArray.mk #[0x83, 0x00]) 0 with
  | some (v, consumed) =>
    assert (v.toNat == 3) "U32 trailing-zero encoding for 3"
    assert (consumed == 2) "U32 trailing-zero byte count for 3"
  | none => assert false "U32 trailing-zero encoding for 3 failed"
  assert (Radix.Binary.Leb128.decodeU32 (ByteArray.mk #[0x83, 0x80, 0x80, 0x80, 0x10]) 0 == none)
    "U32 rejects terminal byte with non-zero unused high bits"

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

  -- Canonical external SLEB128 example: -123456 -> C0 BB 78
  let sEncNeg123456 := Radix.Binary.Leb128.encodeS32 (Radix.Int32.fromInt (-123456))
  assert (sEncNeg123456 == ByteArray.mk #[0xC0, 0xBB, 0x78])
    "SLEB128 canonical encoding for -123456"
  match Radix.Binary.Leb128.decodeS32 (ByteArray.mk #[0xC0, 0xBB, 0x78]) 0 with
  | some (v, consumed) =>
    assert (v.toInt == -123456) "SLEB128 canonical decode for -123456"
    assert (consumed == 3) "SLEB128 canonical byte count for -123456"
  | none => assert false "SLEB128 canonical decode for -123456 failed"

  -- WebAssembly accepts sign-extension variants within the byte bound.
  match Radix.Binary.Leb128.decodeS32 (ByteArray.mk #[0x7E]) 0 with
  | some (v, consumed) =>
    assert (v.toInt == -2) "S32 short encoding for -2"
    assert (consumed == 1) "S32 short encoding byte count for -2"
  | none => assert false "S32 short encoding for -2 failed"
  match Radix.Binary.Leb128.decodeS32 (ByteArray.mk #[0xFE, 0x7F]) 0 with
  | some (v, consumed) =>
    assert (v.toInt == -2) "S32 sign-extended encoding for -2"
    assert (consumed == 2) "S32 sign-extended byte count for -2"
  | none => assert false "S32 sign-extended encoding for -2 failed"
  match Radix.Binary.Leb128.decodeS32 (ByteArray.mk #[0xFE, 0xFF, 0x7F]) 0 with
  | some (v, consumed) =>
    assert (v.toInt == -2) "S32 longer sign-extended encoding for -2"
    assert (consumed == 3) "S32 longer sign-extended byte count for -2"
  | none => assert false "S32 longer sign-extended encoding for -2 failed"
  assert (Radix.Binary.Leb128.decodeS32 (ByteArray.mk #[0x80, 0x80, 0x80, 0x80, 0x08]) 0 == none)
    "S32 rejects terminal byte with invalid positive sign extension"
  assert (Radix.Binary.Leb128.decodeS32 (ByteArray.mk #[0x80, 0x80, 0x80, 0x80, 0x77]) 0 == none)
    "S32 rejects terminal byte with invalid negative sign extension"

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
  assert (Radix.Binary.Leb128.decodeS32 ByteArray.empty 0 == none) "decS32 empty"
  assert (Radix.Binary.Leb128.decodeS32 (ByteArray.mk #[0x80]) 0 == none) "decS32 truncated"

  c.get
