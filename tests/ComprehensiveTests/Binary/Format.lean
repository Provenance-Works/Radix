import tests.ComprehensiveTests.Framework
import Radix.Binary.Format
import Radix.Binary.Parser
import Radix.Binary.Serial

/-!
# Binary Format Tests
## Spec References
- FR-005: Binary Format DSL, fixedSize, fieldNames, parse/serialize
-/

open ComprehensiveTests

def runBinaryFormatTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Binary format tests..."

  -- ## Format fixedSize
  assert (Radix.Binary.Format.fixedSize (.byte "x") == some 1) "byte fixedSize"
  assert (Radix.Binary.Format.fixedSize (.uint16 "x" .little) == some 2) "u16 fixedSize"
  assert (Radix.Binary.Format.fixedSize (.uint32 "x" .big) == some 4) "u32 fixedSize"
  assert (Radix.Binary.Format.fixedSize (.uint64 "x" .little) == some 8) "u64 fixedSize"
  assert (Radix.Binary.Format.fixedSize (.padding 3) == some 3) "padding fixedSize"
  assert (Radix.Binary.Format.fixedSize (.padding 0) == some 0) "padding 0 fixedSize"

  -- ## Format seq fixedSize
  let seqFmt := Radix.Binary.Format.seq (.byte "a") (.byte "b")
  match Radix.Binary.Format.fixedSize seqFmt with
  | some n => assert (n == 2) "seq byte+byte fixedSize"
  | none   => assert false "seq fixedSize is none"

  let seqFmt2 := Radix.Binary.Format.seq (.uint32 "x" .little)
    (Radix.Binary.Format.seq (.uint16 "y" .big) (.byte "z"))
  match Radix.Binary.Format.fixedSize seqFmt2 with
  | some n => assert (n == 7) "seq u32+u16+byte fixedSize"
  | none   => assert false "seq multi fixedSize none"

  -- ## DSL helpers
  match Radix.Binary.Format.fixedSize (Radix.Binary.Format.u16le "x") with
  | some n => assert (n == 2) "u16le DSL fixedSize"
  | none   => assert false "u16le DSL none"

  match Radix.Binary.Format.fixedSize (Radix.Binary.Format.u32be "x") with
  | some n => assert (n == 4) "u32be DSL fixedSize"
  | none   => assert false "u32be DSL none"

  match Radix.Binary.Format.fixedSize (Radix.Binary.Format.u64le "x") with
  | some n => assert (n == 8) "u64le DSL fixedSize"
  | none   => assert false "u64le DSL none"

  -- ## Format fieldNames
  assert (Radix.Binary.Format.fieldNames (.byte "x") == ["x"]) "byte fieldNames"
  assert (Radix.Binary.Format.fieldNames (.padding 5) == []) "padding fieldNames"
  let seqNames := Radix.Binary.Format.fieldNames
    (Radix.Binary.Format.seq (.byte "a") (.byte "b"))
  assert (seqNames.length == 2) "seq fieldNames count"

  -- ## Format fieldCount
  assert (Radix.Binary.Format.fieldCount (.byte "x") == 1) "byte fieldCount"
  assert (Radix.Binary.Format.fieldCount (.padding 5) == 0) "padding fieldCount"
  assert (Radix.Binary.Format.fieldCount
    (Radix.Binary.Format.seq (.byte "a") (.byte "b")) == 2) "seq fieldCount"

  -- ## Parse single byte
  let data1 := ByteArray.mk #[0x42]
  match Radix.Binary.parseFormat data1 (.byte "x") with
  | .ok fields =>
    assert (fields.length == 1) "parse byte field count"
    match fields.head? with
    | some (.byte name val) =>
      assert (name == "x") "parse byte field name"
      assert (val.toNat == 0x42) "parse byte field value"
    | _ => assert false "parse byte wrong variant"
  | .error e => assert false s!"parse byte error: {e}"

  -- ## Parse uint16 LE
  let data2 := ByteArray.mk #[0xCD, 0xAB]  -- LE: 0xABCD
  match Radix.Binary.parseFormat data2 (.uint16 "val" .little) with
  | .ok fields =>
    match fields.head? with
    | some (.uint16 _ val) => assert (val.toNat == 0xABCD) "parse u16 LE"
    | _ => assert false "parse u16 wrong variant"
  | .error e => assert false s!"parse u16 error: {e}"

  -- ## Parse uint32 BE
  let data4 := ByteArray.mk #[0x12, 0x34, 0x56, 0x78]
  match Radix.Binary.parseFormat data4 (.uint32 "val" .big) with
  | .ok fields =>
    match fields.head? with
    | some (.uint32 _ val) => assert (val.toNat == 0x12345678) "parse u32 BE"
    | _ => assert false "parse u32 wrong variant"
  | .error e => assert false s!"parse u32 error: {e}"

  -- ## Parse padding: no fields emitted
  let data3 := ByteArray.mk #[0, 0, 0]
  match Radix.Binary.parseFormat data3 (.padding 3) with
  | .ok fields => assert (fields.length == 0) "parse padding empty"
  | .error e => assert false s!"parse padding error: {e}"

  -- ## Parse out-of-bounds
  let dataShort := ByteArray.mk #[0x00]
  match Radix.Binary.parseFormat dataShort (.uint32 "x" .little) with
  | .ok _     => assert false "parse OOB should fail"
  | .error _  => assert true "parse OOB error"

  -- ## Serialize single byte
  let byteFields := [Radix.Binary.FieldValue.byte "x" ⟨0x42⟩]
  match Radix.Binary.serializeFormat (.byte "x") byteFields with
  | .ok ba =>
    assert (ba.size == 1) "serialize byte size"
    assert (ba.get! 0 == 0x42) "serialize byte value"
  | .error e => assert false s!"serialize byte error: {e}"

  -- ## Serialize uint16 LE
  let u16Fields := [Radix.Binary.FieldValue.uint16 "val" ⟨0xABCD⟩]
  match Radix.Binary.serializeFormat (.uint16 "val" .little) u16Fields with
  | .ok ba =>
    assert (ba.size == 2) "serialize u16 size"
  | .error e => assert false s!"serialize u16 error: {e}"

  -- ## Parse-Serialize Round-Trip
  -- Build format: byte "magic" ++ u16le "len" ++ u32be "data"
  let fmt := Radix.Binary.Format.seq (.byte "magic")
    (Radix.Binary.Format.seq (.uint16 "len" .little) (.uint32 "data" .big))
  let fields := [
    Radix.Binary.FieldValue.byte "magic" ⟨0xFF⟩,
    Radix.Binary.FieldValue.uint16 "len" ⟨0x0007⟩,
    Radix.Binary.FieldValue.uint32 "data" ⟨0xDEADBEEF⟩
  ]
  match Radix.Binary.serializeFormat fmt fields with
  | .ok ba =>
    assert (ba.size == 7) "roundtrip serialize size"
    match Radix.Binary.parseFormat ba fmt with
    | .ok parsedFields =>
      assert (parsedFields.length == 3) "roundtrip parse field count"
      -- Verify each field
      match parsedFields with
      | [.byte _ v1, .uint16 _ v2, .uint32 _ v3] =>
        assert (v1.toNat == 0xFF) "roundtrip magic"
        assert (v2.toNat == 0x0007) "roundtrip len"
        assert (v3.toNat == 0xDEADBEEF) "roundtrip data"
      | _ => assert false "roundtrip field mismatch"
    | .error e => assert false s!"roundtrip parse error: {e}"
  | .error e => assert false s!"roundtrip serialize error: {e}"

  -- ## Serialize error: missing field
  match Radix.Binary.serializeFormat (.byte "missing") [] with
  | .ok _    => assert false "missing field should error"
  | .error _ => assert true "missing field errors"

  -- ## FormatSpec conversion
  let spec := Radix.Binary.Format.toFormatSpec (.byte "x")
  assert (spec.totalSize == 1) "toFormatSpec byte totalSize"

  let spec2 := Radix.Binary.Format.toFormatSpec fmt
  assert (spec2.totalSize == 7) "toFormatSpec complex totalSize"

  c.get
