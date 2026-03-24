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
  assert (Radix.Binary.Format.fixedSize (.bytes "blob" 5) == some 5) "bytes fixedSize"
  assert (Radix.Binary.Format.fixedSize (.lengthPrefixedBytes "payload" 2 .little) == none) "lengthPrefixedBytes fixedSize none"
  assert (Radix.Binary.Format.fixedSize (.countPrefixedArray "items" 1 .little (.byte "item")) == none) "countPrefixedArray fixedSize none"
  assert (Radix.Binary.Format.fixedSize (.constBytes (ByteArray.mk #[0x52, 0x44, 0x58, 0x21])) == some 4) "constBytes fixedSize"
  assert (Radix.Binary.Format.fixedSize (.padding 3) == some 3) "padding fixedSize"
  assert (Radix.Binary.Format.fixedSize (.padding 0) == some 0) "padding 0 fixedSize"
  assert (Radix.Binary.Format.fixedSize (.align 4) == some 0) "align fixedSize at offset zero"

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

  let alignSeqFmt := Radix.Binary.Format.seq (.byte "tag")
    (Radix.Binary.Format.seq (.align 4) (.uint32 "payload" .little))
  match Radix.Binary.Format.fixedSize alignSeqFmt with
  | some n => assert (n == 8) "seq align fixedSize"
  | none => assert false "seq align fixedSize none"

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

  let arrayFmt := Radix.Binary.Format.array "items" 3 (.byte "item")
  match Radix.Binary.Format.fixedSize arrayFmt with
  | some n => assert (n == 3) "array fixedSize"
  | none => assert false "array fixedSize none"

  -- ## Format fieldNames
  assert (Radix.Binary.Format.fieldNames (.byte "x") == ["x"]) "byte fieldNames"
  assert (Radix.Binary.Format.fieldNames (.bytes "blob" 2) == ["blob"]) "bytes fieldNames"
  assert (Radix.Binary.Format.fieldNames (.lengthPrefixedBytes "payload" 2 .little) == ["payload"]) "lengthPrefixedBytes fieldNames"
  assert (Radix.Binary.Format.fieldNames (.countPrefixedArray "items" 1 .little (.byte "item")) == ["items", "item"]) "countPrefixedArray fieldNames"
  assert (Radix.Binary.Format.fieldNames (.constBytes (ByteArray.mk #[0xAA, 0x55])) == []) "constBytes fieldNames"
  assert (Radix.Binary.Format.fieldNames (.padding 5) == []) "padding fieldNames"
  assert (Radix.Binary.Format.fieldNames (.align 8) == []) "align fieldNames"
  let seqNames := Radix.Binary.Format.fieldNames
    (Radix.Binary.Format.seq (.byte "a") (.byte "b"))
  assert (seqNames.length == 2) "seq fieldNames count"

  -- ## Format fieldCount
  assert (Radix.Binary.Format.fieldCount (.byte "x") == 1) "byte fieldCount"
  assert (Radix.Binary.Format.fieldCount (.bytes "blob" 2) == 1) "bytes fieldCount"
  assert (Radix.Binary.Format.fieldCount (.lengthPrefixedBytes "payload" 2 .little) == 1) "lengthPrefixedBytes fieldCount"
  assert (Radix.Binary.Format.fieldCount (.countPrefixedArray "items" 1 .little (.byte "item")) == 2) "countPrefixedArray fieldCount"
  assert (Radix.Binary.Format.fieldCount (.constBytes (ByteArray.mk #[0xAA, 0x55]) ) == 0) "constBytes fieldCount"
  assert (Radix.Binary.Format.fieldCount (.padding 5) == 0) "padding fieldCount"
  assert (Radix.Binary.Format.fieldCount (.align 8) == 0) "align fieldCount"
  assert (Radix.Binary.Format.fieldCount
    (Radix.Binary.Format.seq (.byte "a") (.byte "b")) == 2) "seq fieldCount"
  assert (Radix.Binary.Format.fieldCount arrayFmt == 2) "array fieldCount includes wrapper and element"

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

  match Radix.Binary.parsePrefix data1 (.byte "x") with
  | .ok (fields, consumed) =>
    assert (fields.length == 1) "parsePrefix byte field count"
    assert (consumed == 1) "parsePrefix byte consumed"
  | .error e => assert false s!"parsePrefix byte error: {e}"

  match Radix.Binary.parseSplit (ByteArray.mk #[0x42, 0x99]) (.byte "x") with
  | .ok (fields, remainder) =>
    assert (fields.length == 1) "parseSplit byte field count"
    assert (remainder == ByteArray.mk #[0x99]) "parseSplit returns suffix"
  | .error e => assert false s!"parseSplit byte error: {e}"

  match Radix.Binary.parseFormatExact data1 (.byte "x") with
  | .ok fields => assert (fields.length == 1) "parseFormatExact byte succeeds"
  | .error e => assert false s!"parseFormatExact byte error: {e}"

  let bytesData := ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF]
  match Radix.Binary.parseFormatExact bytesData (.bytes "blob" 4) with
  | .ok fields =>
    match fields with
    | [.bytes name value] =>
      assert (name == "blob") "parse bytes field name"
      assert (value == bytesData) "parse bytes field value"
    | _ => assert false "parse bytes wrong variant"
  | .error e => assert false s!"parse bytes error: {e}"

  let prefixedData := ByteArray.mk #[0x04, 0x00, 0xDE, 0xAD, 0xBE, 0xEF]
  let prefixedFmt := Radix.Binary.Format.lengthPrefixedBytes "payload" 2 .little
  let countedFmt := Radix.Binary.Format.countPrefixedArray "items" 1 .little (.byte "item")
  match Radix.Binary.parseFormatExact prefixedData prefixedFmt with
  | .ok fields =>
    match fields with
    | [.bytes name value] =>
      assert (name == "payload") "parse lengthPrefixed field name"
      assert (value == bytesData) "parse lengthPrefixed field value"
    | _ => assert false "parse lengthPrefixed wrong variant"
  | .error e => assert false s!"parse lengthPrefixed error: {e}"

  match Radix.Binary.parseFormatExact bytesData (.constBytes (ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF])) with
  | .ok fields => assert (fields.length == 0) "parse constBytes emits no fields"
  | .error e => assert false s!"parse constBytes error: {e}"

  match Radix.Binary.parseFormatExact bytesData (.constBytes (ByteArray.mk #[0xDE, 0xAD, 0xBE, 0x00])) with
  | .ok _ => assert false "parse constBytes mismatch should fail"
  | .error (.constantMismatch off _ _) => assert (off == 0) "parse constBytes mismatch offset"
  | .error _ => assert false "parse constBytes wrong error"

  match Radix.Binary.parseFormatExact (ByteArray.mk #[0x04, 0x00, 0xDE, 0xAD]) prefixedFmt with
  | .ok _ => assert false "parse lengthPrefixed OOB should fail"
  | .error (.outOfBounds name off need have_) =>
    assert (name == "payload") "parse lengthPrefixed OOB field name"
    assert (off == 2 && need == 4 && have_ == 2) "parse lengthPrefixed OOB metadata"
  | .error _ => assert false "parse lengthPrefixed OOB wrong error"

  match Radix.Binary.parseFormat (ByteArray.mk #[0x00]) (.lengthPrefixedBytes "payload" 3 .little) with
  | .ok _ => assert false "parse unsupported length prefix should fail"
  | .error (.unsupportedLengthPrefix name prefixBytes) =>
    assert (name == "payload") "parse unsupported length prefix field name"
    assert (prefixBytes == 3) "parse unsupported length prefix width"
  | .error _ => assert false "parse unsupported length prefix wrong error"

  match Radix.Binary.parseFormatExact (ByteArray.mk #[0x03, 0x10, 0x20, 0x30]) countedFmt with
  | .ok fields =>
    match fields with
    | [.array name elems] =>
      assert (name == "items") "parse countPrefixedArray field name"
      assert (elems.length == 3) "parse countPrefixedArray length"
      match elems with
      | [[.byte _ v0], [.byte _ v1], [.byte _ v2]] =>
        assert (v0.toNat == 0x10) "parse countPrefixedArray item 0"
        assert (v1.toNat == 0x20) "parse countPrefixedArray item 1"
        assert (v2.toNat == 0x30) "parse countPrefixedArray item 2"
      | _ => assert false "parse countPrefixedArray element layout"
    | _ => assert false "parse countPrefixedArray wrong variant"
  | .error e => assert false s!"parse countPrefixedArray error: {e}"

  match Radix.Binary.parseFormatExact (ByteArray.mk #[0x03, 0x10, 0x20]) countedFmt with
  | .ok _ => assert false "parse countPrefixedArray OOB should fail"
  | .error (.outOfBounds name off need have_) =>
    assert (name == "item") "parse countPrefixedArray OOB field name"
    assert (off == 3 && need == 1 && have_ == 0) "parse countPrefixedArray OOB metadata"
  | .error _ => assert false "parse countPrefixedArray OOB wrong error"

  match Radix.Binary.parseFormat (ByteArray.mk #[0x00]) (.countPrefixedArray "items" 3 .little (.byte "item")) with
  | .ok _ => assert false "parse countPrefixedArray unsupported prefix should fail"
  | .error (.unsupportedLengthPrefix name prefixBytes) =>
    assert (name == "items") "parse countPrefixedArray unsupported prefix field name"
    assert (prefixBytes == 3) "parse countPrefixedArray unsupported prefix width"
  | .error _ => assert false "parse countPrefixedArray unsupported prefix wrong error"

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

  -- ## Parse alignment gap
  let alignData := ByteArray.mk #[0x42, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x12]
  match Radix.Binary.parseFormatExact alignData alignSeqFmt with
  | .ok fields =>
    match fields with
    | [.byte _ tag, .uint32 _ payload] =>
      assert (tag.toNat == 0x42) "parse align tag"
      assert (payload.toNat == 0x12345678) "parse align payload"
    | _ => assert false "parse align wrong variant"
  | .error e => assert false s!"parse align error: {e}"

  -- ## Parse fixed array
  let arrayData := ByteArray.mk #[0x10, 0x20, 0x30]
  match Radix.Binary.parseFormat arrayData arrayFmt with
  | .ok fields =>
    match fields with
    | [.array name elems] =>
      assert (name == "items") "parse array field name"
      assert (elems.length == 3) "parse array element count"
      match elems with
      | [[.byte _ v0], [.byte _ v1], [.byte _ v2]] =>
        assert (v0.toNat == 0x10) "parse array item 0"
        assert (v1.toNat == 0x20) "parse array item 1"
        assert (v2.toNat == 0x30) "parse array item 2"
      | _ => assert false "parse array element layout"
    | _ => assert false "parse array wrong variant"
  | .error e => assert false s!"parse array error: {e}"

  -- ## Parse out-of-bounds
  let dataShort := ByteArray.mk #[0x00]
  match Radix.Binary.parseFormat dataShort (.uint32 "x" .little) with
  | .ok _     => assert false "parse OOB should fail"
  | .error _  => assert true "parse OOB error"

  match Radix.Binary.parseFormat dataShort (.padding 2) with
  | .ok _ => assert false "padding OOB should fail"
  | .error (.outOfBounds name off need have_) =>
    assert (name == "padding") "padding OOB field name"
    assert (off == 0 && need == 2 && have_ == 1) "padding OOB metadata"
  | .error _ => assert false "padding OOB wrong error"

  match Radix.Binary.parseFormat (ByteArray.mk #[0x42, 0x00]) alignSeqFmt with
  | .ok _ => assert false "align OOB should fail"
  | .error (.outOfBounds name off need have_) =>
    assert (name == "align(4)") "align OOB field name"
    assert (off == 1 && need == 3 && have_ == 1) "align OOB metadata"
  | .error _ => assert false "align OOB wrong error"

  match Radix.Binary.parseFormat dataShort arrayFmt with
  | .ok _ => assert false "array OOB should fail"
  | .error (.outOfBounds name _ _ _) =>
    assert (name == "item") "array OOB names failing element"
  | .error _ => assert false "array OOB wrong error"

  match Radix.Binary.parseFormatExact (ByteArray.mk #[0x42, 0x99]) (.byte "x") with
  | .ok _ => assert false "parseFormatExact trailing bytes should fail"
  | .error (.trailingBytes off remaining) =>
    assert (off == 1) "parseFormatExact trailing offset"
    assert (remaining == 1) "parseFormatExact trailing remaining"
  | .error _ => assert false "parseFormatExact trailing wrong error"

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

  let bytesFields := [Radix.Binary.FieldValue.bytes "blob" bytesData]
  match Radix.Binary.serializeFormat (.bytes "blob" 4) bytesFields with
  | .ok ba => assert (ba == bytesData) "serialize bytes blob"
  | .error e => assert false s!"serialize bytes error: {e}"

  let prefixedFields := [Radix.Binary.FieldValue.bytes "payload" bytesData]
  match Radix.Binary.serializeFormat prefixedFmt prefixedFields with
  | .ok ba => assert (ba == prefixedData) "serialize lengthPrefixed blob"
  | .error e => assert false s!"serialize lengthPrefixed error: {e}"

  let countedFields :=
    [Radix.Binary.FieldValue.array "items"
      [ [Radix.Binary.FieldValue.byte "item" ⟨0x10⟩]
      , [Radix.Binary.FieldValue.byte "item" ⟨0x20⟩]
      , [Radix.Binary.FieldValue.byte "item" ⟨0x30⟩]
      ]]
  match Radix.Binary.serializeFormat countedFmt countedFields with
  | .ok ba => assert (ba == ByteArray.mk #[0x03, 0x10, 0x20, 0x30]) "serialize countPrefixedArray bytes"
  | .error e => assert false s!"serialize countPrefixedArray error: {e}"

  match Radix.Binary.serializeFormat (.constBytes (ByteArray.mk #[0x52, 0x44, 0x58, 0x21])) [] with
  | .ok ba => assert (ba == ByteArray.mk #[0x52, 0x44, 0x58, 0x21]) "serialize constBytes emits bytes"
  | .error e => assert false s!"serialize constBytes error: {e}"

  let oversizedPayload := ByteArray.mk (Array.replicate 300 (0xAA : UInt8))
  match Radix.Binary.serializeFormat (Radix.Binary.Format.lengthPrefixedBytes "payload" 1 .little)
    [Radix.Binary.FieldValue.bytes "payload" oversizedPayload] with
  | .ok _ => assert false "serialize lengthPrefixed overflow should fail"
  | .error (.lengthOverflow name prefixBytes actualSize) =>
    assert (name == "payload") "serialize lengthPrefixed overflow field name"
    assert (prefixBytes == 1) "serialize lengthPrefixed overflow width"
    assert (actualSize == 300) "serialize lengthPrefixed overflow size"
  | .error _ => assert false "serialize lengthPrefixed overflow wrong error"

  match Radix.Binary.serializeFormat (Radix.Binary.Format.lengthPrefixedBytes "payload" 3 .little) prefixedFields with
  | .ok _ => assert false "serialize unsupported length prefix should fail"
  | .error (.unsupportedLengthPrefix name prefixBytes) =>
    assert (name == "payload") "serialize unsupported length prefix field name"
    assert (prefixBytes == 3) "serialize unsupported length prefix width"
  | .error _ => assert false "serialize unsupported length prefix wrong error"

  let tooManyItems := List.range 300 |>.map (fun n => [Radix.Binary.FieldValue.byte "item" ⟨n.toUInt8⟩])
  match Radix.Binary.serializeFormat (Radix.Binary.Format.countPrefixedArray "items" 1 .little (.byte "item"))
    [Radix.Binary.FieldValue.array "items" tooManyItems] with
  | .ok _ => assert false "serialize countPrefixedArray overflow should fail"
  | .error (.lengthOverflow name prefixBytes actualSize) =>
    assert (name == "items") "serialize countPrefixedArray overflow field name"
    assert (prefixBytes == 1) "serialize countPrefixedArray overflow prefix width"
    assert (actualSize == 300) "serialize countPrefixedArray overflow size"
  | .error _ => assert false "serialize countPrefixedArray overflow wrong error"

  let headerFmt := Radix.Binary.Format.constBytes (ByteArray.mk #[0x52, 0x44, 0x58, 0x21]) ++
    Radix.Binary.Format.u16le "version"
  let headerData := ByteArray.mk #[0x52, 0x44, 0x58, 0x21, 0x01, 0x00]
  match Radix.Binary.parseFormatExact headerData headerFmt with
  | .ok fields =>
    match fields with
    | [.uint16 name version] =>
      assert (name == "version") "constBytes seq version field name"
      assert (version.toNat == 1) "constBytes seq version value"
    | _ => assert false "constBytes seq wrong parsed fields"
  | .error e => assert false s!"constBytes seq parse error: {e}"

  -- ## Serialize fixed array
  let arrayFields :=
    [Radix.Binary.FieldValue.array "items"
      [ [Radix.Binary.FieldValue.byte "item" ⟨0x10⟩]
      , [Radix.Binary.FieldValue.byte "item" ⟨0x20⟩]
      , [Radix.Binary.FieldValue.byte "item" ⟨0x30⟩]
      ]]
  match Radix.Binary.serializeFormat arrayFmt arrayFields with
  | .ok ba => assert (ba == ByteArray.mk #[0x10, 0x20, 0x30]) "serialize array bytes"
  | .error e => assert false s!"serialize array error: {e}"

  let paddedFmt := Radix.Binary.Format.seq (.byte "tag") (Radix.Binary.Format.seq (.padding 2) (.byte "tail"))
  let paddedFields := [Radix.Binary.FieldValue.byte "tag" ⟨0xAA⟩, Radix.Binary.FieldValue.byte "tail" ⟨0xBB⟩]
  match Radix.Binary.serializeFormat paddedFmt paddedFields with
  | .ok ba => assert (ba == ByteArray.mk #[0xAA, 0x00, 0x00, 0xBB]) "serialize padding emits zeros"
  | .error e => assert false s!"serialize padding error: {e}"

  let alignFields := [Radix.Binary.FieldValue.byte "tag" ⟨0xAA⟩, Radix.Binary.FieldValue.uint32 "payload" ⟨0x12345678⟩]
  match Radix.Binary.serializeFormat alignSeqFmt alignFields with
  | .ok ba => assert (ba == ByteArray.mk #[0xAA, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x12]) "serialize align emits computed zeros"
  | .error e => assert false s!"serialize align error: {e}"

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

  match Radix.Binary.serializeFormat (.byte "x") [Radix.Binary.FieldValue.uint16 "x" ⟨1⟩] with
  | .ok _ => assert false "type mismatch should error"
  | .error (.typeMismatch name expected got) =>
    assert (name == "x") "type mismatch field name"
    assert (expected == "byte") "type mismatch expected type"
    assert (got == "uint16") "type mismatch actual type"
  | .error _ => assert false "type mismatch wrong error"

  match Radix.Binary.serializeFormat (.bytes "blob" 4) [Radix.Binary.FieldValue.bytes "blob" (ByteArray.mk #[0xAA])] with
  | .ok _ => assert false "bytes length mismatch should error"
  | .error (.typeMismatch name expected got) =>
    assert (name == "blob") "bytes length mismatch field name"
    assert (expected == "bytes[4]") "bytes length mismatch expected"
    assert (got == "bytes[1]") "bytes length mismatch got"
  | .error _ => assert false "bytes length mismatch wrong error"

  match Radix.Binary.serializeFormat arrayFmt
    [Radix.Binary.FieldValue.array "items" [[Radix.Binary.FieldValue.byte "item" ⟨0x10⟩]]] with
  | .ok _ => assert false "array length mismatch should error"
  | .error (.typeMismatch name expected got) =>
    assert (name == "items") "array length mismatch field name"
    assert (expected == "array[3]") "array length mismatch expected"
    assert (got == "array[1]") "array length mismatch got"
  | .error _ => assert false "array length mismatch wrong error"

  match Radix.Binary.serializeFormat (.byte "x")
    [Radix.Binary.FieldValue.byte "x" ⟨0xAA⟩, Radix.Binary.FieldValue.byte "y" ⟨0xBB⟩] with
  | .ok _ => assert false "unexpected top-level field should error"
  | .error (.unexpectedField name) => assert (name == "y") "unexpected top-level field name"
  | .error _ => assert false "unexpected top-level field wrong error"

  let duplicateFmt := Radix.Binary.Format.seq (.byte "x") (.byte "x")
  match Radix.Binary.serializeFormat duplicateFmt
    [Radix.Binary.FieldValue.byte "x" ⟨0x11⟩, Radix.Binary.FieldValue.byte "x" ⟨0x22⟩] with
  | .ok ba => assert (ba == ByteArray.mk #[0x11, 0x22]) "duplicate field names consume independently"
  | .error e => assert false s!"duplicate field serialize error: {e}"

  let arrayElemFmt := Radix.Binary.Format.array "items" 1 (Radix.Binary.Format.byte "item")
  match Radix.Binary.serializeFormat arrayElemFmt
    [Radix.Binary.FieldValue.array "items"
      [[Radix.Binary.FieldValue.byte "item" ⟨0x10⟩, Radix.Binary.FieldValue.byte "extra" ⟨0x20⟩]]] with
  | .ok _ => assert false "unexpected nested field should error"
  | .error (.unexpectedField name) => assert (name == "extra") "unexpected nested field name"
  | .error _ => assert false "unexpected nested field wrong error"

  -- ## FormatSpec conversion
  let spec := Radix.Binary.Format.toFormatSpec (.byte "x")
  assert (spec.totalSize == 1) "toFormatSpec byte totalSize"

  let bytesSpec := Radix.Binary.Format.toFormatSpec (.bytes "blob" 4)
  assert (bytesSpec.totalSize == 4) "toFormatSpec bytes totalSize"
  match bytesSpec.fields with
  | [field] =>
    assert (field.name == "blob") "toFormatSpec bytes field name"
    assert (field.offset == 0) "toFormatSpec bytes offset"
  | _ => assert false "toFormatSpec bytes field layout"

  let prefixedSpec := Radix.Binary.Format.toFormatSpec prefixedFmt
  assert (prefixedSpec.totalSize == 2) "toFormatSpec lengthPrefixed min totalSize"
  match prefixedSpec.fields with
  | [field] =>
    assert (field.name == "payload") "toFormatSpec lengthPrefixed field name"
    assert (field.offset == 0) "toFormatSpec lengthPrefixed field offset"
    match field.ftype with
    | .var (.lengthPrefixed prefixBytes endian) =>
      assert (prefixBytes == 2) "toFormatSpec lengthPrefixed width"
      assert (endian == .little) "toFormatSpec lengthPrefixed endian"
    | _ => assert false "toFormatSpec lengthPrefixed field type"
  | _ => assert false "toFormatSpec lengthPrefixed field layout"

  let countedSpec := Radix.Binary.Format.toFormatSpec countedFmt
  assert (countedSpec.totalSize == 1) "toFormatSpec countPrefixedArray min totalSize"
  match countedSpec.fields with
  | [field] =>
    assert (field.name == "items") "toFormatSpec countPrefixedArray field name"
    assert (field.offset == 0) "toFormatSpec countPrefixedArray field offset"
    match field.ftype with
    | .var (.countPrefixedArray prefixBytes endian elemMinSize) =>
      assert (prefixBytes == 1) "toFormatSpec countPrefixedArray prefix width"
      assert (endian == .little) "toFormatSpec countPrefixedArray endian"
      assert (elemMinSize == 1) "toFormatSpec countPrefixedArray elem min size"
    | _ => assert false "toFormatSpec countPrefixedArray field type"
  | _ => assert false "toFormatSpec countPrefixedArray field layout"

  let spec2 := Radix.Binary.Format.toFormatSpec fmt
  assert (spec2.totalSize == 7) "toFormatSpec complex totalSize"

  let alignSpec := Radix.Binary.Format.toFormatSpec alignSeqFmt
  assert (alignSpec.totalSize == 8) "toFormatSpec align totalSize"
  match alignSpec.fields with
  | [f0, f1] =>
    assert (f0.name == "tag" && f0.offset == 0) "align spec first field offset"
    assert (f1.name == "payload" && f1.offset == 4) "align spec aligned field offset"
  | _ => assert false "align spec field layout"

  let arraySpec := Radix.Binary.Format.toFormatSpec arrayFmt
  assert (arraySpec.totalSize == 3) "toFormatSpec array totalSize"
  assert (arraySpec.fields.length == 3) "toFormatSpec array expands elements"

  -- ## Nested sequence/array layout metadata
  let nestedFmt := Radix.Binary.Format.seq
    (Radix.Binary.Format.u16le "len")
    (Radix.Binary.Format.seq
      (Radix.Binary.Format.padding 1)
      (Radix.Binary.Format.array "payload" 2 (Radix.Binary.Format.u16be "word")))
  match Radix.Binary.Format.fixedSize nestedFmt with
  | some n => assert (n == 7) "nested fixedSize"
  | none => assert false "nested fixedSize none"
  let nestedSpec := Radix.Binary.Format.toFormatSpec nestedFmt
  assert (nestedSpec.totalSize == 7) "nested spec total size"
  assert (nestedSpec.fields.length == 3) "nested spec field expansion count"
  match nestedSpec.fields with
  | [f0, f1, f2] =>
    assert (f0.name == "len" && f0.offset == 0) "nested spec first field offset"
    assert (f1.name == "word" && f1.offset == 3) "nested spec second field offset"
    assert (f2.name == "word" && f2.offset == 5) "nested spec third field offset"
  | _ => assert false "nested spec field layout"

  let nestedData := ByteArray.mk #[0x02, 0x00, 0x00, 0x12, 0x34, 0x56, 0x78]
  match Radix.Binary.parseFormat nestedData nestedFmt with
  | .ok parsed =>
    match parsed with
    | [.uint16 _ len, .array name elems] =>
      assert (len.toNat == 2) "nested parse length field"
      assert (name == "payload") "nested parse array name"
      match elems with
      | [[.uint16 _ first], [.uint16 _ second]] =>
        assert (first.toNat == 0x1234) "nested parse first element"
        assert (second.toNat == 0x5678) "nested parse second element"
      | _ => assert false "nested parse element layout"
    | _ => assert false "nested parse outer layout"
  | .error e => assert false s!"nested parse error: {e}"

  let nestedFields :=
    [ Radix.Binary.FieldValue.uint16 "len" ⟨2⟩
    , Radix.Binary.FieldValue.array "payload"
        [ [Radix.Binary.FieldValue.uint16 "word" ⟨0x1234⟩]
        , [Radix.Binary.FieldValue.uint16 "word" ⟨0x5678⟩]
        ]
    ]
  match Radix.Binary.serializeFormat nestedFmt nestedFields with
  | .ok ba => assert (ba == nestedData) "nested serialize emits expected bytes"
  | .error e => assert false s!"nested serialize error: {e}"

  match Radix.Binary.serializeFormat nestedFmt [Radix.Binary.FieldValue.uint16 "len" ⟨2⟩] with
  | .ok _ => assert false "missing nested array should fail"
  | .error (.missingField name) => assert (name == "payload") "missing nested array name"
  | .error _ => assert false "missing nested array wrong error"

  let nestedShort := ByteArray.mk #[0x02, 0x00, 0x00, 0x12]
  match Radix.Binary.parseFormat nestedShort nestedFmt with
  | .ok _ => assert false "nested OOB should fail"
  | .error (.outOfBounds name off need have_) =>
    assert (name == "word") "nested OOB failing field name"
    assert (off == 3 || off == 5) "nested OOB offset tracks failing element"
    assert (need == 2) "nested OOB need size"
    assert (have_ < 2) "nested OOB remaining bytes"
  | .error _ => assert false "nested OOB wrong error"

  let nestedExtra := nestedData ++ ByteArray.mk #[0xFF]
  match Radix.Binary.parsePrefix nestedExtra nestedFmt with
  | .ok (_, consumed) => assert (consumed == nestedData.size) "nested parsePrefix reports consumed size"
  | .error e => assert false s!"nested parsePrefix error: {e}"

  match Radix.Binary.parseSplit nestedExtra nestedFmt with
  | .ok (_, remainder) => assert (remainder == ByteArray.mk #[0xFF]) "nested parseSplit returns trailing suffix"
  | .error e => assert false s!"nested parseSplit error: {e}"

  match Radix.Binary.parseFormatExact nestedExtra nestedFmt with
  | .ok _ => assert false "nested parseFormatExact trailing bytes should fail"
  | .error (.trailingBytes off remaining) =>
    assert (off == nestedData.size) "nested parseFormatExact trailing offset"
    assert (remaining == 1) "nested parseFormatExact trailing remaining"
  | .error _ => assert false "nested parseFormatExact trailing wrong error"

  c.get
