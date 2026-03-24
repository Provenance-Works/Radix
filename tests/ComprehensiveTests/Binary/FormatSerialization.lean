import tests.ComprehensiveTests.Framework
import Radix.Binary.Format
import Radix.Binary.Parser
import Radix.Binary.Serial

/-!
# Binary Format Serialization Tests
-/

open ComprehensiveTests

def runBinaryFormatSerializationTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c

  let bytesData := ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF]
  let prefixedData := ByteArray.mk #[0x04, 0x00, 0xDE, 0xAD, 0xBE, 0xEF]
  let prefixedFmt := Radix.Binary.Format.lengthPrefixedBytes "payload" 2 .little
  let countedFmt := Radix.Binary.Format.countPrefixedArray "items" 1 .little (.byte "item")
  let arrayFmt := Radix.Binary.Format.array "items" 3 (.byte "item")
  let alignSeqFmt := Radix.Binary.Format.seq (.byte "tag")
    (Radix.Binary.Format.seq (.align 4) (.uint32 "payload" .little))

  let byteFields := [Radix.Binary.FieldValue.byte "x" ⟨0x42⟩]
  match Radix.Binary.serializeFormat (.byte "x") byteFields with
  | .ok ba =>
    assert (ba.size == 1) "serialize byte size"
    assert (ba.get! 0 == 0x42) "serialize byte value"
  | .error e => assert false s!"serialize byte error: {e}"

  let u16Fields := [Radix.Binary.FieldValue.uint16 "val" ⟨0xABCD⟩]
  match Radix.Binary.serializeFormat (.uint16 "val" .little) u16Fields with
  | .ok ba => assert (ba.size == 2) "serialize u16 size"
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

  let fmt := Radix.Binary.Format.seq (.byte "magic")
    (Radix.Binary.Format.seq (.uint16 "len" .little) (.uint32 "data" .big))
  let fields :=
    [ Radix.Binary.FieldValue.byte "magic" ⟨0xFF⟩
    , Radix.Binary.FieldValue.uint16 "len" ⟨0x0007⟩
    , Radix.Binary.FieldValue.uint32 "data" ⟨0xDEADBEEF⟩
    ]
  match Radix.Binary.serializeFormat fmt fields with
  | .ok ba =>
    assert (ba.size == 7) "roundtrip serialize size"
    match Radix.Binary.parseFormat ba fmt with
    | .ok parsedFields =>
      assert (parsedFields.length == 3) "roundtrip parse field count"
      match parsedFields with
      | [.byte _ v1, .uint16 _ v2, .uint32 _ v3] =>
        assert (v1.toNat == 0xFF) "roundtrip magic"
        assert (v2.toNat == 0x0007) "roundtrip len"
        assert (v3.toNat == 0xDEADBEEF) "roundtrip data"
      | _ => assert false "roundtrip field mismatch"
    | .error e => assert false s!"roundtrip parse error: {e}"
  | .error e => assert false s!"roundtrip serialize error: {e}"

  match Radix.Binary.serializeFormat (.byte "missing") [] with
  | .ok _ => assert false "missing field should error"
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

  c.get
