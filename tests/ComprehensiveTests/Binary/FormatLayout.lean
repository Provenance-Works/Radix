import tests.ComprehensiveTests.Framework
import Radix.Binary.Format
import Radix.Binary.Parser
import Radix.Binary.Serial

/-!
# Binary Format Layout Tests
-/

open ComprehensiveTests

def runBinaryFormatLayoutTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c

  let prefixedFmt := Radix.Binary.Format.lengthPrefixedBytes "payload" 2 .little
  let countedFmt := Radix.Binary.Format.countPrefixedArray "items" 1 .little (.byte "item")
  let alignSeqFmt := Radix.Binary.Format.seq (.byte "tag")
    (Radix.Binary.Format.seq (.align 4) (.uint32 "payload" .little))
  let arrayFmt := Radix.Binary.Format.array "items" 3 (.byte "item")

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

  let fmt := Radix.Binary.Format.seq (.byte "magic")
    (Radix.Binary.Format.seq (.uint16 "len" .little) (.uint32 "data" .big))
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
