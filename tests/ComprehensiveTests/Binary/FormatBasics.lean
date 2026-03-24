import tests.ComprehensiveTests.Framework
import Radix.Binary.Format
import Radix.Binary.Parser

/-!
# Binary Format Basics Tests
-/

open ComprehensiveTests

def runBinaryFormatBasicsTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c

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

  let seqFmt := Radix.Binary.Format.seq (.byte "a") (.byte "b")
  match Radix.Binary.Format.fixedSize seqFmt with
  | some n => assert (n == 2) "seq byte+byte fixedSize"
  | none => assert false "seq fixedSize is none"

  let seqFmt2 := Radix.Binary.Format.seq (.uint32 "x" .little)
    (Radix.Binary.Format.seq (.uint16 "y" .big) (.byte "z"))
  match Radix.Binary.Format.fixedSize seqFmt2 with
  | some n => assert (n == 7) "seq u32+u16+byte fixedSize"
  | none => assert false "seq multi fixedSize none"

  let alignSeqFmt := Radix.Binary.Format.seq (.byte "tag")
    (Radix.Binary.Format.seq (.align 4) (.uint32 "payload" .little))
  match Radix.Binary.Format.fixedSize alignSeqFmt with
  | some n => assert (n == 8) "seq align fixedSize"
  | none => assert false "seq align fixedSize none"

  match Radix.Binary.Format.fixedSize (Radix.Binary.Format.u16le "x") with
  | some n => assert (n == 2) "u16le DSL fixedSize"
  | none => assert false "u16le DSL none"

  match Radix.Binary.Format.fixedSize (Radix.Binary.Format.u32be "x") with
  | some n => assert (n == 4) "u32be DSL fixedSize"
  | none => assert false "u32be DSL none"

  match Radix.Binary.Format.fixedSize (Radix.Binary.Format.u64le "x") with
  | some n => assert (n == 8) "u64le DSL fixedSize"
  | none => assert false "u64le DSL none"

  let arrayFmt := Radix.Binary.Format.array "items" 3 (.byte "item")
  match Radix.Binary.Format.fixedSize arrayFmt with
  | some n => assert (n == 3) "array fixedSize"
  | none => assert false "array fixedSize none"

  assert (Radix.Binary.Format.fieldNames (.byte "x") == ["x"]) "byte fieldNames"
  assert (Radix.Binary.Format.fieldNames (.bytes "blob" 2) == ["blob"]) "bytes fieldNames"
  assert (Radix.Binary.Format.fieldNames (.lengthPrefixedBytes "payload" 2 .little) == ["payload"]) "lengthPrefixedBytes fieldNames"
  assert (Radix.Binary.Format.fieldNames (.countPrefixedArray "items" 1 .little (.byte "item")) == ["items", "item"]) "countPrefixedArray fieldNames"
  assert (Radix.Binary.Format.fieldNames (.constBytes (ByteArray.mk #[0xAA, 0x55])) == []) "constBytes fieldNames"
  assert (Radix.Binary.Format.fieldNames (.padding 5) == []) "padding fieldNames"
  assert (Radix.Binary.Format.fieldNames (.align 8) == []) "align fieldNames"
  let seqNames := Radix.Binary.Format.fieldNames (Radix.Binary.Format.seq (.byte "a") (.byte "b"))
  assert (seqNames.length == 2) "seq fieldNames count"

  assert (Radix.Binary.Format.fieldCount (.byte "x") == 1) "byte fieldCount"
  assert (Radix.Binary.Format.fieldCount (.bytes "blob" 2) == 1) "bytes fieldCount"
  assert (Radix.Binary.Format.fieldCount (.lengthPrefixedBytes "payload" 2 .little) == 1) "lengthPrefixedBytes fieldCount"
  assert (Radix.Binary.Format.fieldCount (.countPrefixedArray "items" 1 .little (.byte "item")) == 2) "countPrefixedArray fieldCount"
  assert (Radix.Binary.Format.fieldCount (.constBytes (ByteArray.mk #[0xAA, 0x55])) == 0) "constBytes fieldCount"
  assert (Radix.Binary.Format.fieldCount (.padding 5) == 0) "padding fieldCount"
  assert (Radix.Binary.Format.fieldCount (.align 8) == 0) "align fieldCount"
  assert (Radix.Binary.Format.fieldCount (Radix.Binary.Format.seq (.byte "a") (.byte "b")) == 2) "seq fieldCount"
  assert (Radix.Binary.Format.fieldCount arrayFmt == 2) "array fieldCount includes wrapper and element"

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

  let data2 := ByteArray.mk #[0xCD, 0xAB]
  match Radix.Binary.parseFormat data2 (.uint16 "val" .little) with
  | .ok fields =>
    match fields.head? with
    | some (.uint16 _ val) => assert (val.toNat == 0xABCD) "parse u16 LE"
    | _ => assert false "parse u16 wrong variant"
  | .error e => assert false s!"parse u16 error: {e}"

  let data4 := ByteArray.mk #[0x12, 0x34, 0x56, 0x78]
  match Radix.Binary.parseFormat data4 (.uint32 "val" .big) with
  | .ok fields =>
    match fields.head? with
    | some (.uint32 _ val) => assert (val.toNat == 0x12345678) "parse u32 BE"
    | _ => assert false "parse u32 wrong variant"
  | .error e => assert false s!"parse u32 error: {e}"

  let data3 := ByteArray.mk #[0, 0, 0]
  match Radix.Binary.parseFormat data3 (.padding 3) with
  | .ok fields => assert (fields.length == 0) "parse padding empty"
  | .error e => assert false s!"parse padding error: {e}"

  let alignData := ByteArray.mk #[0x42, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x12]
  match Radix.Binary.parseFormatExact alignData alignSeqFmt with
  | .ok fields =>
    match fields with
    | [.byte _ tag, .uint32 _ payload] =>
      assert (tag.toNat == 0x42) "parse align tag"
      assert (payload.toNat == 0x12345678) "parse align payload"
    | _ => assert false "parse align wrong variant"
  | .error e => assert false s!"parse align error: {e}"

  let arrayData := ByteArray.mk #[0x10, 0x20, 0x30]
  let arrayFmt := Radix.Binary.Format.array "items" 3 (.byte "item")
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

  let dataShort := ByteArray.mk #[0x00]
  match Radix.Binary.parseFormat dataShort (.uint32 "x" .little) with
  | .ok _ => assert false "parse OOB should fail"
  | .error _ => assert true "parse OOB error"

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

  c.get
