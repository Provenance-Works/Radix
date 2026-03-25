import tests.ComprehensiveTests.Framework
import Radix.UTF8

/-!
# UTF-8 Tests
-/

open ComprehensiveTests

namespace UTF8Test

private def scalar (n : Nat) : IO Radix.UTF8.Scalar := do
  match Radix.UTF8.ofNat? n with
  | some s => pure s
  | none => throw (IO.userError s!"invalid scalar {n}")

private def byteArray (bytes : List UInt8) : ByteArray :=
  ByteArray.mk bytes.toArray

private def scalarValues (scalars : List Radix.UTF8.Scalar) : List Nat :=
  scalars.map (·.val)

private def replacementValue : Nat :=
  Radix.UTF8.replacement.val

private def strictReplacementValues (bytes : List UInt8) : List Nat :=
  Radix.UTF8.scalarsToNats (Radix.UTF8.decodeListReplacingMaximalSubparts bytes)

end UTF8Test

def runUTF8Tests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    UTF8 tests..."

  let ascii ← UTF8Test.scalar 0x41
  let twoByte ← UTF8Test.scalar 0x00A2
  let threeByte ← UTF8Test.scalar 0x20AC
  let fourByte ← UTF8Test.scalar 0x1F642
  let maxScalar ← UTF8Test.scalar 0x10FFFF

  assert (Radix.UTF8.encodedLength ascii == 1) "ASCII length"
  assert (Radix.UTF8.encodedLength twoByte == 2) "2-byte length"
  assert (Radix.UTF8.encodedLength threeByte == 3) "3-byte length"
  assert (Radix.UTF8.encodedLength fourByte == 4) "4-byte length"
  assert (Radix.UTF8.encodedLength maxScalar == 4) "max scalar length"

  let encoded := Radix.UTF8.encodeScalars [ascii, twoByte, threeByte, fourByte]
  assert (Radix.UTF8.isWellFormed encoded) "encoded scalars well formed"
  match Radix.UTF8.decodeBytes? encoded with
  | some scalars =>
    assert (scalars.map (·.val) == [0x41, 0x00A2, 0x20AC, 0x1F642]) "decode encoded scalars"
  | none => assert false "decode encoded scalars failed"

  match Radix.UTF8.decodeNextBytes? (Radix.UTF8.encodeScalar fourByte) with
  | some (decoded, consumed) =>
    assert (decoded.val == 0x1F642) "decodeNext returns scalar"
    assert (consumed == 4) "decodeNext consumed four bytes"
  | none => assert false "decodeNext four-byte scalar failed"

  let boundaryScalars := [ascii, (← UTF8Test.scalar 0x7F), (← UTF8Test.scalar 0x80), (← UTF8Test.scalar 0x7FF), (← UTF8Test.scalar 0x800), (← UTF8Test.scalar 0xD7FF), (← UTF8Test.scalar 0xE000), (← UTF8Test.scalar 0xFFFF), (← UTF8Test.scalar 0x10000), maxScalar]
  let boundaryEncoded := Radix.UTF8.encodeScalars boundaryScalars
  match Radix.UTF8.decodeBytes? boundaryEncoded with
  | some scalars =>
    assert (scalars.map (·.val) == boundaryScalars.map (·.val)) "boundary scalar round-trip"
  | none => assert false "boundary scalar round-trip failed"

  assert (Radix.UTF8.scalarCount? boundaryEncoded == some boundaryScalars.length) "scalar count round-trip"

  let malformed1 := ByteArray.mk #[0xC0, 0xAF]
  let malformed2 := ByteArray.mk #[0xED, 0xA0, 0x80]
  let malformed3 := ByteArray.mk #[0xF0, 0x9F, 0x99]
  assert (!Radix.UTF8.isWellFormed malformed1) "reject overlong"
  assert (!Radix.UTF8.isWellFormed malformed2) "reject surrogate"
  assert (!Radix.UTF8.isWellFormed malformed3) "reject truncated four-byte sequence"
  assert (Radix.UTF8.ofNat? 0xD800 == none) "reject surrogate constructor"

  let assertDetailedError :=
    fun (bytes : List UInt8)
        (kind : Radix.UTF8.Spec.DecodeErrorKind)
        (expectedLength consumed : Nat)
        (label : String) => do
      match Radix.UTF8.decodeNextListStep? bytes with
      | some (Radix.UTF8.Spec.DecodeStep.error err) =>
        assert (err.kind == kind) s!"{label}: error kind"
        assert (err.expectedLength == expectedLength) s!"{label}: expected length"
        assert (err.consumed == consumed) s!"{label}: maximal subpart length"
        assert (Radix.UTF8.maximalSubpartLength bytes == consumed) s!"{label}: maximalSubpartLength"
        assert (Radix.UTF8.firstDecodeErrorList? bytes == some err) s!"{label}: firstDecodeErrorList?"
      | some (Radix.UTF8.Spec.DecodeStep.scalar _ actualConsumed) =>
        assert false s!"{label}: unexpectedly decoded scalar with width {actualConsumed}"
      | none =>
        assert false s!"{label}: missing decode step"

  assertDetailedError [0x80]
    Radix.UTF8.Spec.DecodeErrorKind.unexpectedContinuationByte 1 1
    "detailed error: unexpected continuation"
  assertDetailedError [0xC0, 0xAF]
    Radix.UTF8.Spec.DecodeErrorKind.overlongSequence 2 1
    "detailed error: overlong lead"
  assertDetailedError [0xC2, 0x41, 0x42]
    Radix.UTF8.Spec.DecodeErrorKind.invalidContinuationByte 2 1
    "detailed error: invalid continuation"
  assertDetailedError [0xE1, 0x80]
    Radix.UTF8.Spec.DecodeErrorKind.truncatedSequence 3 2
    "detailed error: truncated three-byte sequence"
  assertDetailedError [0xED, 0xA0, 0x80]
    Radix.UTF8.Spec.DecodeErrorKind.surrogateSequence 3 1
    "detailed error: surrogate sequence"
  assertDetailedError [0xF4, 0x91, 0x92, 0x93]
    Radix.UTF8.Spec.DecodeErrorKind.outOfRangeSequence 4 1
    "detailed error: out-of-range sequence"

  -- ── Spec-level scalar predicates ──
  assert (Radix.UTF8.Spec.Scalar.isAscii ascii) "ASCII scalar isAscii"
  assert (!Radix.UTF8.Spec.Scalar.isAscii fourByte) "four-byte scalar not isAscii"
  assert (Radix.UTF8.Spec.Scalar.isBMP threeByte) "3-byte scalar isBMP"
  assert (!Radix.UTF8.Spec.Scalar.isBMP fourByte) "four-byte scalar not isBMP"
  assert (Radix.UTF8.Spec.Scalar.isSupplementary fourByte) "four-byte scalar isSupplementary"
  assert (!Radix.UTF8.Spec.Scalar.isSupplementary ascii) "ASCII not isSupplementary"
  assert (Radix.UTF8.Spec.Scalar.plane ascii == 0) "ASCII on plane 0"
  assert (Radix.UTF8.Spec.Scalar.plane fourByte == 1) "emoji on plane 1"

  -- ── Ops-level helpers ──
  let encodedList := Radix.UTF8.encodeAllToList [ascii, twoByte]
  assert (encodedList.length > 0) "encodeAllToList produces bytes"
  let decodedList := Radix.UTF8.decodeList? encodedList
  match decodedList with
  | some scalars => assert (scalars.length == 2) "decodeList? round-trip count"
  | none => assert false "decodeList? round-trip failed"
  assert (Radix.UTF8.isWellFormedList encodedList) "encodeAllToList is well-formed"
  let byteCounts := Radix.UTF8.totalByteLength [ascii, twoByte, threeByte, fourByte]
  assert (byteCounts == 10) "totalByteLength 1+2+3+4=10"
  let nats := Radix.UTF8.scalarsToNats [ascii, twoByte]
  assert (nats == [0x41, 0x00A2]) "scalarsToNats"

  -- ── BOM tests ──
  let bomBytes := Radix.UTF8.Spec.bom
  assert (bomBytes == [0xEF, 0xBB, 0xBF]) "BOM bytes"
  assert (Radix.UTF8.Spec.hasBOM [0xEF, 0xBB, 0xBF, 0x41]) "hasBOM true"
  assert (!Radix.UTF8.Spec.hasBOM [0x41, 0x42]) "hasBOM false"
  assert (Radix.UTF8.Spec.stripBOM [0xEF, 0xBB, 0xBF, 0x41] == [0x41]) "stripBOM"
  assert (Radix.UTF8.Spec.stripBOM [0x41] == [0x41]) "stripBOM no BOM"

  -- ── Byte classification ──
  let classes := Radix.UTF8.classifyBytes (ByteArray.mk #[0x41, 0xC2, 0xA2, 0x80])
  assert (classes.length == 4) "classifyBytes length"

  -- RFC 3629 examples and boundary syntax.
  let rfcExample1 := UTF8Test.byteArray [0x41, 0xE2, 0x89, 0xA2, 0xCE, 0x91, 0x2E]
  match Radix.UTF8.decodeBytes? rfcExample1 with
  | some scalars =>
    assert (UTF8Test.scalarValues scalars == [0x41, 0x2262, 0x0391, 0x2E])
      "RFC 3629 example 1 decodes"
  | none => assert false "RFC 3629 example 1 rejected"

  let rfcExampleKorean := UTF8Test.byteArray [0xED, 0x95, 0x9C, 0xEA, 0xB5, 0xAD, 0xEC, 0x96, 0xB4]
  match Radix.UTF8.decodeBytes? rfcExampleKorean with
  | some scalars =>
    assert (UTF8Test.scalarValues scalars == [0xD55C, 0xAD6D, 0xC5B4])
      "RFC 3629 Korean example decodes"
  | none => assert false "RFC 3629 Korean example rejected"

  let rfcExampleJapanese := UTF8Test.byteArray [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC, 0xE8, 0xAA, 0x9E]
  match Radix.UTF8.decodeBytes? rfcExampleJapanese with
  | some scalars =>
    assert (UTF8Test.scalarValues scalars == [0x65E5, 0x672C, 0x8A9E])
      "RFC 3629 Japanese example decodes"
  | none => assert false "RFC 3629 Japanese example rejected"

  let rfcExampleBOM := UTF8Test.byteArray [0xEF, 0xBB, 0xBF, 0xF0, 0xA3, 0x8E, 0xB4]
  assert (Radix.UTF8.hasByteOrderMark rfcExampleBOM) "RFC 3629 BOM detected"
  match Radix.UTF8.decodeBytes? (Radix.UTF8.stripByteOrderMark rfcExampleBOM) with
  | some scalars =>
    assert (UTF8Test.scalarValues scalars == [0x233B4])
      "RFC 3629 BOM stripping preserves payload"
  | none => assert false "RFC 3629 BOM payload rejected"

  let rfcValidBoundaries : List (List UInt8) :=
    [ [0x00]
    , [0x7F]
    , [0xC2, 0x80]
    , [0xDF, 0xBF]
    , [0xE0, 0xA0, 0x80]
    , [0xED, 0x9F, 0xBF]
    , [0xEE, 0x80, 0x80]
    , [0xEF, 0xBF, 0xBF]
    , [0xF0, 0x90, 0x80, 0x80]
    , [0xF4, 0x8F, 0xBF, 0xBF]
    ]
  for bytes in rfcValidBoundaries do
    assert (Radix.UTF8.Spec.validateUTF8 bytes) s!"RFC boundary accepted: {bytes}"
    assert (Radix.UTF8.isWellFormedList bytes) s!"Ops accepts RFC boundary: {bytes}"

  let rfcInvalidBoundaries : List (List UInt8) :=
    [ [0x80]
    , [0xBF]
    , [0xC0, 0x80]
    , [0xC1, 0xBF]
    , [0xE0, 0x80, 0x80]
    , [0xE0, 0x9F, 0xBF]
    , [0xED, 0xA0, 0x80]
    , [0xED, 0xBF, 0xBF]
    , [0xF0, 0x80, 0x80, 0x80]
    , [0xF0, 0x8F, 0xBF, 0xBF]
    , [0xF4, 0x90, 0x80, 0x80]
    , [0xF5, 0x80, 0x80, 0x80]
    , [0xFE]
    , [0xFF]
    ]
  for bytes in rfcInvalidBoundaries do
    assert (!Radix.UTF8.Spec.validateUTF8 bytes) s!"RFC boundary rejected: {bytes}"
    assert (!Radix.UTF8.isWellFormedList bytes) s!"Ops rejects RFC boundary: {bytes}"

  -- Markus Kuhn UTF-8 stress cases: replacement and re-synchronization.
  let unexpectedContinuation := UTF8Test.byteArray [0x80, 0x22]
  assert (!Radix.UTF8.isWellFormed unexpectedContinuation) "unexpected continuation rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing unexpectedContinuation) ==
    [UTF8Test.replacementValue, 0x22]) "unexpected continuation resyncs at quote"

  let lonelyStart := UTF8Test.byteArray [0xE0, 0x22]
  assert (!Radix.UTF8.isWellFormed lonelyStart) "lonely start byte rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing lonelyStart) ==
    [UTF8Test.replacementValue, 0x22]) "lonely start byte resyncs at quote"

  let impossibleBytes := UTF8Test.byteArray [0xFE, 0xFF, 0x22]
  assert (!Radix.UTF8.isWellFormed impossibleBytes) "impossible bytes rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing impossibleBytes) ==
    [UTF8Test.replacementValue, UTF8Test.replacementValue, 0x22])
    "impossible bytes produce one replacement per byte"

  let overlongSlash2 := UTF8Test.byteArray [0xC0, 0xAF, 0x22]
  assert (!Radix.UTF8.isWellFormed overlongSlash2) "overlong slash 2-byte rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing overlongSlash2) ==
    [UTF8Test.replacementValue, UTF8Test.replacementValue, 0x22])
    "overlong slash 2-byte resyncs after invalid bytes"

  let overlongSlash3 := UTF8Test.byteArray [0xE0, 0x80, 0xAF, 0x22]
  assert (!Radix.UTF8.isWellFormed overlongSlash3) "overlong slash 3-byte rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing overlongSlash3) ==
    [UTF8Test.replacementValue, UTF8Test.replacementValue, UTF8Test.replacementValue, 0x22])
    "overlong slash 3-byte resyncs after invalid bytes"

  let overlongSlash4 := UTF8Test.byteArray [0xF0, 0x80, 0x80, 0xAF, 0x22]
  assert (!Radix.UTF8.isWellFormed overlongSlash4) "overlong slash 4-byte rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing overlongSlash4) ==
    [ UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , 0x22
    ]) "overlong slash 4-byte resyncs after invalid bytes"

  let surrogatePairBytes := UTF8Test.byteArray [0xED, 0xA0, 0x80, 0xED, 0xB0, 0x80, 0x22]
  assert (!Radix.UTF8.isWellFormed surrogatePairBytes) "surrogate pair encoding rejected"
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeBytesReplacing surrogatePairBytes) ==
    [ UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , 0x22
    ]) "surrogate pair encoding replaces each invalid byte and resyncs"

  -- Unicode 17 Chapter 3 official conformance vectors.
  let officialReplacementVectors : List (List UInt8 × List Nat × String) :=
    [ ( [0xC0, 0xAF, 0xE0, 0x80, 0xBF, 0xF0, 0x81, 0x82, 0x41]
      , [ UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x41
        ]
      , "Unicode 17 Table 3-8 non-shortest forms"
      )
    , ( [0xED, 0xA0, 0x80, 0xED, 0xBF, 0xBF, 0xED, 0xAF, 0x41]
      , [ UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x41
        ]
      , "Unicode 17 Table 3-9 surrogate sequences"
      )
    , ( [0xF4, 0x91, 0x92, 0x93, 0xFF, 0x41, 0x80, 0xBF, 0x42]
      , [ UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x41
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x42
        ]
      , "Unicode 17 Table 3-10 other ill-formed sequences"
      )
    , ( [0xE1, 0x80, 0xE2, 0xF0, 0x91, 0x92, 0xF1, 0xBF, 0x41]
      , [ UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , UTF8Test.replacementValue
        , 0x41
        ]
      , "Unicode 17 Table 3-11 truncated sequences"
      )
    ]
  for vector in officialReplacementVectors do
    let (bytes, expected, label) := vector
    assert (UTF8Test.strictReplacementValues bytes == expected) s!"{label}: maximal-subpart replacement"

  let truncatedUnicodeTable := [0xE1, 0x80, 0xE2, 0xF0, 0x91, 0x92, 0xF1, 0xBF, 0x41]
  assert (Radix.UTF8.scalarsToNats (Radix.UTF8.decodeListReplacing truncatedUnicodeTable) ==
    [ UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , 0x41
    ]) "legacy replacement keeps one-marker-per-byte semantics"
  assert (UTF8Test.strictReplacementValues truncatedUnicodeTable ==
    [ UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , UTF8Test.replacementValue
    , 0x41
    ]) "strict replacement collapses truncated prefixes to maximal subparts"

  assert (UTF8Test.strictReplacementValues [0xC2, 0x41, 0x42] ==
    [UTF8Test.replacementValue, 0x41, 0x42])
    "Unicode D93b example does not consume valid successor bytes"
  assert (UTF8Test.strictReplacementValues [0x41, 0xC2, 0xC3, 0xB1, 0x42] ==
    [0x41, UTF8Test.replacementValue, 0x00F1, 0x42])
    "Unicode D86 partition preserves following minimal well-formed subsequence"
  assert (UTF8Test.strictReplacementValues [0xE1, 0x80, 0x41] ==
    [UTF8Test.replacementValue, 0x41])
    "strict replacement consumes truncated maximal subpart only"

  -- Exhaustive coverage over all Unicode scalar values.
  let mut exhaustiveCount := 0
  let mut oneByteCount := 0
  let mut twoByteCount := 0
  let mut threeByteCount := 0
  let mut fourByteCount := 0
  let mut scalarNat := 0
  while scalarNat ≤ 0x10FFFF do
    match Radix.UTF8.ofNat? scalarNat with
    | some scalarValue =>
      let encodedList := Radix.UTF8.encodeToList scalarValue
      assert (Radix.UTF8.encodedLength scalarValue == encodedList.length)
        s!"exhaustive encodedLength matches byte count at scalar {scalarNat}"
      assert (Radix.UTF8.maximalSubpartLength encodedList == encodedList.length)
        s!"exhaustive maximalSubpartLength matches valid scalar width at scalar {scalarNat}"
      match Radix.UTF8.decodeList? encodedList with
      | some decoded =>
        assert (decoded == [scalarValue]) s!"exhaustive UTF-8 round-trip failed at scalar {scalarNat}"
      | none =>
        assert false s!"exhaustive decode rejected scalar {scalarNat}"
      exhaustiveCount := exhaustiveCount + 1
      match encodedList.length with
      | 1 => oneByteCount := oneByteCount + 1
      | 2 => twoByteCount := twoByteCount + 1
      | 3 => threeByteCount := threeByteCount + 1
      | 4 => fourByteCount := fourByteCount + 1
      | _ => assert false s!"unexpected UTF-8 width {encodedList.length} at scalar {scalarNat}"
    | none =>
      assert (0xD800 ≤ scalarNat && scalarNat ≤ 0xDFFF)
        s!"only surrogates should be rejected by Scalar.ofNat?: {scalarNat}"

    if scalarNat == 0x10FFFF then
      scalarNat := scalarNat + 1
    else if scalarNat == 0xD7FF then
      scalarNat := 0xE000
    else
      scalarNat := scalarNat + 1

  assert (exhaustiveCount == 1112064) "exhaustive scalar count matches Unicode scalar space"
  assert (oneByteCount == 128) "ASCII scalar count matches Unicode scalar space"
  assert (twoByteCount == 1920) "two-byte scalar count matches Unicode scalar space"
  assert (threeByteCount == 61440) "three-byte scalar count matches Unicode scalar space"
  assert (fourByteCount == 1048576) "four-byte scalar count matches Unicode scalar space"

  -- Streaming strict decode across chunk boundaries.
  let strictChunk1 := UTF8Test.byteArray [0xF0, 0x9F]
  let strictChunk2 := UTF8Test.byteArray [0x99, 0x82, 0x41]
  match Radix.UTF8.StreamDecoder.feed? Radix.UTF8.StreamDecoder.init strictChunk1 with
  | Except.ok chunk1 =>
    assert (chunk1.scalars == []) "streaming strict first chunk defers incomplete scalar"
    assert (chunk1.decoder.pendingByteCount == 2) "streaming strict first chunk stores pending bytes"
    match Radix.UTF8.StreamDecoder.feed? chunk1.decoder strictChunk2 with
    | Except.ok chunk2 =>
      assert (UTF8Test.scalarValues chunk2.scalars == [0x1F642, 0x41])
        "streaming strict second chunk decodes pending scalar and ASCII tail"
      assert (!chunk2.decoder.hasPending) "streaming strict leaves no pending bytes after completion"
      assert (Radix.UTF8.StreamDecoder.finish? chunk2.decoder == Except.ok [])
        "streaming strict finish on empty pending succeeds"
    | Except.error err =>
      assert false s!"streaming strict second chunk unexpectedly failed: {reprStr err}"
  | Except.error err =>
    assert false s!"streaming strict first chunk unexpectedly failed: {reprStr err}"

  match Radix.UTF8.decodeChunks? [strictChunk1, strictChunk2] with
  | Except.ok scalars =>
    assert (UTF8Test.scalarValues scalars == [0x1F642, 0x41])
      "decodeChunks? matches strict streaming result"
  | Except.error err =>
    assert false s!"decodeChunks? unexpectedly failed: {reprStr err}"

  -- Streaming strict decode reports malformed continuation after a pending prefix.
  let invalidChunk1 := UTF8Test.byteArray [0xC2]
  let invalidChunk2 := UTF8Test.byteArray [0x41, 0x42]
  match Radix.UTF8.StreamDecoder.feed? Radix.UTF8.StreamDecoder.init invalidChunk1 with
  | Except.ok chunk1 =>
    assert (chunk1.scalars == []) "invalid streaming prefix yields no scalar before continuation arrives"
    assert (chunk1.decoder.pendingByteCount == 1) "invalid streaming prefix stores one pending byte"
    match Radix.UTF8.StreamDecoder.feed? chunk1.decoder invalidChunk2 with
    | Except.ok chunk2 =>
      assert false s!"invalid continuation unexpectedly decoded: {reprStr chunk2}"
    | Except.error err =>
      assert (err.scalars == []) "invalid continuation emits no scalar before error"
      assert (err.offset == 0) "invalid continuation is reported at buffered offset zero"
      assert (err.error.kind == Radix.UTF8.Spec.DecodeErrorKind.invalidContinuationByte)
        "invalid continuation reports detailed error kind"
  | Except.error err =>
    assert false s!"invalid streaming prefix unexpectedly failed early: {reprStr err}"

  let truncatedStrictChunk := UTF8Test.byteArray [0xE1, 0x80]
  match Radix.UTF8.StreamDecoder.feed? Radix.UTF8.StreamDecoder.init truncatedStrictChunk with
  | Except.ok chunk =>
    assert (chunk.decoder.pendingByteCount == 2) "strict truncated chunk remains pending before finish"
    match Radix.UTF8.StreamDecoder.finish? chunk.decoder with
    | Except.ok scalars =>
      assert false s!"strict finish unexpectedly accepted truncated input: {UTF8Test.scalarValues scalars}"
    | Except.error err =>
      assert (err.scalars == []) "strict finish truncated error emits no scalar"
      assert (err.offset == 0) "strict finish truncated error starts at pending offset zero"
      assert (err.error.kind == Radix.UTF8.Spec.DecodeErrorKind.truncatedSequence)
        "strict finish reports truncated sequence"
      assert (err.error.consumed == 2) "strict finish keeps truncated maximal subpart width"
  | Except.error err =>
    assert false s!"strict truncated chunk unexpectedly failed before finish: {reprStr err}"

  -- Streaming replacement modes preserve chunk boundaries and finish policy.
  let replacementChunk1 := UTF8Test.byteArray [0xE1]
  let replacementChunk2 := UTF8Test.byteArray [0x80, 0x41]
  let perByte1 := Radix.UTF8.StreamDecoder.feedReplacing Radix.UTF8.StreamDecoder.init .perByte replacementChunk1
  assert (perByte1.scalars == []) "per-byte replacement defers incomplete prefix"
  assert (perByte1.decoder.pendingByteCount == 1) "per-byte replacement stores incomplete prefix"
  let perByte2 := Radix.UTF8.StreamDecoder.feedReplacing perByte1.decoder .perByte replacementChunk2
  assert (UTF8Test.scalarValues perByte2.scalars == [UTF8Test.replacementValue, UTF8Test.replacementValue, 0x41])
    "per-byte replacement reports each invalid byte after chunk join"
  assert (!perByte2.decoder.hasPending) "per-byte replacement clears pending after malformed completion"

  let maximal1 := Radix.UTF8.StreamDecoder.feedReplacing Radix.UTF8.StreamDecoder.init .maximalSubpart replacementChunk1
  assert (maximal1.scalars == []) "maximal-subpart replacement defers incomplete prefix"
  assert (maximal1.decoder.pendingByteCount == 1) "maximal-subpart replacement stores incomplete prefix"
  let maximal2 := Radix.UTF8.StreamDecoder.feedReplacing maximal1.decoder .maximalSubpart replacementChunk2
  assert (UTF8Test.scalarValues maximal2.scalars == [UTF8Test.replacementValue, 0x41])
    "maximal-subpart replacement collapses buffered invalid prefix into one marker"
  assert (!maximal2.decoder.hasPending) "maximal-subpart replacement clears pending after malformed completion"

  let finishPerByte :=
    Radix.UTF8.StreamDecoder.finishReplacing
      (Radix.UTF8.StreamDecoder.feedReplacing Radix.UTF8.StreamDecoder.init .perByte truncatedStrictChunk).decoder
      .perByte
  assert (UTF8Test.scalarValues finishPerByte == [UTF8Test.replacementValue, UTF8Test.replacementValue])
    "per-byte finish replaces each pending truncated byte"

  let finishMaximal :=
    Radix.UTF8.StreamDecoder.finishReplacing
      (Radix.UTF8.StreamDecoder.feedReplacing Radix.UTF8.StreamDecoder.init .maximalSubpart truncatedStrictChunk).decoder
      .maximalSubpart
  assert (UTF8Test.scalarValues finishMaximal == [UTF8Test.replacementValue])
    "maximal-subpart finish replaces pending truncated prefix once"

  assert (UTF8Test.scalarValues (Radix.UTF8.decodeChunksReplacing .maximalSubpart
    [UTF8Test.byteArray [0xE2], UTF8Test.byteArray [0x82], UTF8Test.byteArray [0xAC]]) == [0x20AC])
    "decodeChunksReplacing reconstructs valid scalar across three chunks"
  assert (UTF8Test.scalarValues (Radix.UTF8.decodeChunksReplacing .maximalSubpart
    [replacementChunk1, replacementChunk2]) == [UTF8Test.replacementValue, 0x41])
    "decodeChunksReplacing maximal-subpart matches manual streaming result"

  c.get
