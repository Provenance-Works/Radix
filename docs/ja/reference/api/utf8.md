# UTF-8 モジュール APIリファレンス

> **モジュール**: `Radix.UTF8`
> **ソース**: `Radix/UTF8/`

## 概要

検証済みの Unicode scalar モデルと、実行可能な UTF-8 エンコード/デコードヘルパーを提供します。仕様層は `List UInt8` 上で定義され、操作層は downstream の parser や binary format で使いやすい `ByteArray` ベース API を公開します。

## 仕様 (`UTF8.Spec`)

Unicode scalar の妥当性と UTF-8 構造に関する純粋定義です。

```lean
def IsScalar (n : Nat) : Prop
abbrev Scalar := { n : Nat // IsScalar n }

namespace Scalar
def ofNat? (n : Nat) : Option Scalar
def replacement : Scalar
def byteCount (s : Scalar) : Nat
end Scalar

def isContinuationByte (b : UInt8) : Bool
def continuationPayload (b : UInt8) : Nat
def encode (s : Scalar) : List UInt8
def encodeAll : List Scalar → List UInt8
def decodeNext? : List UInt8 → Option (Scalar × Nat)
def decodeNextStep? : List UInt8 → Option DecodeStep
def decodeAll? (bytes : List UInt8) : Option (List Scalar)
def decodeAllReplacingMaximalSubparts (bytes : List UInt8) : List Scalar
def maximalSubpartLength (bytes : List UInt8) : Nat
def firstDecodeError? (bytes : List UInt8) : Option DecodeError
def WellFormed (bytes : List UInt8) : Prop
```

```lean
inductive DecodeErrorKind
  | invalidStartByte
  | unexpectedContinuationByte
  | invalidContinuationByte
  | overlongSequence
  | surrogateSequence
  | outOfRangeSequence
  | truncatedSequence

structure DecodeError where
  kind : DecodeErrorKind
  expectedLength : Nat
  consumed : Nat

inductive DecodeStep where
  | scalar (scalar : Scalar) (consumed : Nat)
  | error (error : DecodeError)
```

### 意味論

- `Scalar.ofNat?` はサロゲート領域と Unicode 範囲外の値を拒否します。
- `decodeNext?` は overlong encoding と不正な continuation byte を拒否します。
- `decodeAll?` は入力全体が正しい UTF-8 のときだけ成功します。
- `decodeNextStep?` は不正入力を分類し、現在オフセットでの Unicode maximal subpart 長を返します。
- `decodeAllReplacingMaximalSubparts` は Unicode 17 Chapter 3 の maximal-subpart 置換例（Table 3-8 から 3-11）に従います。

## 操作 (`UTF8.Ops`)

`ByteArray` 上の実行可能ヘルパーです。

```lean
abbrev Scalar := Spec.Scalar

def encodeScalar (s : Scalar) : ByteArray
def encodeScalars (scalars : List Scalar) : ByteArray
def decodeNextBytes? (bytes : ByteArray) : Option (Scalar × Nat)
def decodeNextBytesStep? (bytes : ByteArray) : Option DecodeStep
def decodeBytes? (bytes : ByteArray) : Option (List Scalar)
def decodeBytesReplacing (bytes : ByteArray) : List Scalar
def decodeBytesReplacingMaximalSubparts (bytes : ByteArray) : List Scalar
def isWellFormed (bytes : ByteArray) : Bool
def encodedLength (s : Scalar) : Nat
def scalarCount? (bytes : ByteArray) : Option Nat
def firstDecodeErrorBytes? (bytes : ByteArray) : Option DecodeError
```

### UTF-16 API

```lean
abbrev UTF16CodeUnit := UInt16

def utf16ArrayToList (units : Array UTF16CodeUnit) : List UTF16CodeUnit
def listToUTF16Array (units : List UTF16CodeUnit) : Array UTF16CodeUnit

inductive UTF16DecodeErrorKind
  | unexpectedLowSurrogate
  | invalidLowSurrogate
  | truncatedHighSurrogate

structure UTF16DecodeError where
  kind : UTF16DecodeErrorKind
  expectedLength : Nat
  consumed : Nat

inductive UTF16DecodeStep where
  | scalar (scalar : Scalar) (consumed : Nat)
  | error (error : UTF16DecodeError)

def encodeScalarToUTF16List (s : Scalar) : List UTF16CodeUnit
def encodeScalarToUTF16 (s : Scalar) : Array UTF16CodeUnit
def encodeScalarsToUTF16List (scalars : List Scalar) : List UTF16CodeUnit
def encodeScalarsToUTF16 (scalars : List Scalar) : Array UTF16CodeUnit

def decodeNextUTF16ListStep? (units : List UTF16CodeUnit) : Option UTF16DecodeStep
def decodeNextUTF16Step? (units : Array UTF16CodeUnit) : Option UTF16DecodeStep
def decodeUTF16List? (units : List UTF16CodeUnit) : Option (List Scalar)
def decodeUTF16? (units : Array UTF16CodeUnit) : Option (List Scalar)
def decodeUTF16ListReplacing (units : List UTF16CodeUnit) : List Scalar
def decodeUTF16Replacing (units : Array UTF16CodeUnit) : List Scalar
def firstUTF16DecodeErrorList? (units : List UTF16CodeUnit) : Option UTF16DecodeError
def firstUTF16DecodeError? (units : Array UTF16CodeUnit) : Option UTF16DecodeError
def utf16ScalarCount? (units : Array UTF16CodeUnit) : Option Nat

def transcodeUTF16ToUTF8? (units : Array UTF16CodeUnit) : Option ByteArray
def transcodeUTF16ToUTF8Replacing (units : Array UTF16CodeUnit) : ByteArray
def transcodeUTF8ToUTF16? (bytes : ByteArray) : Option (Array UTF16CodeUnit)
def transcodeUTF8ToUTF16Replacing (mode : ReplacementMode) (bytes : ByteArray)
  : Array UTF16CodeUnit
```

### Streaming API

```lean
inductive ReplacementMode
  | perByte
  | maximalSubpart

structure StreamDecoder where
  pending : List UInt8

structure StreamChunk where
  scalars : List Scalar
  decoder : StreamDecoder

structure StreamError where
  scalars : List Scalar
  error : DecodeError
  offset : Nat

def StreamDecoder.init : StreamDecoder
def StreamDecoder.feed? (decoder : StreamDecoder) (chunk : ByteArray)
  : Except StreamError StreamChunk
def StreamDecoder.feedReplacing (decoder : StreamDecoder) (mode : ReplacementMode)
  (chunk : ByteArray) : StreamChunk
def StreamDecoder.finish? (decoder : StreamDecoder) : Except StreamError (List Scalar)
def StreamDecoder.finishReplacing (decoder : StreamDecoder) (mode : ReplacementMode)
  : List Scalar

def decodeChunks? (chunks : List ByteArray) : Except StreamError (List Scalar)
def decodeChunksReplacing (mode : ReplacementMode) (chunks : List ByteArray)
  : List Scalar
```

### Cursor API

```lean
structure Cursor where
  bytes : ByteArray
  offset : Nat

def Cursor.init (bytes : ByteArray) : Cursor
def Cursor.atOffset? (bytes : ByteArray) (offset : Nat) : Option Cursor
def Cursor.byteOffset (cursor : Cursor) : Nat
def Cursor.remainingByteCount (cursor : Cursor) : Nat
def Cursor.isAtEnd (cursor : Cursor) : Bool
def Cursor.currentStep? (cursor : Cursor) : Option DecodeStep
def Cursor.current? (cursor : Cursor) : Option Scalar
def Cursor.currentError? (cursor : Cursor) : Option DecodeError
def Cursor.advance? (cursor : Cursor) : Option (Scalar × Cursor)
def Cursor.advanceReplacing (mode : ReplacementMode) (cursor : Cursor)
  : Option (Scalar × Cursor)
def Cursor.decodeRemaining? (cursor : Cursor) : Option (List Scalar)
def Cursor.decodeRemainingReplacing (mode : ReplacementMode) (cursor : Cursor)
  : List Scalar

def decodeWithCursor? (bytes : ByteArray) : Option (List Scalar)
def decodeWithCursorReplacing (mode : ReplacementMode) (bytes : ByteArray)
  : List Scalar
```

### Grapheme API

```lean
structure Grapheme where
  scalars : List Scalar
  startOffset : Nat
  endOffset : Nat

def Grapheme.byteLength (grapheme : Grapheme) : Nat
def Grapheme.scalarCount (grapheme : Grapheme) : Nat
def Grapheme.isEmpty (grapheme : Grapheme) : Bool

def Cursor.advanceGrapheme? (cursor : Cursor) : Option (Grapheme × Cursor)
def Cursor.advanceGraphemeReplacing (mode : ReplacementMode) (cursor : Cursor)
  : Option (Grapheme × Cursor)
def Cursor.currentGrapheme? (cursor : Cursor) : Option Grapheme
def Cursor.currentGraphemeReplacing (mode : ReplacementMode) (cursor : Cursor)
  : Option Grapheme
def Cursor.decodeRemainingGraphemes? (cursor : Cursor) : Option (List Grapheme)
def Cursor.decodeRemainingGraphemesReplacing (mode : ReplacementMode) (cursor : Cursor)
  : List Grapheme

def decodeGraphemes? (bytes : ByteArray) : Option (List Grapheme)
def decodeGraphemesReplacing (mode : ReplacementMode) (bytes : ByteArray)
  : List Grapheme
def graphemeCount? (bytes : ByteArray) : Option Nat
```

### Normalization API

```lean
abbrev CombiningClass := Nat

structure DecompositionEntry where
  source : Nat
  target : List Nat

inductive NormalizationForm where
  | nfd
  | nfc
  | nfkd
  | nfkc

def isStarter (ccc : CombiningClass) : Bool
def isCombining (ccc : CombiningClass) : Bool
def canonicalCombiningClass (s : Scalar) : CombiningClass
def supportsNormalizationForm (form : NormalizationForm) : Bool

def canonicalDecomposition? (s : Scalar) : Option (List Scalar)
def canonicalComposePair? (starter mark : Scalar) : Option Scalar

def normalizeScalarsNFD (scalars : List Scalar) : List Scalar
def normalizeScalarsNFC (scalars : List Scalar) : List Scalar
def normalizeScalars? (form : NormalizationForm) (scalars : List Scalar)
  : Option (List Scalar)

def isNormalizedNFD (scalars : List Scalar) : Bool
def isNormalizedNFC (scalars : List Scalar) : Bool
def canonicallyEquivalent (left right : List Scalar) : Bool

def normalizeBytesNFD? (bytes : ByteArray) : Option ByteArray
def normalizeBytesNFC? (bytes : ByteArray) : Option ByteArray
def normalizeListNFD? (bytes : List UInt8) : Option (List UInt8)
def normalizeListNFC? (bytes : List UInt8) : Option (List UInt8)
def normalizeBytes? (form : NormalizationForm) (bytes : ByteArray) : Option ByteArray
def normalizeList? (form : NormalizationForm) (bytes : List UInt8) : Option (List UInt8)
def isNormalizedBytesNFD? (bytes : ByteArray) : Option Bool
def isNormalizedBytesNFC? (bytes : ByteArray) : Option Bool
def canonicallyEquivalentBytes? (left right : ByteArray) : Bool
```

### Text Operations API

```lean
def scalarBoundaryOffsets? (bytes : ByteArray) : Option (List Nat)
def graphemeBoundaryOffsets? (bytes : ByteArray) : Option (List Nat)

def byteOffsetOfScalarIndex? (bytes : ByteArray) (index : Nat) : Option Nat
def byteOffsetOfGraphemeIndex? (bytes : ByteArray) (index : Nat) : Option Nat

def scalarAtIndex? (bytes : ByteArray) (index : Nat) : Option Scalar
def graphemeAtIndex? (bytes : ByteArray) (index : Nat) : Option Grapheme

def sliceBytes? (bytes : ByteArray) (startOffset endOffset : Nat) : Option ByteArray
def sliceScalars? (bytes : ByteArray) (startIndex endIndex : Nat) : Option ByteArray
def sliceGraphemes? (bytes : ByteArray) (startIndex endIndex : Nat) : Option ByteArray

def startsWithScalars (bytes : ByteArray) (prefixBytes : ByteArray) : Bool
def endsWithScalars (bytes : ByteArray) (suffixBytes : ByteArray) : Bool
def findScalars? (bytes : ByteArray) (needleBytes : ByteArray) : Option Nat
def containsScalars (bytes : ByteArray) (needleBytes : ByteArray) : Bool

def startsWithGraphemes (bytes : ByteArray) (prefixBytes : ByteArray) : Bool
def endsWithGraphemes (bytes : ByteArray) (suffixBytes : ByteArray) : Bool
def findGraphemes? (bytes : ByteArray) (needleBytes : ByteArray) : Option Nat
def containsGraphemes (bytes : ByteArray) (needleBytes : ByteArray) : Bool
```

### Replacement Mode

- `decodeBytesReplacing` は既存の「不正バイト 1 個につき U+FFFD 1 個」の互換挙動を維持します。
- `decodeBytesReplacingMaximalSubparts` は Unicode maximal subpart に従って不正 prefix をまとめて置換しつつ、隣接する well-formed subsequence を誤って消費しません。
- `StreamDecoder.feed?` は incomplete な UTF-8 prefix を chunk 境界で保留し、不正列として早まって確定しません。
- `StreamDecoder.finish?` は残った pending prefix を end-of-stream の truncated-sequence error として確定します。
- `StreamDecoder.feedReplacing` と `decodeChunksReplacing` は chunked byte stream に同じ recovery policy を適用します。
- `Cursor.atOffset?` は scalar 境界のみを受理し、continuation byte の途中オフセットを拒否します。
- `Cursor.advance?` は正しい UTF-8 バッファをバイトオフセット付きで 1 scalar ずつ前進させます。
- `Cursor.advanceReplacing` は不正なバッファでも置換モード付きで同じ走査を提供します。
- `decodeGraphemes?` は well-formed UTF-8 を、リポジトリ内の simplified UAX #29 モデルに従って grapheme cluster へ分割します。
- `decodeGraphemesReplacing` は不正 prefix を置換した後も同じ cluster segmentation を適用します。
- regional indicator は grapheme 走査時に 2 個ずつペアリングし、flag 風の cluster を保ちます。
- `normalizeScalarsNFD` は、サポート対象の canonical decomposition と canonical combining class ordering を適用します。
- `normalizeScalarsNFC` は NFD の上に canonical composition を適用し、algorithmic Hangul composition とサポート対象の Latin precomposed 文字を扱います。
- `normalizeScalars?` と `normalizeBytes?` は現在 `nfd` と `nfc` をサポートし、`nfkd` と `nfkc` は compatibility mapping 未実装のため `none` を返します。
- `canonicallyEquivalent` と `canonicallyEquivalentBytes?` は canonical decomposition を通して比較するため、precomposed 形と decomposed 形を等価とみなせます。
- `scalarBoundaryOffsets?` と `graphemeBoundaryOffsets?` はバイト単位の安全な切断点を返し、常に `0` と入力末尾オフセットを含みます。
- `sliceBytes?` は UTF-8 scalar 境界にそろっていないオフセットを拒否します。
- `sliceScalars?` と `sliceGraphemes?` は scalar または grapheme の index 範囲を、再利用しやすい well-formed UTF-8 部分列へ戻します。
- `findScalars?` と `findGraphemes?` は最初の整列済み一致位置をバイトオフセットで返すため、cursor や slice API へそのまま渡せます。
- `startsWithScalars`、`endsWithScalars`、`containsScalars` と grapheme 版は、比較対象が対応するテキスト境界にそろっている場合だけ成功します。

### UTF-16 Notes

- strict UTF-16 decode は BMP scalar をそのまま受理し、supplementary scalar は妥当な surrogate pair から復元します。
- malformed surrogate usage は `unexpectedLowSurrogate`、`invalidLowSurrogate`、`truncatedHighSurrogate` に分類されます。
- UTF-16 replacement decode は malformed code unit を 1 個ずつ消費するので、次の妥当な code unit で再同期できます。
- `transcodeUTF16ToUTF8Replacing` は置換後に UTF-8 へ再エンコードするため、常に well-formed UTF-8 を返します。

### Grapheme Notes

- grapheme segmentation は intentionally simplified です。`UTF8.Spec` の `classifyGraphemeBreak` と `isGraphemeBreak` を使い、実行層で regional-indicator pairing を追加しています。
- precomposed Hangul LV/LVT syllable も明示的に分類するので、Jamo 列と precomposed Hangul の両方をサポート範囲内で正しく cluster 化します。
- emoji ZWJ sequence や full Unicode property table まで含む完全な UAX #29 実装ではまだありません。

### Normalization Notes

- canonical normalization は現在、algorithmic Hangul decomposition/composition と、よく使う Latin precomposed 文字および combining mark のサブセットをカバーします。
- canonical ordering は starter ごとの segment 内で安定に並べ替えるため、starter 境界をまたがずに combining mark 順序だけを正規化します。
- compatibility normalization (`nfkd` / `nfkc`) は、より大きい compatibility-mapping table が必要になるため、意図的に未実装です。

### 再公開される構築子

```lean
def Scalar.ofNat? (n : Nat) : Option Scalar
def Scalar.replacement : Scalar
def Scalar.byteCount (s : Scalar) : Nat
```

## 証明 (`UTF8.Lemmas`)

- `encode_length_eq_byteCount`: 仕様層のエンコード長が scalar の長さクラスと一致
- `wellFormed_encode`: `encode` が生成した列は常に well-formed UTF-8
- `decodeNext_encode`: 1 個の scalar の正準エンコードを decode すると同じ scalar に戻る
- `decodeAll_encodeAll`: 仕様層の decode after encode が元の scalar list を返す
- `encodedLength_eq_spec`: 実行層の encoded length が仕様と一致
- `decodeBytes_encodeScalars`: 実行層の decode after encode が元の scalar list を返す
- `scalarCount_encodeScalars`: 実行層の scalar count がエンコードした list 長と一致
- `isWellFormed_encodeScalar`: 操作層エンコードは常にデコーダに受理される
- `isWellFormed_encodeScalars`: 操作層の scalar sequence 全体も常にデコーダに受理される

## Conformance Coverage

- Unicode 17 Chapter 3 Table 3-7 の well-formed boundary 行を execution test で検証します。
- Unicode 17 Chapter 3 Table 3-8 から 3-11 を official maximal-subpart replacement vector として実装しています。
- U+0000 から U+10FFFF までの全 Unicode scalar 値（サロゲート除く）を exhaustive に round-trip 検証します。
- Property test と comprehensive test で chunked strict decode、chunked replacement decode、end-of-stream truncation を検証します。
- Property test と comprehensive test で cursor traversal、正しい境界シーク、cursor replacement semantics も検証します。
- Property test と comprehensive test で combining mark、CRLF、Hangul sequence、regional indicator、replacement-aware malformed input の grapheme clustering も検証します。
- Property test と comprehensive test で UTF-16 surrogate pair encoding、strict/replacement UTF-16 decode、UTF-8/UTF-16 transcoding も検証します。
- Property test と comprehensive test で、サポート対象の Latin precomposed 文字の canonical decomposition/composition、canonical ordering、Hangul normalization、canonical equivalence も検証します。
- Property test と comprehensive test で scalar 境界列挙、scalar 単位の slice、scalar subsequence の byte-offset 検索も検証します。

## 使用例

```lean
import Radix.UTF8

def euro : IO Radix.UTF8.Scalar := do
  match Radix.UTF8.ofNat? 0x20AC with
  | some scalar => pure scalar
  | none => throw (IO.userError "invalid scalar")

def demo : IO Unit := do
  let scalar ← euro
  let bytes := Radix.UTF8.encodeScalar scalar
  IO.println s!"encoded: {bytes.toList}"
  IO.println s!"well formed: {Radix.UTF8.isWellFormed bytes}"

def streamingDemo : IO Unit := do
  let chunk1 := ByteArray.mk #[0xF0, 0x9F]
  let chunk2 := ByteArray.mk #[0x99, 0x82, 0x21]
  match Radix.UTF8.StreamDecoder.feed? Radix.UTF8.StreamDecoder.init chunk1 with
  | Except.ok step1 =>
    match Radix.UTF8.StreamDecoder.feed? step1.decoder chunk2 with
    | Except.ok step2 =>
      IO.println s!"decoded: {step2.scalars.map (·.val)}"
    | Except.error err =>
      IO.println s!"streaming error: {reprStr err}"
  | Except.error err =>
    IO.println s!"streaming error: {reprStr err}"

def cursorDemo : IO Unit := do
  let bytes := ByteArray.mk #[0x41, 0xE2, 0x82, 0xAC]
  let cursor := Radix.UTF8.Cursor.init bytes
  match Radix.UTF8.Cursor.advance? cursor with
  | some (scalar, nextCursor) =>
    IO.println s!"first scalar: {scalar.val}, next offset: {nextCursor.byteOffset}"
  | none =>
    IO.println "cursor error"

def graphemeDemo : IO Unit := do
  let bytes := ByteArray.mk #[0x41, 0xCC, 0x81, 0x42]
  match Radix.UTF8.decodeGraphemes? bytes with
  | some graphemes =>
    IO.println s!"graphemes: {graphemes.map (fun grapheme => grapheme.scalars.map (·.val))}"
  | none =>
    IO.println "grapheme decode error"

def utf16Demo : IO Unit := do
  let units := Radix.UTF8.encodeScalarsToUTF16 [⟨0x41, by decide⟩, ⟨0x1F642, by decide⟩]
  IO.println s!"utf16 units: {units.toList.map UInt16.toNat}"
  match Radix.UTF8.decodeUTF16? units with
  | some scalars =>
    IO.println s!"decoded scalars: {scalars.map (·.val)}"
  | none =>
    IO.println "utf16 decode error"

def textOpDemo : IO Unit := do
  let bytes := ByteArray.mk #[0x41, 0xCC, 0x81, 0x42, 0xE2, 0x82, 0xAC]
  IO.println s!"scalar boundaries: {Radix.UTF8.scalarBoundaryOffsets? bytes}"
  IO.println s!"grapheme boundaries: {Radix.UTF8.graphemeBoundaryOffsets? bytes}"
  IO.println s!"slice scalars [1, 3): {Radix.UTF8.sliceScalars? bytes 1 3 |>.map ByteArray.toList}"
  IO.println s!"find scalar subsequence: {Radix.UTF8.findScalars? bytes (ByteArray.mk #[0x42, 0xE2, 0x82, 0xAC])}"

def normalizationDemo : IO Unit := do
  let composed := ByteArray.mk #[0xC3, 0x81]
  let decomposed := ByteArray.mk #[0x41, 0xCC, 0x81]
  IO.println s!"nfd(composed): {Radix.UTF8.normalizeBytesNFD? composed |>.map ByteArray.toList}"
  IO.println s!"nfc(decomposed): {Radix.UTF8.normalizeBytesNFC? decomposed |>.map ByteArray.toList}"
  IO.println s!"canonically equivalent: {Radix.UTF8.canonicallyEquivalentBytes? composed decomposed}"
```

## 関連ドキュメント

- [Bytes](bytes.md) — downstream codec と組み合わせるバイトレベル補助
- [Binary](binary.md) — UTF-8 payload を含む parser / serializer
