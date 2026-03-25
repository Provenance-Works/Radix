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

### Replacement Mode

- `decodeBytesReplacing` は既存の「不正バイト 1 個につき U+FFFD 1 個」の互換挙動を維持します。
- `decodeBytesReplacingMaximalSubparts` は Unicode maximal subpart に従って不正 prefix をまとめて置換しつつ、隣接する well-formed subsequence を誤って消費しません。
- `StreamDecoder.feed?` は incomplete な UTF-8 prefix を chunk 境界で保留し、不正列として早まって確定しません。
- `StreamDecoder.finish?` は残った pending prefix を end-of-stream の truncated-sequence error として確定します。
- `StreamDecoder.feedReplacing` と `decodeChunksReplacing` は chunked byte stream に同じ recovery policy を適用します。

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
```

## 関連ドキュメント

- [Bytes](bytes.md) — downstream codec と組み合わせるバイトレベル補助
- [Binary](binary.md) — UTF-8 payload を含む parser / serializer
