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
def decodeAll? (bytes : List UInt8) : Option (List Scalar)
def WellFormed (bytes : List UInt8) : Prop
```

### 意味論

- `Scalar.ofNat?` はサロゲート領域と Unicode 範囲外の値を拒否します。
- `decodeNext?` は overlong encoding と不正な continuation byte を拒否します。
- `decodeAll?` は入力全体が正しい UTF-8 のときだけ成功します。

## 操作 (`UTF8.Ops`)

`ByteArray` 上の実行可能ヘルパーです。

```lean
abbrev Scalar := Spec.Scalar

def encodeScalar (s : Scalar) : ByteArray
def encodeScalars (scalars : List Scalar) : ByteArray
def decodeNextBytes? (bytes : ByteArray) : Option (Scalar × Nat)
def decodeBytes? (bytes : ByteArray) : Option (List Scalar)
def isWellFormed (bytes : ByteArray) : Bool
def encodedLength (s : Scalar) : Nat
def scalarCount? (bytes : ByteArray) : Option Nat
```

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
```

## 関連ドキュメント

- [Bytes](bytes.md) — downstream codec と組み合わせるバイトレベル補助
- [Binary](binary.md) — UTF-8 payload を含む parser / serializer
