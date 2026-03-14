# Binary モジュール APIリファレンス

> **モジュール**: `Radix.Binary`
> **ソース**: `Radix/Binary/`

## 概要

バイナリワイヤフォーマットを指定する宣言的 DSL と、フォーマット駆動のパーサーとシリアライザーの生成を提供します。LEB128 可変長整数エンコーディングも含みます。すべてのラウンドトリップ特性が形式的に証明済みです。

## フォーマット DSL (`Binary.Format`)

```lean
inductive Format where
  | byte (name : String)                          -- 1バイト
  | uint16 (name : String) (endian : Endian)     -- エンディアン付き2バイト
  | uint32 (name : String) (endian : Endian)     -- エンディアン付き4バイト
  | uint64 (name : String) (endian : Endian)     -- エンディアン付き8バイト
  | padding (n : Nat)                             -- nバイトのゼロ
  | array (name : String) (len : Nat) (elem : Format)  -- 要素の繰り返し
  | seq (a b : Format)                            -- 逐次合成
```

### DSL ヘルパー

```lean
def u16be : Format := .uint16 .big
def u16le : Format := .uint16 .little
def u32be : Format := .uint32 .big
def u32le : Format := .uint32 .little
def u64be : Format := .uint64 .big
def u64le : Format := .uint64 .little
def pad (n : Nat) : Format := .padding n
```

### フォーマットの性質

```lean
def Format.fixedSize : Format → Option Nat  -- 合計バイトサイズ（可変の場合 none）
def Format.fieldNames : Format → List String
def Format.fieldCount : Format → Nat
def Format.toFormatSpec : Format → FormatSpec
```

## パーサー (`Binary.Parser`)

```lean
inductive ParseError where
  | outOfBounds
  | internal

inductive FieldValue where
  | byte (v : UInt8)
  | uint16 (v : UInt16)
  | uint32 (v : UInt32)
  | uint64 (v : UInt64)
  | array (vs : List FieldValue)

def parseFormat (fmt : Format) (data : ByteArray) : Except ParseError (List FieldValue)
```

## シリアライザー (`Binary.Serial`)

```lean
inductive SerialError where
  | missingField
  | typeMismatch

def serializeFormat (fmt : Format) (values : List FieldValue) : Except SerialError ByteArray
def writePadding (n : Nat) (arr : ByteArray) : ByteArray
```

## LEB128 (`Binary.Leb128`)

### エンコーディング

```lean
@[inline] def encodeU32 (x : UInt32) : ByteArray   -- 1～5バイト
@[inline] def encodeU64 (x : UInt64) : ByteArray   -- 1～10バイト
@[inline] def encodeS32 (x : Int32) : ByteArray    -- 1～5バイト
@[inline] def encodeS64 (x : Int64) : ByteArray    -- 1～10バイト
```

### デコーディング

```lean
def decodeU32 (data : ByteArray) (offset : Nat) : Option (UInt32 × Nat)
def decodeU64 (data : ByteArray) (offset : Nat) : Option (UInt64 × Nat)
def decodeS32 (data : ByteArray) (offset : Nat) : Option (Int32 × Nat)
def decodeS64 (data : ByteArray) (offset : Nat) : Option (Int64 × Nat)
```

不正な入力では `(value, bytesConsumed)` または `none` を返します。

### LEB128 仕様 (`Binary.Leb128.Spec`)

```lean
def unsignedDecodeValue : List UInt8 → Nat    -- 数学的定義
def signedDecodeValue : List UInt8 → Int      -- 数学的定義
def isValidUnsignedEncoding : List UInt8 → Prop
def isValidU32Encoding : List UInt8 → Prop
```

## 証明

### フォーマット証明 (`Binary.Lemmas`)
- `PrimType.byteSize_pos`
- `Format.fixedSize` コンストラクタごとの正しさ
- `FormatSpec.empty_isValid`
- `Serial.writePadding_size`
- `Parser.parse_padding_ok`

### LEB128 証明 (`Binary.Leb128.Lemmas`)
- **ラウンドトリップ**: `decodeU32 (encodeU32 x) 0 = some (x, (encodeU32 x).size)`
- **ラウンドトリップ**: `decodeU64 (encodeU64 x) 0 = some (x, (encodeU64 x).size)`
- **ラウンドトリップ**: `decodeS32 (encodeS32 x) 0 = some (x, (encodeS32 x).size)`
- **ラウンドトリップ**: `decodeS64 (encodeS64 x) 0 = some (x, (encodeS64 x).size)`
- **サイズ上限**: `(encodeU32 x).size ≤ 5`, `(encodeU64 x).size ≤ 10`
- **空でない**: `(encodeU32 x).size > 0`

## 関連ドキュメント

- [Memory](memory.md) — バイナリデータに使用されるバッファ
- [Bytes](bytes.md) — エンディアンプリミティブ
