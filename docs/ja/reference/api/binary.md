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
  | bytes (name : String) (count : Nat)          -- 固定長の生バイト列
  | lengthPrefixedBytes (name : String) (prefixBytes : Nat) (endian : Endian)
                                                 -- 長さ prefix 付きの生バイト列
  | countPrefixedArray (name : String) (prefixBytes : Nat) (endian : Endian) (elem : Format)
                                                 -- 要素数 prefix 付きの配列
  | constBytes (value : ByteArray)               -- 完全一致が必要な固定バイト列
  | padding (n : Nat)                             -- nバイトのゼロ
  | align (n : Nat)                               -- 次の n バイト境界まで 0 埋めする
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

`align n` は現在のオフセットから見て、次の `n` バイト境界まで必要最小限の 0 埋めを挿入します。

`lengthPrefixedBytes name prefixBytes endian` は 1, 2, 4, 8 バイトの長さ prefix を持つ生バイト列を表します。parse 時は prefix を復号してその長さだけ payload を読み、serialize 時は payload 長から prefix を自動計算します。

`countPrefixedArray name prefixBytes endian elem` は 1, 2, 4, 8 バイトの要素数 prefix を持つ配列を表します。parse 時は count を復号して `elem` をその個数だけ読み、serialize 時は `FieldValue.array` の長さから count を自動計算します。

`constBytes value` は固定ヘッダを DSL に直接埋め込みます。parse 時は `value` と完全一致を要求し、serialize 時は名前付きフィールドを消費せずに `value` をそのまま出力します。

### フォーマットの性質

```lean
def Format.fixedSize : Format → Option Nat  -- 合計バイトサイズ（可変の場合 none）
def Format.fieldNames : Format → List String
def Format.fieldCount : Format → Nat
def Format.toFormatSpec : Format → FormatSpec
```

可変長フォーマットに対する `Format.toFormatSpec` は最小レイアウト情報を返します。`totalSize` は必要最小 prefix サイズで、可変長フィールドの後続オフセットは厳密値ではなく下限として扱ってください。

## パーサー (`Binary.Parser`)

```lean
inductive ParseError where
  | outOfBounds
  | unsupportedLengthPrefix
  | constantMismatch
  | trailingBytes
  | internal

inductive FieldValue where
  | byte (v : UInt8)
  | uint16 (v : UInt16)
  | uint32 (v : UInt32)
  | uint64 (v : UInt64)
  | bytes (v : ByteArray)
  | array (vs : List FieldValue)

def parsePrefix (data : ByteArray) (fmt : Format) : Except ParseError (List FieldValue × Nat)
def parseSplit (data : ByteArray) (fmt : Format) : Except ParseError (List FieldValue × ByteArray)
def parseFormat (data : ByteArray) (fmt : Format) : Except ParseError (List FieldValue)
def parseFormatExact (data : ByteArray) (fmt : Format) : Except ParseError (List FieldValue)
```

`parseFormat` は prefix parse を行い、後続の余剰バイトは無視します。
`parseSplit` は prefix parse を行い、未消費の suffix を返します。
`parseFormatExact` は余剰入力を `trailingBytes` で拒否します。

`bytes name count` は単一バイト配列へ分解せずに、固定長の生バイト列をそのまま表現します。

`lengthPrefixedBytes` は可変長 blob を表現しつつ、復号結果は通常の `FieldValue.bytes` で受け取れます。

`countPrefixedArray` は可変長の繰り返し構造を表現しつつ、復号結果は既存の `FieldValue.array` 形をそのまま使います。

`constBytes` は magic 値、シグネチャ、固定タグの宣言的検証に向いています。parse 後の手動比較ではなく、フォーマット自体に検証責務を持たせられます。

## シリアライザー (`Binary.Serial`)

```lean
inductive SerialError where
  | missingField
  | typeMismatch
  | unsupportedLengthPrefix
  | lengthOverflow
  | unexpectedField

def serializeFormat (fmt : Format) (values : List FieldValue) : Except SerialError ByteArray
def writePadding (n : Nat) (arr : ByteArray) : ByteArray
```

シリアライゼーションは各フォーマットノードごとに一致するフィールドを1つだけ消費します。
入力に未消費の値が残った場合、`serializeFormat` は `unexpectedField` を返します。

`lengthPrefixedBytes` の payload が prefix 幅に収まらない場合、serialize は `lengthOverflow` を返します。

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
