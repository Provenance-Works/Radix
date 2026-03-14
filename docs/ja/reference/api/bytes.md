# Bytes モジュール APIリファレンス

> **モジュール**: `Radix.Bytes`
> **ソース**: `Radix/Bytes/`

## 概要

エンディアン対応のバイト操作を提供します：バイトスワップ、ビッグ/リトルエンディアン変換、境界チェック付きバイト配列ビュー。

## バイトオーダー (`Bytes.Order`)

### バイトスワップ

```lean
@[inline] def UInt16.bswap (x : UInt16) : UInt16  -- 2バイト反転
@[inline] def UInt32.bswap (x : UInt32) : UInt32  -- 4バイト反転
@[inline] def UInt64.bswap (x : UInt64) : UInt64  -- 8バイト反転
```

### エンディアン変換

すべての符号なし・符号付きマルチバイト型に定義：

```lean
def UInt32.toBigEndian (x : UInt32) : UInt32
def UInt32.fromBigEndian (x : UInt32) : UInt32
def UInt32.toLittleEndian (x : UInt32) : UInt32
def UInt32.fromLittleEndian (x : UInt32) : UInt32
def UInt32.toEndian (endian : Endian) (x : UInt32) : UInt32  -- 汎用
def UInt32.fromEndian (endian : Endian) (x : UInt32) : UInt32

-- UInt16, UInt64, Int16, Int32, Int64 でも利用可能
```

### ネイティブエンディアン検出

```lean
def nativeEndian : Endian  -- x86_64 では .little を返す
```

## ByteSlice (`Bytes.Slice`)

`ByteArray` への境界チェック付きゼロコピービュー：

```lean
structure ByteSlice where
  data : ByteArray
  start : Nat
  len : Nat
  valid : start + len ≤ data.size
```

### Tier 1: 証明付きリード

```lean
def readU8 (s : ByteSlice) (offset : Nat) (h : offset < s.len) : UInt8
def readU16 (s : ByteSlice) (offset : Nat) (endian : Endian) (h : offset + 2 ≤ s.len) : UInt16
def readU32 (s : ByteSlice) (offset : Nat) (endian : Endian) (h : offset + 4 ≤ s.len) : UInt32
def readU64 (s : ByteSlice) (offset : Nat) (endian : Endian) (h : offset + 8 ≤ s.len) : UInt64
```

### Tier 2: チェック付きリード

```lean
def checkedReadU8 (s : ByteSlice) (offset : Nat) : Option UInt8
def checkedReadU16 (s : ByteSlice) (offset : Nat) (endian : Endian) : Option UInt16
-- 以下同様
```

### スライシング

```lean
def subslice (s : ByteSlice) (offset len : Nat) (h : offset + len ≤ s.len) : ByteSlice
def checkedSubslice (s : ByteSlice) (offset len : Nat) : Option ByteSlice
```

## 証明 (`Bytes.Lemmas`)

- **bswap 退化性**: すべてのビット幅で `bswap (bswap x) = x`
- **BE ラウンドトリップ**: `fromBigEndian (toBigEndian x) = x`
- **LE ラウンドトリップ**: `fromLittleEndian (toLittleEndian x) = x`
- **BE/LE 関係**: `toBigEndian = bswap ∘ toLittleEndian`
- **符号付き BE ラウンドトリップ**: `Int16`, `Int32`, `Int64` について
- **ByteSlice の性質**: `subslice_len`, `zeros_len`, `empty_len`, `ofByteArray_len`

## 関連ドキュメント

- [Word](word.md) — エンディアン変換の整数型
- [Memory](memory.md) — エンディアン付きバッファベースのリード/ライト
