# Memory モジュール APIリファレンス

> **モジュール**: `Radix.Memory`
> **ソース**: `Radix/Memory/`

## 概要

Lean 4 の `ByteArray` 上に構築された抽象メモリモデルを提供します。証明付きバッファ、ポインタ抽象化、パックド構造体レイアウト計算に加えて、メモリマップ推論向けの区間代数も含みます。すべての操作は GC フレンドリーで、手動メモリ管理は不要です。

## バッファ (`Memory.Model`)

```lean
structure Buffer where
  bytes : ByteArray
```

### コンストラクション

```lean
def Buffer.zeros (size : Nat) : Buffer      -- ゼロ初期化バッファ
def Buffer.empty : Buffer                     -- 空（0バイト）
def Buffer.ofByteArray (ba : ByteArray) : Buffer
```

### Tier 1: 証明付き API

```lean
def Buffer.readU8 (buf : Buffer) (offset : Nat) (h : offset < buf.bytes.size) : UInt8
def Buffer.writeU8 (buf : Buffer) (offset : Nat) (val : UInt8) (h : offset < buf.bytes.size) : Buffer

-- エンディアン付きマルチバイト（個別 BE/LE 関数）
def Buffer.readU16BE (buf : Buffer) (offset : Nat) (h : offset + 2 ≤ buf.bytes.size) : UInt16
def Buffer.readU16LE (buf : Buffer) (offset : Nat) (h : offset + 2 ≤ buf.bytes.size) : UInt16
def Buffer.readU32BE (buf : Buffer) (offset : Nat) (h : offset + 4 ≤ buf.bytes.size) : UInt32
def Buffer.readU32LE (buf : Buffer) (offset : Nat) (h : offset + 4 ≤ buf.bytes.size) : UInt32
def Buffer.readU64BE (buf : Buffer) (offset : Nat) (h : offset + 8 ≤ buf.bytes.size) : UInt64
def Buffer.readU64LE (buf : Buffer) (offset : Nat) (h : offset + 8 ≤ buf.bytes.size) : UInt64

def Buffer.writeU16BE (buf : Buffer) (offset : Nat) (val : UInt16) (h : offset + 2 ≤ buf.bytes.size) : Buffer
def Buffer.writeU16LE (buf : Buffer) (offset : Nat) (val : UInt16) (h : offset + 2 ≤ buf.bytes.size) : Buffer
def Buffer.writeU32BE (buf : Buffer) (offset : Nat) (val : UInt32) (h : offset + 4 ≤ buf.bytes.size) : Buffer
def Buffer.writeU32LE (buf : Buffer) (offset : Nat) (val : UInt32) (h : offset + 4 ≤ buf.bytes.size) : Buffer
def Buffer.writeU64BE (buf : Buffer) (offset : Nat) (val : UInt64) (h : offset + 8 ≤ buf.bytes.size) : Buffer
def Buffer.writeU64LE (buf : Buffer) (offset : Nat) (val : UInt64) (h : offset + 8 ≤ buf.bytes.size) : Buffer
```

### Tier 2: チェック付き API

```lean
def Buffer.checkedReadU8 (buf : Buffer) (offset : Nat) : Option UInt8
def Buffer.checkedWriteU8 (buf : Buffer) (offset : Nat) (val : UInt8) : Option Buffer
-- U16, U32, U64 についても同様
```

## ポインタ抽象化 (`Memory.Ptr`)

```lean
structure Ptr (n : Nat) where
  buf : Buffer
  offset : Nat
  h : offset + n ≤ buf.size
```

### 操作

```lean
def Ptr.ofBuffer (buf : Buffer) (offset : Nat) (h : offset + n ≤ buf.size) : Ptr n
def Ptr.advance (p : Ptr n) (delta : Nat) (h : p.offset + delta + n ≤ p.buf.size) : Ptr n
def Ptr.retreat (p : Ptr n) (delta : Nat) (h : delta ≤ p.offset) : Ptr n
def Ptr.readU8 (p : Ptr n) (h : 1 ≤ n) : UInt8
def Ptr.readU16 (p : Ptr n) (endian : Endian) (h : 2 ≤ n) : UInt16
def Ptr.readU32 (p : Ptr n) (endian : Endian) (h : 4 ≤ n) : UInt32
def Ptr.readU64 (p : Ptr n) (endian : Endian) (h : 8 ≤ n) : UInt64
```

## レイアウト (`Memory.Layout`)

```lean
structure FieldDesc where
  name : String
  offset : Nat
  size : Nat

structure LayoutDesc where
  fields : List FieldDesc
  totalSize : Nat
```

### 操作

```lean
def LayoutDesc.appendField (layout : LayoutDesc) (name : String) (size : Nat) : LayoutDesc
def LayoutDesc.appendAligned (layout : LayoutDesc) (name : String) (size align : Nat) : LayoutDesc
def LayoutDesc.isNonOverlapping (layout : LayoutDesc) : Bool
def LayoutDesc.allFieldsFit (layout : LayoutDesc) : Bool
```

## 仕様 (`Memory.Spec`)

```lean
structure Region where
  start : Nat
  size : Nat

def Region.endOffset (r : Region) : Nat
def Region.intersects (a b : Region) : Prop
def Region.disjoint (a b : Region) : Prop
def Region.adjacent (a b : Region) : Prop
def Region.mergeable (a b : Region) : Prop
def Region.contains (outer inner : Region) : Prop
def Region.inBounds (r : Region) (addr : Nat) : Prop
def Region.span (a b : Region) : Region
def Region.intersection (a b : Region) : Region
def Region.union? (a b : Region) : Option Region
def Region.difference (a b : Region) : List Region
def isAligned (addr align : Nat) : Prop
```

### 領域代数のメモ

- `span` は 2 つの入力領域を両方含む最小区間を返します。
- `intersection` は重なりがない場合、正規化された `Region.empty` を返します。
- `union?` は 2 領域が重なっているか、ちょうど隣接している場合にだけ成功します。
- `difference` は区間差で分割が起こり得るため、0 個、1 個、2 個の非空残余領域を返します。

## 証明 (`Memory.Lemmas`)

- **バッファサイズ保存**: `(Buffer.zeros n).size = n`, `(buf.writeU8 ..).size = buf.size`
- **領域分離性**: 可換律、`empty_left`、`empty_right`、`intersects_comm`、`adjacent_comm`
- **領域代数**: `span_contains_left`、`span_contains_right`、`span_comm`、`intersection_comm`、`union?_isSome_iff_mergeable`、`span_least_upper_bound`
- **アライメント**: `isAligned_zero`、`isAligned_mul`
- **レイアウト**: `empty_totalSize`、`appendField_totalSize`
- **チェック付き API**: `checkedReadU8_some`（範囲内の場合）、`checkedReadU8_none`（範囲外の場合）

## 関連ドキュメント

- [Bytes](bytes.md) — ゼロコピービューの ByteSlice
- [Binary](binary.md) — フォーマット駆動メモリアクセス
