# メモリプールモジュール APIリファレンス

> **モジュール**: `Radix.MemoryPool`
> **ソース**: `Radix/MemoryPool/`

## 概要

2種類の検証済みメモリプールアロケータを提供します：リニアバンプアロケータと固定サイズスラブアロケータ。両方とも `Memory.Buffer` をバックエンドとし、動的ヒープ割り当てが利用できないベアメタルまたは組み込み環境向けに設計されています。仕様層は抽象的な安全性証明を提供し、モデル層は証明付き不変条件を備えた具体的な実装を提供します。

## 仕様 (`MemoryPool.Spec`)

検証のための抽象状態マシン：

```lean
structure BumpState where
  capacity : Nat
  cursor   : Nat

structure SlabState where
  blockSize  : Nat
  blockCount : Nat
  allocated  : Finset Nat
```

仕様レベルで証明される安全性の性質：
- バンプ割り当ては容量を超えない
- スラブ割り当てはどのブロックが使用中かを追跡する
- 二重解放は静的に防止される

## バンププール (`MemoryPool.Model`)

単一バッファから連続領域を割り当てるリニアバンプアロケータ。割り当ては O(1) です。メモリの回収は `reset` による一括でのみ可能です。

### 構造体

```lean
structure BumpPool where
  buf      : Memory.Buffer
  capacity : Nat
  cursor   : Nat
```

- `buf` — 基盤メモリバッファ
- `capacity` — バイト単位の合計サイズ
- `cursor` — 次の空きバイトオフセット（リセットまで単調増加）

### コンストラクション

```lean
def BumpPool.new (capacity : Nat) : BumpPool
```

`cursor = 0` でゼロ初期化されたプールを作成します。

### クエリ

```lean
def BumpPool.remaining (pool : BumpPool) : Nat       -- capacity - cursor
def BumpPool.canAlloc (pool : BumpPool) (size : Nat) : Bool
```

### 割り当て

```lean
def BumpPool.alloc (pool : BumpPool) (size : Nat) : Option (Nat × BumpPool)
def BumpPool.allocAligned (pool : BumpPool) (size align : Nat) : Option (Nat × BumpPool)
```

- `alloc` は開始オフセットと更新されたプールを返すか、空き領域が不足している場合は `none` を返します。
- `allocAligned` はまずカーソルを次のアラインされたオフセットに進め、その後割り当てを行います。

### リセット

```lean
def BumpPool.reset (pool : BumpPool) : BumpPool
```

カーソルを 0 にリセットし、すべての割り当てを実質的に解放します。バッファの内容はゼロ化されません。

### 読み書き

```lean
def BumpPool.writeU8 (pool : BumpPool) (offset : Nat) (val : UInt8)
    (h : offset < pool.capacity) : BumpPool
def BumpPool.readU8 (pool : BumpPool) (offset : Nat)
    (h : offset < pool.capacity) : UInt8
```

## スラブプール (`MemoryPool.Model`)

同一サイズのブロックのプールを管理する固定サイズブロックアロケータ。個別のブロック割り当てと解放をサポートし、二重解放防止機能を備えています。

### 構造体

```lean
structure SlabPool where
  buf        : Memory.Buffer
  blockSize  : Nat
  blockCount : Nat
  freeList   : List Nat
  allocated  : List Nat
```

- `buf` — サイズ `blockSize * blockCount` の基盤メモリバッファ
- `blockSize` — 各ブロックのバイト単位サイズ
- `blockCount` — ブロックの合計数
- `freeList` — 利用可能なブロックのインデックス
- `allocated` — 現在使用中のブロックのインデックス

### コンストラクション

```lean
def SlabPool.new (blockSize blockCount : Nat) : SlabPool
```

すべてのブロックがフリーリストに含まれた状態でプールを作成します。

### クエリ

```lean
def SlabPool.freeCount (pool : SlabPool) : Nat           -- freeList.length
def SlabPool.allocatedCount (pool : SlabPool) : Nat      -- allocated.length
def SlabPool.canAlloc (pool : SlabPool) : Bool            -- freeList が空でない
```

### 割り当てと解放

```lean
def SlabPool.alloc (pool : SlabPool) : Option (Nat × Nat × SlabPool)
def SlabPool.free (pool : SlabPool) (blockIdx : Nat) : Option SlabPool
```

- `alloc` はフリーリストからポップして `(blockIdx, byteOffset, updatedPool)` を返すか、ブロックがない場合は `none` を返します。
- `free` はブロックをフリーリストに返却します。`blockIdx` が `allocated` に含まれない場合は `none` を返します（二重解放を防止）。

### ブロックの読み書き

```lean
def SlabPool.writeBlockU8 (pool : SlabPool) (blockIdx offset : Nat) (val : UInt8)
    (hBlock : blockIdx ∈ pool.allocated)
    (hOffset : offset < pool.blockSize) : SlabPool
def SlabPool.readBlockU8 (pool : SlabPool) (blockIdx offset : Nat)
    (hBlock : blockIdx ∈ pool.allocated)
    (hOffset : offset < pool.blockSize) : UInt8
```

両方の操作は、ブロックが現在割り当て済みであること、およびオフセットがブロック内であることの証明を必要とします。

## 証明 (`MemoryPool.Lemmas`)

### バンププール

- `bump_cursor_le_capacity`: `alloc` 後、`cursor ≤ capacity`
- `bump_alloc_offset_valid`: 返されたオフセットは `offset + size ≤ capacity` を満たす
- `bump_reset_cursor`: `(pool.reset).cursor = 0`
- `bump_capacity_preserved`: すべての操作が `pool.capacity` を保存

### スラブプール

- `slab_no_double_free`: ブロックが `allocated` に含まれない場合、`free` は失敗する
- `slab_alloc_free_roundtrip`: `alloc` して `free` するとプールは等価な状態に戻る
- `slab_count_invariant`: `freeCount + allocatedCount = blockCount`
- `slab_capacity_preserved`: `blockSize` と `blockCount` は不変

## 使用例

```lean
-- バンプアロケータ
let pool := BumpPool.new 1024
let (off1, pool) := pool.alloc 64 |>.get!       -- オフセット0で64バイトを割り当て
let (off2, pool) := pool.alloc 128 |>.get!      -- オフセット64で128バイトを割り当て
#eval pool.remaining                              -- 832
let pool := pool.reset                            -- すべてを解放
#eval pool.remaining                              -- 1024

-- 32バイトブロックのスラブアロケータ
let pool := SlabPool.new 32 16                    -- 32バイトのブロック16個
let (blk, off, pool) := pool.alloc.get!
#eval pool.freeCount                              -- 15
let pool := pool.free blk |>.get!
#eval pool.freeCount                              -- 16
```

## 関連ドキュメント

- [Memory](memory.md) — 両アロケータが使用する基盤 `Buffer`
- [アラインメント](alignment.md) — アラインされた割り当てのサポート
