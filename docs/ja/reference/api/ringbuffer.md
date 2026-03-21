# リングバッファモジュール APIリファレンス

> **モジュール**: `Radix.RingBuffer`
> **ソース**: `Radix/RingBuffer/`

## 概要

`Memory.Buffer` をバックエンドとする、検証済みの固定容量リングバッファ（循環バッファ）を提供します。実装はインデックスが境界内に収まり、カウントが実際の要素数を追跡することを保証する証明レベルの不変条件を保持します。チェック付きプッシュと強制上書きプッシュの両方のセマンティクスをサポートし、FIFO 順序を証明する完全な仕様層を備えています。

## 仕様 (`RingBuffer.Spec`)

リングバッファを容量制限付き純粋リストとしてモデル化する抽象仕様：

```lean
structure RingBufferState (α : Type) where
  contents : List α
  capacity : Nat
```

### 仕様操作

```lean
def pushSpec (s : RingBufferState α) (val : α) : Option (RingBufferState α)
def popSpec (s : RingBufferState α) : Option (α × RingBufferState α)
def peekSpec (s : RingBufferState α) : Option α
```

### 仕様の性質

- **不変条件の保存**: すべての操作が `contents.length ≤ capacity` を維持
- **FIFO 順序**: `popSpec` はプッシュされた順序で要素を返す

## 実装 (`RingBuffer.Impl`)

### 構造体

```lean
structure RingBuf where
  buf      : Memory.Buffer
  capacity : Nat
  head     : Nat
  tail     : Nat
  count    : Nat
  hCount   : count ≤ capacity
  hHead    : head < capacity
  hTail    : tail < capacity
  hSize    : buf.bytes.size = capacity
```

構造体は以下を保証する4つの証明付き不変条件を保持します：
- `hCount` — 要素数が容量を超えない
- `hHead` — 読み取りインデックスが有効
- `hTail` — 書き込みインデックスが有効
- `hSize` — 基盤バッファが宣言された容量と一致

### コンストラクション

```lean
def RingBuf.new (capacity : Nat) : RingBuf
```

指定された容量でゼロ初期化されたリングバッファを作成します。

### クエリ

```lean
def RingBuf.isEmpty (rb : RingBuf) : Bool       -- count == 0
def RingBuf.isFull (rb : RingBuf) : Bool         -- count == capacity
def RingBuf.remaining (rb : RingBuf) : Nat       -- capacity - count
```

### 単一要素操作

```lean
def RingBuf.push (rb : RingBuf) (val : Radix.UInt8) : Option RingBuf
def RingBuf.pushForce (rb : RingBuf) (val : Radix.UInt8) : RingBuf
def RingBuf.pop (rb : RingBuf) : Option (Radix.UInt8 × RingBuf)
def RingBuf.peek (rb : RingBuf) : Option Radix.UInt8
```

- `push` はバッファが満杯の場合 `none` を返します。
- `pushForce` は満杯時に最も古い要素を上書きし、`head` を進めます。
- `pop` はバッファが空の場合 `none` を返します。
- `peek` は先頭要素を削除せずに読み取ります。

### バルク操作

```lean
def RingBuf.pushMany (rb : RingBuf) (data : List Radix.UInt8) : RingBuf × Nat
def RingBuf.popMany (rb : RingBuf) (n : Nat) : List Radix.UInt8 × RingBuf
def RingBuf.drain (rb : RingBuf) : List Radix.UInt8 × RingBuf
def RingBuf.clear (rb : RingBuf) : RingBuf
def RingBuf.toList (rb : RingBuf) : List Radix.UInt8
```

- `pushMany` は要素を順次プッシュし、バッファと実際にプッシュされた要素数を返します。
- `popMany` は最大 `n` 個の要素をポップし、FIFO 順序で返します。
- `drain` はすべての要素をポップします。`popMany rb rb.count` と等価です。
- `clear` は head、tail、count をゼロにリセットします。
- `toList` は変更なしで現在の内容を FIFO 順序で返します。

## 証明 (`RingBuffer.Lemmas`)

- `new_invariant`: `RingBuf.new` はすべての構造的不変条件を満たす
- `push_count`: `(rb.push val).count = rb.count + 1`（満杯でない場合）
- `pop_count`: `(rb.pop).count = rb.count - 1`（空でない場合）
- `push_pop_roundtrip`: 空のバッファにプッシュしてポップすると、プッシュした値が得られる
- `capacity_preserved`: すべての操作が `rb.capacity` を保存する

## 使用例

```lean
-- リングバッファの作成と使用
let rb := RingBuf.new 4
let rb := (rb.push 0x41).get!       -- 'A' をプッシュ
let rb := (rb.push 0x42).get!       -- 'B' をプッシュ
let (val, rb) := rb.pop.get!        -- ポップ → 0x41
#eval val                             -- 65 (0x41)

-- 満杯バッファへの強制プッシュは最も古い要素を上書き
let rb := RingBuf.new 2
let rb := (rb.push 0x01).get!
let rb := (rb.push 0x02).get!
let rb := rb.pushForce 0x03          -- 0x01 を上書き
let (val, _) := rb.pop.get!
#eval val                             -- 2 (0x02)
```

## 関連ドキュメント

- [Memory](memory.md) — リングバッファが使用する基盤バッファ
- [Bytes](bytes.md) — バイトレベル操作とエンディアン
