# ビットマップモジュール APIリファレンス

> **モジュール**: `Radix.Bitmap`
> **ソース**: `Radix/Bitmap/`

## 概要

`Array Radix.UInt64`（1ワード64ビット）をバックエンドとする高密度の検証済みビットマップを提供します。すべての単一ビット操作は、ワードインデックスとビットオフセット計算により O(1) です。バルク操作（和集合、積集合など）はビットマップサイズの一致を必要とし、ワード単位で処理されます。ビットマップを `Nat → Bool` 関数としてモデル化する仕様層を含みます。

## 仕様 (`Bitmap.Spec`)

ビットインデックスからブール値への純粋関数としての抽象仕様：

```lean
def BitmapState := Nat → Bool

def setSpec (bm : BitmapState) (idx : Nat) : BitmapState
def clearSpec (bm : BitmapState) (idx : Nat) : BitmapState
def toggleSpec (bm : BitmapState) (idx : Nat) : BitmapState
def popcountSpec (bm : BitmapState) (n : Nat) : Nat
def findFirstSetSpec (bm : BitmapState) (n : Nat) : Option Nat
```

## 操作 (`Bitmap.Ops`)

### 構造体

```lean
structure Bitmap where
  numBits : Nat
  words   : Array Radix.UInt64
  hSize   : words.size = (numBits + 63) / 64
```

`hSize` 不変条件は、ワード配列が `numBits` をカバーするのに必要な64ビットワード数を正確に持つことを保証します。

### コンストラクション

```lean
def Bitmap.zeros (n : Nat) : Bitmap     -- 全ビットクリア
def Bitmap.ones (n : Nat) : Bitmap      -- 全ビットセット（numBits まで）
```

### 単一ビット操作 (O(1))

```lean
def Bitmap.test (bm : Bitmap) (idx : Nat) : Bool       -- インデックスのビットを読み取り
def Bitmap.set (bm : Bitmap) (idx : Nat) : Bitmap       -- ビットを1にセット
def Bitmap.clear (bm : Bitmap) (idx : Nat) : Bitmap     -- ビットを0にクリア
def Bitmap.toggle (bm : Bitmap) (idx : Nat) : Bitmap    -- ビットを反転
```

各操作は `wordIdx := idx / 64` と `bitIdx := idx % 64` を計算し、対象ワードに対応するビット演算を適用します。

### スキャン

```lean
def Bitmap.popcount (bm : Bitmap) : Nat                  -- セットされたビットの合計数
def Bitmap.findFirstSet (bm : Bitmap) : Option Nat        -- 最下位セットビットのインデックス
def Bitmap.findFirstClear (bm : Bitmap) : Option Nat      -- 最下位クリアビットのインデックス
```

### バルク操作

すべてのバルク操作はビットマップサイズの一致を必要とします：

```lean
def Bitmap.union (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bitmap
def Bitmap.intersection (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bitmap
def Bitmap.difference (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bitmap
def Bitmap.complement (bm : Bitmap) : Bitmap
```

- `union` — 全ワードのビット単位 OR
- `intersection` — 全ワードのビット単位 AND
- `difference` — `a AND (NOT b)`
- `complement` — ビット単位 NOT（最終ワードの余剰ビットをマスク）

### クエリ

```lean
def Bitmap.isEmpty (bm : Bitmap) : Bool      -- 全ビットがクリアか？
def Bitmap.isFull (bm : Bitmap) : Bool        -- 全ビットがセットか？
def Bitmap.isDisjoint (a b : Bitmap) (hSize : a.numBits = b.numBits) : Bool
```

`isDisjoint` は `intersection a b` にセットされたビットがない場合に `true` を返します。

## 証明 (`Bitmap.Lemmas`)

### 構造的不変条件

- コンストラクションは `hSize` を保存: `(Bitmap.zeros n).words.size = (n + 63) / 64`
- すべての単一ビットおよびバルク操作が `numBits` と `hSize` を保存

### 仕様レベルのラウンドトリップ

- `set` / `clear` ラウンドトリップ: `(bm.set idx).clear idx = bm.clear idx`
- `toggle` 退化性: `(bm.toggle idx).toggle idx = bm`
- `set` 後の `test`: `(bm.set idx).test idx = true`
- `clear` 後の `test`: `(bm.clear idx).test idx = false`

### バルク操作の性質

- `union` の可換律および結合律
- `intersection` の可換律および結合律
- `complement (complement bm) = bm`

## 使用例

```lean
-- 128ビットのビットマップを作成してビットを操作
let bm := Bitmap.zeros 128
let bm := bm.set 0
let bm := bm.set 42
let bm := bm.set 127
#eval bm.popcount              -- 3
#eval bm.test 42               -- true
#eval bm.findFirstSet          -- some 0

-- バルク操作
let a := Bitmap.zeros 64 |>.set 0 |>.set 1
let b := Bitmap.zeros 64 |>.set 1 |>.set 2
let c := Bitmap.intersection a b (by rfl)
#eval c.test 1                 -- true
#eval c.test 0                 -- false
```

## 関連ドキュメント

- [Bit](bit.md) — 整数型に対する基盤ビット演算
- [Word](word.md) — ビットマップのワードとして使用される `Radix.UInt64` 型
