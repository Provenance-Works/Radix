# Bit モジュール APIリファレンス

> **モジュール**: `Radix.Bit`
> **ソース**: `Radix/Bit/`

## 概要

全10種の Radix 整数型に対するビット演算、ビットスキャン、ビットフィールド操作を提供します。すべてのシフト/ローテート操作は `count % bitWidth` でカウントを正規化します（Rustセマンティクス）。

## ビット演算 (`Bit.Ops`)

すべての操作は `@[inline]` で、全10型に定義されています。例として `UInt32` を使用：

```lean
@[inline] def band (x y : UInt32) : UInt32       -- ビット単位 AND
@[inline] def bor  (x y : UInt32) : UInt32       -- ビット単位 OR
@[inline] def bxor (x y : UInt32) : UInt32       -- ビット単位 XOR
@[inline] def bnot (x : UInt32) : UInt32          -- ビット単位 NOT

-- 演算子インスタンス: &&&, |||, ^^^, ~~~
```

### シフト操作

```lean
@[inline] def shl (x : UInt32) (count : UInt32) : UInt32        -- 左シフト
@[inline] def shrLogical (x : UInt32) (count : UInt32) : UInt32  -- 論理右シフト
@[inline] def shrArith (x : UInt32) (count : UInt32) : UInt32    -- 算術右シフト（符号保存）
```

> **重要:** `count >= bitWidth` の場合、シフト量は `count % bitWidth` となります（FR-002.1a）。

### ローテート操作

```lean
@[inline] def rotl (x : UInt32) (count : UInt32) : UInt32  -- 左ローテート
@[inline] def rotr (x : UInt32) (count : UInt32) : UInt32  -- 右ローテート
```

## ビットスキャン (`Bit.Scan`)

```lean
def clz (x : UInt32) : Nat        -- 先頭ゼロカウント（0～32）
def ctz (x : UInt32) : Nat        -- 末尾ゼロカウント（0～32）
def popcount (x : UInt32) : Nat   -- ポピュレーションカウント / ハミング重み（0～32）
def bitReverse (x : UInt32) : UInt32  -- ビット順序反転
def hammingDistance (x y : UInt32) : UInt32  -- ハミング距離 = popcount(x XOR y)
```

## ビットフィールド操作 (`Bit.Field`)

```lean
def testBit (x : UInt32) (bit : Nat) : Bool           -- 位置のビットをテスト
def setBit (x : UInt32) (bit : Nat) : UInt32           -- ビットを1にセット
def clearBit (x : UInt32) (bit : Nat) : UInt32         -- ビットを0にクリア
def toggleBit (x : UInt32) (bit : Nat) : UInt32        -- ビットをトグル

-- 有効範囲の証明付きビットフィールド抽出と挿入
def extractBits (x : UInt32) (lo hi : Nat) (h : lo < hi ∧ hi ≤ 32) : UInt32
def insertBits (dest val : UInt32) (lo hi : Nat) (h : lo < hi ∧ hi ≤ 32) : UInt32
```

## 証明 (`Bit.Lemmas`)

全10型で証明済み：

### ブール代数
- 可換律: `band x y = band y x`, `bor x y = bor y x`, `bxor x y = bxor y x`
- 結合律: `band (band x y) z = band x (band y z)`
- 単位元: `band x (allOnes) = x`, `bor x 0 = x`
- 零化: `band x 0 = 0`, `bor x (allOnes) = allOnes`
- 自己逆元: `bxor x x = 0`, `bnot (bnot x) = x`
- ド・モルガン: `bnot (band x y) = bor (bnot x) (bnot y)`

### BitVec 仕様等価性
- すべての操作が `Bit.Spec` の `BitVec` 仕様と一致

### シフトの性質
- ゼロシフト恒等: `shl x 0 = x`

### スキャンの性質
- `popcount 0 = 0`
- `popcount (allOnes) = bitWidth`
- `bitReverse (bitReverse x) = x`（退化性）

### フィールドラウンドトリップ
- `extractBits (insertBits dest val lo hi h) lo hi h = val`（val が収まる場合）

## 関連ドキュメント

- [Word](word.md) — これらの操作が適用される整数型
- [アーキテクチャ: コンポーネント](../../architecture/components.md) — モジュール概要
