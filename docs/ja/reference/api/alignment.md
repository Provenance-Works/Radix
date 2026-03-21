# アラインメントモジュール APIリファレンス

> **モジュール**: `Radix.Alignment`
> **ソース**: `Radix/Alignment/`

## 概要

システムプログラミング向けのアドレスおよびオフセットアラインメント操作を提供します。汎用的なモジュラーアラインメントと、2のべき乗アラインメントに最適化されたビット演算による高速パスの両方をサポートします。型にアラインメント要件を関連付ける型クラスと、正当性を保証する検証済み補題の完全なセットを含みます。

## 仕様 (`Alignment.Spec`)

検証の基盤として使用される純粋な数学的定義：

```lean
def isAligned (offset align : Nat) : Prop      -- offset は align で割り切れる
def alignUp (offset align : Nat) : Nat          -- align の次の倍数に切り上げ
def alignDown (offset align : Nat) : Nat        -- align の前の倍数に切り下げ
def isPowerOfTwo (n : Nat) : Prop               -- n は2のべき乗
def alignPadding (offset align : Nat) : Nat     -- 次のアラインされたオフセットまでのバイト数
```

## 操作 (`Alignment.Ops`)

仕様に一致する実行可能な実装：

### コアアラインメント

```lean
def isAligned (offset align : Nat) : Bool       -- 割り切れるかチェック
def alignUp (offset align : Nat) : Nat          -- 次の倍数に切り上げ
def alignDown (offset align : Nat) : Nat        -- 前の倍数に切り下げ
def alignPadding (offset align : Nat) : Nat     -- 次のアラインされたオフセットまでのパディング
def isPowerOfTwo (n : Nat) : Bool               -- 2のべき乗判定
```

### 2のべき乗高速パス

アラインメントが2のべき乗であることが既知の場合に、除算を回避するビット演算実装：

```lean
def alignUpPow2 (offset align : Nat) : Nat      -- (offset + align - 1) &&& ~~~(align - 1)
def alignDownPow2 (offset align : Nat) : Nat     -- offset &&& ~~~(align - 1)
def isAlignedPow2 (offset align : Nat) : Bool    -- offset &&& (align - 1) == 0
```

> **注意:** これらの関数は `align` が2のべき乗であることを前提としています。2のべき乗でない値に対する動作は未定義です。

### 型アラインメント定数

一般的な整数型の標準アラインメント値：

```lean
def alignmentOfU8  : Nat    -- 1
def alignmentOfU16 : Nat    -- 2
def alignmentOfU32 : Nat    -- 4
def alignmentOfU64 : Nat    -- 8
```

### 型クラス

```lean
class HasAlignment (α : Type) where
  alignment : Nat

def alignmentOf (α : Type) [HasAlignment α] : Nat
```

ジェネリックコードから型の自然なアラインメントを問い合わせることができます：

```lean
-- 使用例
#eval alignmentOf Radix.UInt32    -- 4
#eval alignmentOf Radix.UInt64    -- 8
```

## 証明 (`Alignment.Lemmas`)

### サンドイッチ性質

- `alignUp_ge`: `offset ≤ alignUp offset align`
- `alignDown_le`: `alignDown offset align ≤ offset`
- `alignDown_le_alignUp`: `alignDown offset align ≤ alignUp offset align`

### アラインメントの正当性

- `alignUp_isAligned`: `isAligned (alignUp offset align) align`
- `isAligned_zero`: `isAligned 0 align`
- `isAligned_mul`: `isAligned (n * align) align`

### パディングと等価性

- `alignPadding_spec`: `alignUp offset align = offset + alignPadding offset align`
- `pow2_equivalence`: `isPowerOfTwo align → alignUpPow2 offset align = alignUp offset align`

## 使用例

```lean
-- 基本的なアラインメント操作
#eval Radix.Alignment.Ops.alignUp 13 4        -- 16
#eval Radix.Alignment.Ops.alignDown 13 4      -- 12
#eval Radix.Alignment.Ops.alignPadding 13 4   -- 3
#eval Radix.Alignment.Ops.isAligned 16 4       -- true

-- 2のべき乗高速パス
#eval Radix.Alignment.Ops.alignUpPow2 13 4    -- 16
#eval Radix.Alignment.Ops.isAlignedPow2 16 8  -- true
```

## 関連ドキュメント

- [Memory](memory.md) — アラインメントに依存するバッファおよびレイアウト操作
- [メモリプール](memorypool.md) — アラインされた割り当てを使用するアロケータ
