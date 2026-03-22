# 数値型クラス API リファレンス

> **モジュール**: `Radix.Word.Numeric`
> **ソース**: `Radix/Word/Numeric.lean`, `Radix/Word/Lemmas/Numeric.lean`

## 概要

Radixの全10整数型に対するジェネリックな数値型クラスを提供します。各具象型ごとにロジックを複製する代わりに、ビット幅に依存しないコードを一度だけ記述できます。符号なし境界、符号付き境界、ビット演算の3つの型クラスをカバーします。

## 型クラス

### `BoundedUInt`

符号なし固定幅整数のジェネリック型クラス。`LawfulFixedWidth`を拡張。

```lean
class BoundedUInt (α : Type) extends LawfulFixedWidth α where
  minVal        : α                    -- 最小値（常に0）
  maxVal        : α                    -- 最大値（2^bitWidth - 1）
  toNat         : α → Nat             -- 自然数への変換
  wrappingAdd   : α → α → α           -- (x + y) mod 2^bitWidth
  wrappingSub   : α → α → α           -- (x - y) mod 2^bitWidth
  wrappingMul   : α → α → α           -- (x * y) mod 2^bitWidth
  saturatingAdd : α → α → α           -- min(x + y, maxVal)
  saturatingSub : α → α → α           -- max(x - y, 0)
  checkedAdd    : α → α → Option α    -- オーバーフロー時none
  checkedSub    : α → α → Option α    -- アンダーフロー時none
  checkedMul    : α → α → Option α    -- オーバーフロー時none
```

**インスタンス**: `UInt8`, `UInt16`, `UInt32`, `UInt64`

### `BoundedInt`

符号付き固定幅整数のジェネリック型クラス（2の補数）。`FixedWidth`を拡張。

```lean
class BoundedInt (α : Type) extends FixedWidth α, Add α, Sub α, Mul α, Neg α where
  minVal   : α             -- 最小値（-2^(bitWidth-1)）
  maxVal   : α             -- 最大値（2^(bitWidth-1) - 1）
  toInt    : α → Int       -- 2の補数解釈
  isNeg    : α → Bool      -- MSB = 1
  fromInt  : Int → α       -- Intからの切り詰め変換
```

**インスタンス**: `Int8`, `Int16`, `Int32`, `Int64`

### `BitwiseOps`

ビット演算のジェネリック型クラス。`FixedWidth`を拡張。

```lean
class BitwiseOps (α : Type) extends FixedWidth α where
  band     : α → α → α        -- ビットAND
  bor      : α → α → α        -- ビットOR
  bxor     : α → α → α        -- ビットXOR
  bnot     : α → α            -- ビットNOT
  testBit  : α → Nat → Bool   -- 特定ビット位置のテスト
  popcount : α → α            -- ポピュレーションカウント
```

**インスタンス**: `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Int8`, `Int16`, `Int32`, `Int64`

## ジェネリックユーティリティ関数

```lean
def genericZero {α : Type} [BoundedUInt α] : α           -- ゼロ（minVal）
def genericMaxVal {α : Type} [BoundedUInt α] : α         -- 最大値
def genericPopcount {α : Type} [BitwiseOps α] (x : α) : α  -- ポピュレーションカウント
def isZero {α : Type} [BoundedUInt α] (x : α) : Bool     -- ゼロ判定
def isMax {α : Type} [BoundedUInt α] (x : α) : Bool      -- 最大値判定
```

## 検証済みプロパティ (`Word.Lemmas.Numeric`)

| 定理 | 内容 |
|------|------|
| `wrappingAdd_minVal` | `wrappingAdd x minVal = x`（加算の単位元）|
| `wrappingAdd_comm` | `wrappingAdd x y = wrappingAdd y x`（可換性）|
| `minVal_le_maxVal` | `toNat minVal ≤ toNat maxVal`（符号なし境界の順序）|
| `BoundedInt.minVal_le_maxVal` | `toInt minVal ≤ toInt maxVal`（符号付き境界の順序、bitWidth > 0）|

## 使用例

```lean
import Radix.Word.Numeric
open Radix

-- 任意の符号なし整数幅で動作するジェネリック関数
def showBounds {α : Type} [inst : BoundedUInt α] (name : String) : IO Unit := do
  IO.println s!"{name}: min={inst.toNat inst.minVal}, max={inst.toNat inst.maxVal}"

-- 具象型で使用
#eval showBounds (α := UInt8)  "UInt8"   -- UInt8: min=0, max=255
#eval showBounds (α := UInt32) "UInt32"  -- UInt32: min=0, max=4294967295

-- BitwiseOpsによるジェネリックpopcount
def countOnes {α : Type} [BitwiseOps α] (x : α) : α := BitwiseOps.popcount x
```

## アーキテクチャ

- **Layer 2**（検証済み実装）: `Radix.Word.Numeric` の型クラス定義とインスタンス
- **Layer 3**（検証済み仕様）: `Radix.Word.Lemmas.Numeric` の証明

注：数値型クラスは個別のLayer 3 Specモジュールを持ちません。これは具象型上の型クラスという実装レベルの抽象化であるためです。仕様上の義務は `LawfulFixedWidth` と `FixedWidth` から継承されます。
