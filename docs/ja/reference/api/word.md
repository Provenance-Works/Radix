# Word モジュール APIリファレンス

> **モジュール**: `Radix.Word`
> **ソース**: `Radix/Word/`

## 概要

Word モジュールは固定幅整数型（符号なし・符号付き）を提供し、複数の算術モードと正しさの形式証明を備えています。Radix の基盤モジュールであり、他のすべてのモジュールがこれに依存します。

## 型

### 符号なし整数

| 型 | 内部ストレージ | ビット幅 | 範囲 |
|------|-----------------|-----------|-------|
| `Radix.UInt8` | `_root_.UInt8` | 8 | 0 ～ 255 |
| `Radix.UInt16` | `_root_.UInt16` | 16 | 0 ～ 65,535 |
| `Radix.UInt32` | `_root_.UInt32` | 32 | 0 ～ 4,294,967,295 |
| `Radix.UInt64` | `_root_.UInt64` | 64 | 0 ～ 18,446,744,073,709,551,615 |

### 符号付き整数（2の補数）

| 型 | 内部ストレージ | ビット幅 | 範囲 |
|------|-----------------|-----------|-------|
| `Radix.Int8` | `_root_.UInt8` | 8 | -128 ～ 127 |
| `Radix.Int16` | `_root_.UInt16` | 16 | -32,768 ～ 32,767 |
| `Radix.Int32` | `_root_.UInt32` | 32 | -2,147,483,648 ～ 2,147,483,647 |
| `Radix.Int64` | `_root_.UInt64` | 64 | -9,223,372,036,854,775,808 ～ 9,223,372,036,854,775,807 |

### プラットフォーム幅整数

| 型 | 内部ストレージ | ビット幅 | 制約 |
|------|-----------------|-----------|------------|
| `Radix.UWord` | `BitVec w` | 32 または 64 | `PlatformWidth w` |
| `Radix.IWord` | `BitVec w` | 32 または 64 | `PlatformWidth w` |

## 変換

### 型変換

```lean
@[inline] def toBuiltin (x : UInt32) : _root_.UInt32  -- Lean 4 組み込み型へ
@[inline] def fromBuiltin (x : _root_.UInt32) : UInt32 -- Lean 4 組み込み型から
@[inline] def toBitVec (x : UInt32) : BitVec 32        -- BitVec へ（Layer 3）
@[inline] def fromBitVec (x : BitVec 32) : UInt32      -- BitVec から
@[inline] def toNat (x : UInt32) : Nat                  -- 自然数へ
```

### 符号付き固有

```lean
@[inline] def toInt (x : Int32) : Int       -- 符号付き解釈
@[inline] def fromInt (i : Int) : Int32     -- Int から（トランケーティング）
@[inline] def slt (a b : Int32) : Bool      -- 符号付き未満（ゼロコスト）
@[inline] def sle (a b : Int32) : Bool      -- 符号付き以下
@[inline] def sgt (a b : Int32) : Bool      -- 符号付き超過
@[inline] def sge (a b : Int32) : Bool      -- 符号付き以上
```

## 算術（型ごと）

全10型が以下の操作をサポートします。ここでは `UInt32` の例を示します：

### Tier 1: 証明付き（推奨）

```lean
@[inline] def addChecked (x y : UInt32) (h : x.toNat + y.toNat < 2^32) : UInt32
@[inline] def subChecked (x y : UInt32) (h : y.toNat ≤ x.toNat) : UInt32
@[inline] def mulChecked (x y : UInt32) (h : x.toNat * y.toNat < 2^32) : UInt32
```

### Tier 2: ラッピング

```lean
@[inline] def wrappingAdd (x y : UInt32) : UInt32
@[inline] def wrappingSub (x y : UInt32) : UInt32
@[inline] def wrappingMul (x y : UInt32) : UInt32
```

> **注記:** `wrappingDiv` や `wrappingRem` はありません — ゼロ除算は安全にラップできないため、`checkedDiv` を使用してください。

### Tier 2: 飽和

```lean
@[inline] def saturatingAdd (x y : UInt32) : UInt32  -- オーバーフロー時に MAX にクランプ
@[inline] def saturatingSub (x y : UInt32) : UInt32  -- アンダーフロー時に 0 にクランプ
@[inline] def saturatingMul (x y : UInt32) : UInt32  -- オーバーフロー時に MAX にクランプ
```

### Tier 2: チェック付き

```lean
@[inline] def checkedAdd (x y : UInt32) : Option UInt32  -- オーバーフロー時 none
@[inline] def checkedSub (x y : UInt32) : Option UInt32  -- アンダーフロー時 none
@[inline] def checkedMul (x y : UInt32) : Option UInt32  -- オーバーフロー時 none
@[inline] def checkedDiv (x y : UInt32) : Option UInt32  -- y=0 時 none
@[inline] def checkedRem (x y : UInt32) : Option UInt32  -- y=0 時 none
```

### Tier 2: オーバーフロー付き

```lean
@[inline] def overflowingAdd (x y : UInt32) : UInt32 × Bool
@[inline] def overflowingSub (x y : UInt32) : UInt32 × Bool
@[inline] def overflowingMul (x y : UInt32) : UInt32 × Bool
```

## ビット幅変換 (`Word.Conv`)

```lean
-- ゼロ拡張（符号なし拡幅）
@[inline] def UInt8.toUInt16 (x : UInt8) : UInt16
@[inline] def UInt8.toUInt32 (x : UInt8) : UInt32
@[inline] def UInt16.toUInt32 (x : UInt16) : UInt32
@[inline] def UInt32.toUInt64 (x : UInt32) : UInt64

-- トランケート（縮小）
@[inline] def UInt16.toUInt8 (x : UInt16) : UInt8
@[inline] def UInt32.toUInt16 (x : UInt32) : UInt16
@[inline] def UInt64.toUInt32 (x : UInt64) : UInt32

-- 符号拡張（符号付き拡幅）
@[inline] def Int8.toInt16 (x : Int8) : Int16
@[inline] def Int8.toInt32 (x : Int8) : Int32
@[inline] def Int16.toInt32 (x : Int16) : Int32
@[inline] def Int32.toInt64 (x : Int32) : Int64

-- レジスタ内部の符号拡張（Wasm サポート）
@[inline] def UInt32.signExtend8 (x : UInt32) : UInt32
@[inline] def UInt32.signExtend16 (x : UInt32) : UInt32
@[inline] def UInt64.signExtend8 (x : UInt64) : UInt64
@[inline] def UInt64.signExtend16 (x : UInt64) : UInt64
@[inline] def UInt64.signExtend32 (x : UInt64) : UInt64
```

## 証明 (`Word.Lemmas`)

### 環の性質 (`Word.Lemmas.Ring`)

全10型で証明済み：
- 可換律: `wrappingAdd x y = wrappingAdd y x`
- 結合律: `wrappingAdd (wrappingAdd x y) z = wrappingAdd x (wrappingAdd y z)`
- 単位元: `wrappingAdd x 0 = x`, `wrappingMul x 1 = x`
- 分配律: `wrappingMul x (wrappingAdd y z) = wrappingAdd (wrappingMul x y) (wrappingMul x z)`

### オーバーフローの性質 (`Word.Lemmas.Overflow`)

- ラッピング仕様: wrappingAdd は `(x + y) % 2^n` に一致
- チェック付き: オーバーフロー時かつその時に限り none
- 飽和: 境界値へのクランプ
- オーバーフロー付き: フラグの正しさ
- 符号付き `MIN / -1` と `MIN % -1` の処理

### BitVec 等価性 (`Word.Lemmas.BitVec`)

- ラウンドトリップ: 全10型で `fromBitVec (toBitVec x) = x`
- 操作等価性: `wrappingAdd.toBitVec = BitVec.add`

### 変換の性質 (`Word.Lemmas.Conv`)

- ゼロ拡張は値を保存
- 符号拡張は符号付き解釈を保存
- トランケートは非可逆
- キャストはビット保存
- レジスタ符号拡張仕様: `signExtend8.toBitVec = BitVec.signExtend 32 (x.toBitVec.truncate 8)`

## 関連ドキュメント

- [Bit](bit.md) — これらの型に対するビット演算
- [アーキテクチャ: コンポーネント](../../architecture/components.md) — モジュール概要
