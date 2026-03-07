# Word Module: Interface

Version: 0.1.0-draft
Last updated: 2026-03-07

## 1. データ型 (Data Types)

### 1.1 符号なし整数 (Unsigned Integers)
Lean 4の組み込みプリミティブ型をラップし、ゼロコストでCのプリミティブにマップさせます（ADR-003, NFR-002）。

```lean
structure UInt8  where val : _root_.UInt8
structure UInt16 where val : _root_.UInt16
structure UInt32 where val : _root_.UInt32
structure UInt64 where val : _root_.UInt64
```

### 1.2 符号あり整数 (Signed Integers)
符号なし整数をラップし、2の補数として解釈します。コンパイル時は同一のC言語型として取り扱われ、メモリオーバーヘッドはありません（ADR-003）。

```lean
structure Int8  where val : _root_.UInt8
structure Int16 where val : _root_.UInt16
structure Int32 where val : _root_.UInt32
structure Int64 where val : _root_.UInt64
```

### 1.3 プラットフォーム幅依存型 (`UWord` / `IWord`)
クロスコンパイルの安全性を担保するため、プラットフォーム幅（32/64）でパラメータ化します（FR-001.1a）。ハードコードされた `System.Platform.numBits` に依存しません。

```lean
class PlatformWidth (n : Nat) where
  isValid : n = 32 ∨ n = 64

variable (platformWidth : Nat) [PlatformWidth platformWidth]

-- `UWord` は数学的・形式的には `BitVec platformWidth` として定義され、 
-- 実装レイヤー(Layer 2)においてネイティブ `size_t` と同等の 
-- ゼロコストな組み込みポインタ幅型として紐付けられます。
structure UWord where val : _root_.USize
structure IWord where val : _root_.USize
```

## 2. 算術API (FR-001.2)

全ての整数型に対して以下のAPIを提供します（例として `UInt32` を記載）。

### 2.1 Tier 1: Proof-Carrying API (推奨)
事前条件の証明を要求することで、未定義動作やパニックを仕様上およびコンパイル時に完全に排除します。

```lean
def add (x y : UInt32) (h : x.val.toNat + y.val.toNat < 2^32) : UInt32
def sub (x y : UInt32) (h : x.val.toNat ≥ y.val.toNat) : UInt32
def mul (x y : UInt32) (h : x.val.toNat * y.val.toNat < 2^32) : UInt32
def div (x y : UInt32) (h : y ≠ 0) : UInt32
def rem (x y : UInt32) (h : y ≠ 0) : UInt32
```

### 2.2 Tier 2: Mode-Based API (利便性ラッパー)
厳密な証明の取り回しが困難なシステムプログラミングの文脈向けに、動作が完全に規定された全域関数（またはOption）を提供します。

```lean
-- Wrapping
def wrappingAdd (x y : UInt32) : UInt32
def wrappingSub (x y : UInt32) : UInt32
def wrappingMul (x y : UInt32) : UInt32

-- Saturating
def saturatingAdd (x y : UInt32) : UInt32
def saturatingSub (x y : UInt32) : UInt32

-- Checked
def checkedAdd (x y : UInt32) : Option UInt32
def checkedSub (x y : UInt32) : Option UInt32
def checkedMul (x y : UInt32) : Option UInt32
def checkedDiv (x y : UInt32) : Option UInt32
def checkedRem (x y : UInt32) : Option UInt32

-- Overflowing
def overflowingAdd (x y : UInt32) : UInt32 × Bool
def overflowingSub (x y : UInt32) : UInt32 × Bool
def overflowingMul (x y : UInt32) : UInt32 × Bool
```