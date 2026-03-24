# DMA モジュール APIリファレンス

> **モジュール**: `Radix.DMA`
> **ソース**: `Radix/DMA/`

## 概要

DMA 転送を source / destination メモリ領域間の関係としてモデル化します。メモリ順序、キャッシュコヒーレンス、転送 atomicity でパラメータ化され、実行層では descriptor の検証と `ByteArray` 上のコピーシミュレーションを提供します。

## 仕様 (`DMA.Spec`)

```lean
inductive Coherence where
  | coherent
  | nonCoherent

inductive Atomicity where
  | whole
  | burst (bytes : Nat)

structure Descriptor where
  source : Radix.Memory.Spec.Region
  destination : Radix.Memory.Spec.Region
  order : Radix.Concurrency.Spec.MemoryOrder
  coherence : Coherence
  atomicity : Atomicity

def fenceOrderSufficient (d : Descriptor) : Prop
def atomicityValid (d : Descriptor) : Prop
def Descriptor.valid (d : Descriptor) : Prop
def Descriptor.bytesMoved (d : Descriptor) : Nat
def Descriptor.stepCount (d : Descriptor) : Nat
def Descriptor.burstBytes (d : Descriptor) : Nat
def Descriptor.stepOffset (d : Descriptor) (step : Nat) : Nat
def Descriptor.stepByteCount (d : Descriptor) (step : Nat) : Nat
def Descriptor.sourceChunk (d : Descriptor) (step : Nat) : Radix.Memory.Spec.Region
def Descriptor.destinationChunk (d : Descriptor) (step : Nat) : Radix.Memory.Spec.Region
```

### 妥当性ルール

- source / destination は等しい正のサイズでなければなりません。
- burst atomicity は正の chunk size で、かつ領域サイズ以下である必要があります。
- non-coherent 転送では `seqCst` ordering が必要です。

実行層のシミュレータは source / destination の offset を別々の buffer に対する
相対位置として解釈するため、2 つの region descriptor が重なっていても許容されます。

## 操作 (`DMA.Ops`)

```lean
abbrev Descriptor := Spec.Descriptor
abbrev Coherence := Spec.Coherence
abbrev Atomicity := Spec.Atomicity

def isValid (d : Descriptor) : Bool
def canSimulate (src dst : ByteArray) (d : Descriptor) : Bool
def bytesMoved (d : Descriptor) : Nat
def burstBytes (d : Descriptor) : Nat
def stepByteCount (d : Descriptor) (step : Nat) : Nat
def sourceChunk (d : Descriptor) (step : Nat) : Radix.Memory.Spec.Region
def destinationChunk (d : Descriptor) (step : Nat) : Radix.Memory.Spec.Region
def stepCount (d : Descriptor) : Nat
def stepCopy (src dst : ByteArray) (d : Descriptor) (step : Nat) : Option ByteArray
def simulateSteps (src dst : ByteArray) (d : Descriptor) : Option (Array ByteArray)
def simulateCopy (src dst : ByteArray) (d : Descriptor) : Option ByteArray
def chainSourcesDisjoint (chain : List Descriptor) : Bool
def chainDestinationsDisjoint (chain : List Descriptor) : Bool
```

### シミュレーションの注意点

- `simulateCopy` は destination buffer のサイズを保存します。
- `canSimulate` は whole copy と staged copy の両方が使う checked precondition を公開します。
- `burstBytes`、`stepByteCount`、`sourceChunk`、`destinationChunk` は burst 転送の visibility geometry を表します。
- `stepCopy` は 1 段階ぶんの可視状態を返し、`simulateSteps` はすべての中間状態を収集します。
- descriptor が不正、または領域が out-of-bounds の場合は失敗します。
- `stepCount` はバイト数ではなく visibility step 数です。

## 証明 (`DMA.Lemmas`)

- `isValid_iff_valid`: Bool の妥当性判定が仕様 predicate と一致
- `canSimulate_eq_true_iff`: シミュレーション前提が仕様妥当性と buffer 境界条件に一致
- `bytesMoved_pos`: 妥当な descriptor は常に正のバイト数を移動する
- `stepCount_pos`: 妥当な descriptor は少なくとも 1 つの visibility step を持つ
- `stepCopy_eq_some`: staged step 成功時の結果がその chunk の splice と一致する
- `simulateCopy_eq_some`: シミュレーション成功時の結果が期待される destination splice と一致する

## 使用例

```lean
import Radix.DMA

def descriptor : Radix.DMA.Descriptor :=
  { source := { start := 0, size := 4 }
  , destination := { start := 8, size := 4 }
  , order := .seqCst
  , coherence := .nonCoherent
  , atomicity := .burst 2
  }

#eval Radix.DMA.simulateSteps (ByteArray.mk #[1, 2, 3, 4]) (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0]) descriptor
```

## 関連ドキュメント

- [Memory](memory.md) — descriptor 検証で再利用される領域演算
- [Concurrency](concurrency.md) — fence requirement に使うメモリ順序モデル
