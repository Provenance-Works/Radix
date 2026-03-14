# Concurrency モジュール APIリファレンス

> **モジュール**: `Radix.Concurrency`
> **ソース**: `Radix/Concurrency/`

## 概要

C11/C++11 メモリモデルに従う並行アトミック操作をモデル化します。これは**純粋モデル**であり、実際のハードウェアとの対話はありません。すべての操作は抽象アトミックセル上の状態遷移としてモデル化されています。

## メモリ順序 (`Concurrency.Spec`)

```lean
inductive MemoryOrder where
  | relaxed  -- スレッド間の順序保証なし
  | acquire  -- 以降のリード/ライトがこのロードより前に移動不可
  | release  -- 以前のリード/ライトがこのストアより後に移動不可
  | acqRel   -- acquire と release の両方（RMW 操作用）
  | seqCst   -- 全スレッドにまたがる完全なグローバル順序

def MemoryOrder.strength : MemoryOrder → Nat
def MemoryOrder.isAtLeast (a b : MemoryOrder) : Bool
```

## アトミックセル (`Concurrency.Atomic`)

```lean
structure AtomicCell where
  val : Nat

def AtomicCell.new (v : Nat) : AtomicCell

-- 操作は結果 + 新しいセル状態を返す
def atomicLoad (cell : AtomicCell) (order : MemoryOrder) : LoadResult × AtomicCell
def atomicStore (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : StoreResult × AtomicCell
def atomicCAS (cell : AtomicCell) (expected new_ : Nat) (succ fail : MemoryOrder) : CASResult × AtomicCell
def atomicExchange (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell

-- フェッチ・アンド・モディファイ
def fetchAdd (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
def fetchSub (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
def fetchAnd (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
def fetchOr  (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
def fetchXor (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
```

## 順序ユーティリティ (`Concurrency.Ordering`)

```lean
def strengthen (order : MemoryOrder) : MemoryOrder
def combineLoadStore (load store : MemoryOrder) : MemoryOrder
def hasAcquireSemantics (order : MemoryOrder) : Bool
def hasReleaseSemantics (order : MemoryOrder) : Bool
def validOrderForAccess (kind : AccessKind) (order : MemoryOrder) : Bool
```

## 証明 (`Concurrency.Lemmas`)

- 順序強度の証明と推移律
- CAS 成功/失敗動作
- フェッチ操作の正しさ
- ストア-ロードのラウンドトリップ
- `programOrder` の推移律
- シングルスレッド線形化可能性
- 空/単一トレースのデータ競合フリー性

## 信頼仮定 (`Concurrency.Assumptions`)

| 公理 | 主張 |
|-------|---------|
| `trust_atomic_word_access` | ワードサイズのアトミック操作は不可分 |
| `trust_cas_atomicity` | CAS はアトミック（比較 + スワップが1ステップ） |
| `trust_seqcst_total_order` | SeqCst 操作は完全なグローバル順序を持つ |
| `trust_acquire_release_sync` | Acquire/Release ペアはスレッドを同期する |
| `trust_fence_ordering` | フェンス命令はメモリ順序を強制する |

## 関連ドキュメント

- [BareMetal](baremetal.md) — ベアメタルサポート（OS なし）
- [アーキテクチャ: コンポーネント](../../architecture/components.md) — モジュール概要
