# Timer モジュール APIリファレンス

> **モジュール**: `Radix.Timer`
> **ソース**: `Radix/Timer/`

## 概要

単調クロックと deadline のための小さな検証済みモデルを提供します。リアルタイム推論、timeout 判定、bare-metal や systems code の scheduler 的証明で使うことを想定しています。

## 仕様 (`Timer.Spec`)

```lean
structure Clock where
  ticks : Nat

structure Deadline where
  deadlineTick : Nat

def zero : Clock
def advance (clock : Clock) (delta : Nat) : Clock
def elapsed (start finish : Clock) : Nat
def Monotonic (before after : Clock) : Prop
def deadlineAfter (clock : Clock) (timeout : Nat) : Deadline
def expired (clock : Clock) (deadline : Deadline) : Prop
def remaining (clock : Clock) (deadline : Deadline) : Nat
```

## 操作 (`Timer.Ops`)

```lean
abbrev Clock := Spec.Clock
abbrev Deadline := Spec.Deadline

def zero : Clock
def now (clock : Clock) : Nat
def tick (clock : Clock) (delta : Nat := 1) : Clock
def after (clock : Clock) (timeout : Nat) : Deadline
def hasExpired (clock : Clock) (deadline : Deadline) : Bool
def remaining (clock : Clock) (deadline : Deadline) : Nat
def elapsed (start finish : Clock) : Nat
```

### 意味論

- `tick` はクロックを単調に進めます。
- `remaining` は deadline を過ぎると 0 に飽和します。
- `hasExpired` は仕様層 `expired` predicate の Bool 版です。

## 証明 (`Timer.Lemmas`)

- `advance_monotonic`: クロックを進めると単調性が保たれる
- `remaining_zero_of_expired`: deadline 後は残時間が 0 になる
- `expired_of_remaining_zero`: 残時間 0 なら期限切れ
- `tick_monotonic`: 操作層の tick でも単調性が保たれる
- `after_not_expired`: 正の timeout は即座には期限切れにならない

## 使用例

```lean
import Radix.Timer

def demo : Nat :=
  let start := Radix.Timer.zero
  let deadline := Radix.Timer.after start 10
  let mid := Radix.Timer.tick start 4
  Radix.Timer.remaining mid deadline
```

## 関連ドキュメント

- [BareMetal](baremetal.md) — 単調 deadline を消費する downstream runtime model
- [System](system.md) — timeout logic を積み上げられる host-boundary wrapper
