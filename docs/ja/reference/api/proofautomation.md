# Proof Automation APIリファレンス

> **モジュール**: `Radix.ProofAutomation`
> **ソース**: `Radix/ProofAutomation.lean`

## 概要

Radix と downstream proof に頻出するパターン向けの軽量 tactic macro を提供します。目的は、custom trusted code を増やさずに算術 goal や decidable goal の boilerplate を減らすことです。

## Tactics

```lean
syntax "radix_decide" : tactic
syntax "radix_omega" : tactic
```

### `radix_decide`

次の fallback chain に展開されます。

```lean
first | omega | simp | simp_all | exact (by decide)
```

小さな等式、閉じた proposition、簡約後に自明化する decidable goal に向きます。

### `radix_omega`

次の算術寄り fallback chain に展開されます。

```lean
first
  | exact Nat.le_trans ‹_› ‹_›
  | exact Nat.zero_le _
  | try simp at *; omega
  | aesop
  | exact (by decide)
```

順序推移、`0 ≤ _` 形の goal、簡約後に Presburger arithmetic に落ちる副条件に向きます。

## 使用例

```lean
import Radix.ProofAutomation

example : 4 + 5 = 9 := by
  radix_decide

example (a b : Nat) (h : a = b) : b = a := by
  radix_decide

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  radix_omega

example (a : Nat) : 0 ≤ a := by
  radix_omega
```

## 関連ドキュメント

- [Memory](memory.md) — 領域やレイアウトの証明は算術 goal に落ちやすい
- [Alignment](alignment.md) — alignment 証明は `omega` obligation の典型例
