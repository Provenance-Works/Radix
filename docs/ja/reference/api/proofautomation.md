# Proof Automation APIリファレンス

> **モジュール**: `Radix.ProofAutomation`
> **ソース**: `Radix/ProofAutomation.lean`

## 概要

Radix と downstream proof に頻出するパターン向けの軽量 tactic macro を提供します。目的は、custom trusted code を増やさずに算術 goal や decidable goal の boilerplate を減らすことです。

## Tactics

```lean
syntax "radix_decide" : tactic
syntax "radix_omega" : tactic
syntax "radix_simp" : tactic
syntax "radix_finish" : tactic
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

### `radix_simp`

次の simplification-first chain に展開されます。

```lean
first | simp | simp_all | aesop | exact (by decide)
```

局所的な書き換え、分岐簡約、仮定の伝播で goal が消える場面に向きます。

### `radix_finish`

partial simplification で止まらないよう、証明項を返す branch だけで構成した最終クローザです。

```lean
first
  | exact (by try simp at *; omega)
  | exact Nat.zero_le _
  | exact Nat.le_refl _
  | exact Nat.le_trans ‹_› ‹_›
  | exact (by simp at *; decide)
  | exact (by aesop)
  | exact (by decide)
```

残り goal が算術、簡約、decidable のどれに落ちてもよい短い証明の終端に向きます。

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

example : (if True then (6 : Nat) else 0) = 6 := by
  radix_simp

example : 2 ≤ 6 := by
  have h1 : 2 ≤ 4 := by decide
  have h2 : 4 ≤ 6 := by decide
  radix_finish
```

## 関連ドキュメント

- [Memory](memory.md) — 領域やレイアウトの証明は算術 goal に落ちやすい
- [Alignment](alignment.md) — alignment 証明は `omega` obligation の典型例
