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
first | decide | simp | simp_all | omega
```

閉じた goal や、簡約後に解ける goal に向きます。

### `radix_omega`

仮定と goal を簡約してから Presburger arithmetic に渡します。

```lean
simp at * <;> omega
```

境界、オフセット、順序推移のような線形算術に向きます。

## 使用例

```lean
import Radix.ProofAutomation

example : 4 + 5 = 9 := by
  radix_decide

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  radix_omega
```

## 関連ドキュメント

- [Memory](memory.md) — 領域やレイアウトの証明は算術 goal に落ちやすい
- [Alignment](alignment.md) — alignment 証明は `omega` obligation の典型例
