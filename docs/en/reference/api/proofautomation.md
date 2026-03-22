# Proof Automation API Reference

> **Module**: `Radix.ProofAutomation`
> **Source**: `Radix/ProofAutomation.lean`

## Overview

Provides lightweight tactic macros for common proof patterns that appear throughout Radix and downstream proofs. The goal is to reduce boilerplate in arithmetic and decidable-goal proofs without introducing custom trusted code.

## Tactics

```lean
syntax "radix_decide" : tactic
syntax "radix_omega" : tactic
```

### `radix_decide`

Expands to a small fallback chain:

```lean
first | decide | simp | simp_all | omega
```

Use it for closed goals or goals that can be discharged after simplification.

### `radix_omega`

Simplifies hypotheses and goals before handing the result to Presburger arithmetic:

```lean
simp at * <;> omega
```

Use it for linear arithmetic facts such as bounds, offsets, or order transitivity.

## Examples

```lean
import Radix.ProofAutomation

example : 4 + 5 = 9 := by
  radix_decide

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  radix_omega
```

## Related Documents

- [Memory](memory.md) — region and layout proofs often reduce to arithmetic goals
- [Alignment](alignment.md) — alignment proofs are a common source of `omega` obligations
