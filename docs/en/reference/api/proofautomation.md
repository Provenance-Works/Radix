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
first | omega | simp | simp_all | exact (by decide)
```

Use it for small equalities, closed propositions, or decidable goals that become trivial after simplification.

### `radix_omega`

Expands to a short arithmetic-oriented chain:

```lean
first
  | exact Nat.le_trans ‹_› ‹_›
  | exact Nat.zero_le _
  | try simp at *; omega
  | aesop
  | exact (by decide)
```

Use it for order transitivity, zero-lower-bound goals, and arithmetic side conditions that become Presburger after simplification.

## Examples

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

## Related Documents

- [Memory](memory.md) — region and layout proofs often reduce to arithmetic goals
- [Alignment](alignment.md) — alignment proofs are a common source of `omega` obligations
