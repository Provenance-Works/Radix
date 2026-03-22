/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Proof Automation Helpers

Small tactic combinators for common Radix proof patterns.

## References

- v0.3.0 Roadmap: Proof Automation Tactics
-/

set_option autoImplicit false

syntax (name := radixDecideTac) "radix_decide" : tactic
syntax (name := radixOmegaTac) "radix_omega" : tactic

macro_rules
  | `(tactic| radix_decide) =>
      `(tactic|
        first
          | omega
          | simp
          | simp_all
          | exact (by decide))

macro_rules
  | `(tactic| radix_omega) =>
      `(tactic|
        first
          | exact Nat.le_trans ‹_› ‹_›
          | exact Nat.zero_le _
          | try simp at *; omega
          | aesop
          | exact (by decide))
