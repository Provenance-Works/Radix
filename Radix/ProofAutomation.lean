/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Proof Automation Helpers

Domain-specific tactic combinators for common Radix proof patterns:
overflow checking, alignment, region disjointness, and bitwise reasoning.

## Tactics

| Tactic | Purpose |
|--------|---------|
| `radix_decide` | General-purpose proof combinator: omega → simp → decide |
| `radix_omega` | Nat inequality chains and transitivity |
| `radix_simp` | Simplification cascade: simp → simp_all → aesop |
| `radix_finish` | Last-resort: combines all strategies |
| `radix_bitwise` | Bitwise/boolean goals: Nat.testBit, land, lor, xor |
| `radix_align` | Alignment goals: divisibility, power-of-two, modular arithmetic |
| `radix_region` | Region disjointness: non-overlapping address ranges |
| `radix_overflow` | Overflow checking: bounded arithmetic on Nat/UInt |

## References

- v0.3.0 Roadmap: Proof Automation Tactics
-/

set_option autoImplicit false

-- ════════════════════════════════════════════════════════════════════
-- General-Purpose Tactics
-- ════════════════════════════════════════════════════════════════════

syntax (name := radixDecideTac) "radix_decide" : tactic
syntax (name := radixOmegaTac) "radix_omega" : tactic
syntax (name := radixSimpTac) "radix_simp" : tactic
syntax (name := radixFinishTac) "radix_finish" : tactic

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

macro_rules
  | `(tactic| radix_simp) =>
      `(tactic|
        first
          | simp
          | simp_all
          | aesop
          | exact (by decide))

macro_rules
  | `(tactic| radix_finish) =>
      `(tactic|
        first
          | exact (by
              try simp at *
              omega)
          | exact Nat.zero_le _
          | exact Nat.le_refl _
          | exact Nat.le_trans ‹_› ‹_›
          | exact (by
              simp at *
              decide)
          | exact (by aesop)
          | exact (by decide))

-- ════════════════════════════════════════════════════════════════════
-- Bitwise Automation
-- ════════════════════════════════════════════════════════════════════

/-- `radix_bitwise` attempts to close goals involving bitwise operations
    (land, lor, xor, shiftLeft, shiftRight, testBit) by unfolding
    definitions and applying omega/decide. -/
syntax (name := radixBitwiseTac) "radix_bitwise" : tactic

macro_rules
  | `(tactic| radix_bitwise) =>
      `(tactic|
        first
          | simp only [Nat.land_comm, Nat.lor_comm, Nat.xor_comm,
                        Nat.land_assoc, Nat.lor_assoc, Nat.xor_assoc,
                        Nat.land_zero, Nat.zero_land,
                        Nat.lor_zero, Nat.zero_lor,
                        Nat.xor_zero, Nat.zero_xor,
                        Nat.xor_self, Nat.land_self, Nat.lor_self]
          | simp [Nat.testBit, Nat.shiftRight, Nat.shiftLeft]
          | (try simp_all; omega)
          | exact (by decide))

-- ════════════════════════════════════════════════════════════════════
-- Alignment Automation
-- ════════════════════════════════════════════════════════════════════

/-- Helper: check that a number is a power of two. -/
def Radix.ProofAutomation.isPowerOfTwo (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) == 0

/-- `radix_align` solves goals about alignment (divisibility by power of two,
    modular arithmetic). Works well with `addr % alignment = 0` patterns. -/
syntax (name := radixAlignTac) "radix_align" : tactic

macro_rules
  | `(tactic| radix_align) =>
      `(tactic|
        first
          | omega
          | simp only [Nat.mul_mod_cancel, Nat.add_mod_right, Nat.mod_self,
                        Nat.zero_mod, Nat.mul_mod_cancel_left,
                        Nat.dvd_refl, Nat.dvd_zero]
          | (try simp at *; omega)
          | exact (by decide))

-- ════════════════════════════════════════════════════════════════════
-- Region Disjointness Automation
-- ════════════════════════════════════════════════════════════════════

/-- Predicate for non-overlapping address ranges: [start1, start1+size1) and
    [start2, start2+size2) do not intersect. -/
def Radix.ProofAutomation.regionsDisjoint
    (start1 size1 start2 size2 : Nat) : Prop :=
  start1 + size1 ≤ start2 ∨ start2 + size2 ≤ start1

/-- `Decidable` instance for regionsDisjoint. -/
instance (start1 size1 start2 size2 : Nat) :
    Decidable (Radix.ProofAutomation.regionsDisjoint start1 size1 start2 size2) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `radix_region` solves region disjointness goals by reducing to
    arithmetic and applying omega. -/
syntax (name := radixRegionTac) "radix_region" : tactic

macro_rules
  | `(tactic| radix_region) =>
      `(tactic|
        first
          | exact Or.inl (by omega)
          | exact Or.inr (by omega)
          | (simp only [Radix.ProofAutomation.regionsDisjoint]; omega)
          | omega)

-- ════════════════════════════════════════════════════════════════════
-- Overflow Checking Automation
-- ════════════════════════════════════════════════════════════════════

/-- Overflow predicate: a + b does not exceed bound. -/
def Radix.ProofAutomation.addNoOverflow (a b bound : Nat) : Prop :=
  a + b ≤ bound

/-- `Decidable` instance for addNoOverflow. -/
instance (a b bound : Nat) :
    Decidable (Radix.ProofAutomation.addNoOverflow a b bound) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Overflow predicate: a * b does not exceed bound. -/
def Radix.ProofAutomation.mulNoOverflow (a b bound : Nat) : Prop :=
  a * b ≤ bound

/-- `Decidable` instance for mulNoOverflow. -/
instance (a b bound : Nat) :
    Decidable (Radix.ProofAutomation.mulNoOverflow a b bound) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- `radix_overflow` solves bounded arithmetic goals by applying omega
    and simplification of Nat overflow conditions. -/
syntax (name := radixOverflowTac) "radix_overflow" : tactic

macro_rules
  | `(tactic| radix_overflow) =>
      `(tactic|
        first
          | omega
          | simp only [Radix.ProofAutomation.addNoOverflow,
                        Radix.ProofAutomation.mulNoOverflow]; omega
          | (try simp at *; omega)
          | exact (by decide))

-- ════════════════════════════════════════════════════════════════════
-- Convenience Lemmas for Common Patterns
-- ════════════════════════════════════════════════════════════════════

namespace Radix.ProofAutomation

/-- Two adjacent regions of the same size starting at 0 and n are disjoint. -/
theorem adjacent_regions_disjoint (n : Nat) (_ : 0 < n) :
    regionsDisjoint 0 n n n := by
  simp [regionsDisjoint]

/-- A zero-size region at start is disjoint from any region starting at or after start. -/
theorem empty_region_disjoint_left (start1 start2 size2 : Nat)
    (h : start1 ≤ start2) :
    regionsDisjoint start1 0 start2 size2 := by
  left; omega

/-- Region disjointness is symmetric. -/
theorem regionsDisjoint_comm (s1 n1 s2 n2 : Nat) :
    regionsDisjoint s1 n1 s2 n2 ↔ regionsDisjoint s2 n2 s1 n1 := by
  simp [regionsDisjoint, or_comm]

/-- Addition does not overflow when both operands are within half the bound. -/
theorem add_no_overflow_of_halves (a b bound : Nat) (ha : a ≤ bound / 2) (hb : b ≤ bound / 2) :
    addNoOverflow a b bound := by
  simp [addNoOverflow]
  omega

/-- Zero addition never overflows. -/
theorem add_no_overflow_zero_left (b bound : Nat) (hb : b ≤ bound) :
    addNoOverflow 0 b bound := by
  simp [addNoOverflow]
  omega

/-- Multiplication by zero never overflows. -/
theorem mul_no_overflow_zero_left (b bound : Nat) :
    mulNoOverflow 0 b bound := by
  simp [mulNoOverflow]

/-- Multiplication by one preserves the bound. -/
theorem mul_no_overflow_one_left (b bound : Nat) (hb : b ≤ bound) :
    mulNoOverflow 1 b bound := by
  simp [mulNoOverflow]
  omega

/-- Power-of-two alignment: n * 2^k is aligned to 2^k. -/
theorem pow2_aligned (n k : Nat) : n * 2 ^ k % 2 ^ k = 0 := by
  exact Nat.mul_mod_left n (2 ^ k)

/-- Alignment to 1 is trivially satisfied. -/
theorem align_one (n : Nat) : n % 1 = 0 := by
  omega

end Radix.ProofAutomation
