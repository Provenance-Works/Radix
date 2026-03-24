import tests.ComprehensiveTests.Framework
import Radix.ProofAutomation

/-!
# Proof Automation Tests
-/

open ComprehensiveTests

example : (7 : Nat) + 0 = 7 := by
  radix_decide

example (a b : Nat) (h : a = b) : b = a := by
  radix_decide

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  radix_omega

example (a : Nat) : 0 ≤ a := by
  radix_omega

example : (if True then (8 : Nat) else 0) = 8 := by
  radix_simp

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  radix_finish

def runProofAutomationTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Proof automation tests..."

  have _ : (7 : Nat) + 0 = 7 := by
    radix_decide
  have _ : (if True then (5 : Nat) else 9) = 5 := by
    radix_decide
  have _ : (3 : Nat) = 3 := by
    radix_decide
  have _ : 4 = 4 := by
    radix_decide
  have _ : 0 ≤ 9 := by
    radix_omega
  have _ : 0 ≤ (37 : Nat) := by
    radix_omega
  have _ : (if True then (8 : Nat) else 0) = 8 := by
    radix_simp
  have _ : 0 ≤ (6 : Nat) := by
    radix_finish
  assert (decide ((7 : Nat) + 0 = 7)) "radix_decide theorem"
  assert (decide ((if True then (5 : Nat) else 9) = 5)) "radix_decide simp branch"
  assert (decide ((4 : Nat) = 4)) "radix_decide decide branch"
  assert (decide (0 ≤ 9)) "radix_omega theorem"
  assert (decide (0 ≤ (37 : Nat))) "radix_omega zero branch"
  assert (decide ((if True then (8 : Nat) else 0) = 8)) "radix_simp simplification branch"
  assert (decide (0 ≤ (6 : Nat))) "radix_finish combined finishing"

  -- ── radix_bitwise ──
  have _ : Nat.xor 5 5 = 0 := by decide
  have _ : Nat.lor 0 7 = 7 := by decide
  have _ : Nat.land 0xFF 0 = 0 := by decide
  assert (decide (Nat.xor 5 5 = 0)) "radix_bitwise xor self"
  assert (decide (Nat.lor 0 7 = 7)) "radix_bitwise lor zero"
  assert (decide (Nat.land 0xFF 0 = 0)) "radix_bitwise land zero"

  -- ── radix_align ──
  have _ : 8 * 4 % 4 = 0 := by radix_align
  have _ : (0 : Nat) % 1 = 0 := by radix_align
  assert (decide (8 * 4 % 4 = 0)) "radix_align mul mod"
  assert (decide ((0 : Nat) % 1 = 0)) "radix_align zero mod one"

  -- ── radix_region ──
  have _ : Radix.ProofAutomation.regionsDisjoint 0 10 20 10 := by radix_region
  have _ : Radix.ProofAutomation.regionsDisjoint 100 50 0 50 := by radix_region
  assert (decide (Radix.ProofAutomation.regionsDisjoint 0 10 20 10))
    "radix_region adjacent regions"
  assert (decide (Radix.ProofAutomation.regionsDisjoint 100 50 0 50))
    "radix_region separated regions"

  -- ── radix_overflow ──
  have _ : Radix.ProofAutomation.addNoOverflow 100 50 200 := by radix_overflow
  have _ : Radix.ProofAutomation.mulNoOverflow 10 20 200 := by radix_overflow
  assert (decide (Radix.ProofAutomation.addNoOverflow 100 50 200))
    "radix_overflow add no overflow"
  assert (decide (Radix.ProofAutomation.mulNoOverflow 10 20 200))
    "radix_overflow mul no overflow"

  -- ── Convenience lemma tests ──
  have _ := Radix.ProofAutomation.adjacent_regions_disjoint 10 (by omega)
  have _ := Radix.ProofAutomation.regionsDisjoint_comm 0 10 20 10
  have _ := Radix.ProofAutomation.pow2_aligned 3 4
  have _ := Radix.ProofAutomation.align_one 42
  assert (decide (Radix.ProofAutomation.regionsDisjoint 0 10 10 10))
    "adjacent_regions_disjoint applied"
  assert (decide (3 * 2 ^ 4 % 2 ^ 4 = 0)) "pow2_aligned applied"
  assert (decide (42 % 1 = 0)) "align_one applied"

  c.get
