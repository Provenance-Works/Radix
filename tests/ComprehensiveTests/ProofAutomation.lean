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
  assert (decide ((7 : Nat) + 0 = 7)) "radix_decide theorem"
  assert (decide ((if True then (5 : Nat) else 9) = 5)) "radix_decide simp branch"
  assert (decide ((4 : Nat) = 4)) "radix_decide decide branch"
  assert (decide (0 ≤ 9)) "radix_omega theorem"
  assert (decide (0 ≤ (37 : Nat))) "radix_omega zero branch"

  c.get
