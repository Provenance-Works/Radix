import tests.ComprehensiveTests.Framework
import Radix.ProofAutomation

/-!
# Proof Automation Tests
-/

open ComprehensiveTests

example : (7 : Nat) + 0 = 7 := by
  radix_decide

example (a b c : Nat) (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  radix_omega

def runProofAutomationTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Proof automation tests..."

  have _ : (7 : Nat) + 0 = 7 := by
    radix_decide
  have _ : 0 ≤ 9 := by
    radix_omega
  assert (decide ((7 : Nat) + 0 = 7)) "radix_decide theorem"
  assert (decide (0 ≤ 9)) "radix_omega theorem"

  c.get
