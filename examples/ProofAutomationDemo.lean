import Radix.ProofAutomation

/-!
# Example: Proof Automation
-/

namespace Examples.ProofAutomationDemo

theorem add_example : (4 : Nat) + 0 = 4 := by
  radix_decide

theorem order_example : 0 ≤ 7 := by
  radix_omega

theorem simp_example : (if True then (6 : Nat) else 0) = 6 := by
  radix_simp

theorem finish_example : 0 ≤ (6 : Nat) := by
  radix_finish

def main : IO Unit := do
  IO.println "━━━ Proof Automation Example ━━━"
  IO.println s!"  add_example: {decide ((4 : Nat) + 0 = 4)}"
  IO.println s!"  order_example: {decide (0 ≤ 7)}"
  IO.println s!"  simp_example: {decide ((if True then (6 : Nat) else 0) = 6)}"
  IO.println s!"  finish_example: {decide (0 ≤ (6 : Nat))}"

end Examples.ProofAutomationDemo
