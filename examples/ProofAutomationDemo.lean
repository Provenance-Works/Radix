import Radix.ProofAutomation

/-!
# Example: Proof Automation
-/

namespace Examples.ProofAutomationDemo

theorem add_example : (4 : Nat) + 0 = 4 := by
  radix_decide

theorem order_example : 0 ≤ 7 := by
  radix_omega

def main : IO Unit := do
  IO.println "━━━ Proof Automation Example ━━━"
  IO.println s!"  add_example: {decide ((4 : Nat) + 0 = 4)}"
  IO.println s!"  order_example: {decide (0 ≤ 7)}"

end Examples.ProofAutomationDemo
