import Radix.Timer

/-!
# Example: Timer / Clock
-/

namespace Examples.TimerDemo

def main : IO Unit := do
  IO.println "━━━ Timer Example ━━━"
  let start := Radix.Timer.zero
  let deadline := Radix.Timer.after start 10
  let mid := Radix.Timer.tick start 4
  let finish := Radix.Timer.tick mid 6
  IO.println s!"  Remaining at tick 4: {Radix.Timer.remaining mid deadline}"
  IO.println s!"  Checked elapsed start->tick4: {Radix.Timer.elapsed? start mid}"
  IO.println s!"  Expired at tick 10: {Radix.Timer.hasExpired finish deadline}"

end Examples.TimerDemo
