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
  let overdue := Radix.Timer.tick finish 3
  let extended := Radix.Timer.extend deadline 5
  IO.println s!"  Remaining at tick 4: {Radix.Timer.remaining mid deadline}"
  IO.println s!"  Checked elapsed start->tick4: {Radix.Timer.elapsed? start mid}"
  IO.println s!"  Expired at tick 10: {Radix.Timer.hasExpired finish deadline}"
  IO.println s!"  Overdue at tick 13: {Radix.Timer.overdue overdue deadline}"
  IO.println s!"  Expires within 6 ticks at tick 4: {Radix.Timer.expiresWithin mid deadline 6}"
  IO.println s!"  Extended deadline tick: {extended.deadlineTick}"
  IO.println s!"  Sooner tick: {(Radix.Timer.sooner deadline extended).deadlineTick}"
  IO.println s!"  Later tick: {(Radix.Timer.later deadline extended).deadlineTick}"

end Examples.TimerDemo
