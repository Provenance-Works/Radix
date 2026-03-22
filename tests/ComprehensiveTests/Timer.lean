import tests.ComprehensiveTests.Framework
import Radix.Timer

/-!
# Timer Tests
-/

open ComprehensiveTests

def runTimerTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Timer tests..."

  let clock := Radix.Timer.zero
  let deadline := Radix.Timer.after clock 5
  assert (Radix.Timer.hasExpired clock deadline == false) "future deadline"
  assert (Radix.Timer.remaining clock deadline == 5) "initial remaining"

  let later := Radix.Timer.tick clock 3
  assert (Radix.Timer.remaining later deadline == 2) "remaining after tick"

  let done := Radix.Timer.tick later 2
  assert (Radix.Timer.hasExpired done deadline) "deadline expired"
  assert (Radix.Timer.remaining done deadline == 0) "remaining saturates"

  c.get
