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
  assert (Radix.Timer.overdue clock deadline == 0) "future deadline is not overdue"
  assert (Radix.Timer.hasExpired clock (Radix.Timer.after clock 0)) "zero-timeout deadline"

  let later := Radix.Timer.tick clock 3
  assert (Radix.Timer.remaining later deadline == 2) "remaining after tick"
  assert (Radix.Timer.elapsed clock later == 3) "elapsed after tick"
  assert (Radix.Timer.elapsed? clock later == some 3) "checked elapsed after tick"
  assert (Radix.Timer.expiresWithin later deadline 2) "deadline expires within exact remaining budget"
  assert (!Radix.Timer.expiresWithin later deadline 1) "deadline does not expire within too-small budget"

  let done := Radix.Timer.tick later 2
  assert (Radix.Timer.hasExpired done deadline) "deadline expired"
  assert (Radix.Timer.remaining done deadline == 0) "remaining saturates"
  assert (Radix.Timer.overdue done deadline == 0) "exact-boundary expiry is not overdue"

  let overdueClock := Radix.Timer.tick done 3
  assert (Radix.Timer.overdue overdueClock deadline == 3) "overdue grows after expiry"

  let extended := Radix.Timer.extend deadline 4
  assert (extended.deadlineTick == 9) "extend shifts deadline forward"
  assert (Radix.Timer.hasExpired done extended == false) "extended deadline is still live"

  let slower := Radix.Timer.after clock 8
  assert ((Radix.Timer.sooner deadline slower).deadlineTick == 5) "sooner picks earlier deadline"
  assert ((Radix.Timer.later deadline slower).deadlineTick == 8) "later picks later deadline"

  let exact := Radix.Timer.tick clock 5
  assert (Radix.Timer.hasExpired exact deadline) "deadline expires exactly on boundary"
  assert (Radix.Timer.elapsed clock exact == 5) "elapsed exact boundary"

  let reversed : Radix.Timer.Clock := { ticks := 2 }
  let earlier : Radix.Timer.Clock := { ticks := 7 }
  assert (Radix.Timer.elapsed earlier reversed == 0) "elapsed saturates on reversed clocks"
  assert (Radix.Timer.elapsed? earlier reversed == none) "checked elapsed rejects reversed clocks"

  c.get
