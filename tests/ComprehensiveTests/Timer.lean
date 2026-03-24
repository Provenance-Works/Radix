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

  -- ── Frequency / Unit Conversion ──
  let freq1k : Radix.Timer.Frequency := ⟨1000, by omega⟩
  assert (Radix.Timer.secondsToTicks freq1k 3 == 3000) "secondsToTicks 3s @ 1kHz"
  assert (Radix.Timer.secondsToTicks freq1k 0 == 0) "secondsToTicks zero"
  assert (Radix.Timer.millisToTicks freq1k 500 == 500) "millisToTicks 500ms @ 1kHz"
  assert (Radix.Timer.millisToTicks freq1k 0 == 0) "millisToTicks zero"
  assert (Radix.Timer.ticksToSeconds freq1k 5000 == 5) "ticksToSeconds 5000 @ 1kHz"
  assert (Radix.Timer.ticksToSeconds freq1k 0 == 0) "ticksToSeconds zero"
  assert (Radix.Timer.ticksToMillis freq1k 3000 == 3000) "ticksToMillis 3000 @ 1kHz"
  assert (Radix.Timer.ticksToMillis freq1k 0 == 0) "ticksToMillis zero"
  -- Round-trip: seconds → ticks → seconds
  assert (Radix.Timer.ticksToSeconds freq1k (Radix.Timer.secondsToTicks freq1k 42) == 42)
    "secondsToTicks/ticksToSeconds round-trip"

  -- ── Interval Timer ──
  let timer := Radix.Timer.mkInterval clock 10 (by omega)
  assert (Radix.Timer.intervalFired clock timer == false) "interval timer not fired initially"
  assert (Radix.Timer.intervalFireCount clock timer == 0) "interval fire count is 0 initially"
  let atFire := Radix.Timer.tick clock 10
  assert (Radix.Timer.intervalFired atFire timer == true) "interval timer fired at boundary"
  assert (Radix.Timer.intervalFireCount atFire timer == 1) "interval fire count 1 at boundary"
  let afterFire := Radix.Timer.tick clock 25
  assert (Radix.Timer.intervalFired afterFire timer == true) "interval timer still fired after boundary"
  assert (Radix.Timer.intervalFireCount afterFire timer == 2) "interval fire count 2 at 25 ticks"
  let resetTimer := Radix.Timer.intervalReset timer
  assert (Radix.Timer.intervalFired atFire resetTimer == false) "reset interval timer not fired at original boundary"
  assert (resetTimer.nextTick == 20) "reset interval timer nextTick"

  -- ── Watchdog Timer ──
  let wd := Radix.Timer.mkWatchdog clock 100 (by omega)
  assert (Radix.Timer.watchdogExpired clock wd == false) "new watchdog not expired"
  let wdClock50 := Radix.Timer.tick clock 50
  assert (Radix.Timer.watchdogExpired wdClock50 wd == false) "watchdog alive at half"
  let wdClockExpired := Radix.Timer.tick clock 100
  assert (Radix.Timer.watchdogExpired wdClockExpired wd == true) "watchdog expired at boundary"
  let kicked := Radix.Timer.watchdogKick wdClock50 wd
  assert (Radix.Timer.watchdogExpired wdClock50 kicked == false) "kicked watchdog not expired"
  assert (Radix.Timer.watchdogExpired wdClockExpired kicked == false)
    "kicked watchdog still alive at original expiry"
  let wdClockLate := Radix.Timer.tick clock 150
  assert (Radix.Timer.watchdogExpired wdClockLate kicked == true)
    "kicked watchdog expired at new deadline"

  -- ── Batch Operations ──
  let advancedClock := Radix.Timer.advanceN clock [10, 20, 30]
  assert (Radix.Timer.now advancedClock == 60) "advanceN sums steps"
  assert (Radix.Timer.now (Radix.Timer.advanceN clock []) == 0) "advanceN empty is identity"
  let d1 := Radix.Timer.after clock 5
  let d2 := Radix.Timer.after clock 15
  let d3 := Radix.Timer.after clock 25
  let allDeadlines := [d1, d2, d3]
  let expiredList := Radix.Timer.expiredDeadlines (Radix.Timer.tick clock 10) allDeadlines
  assert (expiredList.length == 1) "expiredDeadlines returns 1 expired"
  let pendingList := Radix.Timer.pendingDeadlines (Radix.Timer.tick clock 10) allDeadlines
  assert (pendingList.length == 2) "pendingDeadlines returns 2 pending"

  c.get
