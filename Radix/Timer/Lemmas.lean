/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Timer.Spec
import Radix.Timer.Ops

/-!
# Timer Proofs (Layer 3)
-/

set_option autoImplicit false

namespace Radix.Timer

open Spec

/-- Ticking the clock preserves monotonicity. -/
theorem tick_monotonic (clock : Clock) (delta : Nat) :
    Spec.Monotonic clock (tick clock delta) := by
  simpa [tick] using Spec.advance_monotonic clock delta

/-- Advancing a clock by `delta` ticks makes exactly `delta` ticks elapse. -/
theorem elapsed_tick (clock : Clock) (delta : Nat) :
    elapsed clock (tick clock delta) = delta := by
  simp [elapsed, tick, Spec.elapsed, Spec.advance]

/-- Checked elapsed time agrees with ticking on monotone observations. -/
theorem elapsed?_tick (clock : Clock) (delta : Nat) :
    Radix.Timer.elapsed? clock (tick clock delta) = some delta := by
  simpa [Radix.Timer.elapsed?, elapsed, tick, Spec.elapsed, Spec.advance, Spec.Monotonic] using
    Radix.Timer.Spec.elapsed?_eq_some_of_monotonic clock (Spec.advance clock delta)
      (Spec.advance_monotonic clock delta)

/-- Checked elapsed time rejects reversed observations. -/
theorem elapsed?_none_of_reverse (start finish : Clock)
    (h : finish.ticks < start.ticks) :
    Radix.Timer.elapsed? start finish = none := by
  apply Radix.Timer.Spec.elapsed?_eq_none_of_not_monotonic
  simp [Spec.Monotonic]
  omega

/-- Remaining time is zero once a deadline has expired. -/
theorem remaining_zero_of_hasExpired (clock : Clock) (deadline : Deadline)
    (h : hasExpired clock deadline = true) :
    remaining clock deadline = 0 := by
  have hexp : Spec.expired clock deadline := by
    simp [hasExpired] at h
    exact h
  simpa [remaining] using Spec.remaining_zero_of_expired clock deadline hexp

/-- A future deadline with positive timeout is not immediately expired. -/
theorem after_not_expired (clock : Clock) (timeout : Nat) (h : 0 < timeout) :
    hasExpired clock (after clock timeout) = false := by
  simp [hasExpired, after, Spec.deadlineAfter]
  omega

/-- A zero-timeout deadline expires immediately. -/
theorem after_zero_expired (clock : Clock) :
    hasExpired clock (after clock 0) = true := by
  simp [hasExpired, after, Spec.deadlineAfter]

/-- Ticking exactly to the deadline makes it expire and leaves no remaining time. -/
theorem remaining_tick_after (clock : Clock) (timeout : Nat) :
    remaining (tick clock timeout) (after clock timeout) = 0 := by
  simp [remaining, tick, after, Spec.remaining, Spec.advance, Spec.deadlineAfter]

/-- Non-expired deadlines are not overdue. -/
theorem overdue_zero_of_not_hasExpired (clock : Clock) (deadline : Deadline)
    (h : hasExpired clock deadline = false) :
    Radix.Timer.overdue clock deadline = 0 := by
  have hle : clock.ticks ≤ deadline.deadlineTick := by
    simp [hasExpired] at h
    omega
  simpa [Radix.Timer.overdue] using Radix.Timer.Spec.overdue_zero_of_not_expired clock deadline hle

/-- Extending a deadline never moves it earlier. -/
theorem extend_not_earlier (deadline : Deadline) (delta : Nat) :
    deadline.deadlineTick ≤ (Radix.Timer.extend deadline delta).deadlineTick := by
  simpa [Radix.Timer.extend] using Radix.Timer.Spec.extend_not_earlier deadline delta

/-- Any deadline expires within its exact remaining budget. -/
theorem expiresWithin_remaining (clock : Clock) (deadline : Deadline) :
    Radix.Timer.expiresWithin clock deadline (remaining clock deadline) = true := by
  simp [Radix.Timer.expiresWithin]

/-- Expired deadlines are always within any non-negative budget. -/
theorem expiresWithin_of_hasExpired (clock : Clock) (deadline : Deadline) (budget : Nat)
    (h : hasExpired clock deadline = true) :
    Radix.Timer.expiresWithin clock deadline budget = true := by
  have hrem : remaining clock deadline = 0 := remaining_zero_of_hasExpired clock deadline h
  simp [Radix.Timer.expiresWithin, hrem]

/-- The earlier deadline is no later than either input. -/
theorem sooner_le_left (a b : Deadline) :
    (Radix.Timer.sooner a b).deadlineTick ≤ a.deadlineTick := by
  simpa [Radix.Timer.sooner] using Radix.Timer.Spec.sooner_deadlineTick_le_left a b

/-- The later deadline is at least as late as either input. -/
theorem later_ge_right (a b : Deadline) :
    b.deadlineTick ≤ (Radix.Timer.later a b).deadlineTick := by
  simpa [Radix.Timer.later] using Radix.Timer.Spec.later_deadlineTick_ge_right a b

-- ════════════════════════════════════════════════════════════════════
-- Frequency / Unit Conversion Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- Seconds-to-ticks round-trips via ticks-to-seconds at exact multiples. -/
theorem ticksToSeconds_secondsToTicks (freq : Spec.Frequency) (s : Nat) :
    ticksToSeconds freq (secondsToTicks freq s) = s := by
  simp [ticksToSeconds, secondsToTicks]
  exact Spec.ticksToSeconds_secondsToTicks freq s

/-- Zero seconds maps to zero ticks. -/
theorem secondsToTicks_zero (freq : Spec.Frequency) :
    secondsToTicks freq 0 = 0 := by
  simp [secondsToTicks, Spec.secondsToTicks]

/-- Zero millis maps to zero ticks. -/
theorem millisToTicks_zero (freq : Spec.Frequency) :
    millisToTicks freq 0 = 0 := by
  simp [millisToTicks, Spec.millisToTicks]

/-- Zero ticks maps to zero seconds. -/
theorem ticksToSeconds_zero (freq : Spec.Frequency) :
    ticksToSeconds freq 0 = 0 := by
  simp [ticksToSeconds, Spec.ticksToSeconds]

/-- Zero ticks maps to zero milliseconds. -/
theorem ticksToMillis_zero (freq : Spec.Frequency) :
    ticksToMillis freq 0 = 0 := by
  simp [ticksToMillis, Spec.ticksToMillis]

-- ════════════════════════════════════════════════════════════════════
-- Interval Timer Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- A newly created interval timer has not yet fired. -/
theorem mkInterval_not_fired (clock : Clock) (period : Nat) (hp : 0 < period) :
    intervalFired clock (mkInterval clock period hp) = false := by
  simp [intervalFired, mkInterval]
  exact Spec.mkInterval_not_fired clock period hp

/-- After reset, the interval timer has nextTick advanced by one period. -/
theorem intervalReset_nextTick (timer : Spec.IntervalTimer) :
    (intervalReset timer).nextTick = timer.nextTick + timer.period := by
  simp [intervalReset, Spec.intervalReset]

/-- Fire count is zero before the timer fires. -/
theorem intervalFireCount_zero_before (clock : Clock) (timer : Spec.IntervalTimer)
    (h : intervalFired clock timer = false) :
    intervalFireCount clock timer = 0 := by
  simp [intervalFireCount, intervalFired, Spec.intervalFireCount, Spec.intervalFired] at *
  omega

-- ════════════════════════════════════════════════════════════════════
-- Watchdog Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- A newly created watchdog has not expired. -/
theorem mkWatchdog_not_expired (clock : Clock) (timeout : Nat) (hp : 0 < timeout) :
    watchdogExpired clock (mkWatchdog clock timeout hp) = false := by
  simp [watchdogExpired, mkWatchdog]
  exact Spec.mkWatchdog_not_expired clock timeout hp

/-- Kicking the watchdog resets its deadline. -/
theorem watchdogKick_deadline (clock : Clock) (wd : Spec.Watchdog) :
    (watchdogKick clock wd).deadline = Spec.deadlineAfter clock wd.timeout := by
  simp [watchdogKick]
  exact Spec.watchdogKick_deadline clock wd

/-- A just-kicked watchdog is not expired. -/
theorem watchdogKick_not_expired (clock : Clock) (wd : Spec.Watchdog) :
    watchdogExpired clock (watchdogKick clock wd) = false := by
  show Spec.watchdogExpired clock (Spec.watchdogKick clock wd) = false
  simp [Spec.watchdogExpired, Spec.watchdogKick, Spec.deadlineAfter]
  exact Nat.pos_iff_ne_zero.mp wd.timeoutPos

-- ════════════════════════════════════════════════════════════════════
-- Batch Operation Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- Advancing by an empty list of steps is identity. -/
theorem advanceN_nil (clock : Clock) :
    advanceN clock [] = clock := by
  simp [advanceN]

/-- Advancing by a single step equals a single tick. -/
theorem advanceN_singleton (clock : Clock) (d : Nat) :
    advanceN clock [d] = tick clock d := by
  simp [advanceN, tick, Spec.advance]

/-- No expired deadlines from an empty list. -/
theorem expiredDeadlines_nil (clock : Clock) :
    expiredDeadlines clock [] = [] := by
  simp [expiredDeadlines]

/-- No pending deadlines from an empty list. -/
theorem pendingDeadlines_nil (clock : Clock) :
    pendingDeadlines clock [] = [] := by
  simp [pendingDeadlines]

-- ════════════════════════════════════════════════════════════════════
-- Clock Algebra Lemmas
-- ════════════════════════════════════════════════════════════════════

/-- Monotonicity is reflexive. -/
theorem monotonic_refl (clock : Clock) : Spec.Monotonic clock clock := by
  exact Spec.monotonic_refl clock

/-- Ticking preserves monotonicity. -/
theorem tick_tick_monotonic (clock : Clock) (d1 d2 : Nat) :
    Spec.Monotonic clock (tick (tick clock d1) d2) := by
  simp [tick, Spec.advance, Spec.Monotonic]
  omega

/-- Elapsed after double tick is the sum of deltas. -/
theorem elapsed_tick_tick (clock : Clock) (d1 d2 : Nat) :
    elapsed clock (tick (tick clock d1) d2) = d1 + d2 := by
  simp [elapsed, tick, Spec.elapsed, Spec.advance]
  omega

/-- Sooner is commutative. -/
theorem sooner_comm (a b : Deadline) :
    (Radix.Timer.sooner a b).deadlineTick = (Radix.Timer.sooner b a).deadlineTick := by
  simp [Radix.Timer.sooner]
  exact Spec.sooner_comm a b

/-- Later is commutative. -/
theorem later_comm (a b : Deadline) :
    (Radix.Timer.later a b).deadlineTick = (Radix.Timer.later b a).deadlineTick := by
  simp [Radix.Timer.later]
  exact Spec.later_comm a b

end Radix.Timer
