/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic

/-!
# Timer Specification (Layer 3)

Monotonic clocks, deadlines, and timeout reasoning.

## References

- v0.3.0 Roadmap: Timer / Clock Model
-/

set_option autoImplicit false

namespace Radix.Timer.Spec

/-- Monotonic logical clock measured in ticks. -/
structure Clock where
  ticks : Nat
  deriving DecidableEq, Repr

/-- A deadline on the monotonic clock. -/
structure Deadline where
  deadlineTick : Nat
  deriving DecidableEq, Repr

/-- Initial clock at tick zero. -/
def zero : Clock :=
  ⟨0⟩

/-- Advance the clock by a non-negative delta. -/
def advance (clock : Clock) (delta : Nat) : Clock :=
  ⟨clock.ticks + delta⟩

/-- The elapsed ticks between two clock snapshots, saturating at zero when the
    observations are out of order. -/
def elapsed (start finish : Clock) : Nat :=
  finish.ticks - start.ticks

/-- Monotonicity between clock observations. -/
def Monotonic (before after : Clock) : Prop :=
  before.ticks ≤ after.ticks

instance (before after : Clock) : Decidable (Monotonic before after) :=
  inferInstanceAs (Decidable (before.ticks ≤ after.ticks))

/-- Checked elapsed ticks between two clock snapshots. Returns `none` when the
    observations are out of order. -/
def elapsed? (start finish : Clock) : Option Nat :=
  if Monotonic start finish then
    some (elapsed start finish)
  else
    none

/-- Construct a deadline after `timeout` ticks from the current clock. -/
def deadlineAfter (clock : Clock) (timeout : Nat) : Deadline :=
  ⟨clock.ticks + timeout⟩

/-- A deadline has expired when the current clock is at or past it. -/
def expired (clock : Clock) (deadline : Deadline) : Prop :=
  deadline.deadlineTick ≤ clock.ticks

/-- Remaining time until the deadline, saturating at zero. -/
def remaining (clock : Clock) (deadline : Deadline) : Nat :=
  deadline.deadlineTick - clock.ticks

/-- Time that has passed since a deadline, saturating at zero before expiry. -/
def overdue (clock : Clock) (deadline : Deadline) : Nat :=
  clock.ticks - deadline.deadlineTick

/-- Extend a deadline by a further number of ticks. -/
def extend (deadline : Deadline) (delta : Nat) : Deadline :=
  ⟨deadline.deadlineTick + delta⟩

/-- The earlier of two deadlines. -/
def sooner (a b : Deadline) : Deadline :=
  if a.deadlineTick ≤ b.deadlineTick then a else b

/-- The later of two deadlines. -/
def later (a b : Deadline) : Deadline :=
  if a.deadlineTick ≤ b.deadlineTick then b else a

theorem advance_monotonic (clock : Clock) (delta : Nat) :
    Monotonic clock (advance clock delta) := by
  simp [Monotonic, advance]

theorem elapsed?_eq_some_of_monotonic (start finish : Clock)
    (h : Monotonic start finish) :
    elapsed? start finish = some (elapsed start finish) := by
  unfold elapsed?
  rw [if_pos h]

theorem elapsed?_eq_none_of_not_monotonic (start finish : Clock)
    (h : ¬ Monotonic start finish) :
    elapsed? start finish = none := by
  unfold elapsed?
  rw [if_neg h]

theorem remaining_zero_of_expired (clock : Clock) (deadline : Deadline)
    (h : expired clock deadline) :
    remaining clock deadline = 0 := by
  simp [expired, remaining] at *
  omega

theorem expired_of_remaining_zero (clock : Clock) (deadline : Deadline)
    (h : remaining clock deadline = 0) :
    expired clock deadline := by
  simp [expired, remaining] at *
  omega

theorem overdue_zero_of_not_expired (clock : Clock) (deadline : Deadline)
    (h : clock.ticks ≤ deadline.deadlineTick) :
    overdue clock deadline = 0 := by
  simp [overdue]
  omega

theorem overdue_pos_of_expired (clock : Clock) (deadline : Deadline)
    (h : deadline.deadlineTick < clock.ticks) :
    0 < overdue clock deadline := by
  simp [overdue]
  omega

theorem extend_not_earlier (deadline : Deadline) (delta : Nat) :
    deadline.deadlineTick ≤ (extend deadline delta).deadlineTick := by
  simp [extend]

theorem sooner_deadlineTick_le_left (a b : Deadline) :
    (sooner a b).deadlineTick ≤ a.deadlineTick := by
  unfold sooner
  by_cases h : a.deadlineTick ≤ b.deadlineTick
  · simp [h]
  · simp [h]
    omega

theorem sooner_deadlineTick_le_right (a b : Deadline) :
    (sooner a b).deadlineTick ≤ b.deadlineTick := by
  unfold sooner
  by_cases h : a.deadlineTick ≤ b.deadlineTick
  · simp [h]
  · simp [h]

theorem later_deadlineTick_ge_left (a b : Deadline) :
    a.deadlineTick ≤ (later a b).deadlineTick := by
  unfold later
  by_cases h : a.deadlineTick ≤ b.deadlineTick
  · simp [h]
  · simp [h]

theorem later_deadlineTick_ge_right (a b : Deadline) :
    b.deadlineTick ≤ (later a b).deadlineTick := by
  unfold later
  by_cases h : a.deadlineTick ≤ b.deadlineTick <;> simp [h]
  omega

-- ════════════════════════════════════════════════════════════════════
-- Frequency and Unit Conversion
-- ════════════════════════════════════════════════════════════════════

/-- Tick frequency in Hz (ticks per second). -/
structure Frequency where
  hz : Nat
  pos : 0 < hz
  deriving Repr

/-- Convert seconds to ticks at the given frequency. -/
def secondsToTicks (freq : Frequency) (seconds : Nat) : Nat :=
  seconds * freq.hz

/-- Convert milliseconds to ticks at the given frequency (rounds down). -/
def millisToTicks (freq : Frequency) (millis : Nat) : Nat :=
  millis * freq.hz / 1000

/-- Convert ticks to seconds at the given frequency (rounds down). -/
def ticksToSeconds (freq : Frequency) (ticks : Nat) : Nat :=
  ticks / freq.hz

/-- Convert ticks to milliseconds at the given frequency (rounds down). -/
def ticksToMillis (freq : Frequency) (ticks : Nat) : Nat :=
  ticks * 1000 / freq.hz

-- ════════════════════════════════════════════════════════════════════
-- Interval Timer (Periodic)
-- ════════════════════════════════════════════════════════════════════

/-- An interval timer that fires periodically. -/
structure IntervalTimer where
  period : Nat
  nextTick : Nat
  periodPos : 0 < period
  deriving Repr

/-- Create an interval timer starting at the given clock. -/
def mkInterval (clock : Clock) (period : Nat) (hp : 0 < period) : IntervalTimer :=
  { period := period
  , nextTick := clock.ticks + period
  , periodPos := hp
  }

/-- Check if the interval timer has fired. -/
def intervalFired (clock : Clock) (timer : IntervalTimer) : Bool :=
  timer.nextTick ≤ clock.ticks

/-- Reset the interval timer to the next period. -/
def intervalReset (timer : IntervalTimer) : IntervalTimer :=
  { timer with nextTick := timer.nextTick + timer.period }

/-- Number of times the interval timer has fired since its nextTick. -/
def intervalFireCount (clock : Clock) (timer : IntervalTimer) : Nat :=
  if timer.nextTick ≤ clock.ticks then
    (clock.ticks - timer.nextTick) / timer.period + 1
  else 0

-- ════════════════════════════════════════════════════════════════════
-- Watchdog Timer
-- ════════════════════════════════════════════════════════════════════

/-- A watchdog timer that must be "kicked" periodically to prevent timeout. -/
structure Watchdog where
  timeout : Nat
  deadline : Deadline
  timeoutPos : 0 < timeout
  deriving Repr

/-- Create a watchdog timer. -/
def mkWatchdog (clock : Clock) (timeout : Nat) (hp : 0 < timeout) : Watchdog :=
  { timeout := timeout
  , deadline := deadlineAfter clock timeout
  , timeoutPos := hp
  }

/-- Kick (reset) the watchdog timer, pushing the deadline forward. -/
def watchdogKick (clock : Clock) (wd : Watchdog) : Watchdog :=
  { wd with deadline := deadlineAfter clock wd.timeout }

/-- Check if the watchdog has timed out. -/
def watchdogExpired (clock : Clock) (wd : Watchdog) : Bool :=
  wd.deadline.deadlineTick ≤ clock.ticks

-- ════════════════════════════════════════════════════════════════════
-- Additional Clock Theorems
-- ════════════════════════════════════════════════════════════════════

/-- Monotonicity is reflexive. -/
theorem monotonic_refl (clock : Clock) : Monotonic clock clock := by
  simp [Monotonic]

/-- Monotonicity is transitive. -/
theorem monotonic_trans (a b c : Clock) (hab : Monotonic a b) (hbc : Monotonic b c) :
    Monotonic a c := by
  simp [Monotonic] at *
  omega

/-- Advancing by zero is identity. -/
theorem advance_zero (clock : Clock) : advance clock 0 = clock := by
  simp [advance]

/-- Double advance equals a single advance of the sum. -/
theorem advance_advance (clock : Clock) (d1 d2 : Nat) :
    advance (advance clock d1) d2 = advance clock (d1 + d2) := by
  simp [advance, Nat.add_assoc]

/-- Elapsed ticks from clock to itself is zero. -/
theorem elapsed_self (clock : Clock) : elapsed clock clock = 0 := by
  simp [elapsed]

/-- Elapsed ticks after advancing equals the delta. -/
theorem elapsed_advance (clock : Clock) (delta : Nat) :
    elapsed clock (advance clock delta) = delta := by
  simp [elapsed, advance]

/-- Seconds-to-ticks round-trips with ticks-to-seconds at exact multiples. -/
theorem ticksToSeconds_secondsToTicks (freq : Frequency) (s : Nat) :
    ticksToSeconds freq (secondsToTicks freq s) = s := by
  simp [ticksToSeconds, secondsToTicks]
  exact Nat.mul_div_cancel s freq.pos

/-- A newly created interval timer has not yet fired. -/
theorem mkInterval_not_fired (clock : Clock) (period : Nat) (hp : 0 < period) :
    intervalFired clock (mkInterval clock period hp) = false := by
  simp [intervalFired, mkInterval]
  omega

/-- A newly created watchdog has not expired. -/
theorem mkWatchdog_not_expired (clock : Clock) (timeout : Nat) (hp : 0 < timeout) :
    watchdogExpired clock (mkWatchdog clock timeout hp) = false := by
  simp [watchdogExpired, mkWatchdog, deadlineAfter]
  omega

/-- Kicking the watchdog pushes back the deadline. -/
theorem watchdogKick_deadline (clock : Clock) (wd : Watchdog) :
    (watchdogKick clock wd).deadline = deadlineAfter clock wd.timeout := by
  simp [watchdogKick]

/-- Sooner is commutative. -/
theorem sooner_comm (a b : Deadline) :
    (sooner a b).deadlineTick = (sooner b a).deadlineTick := by
  unfold sooner
  by_cases h : a.deadlineTick ≤ b.deadlineTick <;>
  by_cases h2 : b.deadlineTick ≤ a.deadlineTick <;> simp [h, h2] <;> omega

/-- Later is commutative. -/
theorem later_comm (a b : Deadline) :
    (later a b).deadlineTick = (later b a).deadlineTick := by
  unfold later
  by_cases h : a.deadlineTick ≤ b.deadlineTick <;>
  by_cases h2 : b.deadlineTick ≤ a.deadlineTick <;> simp [h, h2] <;> omega

/-- Remaining plus overdue equals the absolute tick difference. -/
theorem remaining_add_overdue (clock : Clock) (deadline : Deadline) :
    remaining clock deadline + overdue clock deadline =
    if deadline.deadlineTick ≤ clock.ticks then clock.ticks - deadline.deadlineTick
    else deadline.deadlineTick - clock.ticks := by
  simp [remaining, overdue]
  by_cases h : deadline.deadlineTick ≤ clock.ticks
  · simp [h]
  · simp [h]; omega

-- ════════════════════════════════════════════════════════════════════
-- Deadline Algebra
-- ════════════════════════════════════════════════════════════════════

/-- Extending a deadline by zero is identity. -/
theorem extend_zero (d : Deadline) : extend d 0 = d := by
  simp [extend]

/-- Extending twice equals extending by the sum. -/
theorem extend_extend (d : Deadline) (a b : Nat) :
    extend (extend d a) b = extend d (a + b) := by
  simp [extend, Nat.add_assoc]

/-- A deadline created after a clock cannot be expired at that clock. -/
theorem not_expired_deadlineAfter (clock : Clock) (timeout : Nat) (h : 0 < timeout) :
    ¬expired clock (deadlineAfter clock timeout) := by
  simp [expired, deadlineAfter]; omega

/-- Sooner is idempotent. -/
theorem sooner_self (d : Deadline) : sooner d d = d := by
  simp [sooner]

/-- Later is idempotent. -/
theorem later_self (d : Deadline) : later d d = d := by
  simp [later]

/-- Sooner of a and b is always ≤ later of a and b. -/
theorem sooner_le_later (a b : Deadline) :
    (sooner a b).deadlineTick ≤ (later a b).deadlineTick := by
  unfold sooner later
  by_cases h : a.deadlineTick ≤ b.deadlineTick
  · simp [h]
  · simp [h]; omega
-- ════════════════════════════════════════════════════════════════════

/-- Zero seconds converts to zero ticks. -/
theorem secondsToTicks_zero (freq : Frequency) : secondsToTicks freq 0 = 0 := by
  simp [secondsToTicks]

/-- Zero ticks converts to zero seconds. -/
theorem ticksToSeconds_zero (freq : Frequency) : ticksToSeconds freq 0 = 0 := by
  simp [ticksToSeconds]

/-- Seconds to ticks is monotonic. -/
theorem secondsToTicks_mono (freq : Frequency) (a b : Nat) (h : a ≤ b) :
    secondsToTicks freq a ≤ secondsToTicks freq b := by
  simp [secondsToTicks]
  exact Nat.mul_le_mul_right freq.hz h

/-- TicksToSeconds is monotonic. -/
theorem ticksToSeconds_mono (freq : Frequency) (a b : Nat) (h : a ≤ b) :
    ticksToSeconds freq a ≤ ticksToSeconds freq b := by
  simp [ticksToSeconds]
  exact Nat.div_le_div_right h

-- ════════════════════════════════════════════════════════════════════
-- Interval Timer Extended Properties
-- ════════════════════════════════════════════════════════════════════

/-- An unfired interval timer has zero fire count. -/
theorem intervalFireCount_zero_of_not_fired (clock : Clock) (timer : IntervalTimer)
    (h : intervalFired clock timer = false) :
    intervalFireCount clock timer = 0 := by
  simp [intervalFired] at h
  simp [intervalFireCount, h]

/-- Resetting an interval timer pushes nextTick by one period. -/
theorem intervalReset_nextTick (timer : IntervalTimer) :
    (intervalReset timer).nextTick = timer.nextTick + timer.period := by
  simp [intervalReset]

/-- Resetting preserves the period. -/
theorem intervalReset_period (timer : IntervalTimer) :
    (intervalReset timer).period = timer.period := by
  simp [intervalReset]

end Radix.Timer.Spec
