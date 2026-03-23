/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Timer.Spec

/-!
# Timer Operations (Layer 2)

Executable clock and timeout helpers.
-/

set_option autoImplicit false

namespace Radix.Timer

abbrev Clock := Spec.Clock
abbrev Deadline := Spec.Deadline

/-- Initial monotonic clock. -/
def zero : Clock :=
  Spec.zero

/-- Current tick count. -/
def now (clock : Clock) : Nat :=
  clock.ticks

/-- Advance the clock. -/
def tick (clock : Clock) (delta : Nat := 1) : Clock :=
  Spec.advance clock delta

/-- Construct a deadline `timeout` ticks in the future. -/
def after (clock : Clock) (timeout : Nat) : Deadline :=
  Spec.deadlineAfter clock timeout

/-- Boolean expiry test. -/
def hasExpired (clock : Clock) (deadline : Deadline) : Bool :=
  deadline.deadlineTick ≤ clock.ticks

/-- Remaining ticks before timeout. -/
def remaining (clock : Clock) (deadline : Deadline) : Nat :=
  Spec.remaining clock deadline

/-- Ticks spent past the deadline, saturating to zero before expiry. -/
def overdue (clock : Clock) (deadline : Deadline) : Nat :=
  Radix.Timer.Spec.overdue clock deadline

/-- Extend a deadline by a further number of ticks. -/
def extend (deadline : Deadline) (delta : Nat) : Deadline :=
  Radix.Timer.Spec.extend deadline delta

/-- Select the earlier of two deadlines. -/
def sooner (a b : Deadline) : Deadline :=
  Radix.Timer.Spec.sooner a b

/-- Select the later of two deadlines. -/
def later (a b : Deadline) : Deadline :=
  Radix.Timer.Spec.later a b

/-- Check whether a deadline expires within the provided tick budget. -/
def expiresWithin (clock : Clock) (deadline : Deadline) (budget : Nat) : Bool :=
  remaining clock deadline ≤ budget

/-- Elapsed ticks between two observations. -/
def elapsed (start finish : Clock) : Nat :=
  Spec.elapsed start finish

/-- Checked elapsed ticks between two observations. -/
def elapsed? (start finish : Clock) : Option Nat :=
  Radix.Timer.Spec.elapsed? start finish

-- ════════════════════════════════════════════════════════════════════
-- Frequency / Unit Conversion
-- ════════════════════════════════════════════════════════════════════

abbrev Frequency := Spec.Frequency

/-- Convert seconds to ticks at the given frequency. -/
def secondsToTicks (freq : Frequency) (seconds : Nat) : Nat :=
  Spec.secondsToTicks freq seconds

/-- Convert milliseconds to ticks at the given frequency (rounds down). -/
def millisToTicks (freq : Frequency) (millis : Nat) : Nat :=
  Spec.millisToTicks freq millis

/-- Convert ticks to seconds at the given frequency (rounds down). -/
def ticksToSeconds (freq : Frequency) (ticks : Nat) : Nat :=
  Spec.ticksToSeconds freq ticks

/-- Convert ticks to milliseconds at the given frequency (rounds down). -/
def ticksToMillis (freq : Frequency) (ticks : Nat) : Nat :=
  Spec.ticksToMillis freq ticks

-- ════════════════════════════════════════════════════════════════════
-- Interval Timer
-- ════════════════════════════════════════════════════════════════════

abbrev IntervalTimer := Spec.IntervalTimer

/-- Create an interval timer starting at the given clock. -/
def mkInterval (clock : Clock) (period : Nat) (hp : 0 < period) : IntervalTimer :=
  Spec.mkInterval clock period hp

/-- Check if the interval timer has fired. -/
def intervalFired (clock : Clock) (timer : IntervalTimer) : Bool :=
  Spec.intervalFired clock timer

/-- Reset the interval timer to the next period. -/
def intervalReset (timer : IntervalTimer) : IntervalTimer :=
  Spec.intervalReset timer

/-- Number of times the interval timer has fired since its nextTick. -/
def intervalFireCount (clock : Clock) (timer : IntervalTimer) : Nat :=
  Spec.intervalFireCount clock timer

-- ════════════════════════════════════════════════════════════════════
-- Watchdog Timer
-- ════════════════════════════════════════════════════════════════════

abbrev Watchdog := Spec.Watchdog

/-- Create a watchdog timer. -/
def mkWatchdog (clock : Clock) (timeout : Nat) (hp : 0 < timeout) : Watchdog :=
  Spec.mkWatchdog clock timeout hp

/-- Kick (reset) the watchdog timer. -/
def watchdogKick (clock : Clock) (wd : Watchdog) : Watchdog :=
  Spec.watchdogKick clock wd

/-- Check if the watchdog has timed out. -/
def watchdogExpired (clock : Clock) (wd : Watchdog) : Bool :=
  Spec.watchdogExpired clock wd

-- ════════════════════════════════════════════════════════════════════
-- Batch / Utility Operations
-- ════════════════════════════════════════════════════════════════════

/-- Advance a clock multiple times, returning the final clock. -/
def advanceN (clock : Clock) (steps : List Nat) : Clock :=
  steps.foldl Spec.advance clock

/-- Check multiple deadlines for expiry, returning those that have fired. -/
def expiredDeadlines (clock : Clock) (deadlines : List Deadline) : List Deadline :=
  deadlines.filter (hasExpired clock ·)

/-- Check multiple deadlines for expiry, returning those still pending. -/
def pendingDeadlines (clock : Clock) (deadlines : List Deadline) : List Deadline :=
  deadlines.filter (! hasExpired clock ·)

end Radix.Timer
