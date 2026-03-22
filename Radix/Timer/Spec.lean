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

/-- The elapsed ticks between two clock snapshots. -/
def elapsed (start finish : Clock) : Nat :=
  finish.ticks - start.ticks

/-- Monotonicity between clock observations. -/
def Monotonic (before after : Clock) : Prop :=
  before.ticks ≤ after.ticks

/-- Construct a deadline after `timeout` ticks from the current clock. -/
def deadlineAfter (clock : Clock) (timeout : Nat) : Deadline :=
  ⟨clock.ticks + timeout⟩

/-- A deadline has expired when the current clock is at or past it. -/
def expired (clock : Clock) (deadline : Deadline) : Prop :=
  deadline.deadlineTick ≤ clock.ticks

/-- Remaining time until the deadline, saturating at zero. -/
def remaining (clock : Clock) (deadline : Deadline) : Nat :=
  deadline.deadlineTick - clock.ticks

theorem advance_monotonic (clock : Clock) (delta : Nat) :
    Monotonic clock (advance clock delta) := by
  simp [Monotonic, advance]

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

end Radix.Timer.Spec
