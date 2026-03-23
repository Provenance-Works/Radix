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

end Radix.Timer
