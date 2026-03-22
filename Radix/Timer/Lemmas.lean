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

end Radix.Timer
