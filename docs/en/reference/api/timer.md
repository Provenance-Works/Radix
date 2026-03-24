# Timer Module API Reference

> **Module**: `Radix.Timer`
> **Source**: `Radix/Timer/`

## Overview

Provides a small verified model of monotonic clocks and deadlines. The module is intended for real-time reasoning, timeout checks, and scheduler-style proofs in downstream bare-metal or systems code.

## Specification (`Timer.Spec`)

```lean
structure Clock where
  ticks : Nat

structure Deadline where
  deadlineTick : Nat

def zero : Clock
def advance (clock : Clock) (delta : Nat) : Clock
def elapsed (start finish : Clock) : Nat
def elapsed? (start finish : Clock) : Option Nat
def Monotonic (before after : Clock) : Prop
def deadlineAfter (clock : Clock) (timeout : Nat) : Deadline
def expired (clock : Clock) (deadline : Deadline) : Prop
def remaining (clock : Clock) (deadline : Deadline) : Nat
def overdue (clock : Clock) (deadline : Deadline) : Nat
def extend (deadline : Deadline) (delta : Nat) : Deadline
def sooner (a b : Deadline) : Deadline
def later (a b : Deadline) : Deadline
```

## Operations (`Timer.Ops`)

```lean
abbrev Clock := Spec.Clock
abbrev Deadline := Spec.Deadline

def zero : Clock
def now (clock : Clock) : Nat
def tick (clock : Clock) (delta : Nat := 1) : Clock
def after (clock : Clock) (timeout : Nat) : Deadline
def hasExpired (clock : Clock) (deadline : Deadline) : Bool
def remaining (clock : Clock) (deadline : Deadline) : Nat
def overdue (clock : Clock) (deadline : Deadline) : Nat
def extend (deadline : Deadline) (delta : Nat) : Deadline
def sooner (a b : Deadline) : Deadline
def later (a b : Deadline) : Deadline
def expiresWithin (clock : Clock) (deadline : Deadline) (budget : Nat) : Bool
def elapsed (start finish : Clock) : Nat
def elapsed? (start finish : Clock) : Option Nat
```

### Semantics

- `tick` advances the clock monotonically.
- `elapsed` is a saturating helper: reversed observations collapse to `0`.
- `elapsed?` rejects reversed observations with `none`.
- `remaining` saturates at zero once the deadline has expired.
- `overdue` saturates at zero before expiry and grows once the deadline is missed.
- `extend`, `sooner`, and `later` expose deadline algebra for scheduler-style reasoning.
- `expiresWithin` is a checked budget test over the saturated `remaining` helper.
- `hasExpired` is a boolean view of the spec-level `expired` predicate.

## Proofs (`Timer.Lemmas`)

- `advance_monotonic`: advancing the clock preserves monotonicity
- `elapsed?_eq_some_of_monotonic`: checked elapsed agrees with monotone observations
- `elapsed?_eq_none_of_not_monotonic`: checked elapsed rejects reversed observations
- `remaining_zero_of_expired`: no time remains once a deadline has expired
- `expired_of_remaining_zero`: zero remaining time implies expiry
- `tick_monotonic`: operation-layer ticking preserves monotonicity
- `after_not_expired`: a positive timeout is not expired immediately
- `overdue_zero_of_not_hasExpired`: live deadlines are not overdue
- `extend_not_earlier`: extending a deadline cannot move it earlier
- `expiresWithin_remaining`: every deadline expires within its exact remaining budget

## Examples

```lean
import Radix.Timer

def demo : Nat :=
  let start := Radix.Timer.zero
  let deadline := Radix.Timer.after start 10
  let mid := Radix.Timer.tick start 4
  let late := Radix.Timer.tick start 13
  if Radix.Timer.expiresWithin mid deadline 6 then
    Radix.Timer.overdue late deadline
  else
    Radix.Timer.remaining mid deadline
```

## Related Documents

- [BareMetal](baremetal.md) — downstream startup and runtime models that can consume monotonic deadlines
- [System](system.md) — host-boundary wrappers where timeout logic may be layered on top
