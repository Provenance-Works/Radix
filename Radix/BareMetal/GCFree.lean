/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.BareMetal.Spec

/-!
# GC-Free Compilation Constraints (Layer 2)

This module defines constraints and verification conditions for
GC-free (garbage-collector-free) compilation:

- Value classification (static, stack, arena)
- GC-free constraint checking
- Stack usage analysis model
- Forbidden pattern detection

## Architecture

This is a **Layer 2 (Implementation)** module.

## References

- P5-02: GC-free compilation mode
- Lean 4 runtime: reference counting model
-/

set_option autoImplicit false

namespace Radix.BareMetal.GCFree

open Radix.BareMetal.Spec

/-! ## Value Lifetime Classification -/

/-- Classification of a value's lifetime in a GC-free context. -/
inductive Lifetime where
  /-- Value lives for the entire program duration (global/static). -/
  | static
  /-- Value lives for the duration of the enclosing function call. -/
  | stack
  /-- Value lives for the duration of the enclosing arena scope. -/
  | arena
  /-- Value is a compile-time constant (no runtime allocation). -/
  | compileTime
  /-- Value lives on the GC/RC-managed heap (unbounded dynamic lifetime). -/
  | heap
  deriving DecidableEq, Repr

/-- Whether a lifetime is bounded (known at compile time).
    Heap lifetimes are not bounded — their deallocation depends on
    runtime reference counting or garbage collection. -/
def Lifetime.isBounded : Lifetime → Bool
  | .static      => true
  | .stack        => true
  | .arena        => true
  | .compileTime  => true
  | .heap         => false

/-! ## Forbidden Patterns -/

/-- Patterns that are forbidden in GC-free code. Each variant
    represents a Lean 4 construct that requires GC/RC support. -/
inductive ForbiddenPattern where
  /-- Unbounded heap allocation (e.g., arbitrary List growth). -/
  | unboundedAlloc
  /-- Closure capture of mutable references. -/
  | mutableCapture
  /-- Dynamic dispatch through object polymorphism. -/
  | dynamicDispatch
  /-- Lazy thunk creation (requires heap allocation). -/
  | lazyThunk
  /-- Exception objects on the heap. -/
  | heapException
  deriving DecidableEq, Repr

/-- Human-readable description of a forbidden pattern. -/
def ForbiddenPattern.description : ForbiddenPattern → String
  | .unboundedAlloc  => "Unbounded heap allocation"
  | .mutableCapture  => "Closure capture of mutable reference"
  | .dynamicDispatch => "Dynamic dispatch via object polymorphism"
  | .lazyThunk       => "Lazy thunk creation"
  | .heapException   => "Heap-allocated exception object"

/-! ## GC-Free Constraints -/

/-- A constraint that a function must satisfy to be GC-free. -/
structure GCFreeConstraint where
  /-- Maximum stack usage in bytes. -/
  maxStackBytes     : Nat
  /-- Allowed allocation strategies. -/
  allowedStrategies : List AllocStrategy
  /-- Patterns that must not appear. -/
  forbidden         : List ForbiddenPattern
  deriving Repr

/-- Default bare-metal constraint: no heap, stack bounded. -/
def GCFreeConstraint.default : GCFreeConstraint :=
  { maxStackBytes := 4096
    allowedStrategies := [.static, .stack, .none]
    forbidden := [.unboundedAlloc, .mutableCapture,
                  .dynamicDispatch, .lazyThunk, .heapException] }

/-- Constraint with arena allocation allowed (larger stack budget). -/
def GCFreeConstraint.withArena (maxStack : Nat := 8192) : GCFreeConstraint :=
  { maxStackBytes := maxStack
    allowedStrategies := [.static, .stack, .arena, .none]
    forbidden := [.unboundedAlloc, .mutableCapture,
                  .dynamicDispatch, .lazyThunk, .heapException] }

/-! ## Constraint Checking -/

/-- Check if an allocation profile satisfies a GC-free constraint. -/
def checkProfile (constraint : GCFreeConstraint)
    (profile : AllocProfile) : Bool :=
  profile.strategy ∈ constraint.allowedStrategies
  && match profile.maxStack with
     | some s => s ≤ constraint.maxStackBytes
     | none   => true  -- Unknown stack usage: assume OK (flagged separately)

/-- Check result with diagnostic information. -/
inductive CheckResult where
  | pass
  | failStrategy (name : String) (strategy : AllocStrategy)
  | failStackOverflow (name : String) (used limit : Nat)
  deriving Repr

/-- Check a profile with detailed diagnostics. -/
def checkProfileDetailed (constraint : GCFreeConstraint)
    (profile : AllocProfile) : CheckResult :=
  if ¬(profile.strategy ∈ constraint.allowedStrategies) then
    .failStrategy profile.name profile.strategy
  else match profile.maxStack with
    | some s =>
      if s > constraint.maxStackBytes then
        .failStackOverflow profile.name s constraint.maxStackBytes
      else .pass
    | none => .pass

/-- Check all profiles in a module against a constraint. -/
def checkModule (constraint : GCFreeConstraint)
    (profiles : List AllocProfile) : List CheckResult :=
  profiles.filterMap fun p =>
    let r := checkProfileDetailed constraint p
    match r with
    | .pass => none
    | _     => some r

/-! ## Stack Usage Model -/

/-- Stack frame descriptor for a function. -/
structure StackFrame where
  /-- Function name. -/
  name       : String
  /-- Local variable space in bytes. -/
  localBytes : Nat
  /-- Saved register space in bytes. -/
  savedRegs  : Nat
  /-- Alignment padding in bytes. -/
  padding    : Nat
  deriving Repr

/-- Total frame size. -/
def StackFrame.totalSize (f : StackFrame) : Nat :=
  f.localBytes + f.savedRegs + f.padding

/-- Compute worst-case stack depth for a call chain. -/
def worstCaseStackDepth (frames : List StackFrame) : Nat :=
  frames.foldl (fun acc f => acc + f.totalSize) 0

end Radix.BareMetal.GCFree
