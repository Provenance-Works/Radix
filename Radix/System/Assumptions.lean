/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.System.Spec

/-!
# System Assumptions (Layer 1)

This module contains all `axiom` declarations for the System module.
The full library trusted boundary is split across the System,
Concurrency, and BareMetal `Assumptions.lean` files per ADR C-004a.

## Rules (ADR C-004a)

1. All axioms MUST be `Prop`-typed.
2. All axioms MUST use the `trust_` prefix.
3. Each axiom MUST cite its POSIX or Lean 4 runtime reference.
4. Axioms are only for properties of the external world that
   Lean 4's type system cannot verify.

## Architecture

This is a **Layer 1 (System Bridge)** module.
- Contains ONLY axiom declarations and nothing else.
- Referenced by proof modules that need to reason about I/O behavior.

## References

- ADR C-004a: Axiom discipline
- POSIX.1-2024 (IEEE Std 1003.1)
-/

set_option autoImplicit false

namespace Radix.System.Assumptions

open Radix.System.Spec

/-! ## File System Axioms -/

/-- An opaque descriptor of an OS-level file operation result.
    Lean cannot construct or inspect values of this type; it
    exists so axioms about OS behavior are genuinely unprovable.
    The `requestedCount` field records the count passed to the
    OS call, binding the result to a specific request. -/
opaque OSReadResult : Type

/-- The number of bytes the OS actually transferred. -/
opaque OSReadResult.actual (r : OSReadResult) : Nat

/-- The number of bytes requested in the OS call that produced
    this result.  Opaque — binds each result to a specific request
    so the bound axiom cannot be trivialized by choosing count = 0. -/
opaque OSReadResult.requestedCount (r : OSReadResult) : Nat

/-- POSIX guarantees that a successful `read(2)` returns between 0
    and `count` bytes inclusive. A return of 0 indicates EOF.
    This is an external OS guarantee that Lean cannot verify.

    The bound is stated in terms of the *same* request's count,
    preventing trivialization by instantiating with count = 0.

    Reference: POSIX.1-2024, read(2):
    "Upon successful completion, [...] shall return a non-negative
     integer indicating the number of bytes actually read. [...]
     This number shall never be greater than nbyte." -/
axiom trust_read_bounded
    (result : OSReadResult) :
    result.actual ≤ result.requestedCount

/-- POSIX guarantees that a successful `write(2)` writes between 1
    and `count` bytes inclusive for a regular file.

    Reference: POSIX.1-2024, write(2):
    "Upon successful completion, write() [...] shall return the
     number of bytes actually written to the file [...]. This
     number shall never be greater than nbyte." -/
axiom trust_write_bounded
    (result : OSReadResult) :
    result.actual ≤ result.requestedCount

/-- The opaque result of a Lean 4 runtime IO read operation.
    Lean cannot construct values — the actual byte count is
    determined by the OS at runtime. -/
opaque IOReadActual (pre : FileState) (count : Nat) (hOpen : readPre pre) : Nat

/-- The Lean 4 runtime's `IO.FS.Handle` operations faithfully
    delegate to the underlying OS file descriptor. In particular,
    `IO.FS.Handle.read` maps to POSIX `read(2)` and produces a
    `ByteArray` whose length satisfies the POSIX read bound.

    This axiom bridges the gap between Lean 4's monadic `IO` type
    (which erases operational semantics) and the POSIX contract
    (which bounds the result). It cannot be proven because Lean's
    `IO` type is opaque — we cannot inspect what `IO.FS.Handle.read`
    actually does.  The opaque `IOReadActual` prevents trivialization
    by choosing `actual := 0`.

    Reference: Lean 4 runtime — `lean_io_prim_handle_read` in
    `runtime/io.cpp`. -/
axiom trust_lean_io_faithful
    (pre : FileState) (count : Nat)
    (hOpen : readPre pre) :
    let actual := IOReadActual pre count hOpen
    actual ≤ count ∧
      ∀ (info : OpenFileState), pre = FileState.open info →
        readPost pre
          (FileState.open { info with
            position := info.position + actual,
            bytesRead := info.bytesRead + actual })
          count actual

end Radix.System.Assumptions
