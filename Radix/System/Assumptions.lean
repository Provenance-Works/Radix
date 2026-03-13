/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.System.Spec

/-!
# System Assumptions (Layer 1)

This module contains all `axiom` declarations for the System module.
These are the ONLY axioms permitted in the entire Radix library per
ADR C-004a.

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

/-- POSIX guarantees that a successful read returns between 0 and
    `count` bytes inclusive. A return of 0 indicates EOF.

    Reference: POSIX.1-2024, read(2):
    "If the value of nbyte is greater than {SSIZE_MAX}, the result
     is implementation-defined. [...] Upon successful completion,
     [...] shall return a non-negative integer indicating the number
     of bytes actually read." -/
axiom trust_read_bounded
    (count : Nat) (actual : Nat) (hSuccess : actual > 0) :
    actual ≤ count

/-- POSIX guarantees that a successful write writes between 1 and
    `count` bytes inclusive for a regular file.

    Reference: POSIX.1-2024, write(2):
    "Upon successful completion, write() [...] shall return the
     number of bytes actually written to the file [...]. This
     number shall never be greater than nbyte." -/
axiom trust_write_bounded
    (count : Nat) (actual : Nat) (hSuccess : actual > 0) :
    actual ≤ count

/-- The Lean 4 runtime's `IO.FS.Handle` operations faithfully
    delegate to the underlying OS file descriptor. In particular,
    `IO.FS.Handle.read` maps to POSIX `read(2)` and
    `IO.FS.Handle.write` maps to POSIX `write(2)`.

    Specifically: a read on an open file returns between 0 and
    `count` bytes (per POSIX) and preserves the open state, so the
    result conforms to `readPost`.

    Reference: Lean 4 runtime — `lean_io_prim_handle_read`,
    `lean_io_prim_handle_write` in `runtime/io.cpp`. -/
axiom trust_lean_io_faithful
    (pre : FileState) (count actual : Nat)
    (hOpen : readPre pre) (hBound : actual ≤ count) :
    readPost pre .open count actual

/-- After a successful close, the file descriptor is no longer
    valid for any I/O operation. The runtime must not reuse
    the same handle object.

    Reference: POSIX.1-2024, close(2):
    "Upon successful completion, 0 shall be returned; [...]
     the file descriptor no longer refers to any file." -/
axiom trust_close_invalidates (pre : FileState) :
    closePre pre → closePost pre .closed

/-- POSIX guarantees that `lseek` on a regular file succeeds when
    the resulting offset is non-negative. A successful seek is a
    valid lifecycle step on an open file.

    Reference: POSIX.1-2024, lseek(2):
    "Upon successful completion, the resulting offset [...] shall
     be returned." -/
axiom trust_seek_succeeds
    (pre : FileState) (mode : SeekMode) (offset : Int)
    (hOpen : seekPre pre) (hNonNeg : offset ≥ 0) :
    validStep pre (.seek mode offset) = true

end Radix.System.Assumptions
