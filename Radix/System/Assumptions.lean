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

/-- An opaque descriptor of an OS-level file operation result.
    Lean cannot construct or inspect values of this type; it
    exists so axioms about OS behavior are genuinely unprovable. -/
opaque OSReadResult : Type

/-- The number of bytes the OS actually transferred in a read. -/
opaque OSReadResult.actual (r : OSReadResult) : Nat

/-- POSIX guarantees that a successful `read(2)` returns between 0
    and `count` bytes inclusive. A return of 0 indicates EOF.
    This is an external OS guarantee that Lean cannot verify.

    Reference: POSIX.1-2024, read(2):
    "Upon successful completion, [...] shall return a non-negative
     integer indicating the number of bytes actually read. [...]
     This number shall never be greater than nbyte." -/
axiom trust_read_bounded
    (count : Nat) (result : OSReadResult) :
    result.actual ≤ count

/-- POSIX guarantees that a successful `write(2)` writes between 1
    and `count` bytes inclusive for a regular file.

    Reference: POSIX.1-2024, write(2):
    "Upon successful completion, write() [...] shall return the
     number of bytes actually written to the file [...]. This
     number shall never be greater than nbyte." -/
axiom trust_write_bounded
    (count : Nat) (result : OSReadResult) :
    result.actual ≤ count

/-- The Lean 4 runtime's `IO.FS.Handle` operations faithfully
    delegate to the underlying OS file descriptor. In particular,
    `IO.FS.Handle.read` maps to POSIX `read(2)` and produces a
    `ByteArray` whose length satisfies the POSIX read bound.

    This axiom bridges the gap between Lean 4's monadic `IO` type
    (which erases operational semantics) and the POSIX contract
    (which bounds the result). It cannot be proven because Lean's
    `IO` type is opaque — we cannot inspect what `IO.FS.Handle.read`
    actually does.

    Reference: Lean 4 runtime — `lean_io_prim_handle_read` in
    `runtime/io.cpp`. -/
axiom trust_lean_io_faithful
    (pre : FileState) (count : Nat)
    (hOpen : readPre pre) :
    ∃ (actual : Nat), actual ≤ count ∧
      ∀ (info : OpenFileState), pre = FileState.open info →
        readPost pre
          (FileState.open { info with
            position := info.position + actual,
            bytesRead := info.bytesRead + actual })
          count actual

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
