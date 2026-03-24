/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.System.Spec
import Radix.System.Error

/-!
# File Descriptor Abstraction (Layer 2)

This module provides a typed file descriptor wrapper with ownership
semantics and the `withFile` bracket pattern for resource safety.

## Architecture

This is a **Layer 2 (Implementation)** module.
- Wraps `IO.FS.Handle` with ownership tracking.
- Provides the `withFile` bracket pattern ensuring flush-on-exit
  for write modes.
- Does NOT perform I/O directly — delegates to System.IO.

## Design

The `FD` type wraps an `IO.FS.Handle` with an ownership tag.
- `Owned`: The caller is responsible for the FD's lifetime.
- `Borrowed`: The FD was obtained from elsewhere; do not manage.

The `withFile` combinator guarantees:
1. The file is opened before the body runs.
2. Write buffers are flushed after the body completes successfully.

**Note on handle lifecycle (C-001)**:
Lean 4's `IO.FS.Handle` is garbage-collected; there is no explicit
`close` method in the pure Lean 4 API. The standard library's own
`IO.FS.withFile` has the same characteristic. Flushing write buffers
is the mechanism for ensuring data durability before GC collects
the handle.

## References

- FR-007.1: File Operations
- FR-007.3: Resource Management
- ADR C-001: Pure Lean 4
-/

set_option autoImplicit false

namespace Radix.System

/-! ## Ownership Model -/

/-- Ownership tag for a file descriptor. -/
inductive Ownership where
  /-- Caller owns the FD and must close it. -/
  | owned
  /-- FD is borrowed; do not close. -/
  | borrowed
  deriving DecidableEq, Repr

/-! ## File Open Mode -/

/-- File open modes corresponding to POSIX fopen modes. -/
inductive OpenMode where
  /-- Read-only. File must exist. -/
  | read
  /-- Write-only. Creates or truncates. -/
  | write
  /-- Read-write. Creates or truncates. -/
  | readWrite
  /-- Append. Creates if needed, writes at end. -/
  | append
  deriving DecidableEq, Repr

/-- Convert our OpenMode to Lean 4's IO.FS.Mode. -/
def OpenMode.toFSMode : OpenMode → IO.FS.Mode
  | .read      => .read
  | .write     => .write
  | .readWrite => .readWrite
  | .append    => .append

/-- Whether this mode permits reads. -/
def OpenMode.canRead : OpenMode → Bool
  | .read => true
  | .write => false
  | .readWrite => true
  | .append => false

/-- Whether this mode permits writes. -/
def OpenMode.canWrite : OpenMode → Bool
  | .read => false
  | .write => true
  | .readWrite => true
  | .append => true

/-! ## File Descriptor -/

/-- A file descriptor wrapping a Lean 4 `IO.FS.Handle` with
    ownership tracking. -/
structure FD where
  /-- The underlying Lean 4 file handle. -/
  handle : IO.FS.Handle
  /-- The access mode used to open the handle. -/
  mode : OpenMode
  /-- Ownership tag. -/
  ownership : Ownership

/-- Create an owned FD from a handle. -/
def FD.ofHandle (h : IO.FS.Handle) (mode : OpenMode) : FD :=
  { handle := h, mode := mode, ownership := .owned }

/-- Create a borrowed FD from a handle. -/
def FD.borrow (h : IO.FS.Handle) (mode : OpenMode) : FD :=
  { handle := h, mode := mode, ownership := .borrowed }

/-- Check if this FD is owned. -/
def FD.isOwned (fd : FD) : Bool :=
  fd.ownership == .owned

/-! ## Bracket Pattern -/

/-- Open a file, run a computation using the FD, then flush write buffers.
    This is the primary resource-safe pattern for file I/O.

    For write modes (`.write`, `.readWrite`, `.append`), the handle is
    flushed after `body` completes successfully. If the body returns
    an error, flush is skipped (the write was incomplete anyway).
    If flush fails after a successful body, the flush error is returned.

    Lean 4 handles are garbage-collected (no explicit `close` per C-001).
    Flushing ensures data durability before GC collects the handle.

    ```
    withFile "/tmp/test.txt" .read fun fd => do
      System.IO.sysRead fd 1024
    ```
-/
def withFile {α : Type} (path : String) (mode : OpenMode)
    (body : FD → IO (Except SysError α)) : IO (Except SysError α) := do
  let handleResult ← liftIO (IO.FS.Handle.mk (path : System.FilePath) mode.toFSMode)
  match handleResult with
  | .error e => return .error e
  | .ok handle =>
    let fd := FD.ofHandle handle mode
    let result ← body fd
    -- Flush write buffers to ensure data persistence before GC
    match mode, result with
    | .read, _ => return result
    | _, .error _ => return result
    | _, .ok _ =>
      let flushResult ← liftIO handle.flush
      match flushResult with
      | .error e => return .error e
      | .ok () => return result

end Radix.System
