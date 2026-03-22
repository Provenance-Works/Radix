/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# System Call Specification (Layer 3)

This module defines the abstract POSIX-like model for system operations:
- File state machine (Open / Closed)
- Pre/postconditions for file operations
- Resource lifecycle model (open -> use -> close)

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.
- Defines the formal contracts for System.IO to satisfy.

## References

- FR-007: System Call Model
- FR-007.1: File Operations
- FR-007.4: Proofs and Error Handling
-/

set_option autoImplicit false

namespace Radix.System.Spec

/-! ## File State Machine -/

/-- Abstract state of a file resource. Models the lifecycle
    open -> use -> close with operational state tracking.

    Unlike a simple open/closed tag, this model tracks:
    - The file position (byte offset from the start)
    - The access mode under which the file was opened
    - Cumulative bytes read/written (for specification-level reasoning)

    This enables meaningful pre/postcondition reasoning:
    a read on a write-only file can be rejected at the spec level,
    and sequential reads advance the position correctly. -/
inductive FileAccessMode where
  /-- File was opened for reading only. -/
  | readOnly
  /-- File was opened for writing only (creates or truncates). -/
  | writeOnly
  /-- File was opened for both reading and writing. -/
  | readWrite
  /-- File was opened in append mode (writes always go to the end). -/
  | appendOnly
  deriving DecidableEq, Repr

/-- Whether a file access mode permits reading. -/
def FileAccessMode.canRead : FileAccessMode → Bool
  | .readOnly  => true
  | .writeOnly => false
  | .readWrite => true
  | .appendOnly => false

/-- Whether a file access mode permits writing. -/
def FileAccessMode.canWrite : FileAccessMode → Bool
  | .readOnly  => false
  | .writeOnly => true
  | .readWrite => true
  | .appendOnly => true

/-- Runtime state of an open file. -/
structure OpenFileState where
  /-- Current byte offset (file position). -/
  position : Nat
  /-- Access mode under which the file was opened. -/
  mode : FileAccessMode
  /-- Total bytes read so far (monotonically increasing). -/
  bytesRead : Nat
  /-- Total bytes written so far (monotonically increasing). -/
  bytesWritten : Nat
  deriving DecidableEq, Repr

/-- Abstract state of a file resource. -/
inductive FileState where
  /-- The file is open and available for I/O. -/
  | open (info : OpenFileState)
  /-- The file has been closed and must not be used. -/
  | closed
  deriving DecidableEq, Repr

/-- Convenience: check if a file state is open (regardless of details). -/
def FileState.isOpen : FileState → Bool
  | .open _ => true
  | .closed => false

/-! ## Seek Modes -/

/-- Abstract seek position modes matching POSIX lseek semantics. -/
inductive SeekMode where
  /-- Offset from the beginning of the file. -/
  | set
  /-- Offset from the current position. -/
  | cur
  /-- Offset from the end of the file. -/
  | end_
  deriving DecidableEq, Repr

/-! ## File Metadata -/

/-- Abstract file metadata. -/
structure FileInfo where
  /-- File size in bytes. -/
  size : Nat
  /-- Whether the file is a regular file. -/
  isFile : Bool
  /-- Whether the file is a directory. -/
  isDir : Bool
  deriving Repr

/-! ## Operation Preconditions -/

/-- Precondition for read: file must be open with read permission. -/
def readPre (state : FileState) : Prop :=
  match state with
  | .open info => info.mode.canRead = true
  | .closed    => False

/-- Precondition for write: file must be open with write permission. -/
def writePre (state : FileState) : Prop :=
  match state with
  | .open info => info.mode.canWrite = true
  | .closed    => False

/-- Precondition for seek: file must be open (any mode). -/
def seekPre (state : FileState) : Prop :=
  state.isOpen = true

/-- Precondition for close: file must be open (any mode). -/
def closePre (state : FileState) : Prop :=
  state.isOpen = true

instance (state : FileState) : Decidable (readPre state) := by
  unfold readPre; cases state <;> simp <;> exact inferInstance

instance (state : FileState) : Decidable (writePre state) := by
  unfold writePre; cases state <;> simp <;> exact inferInstance

instance (state : FileState) : Decidable (seekPre state) :=
  inferInstanceAs (Decidable (_ = _))

instance (state : FileState) : Decidable (closePre state) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Operation Postconditions -/

/-- Postcondition for close: state transitions to closed. -/
def closePost (_pre : FileState) (post : FileState) : Prop :=
  post = .closed

/-- Postcondition for read: state remains open with updated position
    and bytes-read counter. Result is bounded by requested count. -/
def readPost (pre post : FileState) (count : Nat) (result : Nat) : Prop :=
  result ≤ count ∧
  match pre, post with
  | .open infoPre, .open infoPost =>
    infoPost.position = infoPre.position + result
    ∧ infoPost.bytesRead = infoPre.bytesRead + result
    ∧ infoPost.mode = infoPre.mode
    ∧ infoPost.bytesWritten = infoPre.bytesWritten
  | _, _ => False

/-- Postcondition for write: state remains open with updated position
    and bytes-written counter. Result is bounded by offered count. -/
def writePost (pre post : FileState) (count : Nat) (result : Nat) : Prop :=
  result ≤ count ∧
  match pre, post with
  | .open infoPre, .open infoPost =>
    infoPost.position = infoPre.position + result
    ∧ infoPost.bytesWritten = infoPre.bytesWritten + result
    ∧ infoPost.mode = infoPre.mode
    ∧ infoPost.bytesRead = infoPre.bytesRead
  | _, _ => False

/-! ## Resource Lifecycle -/

/-- A file lifecycle is well-formed if it starts open, uses operations
    while open, and ends with a close. -/
inductive LifecycleStep where
  /-- Open a file with an access mode. -/
  | open (path : String) (mode : FileAccessMode)
  /-- Read from the file. -/
  | read (count : Nat)
  /-- Write to the file. -/
  | write (count : Nat)
  /-- Seek within the file. -/
  | seek (mode : SeekMode) (offset : Int)
  /-- Close the file. -/
  | close
  deriving Repr

/-- Check if a lifecycle step is valid given the current state. -/
def validStep (state : FileState) : LifecycleStep → Bool
  | .open _ _  => state == .closed
  | .read _    => match state with | .open info => info.mode.canRead | .closed => false
  | .write _   => match state with | .open info => info.mode.canWrite | .closed => false
  | .seek _ _  => state.isOpen
  | .close     => state.isOpen

/-- Compute the next state after a lifecycle step. -/
def nextState (state : FileState) : LifecycleStep → FileState
  | .open _ mode => .open { position := 0, mode := mode, bytesRead := 0, bytesWritten := 0 }
  | .read n    => match state with
    | .open info => .open { info with position := info.position + n, bytesRead := info.bytesRead + n }
    | .closed    => .closed
  | .write n   => match state with
    | .open info => .open { info with position := info.position + n, bytesWritten := info.bytesWritten + n }
    | .closed    => .closed
  | .seek _ _  => state  -- position change modeled abstractly
  | .close     => .closed

/-- A lifecycle is valid if every step is valid for its state. -/
def validLifecycle : FileState → List LifecycleStep → Bool
  | _, [] => true
  | state, step :: rest =>
    validStep state step && validLifecycle (nextState state step) rest

/-! ## Abstract Read/Write Specification -/

/-- Specification for what a correct read operation returns.
    A compliant read of `count` bytes returns between 0 and `count`
    bytes from the current file position. -/
structure ReadSpec where
  /-- Number of bytes requested. -/
  requested : Nat
  /-- Number of bytes actually read (0 indicates EOF). -/
  actual : Nat
  /-- Actual count must not exceed requested. -/
  hBound : actual ≤ requested

/-- Specification for what a correct write operation accepts.
    A compliant write of `count` bytes writes between 0 and `count`
    bytes at the current file position. -/
structure WriteSpec where
  /-- Number of bytes offered. -/
  offered : Nat
  /-- Number of bytes actually written. -/
  actual : Nat
  /-- Actual count must not exceed offered. -/
  hBound : actual ≤ offered

end Radix.System.Spec
