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
    open -> use -> close. -/
inductive FileState where
  /-- The file is open and available for I/O. -/
  | open
  /-- The file has been closed and must not be used. -/
  | closed
  deriving DecidableEq, Repr

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

/-- Precondition for read: file must be in open state. -/
def readPre (state : FileState) : Prop :=
  state = .open

/-- Precondition for write: file must be in open state. -/
def writePre (state : FileState) : Prop :=
  state = .open

/-- Precondition for seek: file must be in open state. -/
def seekPre (state : FileState) : Prop :=
  state = .open

/-- Precondition for close: file must be in open state. -/
def closePre (state : FileState) : Prop :=
  state = .open

instance (state : FileState) : Decidable (readPre state) :=
  inferInstanceAs (Decidable (_ = _))

instance (state : FileState) : Decidable (writePre state) :=
  inferInstanceAs (Decidable (_ = _))

instance (state : FileState) : Decidable (seekPre state) :=
  inferInstanceAs (Decidable (_ = _))

instance (state : FileState) : Decidable (closePre state) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Operation Postconditions -/

/-- Postcondition for close: state transitions to closed. -/
def closePost (_pre : FileState) (post : FileState) : Prop :=
  post = .closed

/-- Postcondition for read: state remains open, returns bytes up to count. -/
def readPost (pre post : FileState) (count : Nat) (result : Nat) : Prop :=
  pre = .open ∧ post = .open ∧ result ≤ count

/-- Postcondition for write: state remains open, writes bytes up to count. -/
def writePost (pre post : FileState) (count : Nat) (result : Nat) : Prop :=
  pre = .open ∧ post = .open ∧ result ≤ count

/-! ## Resource Lifecycle -/

/-- A file lifecycle is well-formed if it starts open, uses operations
    while open, and ends with a close. -/
inductive LifecycleStep where
  /-- Open a file. -/
  | open (path : String)
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
  | .open _    => state == .closed
  | .read _    => state == .open
  | .write _   => state == .open
  | .seek _ _  => state == .open
  | .close     => state == .open

/-- Compute the next state after a lifecycle step. -/
def nextState (_state : FileState) : LifecycleStep → FileState
  | .open _    => .open
  | .read _    => .open
  | .write _   => .open
  | .seek _ _  => .open
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
