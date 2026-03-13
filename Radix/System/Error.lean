/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# System Error Model (Layer 2)

This module defines the error types for system operations.
All system I/O operations return `IO (Except SysError α)` to
provide an exception-free API surface.

## Architecture

This is a **Layer 2 (Implementation)** module.
- Provides the error ADT used by System.FD and System.IO.
- Maps from Lean 4's `IO.Error` to our domain-specific error type.

## References

- FR-007.4: Error Handling
- ADR C-001: Pure Lean 4 only (no FFI)
-/

set_option autoImplicit false

namespace Radix.System

/-! ## Error Type -/

/-- System error codes covering the POSIX error classes we support.
    All system operations in `System.IO` return `Except SysError α`
    rather than throwing exceptions. -/
inductive SysError where
  /-- Permission denied (EACCES / EPERM). -/
  | permissionDenied (msg : String)
  /-- File or directory not found (ENOENT). -/
  | notFound (msg : String)
  /-- File already exists (EEXIST). -/
  | alreadyExists (msg : String)
  /-- Resource is busy or locked (EBUSY). -/
  | resourceBusy (msg : String)
  /-- Invalid argument to a system call (EINVAL). -/
  | invalidArgument (msg : String)
  /-- No space left on device (ENOSPC). -/
  | noSpace (msg : String)
  /-- I/O error (EIO) or other unclassified OS error. -/
  | ioError (msg : String)
  /-- Operation interrupted by signal (EINTR). -/
  | interrupted (msg : String)
  /-- End of file reached. -/
  | endOfFile
  /-- The file descriptor is in an invalid state
      (e.g., using a closed handle). -/
  | invalidState (msg : String)
  /-- The operation is not supported in the pure Lean 4 backend
      (e.g., negative SEEK_CUR, SEEK_END without FFI). -/
  | unsupported (msg : String)
  deriving Repr, BEq

instance : ToString SysError where
  toString
    | .permissionDenied msg  => s!"permission denied: {msg}"
    | .notFound msg          => s!"not found: {msg}"
    | .alreadyExists msg     => s!"already exists: {msg}"
    | .resourceBusy msg      => s!"resource busy: {msg}"
    | .invalidArgument msg   => s!"invalid argument: {msg}"
    | .noSpace msg           => s!"no space: {msg}"
    | .ioError msg           => s!"I/O error: {msg}"
    | .interrupted msg       => s!"interrupted: {msg}"
    | .endOfFile             => "end of file"
    | .invalidState msg      => s!"invalid state: {msg}"
    | .unsupported msg       => s!"unsupported: {msg}"

/-! ## Conversion from Lean 4 IO.Error -/

/-- Map a Lean 4 `IO.Error` to our domain-specific `SysError`.
    This is the single point of translation between the Lean runtime
    error model and our typed error model. -/
def SysError.fromIOError (e : IO.Error) : SysError :=
  match e with
  | .alreadyExists _ _ msg        => .alreadyExists msg
  | .otherError _ msg             => .ioError msg
  | .resourceBusy _ msg           => .resourceBusy msg
  | .resourceVanished _ msg       => .notFound msg
  | .unsupportedOperation _ msg   => .invalidArgument msg
  | .hardwareFault _ msg          => .ioError msg
  | .unsatisfiedConstraints _ msg => .invalidArgument msg
  | .illegalOperation _ msg       => .invalidState msg
  | .protocolError _ msg          => .ioError msg
  | .timeExpired _ msg            => .ioError msg
  | .interrupted _ _ msg          => .interrupted msg
  | .noFileOrDirectory _ _ msg    => .notFound msg
  | .invalidArgument _ _ msg      => .invalidArgument msg
  | .permissionDenied _ _ msg     => .permissionDenied msg
  | .resourceExhausted _ _ msg    => .noSpace msg
  | .inappropriateType _ _ msg    => .invalidArgument msg
  | .noSuchThing _ _ msg          => .notFound msg
  | .userError msg                => .ioError msg
  | .unexpectedEof                => .endOfFile

/-! ## Helper Combinators -/

/-- Lift an `IO α` action into `IO (Except SysError α)`,
    catching any IO exception and converting it to `SysError`. -/
def liftIO {α : Type} (action : IO α) : IO (Except SysError α) := do
  try
    let result ← action
    return .ok result
  catch e =>
    return .error (SysError.fromIOError e)

end Radix.System
