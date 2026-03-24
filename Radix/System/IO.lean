/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.System.FD

/-!
# System I/O Operations (Layer 1)

This module provides the system call wrappers for file I/O.
Every operation wraps Lean 4's `IO.FS` API and returns
`IO (Except SysError α)` for exception-free error handling.

## Architecture

This is a **Layer 1 (System Bridge)** module — the ONLY layer
permitted to perform real I/O via Lean 4's runtime.

- Wraps `IO.FS.Handle` methods (read, write, getLine, etc.)
- All functions return `IO (Except SysError α)`
- No exceptions escape — all are caught and mapped to `SysError`

## Constraints

- **C-001**: No FFI, no `@[extern]`. Uses only Lean 4 `IO.FS`.
- **C-004a**: No axioms here. Axioms live in `System.Assumptions`.

## References

- FR-007: System Call Model
- FR-007.1: File Operations (sysRead, sysWrite, sysSeek)
- FR-007.2: Process Operations (deferred to future phase)
-/

set_option autoImplicit false

namespace Radix.System.IO

open Radix.System

/-! ## Read Operations -/

private def checkReadable (fd : FD) : Except SysError Unit :=
  if fd.mode.canRead then
    .ok ()
  else
    .error (.permissionDenied "file descriptor is not open for reading")

private def checkWritable (fd : FD) : Except SysError Unit :=
  if fd.mode.canWrite then
    .ok ()
  else
    .error (.permissionDenied "file descriptor is not open for writing")

/-- Read up to `count` bytes from a file descriptor.
    Returns a `ByteArray` of length ≤ `count`.
    Returns empty `ByteArray` at EOF. -/
def sysRead (fd : FD) (count : USize) : IO (Except SysError ByteArray) :=
  match checkReadable fd with
  | .error e => pure (.error e)
  | .ok () => liftIO (fd.handle.read count)

/-- Read a single line (up to and including newline) from a file descriptor.
    Returns an empty string at EOF. -/
def sysReadLine (fd : FD) : IO (Except SysError String) :=
  match checkReadable fd with
  | .error e => pure (.error e)
  | .ok () => liftIO (fd.handle.getLine)

/-- Read all remaining bytes from the current position to EOF. -/
def sysReadAll (fd : FD) : IO (Except SysError ByteArray) :=
  match checkReadable fd with
  | .error e => pure (.error e)
  | .ok () =>
    liftIO (do
      let mut result := ByteArray.empty
      let mut done := false
      while !done do
        let chunk ← fd.handle.read 4096
        if chunk.isEmpty then
          done := true
        else
          result := result ++ chunk
      return result)

/-! ## Write Operations -/

/-- Write a byte array to a file descriptor.
    Writes all bytes (Lean 4's `IO.FS.Handle.write` is total). -/
def sysWrite (fd : FD) (data : ByteArray) : IO (Except SysError Unit) :=
  match checkWritable fd with
  | .error e => pure (.error e)
  | .ok () => liftIO (fd.handle.write data)

/-- Write a string (as UTF-8) to a file descriptor. -/
def sysWriteString (fd : FD) (s : String) : IO (Except SysError Unit) :=
  match checkWritable fd with
  | .error e => pure (.error e)
  | .ok () => liftIO (fd.handle.putStr s)

/-! ## Seek Operations -/

/-- Convert our SeekMode to a Lean 4-compatible seek value and
    perform the seek. The offset is relative to the chosen origin.

    Limitations of the pure Lean 4 backend (C-001: no FFI):
    - SEEK_SET: O(n) time via rewind + chunked skip, but O(1) memory.
    - SEEK_CUR (positive): O(n) time via chunked skip.
    - SEEK_CUR (negative): Not supported — returns `unsupported` error.
    - SEEK_END: Not supported — returns `unsupported` error. -/
def sysSeek (fd : FD) (mode : Spec.SeekMode) (offset : Int)
    : IO (Except SysError Unit) :=
  liftIO (do
    match mode with
    | .set   =>
      -- POSIX SEEK_SET: absolute position via rewind + chunked skip
      if offset < 0 then
        throw (.invalidArgument none 0 "sysSeek: negative offset for SEEK_SET")
      IO.FS.Handle.rewind fd.handle
      skipBytes fd.handle offset.toNat
    | .cur   =>
      -- POSIX SEEK_CUR: relative skip forward only
      if offset < 0 then
        throw (.unsupportedOperation 0 "sysSeek: negative SEEK_CUR not supported without FFI (C-001)")
      skipBytes fd.handle offset.toNat
    | .end_  =>
      -- SEEK_END not supported without lseek FFI
      throw (.unsupportedOperation 0 "sysSeek: SEEK_END not supported without FFI (C-001)"))
where
  /-- Skip `n` bytes by reading and discarding in 4096-byte chunks. O(1) memory. -/
  skipBytes (h : IO.FS.Handle) (n : Nat) : IO Unit := do
    let mut remaining := n
    while remaining > 0 do
      let chunkSize := min remaining 4096
      let _ ← h.read chunkSize.toUSize
      remaining := remaining - chunkSize

/-! ## File Metadata Operations -/

/-- Get metadata for a file at the given path. -/
def sysFileMeta (path : String) : IO (Except SysError Spec.FileInfo) :=
  liftIO (do
    let info ← (path : System.FilePath).metadata
    return {
      size := info.byteSize.toNat
      isFile := info.type == .file
      isDir := info.type == .dir
    })

/-- Check if a file exists at the given path. -/
def sysFileExists (path : String) : IO (Except SysError Bool) :=
  liftIO (do
    let info ← (path : System.FilePath).metadata
    return info.type == .file)

/-! ## Directory Operations -/

/-- List entries in a directory. Returns file names (not full paths). -/
def sysDirEntries (path : String) : IO (Except SysError (Array String)) :=
  liftIO (do
    let entries ← (path : System.FilePath).readDir
    return entries.map fun e => e.fileName)

/-! ## Convenience Combinators -/

/-- Read an entire file as a `ByteArray`. -/
def readFileBytes (path : String) : IO (Except SysError ByteArray) :=
  withFile path .read fun fd => sysReadAll fd

/-- Write a `ByteArray` to a file (creates or truncates). -/
def writeFileBytes (path : String) (data : ByteArray)
    : IO (Except SysError Unit) :=
  withFile path .write fun fd => sysWrite fd data

/-- Read an entire file as a `String`. -/
def readFileString (path : String) : IO (Except SysError String) :=
  liftIO (IO.FS.readFile (path : System.FilePath))

/-- Write a `String` to a file (creates or truncates). -/
def writeFileString (path : String) (content : String)
    : IO (Except SysError Unit) :=
  liftIO (IO.FS.writeFile (path : System.FilePath) content)

end Radix.System.IO
