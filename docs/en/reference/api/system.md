# System Module API Reference

> **Module**: `Radix.System`
> **Source**: `Radix/System/`

## Overview

Provides an abstract POSIX-like model for system operations. The only Radix module with a Layer 1 (System Bridge) component. All IO operations return `IO (Except SysError α)` for exception-free error handling.

## Error Model (`System.Error`)

```lean
inductive SysError where
  | permissionDenied (msg : String) | notFound (msg : String)
  | alreadyExists (msg : String) | resourceBusy (msg : String)
  | invalidArgument (msg : String) | noSpace (msg : String)
  | ioError (msg : String) | interrupted (msg : String)
  | endOfFile | invalidState (msg : String) | unsupported (msg : String)

def SysError.fromIOError : IO.Error → SysError  -- Complete mapping
def liftIO : IO α → IO (Except SysError α)      -- Exception capture combinator
instance : ToString SysError
```

## File Descriptor (`System.FD`)

```lean
inductive Ownership where
  | owned     -- FD is owned; will be closed
  | borrowed  -- FD is borrowed; caller manages lifetime

inductive OpenMode where
  | read | write | readWrite | append

def OpenMode.toFSMode : OpenMode → IO.FS.Mode

structure FD where
  handle : IO.FS.Handle
  ownership : Ownership

def FD.ofHandle (h : IO.FS.Handle) (own : Ownership) : FD
def FD.borrow (fd : FD) : FD
def FD.isOwned (fd : FD) : Bool
```

### Resource-Safe File Access

```lean
def FD.withFile (path : String) (mode : OpenMode) (f : FD → IO α) : IO α
```

Opens the file, passes the FD to the callback, and **automatically closes** on exit (even on error). Bracket pattern ensures no resource leaks.

## I/O Operations (`System.IO`)

All functions return `IO (Except SysError α)`:

### Read Operations

```lean
def sysRead (fd : FD) (count : Nat) : IO (Except SysError ByteArray)
def sysReadLine (fd : FD) : IO (Except SysError String)
def sysReadAll (fd : FD) : IO (Except SysError ByteArray)
```

### Write Operations

```lean
def sysWrite (fd : FD) (data : ByteArray) : IO (Except SysError Nat)
def sysWriteString (fd : FD) (s : String) : IO (Except SysError Nat)
```

### Seek

```lean
def sysSeek (fd : FD) (offset : Int) (mode : SeekMode) : IO (Except SysError Unit)
```

### Metadata

```lean
def sysFileMeta (path : String) : IO (Except SysError FileInfo)
def sysFileExists (path : String) : IO (Except SysError Bool)
def sysDirEntries (path : String) : IO (Except SysError (List String))
```

### Convenience Functions

```lean
def readFileBytes (path : String) : IO (Except SysError ByteArray)
def writeFileBytes (path : String) (data : ByteArray) : IO (Except SysError Unit)
def readFileString (path : String) : IO (Except SysError String)
def writeFileString (path : String) (s : String) : IO (Except SysError Unit)
```

## Specification (`System.Spec`)

```lean
inductive FileState where | open | closed
inductive SeekMode where | set | cur | end_

structure FileInfo where
  size : Nat
  isFile : Bool
  isDir : Bool

-- Preconditions (all require open state)
def readPre (state : FileState) : Prop := state = .open
def writePre (state : FileState) : Prop := state = .open
def seekPre (state : FileState) : Prop := state = .open
def closePre (state : FileState) : Prop := state = .open

-- Postconditions
def closePost (pre post : FileState) : Prop := pre = .open ∧ post = .closed
def readPost (pre post : FileState) (count actual : Nat) : Prop
-- Lifecycle model
inductive LifecycleStep | openStep | readStep | writeStep | seekStep | closeStep
```

## Trusted Assumptions (`System.Assumptions`)

All axioms are `Prop`-typed, prefixed with `trust_`, and cite POSIX.1-2024:

| Axiom | Reference | Asserts |
|-------|-----------|---------|
| `trust_read_bounded` | POSIX read(2) | Successful read returns ≤ count bytes |
| `trust_write_bounded` | POSIX write(2) | Successful write writes ≤ count bytes |
| `trust_lean_io_faithful` | Lean 4 runtime | IO.FS.Handle faithfully delegates to POSIX |
| `trust_close_invalidates` | POSIX close(2) | Close invalidates the file descriptor |
| `trust_seek_succeeds` | POSIX lseek(2) | Seek succeeds on valid open file |

## Related Documents

- [Errors](../errors.md) — Error variant details
- [Architecture: TCB](../../en/architecture/README.md#trusted-computing-base-tcb) — TCB analysis
