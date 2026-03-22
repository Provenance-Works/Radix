/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.System.Spec
import Radix.System.Assumptions

/-!
# System Specification Proofs (Layer 3)

This module contains proofs for the System module's file state machine:
- Access mode capability reasoning
- State transition correctness with position tracking
- Lifecycle validity properties
- Pre/postcondition consistency
- Axiom-based I/O correctness

## Architecture

This is a **Layer 3 (Verified Specification)** module containing proofs.

## References

- FR-007: System Call Model
- FR-007.4: Proofs and Error Handling
-/

set_option autoImplicit false

namespace Radix.System

open Spec
open Assumptions

/-! ## Access Mode Properties -/

@[simp] theorem FileAccessMode.readOnly_canRead : FileAccessMode.readOnly.canRead = true := rfl
@[simp] theorem FileAccessMode.readOnly_not_canWrite : FileAccessMode.readOnly.canWrite = false := rfl
@[simp] theorem FileAccessMode.writeOnly_canWrite : FileAccessMode.writeOnly.canWrite = true := rfl
@[simp] theorem FileAccessMode.writeOnly_not_canRead : FileAccessMode.writeOnly.canRead = false := rfl
@[simp] theorem FileAccessMode.readWrite_canRead : FileAccessMode.readWrite.canRead = true := rfl
@[simp] theorem FileAccessMode.readWrite_canWrite : FileAccessMode.readWrite.canWrite = true := rfl
@[simp] theorem FileAccessMode.appendOnly_canWrite : FileAccessMode.appendOnly.canWrite = true := rfl
@[simp] theorem FileAccessMode.appendOnly_not_canRead : FileAccessMode.appendOnly.canRead = false := rfl

/-! ## Precondition Properties -/

theorem readPre_of_open_readable (info : OpenFileState) (h : info.mode.canRead = true) :
    readPre (.open info) := by
  simp [readPre, h]

theorem readPre_not_closed : ¬ readPre .closed := by
  simp [readPre]

theorem writePre_of_open_writable (info : OpenFileState) (h : info.mode.canWrite = true) :
    writePre (.open info) := by
  simp [writePre, h]

theorem writePre_not_closed : ¬ writePre .closed := by
  simp [writePre]

theorem readPre_readOnly (info : OpenFileState) (hm : info.mode = .readOnly) :
    readPre (.open info) := by
  simp [readPre, hm, FileAccessMode.canRead]

theorem writePre_readOnly_false (info : OpenFileState) (hm : info.mode = .readOnly) :
    ¬ writePre (.open info) := by
  simp [writePre, hm, FileAccessMode.canWrite]

theorem readPre_writeOnly_false (info : OpenFileState) (hm : info.mode = .writeOnly) :
    ¬ readPre (.open info) := by
  simp [readPre, hm, FileAccessMode.canRead]

theorem seekPre_of_open (info : OpenFileState) :
    seekPre (.open info) := by
  simp [seekPre, FileState.isOpen]

theorem closePre_of_open (info : OpenFileState) :
    closePre (.open info) := by
  simp [closePre, FileState.isOpen]

theorem seekPre_not_closed : ¬ seekPre .closed := by
  simp [seekPre, FileState.isOpen]

theorem closePre_not_closed : ¬ closePre .closed := by
  simp [closePre, FileState.isOpen]

/-! ## Postcondition Properties -/

theorem closePost_yields_closed (info : OpenFileState) :
    closePost (.open info) .closed := rfl

theorem readPost_advances_position (info : OpenFileState) (count actual : Nat)
    (h : actual ≤ count) :
    let post := OpenFileState.mk (info.position + actual) info.mode (info.bytesRead + actual) info.bytesWritten
    readPost (.open info) (.open post) count actual := by
  exact ⟨h, rfl, rfl, rfl, rfl⟩

theorem readPost_bound (pre post : FileState) (count actual : Nat)
    (h : readPost pre post count actual) : actual ≤ count := h.1

theorem writePost_advances_position (info : OpenFileState) (count actual : Nat)
    (h : actual ≤ count) :
    let post := OpenFileState.mk (info.position + actual) info.mode info.bytesRead (info.bytesWritten + actual)
    writePost (.open info) (.open post) count actual := by
  exact ⟨h, rfl, rfl, rfl, rfl⟩

theorem writePost_bound (pre post : FileState) (count actual : Nat)
    (h : writePost pre post count actual) : actual ≤ count := h.1

/-! ## State Transition Validity -/

theorem validStep_open_read (info : OpenFileState) (n : Nat) (hm : info.mode.canRead = true) :
    validStep (.open info) (.read n) = true := by
  simp [validStep, hm]

theorem validStep_open_write (info : OpenFileState) (n : Nat) (hm : info.mode.canWrite = true) :
    validStep (.open info) (.write n) = true := by
  simp [validStep, hm]

theorem validStep_open_seek (info : OpenFileState) (m : SeekMode) (off : Int) :
    validStep (.open info) (.seek m off) = true := by
  simp [validStep, FileState.isOpen]

theorem validStep_open_close (info : OpenFileState) :
    validStep (.open info) .close = true := by
  simp [validStep, FileState.isOpen]

@[simp] theorem validStep_closed_open (path : String) (mode : FileAccessMode) :
    validStep .closed (.open path mode) = true := rfl

@[simp] theorem validStep_closed_read_false (n : Nat) :
    validStep .closed (.read n) = false := rfl

@[simp] theorem validStep_closed_write_false (n : Nat) :
    validStep .closed (.write n) = false := rfl

@[simp] theorem validStep_closed_close_false :
    validStep .closed .close = false := rfl

/-! ## Next State Properties -/

theorem nextState_open_opens (state : FileState) (path : String) (mode : FileAccessMode) :
    (nextState state (.open path mode)).isOpen = true := by
  simp [nextState, FileState.isOpen]

@[simp] theorem nextState_close_closes (state : FileState) :
    nextState state .close = .closed := rfl

theorem nextState_read_preserves_mode (info : OpenFileState) (n : Nat) :
    match nextState (.open info) (.read n) with
    | .open info' => info'.mode = info.mode
    | .closed => False := by
  simp [nextState]

theorem nextState_write_preserves_mode (info : OpenFileState) (n : Nat) :
    match nextState (.open info) (.write n) with
    | .open info' => info'.mode = info.mode
    | .closed => False := by
  simp [nextState]

theorem nextState_read_advances_position (info : OpenFileState) (n : Nat) :
    match nextState (.open info) (.read n) with
    | .open info' => info'.position = info.position + n
    | .closed => False := by
  simp [nextState]

theorem nextState_write_advances_position (info : OpenFileState) (n : Nat) :
    match nextState (.open info) (.write n) with
    | .open info' => info'.position = info.position + n
    | .closed => False := by
  simp [nextState]

/-! ## Lifecycle Validity -/

theorem validLifecycle_nil (s : FileState) :
    validLifecycle s [] = true := rfl

theorem validLifecycle_open_read_close :
    validLifecycle .closed [.open "/tmp/f" .readOnly, .read 1024, .close] = true := by
  rfl

theorem validLifecycle_open_write_close :
    validLifecycle .closed [.open "/tmp/f" .writeOnly, .write 512, .close] = true := by
  rfl

theorem validLifecycle_open_close :
    validLifecycle .closed [.open "/tmp/f" .readOnly, .close] = true := by
  rfl

theorem validLifecycle_readOnly_cannot_write :
    validLifecycle .closed [.open "/tmp/f" .readOnly, .write 100, .close] = false := by
  rfl

theorem validLifecycle_writeOnly_cannot_read :
    validLifecycle .closed [.open "/tmp/f" .writeOnly, .read 100, .close] = false := by
  rfl

theorem validLifecycle_readWrite_can_both :
    validLifecycle .closed [.open "/tmp/f" .readWrite, .read 100, .write 50, .close] = true := by
  rfl

theorem validLifecycle_read_without_open_false :
    validLifecycle .closed [.read 1024] = false := by rfl

theorem validLifecycle_double_close_false :
    validLifecycle .closed [.open "/tmp/f" .readOnly, .close, .close] = false := by
  rfl

theorem validLifecycle_write_after_close_false :
    validLifecycle .closed [.open "/tmp/f" .writeOnly, .close, .write 10] = false := by
  rfl

/-! ## Mode Safety -/

/-- A read-only file never has a write as the first operation after open. -/
theorem readOnly_write_step_invalid (n : Nat) :
    validStep (.open { position := 0, mode := .readOnly, bytesRead := 0, bytesWritten := 0 }) (.write n) = false := by
  simp [validStep, FileAccessMode.canWrite]

/-! ## Axiom-Based Proofs -/

theorem read_bounded_by_request (result : Assumptions.OSReadResult) :
    result.actual ≤ result.requestedCount := trust_read_bounded result

theorem write_bounded_by_request (result : Assumptions.OSReadResult) :
    result.actual ≤ result.requestedCount := trust_write_bounded result

theorem close_transitions_to_closed (info : OpenFileState) :
    closePre (.open info) → closePost (.open info) .closed := by
  intro _; rfl

theorem seek_valid_when_open (info : OpenFileState) (mode : SeekMode) (offset : Int) :
    seekPre (.open info) → validStep (.open info) (.seek mode offset) = true := by
  intro _; simp [validStep, FileState.isOpen]

theorem io_faithful_read (count : Nat) (info : OpenFileState) (hRead : info.mode.canRead = true) :
    let actual := Assumptions.IOReadActual (.open info) count (by simp [readPre, hRead])
    actual ≤ count ∧ readPost
      (.open info)
      (.open { info with position := info.position + actual, bytesRead := info.bytesRead + actual })
      count actual := by
  have h := trust_lean_io_faithful (.open info) count (by simp [readPre, hRead])
  exact ⟨h.1, h.2 info rfl⟩

end Radix.System
