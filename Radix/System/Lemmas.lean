/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.System.Spec
import Radix.System.Assumptions

/-!
# System Specification Proofs (Layer 3)

This module contains proofs for the System module's file state machine:
- State transition correctness
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

/-! ## Precondition Properties -/

theorem readPre_iff_open (s : FileState) : readPre s ↔ s = .open := Iff.rfl

theorem writePre_iff_open (s : FileState) : writePre s ↔ s = .open := Iff.rfl

theorem seekPre_iff_open (s : FileState) : seekPre s ↔ s = .open := Iff.rfl

theorem closePre_iff_open (s : FileState) : closePre s ↔ s = .open := Iff.rfl

/-! ## Postcondition Properties -/

theorem readPost_preserves_open (count actual : Nat)
    (h : readPost .open .open count actual) : h.2.1 = rfl := rfl

theorem closePost_yields_closed :
    closePost .open .closed := rfl

theorem readPost_bound (pre post : FileState) (count actual : Nat)
    (h : readPost pre post count actual) : actual ≤ count := h.2.2

/-! ## State Transition Validity -/

theorem validStep_open_read (n : Nat) :
    validStep .open (.read n) = true := rfl

theorem validStep_open_write (n : Nat) :
    validStep .open (.write n) = true := rfl

theorem validStep_open_seek (m : SeekMode) (off : Int) :
    validStep .open (.seek m off) = true := rfl

theorem validStep_open_close :
    validStep .open .close = true := rfl

theorem validStep_closed_open (path : String) :
    validStep .closed (.open path) = true := rfl

theorem validStep_closed_read_false (n : Nat) :
    validStep .closed (.read n) = false := rfl

theorem validStep_closed_write_false (n : Nat) :
    validStep .closed (.write n) = false := rfl

theorem validStep_closed_close_false :
    validStep .closed .close = false := rfl

/-! ## Next State Properties -/

theorem nextState_read_preserves (s : FileState) (n : Nat) :
    nextState s (.read n) = .open := rfl

theorem nextState_write_preserves (s : FileState) (n : Nat) :
    nextState s (.write n) = .open := rfl

theorem nextState_seek_preserves (s : FileState) (m : SeekMode) (off : Int) :
    nextState s (.seek m off) = .open := rfl

theorem nextState_close_closes (s : FileState) :
    nextState s .close = .closed := rfl

theorem nextState_open_opens (s : FileState) (path : String) :
    nextState s (.open path) = .open := rfl

/-! ## Lifecycle Validity -/

theorem validLifecycle_nil (s : FileState) :
    validLifecycle s [] = true := rfl

theorem validLifecycle_open_read_close :
    validLifecycle .closed [.open "/tmp/f", .read 1024, .close] = true := by
  decide

theorem validLifecycle_open_write_close :
    validLifecycle .closed [.open "/tmp/f", .write 512, .close] = true := by
  decide

theorem validLifecycle_open_close :
    validLifecycle .closed [.open "/tmp/f", .close] = true := by
  decide

theorem validLifecycle_double_read :
    validLifecycle .closed [.open "/tmp/f", .read 100, .read 200, .close] = true := by
  decide

theorem validLifecycle_read_write :
    validLifecycle .closed [.open "/tmp/f", .read 100, .write 50, .close] = true := by
  decide

theorem validLifecycle_read_without_open_false :
    validLifecycle .closed [.read 1024] = false := by decide

theorem validLifecycle_double_close_false :
    validLifecycle .closed [.open "/tmp/f", .close, .close] = false := by
  decide

theorem validLifecycle_write_after_close_false :
    validLifecycle .closed [.open "/tmp/f", .close, .write 10] = false := by
  decide

/-! ## Axiom-Based Proofs -/

theorem read_bounded_by_request (count actual : Nat) (h : actual > 0) :
    actual ≤ count := trust_read_bounded count actual h

theorem write_bounded_by_request (count actual : Nat) (h : actual > 0) :
    actual ≤ count := trust_write_bounded count actual h

theorem close_transitions_to_closed :
    closePre .open → closePost .open .closed :=
  trust_close_invalidates .open

theorem seek_on_open_is_valid (mode : SeekMode) (offset : Int) (h : offset ≥ 0) :
    validStep .open (.seek mode offset) = true :=
  trust_seek_succeeds .open mode offset rfl h

theorem io_faithful_read (count actual : Nat) (hBound : actual ≤ count) :
    readPost .open .open count actual :=
  trust_lean_io_faithful .open count actual rfl hBound

end Radix.System
