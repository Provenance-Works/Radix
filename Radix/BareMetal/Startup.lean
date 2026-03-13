/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.BareMetal.Spec
import Radix.BareMetal.Linker

/-!
# Platform Startup Sequence Model (Layer 2)

This module models platform-specific startup sequences for
bare-metal targets:

- Startup step definitions for each platform
- Init sequence construction and validation
- BSS zeroing and data section initialization models
- Interrupt vector table setup model

## Architecture

This is a **Layer 2 (Implementation)** module.

## References

- P5-02: Platform-specific startup code
- ARM Architecture Reference Manual, Chapter D1.6 (Reset)
- RISC-V Privileged Specification, Section 3.4 (Reset)
- Intel SDM Vol. 3A, Chapter 9 (Processor Management and Initialization)
-/

set_option autoImplicit false

namespace Radix.BareMetal.Startup

open Radix.BareMetal.Spec
open Radix.BareMetal.Linker

/-! ## Startup Actions -/

/-- Individual actions performed during startup. -/
inductive StartupAction where
  /-- Set the stack pointer to a given address. -/
  | setStackPointer (addr : Nat)
  /-- Zero the BSS section (base address + size). -/
  | zeroBSS (baseAddr size : Nat)
  /-- Copy initialized data from Flash (LMA) to RAM (VMA). -/
  | copyData (lma vma size : Nat)
  /-- Configure the interrupt vector table base address. -/
  | setVectorTable (addr : Nat)
  /-- Enable/disable interrupts. -/
  | setInterrupts (enable : Bool)
  /-- Configure clock source and dividers. -/
  | configClock
  /-- Call global constructors. -/
  | callConstructors
  /-- Jump to application entry point. -/
  | jumpToEntry (addr : Nat)
  deriving Repr

/-! ## Platform Startup Templates -/

/-- The standard startup sequence for a bare-metal target.
    This is the minimum viable sequence to reach application code. -/
def minimalStartupActions (stackTop bssBase bssSize dataLMA dataVMA dataSize entry : Nat) :
    List StartupAction :=
  [ .setInterrupts false
  , .setStackPointer stackTop
  , .zeroBSS bssBase bssSize
  , .copyData dataLMA dataVMA dataSize
  , .setInterrupts true
  , .jumpToEntry entry ]

/-- Extended startup with interrupt vector table and clock configuration. -/
def fullStartupActions (stackTop bssBase bssSize dataLMA dataVMA dataSize
    vectorTable entry : Nat) :
    List StartupAction :=
  [ .setInterrupts false
  , .setStackPointer stackTop
  , .setVectorTable vectorTable
  , .configClock
  , .zeroBSS bssBase bssSize
  , .copyData dataLMA dataVMA dataSize
  , .callConstructors
  , .setInterrupts true
  , .jumpToEntry entry ]

/-! ## Startup Validation -/

/-- A startup action list must begin with disabling interrupts. -/
def startsWithInterruptsDisabled (actions : List StartupAction) : Bool :=
  match actions.head? with
  | some (.setInterrupts false) => true
  | _ => false

/-- A startup action list must set the stack pointer before any
    function-style operations. -/
def setsStackBeforeUse (actions : List StartupAction) : Bool :=
  let spIdx := actions.findIdx? (fun a => match a with
    | .setStackPointer _ => true | _ => false)
  let useIdx := actions.findIdx? (fun a => match a with
    | .zeroBSS _ _ | .copyData _ _ _ | .callConstructors | .jumpToEntry _ => true
    | _ => false)
  match spIdx, useIdx with
  | some sp, some use => sp < use
  | some _, none      => true   -- SP set but no users: OK
  | none, none        => true   -- No SP and no users: trivial OK
  | none, some _      => false  -- Users without SP: invalid

/-- A startup action list must end with jumping to entry. -/
def endsWithJump (actions : List StartupAction) : Bool :=
  match actions.getLast? with
  | some (.jumpToEntry _) => true
  | _ => false

/-- Full validation of a startup action sequence. -/
def isValidStartupSequence (actions : List StartupAction) : Bool :=
  actions.length > 0
  && startsWithInterruptsDisabled actions
  && setsStackBeforeUse actions
  && endsWithJump actions

/-! ## Startup from Linker Script -/

/-- Extract startup parameters from a linker script.
    Returns (stackTop, bssBase, bssSize, dataLMA, dataVMA, dataSize, entry)
    or none if required sections/symbols are missing. -/
def extractStartupParams (ls : LinkerScript) :
    Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat) := do
  let bss ← ls.findSection ".bss"
  let data ← ls.findSection ".data"
  let entry ← ls.entryAddr
  -- Stack top is typically the end of the last RAM region
  let ramSections := ls.sections.filter (fun s => s.flags.write)
  let stackTop := ramSections.foldl (fun acc s => max acc s.endAddr) 0
  pure (stackTop, bss.vma, bss.size, data.lma, data.vma, data.size, entry)

/-- Generate a minimal startup sequence from a linker script. -/
def generateStartup (ls : LinkerScript) : Option (List StartupAction) := do
  let (stackTop, bssBase, bssSize, dataLMA, dataVMA, dataSize, entry) ←
    extractStartupParams ls
  pure (minimalStartupActions stackTop bssBase bssSize dataLMA dataVMA dataSize entry)

end Radix.BareMetal.Startup
