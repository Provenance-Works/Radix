/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.BareMetal.Spec

/-!
# Linker Script Model (Layer 2)

This module models linker script concepts for bare-metal targets:

- ELF section definitions (.text, .data, .bss, .rodata)
- Symbol resolution model
- Memory map construction from section layout
- Address alignment operations

## Architecture

This is a **Layer 2 (Implementation)** module.
- Models linker script semantics as pure data structures.
- No actual ELF parsing or linking (pure Lean 4 model).

## References

- P5-02: Linker script integration
- System V ABI, Tool Interface Standard (TIS) ELF Specification
- GNU ld manual, Section 3 (Linker Scripts)
-/

set_option autoImplicit false

namespace Radix.BareMetal.Linker

open Radix.BareMetal.Spec

/-! ## Section Flags -/

/-- ELF section flags. -/
structure SectionFlags where
  /-- Section contains writable data. -/
  write   : Bool
  /-- Section occupies memory during execution. -/
  alloc   : Bool
  /-- Section contains executable machine instructions. -/
  exec    : Bool
  deriving DecidableEq, Repr

/-- Standard section flag sets. -/
def SectionFlags.text : SectionFlags :=
  { write := false, alloc := true, exec := true }

def SectionFlags.rodata : SectionFlags :=
  { write := false, alloc := true, exec := false }

def SectionFlags.data : SectionFlags :=
  { write := true, alloc := true, exec := false }

def SectionFlags.bss : SectionFlags :=
  { write := true, alloc := true, exec := false }

/-! ## Section Model -/

/-- A linker section with name, address, size, and flags. -/
structure Section where
  /-- Section name (e.g., ".text", ".data", ".bss"). -/
  name    : String
  /-- Load address (LMA - where the section is loaded from). -/
  lma     : Nat
  /-- Virtual address (VMA - where the section resides at runtime). -/
  vma     : Nat
  /-- Size in bytes. -/
  size    : Nat
  /-- Section flags. -/
  flags   : SectionFlags
  deriving Repr

/-- End address of a section (VMA + size). -/
def Section.endAddr (s : Section) : Nat :=
  s.vma + s.size

/-- Whether two sections overlap in virtual address space. -/
def Section.overlaps (a b : Section) : Prop :=
  a.vma < b.endAddr ∧ b.vma < a.endAddr

instance (a b : Section) : Decidable (Section.overlaps a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether two sections are disjoint in virtual address space. -/
def Section.disjoint (a b : Section) : Prop :=
  a.endAddr ≤ b.vma ∨ b.endAddr ≤ a.vma

instance (a b : Section) : Decidable (Section.disjoint a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-! ## Symbol Model -/

/-- A linker symbol with name and address. -/
structure Symbol where
  /-- Symbol name. -/
  name       : String
  /-- Symbol address. -/
  addr       : Nat
  /-- Section name the symbol belongs to. -/
  sectionName : String
  deriving Repr

/-! ## Linker Script Model -/

/-- A linker script: a list of sections, symbols, and entry point. -/
structure LinkerScript where
  /-- Output sections. -/
  sections   : List Section
  /-- Exported symbols. -/
  symbols    : List Symbol
  /-- Entry point symbol name. -/
  entryPoint : String
  /-- Target platform. -/
  platform   : Platform
  deriving Repr

/-- Find a section by name. -/
def LinkerScript.findSection (ls : LinkerScript) (name : String) :
    Option Section :=
  ls.sections.find? (fun s => s.name == name)

/-- Find a symbol by name. -/
def LinkerScript.findSymbol (ls : LinkerScript) (name : String) :
    Option Symbol :=
  ls.symbols.find? (fun s => s.name == name)

/-- Resolve the entry point address. -/
def LinkerScript.entryAddr (ls : LinkerScript) : Option Nat :=
  (ls.findSymbol ls.entryPoint).map Symbol.addr

/-- All sections are pairwise disjoint (no overlapping addresses). -/
def LinkerScript.isNonOverlapping (ls : LinkerScript) : Prop :=
  ∀ (a : Section), a ∈ ls.sections →
  ∀ (b : Section), b ∈ ls.sections →
    a ≠ b → Section.disjoint a b

/-- All sections have positive size. -/
def LinkerScript.allNonEmpty (ls : LinkerScript) : Prop :=
  ∀ (s : Section), s ∈ ls.sections → s.size > 0

/-- A linker script is valid if sections are non-overlapping, non-empty,
    and the entry point is defined. -/
def LinkerScript.isValid (ls : LinkerScript) : Prop :=
  ls.isNonOverlapping
  ∧ ls.allNonEmpty
  ∧ ls.entryAddr.isSome

/-- Total output size across all sections. -/
def LinkerScript.totalSize (ls : LinkerScript) : Nat :=
  ls.sections.foldl (fun acc s => acc + s.size) 0

/-! ## Address Alignment Utilities -/

/-- Align an address up to the nearest multiple of `align`.
    Precondition: `align > 0`. -/
def alignUp (addr align : Nat) : Nat :=
  if align == 0 then addr
  else ((addr + align - 1) / align) * align

/-- Align an address down to the nearest multiple of `align`. -/
def alignDown (addr align : Nat) : Nat :=
  if align == 0 then addr
  else (addr / align) * align

/-- Whether an address is aligned to the given boundary. -/
def isAligned (addr align : Nat) : Bool :=
  if align == 0 then true
  else addr % align == 0

/-! ## Memory Map Construction -/

/-- Convert a linker script section to a memory region for the
    bare-metal memory map. -/
def sectionToRegion (s : Section) : MemRegion :=
  { name        := s.name
    baseAddr    := s.vma
    size        := s.size
    kind        := if s.flags.exec then .flash
                   else if s.flags.write then .ram
                   else .flash
    permissions := { read    := s.flags.alloc
                     write   := s.flags.write
                     execute := s.flags.exec } }

/-- Build a memory map from a linker script. -/
def toMemoryMap (ls : LinkerScript) : MemoryMap :=
  { regions  := ls.sections.map sectionToRegion
    platform := ls.platform }

end Radix.BareMetal.Linker
