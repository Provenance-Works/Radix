/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Bare Metal Specification (Layer 3)

This module defines the formal model for bare-metal environments:

- Memory region kinds (Flash, RAM, MMIO, Reserved)
- Memory map specification with non-overlap invariants
- Boot invariants (stack pointer, entry point, BSS zeroed)
- Startup phase state machine
- GC-free allocation constraints

## Architecture

This is a **Layer 3 (Verified Specification)** module.
- MUST NOT import any Layer 2 or Layer 1 modules.
- Defines the formal contracts for bare-metal subsystems.

## References

- P5-02: Bare metal support
- ARM Architecture Reference Manual, Chapter D1 (AArch64 System Level)
- RISC-V Privileged Specification, Chapter 3 (Machine-Level ISA)
- System V ABI (ELF sections and linking)
-/

set_option autoImplicit false

namespace Radix.BareMetal.Spec

/-! ## Target Platforms -/

/-- Supported bare-metal target architectures. -/
inductive Platform where
  | x86_64
  | aarch64
  | riscv64
  deriving DecidableEq, Repr

/-- The natural word size (in bits) for a platform. -/
def Platform.wordBits : Platform → Nat
  | .x86_64  => 64
  | .aarch64 => 64
  | .riscv64 => 64

/-- The natural alignment (in bytes) for a platform. -/
def Platform.naturalAlign : Platform → Nat
  | .x86_64  => 8
  | .aarch64 => 8
  | .riscv64 => 8

/-! ## Memory Region Model -/

/-- The kind of a memory region in a bare-metal memory map. -/
inductive RegionKind where
  /-- Read-only executable code and constant data (typically Flash/ROM). -/
  | flash
  /-- Read-write data (RAM). -/
  | ram
  /-- Memory-mapped I/O registers. Accesses have side effects. -/
  | mmio
  /-- Reserved or unmapped. Accesses are undefined. -/
  | reserved
  deriving DecidableEq, Repr

/-- Access permissions for a memory region. -/
structure Permissions where
  read    : Bool
  write   : Bool
  execute : Bool
  deriving DecidableEq, Repr

/-- Standard permission sets. -/
def Permissions.readOnly : Permissions :=
  { read := true, write := false, execute := false }

def Permissions.readWrite : Permissions :=
  { read := true, write := true, execute := false }

def Permissions.readExecute : Permissions :=
  { read := true, write := false, execute := true }

def Permissions.none : Permissions :=
  { read := false, write := false, execute := false }

/-- A memory region in the bare-metal memory map. -/
structure MemRegion where
  /-- Human-readable name (e.g., ".text", "SRAM1", "UART0"). -/
  name        : String
  /-- Base address of the region. -/
  baseAddr    : Nat
  /-- Size of the region in bytes. -/
  size        : Nat
  /-- Kind of memory. -/
  kind        : RegionKind
  /-- Access permissions. -/
  permissions : Permissions
  deriving Repr

/-- The end address (exclusive) of a memory region. -/
def MemRegion.endAddr (r : MemRegion) : Nat :=
  r.baseAddr + r.size

/-- Whether two memory regions overlap. -/
def MemRegion.overlaps (a b : MemRegion) : Prop :=
  a.baseAddr < b.endAddr ∧ b.baseAddr < a.endAddr

instance (a b : MemRegion) : Decidable (MemRegion.overlaps a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Whether two memory regions are disjoint (non-overlapping). -/
def MemRegion.disjoint (a b : MemRegion) : Prop :=
  a.endAddr ≤ b.baseAddr ∨ b.endAddr ≤ a.baseAddr

instance (a b : MemRegion) : Decidable (MemRegion.disjoint a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Whether an address falls within a memory region. -/
def MemRegion.contains (r : MemRegion) (addr : Nat) : Prop :=
  r.baseAddr ≤ addr ∧ addr < r.endAddr

instance (r : MemRegion) (addr : Nat) : Decidable (MemRegion.contains r addr) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## Memory Map -/

/-- A bare-metal memory map: a list of non-overlapping memory regions. -/
structure MemoryMap where
  /-- The memory regions. -/
  regions  : List MemRegion
  /-- Target platform. -/
  platform : Platform
  deriving Repr

/-- All regions in a memory map are pairwise disjoint. -/
def MemoryMap.isNonOverlapping (mm : MemoryMap) : Prop :=
  ∀ (a : MemRegion), a ∈ mm.regions →
  ∀ (b : MemRegion), b ∈ mm.regions →
    a ≠ b → MemRegion.disjoint a b

/-- All regions have positive size. -/
def MemoryMap.allNonEmpty (mm : MemoryMap) : Prop :=
  ∀ (r : MemRegion), r ∈ mm.regions → r.size > 0

/-- A memory map is valid if regions are non-overlapping and non-empty. -/
def MemoryMap.isValid (mm : MemoryMap) : Prop :=
  mm.isNonOverlapping ∧ mm.allNonEmpty

/-- Find the region containing a given address. -/
def MemoryMap.findRegion (mm : MemoryMap) (addr : Nat) : Option MemRegion :=
  mm.regions.find? (fun r => decide (MemRegion.contains r addr))

/-- Total mapped bytes across all regions. -/
def MemoryMap.totalSize (mm : MemoryMap) : Nat :=
  mm.regions.foldl (fun acc r => acc + r.size) 0

/-! ## Boot Invariants -/

/-- Startup phases in a bare-metal boot sequence. -/
inductive StartupPhase where
  /-- Processor reset, minimal hardware init. -/
  | reset
  /-- Early init: stack pointer, BSS, data sections. -/
  | earlyInit
  /-- Platform init: clock, peripherals, interrupts. -/
  | platformInit
  /-- Runtime init: heap (if any), global constructors. -/
  | runtimeInit
  /-- Application entry (main). -/
  | appEntry
  deriving DecidableEq, Repr

/-- Phase ordering (earlier phases have smaller numbers). -/
def StartupPhase.order : StartupPhase → Nat
  | .reset        => 0
  | .earlyInit    => 1
  | .platformInit => 2
  | .runtimeInit  => 3
  | .appEntry     => 4

/-- Whether phase `a` precedes phase `b`. -/
def StartupPhase.precedes (a b : StartupPhase) : Bool :=
  a.order < b.order

/-- A startup step: transition from one phase to the next. -/
structure StartupStep where
  source : StartupPhase
  target : StartupPhase
  deriving DecidableEq, Repr

/-- A startup step is valid if `source` immediately precedes `target`. -/
def StartupStep.isValid (s : StartupStep) : Prop :=
  s.target.order = s.source.order + 1

instance (s : StartupStep) : Decidable (StartupStep.isValid s) :=
  inferInstanceAs (Decidable (_ = _))

/-- A startup sequence is a list of steps. -/
structure StartupSequence where
  steps : List StartupStep
  deriving Repr

/-- A startup sequence is valid if:
    1. It starts from reset.
    2. Each step is valid (consecutive phases).
    3. It ends at appEntry. -/
def StartupSequence.isComplete (seq : StartupSequence) : Prop :=
  seq.steps.length = 4
  ∧ (∀ s, s ∈ seq.steps → StartupStep.isValid s)
  ∧ (match seq.steps.head? with
     | some s => s.source = .reset
     | none   => False)
  ∧ (match seq.steps.getLast? with
     | some s => s.target = .appEntry
     | none   => False)

/-! ## Boot Invariants -/

/-- Invariants that must hold at application entry. -/
structure BootInvariant where
  /-- Stack pointer is aligned to platform natural alignment. -/
  stackAligned    : Nat → Platform → Prop := fun sp p =>
    sp % p.naturalAlign = 0
  /-- Stack pointer points within a valid RAM region. -/
  stackInRAM      : Nat → MemoryMap → Prop := fun sp mm =>
    ∃ r, r ∈ mm.regions ∧ r.kind = .ram ∧ MemRegion.contains r sp
  /-- BSS section is zeroed. -/
  bssZeroed       : Prop
  /-- Data section is initialized from Flash. -/
  dataInitialized : Prop

/-! ## GC-Free Constraint Specification -/

/-- Allocation strategies in a GC-free environment. -/
inductive AllocStrategy where
  /-- Static allocation at compile time (global/static variables). -/
  | static
  /-- Stack allocation (function-local variables). -/
  | stack
  /-- Arena/pool allocation (caller manages lifetime). -/
  | arena
  /-- No allocation (pure computation). -/
  | none
  /-- Heap allocation requiring GC or reference counting. -/
  | heap
  deriving DecidableEq, Repr

/-- Whether an allocation strategy is GC-free safe. -/
def AllocStrategy.isGCFree : AllocStrategy → Bool
  | .static => true
  | .stack  => true
  | .arena  => true
  | .none   => true
  | .heap   => false

/-- A function's allocation profile. -/
structure AllocProfile where
  /-- Name of the function. -/
  name     : String
  /-- The allocation strategy used. -/
  strategy : AllocStrategy
  /-- Maximum stack usage in bytes (if known). -/
  maxStack : Option Nat
  deriving Repr

/-- Whether an allocation profile is GC-free compatible. -/
def AllocProfile.isGCFreeCompatible (p : AllocProfile) : Bool :=
  p.strategy.isGCFree

end Radix.BareMetal.Spec
