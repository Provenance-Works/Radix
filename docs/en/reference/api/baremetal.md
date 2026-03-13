# BareMetal Module API Reference

> **Module**: `Radix.BareMetal`
> **Source**: `Radix/BareMetal/`

## Overview

Models bare-metal (no-OS) execution environments for embedded systems. Provides platform definitions, memory region modeling, ELF linker script abstractions, startup sequence validation, and GC-free constraint checking. This is a **pure model** — no actual hardware interaction. All definitions are Lean 4 data structures and functions used for verification and reasoning.

## Target Platforms (`BareMetal.Spec`)

```lean
inductive Platform where
  | x86_64
  | aarch64
  | riscv64
  deriving DecidableEq, Repr

def Platform.wordBits : Platform → Nat     -- 64 for all platforms
def Platform.naturalAlign : Platform → Nat  -- 8 bytes for all platforms
```

## Memory Region Model (`BareMetal.Spec`)

### Region Kinds

```lean
inductive RegionKind where
  | flash     -- Read-only executable code and constant data (ROM)
  | ram       -- Read-write data
  | mmio      -- Memory-mapped I/O registers (accesses have side effects)
  | reserved  -- Unmapped; accesses are undefined
  deriving DecidableEq, Repr
```

### Permissions

```lean
structure Permissions where
  read    : Bool
  write   : Bool
  execute : Bool
  deriving DecidableEq, Repr

-- Standard permission sets
def Permissions.readOnly : Permissions      -- r--
def Permissions.readWrite : Permissions     -- rw-
def Permissions.readExecute : Permissions   -- r-x
def Permissions.none : Permissions          -- ---
```

### Memory Region

```lean
structure MemRegion where
  name        : String       -- e.g., ".text", "SRAM1", "UART0"
  baseAddr    : Nat
  size        : Nat
  kind        : RegionKind
  permissions : Permissions
  deriving Repr

def MemRegion.endAddr (r : MemRegion) : Nat            -- baseAddr + size
def MemRegion.overlaps (a b : MemRegion) : Prop         -- Decidable
def MemRegion.disjoint (a b : MemRegion) : Prop         -- Decidable
def MemRegion.contains (r : MemRegion) (addr : Nat) : Prop  -- Decidable
```

### Memory Map

```lean
structure MemoryMap where
  regions  : List MemRegion
  platform : Platform
  deriving Repr

def MemoryMap.isNonOverlapping (mm : MemoryMap) : Prop
def MemoryMap.allNonEmpty (mm : MemoryMap) : Prop
def MemoryMap.isValid (mm : MemoryMap) : Prop      -- isNonOverlapping ∧ allNonEmpty
def MemoryMap.findRegion (mm : MemoryMap) (addr : Nat) : Option MemRegion
def MemoryMap.totalSize (mm : MemoryMap) : Nat
```

## Boot Sequence (`BareMetal.Spec`)

### Startup Phases

```lean
inductive StartupPhase where
  | reset         -- Processor reset, minimal hardware init
  | earlyInit     -- Stack pointer, BSS, data sections
  | platformInit  -- Clock, peripherals, interrupts
  | runtimeInit   -- Heap (if any), global constructors
  | appEntry      -- Application entry (main)
  deriving DecidableEq, Repr

def StartupPhase.order : StartupPhase → Nat   -- 0..4
def StartupPhase.precedes (a b : StartupPhase) : Bool
```

### Startup Steps and Sequences

```lean
structure StartupStep where
  source : StartupPhase
  target : StartupPhase

def StartupStep.isValid (s : StartupStep) : Prop   -- target.order = source.order + 1

structure StartupSequence where
  steps : List StartupStep

def StartupSequence.isComplete (seq : StartupSequence) : Prop
  -- 4 steps, all valid, starts at reset, ends at appEntry
```

### Boot Invariants

```lean
structure BootInvariant where
  stackAligned    : Nat → Platform → Prop   -- SP % naturalAlign = 0
  stackInRAM      : Nat → MemoryMap → Prop  -- SP within a RAM region
  bssZeroed       : Prop
  dataInitialized : Prop
```

### Allocation Strategies

```lean
inductive AllocStrategy where
  | static  -- Compile-time allocation (global/static)
  | stack   -- Function-local allocation
  | arena   -- Arena/pool allocation (caller manages lifetime)
  | none    -- Pure computation, no allocation
  deriving DecidableEq, Repr

def AllocStrategy.isGCFree : AllocStrategy → Bool  -- true for all variants

structure AllocProfile where
  name     : String
  strategy : AllocStrategy
  maxStack : Option Nat
```

## GC-Free Constraints (`BareMetal.GCFree`)

### Lifetime Classification

```lean
inductive Lifetime where
  | static      -- Entire program duration
  | stack       -- Enclosing function call
  | arena       -- Enclosing arena scope
  | compileTime -- Compile-time constant
  deriving DecidableEq, Repr

def Lifetime.isBounded : Lifetime → Bool  -- true for all variants
```

### Forbidden Patterns

```lean
inductive ForbiddenPattern where
  | unboundedAlloc   -- Arbitrary heap growth
  | mutableCapture   -- Closure capture of mutable references
  | dynamicDispatch  -- Object polymorphism
  | lazyThunk        -- Lazy thunk creation
  | heapException    -- Heap-allocated exception objects
  deriving DecidableEq, Repr

def ForbiddenPattern.description : ForbiddenPattern → String
```

### Constraint Checking

```lean
structure GCFreeConstraint where
  maxStackBytes     : Nat
  allowedStrategies : List AllocStrategy
  forbidden         : List ForbiddenPattern

def GCFreeConstraint.default : GCFreeConstraint
  -- maxStack=4096, strategies=[static,stack,none], all patterns forbidden

def GCFreeConstraint.withArena (maxStack : Nat := 8192) : GCFreeConstraint
  -- Adds arena to allowed strategies

inductive CheckResult where
  | pass
  | failStrategy (name : String) (strategy : AllocStrategy)
  | failStackOverflow (name : String) (used limit : Nat)

def checkProfile (constraint : GCFreeConstraint) (profile : AllocProfile) : Bool
def checkProfileDetailed (constraint : GCFreeConstraint) (profile : AllocProfile) : CheckResult
def checkModule (constraint : GCFreeConstraint) (profiles : List AllocProfile) : List CheckResult
```

### Stack Usage Model

```lean
structure StackFrame where
  name       : String
  localBytes : Nat
  savedRegs  : Nat
  padding    : Nat

def StackFrame.totalSize (f : StackFrame) : Nat  -- localBytes + savedRegs + padding
def worstCaseStackDepth (frames : List StackFrame) : Nat
```

## Linker Script Model (`BareMetal.Linker`)

### Section Flags

```lean
structure SectionFlags where
  write : Bool
  alloc : Bool
  exec  : Bool
  deriving DecidableEq, Repr

-- Standard flag sets
def SectionFlags.text : SectionFlags      -- alloc + exec
def SectionFlags.rodata : SectionFlags    -- alloc only
def SectionFlags.data : SectionFlags      -- alloc + write
def SectionFlags.bss : SectionFlags       -- alloc + write
```

### Section

```lean
structure Section where
  name  : String     -- e.g., ".text", ".data", ".bss"
  lma   : Nat        -- Load Memory Address (where loaded from)
  vma   : Nat        -- Virtual Memory Address (runtime location)
  size  : Nat
  flags : SectionFlags

def Section.endAddr (s : Section) : Nat   -- vma + size
def Section.overlaps (a b : Section) : Prop
def Section.disjoint (a b : Section) : Prop
```

### Symbol

```lean
structure Symbol where
  name        : String
  addr        : Nat
  sectionName : String
```

### Linker Script

```lean
structure LinkerScript where
  sections   : List Section
  symbols    : List Symbol
  entryPoint : String
  platform   : Platform

def LinkerScript.findSection (ls : LinkerScript) (name : String) : Option Section
def LinkerScript.findSymbol (ls : LinkerScript) (name : String) : Option Symbol
def LinkerScript.entryAddr (ls : LinkerScript) : Option Nat
def LinkerScript.isNonOverlapping (ls : LinkerScript) : Prop
def LinkerScript.allNonEmpty (ls : LinkerScript) : Prop
def LinkerScript.isValid (ls : LinkerScript) : Prop
  -- isNonOverlapping ∧ allNonEmpty ∧ entryAddr.isSome
def LinkerScript.totalSize (ls : LinkerScript) : Nat
```

### Address Alignment

```lean
def alignUp (addr align : Nat) : Nat      -- Round up to next multiple
def alignDown (addr align : Nat) : Nat    -- Round down to previous multiple
def isAligned (addr align : Nat) : Bool    -- addr % align == 0
```

### Memory Map Construction

```lean
def sectionToRegion (s : Section) : MemRegion   -- exec→flash, write→ram, else flash
def toMemoryMap (ls : LinkerScript) : MemoryMap
```

## Startup Sequence (`BareMetal.Startup`)

### Startup Actions

```lean
inductive StartupAction where
  | setStackPointer (addr : Nat)
  | zeroBSS (baseAddr size : Nat)
  | copyData (lma vma size : Nat)
  | setVectorTable (addr : Nat)
  | setInterrupts (enable : Bool)
  | configClock
  | callConstructors
  | jumpToEntry (addr : Nat)
  deriving Repr
```

### Startup Templates

```lean
def minimalStartupActions (stackTop bssBase bssSize dataLMA dataVMA dataSize entry : Nat)
    : List StartupAction
  -- [disableIRQ, setSP, zeroBSS, copyData, enableIRQ, jumpToEntry]

def fullStartupActions (stackTop bssBase bssSize dataLMA dataVMA dataSize vectorTable entry : Nat)
    : List StartupAction
  -- [disableIRQ, setSP, setVectorTable, configClock, zeroBSS, copyData,
  --  callConstructors, enableIRQ, jumpToEntry]
```

### Startup Validation

```lean
def startsWithInterruptsDisabled (actions : List StartupAction) : Bool
def setsStackBeforeUse (actions : List StartupAction) : Bool
def endsWithJump (actions : List StartupAction) : Bool
def isValidStartupSequence (actions : List StartupAction) : Bool
  -- length > 0 ∧ startsWithInterruptsDisabled ∧ setsStackBeforeUse ∧ endsWithJump
```

### Generation from Linker Script

```lean
def extractStartupParams (ls : LinkerScript)
    : Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat)
  -- (stackTop, bssBase, bssSize, dataLMA, dataVMA, dataSize, entry)

def generateStartup (ls : LinkerScript) : Option (List StartupAction)
```

## Proofs (`BareMetal.Lemmas`)

### Memory Region Properties
- `MemRegion.disjoint_comm`: disjoint is symmetric
- `MemRegion.disjoint_of_endAddr_le`: sufficient condition for disjointness
- `MemRegion.not_contains_of_disjoint`: disjoint regions don't share addresses
- `MemRegion.endAddr_eq`: `endAddr = baseAddr + size`

### Memory Map Properties
- `MemoryMap.empty_isValid`: empty memory map is valid
- `MemoryMap.empty_totalSize`: empty memory map has size 0
- `MemoryMap.empty_findRegion`: empty map finds nothing

### Section and Linker Script Properties
- `Section.disjoint_comm`: section disjointness is symmetric
- `LinkerScript.empty_isNonOverlapping`: empty linker script is non-overlapping
- `LinkerScript.empty_totalSize`: empty linker script has total size 0

### Alignment Properties
- `alignUp_ge`: `alignUp addr align ≥ addr`
- `alignDown_le`: `alignDown addr align ≤ addr`
- `alignUp_zero`: `alignUp 0 align = 0`
- `alignDown_zero`: `alignDown 0 align = 0`
- `isAligned_zero`: `isAligned 0 align = true`

### GC-Free Properties
- `AllocStrategy.all_isGCFree`: all strategies are GC-free
- `GCFreeConstraint.default_allows_static`: default allows static
- `GCFreeConstraint.default_allows_stack`: default allows stack
- `GCFreeConstraint.default_forbids_arena`: default forbids arena
- `GCFreeConstraint.withArena_allows_arena`: withArena allows arena
- `checkModule_empty`: empty module passes

### Stack Frame Properties
- `StackFrame.totalSize_eq`: `totalSize = localBytes + savedRegs + padding`
- `worstCaseStackDepth_nil`: empty list has depth 0
- `worstCaseStackDepth_cons`: `depth(f::fs) = depth(fs) + f.totalSize`

### Startup Properties
- `minimalStartup_startsWithInterruptsDisabled`: minimal starts with IRQ off
- `minimalStartup_endsWithJump`: minimal ends with jump
- `minimalStartup_isValid`: minimal startup is valid
- `fullStartup_isValid`: full startup is valid

### Platform Properties
- `Platform.wordBits_pos`: word bits > 0
- `Platform.naturalAlign_pos`: natural alignment > 0
- `StartupPhase.reset_precedes_appEntry`: reset comes before appEntry
- `StartupPhase.order_injective`: phase order is injective

## Trusted Assumptions (`BareMetal.Assumptions`)

All axioms are `Prop`-typed, prefixed with `trust_`, and cite hardware specification references:

| Axiom | Reference | Asserts |
|-------|-----------|---------|
| `trust_reset_entry` | ARM D1.6.1, RISC-V §3.4 | Processor starts at designated reset vector |
| `trust_static_allocation_stable` | System V ABI, ELF §2-2 | Static memory allocations are not relocated at runtime |
| `trust_mmio_volatile` | ARM B2.1, RISC-V PMA | MMIO accesses produce exactly one bus transaction, not reordered |
| `trust_bss_zeroed` | System V ABI, Process Init | BSS region reads as zero after startup initialization |
| `trust_stack_grows_down` | AMD64 ABI §3.2.2, AAPCS64 §6.2.2 | Stack pointer is decremented before push |

## Related Documents

- [Concurrency](concurrency.md) — Atomic operations model
- [Memory](memory.md) — Abstract memory model
- [Architecture: Components](../../architecture/components.md#baremetal) — Module overview
