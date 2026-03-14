import Radix.BareMetal
import Radix.Memory

/-!
# Example: Embedded Firmware Image Builder

Models a firmware image for an ARM Cortex-M4 microcontroller
(STM32F407 style). Demonstrates:

- Memory map definition with flash, SRAM, peripherals
- Linker script modeling with ELF sections
- Startup sequence generation and validation
- GC-free constraint checking for bare-metal code
- Stack usage analysis
- Memory layout with alignment
-/

namespace Examples.FirmwareImage

open Radix.BareMetal.Spec
open Radix.BareMetal.Linker
open Radix.BareMetal.Startup
open Radix.BareMetal.GCFree
open Radix.Memory

/-- Right-pad a string with spaces to the given width. -/
private def rightpad (s : String) (width : Nat) : String :=
  if s.length >= width then s
  else s ++ String.ofList (List.replicate (width - s.length) ' ')

/-- Format an address as hex. -/
private def hexAddr (n : Nat) : String :=
  let digits := Nat.toDigits 16 n
  let padded := List.replicate (8 - digits.length) '0' ++ digits
  "0x" ++ String.ofList padded

/-- Format a size in human-readable form. -/
private def fmtSize (bytes : Nat) : String :=
  if bytes >= 1024 * 1024 then s!"{bytes / (1024 * 1024)}MB"
  else if bytes >= 1024 then s!"{bytes / 1024}KB"
  else s!"{bytes}B"

def run : IO Unit := do
  IO.println "=== Embedded Firmware Image Builder ==="
  IO.println ""

  -- 1. Memory Map (STM32F407-style Cortex-M4)
  IO.println "  1. Memory Map (STM32F407)"
  IO.println "  ---"

  let flashRegion : MemRegion :=
    { name := "FLASH", baseAddr := 0x08000000, size := 1024 * 1024
      kind := .flash, permissions := .readExecute }
  let sramRegion : MemRegion :=
    { name := "SRAM", baseAddr := 0x20000000, size := 192 * 1024
      kind := .ram, permissions := .readWrite }
  let ccmRegion : MemRegion :=
    { name := "CCM_RAM", baseAddr := 0x10000000, size := 64 * 1024
      kind := .ram, permissions := .readWrite }
  let periphRegion : MemRegion :=
    { name := "PERIPH", baseAddr := 0x40000000, size := 0x20000000
      kind := .mmio, permissions := .readWrite }

  let memMap : MemoryMap :=
    { regions := [flashRegion, sramRegion, ccmRegion, periphRegion]
      platform := .aarch64 }

  IO.println "    Region     | Base       | Size     | Kind"
  IO.println "    -----------|------------|----------|------"
  for r in memMap.regions do
    IO.println s!"    {rightpad r.name 11}| {hexAddr r.baseAddr} | {rightpad (fmtSize r.size) 9}| {reprStr r.kind}"
  IO.println s!"    Total mapped: {fmtSize memMap.totalSize}"
  IO.println ""

  -- 2. Linker Script
  IO.println "  2. Linker Script"
  IO.println "  ---"

  let ls : LinkerScript :=
    { sections := [
        { name := ".isr_vector", lma := 0x08000000, vma := 0x08000000
          size := 428, flags := .rodata }
      , { name := ".text", lma := 0x080001AC, vma := 0x080001AC
          size := 32768, flags := .text }
      , { name := ".rodata", lma := 0x080081AC, vma := 0x080081AC
          size := 4096, flags := .rodata }
      , { name := ".data", lma := 0x080091AC, vma := 0x20000000
          size := 512, flags := .data }
      , { name := ".bss", lma := 0, vma := 0x20000200
          size := 8192, flags := .bss }
      ]
      symbols := [
        { name := "Reset_Handler", addr := 0x080001AD, sectionName := ".text" }
      , { name := "__stack_top", addr := 0x20030000, sectionName := "" }
      , { name := "_sidata", addr := 0x080091AC, sectionName := ".data" }
      , { name := "_sdata", addr := 0x20000000, sectionName := ".data" }
      , { name := "_edata", addr := 0x20000200, sectionName := ".data" }
      , { name := "_sbss", addr := 0x20000200, sectionName := ".bss" }
      , { name := "_ebss", addr := 0x20002200, sectionName := ".bss" }
      ]
      entryPoint := "Reset_Handler"
      platform := .aarch64 }

  IO.println "    Section      | VMA        | LMA        | Size"
  IO.println "    -------------|------------|------------|------"
  for s in ls.sections do
    IO.println s!"    {rightpad s.name 13}| {hexAddr s.vma} | {hexAddr s.lma} | {fmtSize s.size}"
  IO.println s!"    Total output: {fmtSize ls.totalSize}"

  match ls.entryAddr with
  | some addr => IO.println s!"    Entry point: {hexAddr addr}"
  | none => IO.println "    Entry point: NOT FOUND"

  -- Flash utilization
  let flashUsed := ls.totalSize
  let flashTotal := flashRegion.size
  let pct := flashUsed * 100 / flashTotal
  IO.println s!"    Flash utilization: {fmtSize flashUsed} / {fmtSize flashTotal} ({pct}%)"
  IO.println ""

  -- 3. Startup Sequence
  IO.println "  3. Startup Sequence"
  IO.println "  ---"

  match generateStartup ls with
  | some actions =>
    IO.println s!"    Generated {actions.length} startup actions:"
    let mut idx := 1
    for action in actions do
      IO.println s!"      [{idx}] {reprStr action}"
      idx := idx + 1
    let valid := isValidStartupSequence actions
    IO.println s!"    Valid sequence: {valid}"
  | none =>
    IO.println "    Could not generate startup sequence"
  IO.println ""

  -- 4. GC-Free Analysis
  IO.println "  4. GC-Free Constraint Analysis"
  IO.println "  ---"

  let constraint := GCFreeConstraint.default
  IO.println s!"    Max stack: {constraint.maxStackBytes} bytes"
  IO.println s!"    Allowed strategies: {reprStr constraint.allowedStrategies}"

  -- Define function profiles for our firmware
  let profiles : List AllocProfile := [
    { name := "Reset_Handler", strategy := .none, maxStack := some 0 }
  , { name := "SystemInit", strategy := .stack, maxStack := some 128 }
  , { name := "main", strategy := .stack, maxStack := some 512 }
  , { name := "UART_IRQHandler", strategy := .stack, maxStack := some 256 }
  , { name := "processData", strategy := .stack, maxStack := some 2048 }
  , { name := "idleTask", strategy := .static, maxStack := some 64 }
  ]

  IO.println s!"    Checking {profiles.length} function profiles..."
  let failures := checkModule constraint profiles
  if failures.isEmpty then
    IO.println "    ✓ All profiles pass GC-free constraints"
  else
    for f in failures do
      IO.println s!"    ✗ {reprStr f}"

  -- Demonstrate that non-stack strategies can also be flagged
  -- (AllocStrategy has: static, stack, arena, none — all are GC-free safe)
  let arenaProfile : AllocProfile :=
    { name := "arenaAlloc", strategy := .arena, maxStack := some 16384 }
  let arenaResult := checkProfileDetailed constraint arenaProfile
  IO.println s!"    Arena profile (16KB stack): {reprStr arenaResult}"
  IO.println ""

  -- 5. Stack Analysis
  IO.println "  5. Stack Depth Analysis"
  IO.println "  ---"

  -- Worst-case call chain: main → processData → UART_IRQHandler
  let callChain : List StackFrame := [
    { name := "main", localBytes := 64, savedRegs := 32, padding := 0 }
  , { name := "processData", localBytes := 256, savedRegs := 48, padding := 0 }
  , { name := "UART_IRQHandler", localBytes := 128, savedRegs := 64, padding := 0 }
  ]

  IO.println "    Worst-case call chain:"
  for frame in callChain do
    IO.println s!"      {frame.name}: {frame.totalSize} bytes (local={frame.localBytes}, regs={frame.savedRegs})"

  let depth := worstCaseStackDepth callChain
  IO.println s!"    Total stack depth: {depth} bytes"
  IO.println s!"    Stack budget: {constraint.maxStackBytes} bytes"
  IO.println s!"    Within budget: {decide (depth ≤ constraint.maxStackBytes)}"
  IO.println ""

  -- 6. Address Alignment
  IO.println "  6. Address Alignment"
  IO.println "  ---"

  let testAddrs := [(0x1001, 16), (0x2004, 4), (0x3000, 1024), (0x1234, 256)]
  for (addr, align) in testAddrs do
    let up := alignUp addr align
    let down := alignDown addr align
    let aligned := isAligned addr align
    IO.println s!"    {hexAddr addr} align {align}: up={hexAddr up}, down={hexAddr down}, aligned={aligned}"

  -- 7. Memory Layout for structured data
  IO.println ""
  IO.println "  7. Sensor Data Layout"
  IO.println "  ---"

  -- Build a packed sensor data layout:
  -- timestamp: u32 (4 bytes), sensor_id: u16 (2 bytes), value: u32 (4 bytes), flags: u8 (1 byte)
  let layout := LayoutDesc.empty
    |>.appendField "timestamp" 4
    |>.appendField "sensor_id" 2
    |>.appendField "value" 4
    |>.appendField "flags" 1

  IO.println s!"    Fields: {layout.fields.length}"
  IO.println s!"    Total size: {layout.totalSize} bytes"
  for f in layout.fields do
    IO.println s!"      {f.name}: offset={f.offset}, size={f.size}"
  IO.println s!"    Non-overlapping: {layout.isNonOverlapping}"
  IO.println s!"    All fields fit: {layout.allFieldsFit}"

  -- Aligned layout (4-byte alignment for each field)
  let alignedLayout := LayoutDesc.empty
    |>.appendAligned "timestamp" 4 4 (by omega)
    |>.appendAligned "sensor_id" 2 2 (by omega)
    |>.appendAligned "value" 4 4 (by omega)
    |>.appendAligned "flags" 1 1 (by omega)

  IO.println ""
  IO.println "    Aligned layout:"
  IO.println s!"    Total size: {alignedLayout.totalSize} bytes"
  for f in alignedLayout.fields do
    IO.println s!"      {f.name}: offset={f.offset}, size={f.size}"
  IO.println ""

end Examples.FirmwareImage
