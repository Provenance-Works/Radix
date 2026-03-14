import tests.ComprehensiveTests.Framework
import Radix.BareMetal.Linker

/-!
# BareMetal Linker Tests
## Spec References
- P5-02: Section, LinkerScript, alignment, sectionToRegion, toMemoryMap
-/

open ComprehensiveTests
open Radix.BareMetal.Spec
open Radix.BareMetal.Linker

def runBareMetalLinkerTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    BareMetal linker tests..."

  -- ## SectionFlags standard sets
  let tf := SectionFlags.text
  assert (tf.write == false && tf.alloc == true && tf.exec == true) "text flags"

  let rf := SectionFlags.rodata
  assert (rf.write == false && rf.alloc == true && rf.exec == false) "rodata flags"

  let df := SectionFlags.data
  assert (df.write == true && df.alloc == true && df.exec == false) "data flags"

  let bf := SectionFlags.bss
  assert (bf.write == true && bf.alloc == true && bf.exec == false) "bss flags"

  -- BEq
  assert (SectionFlags.text == SectionFlags.text) "flags self-eq"
  assert (!(SectionFlags.text == SectionFlags.data)) "flags neq"

  -- ## Section endAddr
  let textSect : Section := ⟨".text", 0x08000000, 0x08000000, 0x10000, .text⟩
  assert (textSect.endAddr == 0x08010000) "section endAddr"

  -- ## Section disjoint/overlaps
  let dataSect : Section := ⟨".data", 0x08010000, 0x20000000, 0x2000, .data⟩
  let bssSect  : Section := ⟨".bss",  0x20002000, 0x20002000, 0x1000, .bss⟩

  -- .text and .data: .text ends at 0x08010000, .data VMA at 0x20000000 -> disjoint
  assert (Decidable.decide (Section.disjoint textSect dataSect) == true)
    "text/data disjoint"

  -- .data and .bss: .data VMA at 0x20000000, size 0x2000 -> endAddr 0x20002000
  -- .bss VMA at 0x20002000 -> adjacent = disjoint
  assert (Decidable.decide (Section.disjoint dataSect bssSect) == true)
    "data/bss disjoint"

  -- Self overlaps
  assert (Decidable.decide (Section.overlaps textSect textSect) == true)
    "self overlaps"

  -- ## Symbol
  let sym := Symbol.mk "_start" 0x08000100 ".text"
  assert (sym.name == "_start") "symbol name"
  assert (sym.addr == 0x08000100) "symbol addr"
  assert (sym.sectionName == ".text") "symbol section"

  -- ## LinkerScript construction
  let ls : LinkerScript := {
    sections   := [textSect, dataSect, bssSect]
    symbols    := [sym, ⟨"_edata", 0x20002000, ".data"⟩]
    entryPoint := "_start"
    platform   := .aarch64
  }

  assert (ls.sections.length == 3) "ls sections count"
  assert (ls.symbols.length == 2) "ls symbols count"

  -- ## LinkerScript.findSection
  match ls.findSection ".text" with
  | some s => assert (s.size == 0x10000) "find .text"
  | none => assert false "should find .text"

  match ls.findSection ".data" with
  | some s => assert (s.size == 0x2000) "find .data"
  | none => assert false "should find .data"

  match ls.findSection ".heap" with
  | some _ => assert false "should not find .heap"
  | none => assert true "no .heap"

  -- ## LinkerScript.findSymbol
  match ls.findSymbol "_start" with
  | some s => assert (s.addr == 0x08000100) "find _start"
  | none => assert false "should find _start"

  match ls.findSymbol "_edata" with
  | some s => assert (s.addr == 0x20002000) "find _edata"
  | none => assert false "should find _edata"

  match ls.findSymbol "nonexistent" with
  | some _ => assert false "should not find nonexistent"
  | none => assert true "no nonexistent sym"

  -- ## LinkerScript.entryAddr
  match ls.entryAddr with
  | some addr => assert (addr == 0x08000100) "entryAddr"
  | none => assert false "entryAddr should resolve"

  -- Script with no matching entry
  let lsBadEntry : LinkerScript := {
    sections := [textSect], symbols := [], entryPoint := "missing", platform := .x86_64
  }
  match lsBadEntry.entryAddr with
  | some _ => assert false "bad entry should be none"
  | none => assert true "bad entry = none"

  -- ## LinkerScript.totalSize
  assert (ls.totalSize == 0x10000 + 0x2000 + 0x1000) "linker totalSize"

  -- ## alignUp
  assert (alignUp 0 4 == 0) "alignUp 0 to 4"
  assert (alignUp 1 4 == 4) "alignUp 1 to 4"
  assert (alignUp 3 4 == 4) "alignUp 3 to 4"
  assert (alignUp 4 4 == 4) "alignUp 4 to 4"
  assert (alignUp 5 4 == 8) "alignUp 5 to 4"
  assert (alignUp 7 8 == 8) "alignUp 7 to 8"
  assert (alignUp 8 8 == 8) "alignUp 8 to 8"
  assert (alignUp 9 8 == 16) "alignUp 9 to 8"
  assert (alignUp 0 1 == 0) "alignUp to 1"
  assert (alignUp 100 1 == 100) "alignUp 100 to 1"
  assert (alignUp 100 0 == 100) "alignUp align 0"

  -- ## alignDown
  assert (alignDown 0 4 == 0) "alignDown 0 to 4"
  assert (alignDown 1 4 == 0) "alignDown 1 to 4"
  assert (alignDown 3 4 == 0) "alignDown 3 to 4"
  assert (alignDown 4 4 == 4) "alignDown 4 to 4"
  assert (alignDown 5 4 == 4) "alignDown 5 to 4"
  assert (alignDown 7 8 == 0) "alignDown 7 to 8"
  assert (alignDown 8 8 == 8) "alignDown 8 to 8"
  assert (alignDown 15 8 == 8) "alignDown 15 to 8"
  assert (alignDown 100 0 == 100) "alignDown align 0"

  -- ## isAligned
  assert (isAligned 0 4 == true) "isAligned 0 4"
  assert (isAligned 4 4 == true) "isAligned 4 4"
  assert (isAligned 8 4 == true) "isAligned 8 4"
  assert (isAligned 1 4 == false) "isAligned 1 4"
  assert (isAligned 3 4 == false) "isAligned 3 4"
  assert (isAligned 16 8 == true) "isAligned 16 8"
  assert (isAligned 15 8 == false) "isAligned 15 8"
  assert (isAligned 0 0 == true) "isAligned 0 0"
  assert (isAligned 42 0 == true) "isAligned 42 0"

  -- ## Alignment properties
  -- alignUp is >= addr
  for addr in [0, 1, 2, 3, 4, 5, 6, 7, 8, 15, 16, 100, 255, 256, 1023, 1024] do
    for align_ in [1, 2, 4, 8, 16, 32, 64, 128, 256] do
      let up := alignUp addr align_
      assert (up ≥ addr) "alignUp >= addr"
      assert (isAligned up align_ == true) "alignUp is aligned"
      let down := alignDown addr align_
      assert (down ≤ addr) "alignDown <= addr"
      assert (isAligned down align_ == true) "alignDown is aligned"

  -- ## sectionToRegion
  let textRegion := sectionToRegion textSect
  assert (textRegion.name == ".text") "sectionToRegion name"
  assert (textRegion.baseAddr == 0x08000000) "sectionToRegion baseAddr"
  assert (textRegion.size == 0x10000) "sectionToRegion size"
  assert (textRegion.kind == .flash) "sectionToRegion exec = flash"
  assert (textRegion.permissions.execute == true) "sectionToRegion exec perm"

  let dataRegion := sectionToRegion dataSect
  assert (dataRegion.kind == .ram) "sectionToRegion write = ram"
  assert (dataRegion.permissions.write == true) "sectionToRegion write perm"

  -- ## toMemoryMap
  let mm := toMemoryMap ls
  assert (mm.regions.length == 3) "toMemoryMap regions"
  assert (mm.platform == .aarch64) "toMemoryMap platform"
  assert (mm.totalSize == ls.totalSize) "toMemoryMap totalSize"

  c.get
