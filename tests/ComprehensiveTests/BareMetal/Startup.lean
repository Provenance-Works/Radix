import tests.ComprehensiveTests.Framework
import Radix.BareMetal.Startup

/-!
# BareMetal Startup Tests
## Spec References
- P5-02: StartupAction, minimalStartupActions, validation, generateStartup
-/

open ComprehensiveTests
open Radix.BareMetal.Spec
open Radix.BareMetal.Startup
open Radix.BareMetal.Linker

def runBareMetalStartupTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    BareMetal startup tests..."

  -- ## minimalStartupActions
  let minimal := minimalStartupActions
    0x20010000  -- stackTop
    0x20008000  -- bssBase
    0x1000      -- bssSize
    0x08000000  -- dataLMA
    0x20000000  -- dataVMA
    0x2000      -- dataSize
    0x08000100  -- entry
  assert (minimal.length == 6) "minimal actions 6"
  assert (isValidStartupSequence minimal == true) "minimal is valid"
  assert (startsWithInterruptsDisabled minimal == true) "minimal starts with int off"
  assert (setsStackBeforeUse minimal == true) "minimal SP before use"
  assert (endsWithJump minimal == true) "minimal ends with jump"

  -- ## fullStartupActions
  let full := fullStartupActions
    0x20010000 0x20008000 0x1000
    0x08000000 0x20000000 0x2000
    0x08080000  -- vectorTable
    0x08000100  -- entry
  assert (full.length == 9) "full actions 9"
  assert (isValidStartupSequence full == true) "full is valid"
  assert (startsWithInterruptsDisabled full == true) "full starts disabled"
  assert (endsWithJump full == true) "full ends with jump"

  -- ## Invalid sequences
  assert (isValidStartupSequence [] == false) "empty seq invalid"

  -- Not starting with disableInterrupts
  let badStart := [
    StartupAction.setStackPointer 0x20010000,
    StartupAction.jumpToEntry 0x08000100
  ]
  assert (startsWithInterruptsDisabled badStart == false) "bad start"

  -- Not ending with jump
  let badEnd := [
    StartupAction.setInterrupts false,
    StartupAction.setStackPointer 0x20010000
  ]
  assert (endsWithJump badEnd == false) "bad end"

  -- Stack used before setting
  let badSP := [
    StartupAction.setInterrupts false,
    StartupAction.zeroBSS 0x20008000 0x1000,
    StartupAction.setStackPointer 0x20010000,
    StartupAction.jumpToEntry 0x08000100
  ]
  assert (setsStackBeforeUse badSP == false) "SP after use"

  -- ## generateStartup from LinkerScript
  let textSection : Section := ⟨".text", 0x08000000, 0x08000000, 0x10000, .text⟩
  let dataSection : Section := ⟨".data", 0x08010000, 0x20000000, 0x2000, .data⟩
  let bssSection  : Section := ⟨".bss",  0x20002000, 0x20002000, 0x1000, .bss⟩
  let entrySymbol : Symbol  := ⟨"_start", 0x08000100, ".text"⟩

  let ls : LinkerScript := {
    sections   := [textSection, dataSection, bssSection]
    symbols    := [entrySymbol]
    entryPoint := "_start"
    platform   := .aarch64
  }

  match generateStartup ls with
  | some actions =>
    assert (isValidStartupSequence actions == true) "generated seq valid"
    assert (actions.length == 6) "generated seq length"
  | none => assert false "generateStartup should succeed"

  -- ## LinkerScript findSection
  match ls.findSection ".text" with
  | some s => assert (s.size == 0x10000) "findSection .text"
  | none => assert false "findSection should find .text"

  match ls.findSection ".bss" with
  | some s => assert (s.size == 0x1000) "findSection .bss"
  | none => assert false "findSection should find .bss"

  match ls.findSection ".nonexistent" with
  | some _ => assert false "findSection should not find nonexistent"
  | none => assert true "findSection nonexistent = none"

  -- ## LinkerScript findSymbol
  match ls.findSymbol "_start" with
  | some sym => assert (sym.addr == 0x08000100) "findSymbol _start"
  | none => assert false "findSymbol should find _start"

  -- ## LinkerScript entryAddr
  match ls.entryAddr with
  | some addr => assert (addr == 0x08000100) "entryAddr"
  | none => assert false "entryAddr should resolve"

  -- ## LinkerScript totalSize
  assert (ls.totalSize == 0x10000 + 0x2000 + 0x1000) "ls totalSize"

  -- ## extractStartupParams
  match extractStartupParams ls with
  | some (stackTop, bssBase, bssSize, dataLMA, dataVMA, dataSize, entry) =>
    assert (bssBase == 0x20002000) "params bssBase"
    assert (bssSize == 0x1000) "params bssSize"
    assert (dataLMA == 0x08010000) "params dataLMA"
    assert (dataVMA == 0x20000000) "params dataVMA"
    assert (dataSize == 0x2000) "params dataSize"
    assert (entry == 0x08000100) "params entry"
    -- stackTop should be max endAddr of writable sections
    assert (stackTop ≥ 0x20003000) "params stackTop"
  | none => assert false "extractStartupParams should succeed"

  -- ## Missing sections = generation fails
  let lsNoBSS : LinkerScript := {
    sections   := [textSection, dataSection]
    symbols    := [entrySymbol]
    entryPoint := "_start"
    platform   := .x86_64
  }
  match generateStartup lsNoBSS with
  | some _ => assert false "no BSS should fail startup"
  | none => assert true "missing BSS = none"

  c.get
