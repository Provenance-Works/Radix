import tests.ComprehensiveTests.Framework
import Radix.BareMetal.GCFree

/-!
# BareMetal GC-Free Tests
## Spec References
- P5-02: GCFreeConstraint, checkProfile, Lifetime, ForbiddenPattern, StackFrame
-/

open ComprehensiveTests
open Radix.BareMetal.Spec
open Radix.BareMetal.GCFree

def runBareMetalGCFreeTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    BareMetal GC-free tests..."

  -- ## Lifetime.isBounded
  assert (Lifetime.static.isBounded == true) "static bounded"
  assert (Lifetime.stack.isBounded == true) "stack bounded"
  assert (Lifetime.arena.isBounded == true) "arena bounded"
  assert (Lifetime.compileTime.isBounded == true) "compileTime bounded"

  -- ## ForbiddenPattern.description
  assert (ForbiddenPattern.unboundedAlloc.description != "") "unboundedAlloc desc"
  assert (ForbiddenPattern.mutableCapture.description != "") "mutableCapture desc"
  assert (ForbiddenPattern.dynamicDispatch.description != "") "dynamicDispatch desc"
  assert (ForbiddenPattern.lazyThunk.description != "") "lazyThunk desc"
  assert (ForbiddenPattern.heapException.description != "") "heapException desc"

  -- Descriptions are distinct
  let descs := [
    ForbiddenPattern.unboundedAlloc.description,
    ForbiddenPattern.mutableCapture.description,
    ForbiddenPattern.dynamicDispatch.description,
    ForbiddenPattern.lazyThunk.description,
    ForbiddenPattern.heapException.description
  ]
  for i in [:descs.length] do
    for j in [:descs.length] do
      if i != j then
        assert (descs[i]! != descs[j]!) "descriptions distinct"

  -- ## GCFreeConstraint.default
  let dflt := GCFreeConstraint.default
  assert (dflt.maxStackBytes == 4096) "default maxStack"
  assert (dflt.allowedStrategies.length == 3) "default strategies count"
  assert (dflt.forbidden.length == 5) "default forbidden count"

  -- ## GCFreeConstraint.withArena
  let arena := GCFreeConstraint.withArena
  assert (arena.maxStackBytes == 8192) "withArena maxStack"
  assert (arena.allowedStrategies.length == 4) "withArena strategies count"

  let arenaCustom := GCFreeConstraint.withArena 16384
  assert (arenaCustom.maxStackBytes == 16384) "withArena custom"

  -- ## checkProfile
  -- Valid: stack with OK size
  let p1 := AllocProfile.mk "fn1" .stack (some 1024)
  assert (checkProfile dflt p1 == true) "checkProfile stack OK"

  -- Valid: static (no stack limit)
  let p2 := AllocProfile.mk "fn2" .static none
  assert (checkProfile dflt p2 == true) "checkProfile static OK"

  -- Valid: none strategy
  let p3 := AllocProfile.mk "fn3" .none none
  assert (checkProfile dflt p3 == true) "checkProfile none OK"

  -- Invalid: arena not in default strategies
  let p4 := AllocProfile.mk "fn4" .arena (some 100)
  assert (checkProfile dflt p4 == false) "checkProfile arena fail"

  -- arena IS in withArena
  assert (checkProfile arena p4 == true) "checkProfile arena in withArena"

  -- Invalid: stack overflow
  let p5 := AllocProfile.mk "fn5" .stack (some 8192)
  assert (checkProfile dflt p5 == false) "checkProfile stack overflow"
  assert (checkProfile arena p5 == true) "checkProfile arena larger stack OK"

  -- ## checkProfileDetailed
  match checkProfileDetailed dflt p1 with
  | .pass => assert true "detailed pass"
  | _ => assert false "detailed should pass"

  match checkProfileDetailed dflt p4 with
  | .failStrategy name _ => assert (name == "fn4") "detailed failStrategy"
  | _ => assert false "detailed should failStrategy"

  match checkProfileDetailed dflt p5 with
  | .failStackOverflow name used limit =>
    assert (name == "fn5") "detailed failStack name"
    assert (used == 8192) "detailed failStack used"
    assert (limit == 4096) "detailed failStack limit"
  | _ => assert false "detailed should failStack"

  -- ## checkModule
  let profiles := [p1, p2, p3, p4, p5]
  let failures := checkModule dflt profiles
  assert (failures.length == 2) "checkModule 2 failures"

  let allOK := checkModule dflt [p1, p2, p3]
  assert (allOK.length == 0) "checkModule 0 failures"

  let allFail := checkModule dflt [p4, p5]
  assert (allFail.length == 2) "checkModule all fail"

  -- ## StackFrame
  let frame1 := StackFrame.mk "main" 64 48 16
  assert (frame1.totalSize == 128) "frame1 totalSize"

  let frame2 := StackFrame.mk "helper" 32 32 0
  assert (frame2.totalSize == 64) "frame2 totalSize"

  let zeroFrame := StackFrame.mk "leaf" 0 0 0
  assert (zeroFrame.totalSize == 0) "zero frame"

  -- ## worstCaseStackDepth
  assert (worstCaseStackDepth [] == 0) "empty stack depth"
  assert (worstCaseStackDepth [frame1] == 128) "single frame depth"
  assert (worstCaseStackDepth [frame1, frame2] == 192) "two frame depth"
  assert (worstCaseStackDepth [frame1, frame2, zeroFrame] == 192) "three frame depth"

  -- Many frames
  let manyFrames := List.replicate 20 frame1
  assert (worstCaseStackDepth manyFrames == 20 * 128) "20 frames depth"

  -- ## Boundary: exact stack limit
  let exactFit := AllocProfile.mk "exact" .stack (some 4096)
  assert (checkProfile dflt exactFit == true) "exact stack limit pass"

  let oneOver := AllocProfile.mk "over" .stack (some 4097)
  assert (checkProfile dflt oneOver == false) "one over stack limit fail"

  c.get
