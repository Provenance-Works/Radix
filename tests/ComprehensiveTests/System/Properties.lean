import tests.ComprehensiveTests.Framework
import Radix.System.IO
import Radix.System.Spec

/-!
# System Property-Based Tests
## Spec References
- P4-06: Lifecycle validity, write-read round-trips
-/

open ComprehensiveTests

def runSystemPropertyTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    System property tests..."

  -- Default open state with read-write access for testing
  let openState := Radix.System.Spec.FileState.open
    { position := 0, mode := .readWrite, bytesRead := 0, bytesWritten := 0 }

  -- ## Lifecycle property: any valid step sequence from open stays valid
  -- Single valid steps
  let validSteps : List Radix.System.Spec.LifecycleStep := [
    .read 1, .read 100, .read 0,
    .write 1, .write 100, .write 0,
    .seek .set 0, .seek .cur 10, .seek .end_ 0
  ]
  for step in validSteps do
    assert (Radix.System.Spec.validStep openState step == true) "open → valid step"
    assert ((Radix.System.Spec.nextState openState step).isOpen == true) "step: open → open"

  -- Close is terminal
  assert (Radix.System.Spec.validStep openState .close == true) "open → close valid"
  assert (Radix.System.Spec.nextState openState .close == .closed) "close → closed"
  -- Nothing valid from closed except nothing
  for step in validSteps do
    assert (Radix.System.Spec.validStep .closed step == false) s!"closed → invalid"

  -- ## Lifecycle chains
  -- Generate valid lifecycles
  let chains : List (List Radix.System.Spec.LifecycleStep) := [
    [],
    [.read 100],
    [.write 50],
    [.read 100, .write 50],
    [.read 100, .write 50, .close],
    [.read 1, .read 2, .read 3, .write 1, .write 2, .close],
    [.seek .set 0, .read 100, .seek .cur 10, .write 50, .close],
  ]
  for chain in chains do
    assert (Radix.System.Spec.validLifecycle openState chain == true) "valid lifecycle"

  -- Invalid chains (operations after close)
  let invalidChains : List (List Radix.System.Spec.LifecycleStep) := [
    [.close, .read 1],
    [.close, .write 1],
    [.close, .close],
    [.close, .seek .set 0],
  ]
  for chain in invalidChains do
    assert (Radix.System.Spec.validLifecycle openState chain == false) "invalid lifecycle"

  -- ## IO write-read round-trip property
  let tmpDir := "/tmp/radix_prop_" ++ toString (← IO.monoMsNow)
  IO.FS.createDirAll tmpDir
  let mut rng := PRNG.new 65432

  for i in [:50] do
    -- Generate random data up to 256 bytes
    let (rng', sz) := rng.nextBounded 256;  rng := rng'
    let mut data := ByteArray.empty
    for _ in [:sz.toNat] do
      let (rng'', b) := rng.nextUInt8;  rng := rng''
      data := data.push b
    let path := tmpDir ++ s!"/prop_{i}.bin"
    let wr ← Radix.System.IO.writeFileBytes path data
    match wr with
    | .ok () =>
      let rd ← Radix.System.IO.readFileBytes path
      match rd with
      | .ok bytes => assert (bytes == data) s!"IO write-read round-trip {i}"
      | .error _ => assert false s!"IO read error {i}"
    | .error _ => assert false s!"IO write error {i}"

  -- Cleanup
  IO.FS.removeDirAll tmpDir

  c.get
