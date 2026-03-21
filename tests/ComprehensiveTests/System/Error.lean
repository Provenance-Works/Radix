import tests.ComprehensiveTests.Framework
import Radix.System.Error
import Radix.System.FD
import Radix.System.Spec

/-!
# System Error Tests
## Spec References
- FR-006: SysError variants, toString, FD types, lifecycle
-/

open ComprehensiveTests

def runSystemErrorTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    System error tests..."

  -- ## SysError constructors and ToString
  let e1 := Radix.System.SysError.permissionDenied "test"
  assert (toString e1 != "") "permissionDenied toString"

  let e2 := Radix.System.SysError.notFound "missing"
  assert (toString e2 != "") "notFound toString"

  let e3 := Radix.System.SysError.alreadyExists "dup"
  assert (toString e3 != "") "alreadyExists toString"

  let e4 := Radix.System.SysError.resourceBusy "locked"
  assert (toString e4 != "") "resourceBusy toString"

  let e5 := Radix.System.SysError.invalidArgument "bad"
  assert (toString e5 != "") "invalidArgument toString"

  let e6 := Radix.System.SysError.noSpace "full"
  assert (toString e6 != "") "noSpace toString"

  let e7 := Radix.System.SysError.ioError "fail"
  assert (toString e7 != "") "ioError toString"

  let e8 := Radix.System.SysError.interrupted "sig"
  assert (toString e8 != "") "interrupted toString"

  let e9 := Radix.System.SysError.endOfFile
  assert (toString e9 != "") "endOfFile toString"

  let e10 := Radix.System.SysError.invalidState "bad state"
  assert (toString e10 != "") "invalidState toString"

  let e11 := Radix.System.SysError.unsupported "nope"
  assert (toString e11 != "") "unsupported toString"

  -- ## SysError BEq
  assert (e1 == e1) "SysError BEq reflexive"
  assert (!(e1 == e2)) "SysError BEq different"
  assert (Radix.System.SysError.endOfFile == Radix.System.SysError.endOfFile) "endOfFile BEq"

  -- ## FileState spec
  -- Default open state with read-write access for testing
  let openState := Radix.System.Spec.FileState.open
    { position := 0, mode := .readWrite, bytesRead := 0, bytesWritten := 0 }
  -- readPre requires open state
  assert (Decidable.decide (Radix.System.Spec.readPre openState) == true) "readPre open"
  assert (Decidable.decide (Radix.System.Spec.readPre .closed) == false) "readPre closed"

  assert (Decidable.decide (Radix.System.Spec.writePre openState) == true) "writePre open"
  assert (Decidable.decide (Radix.System.Spec.writePre .closed) == false) "writePre closed"

  assert (Decidable.decide (Radix.System.Spec.seekPre openState) == true) "seekPre open"
  assert (Decidable.decide (Radix.System.Spec.seekPre .closed) == false) "seekPre closed"

  assert (Decidable.decide (Radix.System.Spec.closePre openState) == true) "closePre open"
  assert (Decidable.decide (Radix.System.Spec.closePre .closed) == false) "closePre closed"

  -- ## SeekMode constructors
  assert (Radix.System.Spec.SeekMode.set != Radix.System.Spec.SeekMode.cur) "SeekMode set ≠ cur"
  assert (Radix.System.Spec.SeekMode.cur != Radix.System.Spec.SeekMode.end_) "SeekMode cur ≠ end"

  -- ## LifecycleStep validation
  -- Open is valid from closed (initial) state? Actually lifecycle starts from open
  assert (Radix.System.Spec.validStep openState (.read 100) == true) "validStep open read"
  assert (Radix.System.Spec.validStep openState (.write 100) == true) "validStep open write"
  assert (Radix.System.Spec.validStep openState (.seek .set 0) == true) "validStep open seek"
  assert (Radix.System.Spec.validStep openState .close == true) "validStep open close"
  assert (Radix.System.Spec.validStep .closed (.read 100) == false) "validStep closed read"
  assert (Radix.System.Spec.validStep .closed (.write 100) == false) "validStep closed write"
  assert (Radix.System.Spec.validStep .closed .close == false) "validStep closed close"

  -- ## nextState transitions
  assert ((Radix.System.Spec.nextState openState (.read 100)).isOpen == true) "nextState read stays open"
  assert ((Radix.System.Spec.nextState openState (.write 100)).isOpen == true) "nextState write stays open"
  assert (Radix.System.Spec.nextState openState .close == .closed) "nextState close"

  -- ## validLifecycle
  assert (Radix.System.Spec.validLifecycle openState [] == true) "empty lifecycle valid"
  assert (Radix.System.Spec.validLifecycle openState [.read 100, .write 50, .close] == true)
    "read-write-close lifecycle"
  assert (Radix.System.Spec.validLifecycle .closed [.read 100] == false) "closed read invalid"
  assert (Radix.System.Spec.validLifecycle openState [.close, .read 100] == false)
    "read after close invalid"

  -- ## FileInfo
  let fi : Radix.System.Spec.FileInfo := ⟨1024, true, false⟩
  assert (fi.size == 1024) "FileInfo size"
  assert (fi.isFile == true) "FileInfo isFile"
  assert (fi.isDir == false) "FileInfo isDir"

  -- ## ReadSpec / WriteSpec
  let rs : Radix.System.Spec.ReadSpec := ⟨100, 50, by omega⟩
  assert (rs.requested == 100) "ReadSpec requested"
  assert (rs.actual == 50) "ReadSpec actual"

  let ws : Radix.System.Spec.WriteSpec := ⟨200, 200, by omega⟩
  assert (ws.offered == 200) "WriteSpec offered"
  assert (ws.actual == 200) "WriteSpec actual"

  -- ## Ownership
  assert (Radix.System.Ownership.owned != Radix.System.Ownership.borrowed)
    "Ownership variants differ"

  -- ## OpenMode
  assert (Radix.System.OpenMode.read != Radix.System.OpenMode.write) "OpenMode read ≠ write"
  assert (Radix.System.OpenMode.readWrite != Radix.System.OpenMode.append)
    "OpenMode readWrite ≠ append"

  c.get
