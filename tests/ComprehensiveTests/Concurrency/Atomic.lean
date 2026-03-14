import tests.ComprehensiveTests.Framework
import Radix.Concurrency.Atomic
import Radix.Concurrency.Spec

/-!
# Concurrency Atomic Tests
## Spec References
- FR-007: AtomicCell, load/store, CAS, fetch-and-modify, exchange
-/

open ComprehensiveTests
open Radix.Concurrency.Spec
open Radix.Concurrency.Atomic

def runConcurrencyAtomicTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Concurrency atomic tests..."

  -- ## AtomicCell construction and load
  let cell := AtomicCell.new 42
  assert (cell.val == 42) "AtomicCell.new 42"

  let (result, cell') := atomicLoad cell .relaxed
  assert (result.value == 42) "atomicLoad returns value"
  assert (cell' == cell) "atomicLoad preserves cell"

  let (resultSC, _) := atomicLoad cell .seqCst
  assert (resultSC.value == 42) "atomicLoad seqCst"

  -- ## AtomicStore
  let (_, cell2) := atomicStore cell 100 .relaxed
  assert (cell2.val == 100) "atomicStore sets value"

  let (_, cell3) := atomicStore cell 0 .release
  assert (cell3.val == 0) "atomicStore zero"

  let (_, cellSC) := atomicStore cell 999 .seqCst
  assert (cellSC.val == 999) "atomicStore seqCst"

  -- ## Store-Load round-trip
  let c0 := AtomicCell.new 0
  let (_, c1) := atomicStore c0 77 .seqCst
  let (r1, _) := atomicLoad c1 .seqCst
  assert (r1.value == 77) "store-load round-trip"

  -- ## CAS success
  let cell4 := AtomicCell.new 50
  let (casResult, casCell) := atomicCAS cell4 50 99 .seqCst
  assert (casResult.success == true) "CAS success"
  assert (casResult.previous == 50) "CAS previous"
  assert (casCell.val == 99) "CAS sets desired"

  -- ## CAS failure
  let (casResult2, casCell2) := atomicCAS cell4 999 0 .seqCst
  assert (casResult2.success == false) "CAS failure"
  assert (casResult2.previous == 50) "CAS failure previous"
  assert (casCell2 == cell4) "CAS failure preserves cell"

  -- ## CAS with explicit failure ordering
  let (casR3, _) := atomicCAS cell4 50 100 .acqRel .acquire
  assert (casR3.success == true) "CAS acqRel/acquire success"

  -- ## atomicCompareExchangeStrong alias
  let (casR4, _) := atomicCompareExchangeStrong cell4 50 200 .seqCst
  assert (casR4.success == true) "CAS strong alias"

  -- ## fetchAdd
  let cell5 := AtomicCell.new 10
  let (fetchR, fetchC) := fetchAdd cell5 5 .seqCst
  assert (fetchR.previous == 10) "fetchAdd previous"
  assert (fetchC.val == 15) "fetchAdd result"

  -- fetchAdd 0 = identity
  let (fetchR0, fetchC0) := fetchAdd cell5 0 .relaxed
  assert (fetchR0.previous == 10) "fetchAdd 0 previous"
  assert (fetchC0 == cell5) "fetchAdd 0 identity"

  -- ## fetchSub
  let cell6 := AtomicCell.new 20
  let (subR, subC) := fetchSub cell6 7 .seqCst
  assert (subR.previous == 20) "fetchSub previous"
  assert (subC.val == 13) "fetchSub result"

  -- ## fetchAnd
  let cell7 := AtomicCell.new 0xFF
  let (andR, andC) := fetchAnd cell7 0x0F .seqCst
  assert (andR.previous == 0xFF) "fetchAnd previous"
  assert (andC.val == 0x0F) "fetchAnd result"

  -- ## fetchOr
  let cell8 := AtomicCell.new 0x0F
  let (orR, orC) := fetchOr cell8 0xF0 .seqCst
  assert (orR.previous == 0x0F) "fetchOr previous"
  assert (orC.val == 0xFF) "fetchOr result"

  -- ## fetchXor
  let cell9 := AtomicCell.new 0xFF
  let (xorR, xorC) := fetchXor cell9 0xFF .seqCst
  assert (xorR.previous == 0xFF) "fetchXor previous"
  assert (xorC.val == 0) "fetchXor self = 0"

  -- ## atomicExchange
  let cell10 := AtomicCell.new 42
  let (exchR, exchC) := atomicExchange cell10 100 .seqCst
  assert (exchR.previous == 42) "exchange previous"
  assert (exchC.val == 100) "exchange new value"

  -- ## Sequential operations
  let mut s := AtomicCell.new 0
  for _ in [:10] do
    let (_, s') := fetchAdd s 1 .seqCst
    s := s'
  assert (s.val == 10) "sequential fetchAdd ×10"

  -- ## CAS retry loop pattern
  let mut cell11 := AtomicCell.new 0
  for i in [:5] do
    let mut done := false
    let mut retries := 0
    while !done && retries < 3 do
      let (loadR, _) := atomicLoad cell11 .seqCst
      let expected := loadR.value
      let desired := expected + 1
      let (casR, casC) := atomicCAS cell11 expected desired .seqCst
      if casR.success then
        cell11 := casC
        done := true
      retries := retries + 1
    assert done s!"CAS retry loop iteration {i}"
  assert (cell11.val == 5) "CAS retry result"

  -- ## Event construction
  let tid := ThreadId.mk 1
  let loc := LocationId.mk 100
  let loadEvt := mkLoadEvent tid 0 loc ⟨42⟩ .acquire
  assert (loadEvt.id.thread == tid) "load event thread"
  assert (loadEvt.kind == .load) "load event kind"
  assert (loadEvt.readVal == 42) "load event readVal"
  assert (loadEvt.order == .acquire) "load event order"

  let storeEvt := mkStoreEvent tid 1 loc 99 .release
  assert (storeEvt.kind == .store) "store event kind"
  assert (storeEvt.writeVal == 99) "store event writeVal"

  let fenceEvt := mkFenceEvent tid 2 .seqCst
  assert (fenceEvt.kind == .fence) "fence event kind"
  assert (fenceEvt.order == .seqCst) "fence event order"

  -- ## Trace construction
  let trace := Trace.mk [loadEvt, storeEvt, fenceEvt]
  let threadEvts := trace.threadEvents tid
  assert (threadEvts.length == 3) "trace threadEvents"

  let locEvts := trace.locationEvents loc
  assert (locEvts.length == 2) "trace locationEvents (load + store)"

  let emptyTrace := Trace.mk []
  assert (emptyTrace.events.length == 0) "empty trace"

  -- ## AccessKind
  assert (AccessKind.load.isRead == true) "load isRead"
  assert (AccessKind.store.isRead == false) "store not isRead"
  assert (AccessKind.store.isWrite == true) "store isWrite"
  assert (AccessKind.load.isWrite == false) "load not isWrite"
  assert (AccessKind.rmw.isRead == true) "rmw isRead"
  assert (AccessKind.rmw.isWrite == true) "rmw isWrite"

  c.get
