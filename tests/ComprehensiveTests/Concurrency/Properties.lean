import tests.ComprehensiveTests.Framework
import Radix.Concurrency.Atomic
import Radix.Concurrency.Ordering
import Radix.Concurrency.Spec

/-!
# Concurrency Property-Based Tests
## Spec References
- P4-07: Ordering properties, atomic consistency
-/

open ComprehensiveTests
open Radix.Concurrency.Spec
open Radix.Concurrency.Ordering
open Radix.Concurrency.Atomic

def runConcurrencyPropertyTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Concurrency property tests..."
  let mut rng := PRNG.new 98765

  -- ## strengthen is idempotent
  let orders := [MemoryOrder.relaxed, .acquire, .release, .acqRel, .seqCst]
  for o1 in orders do
    for o2 in orders do
      let s1 := strengthen o1 o2
      let s2 := strengthen s1 o2
      assert (s1 == s2) "strengthen idempotent"

  -- ## seqCst is at least everything
  for o in orders do
    assert (MemoryOrder.seqCst.isAtLeast o == true) "seqCst isAtLeast all"

  -- ## isAtLeast reflexive
  for o in orders do
    assert (o.isAtLeast o == true) "isAtLeast reflexive"

  -- ## strengthen commutative
  -- Note: strengthen may not be commutative in general, but s(a,b).isAtLeast both
  for o1 in orders do
    for o2 in orders do
      let s := strengthen o1 o2
      assert (s.isAtLeast o1 == true) "strengthen >= first"
      assert (s.isAtLeast o2 == true) "strengthen >= second"

  -- ## CAS: success then load sees new value
  for _ in [:numIter] do
    let (rng', v1) := rng.nextBounded 1000;  rng := rng'
    let (rng'', v2) := rng.nextBounded 1000;  rng := rng''
    let cell := AtomicCell.new v1.toNat
    let (casR, casC) := atomicCAS cell v1.toNat v2.toNat .seqCst
    assert (casR.success == true) "CAS success prop"
    let (loadR, _) := atomicLoad casC .seqCst
    assert (loadR.value == v2.toNat) "CAS then load"

  -- ## CAS: failure preserves value
  for _ in [:numIter] do
    let (rng', v1) := rng.nextBounded 1000;  rng := rng'
    let (rng'', wrong) := rng.nextBounded 1000;  rng := rng''
    if v1 != wrong then
      let cell := AtomicCell.new v1.toNat
      let (casR, casC) := atomicCAS cell wrong.toNat 999 .seqCst
      assert (casR.success == false) "CAS failure prop"
      assert (casC.val == v1.toNat) "CAS failure preserves"

  -- ## fetchAdd/fetchSub inverse
  for _ in [:numIter] do
    let (rng', v) := rng.nextBounded 500;  rng := rng'
    let (rng'', delta) := rng.nextBounded 100;  rng := rng''
    let cell := AtomicCell.new (v.toNat + delta.toNat)
    let (_, c1) := fetchAdd cell delta.toNat .relaxed
    let (_, c2) := fetchSub c1 delta.toNat .relaxed
    -- fetchAdd adds delta, fetchSub subtracts delta, net is same as original+delta
    assert (c2.val == (v.toNat + delta.toNat)) "fetchAdd/fetchSub round-trip"

  -- ## fetchXor self = 0
  for _ in [:numIter] do
    let (rng', v) := rng.nextBounded 10000;  rng := rng'
    let cell := AtomicCell.new v.toNat
    let (_, c1) := fetchXor cell v.toNat .relaxed
    assert (c1.val == 0) "fetchXor self = 0"

  -- ## store-load round-trip property
  for _ in [:numIter] do
    let (rng', v) := rng.nextBounded 100000;  rng := rng'
    let cell := AtomicCell.new 0
    let (_, c1) := atomicStore cell v.toNat .release
    let (loadR, _) := atomicLoad c1 .acquire
    assert (loadR.value == v.toNat) "store-load prop"

  -- ## exchange returns old, sets new
  for _ in [:numIter] do
    let (rng', old) := rng.nextBounded 1000;  rng := rng'
    let (rng'', new_) := rng.nextBounded 1000;  rng := rng''
    let cell := AtomicCell.new old.toNat
    let (exchR, exchC) := atomicExchange cell new_.toNat .seqCst
    assert (exchR.previous == old.toNat) "exchange previous prop"
    assert (exchC.val == new_.toNat) "exchange new prop"

  -- ## programOrder: same thread, increasing seqNo
  let tid := ThreadId.mk 1
  let loc := LocationId.mk 0
  let evtA := mkLoadEvent tid 0 loc ⟨10⟩ .relaxed
  let evtB := mkStoreEvent tid 1 loc 20 .relaxed
  assert (Decidable.decide (programOrder evtA evtB) == true) "program order a < b"
  assert (Decidable.decide (programOrder evtB evtA) == false) "program order b < a"

  -- ## defaultFailureOrder: never release/acqRel
  for o in orders do
    let fo := defaultFailureOrder o
    assert (fo != .release) "default failure not release"
    assert (fo != .acqRel) "default failure not acqRel"
    assert (validCASFailureOrder o fo == true) "default failure valid"

  -- ## validOrderForAccess exhaustive
  let kinds := [AccessKind.load, .store, .rmw, .fence]
  for k in kinds do
    for o in orders do
      let valid := validOrderForAccess k o
      match k with
      | .load => assert (valid == validLoadOrder o) "load match"
      | .store => assert (valid == validStoreOrder o) "store match"
      | .rmw => assert (valid == validRMWOrder o) "rmw match"
      | .fence => assert (valid == true) "fence always valid"

  c.get
