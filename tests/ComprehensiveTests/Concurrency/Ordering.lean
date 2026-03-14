import tests.ComprehensiveTests.Framework
import Radix.Concurrency.Ordering
import Radix.Concurrency.Spec

/-!
# Concurrency Ordering Tests
## Spec References
- FR-007: MemoryOrder strength, validity, combine, semantics
-/

open ComprehensiveTests
open Radix.Concurrency.Spec
open Radix.Concurrency.Ordering

def runConcurrencyOrderingTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Concurrency ordering tests..."

  -- ## MemoryOrder strength values
  assert (MemoryOrder.relaxed.strength == 0) "relaxed strength"
  assert (MemoryOrder.acquire.strength == 1) "acquire strength"
  assert (MemoryOrder.release.strength == 1) "release strength"
  assert (MemoryOrder.acqRel.strength == 2) "acqRel strength"
  assert (MemoryOrder.seqCst.strength == 3) "seqCst strength"

  -- ## isAtLeast
  -- seqCst is at least everything
  assert (MemoryOrder.seqCst.isAtLeast .relaxed == true) "seqCst ≥ relaxed"
  assert (MemoryOrder.seqCst.isAtLeast .acquire == true) "seqCst ≥ acquire"
  assert (MemoryOrder.seqCst.isAtLeast .release == true) "seqCst ≥ release"
  assert (MemoryOrder.seqCst.isAtLeast .acqRel == true) "seqCst ≥ acqRel"
  assert (MemoryOrder.seqCst.isAtLeast .seqCst == true) "seqCst ≥ seqCst"

  -- Self is at least self
  assert (MemoryOrder.relaxed.isAtLeast .relaxed == true) "relaxed ≥ relaxed"
  assert (MemoryOrder.acquire.isAtLeast .acquire == true) "acquire ≥ acquire"

  -- Relaxed is not at least anything stronger
  assert (MemoryOrder.relaxed.isAtLeast .acquire == false) "relaxed < acquire"
  assert (MemoryOrder.relaxed.isAtLeast .seqCst == false) "relaxed < seqCst"

  -- ## Valid orderings
  -- Load: relaxed, acquire, seqCst
  assert (validLoadOrder .relaxed == true) "load relaxed valid"
  assert (validLoadOrder .acquire == true) "load acquire valid"
  assert (validLoadOrder .seqCst == true) "load seqCst valid"
  assert (validLoadOrder .release == false) "load release invalid"
  assert (validLoadOrder .acqRel == false) "load acqRel invalid"

  -- Store: relaxed, release, seqCst
  assert (validStoreOrder .relaxed == true) "store relaxed valid"
  assert (validStoreOrder .release == true) "store release valid"
  assert (validStoreOrder .seqCst == true) "store seqCst valid"
  assert (validStoreOrder .acquire == false) "store acquire invalid"
  assert (validStoreOrder .acqRel == false) "store acqRel invalid"

  -- RMW: all valid
  assert (validRMWOrder .relaxed == true) "rmw relaxed valid"
  assert (validRMWOrder .acquire == true) "rmw acquire valid"
  assert (validRMWOrder .release == true) "rmw release valid"
  assert (validRMWOrder .acqRel == true) "rmw acqRel valid"
  assert (validRMWOrder .seqCst == true) "rmw seqCst valid"

  -- ## validOrderForAccess
  assert (validOrderForAccess .load .acquire == true) "load acquire"
  assert (validOrderForAccess .store .release == true) "store release"
  assert (validOrderForAccess .rmw .acqRel == true) "rmw acqRel"
  assert (validOrderForAccess .fence .seqCst == true) "fence seqCst"

  -- ## compare
  assert (Radix.Concurrency.Ordering.compare MemoryOrder.relaxed MemoryOrder.seqCst == Ordering.lt) "compare relaxed seqCst"
  assert (Radix.Concurrency.Ordering.compare MemoryOrder.seqCst MemoryOrder.relaxed == Ordering.gt) "compare seqCst relaxed"
  assert (Radix.Concurrency.Ordering.compare MemoryOrder.acquire MemoryOrder.acquire == Ordering.eq) "compare acquire acquire"

  -- ## isStrongerThan
  assert (isStrongerThan .seqCst .relaxed == true) "seqCst stronger than relaxed"
  assert (isStrongerThan .relaxed .seqCst == false) "relaxed not stronger than seqCst"
  assert (isStrongerThan .acqRel .acquire == true) "acqRel stronger than acquire"

  -- ## strengthen
  assert (strengthen .relaxed .seqCst == .seqCst) "strengthen to seqCst"
  assert (strengthen .seqCst .relaxed == .seqCst) "strengthen from seqCst"
  -- strengthen picks the stronger; acquire and release have equal strength,
  -- so strengthen returns current (acquire). Use combineLoadStore for acqRel.
  assert (strengthen .acquire .release == .acquire) "strengthen acq+rel returns current"
  assert (combineLoadStore .acquire .release == .acqRel) "combineLoadStore acq+rel"
  -- Idempotent
  for o in [MemoryOrder.relaxed, .acquire, .release, .acqRel, .seqCst] do
    assert (strengthen o o == o) s!"strengthen idempotent"

  -- ## Acquire/Release semantics
  assert (hasAcquireSemantics .acquire == true) "acquire has acquire"
  assert (hasAcquireSemantics .acqRel == true) "acqRel has acquire"
  assert (hasAcquireSemantics .seqCst == true) "seqCst has acquire"
  assert (hasAcquireSemantics .relaxed == false) "relaxed no acquire"
  assert (hasAcquireSemantics .release == false) "release no acquire"

  assert (hasReleaseSemantics .release == true) "release has release"
  assert (hasReleaseSemantics .acqRel == true) "acqRel has release"
  assert (hasReleaseSemantics .seqCst == true) "seqCst has release"
  assert (hasReleaseSemantics .relaxed == false) "relaxed no release"
  assert (hasReleaseSemantics .acquire == false) "acquire no release"

  assert (isSequentiallyConsistent .seqCst == true) "seqCst is SC"
  assert (isSequentiallyConsistent .acqRel == false) "acqRel not SC"

  -- ## Fence
  assert (fenceAcquires .acquire == true) "fence acquires acquire"
  assert (fenceAcquires .seqCst == true) "fence acquires seqCst"
  assert (fenceReleases .release == true) "fence releases release"
  assert (fenceReleases .seqCst == true) "fence releases seqCst"

  -- ## combineLoadStore
  let combined := combineLoadStore .acquire .release
  assert (combined == .acqRel) "combine acq+rel = acqRel"

  -- ## CAS failure ordering
  assert (validCASFailureOrder .seqCst (defaultFailureOrder .seqCst) == true)
    "CAS failure default seqCst"
  assert (validCASFailureOrder .acqRel (defaultFailureOrder .acqRel) == true)
    "CAS failure default acqRel"
  assert (validCASFailureOrder .release (defaultFailureOrder .release) == true)
    "CAS failure default release"
  assert (validCASFailureOrder .acquire (defaultFailureOrder .acquire) == true)
    "CAS failure default acquire"
  assert (validCASFailureOrder .relaxed (defaultFailureOrder .relaxed) == true)
    "CAS failure default relaxed"

  -- ## effectiveLoadOrder / effectiveStoreOrder
  assert ((effectiveLoadOrder .relaxed .acquire).isAtLeast .acquire == true)
    "effective load with acquire fence"
  assert ((effectiveStoreOrder .relaxed .release).isAtLeast .release == true)
    "effective store with release fence"

  c.get
