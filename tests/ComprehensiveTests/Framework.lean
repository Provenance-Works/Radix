

/-!
# Comprehensive Test Framework

Shared infrastructure for all comprehensive tests:
- Assertion tracking with counter
- Simple LCG PRNG for property-based testing
- Helper utilities

## References

- P4-01: Property-based tests
- All FR-* requirements (testing infrastructure)
-/

set_option autoImplicit false

namespace ComprehensiveTests

/-! ## Assertion Infrastructure -/

/-- Create an assert function that increments `counter` on each call
    and throws IO.userError on failure. -/
@[inline] def mkAssert (counter : IO.Ref Nat) : Bool → String → IO Unit :=
  fun cond msg => do
    counter.modify (· + 1)
    if !cond then throw (IO.userError s!"FAIL: {msg}")

/-! ## PRNG for Property Tests -/

/-- Simple 64-bit LCG PRNG (Knuth MMIX: a=6364136223846793005, c=1442695040888963407). -/
structure PRNG where
  state : UInt64

def PRNG.new (seed : UInt64 := 42) : PRNG := { state := seed }

def PRNG.next (rng : PRNG) : PRNG × UInt64 :=
  let a : UInt64 := 6364136223846793005
  let c : UInt64 := 1442695040888963407
  let s := rng.state * a + c
  ({ state := s }, s)

def PRNG.nextBounded (rng : PRNG) (bound : UInt64) : PRNG × UInt64 :=
  let (rng', v) := rng.next
  if bound == 0 then (rng', 0) else (rng', v % bound)

def PRNG.nextUInt8 (rng : PRNG) : PRNG × UInt8 :=
  let (rng', v) := rng.next
  (rng', (v % 256).toUInt8)

def PRNG.nextUInt16 (rng : PRNG) : PRNG × UInt16 :=
  let (rng', v) := rng.next
  (rng', (v % 65536).toUInt16)

def PRNG.nextUInt32 (rng : PRNG) : PRNG × UInt32 :=
  let (rng', v) := rng.next
  (rng', (v % 4294967296).toUInt32)

def PRNG.nextUInt64 (rng : PRNG) : PRNG × UInt64 :=
  rng.next

def PRNG.nextNat (rng : PRNG) (bound : Nat) : PRNG × Nat :=
  let (rng', v) := rng.next
  if bound == 0 then (rng', 0) else (rng', v.toNat % bound)

/-! ## Constants -/

/-- Default iteration count for property tests. -/
def numIter : Nat := 200

/-- High iteration count for critical property tests. -/
def numIterHigh : Nat := 500

end ComprehensiveTests
