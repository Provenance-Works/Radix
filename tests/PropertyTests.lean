import Radix.Word.Arith
import Radix.Word.Int
import Radix.Word.Size
import Radix.Word.Conv
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field
import Radix.Bytes
import Radix.Memory
import Radix.Binary
import Radix.System

/-!
# Radix Phase 4 — Property-Based Tests (P4-01)

Randomized and exhaustive property testing for all Radix types.
Uses a simple LCG PRNG to generate pseudo-random inputs.

## Coverage

- 10 types × arithmetic properties (commutativity, identity, inverse)
- Edge case exhaustive tests (MIN, MAX, 0, -1)
- Cross-validation between arithmetic modes
- Bitwise algebraic properties
- Conversion round-trip properties
- LEB128 round-trips with random values
- Byte order round-trips
- Memory buffer read/write properties

## References

- P4-01: Property-based tests
- FR-001: Fixed-width integer arithmetic
-/

set_option autoImplicit false

/-! ## Test Infrastructure -/

private def assert (cond : Bool) (msg : String) : IO Unit :=
  if !cond then throw (IO.userError s!"FAIL: {msg}") else pure ()

/-- Simple 64-bit LCG PRNG for generating test inputs.
    Parameters from Knuth MMIX (a=6364136223846793005, c=1442695040888963407). -/
structure PRNG where
  state : UInt64
  deriving Repr

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

/-- Number of random iterations per property test. -/
private def numIter : Nat := 500

/-! ================================================================ -/
/-! ## UInt8 Property Tests                                          -/
/-! ================================================================ -/

private def testUInt8Properties : IO Unit := do
  IO.println "  UInt8 properties..."
  let mut rng := PRNG.new 1

  -- Addition commutativity: a + b = b + a
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    assert (Radix.UInt8.wrappingAdd a b == Radix.UInt8.wrappingAdd b a)
      s!"UInt8 add comm: {av} + {bv}"

  -- Addition identity: a + 0 = a
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    assert (Radix.UInt8.wrappingAdd a ⟨0⟩ == a)
      s!"UInt8 add identity: {av}"

  -- Subtraction self: a - a = 0
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    assert ((Radix.UInt8.wrappingSub a a).toNat == 0)
      s!"UInt8 sub self: {av}"

  -- Multiplication commutativity: a * b = b * a
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    assert (Radix.UInt8.wrappingMul a b == Radix.UInt8.wrappingMul b a)
      s!"UInt8 mul comm: {av} * {bv}"

  -- Multiplication identity: a * 1 = a
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    assert (Radix.UInt8.wrappingMul a ⟨1⟩ == a)
      s!"UInt8 mul identity: {av}"

  -- Cross-validation: wrapping == overflowing.fst
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    let wr := Radix.UInt8.wrappingAdd a b
    let (ov, _) := Radix.UInt8.overflowingAdd a b
    assert (wr == ov) s!"UInt8 wrapping==overflowing add: {av},{bv}"

  -- Cross-validation: checked.some == wrapping (when no overflow)
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    let ch := Radix.UInt8.checkedAdd a b
    let wr := Radix.UInt8.wrappingAdd a b
    let (_, flag) := Radix.UInt8.overflowingAdd a b
    if flag then
      assert (ch == none) s!"UInt8 checked none on overflow: {av},{bv}"
    else
      assert (ch == some wr) s!"UInt8 checked some: {av},{bv}"

  -- Saturating bounds: saturatingAdd ≤ maxVal
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    assert ((Radix.UInt8.saturatingAdd a b).toNat ≤ 255)
      s!"UInt8 saturating bound: {av},{bv}"

  -- Bitwise: AND commutativity
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    assert (Radix.UInt8.band a b == Radix.UInt8.band b a)
      s!"UInt8 band comm: {av},{bv}"

  -- Bitwise: OR commutativity
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    assert (Radix.UInt8.bor a b == Radix.UInt8.bor b a)
      s!"UInt8 bor comm: {av},{bv}"

  -- Bitwise: XOR commutativity
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    assert (Radix.UInt8.bxor a b == Radix.UInt8.bxor b a)
      s!"UInt8 bxor comm: {av},{bv}"

  -- Bitwise: double NOT involution
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    assert (Radix.UInt8.bnot (Radix.UInt8.bnot a) == a)
      s!"UInt8 bnot involution: {av}"

  -- Bitwise: XOR self = 0
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    assert ((Radix.UInt8.bxor a a).toNat == 0)
      s!"UInt8 xor self: {av}"

  -- Bitwise: AND self = self
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    assert (Radix.UInt8.band a a == a) s!"UInt8 band self: {av}"

  -- Bitwise: De Morgan (NOT(a AND b) = NOT a OR NOT b)
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    assert (Radix.UInt8.bnot (Radix.UInt8.band a b) ==
            Radix.UInt8.bor (Radix.UInt8.bnot a) (Radix.UInt8.bnot b))
      s!"UInt8 De Morgan AND: {av},{bv}"

  -- popcount: popcount(0) = 0, popcount(MAX) = 8
  assert (Radix.UInt8.popcount ⟨0⟩ == 0) "UInt8 popcount(0)"
  assert (Radix.UInt8.popcount ⟨255⟩ == 8) "UInt8 popcount(MAX)"

  -- clz + ctz + popcount relationships
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let pc := Radix.UInt8.popcount a
    assert (pc.toNat ≤ 8) s!"UInt8 popcount bound: {av}"

  -- Rotate: rotl then rotr = identity
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', sv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let s : Radix.UInt8 := ⟨sv % 8⟩
    assert (Radix.UInt8.rotr (Radix.UInt8.rotl a s) s == a)
      s!"UInt8 rotl/rotr round-trip: {av},{sv % 8}"

  -- bitReverse involution
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    assert (Radix.UInt8.bitReverse (Radix.UInt8.bitReverse a) == a)
      s!"UInt8 bitReverse involution: {av}"

/-! ================================================================ -/
/-! ## UInt16 Property Tests                                         -/
/-! ================================================================ -/

private def testUInt16Properties : IO Unit := do
  IO.println "  UInt16 properties..."
  let mut rng := PRNG.new 2

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let (rng', bv) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    let b : Radix.UInt16 := ⟨bv⟩
    -- Commutativity
    assert (Radix.UInt16.wrappingAdd a b == Radix.UInt16.wrappingAdd b a)
      s!"UInt16 add comm: {av},{bv}"
    assert (Radix.UInt16.wrappingMul a b == Radix.UInt16.wrappingMul b a)
      s!"UInt16 mul comm: {av},{bv}"
    -- wrapping == overflowing.fst
    let wr := Radix.UInt16.wrappingAdd a b
    let (ov, _) := Radix.UInt16.overflowingAdd a b
    assert (wr == ov) s!"UInt16 wrapping==overflowing: {av},{bv}"
    -- Bitwise
    assert (Radix.UInt16.band a b == Radix.UInt16.band b a)
      s!"UInt16 band comm"
    assert (Radix.UInt16.bor a b == Radix.UInt16.bor b a)
      s!"UInt16 bor comm"
    assert (Radix.UInt16.bxor a b == Radix.UInt16.bxor b a)
      s!"UInt16 bxor comm"

  -- Identity and self
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    assert (Radix.UInt16.wrappingAdd a ⟨0⟩ == a) s!"UInt16 add identity"
    assert (Radix.UInt16.wrappingMul a ⟨1⟩ == a) s!"UInt16 mul identity"
    assert ((Radix.UInt16.wrappingSub a a).toNat == 0) s!"UInt16 sub self"
    assert ((Radix.UInt16.bxor a a).toNat == 0) s!"UInt16 xor self"
    assert (Radix.UInt16.bnot (Radix.UInt16.bnot a) == a) s!"UInt16 bnot involution"
    assert (Radix.UInt16.band a a == a) s!"UInt16 band self"

  -- De Morgan
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let (rng', bv) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    let b : Radix.UInt16 := ⟨bv⟩
    assert (Radix.UInt16.bnot (Radix.UInt16.band a b) ==
            Radix.UInt16.bor (Radix.UInt16.bnot a) (Radix.UInt16.bnot b))
      s!"UInt16 De Morgan"

  -- Saturating bounds
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let (rng', bv) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    let b : Radix.UInt16 := ⟨bv⟩
    assert ((Radix.UInt16.saturatingAdd a b).toNat ≤ 65535) s!"UInt16 sat bound"
    assert ((Radix.UInt16.saturatingSub a b).toNat ≤ 65535) s!"UInt16 sat sub bound"

  -- Rotate round-trip
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let (rng', sv) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    let s : Radix.UInt16 := ⟨sv % 16⟩
    assert (Radix.UInt16.rotr (Radix.UInt16.rotl a s) s == a)
      s!"UInt16 rotl/rotr round-trip"

  -- bitReverse involution
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    assert (Radix.UInt16.bitReverse (Radix.UInt16.bitReverse a) == a)
      s!"UInt16 bitReverse involution"

  -- popcount bound
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    assert ((Radix.UInt16.popcount a).toNat ≤ 16) s!"UInt16 popcount bound"

/-! ================================================================ -/
/-! ## UInt32 Property Tests                                         -/
/-! ================================================================ -/

private def testUInt32Properties : IO Unit := do
  IO.println "  UInt32 properties..."
  let mut rng := PRNG.new 3

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let (rng', bv) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    let b : Radix.UInt32 := ⟨bv⟩
    assert (Radix.UInt32.wrappingAdd a b == Radix.UInt32.wrappingAdd b a)
      s!"UInt32 add comm"
    assert (Radix.UInt32.wrappingMul a b == Radix.UInt32.wrappingMul b a)
      s!"UInt32 mul comm"
    let wr := Radix.UInt32.wrappingAdd a b
    let (ov, _) := Radix.UInt32.overflowingAdd a b
    assert (wr == ov) s!"UInt32 wrapping==overflowing"
    assert (Radix.UInt32.band a b == Radix.UInt32.band b a) s!"UInt32 band comm"
    assert (Radix.UInt32.bor a b == Radix.UInt32.bor b a) s!"UInt32 bor comm"
    assert (Radix.UInt32.bxor a b == Radix.UInt32.bxor b a) s!"UInt32 bxor comm"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    assert (Radix.UInt32.wrappingAdd a ⟨0⟩ == a) s!"UInt32 add identity"
    assert (Radix.UInt32.wrappingMul a ⟨1⟩ == a) s!"UInt32 mul identity"
    assert ((Radix.UInt32.wrappingSub a a).toNat == 0) s!"UInt32 sub self"
    assert ((Radix.UInt32.bxor a a).toNat == 0) s!"UInt32 xor self"
    assert (Radix.UInt32.bnot (Radix.UInt32.bnot a) == a) s!"UInt32 bnot involution"

  -- De Morgan
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let (rng', bv) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    let b : Radix.UInt32 := ⟨bv⟩
    assert (Radix.UInt32.bnot (Radix.UInt32.band a b) ==
            Radix.UInt32.bor (Radix.UInt32.bnot a) (Radix.UInt32.bnot b))
      s!"UInt32 De Morgan"

  -- Saturating
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let (rng', bv) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    let b : Radix.UInt32 := ⟨bv⟩
    assert ((Radix.UInt32.saturatingAdd a b).toNat ≤ 4294967295)
      s!"UInt32 sat bound"

  -- Rotate round-trip
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let (rng', sv) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    let s : Radix.UInt32 := ⟨sv % 32⟩
    assert (Radix.UInt32.rotr (Radix.UInt32.rotl a s) s == a)
      s!"UInt32 rotl/rotr round-trip"

  -- bitReverse involution
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    assert (Radix.UInt32.bitReverse (Radix.UInt32.bitReverse a) == a)
      s!"UInt32 bitReverse involution"

  -- Checked cross-validation
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let (rng', bv) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    let b : Radix.UInt32 := ⟨bv⟩
    let ch := Radix.UInt32.checkedAdd a b
    let (_, flag) := Radix.UInt32.overflowingAdd a b
    if flag then
      assert (ch == none) s!"UInt32 checked none on overflow"
    else
      assert (ch.isSome) s!"UInt32 checked some when no overflow"

/-! ================================================================ -/
/-! ## UInt64 Property Tests                                         -/
/-! ================================================================ -/

private def testUInt64Properties : IO Unit := do
  IO.println "  UInt64 properties..."
  let mut rng := PRNG.new 4

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let (rng', bv) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    let b : Radix.UInt64 := ⟨bv⟩
    assert (Radix.UInt64.wrappingAdd a b == Radix.UInt64.wrappingAdd b a)
      s!"UInt64 add comm"
    assert (Radix.UInt64.wrappingMul a b == Radix.UInt64.wrappingMul b a)
      s!"UInt64 mul comm"
    let wr := Radix.UInt64.wrappingAdd a b
    let (ov, _) := Radix.UInt64.overflowingAdd a b
    assert (wr == ov) s!"UInt64 wrapping==overflowing"
    assert (Radix.UInt64.band a b == Radix.UInt64.band b a) s!"UInt64 band comm"
    assert (Radix.UInt64.bxor a b == Radix.UInt64.bxor b a) s!"UInt64 bxor comm"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    assert (Radix.UInt64.wrappingAdd a ⟨0⟩ == a) s!"UInt64 add identity"
    assert (Radix.UInt64.wrappingMul a ⟨1⟩ == a) s!"UInt64 mul identity"
    assert ((Radix.UInt64.wrappingSub a a).toNat == 0) s!"UInt64 sub self"
    assert ((Radix.UInt64.bxor a a).toNat == 0) s!"UInt64 xor self"
    assert (Radix.UInt64.bnot (Radix.UInt64.bnot a) == a) s!"UInt64 bnot involution"

  -- De Morgan
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let (rng', bv) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    let b : Radix.UInt64 := ⟨bv⟩
    assert (Radix.UInt64.bnot (Radix.UInt64.band a b) ==
            Radix.UInt64.bor (Radix.UInt64.bnot a) (Radix.UInt64.bnot b))
      s!"UInt64 De Morgan"

  -- Rotate round-trip
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let (rng', sv) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    let s : Radix.UInt64 := ⟨sv % 64⟩
    assert (Radix.UInt64.rotr (Radix.UInt64.rotl a s) s == a)
      s!"UInt64 rotl/rotr round-trip"

  -- bitReverse involution
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    assert (Radix.UInt64.bitReverse (Radix.UInt64.bitReverse a) == a)
      s!"UInt64 bitReverse involution"

  -- Checked cross-validation
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let (rng', bv) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    let b : Radix.UInt64 := ⟨bv⟩
    let ch := Radix.UInt64.checkedAdd a b
    let (_, flag) := Radix.UInt64.overflowingAdd a b
    if flag then
      assert (ch == none) s!"UInt64 checked none on overflow"
    else
      assert (ch.isSome) s!"UInt64 checked some when no overflow"

/-! ================================================================ -/
/-! ## Int8 Property Tests                                           -/
/-! ================================================================ -/

private def testInt8Properties : IO Unit := do
  IO.println "  Int8 properties..."
  let mut rng := PRNG.new 5

  -- Wrapping add commutativity
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.Int8 := ⟨av⟩
    let b : Radix.Int8 := ⟨bv⟩
    assert (Radix.Int8.wrappingAdd a b == Radix.Int8.wrappingAdd b a)
      s!"Int8 add comm"

  -- Wrapping add identity: a + 0 = a
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.Int8 := ⟨av⟩
    let zero : Radix.Int8 := ⟨⟨0⟩⟩
    assert (Radix.Int8.wrappingAdd a zero == a) s!"Int8 add identity"

  -- a - a = 0
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.Int8 := ⟨av⟩
    assert (Radix.Int8.wrappingSub a a == ⟨⟨0⟩⟩) s!"Int8 sub self"

  -- Negation: a + (-a) = 0
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.Int8 := ⟨av⟩
    let neg := Radix.Int8.wrappingNeg a
    assert (Radix.Int8.wrappingAdd a neg == ⟨⟨0⟩⟩) s!"Int8 neg inverse"

  -- Wrapping mul commutativity
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.Int8 := ⟨av⟩
    let b : Radix.Int8 := ⟨bv⟩
    assert (Radix.Int8.wrappingMul a b == Radix.Int8.wrappingMul b a)
      s!"Int8 mul comm"

  -- Bitwise: bnot involution, xor self, band self
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.Int8 := ⟨av⟩
    assert (Radix.Int8.bnot (Radix.Int8.bnot a) == a) s!"Int8 bnot involution"
    assert (Radix.Int8.bxor a a == ⟨⟨0⟩⟩) s!"Int8 xor self"
    assert (Radix.Int8.band a a == a) s!"Int8 band self"

  -- Edge case: MIN + MAX = -1
  assert (Radix.Int8.wrappingAdd Radix.Int8.minVal Radix.Int8.maxVal == ⟨⟨255⟩⟩)
    "Int8 MIN+MAX = -1"

  -- Edge case: MIN / -1 → checked returns none (overflow)
  let minus1 : Radix.Int8 := ⟨⟨255⟩⟩
  assert (Radix.Int8.checkedDiv Radix.Int8.minVal minus1 == none)
    "Int8 MIN/-1 checked"

/-! ================================================================ -/
/-! ## Int16 Property Tests                                          -/
/-! ================================================================ -/

private def testInt16Properties : IO Unit := do
  IO.println "  Int16 properties..."
  let mut rng := PRNG.new 6

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let (rng', bv) := rng.nextUInt16; rng := rng'
    let a : Radix.Int16 := ⟨av⟩
    let b : Radix.Int16 := ⟨bv⟩
    assert (Radix.Int16.wrappingAdd a b == Radix.Int16.wrappingAdd b a)
      s!"Int16 add comm"
    assert (Radix.Int16.wrappingMul a b == Radix.Int16.wrappingMul b a)
      s!"Int16 mul comm"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let a : Radix.Int16 := ⟨av⟩
    let zero : Radix.Int16 := ⟨⟨0⟩⟩
    assert (Radix.Int16.wrappingAdd a zero == a) s!"Int16 add identity"
    assert (Radix.Int16.wrappingSub a a == zero) s!"Int16 sub self"
    let neg := Radix.Int16.wrappingNeg a
    assert (Radix.Int16.wrappingAdd a neg == zero) s!"Int16 neg inverse"
    assert (Radix.Int16.bnot (Radix.Int16.bnot a) == a) s!"Int16 bnot involution"

  -- Edge case
  let minus1_16 : Radix.Int16 := ⟨⟨65535⟩⟩
  assert (Radix.Int16.checkedDiv Radix.Int16.minVal minus1_16 == none)
    "Int16 MIN/-1 checked"

/-! ================================================================ -/
/-! ## Int32 Property Tests                                          -/
/-! ================================================================ -/

private def testInt32Properties : IO Unit := do
  IO.println "  Int32 properties..."
  let mut rng := PRNG.new 7

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let (rng', bv) := rng.nextUInt32; rng := rng'
    let a : Radix.Int32 := ⟨av⟩
    let b : Radix.Int32 := ⟨bv⟩
    assert (Radix.Int32.wrappingAdd a b == Radix.Int32.wrappingAdd b a)
      s!"Int32 add comm"
    assert (Radix.Int32.wrappingMul a b == Radix.Int32.wrappingMul b a)
      s!"Int32 mul comm"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.Int32 := ⟨av⟩
    let zero : Radix.Int32 := ⟨⟨0⟩⟩
    assert (Radix.Int32.wrappingAdd a zero == a) s!"Int32 add identity"
    assert (Radix.Int32.wrappingSub a a == zero) s!"Int32 sub self"
    let neg := Radix.Int32.wrappingNeg a
    assert (Radix.Int32.wrappingAdd a neg == zero) s!"Int32 neg inverse"
    assert (Radix.Int32.bnot (Radix.Int32.bnot a) == a) s!"Int32 bnot involution"

  -- Edge case
  let minus1_32 : Radix.Int32 := ⟨⟨4294967295⟩⟩
  assert (Radix.Int32.checkedDiv Radix.Int32.minVal minus1_32 == none)
    "Int32 MIN/-1 checked"

/-! ================================================================ -/
/-! ## Int64 Property Tests                                          -/
/-! ================================================================ -/

private def testInt64Properties : IO Unit := do
  IO.println "  Int64 properties..."
  let mut rng := PRNG.new 8

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let (rng', bv) := rng.nextUInt64; rng := rng'
    let a : Radix.Int64 := ⟨av⟩
    let b : Radix.Int64 := ⟨bv⟩
    assert (Radix.Int64.wrappingAdd a b == Radix.Int64.wrappingAdd b a)
      s!"Int64 add comm"
    assert (Radix.Int64.wrappingMul a b == Radix.Int64.wrappingMul b a)
      s!"Int64 mul comm"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.Int64 := ⟨av⟩
    let zero : Radix.Int64 := ⟨⟨0⟩⟩
    assert (Radix.Int64.wrappingAdd a zero == a) s!"Int64 add identity"
    assert (Radix.Int64.wrappingSub a a == zero) s!"Int64 sub self"
    let neg := Radix.Int64.wrappingNeg a
    assert (Radix.Int64.wrappingAdd a neg == zero) s!"Int64 neg inverse"
    assert (Radix.Int64.bnot (Radix.Int64.bnot a) == a) s!"Int64 bnot involution"

  -- Edge case
  let minus1_64 : Radix.Int64 := ⟨⟨18446744073709551615⟩⟩
  assert (Radix.Int64.checkedDiv Radix.Int64.minVal minus1_64 == none)
    "Int64 MIN/-1 checked"

/-! ================================================================ -/
/-! ## UWord / IWord Property Tests                                  -/
/-! ================================================================ -/

private def testUWordProperties : IO Unit := do
  IO.println "  UWord properties..."
  let mut rng := PRNG.new 9

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let (rng', bv) := rng.nextUInt64; rng := rng'
    let a : Radix.UWord := ⟨BitVec.ofNat _ av.toNat⟩
    let b : Radix.UWord := ⟨BitVec.ofNat _ bv.toNat⟩
    assert (Radix.UWord.wrappingAdd a b == Radix.UWord.wrappingAdd b a)
      s!"UWord add comm"
    assert (Radix.UWord.wrappingMul a b == Radix.UWord.wrappingMul b a)
      s!"UWord mul comm"
    assert (Radix.UWord.band a b == Radix.UWord.band b a) s!"UWord band comm"
    assert (Radix.UWord.bxor a b == Radix.UWord.bxor b a) s!"UWord bxor comm"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.UWord := ⟨BitVec.ofNat _ av.toNat⟩
    let zero : Radix.UWord := ⟨BitVec.ofNat _ 0⟩
    assert (Radix.UWord.wrappingAdd a zero == a) s!"UWord add identity"
    assert ((Radix.UWord.wrappingSub a a).toNat == 0) s!"UWord sub self"
    assert (Radix.UWord.bnot (Radix.UWord.bnot a) == a) s!"UWord bnot involution"

private def testIWordProperties : IO Unit := do
  IO.println "  IWord properties..."
  let mut rng := PRNG.new 10

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let (rng', bv) := rng.nextUInt64; rng := rng'
    let a : Radix.IWord := ⟨BitVec.ofNat _ av.toNat⟩
    let b : Radix.IWord := ⟨BitVec.ofNat _ bv.toNat⟩
    assert (Radix.IWord.wrappingAdd a b == Radix.IWord.wrappingAdd b a)
      s!"IWord add comm"
    assert (Radix.IWord.wrappingMul a b == Radix.IWord.wrappingMul b a)
      s!"IWord mul comm"
    assert (Radix.IWord.band a b == Radix.IWord.band b a) s!"IWord band comm"
    assert (Radix.IWord.bxor a b == Radix.IWord.bxor b a) s!"IWord bxor comm"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.IWord := ⟨BitVec.ofNat _ av.toNat⟩
    let zero : Radix.IWord := ⟨BitVec.ofNat _ 0⟩
    assert (Radix.IWord.wrappingAdd a zero == a) s!"IWord add identity"
    assert (Radix.IWord.wrappingSub a a == zero) s!"IWord sub self"
    let neg := Radix.IWord.wrappingNeg a
    assert (Radix.IWord.wrappingAdd a neg == zero) s!"IWord neg inverse"

/-! ================================================================ -/
/-! ## Conversion Round-Trip Tests                                   -/
/-! ================================================================ -/

private def testConversionProperties : IO Unit := do
  IO.println "  Conversion round-trip properties..."
  let mut rng := PRNG.new 11

  -- Zero-extend / truncate round-trips
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    -- u8 -> u16 -> u8 round-trip
    assert (Radix.UInt16.toUInt8 (Radix.UInt8.toUInt16 a) == a)
      s!"u8->u16->u8 roundtrip: {av}"
    -- u8 -> u32 -> u8 round-trip
    assert (Radix.UInt32.toUInt8 (Radix.UInt8.toUInt32 a) == a)
      s!"u8->u32->u8 roundtrip: {av}"
    -- u8 -> u64 -> u8 round-trip
    assert (Radix.UInt64.toUInt8 (Radix.UInt8.toUInt64 a) == a)
      s!"u8->u64->u8 roundtrip: {av}"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    assert (Radix.UInt32.toUInt16 (Radix.UInt16.toUInt32 a) == a)
      s!"u16->u32->u16 roundtrip"
    assert (Radix.UInt64.toUInt16 (Radix.UInt16.toUInt64 a) == a)
      s!"u16->u64->u16 roundtrip"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    assert (Radix.UInt64.toUInt32 (Radix.UInt32.toUInt64 a) == a)
      s!"u32->u64->u32 roundtrip"

  -- Signed extend / truncate round-trips
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let a : Radix.Int8 := ⟨av⟩
    assert (Radix.Int8.toInt (Radix.Int8.fromInt (Radix.Int8.toInt a)) ==
            Radix.Int8.toInt a)
      s!"Int8 toInt/fromInt roundtrip: {av}"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let a : Radix.Int16 := ⟨av⟩
    assert (Radix.Int16.toInt (Radix.Int16.fromInt (Radix.Int16.toInt a)) ==
            Radix.Int16.toInt a)
      s!"Int16 toInt/fromInt roundtrip"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.Int32 := ⟨av⟩
    assert (Radix.Int32.toInt (Radix.Int32.fromInt (Radix.Int32.toInt a)) ==
            Radix.Int32.toInt a)
      s!"Int32 toInt/fromInt roundtrip"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.Int64 := ⟨av⟩
    assert (Radix.Int64.toInt (Radix.Int64.fromInt (Radix.Int64.toInt a)) ==
            Radix.Int64.toInt a)
      s!"Int64 toInt/fromInt roundtrip"

/-! ================================================================ -/
/-! ## Byte Order Round-Trip Tests                                   -/
/-! ================================================================ -/

private def testByteOrderProperties : IO Unit := do
  IO.println "  Byte order properties..."
  let mut rng := PRNG.new 12

  -- bswap involution: bswap(bswap(x)) = x
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    assert (Radix.UInt16.bswap (Radix.UInt16.bswap a) == a)
      s!"UInt16 bswap involution"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    assert (Radix.UInt32.bswap (Radix.UInt32.bswap a) == a)
      s!"UInt32 bswap involution"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    assert (Radix.UInt64.bswap (Radix.UInt64.bswap a) == a)
      s!"UInt64 bswap involution"

  -- BE round-trip: fromBE(toBE(x)) = x
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    assert (Radix.UInt16.fromBigEndian (Radix.UInt16.toBigEndian a) == a)
      s!"UInt16 BE round-trip"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    assert (Radix.UInt32.fromBigEndian (Radix.UInt32.toBigEndian a) == a)
      s!"UInt32 BE round-trip"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    assert (Radix.UInt64.fromBigEndian (Radix.UInt64.toBigEndian a) == a)
      s!"UInt64 BE round-trip"

  -- LE round-trip: fromLE(toLE(x)) = x
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    assert (Radix.UInt16.fromLittleEndian (Radix.UInt16.toLittleEndian a) == a)
      s!"UInt16 LE round-trip"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    assert (Radix.UInt32.fromLittleEndian (Radix.UInt32.toLittleEndian a) == a)
      s!"UInt32 LE round-trip"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    assert (Radix.UInt64.fromLittleEndian (Radix.UInt64.toLittleEndian a) == a)
      s!"UInt64 LE round-trip"

/-! ================================================================ -/
/-! ## LEB128 Round-Trip Tests                                       -/
/-! ================================================================ -/

private def testLeb128Properties : IO Unit := do
  IO.println "  LEB128 properties..."
  let mut rng := PRNG.new 13

  -- U32 encode/decode round-trip
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    let encoded := Radix.Binary.Leb128.encodeU32 a
    let decoded := Radix.Binary.Leb128.decodeU32 encoded 0
    match decoded with
    | some (val, _) => assert (val == a) s!"LEB128 U32 roundtrip: {av}"
    | none => assert false s!"LEB128 U32 decode failed: {av}"

  -- U64 encode/decode round-trip
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    let encoded := Radix.Binary.Leb128.encodeU64 a
    let decoded := Radix.Binary.Leb128.decodeU64 encoded 0
    match decoded with
    | some (val, _) => assert (val == a) s!"LEB128 U64 roundtrip: {av}"
    | none => assert false s!"LEB128 U64 decode failed: {av}"

  -- S32 encode/decode round-trip
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.Int32 := ⟨av⟩
    let encoded := Radix.Binary.Leb128.encodeS32 a
    let decoded := Radix.Binary.Leb128.decodeS32 encoded 0
    match decoded with
    | some (val, _) => assert (val == a) s!"LEB128 S32 roundtrip: {av}"
    | none => assert false s!"LEB128 S32 decode failed: {av}"

  -- S64 encode/decode round-trip
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.Int64 := ⟨av⟩
    let encoded := Radix.Binary.Leb128.encodeS64 a
    let decoded := Radix.Binary.Leb128.decodeS64 encoded 0
    match decoded with
    | some (val, _) => assert (val == a) s!"LEB128 S64 roundtrip: {av}"
    | none => assert false s!"LEB128 S64 decode failed: {av}"

  -- Encoding size bounds: U32 ≤ 5 bytes, U64 ≤ 10 bytes
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    let encoded := Radix.Binary.Leb128.encodeU32 a
    assert (encoded.size ≤ 5) s!"LEB128 U32 size bound: {av} -> {encoded.size}"
    assert (encoded.size ≥ 1) s!"LEB128 U32 non-empty: {av}"

  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    let encoded := Radix.Binary.Leb128.encodeU64 a
    assert (encoded.size ≤ 10) s!"LEB128 U64 size bound: {av} -> {encoded.size}"
    assert (encoded.size ≥ 1) s!"LEB128 U64 non-empty: {av}"

  -- Edge cases
  let enc0 := Radix.Binary.Leb128.encodeU32 ⟨0⟩
  assert (enc0.size == 1 && enc0.get! 0 == 0x00) "LEB128 U32 zero"
  let enc127 := Radix.Binary.Leb128.encodeU32 ⟨127⟩
  assert (enc127.size == 1 && enc127.get! 0 == 0x7F) "LEB128 U32 127=single byte"
  let enc0_64 := Radix.Binary.Leb128.encodeU64 ⟨0⟩
  assert (enc0_64.size == 1 && enc0_64.get! 0 == 0x00) "LEB128 U64 zero"

/-! ================================================================ -/
/-! ## Memory Buffer Property Tests                                  -/
/-! ================================================================ -/

private def testMemoryProperties : IO Unit := do
  IO.println "  Memory buffer properties..."

  -- Buffer.zeros has correct size
  for sz in [0, 1, 16, 64, 256, 1024] do
    let buf := Radix.Memory.Buffer.zeros sz
    assert (buf.size == sz) s!"Buffer.zeros size: {sz}"

  -- Write/read round-trip for U8 using checked API
  let buf := Radix.Memory.Buffer.zeros 16
  for i in [:16] do
    let val : Radix.UInt8 := ⟨(i * 17 % 256).toUInt8⟩
    match Radix.Memory.Buffer.checkedWriteU8 buf i val with
    | some buf' =>
      match Radix.Memory.Buffer.checkedReadU8 buf' i with
      | some readBack =>
        assert (readBack == val) s!"Buffer writeU8/readU8 at offset {i}"
      | none => assert false s!"Buffer checkedReadU8 failed at {i}"
    | none => assert false s!"Buffer checkedWriteU8 failed at {i}"

  -- Out-of-bounds returns none
  let buf2 := Radix.Memory.Buffer.zeros 4
  assert (Radix.Memory.Buffer.checkedReadU8 buf2 4 == none) "Buffer OOB read none"
  assert ((Radix.Memory.Buffer.checkedWriteU8 buf2 4 ⟨0⟩).isNone) "Buffer OOB write none"
  assert (Radix.Memory.Buffer.checkedReadU8 buf2 100 == none) "Buffer far OOB read none"

  -- ByteSlice: ofByteArray and checked read
  let data := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
  let slice := Radix.ByteSlice.ofByteArray data
  assert (slice.size == 8) "ByteSlice ofByteArray size"
  match Radix.ByteSlice.checkedReadU8 slice 0 with
  | some v => assert (v == ⟨1⟩) "ByteSlice readU8 at 0"
  | none => assert false "ByteSlice readU8 0 failed"
  match Radix.ByteSlice.checkedReadU8 slice 4 with
  | some v => assert (v == ⟨5⟩) "ByteSlice readU8 at 4"
  | none => assert false "ByteSlice readU8 4 failed"
  -- OOB returns none
  assert (Radix.ByteSlice.checkedReadU8 slice 8 == none) "ByteSlice OOB none"

/-! ================================================================ -/
/-! ## Edge Case Exhaustive Tests                                    -/
/-! ================================================================ -/

private def testEdgeCases : IO Unit := do
  IO.println "  Edge case exhaustive tests..."

  -- UInt8: 0, 1, MAX
  let u8_0 : Radix.UInt8 := ⟨0⟩
  let u8_1 : Radix.UInt8 := ⟨1⟩
  let u8_max : Radix.UInt8 := ⟨255⟩

  -- 0 is additive identity
  assert (Radix.UInt8.wrappingAdd u8_0 u8_max == u8_max) "u8 0+MAX=MAX"
  assert (Radix.UInt8.wrappingSub u8_0 u8_0 == u8_0) "u8 0-0=0"
  -- MAX + 1 wraps to 0
  assert (Radix.UInt8.wrappingAdd u8_max u8_1 == u8_0) "u8 MAX+1=0"
  -- MAX * 0 = 0
  assert (Radix.UInt8.wrappingMul u8_max u8_0 == u8_0) "u8 MAX*0=0"
  -- Checked overflow
  assert (Radix.UInt8.checkedAdd u8_max u8_1 == none) "u8 MAX+1 checked"
  assert (Radix.UInt8.checkedSub u8_0 u8_1 == none) "u8 0-1 checked"
  -- Saturating
  assert (Radix.UInt8.saturatingAdd u8_max u8_max == u8_max) "u8 sat MAX+MAX=MAX"
  assert (Radix.UInt8.saturatingSub u8_0 u8_max == u8_0) "u8 sat 0-MAX=0"
  -- bnot 0 = MAX, bnot MAX = 0
  assert (Radix.UInt8.bnot u8_0 == u8_max) "u8 NOT 0=MAX"
  assert (Radix.UInt8.bnot u8_max == u8_0) "u8 NOT MAX=0"
  -- clz/ctz
  assert (Radix.UInt8.clz u8_0 == 8) "u8 clz(0)=8"
  assert (Radix.UInt8.ctz u8_0 == 8) "u8 ctz(0)=8"
  assert (Radix.UInt8.clz u8_max == 0) "u8 clz(MAX)=0"
  assert (Radix.UInt8.ctz u8_max == 0) "u8 ctz(MAX)=0"

  -- UInt32: similar edge cases
  let u32_0 : Radix.UInt32 := ⟨0⟩
  let u32_1 : Radix.UInt32 := ⟨1⟩
  let u32_max : Radix.UInt32 := ⟨4294967295⟩
  assert (Radix.UInt32.wrappingAdd u32_max u32_1 == u32_0) "u32 MAX+1=0"
  assert (Radix.UInt32.checkedAdd u32_max u32_1 == none) "u32 MAX+1 checked"
  assert (Radix.UInt32.saturatingAdd u32_max u32_max == u32_max) "u32 sat MAX+MAX"
  assert (Radix.UInt32.bnot u32_0 == u32_max) "u32 NOT 0=MAX"
  assert (Radix.UInt32.clz u32_0 == 32) "u32 clz(0)=32"
  assert (Radix.UInt32.ctz u32_0 == 32) "u32 ctz(0)=32"

  -- UInt64: similar edge cases
  let u64_0 : Radix.UInt64 := ⟨0⟩
  let u64_1 : Radix.UInt64 := ⟨1⟩
  let u64_max : Radix.UInt64 := ⟨18446744073709551615⟩
  assert (Radix.UInt64.wrappingAdd u64_max u64_1 == u64_0) "u64 MAX+1=0"
  assert (Radix.UInt64.checkedAdd u64_max u64_1 == none) "u64 MAX+1 checked"
  assert (Radix.UInt64.saturatingAdd u64_max u64_max == u64_max) "u64 sat MAX+MAX"
  assert (Radix.UInt64.bnot u64_0 == u64_max) "u64 NOT 0=MAX"
  assert (Radix.UInt64.clz u64_0 == 64) "u64 clz(0)=64"
  assert (Radix.UInt64.ctz u64_0 == 64) "u64 ctz(0)=64"

  -- Int8: MIN, MAX, 0, -1 edges
  let i8_min := Radix.Int8.minVal   -- -128
  let i8_max := Radix.Int8.maxVal   -- 127
  let i8_0 : Radix.Int8 := ⟨⟨0⟩⟩
  let i8_neg1 : Radix.Int8 := ⟨⟨255⟩⟩   -- -1

  assert (Radix.Int8.wrappingAdd i8_min i8_neg1 == i8_max) "i8 MIN+(-1)=MAX"
  assert (Radix.Int8.wrappingAdd i8_max ⟨⟨1⟩⟩ == i8_min) "i8 MAX+1=MIN"
  assert (Radix.Int8.wrappingSub i8_0 i8_min == i8_min) "i8 0-MIN=MIN (wrapping)"
  assert (Radix.Int8.checkedDiv i8_min i8_neg1 == none) "i8 MIN/-1 overflow"
  assert (Radix.Int8.checkedDiv i8_max i8_0 == none) "i8 MAX/0 div by zero"

  -- Int32 edge: MIN/-1
  let i32_min := Radix.Int32.minVal
  let i32_neg1 : Radix.Int32 := ⟨⟨4294967295⟩⟩
  let i32_0 : Radix.Int32 := ⟨⟨0⟩⟩
  assert (Radix.Int32.checkedDiv i32_min i32_neg1 == none) "i32 MIN/-1 overflow"
  assert (Radix.Int32.checkedDiv i32_min i32_0 == none) "i32 MIN/0 div by zero"

  -- Int64 edge: MIN/-1
  let i64_min := Radix.Int64.minVal
  let i64_neg1 : Radix.Int64 := ⟨⟨18446744073709551615⟩⟩
  let i64_0 : Radix.Int64 := ⟨⟨0⟩⟩
  assert (Radix.Int64.checkedDiv i64_min i64_neg1 == none) "i64 MIN/-1 overflow"
  assert (Radix.Int64.checkedDiv i64_min i64_0 == none) "i64 MIN/0 div by zero"

/-! ================================================================ -/
/-! ## Binary Format Parse/Serialize Round-Trip Tests                 -/
/-! ================================================================ -/

private def testBinaryFormatProperties : IO Unit := do
  IO.println "  Binary format round-trip properties..."

  -- Simple uint32 LE parse/serialize round-trip
  let fmt := Radix.Binary.Format.u32le "val"
  let testData := ByteArray.mk #[0x12, 0x34, 0x56, 0x78]
  match Radix.Binary.parseFormat testData fmt with
  | .ok fields =>
    match Radix.Binary.serializeFormat fmt fields with
    | .ok bytes => assert (bytes == testData) "Binary u32LE round-trip"
    | .error _ => assert false "Binary u32LE serialize failed"
  | .error _ => assert false "Binary u32LE parse failed"

  -- Sequence format: u16be + u32le
  let seqFmt := Radix.Binary.Format.u16be "hdr" ++ Radix.Binary.Format.u32le "payload"
  let seqData := ByteArray.mk #[0xAB, 0xCD, 0x78, 0x56, 0x34, 0x12]
  match Radix.Binary.parseFormat seqData seqFmt with
  | .ok fields =>
    assert (fields.length == 2) "Binary seq parsed 2 fields"
    match Radix.Binary.serializeFormat seqFmt fields with
    | .ok bytes => assert (bytes == seqData) "Binary seq round-trip"
    | .error _ => assert false "Binary seq serialize failed"
  | .error _ => assert false "Binary seq parse failed"

  -- Padding format
  let padFmt := Radix.Binary.Format.byte "tag" ++ Radix.Binary.Format.pad 3
  let padData := ByteArray.mk #[0x42, 0x00, 0x00, 0x00]
  match Radix.Binary.parseFormat padData padFmt with
  | .ok fields =>
    match Radix.Binary.serializeFormat padFmt fields with
    | .ok bytes =>
      assert (bytes.size == 4) "Binary padding serialize size"
      assert (bytes.get! 0 == 0x42) "Binary padding preserves tag"
    | .error _ => assert false "Binary padding serialize failed"
  | .error _ => assert false "Binary padding parse failed"

  -- Complex: u16be + u32le + u64be + pad 2
  let complexFmt :=
    Radix.Binary.Format.u16be "a" ++
    Radix.Binary.Format.u32le "b" ++
    Radix.Binary.Format.u64be "c" ++
    Radix.Binary.Format.pad 2
  let complexData := ByteArray.mk #[
    0x00, 0x01,                         -- u16be = 1
    0x02, 0x00, 0x00, 0x00,             -- u32le = 2
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x03, -- u64be = 3
    0x00, 0x00                          -- padding
  ]
  match Radix.Binary.parseFormat complexData complexFmt with
  | .ok fields =>
    assert (fields.length == 3) "Binary complex 3 fields"
    match Radix.Binary.findField "a" fields with
    | some (Radix.Binary.FieldValue.uint16 _ v) =>
      assert (v.toNat == 1) "Binary complex field a"
    | _ => assert false "Binary complex missing a"
    match Radix.Binary.findField "b" fields with
    | some (Radix.Binary.FieldValue.uint32 _ v) =>
      assert (v.toNat == 2) "Binary complex field b"
    | _ => assert false "Binary complex missing b"
    match Radix.Binary.findField "c" fields with
    | some (Radix.Binary.FieldValue.uint64 _ v) =>
      assert (v.toNat == 3) "Binary complex field c"
    | _ => assert false "Binary complex missing c"
    match Radix.Binary.serializeFormat complexFmt fields with
    | .ok bytes => assert (bytes == complexData) "Binary complex round-trip"
    | .error _ => assert false "Binary complex serialize failed"
  | .error _ => assert false "Binary complex parse failed"

/-! ================================================================ -/
/-! ## System I/O Property Tests                                     -/
/-! ================================================================ -/

private def testSystemIOProperties : IO Unit := do
  IO.println "  System I/O properties..."

  -- Write and read back
  let testPath := "/tmp/radix_prop_test.bin"
  let mut rng := PRNG.new 14
  let mut testData := ByteArray.empty
  for _ in [:256] do
    let (rng', v) := rng.nextUInt8; rng := rng'
    testData := testData.push v

  let writeResult ← Radix.System.IO.writeFileBytes testPath testData
  match writeResult with
  | .error e => assert false s!"Write failed: {e}"
  | .ok () =>
    let readResult ← Radix.System.IO.readFileBytes testPath
    match readResult with
    | .error e => assert false s!"Read failed: {e}"
    | .ok readBack =>
      assert (readBack == testData) "System IO write/read roundtrip"
      assert (readBack.size == 256) "System IO read size"

  -- File metadata
  let metaResult ← Radix.System.IO.sysFileMeta testPath
  match metaResult with
  | .error e => assert false s!"Meta failed: {e}"
  | .ok info =>
    assert (info.size == 256) "System IO file size"
    assert (info.isFile == true) "System IO isFile"
    assert (info.isDir == false) "System IO not dir"

  -- File exists
  let existsResult ← Radix.System.IO.sysFileExists testPath
  match existsResult with
  | .error e => assert false s!"Exists failed: {e}"
  | .ok doesExist => assert (doesExist == true) "System IO file exists"

  -- Non-existent file
  let noExist ← Radix.System.IO.sysFileExists "/tmp/radix_nonexistent_file_xyz.bin"
  match noExist with
  | .error _ => pure ()  -- expected: error for non-existent
  | .ok doesExist => assert (doesExist == false) "System IO non-existent"

  -- String write/read round-trip
  let strPath := "/tmp/radix_prop_str_test.txt"
  let testStr := "Hello, Radix! 日本語テスト 🦀"
  let writeStrResult ← Radix.System.IO.writeFileString strPath testStr
  match writeStrResult with
  | .error e => assert false s!"WriteStr failed: {e}"
  | .ok () =>
    let readStrResult ← Radix.System.IO.readFileString strPath
    match readStrResult with
    | .error e => assert false s!"ReadStr failed: {e}"
    | .ok readBack => assert (readBack == testStr) "System IO string roundtrip"

  -- Cleanup
  IO.FS.removeFile testPath
  IO.FS.removeFile strPath

/-! ================================================================ -/
/-! ## Main Entry Point                                              -/
/-! ================================================================ -/

def main : IO Unit := do
  IO.println "Running Radix Phase 4 Property Tests..."
  IO.println ""

  IO.println "Unsigned integer properties:"
  testUInt8Properties
  testUInt16Properties
  testUInt32Properties
  testUInt64Properties
  IO.println ""

  IO.println "Signed integer properties:"
  testInt8Properties
  testInt16Properties
  testInt32Properties
  testInt64Properties
  IO.println ""

  IO.println "Platform-width properties:"
  testUWordProperties
  testIWordProperties
  IO.println ""

  IO.println "Cross-cutting properties:"
  testConversionProperties
  testByteOrderProperties
  testLeb128Properties
  testMemoryProperties
  IO.println ""

  IO.println "Edge cases:"
  testEdgeCases
  IO.println ""

  IO.println "Binary format:"
  testBinaryFormatProperties
  IO.println ""

  IO.println "System I/O:"
  testSystemIOProperties
  IO.println ""

  IO.println "All Radix Phase 4 Property Tests passed!"
