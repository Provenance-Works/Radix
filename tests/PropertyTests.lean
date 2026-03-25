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
import Radix.Alignment
import Radix.RingBuffer
import Radix.Bitmap
import Radix.CRC
import Radix.MemoryPool
import Radix.Word.Numeric
import Radix.UTF8
import Radix.ECC
import Radix.DMA.Ops
import Radix.Timer

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

def PRNG.nextNat (rng : PRNG) (bound : Nat) : PRNG × Nat :=
  let (rng', v) := rng.nextBounded bound.toUInt64
  (rng', v.toNat)

def PRNG.nextByteList (rng : PRNG) (maxLen : Nat) : PRNG × List UInt8 :=
  Id.run do
    let (rng0, len) := rng.nextNat (maxLen + 1)
    let mut state := rng0
    let mut bytes : List UInt8 := []
    for _ in [:len] do
      let (nextState, value) := state.next
      let byte := (value % 256).toUInt8
      state := nextState
      bytes := byte :: bytes
    return (state, bytes.reverse)

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

private def assertUTF8RoundTrip (n : Nat) : IO Unit := do
  match Radix.UTF8.ofNat? n with
  | some scalar =>
    let encoded := Radix.UTF8.encodeScalar scalar
    assert (Radix.UTF8.isWellFormed encoded) s!"UTF8 scalar well formed: {n}"
    match Radix.UTF8.decodeBytes? encoded with
    | some [decoded] => assert (decoded.val == n) s!"UTF8 round-trip: {n}"
    | _ => assert false s!"UTF8 round-trip decode failed: {n}"
  | none => assert false s!"UTF8 scalar constructor failed: {n}"

private def assertUTF8ReplacementResync (bad : UInt8) : IO Unit := do
  let decoded := Radix.UTF8.decodeListReplacing [bad, 0x22]
  assert (Radix.UTF8.scalarsToNats decoded == [Radix.UTF8.replacement.val, 0x22])
    s!"UTF8 replacement resync after invalid byte: {bad.toNat}"

private def nextUTF8ScalarNat (rng : PRNG) : PRNG × Nat :=
  let (rng0, bucket) := rng.nextNat 5
  let (rng1, offset) :=
    match bucket with
    | 0 => rng0.nextNat 0x80
    | 1 => rng0.nextNat (0x800 - 0x80)
    | 2 => rng0.nextNat (0xD800 - 0x800)
    | 3 => rng0.nextNat (0x10000 - 0xE000)
    | _ => rng0.nextNat (0x110000 - 0x10000)
  let scalarNat :=
    match bucket with
    | 0 => offset
    | 1 => 0x80 + offset
    | 2 => 0x800 + offset
    | 3 => 0xE000 + offset
    | _ => 0x10000 + offset
  (rng1, scalarNat)

private def nextUTF16UnitList (rng : PRNG) (maxLen : Nat) : PRNG × List UInt16 :=
  Id.run do
    let (rng0, len) := rng.nextNat (maxLen + 1)
    let mut state := rng0
    let mut units : List UInt16 := []
    for _ in [:len] do
      let (nextState, unit) := state.nextUInt16
      state := nextState
      units := unit :: units
    return (state, units.reverse)

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
  match Radix.Binary.parseFormatExact testData fmt with
  | .ok fields =>
    match Radix.Binary.serializeFormat fmt fields with
    | .ok bytes => assert (bytes == testData) "Binary u32LE exact round-trip"
    | .error _ => assert false "Binary u32LE exact serialize failed"
  | .error _ => assert false "Binary u32LE exact parse failed"
  assert (match Radix.Binary.parseFormatExact (testData ++ ByteArray.mk #[0x00]) fmt with
    | .error (.trailingBytes _ 1) => true
    | _ => false) "Binary exact parse rejects trailing byte"

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
  match Radix.Binary.parsePrefix seqData seqFmt with
  | .ok (_, consumed) => assert (consumed == seqData.size) "Binary seq parsePrefix consumed size"
  | .error _ => assert false "Binary seq parsePrefix failed"

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

  let alignFmt := Radix.Binary.Format.byte "tag" ++ Radix.Binary.Format.align 4 ++ Radix.Binary.Format.u32le "payload"
  let alignData := ByteArray.mk #[0x42, 0x00, 0x00, 0x00, 0x78, 0x56, 0x34, 0x12]
  match Radix.Binary.parseFormatExact alignData alignFmt with
  | .ok fields =>
    match Radix.Binary.serializeFormat alignFmt fields with
    | .ok bytes => assert (bytes == alignData) "Binary align round-trip"
    | .error _ => assert false "Binary align serialize failed"
  | .error _ => assert false "Binary align parse failed"

  let blobFmt := Radix.Binary.Format.bytes "blob" 4
  let blobData := ByteArray.mk #[0xDE, 0xAD, 0xBE, 0xEF]
  match Radix.Binary.parseFormatExact blobData blobFmt with
  | .ok fields =>
    match Radix.Binary.serializeFormat blobFmt fields with
    | .ok bytes => assert (bytes == blobData) "Binary fixed bytes round-trip"
    | .error _ => assert false "Binary fixed bytes serialize failed"
  | .error _ => assert false "Binary fixed bytes parse failed"

  let constFmt := Radix.Binary.Format.constBytes (ByteArray.mk #[0x52, 0x44, 0x58, 0x21]) ++
    Radix.Binary.Format.u16le "version"
  let constData := ByteArray.mk #[0x52, 0x44, 0x58, 0x21, 0x01, 0x00]
  match Radix.Binary.parseFormatExact constData constFmt with
  | .ok fields =>
    match Radix.Binary.serializeFormat constFmt fields with
    | .ok bytes => assert (bytes == constData) "Binary const bytes round-trip"
    | .error _ => assert false "Binary const bytes serialize failed"
  | .error _ => assert false "Binary const bytes parse failed"
  assert (match Radix.Binary.parseFormatExact (ByteArray.mk #[0x52, 0x44, 0x58, 0x20, 0x01, 0x00]) constFmt with
    | .error (.constantMismatch _ _ _) => true
    | _ => false) "Binary const bytes rejects wrong magic"

  let prefixedFmt := Radix.Binary.Format.lengthPrefixedBytes "payload" 2 .little
  let mut binaryRng := PRNG.new 404
  for _ in [:64] do
    let (nextRng, payloadList) := binaryRng.nextByteList 32
    binaryRng := nextRng
    let payload := ByteArray.mk payloadList.toArray
    let fields := [Radix.Binary.FieldValue.bytes "payload" payload]
    match Radix.Binary.serializeFormat prefixedFmt fields with
    | .ok encoded =>
      match Radix.Binary.parseFormatExact encoded prefixedFmt with
      | .ok parsed =>
        match Radix.Binary.serializeFormat prefixedFmt parsed with
        | .ok roundTrip => assert (roundTrip == encoded) "Binary length-prefixed round-trip"
        | .error _ => assert false "Binary length-prefixed reserialize failed"
      | .error _ => assert false "Binary length-prefixed parse failed"
    | .error _ => assert false "Binary length-prefixed serialize failed"

  let countedFmt := Radix.Binary.Format.countPrefixedArray "items" 1 .little (Radix.Binary.Format.byte "item")
  let mut arrayRng := PRNG.new 405
  for _ in [:64] do
    let (nextRng, payloadList) := arrayRng.nextByteList 32
    arrayRng := nextRng
    let elems := payloadList.map (fun byte => [Radix.Binary.FieldValue.byte "item" ⟨byte⟩])
    let fields := [Radix.Binary.FieldValue.array "items" elems]
    match Radix.Binary.serializeFormat countedFmt fields with
    | .ok encoded =>
      match Radix.Binary.parseFormatExact encoded countedFmt with
      | .ok parsed =>
        match Radix.Binary.serializeFormat countedFmt parsed with
        | .ok roundTrip => assert (roundTrip == encoded) "Binary count-prefixed array round-trip"
        | .error _ => assert false "Binary count-prefixed array reserialize failed"
      | .error _ => assert false "Binary count-prefixed array parse failed"
    | .error _ => assert false "Binary count-prefixed array serialize failed"

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
/-! ## Alignment Property Tests                                      -/
/-! ================================================================ -/

private def testAlignmentProperties : IO Unit := do
  IO.println "  Alignment properties..."
  let mut rng := PRNG.new 100

  -- alignUp >= offset (for align > 0)
  for _ in [:numIter] do
    let (rng', ov) := rng.nextBounded 10000; rng := rng'
    let (rng', av) := rng.nextBounded 64; rng := rng'
    let offset := ov.toNat
    let align := av.toNat + 1  -- ensure > 0
    let up := Radix.Alignment.alignUp offset align
    assert (up >= offset) s!"alignUp >= offset: {offset} align {align} got {up}"

  -- alignDown <= offset (for align > 0)
  for _ in [:numIter] do
    let (rng', ov) := rng.nextBounded 10000; rng := rng'
    let (rng', av) := rng.nextBounded 64; rng := rng'
    let offset := ov.toNat
    let align := av.toNat + 1
    let down := Radix.Alignment.alignDown offset align
    assert (down <= offset) s!"alignDown <= offset: {offset} align {align} got {down}"

  -- alignDown <= alignUp (sandwich)
  for _ in [:numIter] do
    let (rng', ov) := rng.nextBounded 10000; rng := rng'
    let (rng', av) := rng.nextBounded 64; rng := rng'
    let offset := ov.toNat
    let align := av.toNat + 1
    let down := Radix.Alignment.alignDown offset align
    let up := Radix.Alignment.alignUp offset align
    assert (down <= up) s!"alignDown <= alignUp: {offset} align {align} down={down} up={up}"

  -- isAligned (alignUp offset align) for align > 0
  for _ in [:numIter] do
    let (rng', ov) := rng.nextBounded 10000; rng := rng'
    let (rng', av) := rng.nextBounded 64; rng := rng'
    let offset := ov.toNat
    let align := av.toNat + 1
    let up := Radix.Alignment.alignUp offset align
    assert (Radix.Alignment.isAligned up align)
      s!"isAligned(alignUp): offset={offset} align={align} up={up}"

  -- isAligned (alignDown offset align) for align > 0
  for _ in [:numIter] do
    let (rng', ov) := rng.nextBounded 10000; rng := rng'
    let (rng', av) := rng.nextBounded 64; rng := rng'
    let offset := ov.toNat
    let align := av.toNat + 1
    let down := Radix.Alignment.alignDown offset align
    assert (Radix.Alignment.isAligned down align)
      s!"isAligned(alignDown): offset={offset} align={align} down={down}"

  -- offset + alignPadding is aligned
  for _ in [:numIter] do
    let (rng', ov) := rng.nextBounded 10000; rng := rng'
    let (rng', av) := rng.nextBounded 64; rng := rng'
    let offset := ov.toNat
    let align := av.toNat + 1
    let pad := Radix.Alignment.alignPadding offset align
    assert (Radix.Alignment.isAligned (offset + pad) align)
      s!"offset+padding aligned: offset={offset} align={align} pad={pad}"

  -- alignUp == alignUpPow2 for power-of-two alignments
  for _ in [:numIter] do
    let (rng', ov) := rng.nextBounded 10000; rng := rng'
    let (rng', ev) := rng.nextBounded 6; rng := rng'  -- exponent 0..5 → align 1..32
    let offset := ov.toNat
    let align := 1 <<< ev.toNat  -- power of two
    let up := Radix.Alignment.alignUp offset align
    let upPow2 := Radix.Alignment.alignUpPow2 offset align
    assert (up == upPow2)
      s!"alignUp == alignUpPow2: offset={offset} align={align} up={up} upPow2={upPow2}"

  -- alignDown == alignDownPow2 for power-of-two alignments
  for _ in [:numIter] do
    let (rng', ov) := rng.nextBounded 10000; rng := rng'
    let (rng', ev) := rng.nextBounded 6; rng := rng'
    let offset := ov.toNat
    let align := 1 <<< ev.toNat
    let down := Radix.Alignment.alignDown offset align
    let downPow2 := Radix.Alignment.alignDownPow2 offset align
    assert (down == downPow2)
      s!"alignDown == alignDownPow2: offset={offset} align={align} down={down} downPow2={downPow2}"

  -- isPowerOfTwo correctness
  for _ in [:numIter] do
    let (rng', ev) := rng.nextBounded 16; rng := rng'
    let n := 1 <<< ev.toNat
    assert (Radix.Alignment.isPowerOfTwo n)
      s!"isPowerOfTwo(2^{ev.toNat}) should be true"
  -- Non-powers of two
  assert (!Radix.Alignment.isPowerOfTwo 0) "isPowerOfTwo(0) should be false"
  assert (!Radix.Alignment.isPowerOfTwo 3) "isPowerOfTwo(3) should be false"
  assert (!Radix.Alignment.isPowerOfTwo 6) "isPowerOfTwo(6) should be false"
  assert (!Radix.Alignment.isPowerOfTwo 10) "isPowerOfTwo(10) should be false"

/-! ================================================================ -/
/-! ## RingBuffer Property Tests                                     -/
/-! ================================================================ -/

private def testRingBufferProperties : IO Unit := do
  IO.println "  RingBuffer properties..."
  let mut rng := PRNG.new 200

  -- push then pop recovers value (FIFO)
  for _ in [:numIter] do
    let (rng', v) := rng.nextUInt8; rng := rng'
    let rb := Radix.RingBuffer.RingBuf.new 16
    match rb.push ⟨v⟩ with
    | some rb' =>
      match rb'.pop with
      | some (val, _) => assert (val.val == v) s!"RingBuffer push/pop roundtrip: {v}"
      | none => assert false "RingBuffer pop from non-empty failed"
    | none => assert false "RingBuffer push to empty failed"

  -- push increments count, pop decrements count
  for _ in [:numIter] do
    let (rng', v) := rng.nextUInt8; rng := rng'
    let rb := Radix.RingBuffer.RingBuf.new 16
    let countBefore := rb.count
    match rb.push ⟨v⟩ with
    | some rb' =>
      assert (rb'.count == countBefore + 1) s!"RingBuffer push increments count"
      match rb'.pop with
      | some (_, rb'') =>
        assert (rb''.count == countBefore) s!"RingBuffer pop decrements count"
      | none => assert false "RingBuffer pop after push failed"
    | none => assert false "RingBuffer push failed"

  -- empty buffer has count 0
  for _ in [:numIter] do
    let (rng', cv) := rng.nextBounded 64; rng := rng'
    let cap := cv.toNat + 1
    let rb := Radix.RingBuffer.RingBuf.new cap
    assert (rb.count == 0) s!"RingBuffer new has count 0: cap={cap}"
    assert (rb.isEmpty) s!"RingBuffer new isEmpty: cap={cap}"

  -- full buffer rejects push
  for _ in [:numIter] do
    let (rng', cv) := rng.nextBounded 15; rng := rng'
    let cap := cv.toNat + 1
    let mut rb := Radix.RingBuffer.RingBuf.new cap
    -- Fill it up
    for _ in [:cap] do
      let (rng', v) := rng.nextUInt8; rng := rng'
      match rb.push ⟨v⟩ with
      | some rb' => rb := rb'
      | none => pure ()  -- shouldn't happen until full
    assert (rb.isFull) s!"RingBuffer should be full: cap={cap}"
    -- Try one more push
    let (rng', v) := rng.nextUInt8; rng := rng'
    match rb.push ⟨v⟩ with
    | some _ => assert false s!"RingBuffer push to full should fail: cap={cap}"
    | none => pure ()  -- expected

  -- pushMany/popMany round-trip
  for _ in [:numIter] do
    let (rng', cv) := rng.nextBounded 30; rng := rng'
    let cap := cv.toNat + 5
    let rb := Radix.RingBuffer.RingBuf.new cap
    -- Generate a list of values
    let (rng', nv) := rng.nextBounded (cap.toUInt64); rng := rng'
    let numVals := nv.toNat + 1
    let mut vals : List Radix.UInt8 := []
    for _ in [:numVals] do
      let (rng', v) := rng.nextUInt8; rng := rng'
      vals := vals ++ [⟨v⟩]
    let (rb', pushed) := rb.pushMany vals
    let (popped, _) := rb'.popMany pushed
    -- Check FIFO order: first `pushed` elements match
    let expected := vals.take pushed
    assert (popped == expected)
      s!"RingBuffer pushMany/popMany roundtrip: pushed={pushed}"

  -- clear resets count to 0
  for _ in [:numIter] do
    let (rng', cv) := rng.nextBounded 30; rng := rng'
    let cap := cv.toNat + 1
    let mut rb := Radix.RingBuffer.RingBuf.new cap
    -- Push some elements
    let (rng', nv) := rng.nextBounded (cap.toUInt64); rng := rng'
    let numVals := nv.toNat
    for _ in [:numVals] do
      let (rng', v) := rng.nextUInt8; rng := rng'
      match rb.push ⟨v⟩ with
      | some rb' => rb := rb'
      | none => pure ()
    let cleared := rb.clear
    assert (cleared.count == 0) "RingBuffer clear resets count"
    assert (cleared.isEmpty) "RingBuffer clear isEmpty"

  -- capacity is preserved across push/pop
  for _ in [:numIter] do
    let (rng', cv) := rng.nextBounded 30; rng := rng'
    let cap := cv.toNat + 1
    let rb := Radix.RingBuffer.RingBuf.new cap
    let origCap := rb.capacity
    let (rng', v) := rng.nextUInt8; rng := rng'
    match rb.push ⟨v⟩ with
    | some rb' =>
      assert (rb'.capacity == origCap) "RingBuffer capacity preserved after push"
      match rb'.pop with
      | some (_, rb'') =>
        assert (rb''.capacity == origCap) "RingBuffer capacity preserved after pop"
      | none => pure ()
    | none => pure ()

/-! ================================================================ -/
/-! ## Bitmap Property Tests                                         -/
/-! ================================================================ -/

private def testBitmapProperties : IO Unit := do
  IO.println "  Bitmap properties..."
  let mut rng := PRNG.new 300

  -- set then test returns true
  for _ in [:numIter] do
    let (rng', sv) := rng.nextBounded 256; rng := rng'
    let size := sv.toNat + 1
    let (rng', iv) := rng.nextBounded size.toUInt64; rng := rng'
    let idx := iv.toNat
    let bm := Radix.Bitmap.Bitmap.zeros size
    let bm' := bm.set idx
    assert (bm'.test idx) s!"Bitmap set then test: size={size} idx={idx}"

  -- clear then test returns false
  for _ in [:numIter] do
    let (rng', sv) := rng.nextBounded 256; rng := rng'
    let size := sv.toNat + 1
    let (rng', iv) := rng.nextBounded size.toUInt64; rng := rng'
    let idx := iv.toNat
    let bm := Radix.Bitmap.Bitmap.ones size
    let bm' := bm.clear idx
    assert (!bm'.test idx) s!"Bitmap clear then test: size={size} idx={idx}"

  -- toggle then toggle is identity
  for _ in [:numIter] do
    let (rng', sv) := rng.nextBounded 256; rng := rng'
    let size := sv.toNat + 1
    let (rng', iv) := rng.nextBounded size.toUInt64; rng := rng'
    let idx := iv.toNat
    let bm := Radix.Bitmap.Bitmap.zeros size
    let bm' := bm.toggle idx |>.toggle idx
    assert (bm'.test idx == bm.test idx)
      s!"Bitmap toggle/toggle identity: size={size} idx={idx}"

  -- zeros has popcount 0
  for _ in [:numIter] do
    let (rng', sv) := rng.nextBounded 256; rng := rng'
    let size := sv.toNat + 1
    let bm := Radix.Bitmap.Bitmap.zeros size
    assert (bm.popcount == 0) s!"Bitmap zeros popcount: size={size}"

  -- set increases popcount (or keeps same if already set)
  for _ in [:numIter] do
    let (rng', sv) := rng.nextBounded 256; rng := rng'
    let size := sv.toNat + 1
    let (rng', iv) := rng.nextBounded size.toUInt64; rng := rng'
    let idx := iv.toNat
    let bm := Radix.Bitmap.Bitmap.zeros size
    let pcBefore := bm.popcount
    let bm' := bm.set idx
    let pcAfter := bm'.popcount
    assert (pcAfter >= pcBefore)
      s!"Bitmap set popcount non-decreasing: size={size} idx={idx}"

  -- out-of-bounds test returns false
  for _ in [:numIter] do
    let (rng', sv) := rng.nextBounded 128; rng := rng'
    let size := sv.toNat + 1
    let bm := Radix.Bitmap.Bitmap.ones size
    assert (!bm.test (size + 10))
      s!"Bitmap out-of-bounds test returns false: size={size}"

  -- union(a, a) == a (idempotent) — test via popcount equality
  for _ in [:numIter] do
    let (rng', sv) := rng.nextBounded 128; rng := rng'
    let size := sv.toNat + 1
    let mut bm := Radix.Bitmap.Bitmap.zeros size
    -- Set some random bits
    for _ in [:5] do
      let (rng', iv) := rng.nextBounded size.toUInt64; rng := rng'
      bm := bm.set iv.toNat
    let u := Radix.Bitmap.Bitmap.union bm bm rfl
    -- Check all bits match
    let mut allMatch := true
    for i in [:size] do
      if u.test i != bm.test i then
        allMatch := false
    assert allMatch s!"Bitmap union(a,a) idempotent: size={size}"

/-! ================================================================ -/
/-! ## CRC Property Tests                                            -/
/-! ================================================================ -/

private def testCRCProperties : IO Unit := do
  IO.println "  CRC properties..."
  let mut rng := PRNG.new 400

  -- CRC32.compute == CRC32.computeNaive
  for _ in [:numIter] do
    let (rng', lenV) := rng.nextBounded 64; rng := rng'
    let len := lenV.toNat
    let mut data := ByteArray.empty
    for _ in [:len] do
      let (rng', v) := rng.nextUInt8; rng := rng'
      data := data.push v
    let fast := Radix.CRC.CRC32.compute data
    let naive := Radix.CRC.CRC32.computeNaive data
    assert (fast == naive) s!"CRC32 table == naive: len={len}"

  -- CRC16.compute == CRC16.computeNaive
  for _ in [:numIter] do
    let (rng', lenV) := rng.nextBounded 64; rng := rng'
    let len := lenV.toNat
    let mut data := ByteArray.empty
    for _ in [:len] do
      let (rng', v) := rng.nextUInt8; rng := rng'
      data := data.push v
    let fast := Radix.CRC.CRC16.compute data
    let naive := Radix.CRC.CRC16.computeNaive data
    assert (fast == naive) s!"CRC16 table == naive: len={len}"

  -- CRC of empty data is deterministic
  let emptyData := ByteArray.empty
  let crc32a := Radix.CRC.CRC32.compute emptyData
  let crc32b := Radix.CRC.CRC32.compute emptyData
  assert (crc32a == crc32b) "CRC32 empty deterministic"
  let crc16a := Radix.CRC.CRC16.compute emptyData
  let crc16b := Radix.CRC.CRC16.compute emptyData
  assert (crc16a == crc16b) "CRC16 empty deterministic"

  -- Streaming API: init/update/finalize == compute (CRC32)
  for _ in [:numIter] do
    let (rng', lenV) := rng.nextBounded 64; rng := rng'
    let len := lenV.toNat
    let mut data := ByteArray.empty
    for _ in [:len] do
      let (rng', v) := rng.nextUInt8; rng := rng'
      data := data.push v
    let oneshot := Radix.CRC.CRC32.compute data
    let streaming := Radix.CRC.CRC32.finalize (Radix.CRC.CRC32.update Radix.CRC.CRC32.init data)
    assert (oneshot == streaming) s!"CRC32 streaming == oneshot: len={len}"

  -- Concatenation: streaming update across chunks (CRC32)
  for _ in [:numIter] do
    let (rng', lenV) := rng.nextBounded 64; rng := rng'
    let totalLen := lenV.toNat + 2
    let mut fullData := ByteArray.empty
    for _ in [:totalLen] do
      let (rng', v) := rng.nextUInt8; rng := rng'
      fullData := fullData.push v
    -- Split at a random point
    let (rng', splitV) := rng.nextBounded totalLen.toUInt64; rng := rng'
    let splitAt := splitV.toNat + 1
    let chunk1 := ByteArray.mk (fullData.toList.take splitAt |>.toArray)
    let chunk2 := ByteArray.mk (fullData.toList.drop splitAt |>.toArray)
    let oneshot := Radix.CRC.CRC32.compute fullData
    let state := Radix.CRC.CRC32.update Radix.CRC.CRC32.init chunk1
    let state := Radix.CRC.CRC32.update state chunk2
    let chunked := Radix.CRC.CRC32.finalize state
    assert (oneshot == chunked) s!"CRC32 chunked == oneshot: totalLen={totalLen} splitAt={splitAt}"

/-! ================================================================ -/
/-! ## MemoryPool Property Tests                                     -/
/-! ================================================================ -/

private def testMemoryPoolProperties : IO Unit := do
  IO.println "  MemoryPool properties..."
  let mut rng := PRNG.new 500

  -- Bump alloc returns offsets within capacity
  for _ in [:numIter] do
    let (rng', cv) := rng.nextBounded 256; rng := rng'
    let cap := cv.toNat + 16
    let (rng', sv) := rng.nextBounded (cap.toUInt64 / 2 + 1); rng := rng'
    let size := sv.toNat + 1
    let pool := Radix.MemoryPool.BumpPool.new cap
    match pool.alloc size with
    | some (offset, _) =>
      assert (offset + size <= cap)
        s!"BumpPool alloc within capacity: cap={cap} size={size} offset={offset}"
    | none => pure ()  -- may fail if size > cap, which is fine

  -- Bump alloc returns monotonically increasing offsets
  for _ in [:numIter] do
    let (rng', cv) := rng.nextBounded 128; rng := rng'
    let cap := cv.toNat + 64
    let mut pool := Radix.MemoryPool.BumpPool.new cap
    let mut lastOffset : Nat := 0
    let mut first := true
    for _ in [:5] do
      let (rng', sv) := rng.nextBounded 8; rng := rng'
      let size := sv.toNat + 1
      match pool.alloc size with
      | some (offset, pool') =>
        if !first then
          assert (offset >= lastOffset)
            s!"BumpPool monotonic offsets: last={lastOffset} curr={offset}"
        lastOffset := offset
        first := false
        pool := pool'
      | none => pure ()

  -- Bump reset restores full capacity
  for _ in [:numIter] do
    let (rng', cv) := rng.nextBounded 256; rng := rng'
    let cap := cv.toNat + 1
    let mut pool := Radix.MemoryPool.BumpPool.new cap
    -- Allocate something
    let (rng', sv) := rng.nextBounded (cap.toUInt64); rng := rng'
    let size := sv.toNat + 1
    match pool.alloc size with
    | some (_, pool') => pool := pool'
    | none => pure ()
    let resetPool := pool.reset
    assert (resetPool.remaining == cap)
      s!"BumpPool reset restores capacity: cap={cap}"
    assert (resetPool.cursor == 0)
      s!"BumpPool reset cursor to 0: cap={cap}"

  -- Bump alloc zero fails
  for _ in [:numIter] do
    let (rng', cv) := rng.nextBounded 256; rng := rng'
    let cap := cv.toNat + 1
    let pool := Radix.MemoryPool.BumpPool.new cap
    match pool.alloc 0 with
    | some _ => assert false s!"BumpPool alloc 0 should fail: cap={cap}"
    | none => pure ()  -- expected

  -- Slab alloc then free succeeds
  for _ in [:numIter] do
    let (rng', bsv) := rng.nextBounded 16; rng := rng'
    let blockSize := bsv.toNat + 1
    let (rng', bcv) := rng.nextBounded 16; rng := rng'
    let blockCount := bcv.toNat + 1
    let pool := Radix.MemoryPool.SlabPool.new blockSize blockCount (by omega)
    match pool.alloc with
    | some (blockIdx, _, pool') =>
      match pool'.free blockIdx with
      | some _ => pure ()  -- success
      | none => assert false s!"SlabPool free after alloc failed: bs={blockSize} bc={blockCount}"
    | none => assert false s!"SlabPool alloc from fresh pool failed: bs={blockSize} bc={blockCount}"

  -- Slab double-free fails
  for _ in [:numIter] do
    let (rng', bsv) := rng.nextBounded 16; rng := rng'
    let blockSize := bsv.toNat + 1
    let (rng', bcv) := rng.nextBounded 16; rng := rng'
    let blockCount := bcv.toNat + 1
    let pool := Radix.MemoryPool.SlabPool.new blockSize blockCount (by omega)
    match pool.alloc with
    | some (blockIdx, _, pool') =>
      match pool'.free blockIdx with
      | some pool'' =>
        match pool''.free blockIdx with
        | some _ => assert false s!"SlabPool double-free should fail: idx={blockIdx}"
        | none => pure ()  -- expected
      | none => assert false "SlabPool first free failed"
    | none => assert false "SlabPool alloc failed"

  -- Slab alloc from exhausted pool fails
  for _ in [:numIter] do
    let (rng', bsv) := rng.nextBounded 8; rng := rng'
    let blockSize := bsv.toNat + 1
    let (rng', bcv) := rng.nextBounded 8; rng := rng'
    let blockCount := bcv.toNat + 1
    let mut pool := Radix.MemoryPool.SlabPool.new blockSize blockCount (by omega)
    -- Exhaust all blocks
    for _ in [:blockCount] do
      match pool.alloc with
      | some (_, _, pool') => pool := pool'
      | none => pure ()
    -- One more alloc should fail
    match pool.alloc with
    | some _ => assert false s!"SlabPool alloc from exhausted should fail: bc={blockCount}"
    | none => pure ()  -- expected

/-! ================================================================ -/
/-! ## Numeric Typeclass Property Tests                              -/
/-! ================================================================ -/

private def testNumericTypeclassProperties : IO Unit := do
  IO.println "  Numeric typeclass properties..."
  let mut rng := PRNG.new 600

  -- BoundedUInt.toNat minVal == 0 (for all unsigned types)
  assert (Radix.BoundedUInt.toNat (Radix.BoundedUInt.minVal (α := Radix.UInt8)) == 0)
    "BoundedUInt UInt8 minVal == 0"
  assert (Radix.BoundedUInt.toNat (Radix.BoundedUInt.minVal (α := Radix.UInt16)) == 0)
    "BoundedUInt UInt16 minVal == 0"
  assert (Radix.BoundedUInt.toNat (Radix.BoundedUInt.minVal (α := Radix.UInt32)) == 0)
    "BoundedUInt UInt32 minVal == 0"
  assert (Radix.BoundedUInt.toNat (Radix.BoundedUInt.minVal (α := Radix.UInt64)) == 0)
    "BoundedUInt UInt64 minVal == 0"

  -- BoundedUInt.toNat maxVal == 2^bitWidth - 1
  assert (Radix.BoundedUInt.toNat (Radix.BoundedUInt.maxVal (α := Radix.UInt8)) == 255)
    "BoundedUInt UInt8 maxVal == 255"
  assert (Radix.BoundedUInt.toNat (Radix.BoundedUInt.maxVal (α := Radix.UInt16)) == 65535)
    "BoundedUInt UInt16 maxVal == 65535"
  assert (Radix.BoundedUInt.toNat (Radix.BoundedUInt.maxVal (α := Radix.UInt32)) == 4294967295)
    "BoundedUInt UInt32 maxVal == 4294967295"
  assert (Radix.BoundedUInt.toNat (Radix.BoundedUInt.maxVal (α := Radix.UInt64)) == 18446744073709551615)
    "BoundedUInt UInt64 maxVal == 2^64-1"

  -- wrappingAdd commutative (UInt8, generic via typeclass)
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt8; rng := rng'
    let (rng', bv) := rng.nextUInt8; rng := rng'
    let a : Radix.UInt8 := ⟨av⟩
    let b : Radix.UInt8 := ⟨bv⟩
    assert (Radix.BoundedUInt.wrappingAdd a b == Radix.BoundedUInt.wrappingAdd b a)
      s!"BoundedUInt UInt8 wrappingAdd comm: {av} {bv}"

  -- wrappingAdd commutative (UInt16, generic via typeclass)
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt16; rng := rng'
    let (rng', bv) := rng.nextUInt16; rng := rng'
    let a : Radix.UInt16 := ⟨av⟩
    let b : Radix.UInt16 := ⟨bv⟩
    assert (Radix.BoundedUInt.wrappingAdd a b == Radix.BoundedUInt.wrappingAdd b a)
      s!"BoundedUInt UInt16 wrappingAdd comm: {av} {bv}"

  -- wrappingAdd commutative (UInt32, generic via typeclass)
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt32; rng := rng'
    let (rng', bv) := rng.nextUInt32; rng := rng'
    let a : Radix.UInt32 := ⟨av⟩
    let b : Radix.UInt32 := ⟨bv⟩
    assert (Radix.BoundedUInt.wrappingAdd a b == Radix.BoundedUInt.wrappingAdd b a)
      s!"BoundedUInt UInt32 wrappingAdd comm: {av} {bv}"

  -- wrappingAdd commutative (UInt64, generic via typeclass)
  for _ in [:numIter] do
    let (rng', av) := rng.nextUInt64; rng := rng'
    let (rng', bv) := rng.nextUInt64; rng := rng'
    let a : Radix.UInt64 := ⟨av⟩
    let b : Radix.UInt64 := ⟨bv⟩
    assert (Radix.BoundedUInt.wrappingAdd a b == Radix.BoundedUInt.wrappingAdd b a)
      s!"BoundedUInt UInt64 wrappingAdd comm: {av} {bv}"

  -- Generic popcount consistency: BitwiseOps.popcount matches concrete popcount (UInt8)
  for _ in [:numIter] do
    let (rng', v) := rng.nextUInt8; rng := rng'
    let x : Radix.UInt8 := ⟨v⟩
    let generic := Radix.BitwiseOps.popcount x
    let concrete := Radix.UInt8.popcount x
    assert (generic == concrete)
      s!"BitwiseOps popcount UInt8 consistency: {v}"

  -- Generic popcount consistency (UInt16)
  for _ in [:numIter] do
    let (rng', v) := rng.nextUInt16; rng := rng'
    let x : Radix.UInt16 := ⟨v⟩
    let generic := Radix.BitwiseOps.popcount x
    let concrete := Radix.UInt16.popcount x
    assert (generic == concrete)
      s!"BitwiseOps popcount UInt16 consistency: {v}"

  -- Generic popcount consistency (UInt32)
  for _ in [:numIter] do
    let (rng', v) := rng.nextUInt32; rng := rng'
    let x : Radix.UInt32 := ⟨v⟩
    let generic := Radix.BitwiseOps.popcount x
    let concrete := Radix.UInt32.popcount x
    assert (generic == concrete)
      s!"BitwiseOps popcount UInt32 consistency: {v}"

  -- Generic popcount consistency (UInt64)
  for _ in [:numIter] do
    let (rng', v) := rng.nextUInt64; rng := rng'
    let x : Radix.UInt64 := ⟨v⟩
    let generic := Radix.BitwiseOps.popcount x
    let concrete := Radix.UInt64.popcount x
    assert (generic == concrete)
      s!"BitwiseOps popcount UInt64 consistency: {v}"

/-! ================================================================ -/
/-! ## v0.3.0 Property Tests                                         -/
/-! ================================================================ -/

private def testUTF8Properties : IO Unit := do
  IO.println "  UTF8 properties..."
  let boundaryVals := [0x00, 0x24, 0x41, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF]
  for n in boundaryVals do
    assertUTF8RoundTrip n

  let mut rng := PRNG.new 600
  for _ in [:numIter] do
    let (rng', bucket) := rng.nextNat 5; rng := rng'
    let (rng', offset) :=
      match bucket with
      | 0 => rng.nextNat 0x80
      | 1 => rng.nextNat (0x800 - 0x80)
      | 2 => rng.nextNat (0xD800 - 0x800)
      | 3 => rng.nextNat (0x10000 - 0xE000)
      | _ => rng.nextNat (0x110000 - 0x10000)
    rng := rng'
    let scalarNat :=
      match bucket with
      | 0 => offset
      | 1 => 0x80 + offset
      | 2 => 0x800 + offset
      | 3 => 0xE000 + offset
      | _ => 0x10000 + offset
    assertUTF8RoundTrip scalarNat

  assert (Radix.UTF8.ofNat? 0xD800 == none) "UTF8 surrogate lower bound rejected"
  assert (Radix.UTF8.ofNat? 0xDFFF == none) "UTF8 surrogate upper bound rejected"

  let guaranteedInvalidSingles : List UInt8 := [0x80, 0xBF, 0xC0, 0xC1, 0xF5, 0xFE, 0xFF]
  for bad in guaranteedInvalidSingles do
    assertUTF8ReplacementResync bad

  let mut rngBytes := PRNG.new 601
  for _ in [:numIter] do
    let (rng', bytes) := rngBytes.nextByteList 12
    rngBytes := rng'
    let specValid := Radix.UTF8.Spec.validateUTF8 bytes
    let opsValid := Radix.UTF8.isWellFormedList bytes
    assert (specValid == opsValid)
      s!"UTF8 validateUTF8 matches isWellFormedList: {bytes}"

    let replacing := Radix.UTF8.decodeListReplacing bytes
    let strictReplacing := Radix.UTF8.decodeListReplacingMaximalSubparts bytes
    assert (replacing.length ≤ bytes.length)
      s!"UTF8 replacement decode length bounded by input length: {bytes}"
    assert (strictReplacing.length ≤ replacing.length)
      s!"UTF8 maximal-subpart replacement never exceeds per-byte replacement: {bytes}"

    match Radix.UTF8.decodeNextListStep? bytes with
    | some (Radix.UTF8.Spec.DecodeStep.scalar _ consumed) =>
      assert (1 ≤ consumed && consumed ≤ 4)
        s!"UTF8 detailed step scalar width range: {bytes}"
      assert (Radix.UTF8.maximalSubpartLength bytes == consumed)
        s!"UTF8 maximalSubpartLength matches scalar width: {bytes}"
    | some (Radix.UTF8.Spec.DecodeStep.error err) =>
      assert (1 ≤ err.consumed && err.consumed ≤ Nat.min 4 bytes.length)
        s!"UTF8 detailed step error width range: {bytes}"
      assert (Radix.UTF8.maximalSubpartLength bytes == err.consumed)
        s!"UTF8 maximalSubpartLength matches error width: {bytes}"
      assert (Radix.UTF8.firstDecodeErrorList? bytes == some err)
        s!"UTF8 firstDecodeErrorList? matches detailed step: {bytes}"
    | none =>
      assert (bytes == []) "UTF8 detailed step returns none only for empty input"

    match Radix.UTF8.decodeList? bytes with
    | some decoded =>
      assert (replacing == decoded)
        s!"UTF8 replacement decode agrees on well-formed input: {bytes}"
      assert (strictReplacing == decoded)
        s!"UTF8 maximal-subpart replacement agrees on well-formed input: {bytes}"
    | none =>
      pure ()

  let mut rngStreamingValid := PRNG.new 602
  for _ in [:numIter] do
    let (rng', scalarCount0) := rngStreamingValid.nextNat 6
    rngStreamingValid := rng'
    let scalarCount := scalarCount0 + 1
    let mut scalarNats : List Nat := []
    for _ in [:scalarCount] do
      let (nextRng, scalarNat) := nextUTF8ScalarNat rngStreamingValid
      rngStreamingValid := nextRng
      scalarNats := scalarNat :: scalarNats
    let scalarNatList := scalarNats.reverse
    match Radix.UTF8.natsToScalars? scalarNatList with
    | some scalars =>
      let encoded := Radix.UTF8.encodeAllToList scalars
      let (rng', splitA) := rngStreamingValid.nextNat (encoded.length + 1)
      rngStreamingValid := rng'
      let (rng', splitB) := rngStreamingValid.nextNat (encoded.length + 1)
      rngStreamingValid := rng'
      let splitLo := Nat.min splitA splitB
      let splitHi := Nat.max splitA splitB
      let chunks :=
        [ Radix.UTF8.listToByteArray (encoded.take splitLo)
        , Radix.UTF8.listToByteArray ((encoded.drop splitLo).take (splitHi - splitLo))
        , Radix.UTF8.listToByteArray (encoded.drop splitHi)
        ]
      match Radix.UTF8.decodeChunks? chunks with
      | Except.ok decoded =>
        assert (decoded == scalars)
          s!"UTF8 streaming strict decode matches one-shot valid decode: {scalarNatList}"
      | Except.error err =>
        assert false s!"UTF8 streaming strict decode unexpectedly failed on valid data: {reprStr err}"
    | none =>
      assert false s!"UTF8 random scalar generation produced invalid scalar list: {scalarNatList}"

  let mut rngStreamingBytes := PRNG.new 603
  for _ in [:numIter] do
    let (rng', bytes) := rngStreamingBytes.nextByteList 16
    rngStreamingBytes := rng'
    let (rng', splitA) := rngStreamingBytes.nextNat (bytes.length + 1)
    rngStreamingBytes := rng'
    let (rng', splitB) := rngStreamingBytes.nextNat (bytes.length + 1)
    rngStreamingBytes := rng'
    let splitLo := Nat.min splitA splitB
    let splitHi := Nat.max splitA splitB
    let chunks :=
      [ Radix.UTF8.listToByteArray (bytes.take splitLo)
      , Radix.UTF8.listToByteArray ((bytes.drop splitLo).take (splitHi - splitLo))
      , Radix.UTF8.listToByteArray (bytes.drop splitHi)
      ]
    assert (Radix.UTF8.decodeChunksReplacing .perByte chunks == Radix.UTF8.decodeListReplacing bytes)
      s!"UTF8 streaming per-byte replacement matches one-shot decode: {bytes}"
    assert (Radix.UTF8.decodeChunksReplacing .maximalSubpart chunks ==
      Radix.UTF8.decodeListReplacingMaximalSubparts bytes)
      s!"UTF8 streaming maximal-subpart replacement matches one-shot decode: {bytes}"
    let streamingStrict :=
      match Radix.UTF8.decodeChunks? chunks with
      | Except.ok decoded => some decoded
      | Except.error _ => none
    assert (streamingStrict == Radix.UTF8.decodeList? bytes)
      s!"UTF8 streaming strict success/failure matches one-shot decode: {bytes}"

  let mut rngCursorValid := PRNG.new 604
  for _ in [:numIter] do
    let (rng', scalarCount0) := rngCursorValid.nextNat 6
    rngCursorValid := rng'
    let scalarCount := scalarCount0 + 1
    let mut scalarsAcc : List Nat := []
    for _ in [:scalarCount] do
      let (nextRng, scalarNat) := nextUTF8ScalarNat rngCursorValid
      rngCursorValid := nextRng
      scalarsAcc := scalarNat :: scalarsAcc
    let scalarNatList := scalarsAcc.reverse
    match Radix.UTF8.natsToScalars? scalarNatList with
    | some scalars =>
      let encoded := Radix.UTF8.encodeScalars scalars
      assert (Radix.UTF8.decodeWithCursor? encoded == some scalars)
        s!"UTF8 cursor strict decode matches encode/decode on valid data: {scalarNatList}"

      let byteList := Radix.UTF8.byteArrayToList encoded
      let mut boundary := 0
      for scalar in scalars do
        match Radix.UTF8.Cursor.atOffset? encoded boundary with
        | some cursor =>
          assert (Radix.UTF8.Cursor.current? cursor == some scalar)
            s!"UTF8 cursor boundary lookup returns expected scalar at offset {boundary}"
        | none =>
          assert false s!"UTF8 cursor boundary lookup rejected valid offset {boundary}"
        boundary := boundary + scalar.byteCount
      match Radix.UTF8.Cursor.atOffset? encoded boundary with
      | some cursor =>
        assert (Radix.UTF8.Cursor.byteOffset cursor == boundary)
          "UTF8 cursor boundary lookup accepts final offset"
      | none =>
        assert false "UTF8 cursor boundary lookup rejected final offset"
      for idx in List.range byteList.length do
        let byte := byteList[idx]!
        if Radix.UTF8.isContinuationByte byte then
          assert (Radix.UTF8.Cursor.atOffset? encoded idx == none)
            s!"UTF8 cursor boundary lookup rejects continuation-byte offset {idx}"
    | none =>
      assert false s!"UTF8 random cursor scalar generation produced invalid scalar list: {scalarNatList}"

  let mut rngCursorBytes := PRNG.new 605
  for _ in [:numIter] do
    let (rng', bytes) := rngCursorBytes.nextByteList 16
    rngCursorBytes := rng'
    let byteArray := Radix.UTF8.listToByteArray bytes
    let cursorStrict := Radix.UTF8.decodeWithCursor? byteArray
    assert (cursorStrict == Radix.UTF8.decodeList? bytes)
      s!"UTF8 cursor strict decode matches one-shot decode: {bytes}"
    assert (Radix.UTF8.decodeWithCursorReplacing .perByte byteArray == Radix.UTF8.decodeListReplacing bytes)
      s!"UTF8 cursor per-byte replacement matches one-shot decode: {bytes}"
    assert (Radix.UTF8.decodeWithCursorReplacing .maximalSubpart byteArray ==
      Radix.UTF8.decodeListReplacingMaximalSubparts bytes)
      s!"UTF8 cursor maximal-subpart replacement matches one-shot decode: {bytes}"

  let mut rngGraphemeValid := PRNG.new 606
  for _ in [:numIter] do
    let (rng', scalarCount0) := rngGraphemeValid.nextNat 6
    rngGraphemeValid := rng'
    let scalarCount := scalarCount0 + 1
    let mut scalarsAcc : List Nat := []
    for _ in [:scalarCount] do
      let (nextRng, scalarNat) := nextUTF8ScalarNat rngGraphemeValid
      rngGraphemeValid := nextRng
      scalarsAcc := scalarNat :: scalarsAcc
    let scalarNatList := scalarsAcc.reverse
    match Radix.UTF8.natsToScalars? scalarNatList with
    | some scalars =>
      let encoded := Radix.UTF8.encodeScalars scalars
      match Radix.UTF8.decodeGraphemes? encoded with
      | some graphemes =>
        let flattened := graphemes.foldr (fun grapheme acc => grapheme.scalars ++ acc) []
        let totalBytes := graphemes.foldl (fun acc grapheme => acc + grapheme.byteLength) 0
        assert (flattened == scalars)
          s!"UTF8 grapheme decode flattens back to original scalars: {scalarNatList}"
        assert (totalBytes == encoded.size)
          s!"UTF8 grapheme byte coverage matches encoded length: {scalarNatList}"
        assert (Radix.UTF8.graphemeCount? encoded == some graphemes.length)
          s!"UTF8 graphemeCount? matches decoded grapheme list: {scalarNatList}"
      | none =>
        assert false s!"UTF8 grapheme decode unexpectedly failed on valid input: {scalarNatList}"
    | none =>
      assert false s!"UTF8 random grapheme scalar generation produced invalid scalar list: {scalarNatList}"

  let mut rngGraphemeBytes := PRNG.new 607
  for _ in [:numIter] do
    let (rng', bytes) := rngGraphemeBytes.nextByteList 16
    rngGraphemeBytes := rng'
    let byteArray := Radix.UTF8.listToByteArray bytes
    let strictFlattened :=
      match Radix.UTF8.decodeGraphemes? byteArray with
      | some graphemes => some (graphemes.foldr (fun grapheme acc => grapheme.scalars ++ acc) [])
      | none => none
    assert (strictFlattened == Radix.UTF8.decodeWithCursor? byteArray)
      s!"UTF8 grapheme strict decode matches strict cursor flattening: {bytes}"
    let replacementFlattened :=
      (Radix.UTF8.decodeGraphemesReplacing .maximalSubpart byteArray).foldr
        (fun grapheme acc => grapheme.scalars ++ acc) []
    assert (replacementFlattened == Radix.UTF8.decodeWithCursorReplacing .maximalSubpart byteArray)
      s!"UTF8 grapheme maximal-subpart replacement matches cursor replacement flattening: {bytes}"

  let mut rngUTF16Valid := PRNG.new 608
  for _ in [:numIter] do
    let (rng', scalarCount0) := rngUTF16Valid.nextNat 6
    rngUTF16Valid := rng'
    let scalarCount := scalarCount0 + 1
    let mut scalarsAcc : List Nat := []
    for _ in [:scalarCount] do
      let (nextRng, scalarNat) := nextUTF8ScalarNat rngUTF16Valid
      rngUTF16Valid := nextRng
      scalarsAcc := scalarNat :: scalarsAcc
    let scalarNatList := scalarsAcc.reverse
    match Radix.UTF8.natsToScalars? scalarNatList with
    | some scalars =>
      let utf16Units := Radix.UTF8.encodeScalarsToUTF16 scalars
      assert (Radix.UTF8.decodeUTF16? utf16Units == some scalars)
        s!"UTF16 strict decode round-trips encoded scalars: {scalarNatList}"
      assert (Radix.UTF8.utf16ScalarCount? utf16Units == some scalars.length)
        s!"UTF16 scalar count matches scalar list length: {scalarNatList}"
      match Radix.UTF8.transcodeUTF16ToUTF8? utf16Units with
      | some utf8Bytes =>
        assert (Radix.UTF8.decodeBytes? utf8Bytes == some scalars)
          s!"UTF16 to UTF8 transcoding round-trips valid scalars: {scalarNatList}"
      | none =>
        assert false s!"UTF16 to UTF8 transcoding failed on valid scalars: {scalarNatList}"
    | none =>
      assert false s!"UTF16 random scalar generation produced invalid scalar list: {scalarNatList}"

  let mut rngUTF16Units := PRNG.new 609
  for _ in [:numIter] do
    let (rng', units) := nextUTF16UnitList rngUTF16Units 16
    rngUTF16Units := rng'
    let utf16Array := Radix.UTF8.listToUTF16Array units
    let strictUTF16 := Radix.UTF8.decodeUTF16? utf16Array
    let replacingUTF16 := Radix.UTF8.decodeUTF16Replacing utf16Array
    match strictUTF16 with
    | some scalars =>
      assert (replacingUTF16 == scalars)
        s!"UTF16 replacement decode agrees on well-formed input: {units.map UInt16.toNat}"
    | none =>
      pure ()
    let replacementUTF8 := Radix.UTF8.transcodeUTF16ToUTF8Replacing utf16Array
    assert (Radix.UTF8.decodeBytes? replacementUTF8 == some replacingUTF16)
      s!"UTF16 replacement transcoding emits decodable UTF8: {units.map UInt16.toNat}"
    let firstError := Radix.UTF8.firstUTF16DecodeErrorList? units
    match Radix.UTF8.decodeNextUTF16ListStep? units with
    | some (.error err) =>
      assert (firstError == some err)
        s!"UTF16 first error matches detailed step: {units.map UInt16.toNat}"
    | _ =>
      assert (firstError == none)
        s!"UTF16 first error absent on non-error first step: {units.map UInt16.toNat}"

  let mut rngTextOps := PRNG.new 610
  for _ in [:numIter] do
    let (rng', scalarCount0) := rngTextOps.nextNat 6
    rngTextOps := rng'
    let scalarCount := scalarCount0 + 1
    let mut scalarsAcc : List Nat := []
    for _ in [:scalarCount] do
      let (nextRng, scalarNat) := nextUTF8ScalarNat rngTextOps
      rngTextOps := nextRng
      scalarsAcc := scalarNat :: scalarsAcc
    let scalarNatList := scalarsAcc.reverse
    match Radix.UTF8.natsToScalars? scalarNatList with
    | some scalars =>
      let encoded := Radix.UTF8.encodeScalars scalars
      match Radix.UTF8.scalarBoundaryOffsets? encoded with
      | some scalarOffsets =>
        assert (scalarOffsets.head? == some 0)
          s!"UTF8 scalar boundaries start at zero: {scalarNatList}"
        assert (scalarOffsets.getLast? == some encoded.size)
          s!"UTF8 scalar boundaries end at byte size: {scalarNatList}"
        assert (scalarOffsets.length == scalars.length + 1)
          s!"UTF8 scalar boundary count matches scalar count: {scalarNatList}"
        let (rng', i0) := rngTextOps.nextNat (scalars.length + 1)
        rngTextOps := rng'
        let (rng', j0) := rngTextOps.nextNat (scalars.length + 1)
        rngTextOps := rng'
        let startIndex := Nat.min i0 j0
        let endIndex := Nat.max i0 j0
        match Radix.UTF8.sliceScalars? encoded startIndex endIndex with
        | some sliced =>
          let expected := scalars.drop startIndex |>.take (endIndex - startIndex)
          assert (Radix.UTF8.decodeBytes? sliced == some expected)
            s!"UTF8 scalar slicing matches decoded subset: {scalarNatList}"
        | none =>
          assert false s!"UTF8 scalar slicing rejected valid scalar bounds: {scalarNatList}"
      | none =>
        assert false s!"UTF8 scalar boundaries failed on valid input: {scalarNatList}"
    | none =>
      assert false s!"UTF8 random text-op scalar generation produced invalid scalars: {scalarNatList}"

  let mut rngFindScalars := PRNG.new 611
  for _ in [:numIter] do
    let (rng', prefixCount0) := rngFindScalars.nextNat 4
    rngFindScalars := rng'
    let (rng', needleCount0) := rngFindScalars.nextNat 4
    rngFindScalars := rng'
    let (rng', suffixCount0) := rngFindScalars.nextNat 4
    rngFindScalars := rng'
    let prefixCount := prefixCount0 + 1
    let needleCount := needleCount0 + 1
    let suffixCount := suffixCount0 + 1
    let mut prefixAcc : List Nat := []
    let mut needleAcc : List Nat := []
    let mut suffixAcc : List Nat := []
    for _ in [:prefixCount] do
      let (nextRng, scalarNat) := nextUTF8ScalarNat rngFindScalars
      rngFindScalars := nextRng
      prefixAcc := scalarNat :: prefixAcc
    for _ in [:needleCount] do
      let (nextRng, scalarNat) := nextUTF8ScalarNat rngFindScalars
      rngFindScalars := nextRng
      needleAcc := scalarNat :: needleAcc
    for _ in [:suffixCount] do
      let (nextRng, scalarNat) := nextUTF8ScalarNat rngFindScalars
      rngFindScalars := nextRng
      suffixAcc := scalarNat :: suffixAcc
    let prefixNats := prefixAcc.reverse
    let needleNats := needleAcc.reverse
    let suffixNats := suffixAcc.reverse
    match Radix.UTF8.natsToScalars? prefixNats, Radix.UTF8.natsToScalars? needleNats, Radix.UTF8.natsToScalars? suffixNats with
    | some prefixScalars, some needleScalars, some suffixScalars =>
      let haystackScalars := prefixScalars ++ needleScalars ++ suffixScalars
      let haystack := Radix.UTF8.encodeScalars haystackScalars
      let needle := Radix.UTF8.encodeScalars needleScalars
      let expectedOffset := (Radix.UTF8.encodeScalars prefixScalars).size
      assert (Radix.UTF8.findScalars? haystack needle == some expectedOffset)
        s!"UTF8 scalar search finds the inserted needle: prefix={prefixNats} needle={needleNats} suffix={suffixNats}"
      assert (Radix.UTF8.containsScalars haystack needle)
        s!"UTF8 scalar containment reports the inserted needle: prefix={prefixNats} needle={needleNats} suffix={suffixNats}"
      assert (Radix.UTF8.startsWithScalars haystack (Radix.UTF8.encodeScalars prefixScalars) == true)
        s!"UTF8 scalar prefix check accepts valid prefix: {prefixNats}"
      assert (Radix.UTF8.endsWithScalars haystack (Radix.UTF8.encodeScalars suffixScalars) == true)
        s!"UTF8 scalar suffix check accepts valid suffix: {suffixNats}"
    | _, _, _ =>
      assert false "UTF8 scalar search property generated invalid scalar sequence"

private def testECCProperties : IO Unit := do
  IO.println "  ECC properties..."
  let mut rng := PRNG.new 700
  let bitMasks : List UInt8 := [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40]
  for _ in [:numIter] do
    let (rng', v) := rng.nextUInt8; rng := rng'
    let nibble : Radix.ECC.Nibble := ⟨v.toNat % 16, by omega⟩
    let encoded := Radix.ECC.encodeNibble nibble
    assert (Radix.ECC.decode encoded == (some (nibble.val.toUInt8 : UInt8)))
      s!"ECC decode(encode): {nibble.val}"
    assert (Radix.ECC.check encoded) s!"ECC parity holds: {nibble.val}"
    for mask in bitMasks do
      let corrupted := encoded ^^^ mask
      assert (Radix.ECC.decode corrupted == none)
        s!"ECC decode rejects parity-invalid word: {nibble.val} mask={mask.toNat}"
      match (Radix.ECC.correct corrupted : Option UInt8) with
      | some corrected =>
        assert (Radix.ECC.decode corrected == (some (nibble.val.toUInt8 : UInt8)))
          s!"ECC single-bit correction: {nibble.val} mask={mask.toNat}"
        assert (Radix.ECC.check corrected)
          s!"ECC corrected parity holds: {nibble.val} mask={mask.toNat}"
      | none =>
        assert false s!"ECC correction unexpectedly failed: {nibble.val} mask={mask.toNat}"
    match (Radix.ECC.decode (encoded ||| 0x80) : Option UInt8) with
    | none => pure ()
    | some _ => assert false s!"ECC reject high-bit input: {nibble.val}"

private def testDMAProperties : IO Unit := do
  IO.println "  DMA properties..."
  let valid : Radix.DMA.Descriptor :=
    { source := { start := 0, size := 4 }
    , destination := { start := 0, size := 4 }
    , order := .seqCst
    , coherence := .nonCoherent
    , atomicity := .burst 2
    }
  assert (Radix.DMA.isValid valid) "DMA valid descriptor"
  assert (Radix.DMA.stepCount valid == 2) "DMA burst step count"

  let src := ByteArray.mk ((List.range 32).map (fun n => ((n * 7 + 3) % 256).toUInt8)).toArray
  let dst := ByteArray.mk ((List.replicate 32 (0 : UInt8))).toArray
  let mut rng := PRNG.new 801
  for _ in [:numIter] do
    let (rng', srcStart) := rng.nextNat 24; rng := rng'
    let (rng', dstStart) := rng.nextNat 24; rng := rng'
    let (rng', len0) := rng.nextNat 8; rng := rng'
    let len := len0 + 1
    let descriptor : Radix.DMA.Descriptor :=
      { source := { start := srcStart, size := len }
      , destination := { start := dstStart, size := len }
      , order := .seqCst
      , coherence := .nonCoherent
      , atomicity := .burst (Nat.min len 4)
      }
    assert (Radix.DMA.isValid descriptor) s!"DMA random descriptor valid: {srcStart},{dstStart},{len}"
    match Radix.DMA.simulateCopy src dst descriptor with
    | some bytes =>
      let srcList := src.toList
      let dstList := dst.toList
      let copied := (srcList.drop srcStart).take len
      let expected := dstList.take dstStart ++ copied ++ dstList.drop (dstStart + len)
      assert (bytes.size == dst.size) s!"DMA preserves destination size: {srcStart},{dstStart},{len}"
      assert (bytes.toList == expected) s!"DMA copies exact slice: {srcStart},{dstStart},{len}"
    | none => assert false s!"DMA simulation failed: {srcStart},{dstStart},{len}"

  let invalidBurst : Radix.DMA.Descriptor := { valid with atomicity := .burst 0, coherence := .coherent }
  assert (!Radix.DMA.isValid invalidBurst) "DMA rejects zero-sized burst"
  let invalidOrder : Radix.DMA.Descriptor := { valid with order := .acquire }
  assert (!Radix.DMA.isValid invalidOrder) "DMA rejects non-seqCst non-coherent order"

private def testRegionAlgebraProperties : IO Unit := do
  IO.println "  Region algebra properties..."
  let zeroInside : Radix.Memory.Spec.Region := { start := 12, size := 0 }
  let covering : Radix.Memory.Spec.Region := { start := 10, size := 6 }
  assert (!decide (Radix.Memory.Spec.Region.intersects zeroInside covering))
    "zero-sized region does not intersect covering region"
  assert (Radix.Memory.Spec.Region.union? zeroInside covering == some covering)
    "union with empty left region returns right operand"
  assert (Radix.Memory.Spec.Region.union? covering zeroInside == some covering)
    "union with empty right region returns left operand"
  assert (Radix.Memory.Spec.Region.difference covering zeroInside == [covering])
    "difference by empty region leaves source unchanged"
  let mut rng := PRNG.new 800
  for _ in [:numIter] do
    let (rng', s0) := rng.nextNat 128; rng := rng'
    let (rng', len0) := rng.nextNat 32; rng := rng'
    let (rng', s1) := rng.nextNat 128; rng := rng'
    let (rng', len1) := rng.nextNat 32; rng := rng'
    let a : Radix.Memory.Spec.Region := { start := s0, size := len0 + 1 }
    let b : Radix.Memory.Spec.Region := { start := s1, size := len1 + 1 }
    let inter := Radix.Memory.Spec.Region.intersection a b
    let diff := Radix.Memory.Spec.Region.difference a b
    if !decide (Radix.Memory.Spec.Region.intersects a b) then
      assert (inter == Radix.Memory.Spec.Region.empty)
        s!"disjoint intersection canonical empty: {reprStr a} {reprStr b}"
    else
      pure ()
    if (Radix.Memory.Spec.Region.union? a b).isSome || inter.size > 0 then
      assert (Radix.Memory.Spec.Region.contains a inter)
        s!"intersection contained in left: {reprStr a} {reprStr b}"
      assert (Radix.Memory.Spec.Region.contains b inter)
        s!"intersection contained in right: {reprStr a} {reprStr b}"
    else
      pure ()
    assert (diff.length ≤ 2) s!"difference bounded pieces: {reprStr a} {reprStr b}"
    for piece in diff do
      assert (Radix.Memory.Spec.Region.contains a piece)
        s!"difference piece contained in left: {reprStr a} {reprStr piece}"
      assert (decide (0 < piece.size))
        s!"difference piece non-empty: {reprStr piece}"
      assert (Radix.Memory.Spec.Region.disjoint piece b)
        s!"difference piece disjoint from right: {reprStr piece} {reprStr b}"

private def testTimerProperties : IO Unit := do
  IO.println "  Timer properties..."
  let mut rng := PRNG.new 900
  assert (Radix.Timer.hasExpired Radix.Timer.zero (Radix.Timer.after Radix.Timer.zero 0))
    "zero-timeout deadline expires immediately"
  for _ in [:numIter] do
    let (rng', startTicks) := rng.nextNat 1000; rng := rng'
    let (rng', delta) := rng.nextNat 100; rng := rng'
    let start : Radix.Timer.Clock := { ticks := startTicks }
    let finish := Radix.Timer.tick start delta
    assert (Radix.Timer.elapsed start finish == delta)
      s!"timer elapsed: {startTicks} {delta}"
    assert (Radix.Timer.elapsed? start finish == some delta)
      s!"timer checked elapsed: {startTicks} {delta}"
    let deadline := Radix.Timer.after start (delta + 1)
    assert (Radix.Timer.remaining finish deadline == 1)
      s!"deadline remaining before expiry: {startTicks} {delta}"
    assert (Radix.Timer.hasExpired finish deadline == false)
      s!"deadline still future: {startTicks} {delta}"
    let exact := Radix.Timer.tick start (delta + 1)
    assert (Radix.Timer.hasExpired exact deadline)
      s!"deadline expires exactly on boundary: {startTicks} {delta}"
    assert (Radix.Timer.remaining exact deadline == 0)
      s!"remaining saturates at expiry: {startTicks} {delta}"
    assert (Radix.Timer.elapsed? exact start == none)
      s!"timer checked elapsed rejects reversed observations: {startTicks} {delta}"

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

  IO.println "Alignment:"
  testAlignmentProperties
  IO.println ""

  IO.println "Ring buffer:"
  testRingBufferProperties
  IO.println ""

  IO.println "Bitmap:"
  testBitmapProperties
  IO.println ""

  IO.println "CRC:"
  testCRCProperties
  IO.println ""

  IO.println "Memory pool:"
  testMemoryPoolProperties
  IO.println ""

  IO.println "Numeric typeclasses:"
  testNumericTypeclassProperties
  IO.println ""

  IO.println "v0.3.0 modules:"
  testUTF8Properties
  testECCProperties
  testDMAProperties
  testRegionAlgebraProperties
  testTimerProperties
  IO.println ""

  IO.println "All Radix Phase 4 Property Tests passed!"
