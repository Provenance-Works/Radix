import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Word.Int
import Radix.Word.Conv
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# Word Property-Based Tests
## Spec References
- P4-01: Algebraic properties for all word types
- Covers: commutativity, identity, self-inverse, De Morgan, rotate round-trips,
  bitReverse involution, wrapping/overflowing cross-validation, saturating bounds
-/

open ComprehensiveTests

/-! ## Generic UInt Property Runner -/

private def runUInt8Props (assert : Bool → String → IO Unit) (rng : PRNG) : IO PRNG := do
  let mut rng := rng
  for _ in [:numIter] do
    let (rng', a8) := rng.nextUInt8;  rng := rng'
    let (rng'', b8) := rng.nextUInt8;  rng := rng''
    let a : Radix.UInt8 := ⟨a8⟩
    let b : Radix.UInt8 := ⟨b8⟩
    -- Commutativity of add
    assert (Radix.UInt8.wrappingAdd a b == Radix.UInt8.wrappingAdd b a) "u8 add comm"
    -- Commutativity of mul
    assert (Radix.UInt8.wrappingMul a b == Radix.UInt8.wrappingMul b a) "u8 mul comm"
    -- Additive identity
    assert (Radix.UInt8.wrappingAdd a ⟨0⟩ == a) "u8 add identity"
    -- Multiplicative identity
    assert (Radix.UInt8.wrappingMul a ⟨1⟩ == a) "u8 mul identity"
    -- Self-subtraction = 0
    assert ((Radix.UInt8.wrappingSub a a).toNat == 0) "u8 self sub"
    -- wrapping == overflowing (result match)
    let (ovR, _) := Radix.UInt8.overflowingAdd a b
    assert (Radix.UInt8.wrappingAdd a b == ovR) "u8 wrap==ovf add"
    let (ovRS, _) := Radix.UInt8.overflowingSub a b
    assert (Radix.UInt8.wrappingSub a b == ovRS) "u8 wrap==ovf sub"
    -- Band commutativity
    assert (Radix.UInt8.band a b == Radix.UInt8.band b a) "u8 band comm"
    -- Bor commutativity
    assert (Radix.UInt8.bor a b == Radix.UInt8.bor b a) "u8 bor comm"
    -- Bxor commutativity
    assert (Radix.UInt8.bxor a b == Radix.UInt8.bxor b a) "u8 bxor comm"
    -- Bxor self = 0
    assert ((Radix.UInt8.bxor a a).toNat == 0) "u8 bxor self"
    -- Band self = self
    assert (Radix.UInt8.band a a == a) "u8 band self"
    -- Bor self = self
    assert (Radix.UInt8.bor a a == a) "u8 bor self"
    -- bnot involution
    assert (Radix.UInt8.bnot (Radix.UInt8.bnot a) == a) "u8 bnot invol"
    -- bitReverse involution
    assert (Radix.UInt8.bitReverse (Radix.UInt8.bitReverse a) == a) "u8 bitReverse invol"
    -- popcount bound
    assert ((Radix.UInt8.popcount a).toNat ≤ 8) "u8 popcount ≤ 8"
    -- hamming self = 0
    assert ((Radix.UInt8.hammingDistance a a).toNat == 0) "u8 hamming self"
    -- hammingDistance commutativity
    assert (Radix.UInt8.hammingDistance a b == Radix.UInt8.hammingDistance b a)
      "u8 hamming comm"
    -- rotate round-trip: rotl 8 positions = identity for 8-bit
    assert (Radix.UInt8.rotl (Radix.UInt8.rotl a ⟨4⟩) ⟨4⟩ == a) "u8 rotl4+rotl4"
    -- wrappingNeg involution: neg(neg(x)) == x
    assert (Radix.UInt8.wrappingNeg (Radix.UInt8.wrappingNeg a) == a) "u8 neg invol"
    -- saturating add bound: result <= MAX if a <= MAX and b <= MAX (always true)
    assert ((Radix.UInt8.saturatingAdd a b).toNat ≤ 255) "u8 sat add ≤ MAX"
    assert ((Radix.UInt8.saturatingSub a b).toNat ≤ 255) "u8 sat sub ≤ MAX"
    -- checked consistency: if checked returns some, wrapping matches
    match Radix.UInt8.checkedAdd a b with
    | some r => assert (Radix.UInt8.wrappingAdd a b == r) "u8 chk/wrap add agree"
    | none   => assert ((Radix.UInt8.overflowingAdd a b).2 == true) "u8 chk none ↔ ovf"
  return rng

private def runUInt16Props (assert : Bool → String → IO Unit) (rng : PRNG) : IO PRNG := do
  let mut rng := rng
  for _ in [:numIter] do
    let (rng', a16) := rng.nextUInt16;  rng := rng'
    let (rng'', b16) := rng.nextUInt16;  rng := rng''
    let a : Radix.UInt16 := ⟨a16⟩
    let b : Radix.UInt16 := ⟨b16⟩
    assert (Radix.UInt16.wrappingAdd a b == Radix.UInt16.wrappingAdd b a) "u16 add comm"
    assert (Radix.UInt16.wrappingMul a b == Radix.UInt16.wrappingMul b a) "u16 mul comm"
    assert (Radix.UInt16.wrappingAdd a ⟨0⟩ == a) "u16 add identity"
    assert (Radix.UInt16.wrappingMul a ⟨1⟩ == a) "u16 mul identity"
    assert ((Radix.UInt16.wrappingSub a a).toNat == 0) "u16 self sub"
    assert (Radix.UInt16.band a b == Radix.UInt16.band b a) "u16 band comm"
    assert (Radix.UInt16.bxor a b == Radix.UInt16.bxor b a) "u16 bxor comm"
    assert ((Radix.UInt16.bxor a a).toNat == 0) "u16 bxor self"
    assert (Radix.UInt16.bnot (Radix.UInt16.bnot a) == a) "u16 bnot invol"
    assert (Radix.UInt16.bitReverse (Radix.UInt16.bitReverse a) == a) "u16 bitReverse invol"
    assert ((Radix.UInt16.popcount a).toNat ≤ 16) "u16 popcount ≤ 16"
    assert ((Radix.UInt16.hammingDistance a a).toNat == 0) "u16 hamming self"
    assert (Radix.UInt16.wrappingNeg (Radix.UInt16.wrappingNeg a) == a) "u16 neg invol"
    assert ((Radix.UInt16.saturatingAdd a b).toNat ≤ 65535) "u16 sat add ≤ MAX"
    let (ovR, _) := Radix.UInt16.overflowingAdd a b
    assert (Radix.UInt16.wrappingAdd a b == ovR) "u16 wrap==ovf add"
  return rng

private def runUInt32Props (assert : Bool → String → IO Unit) (rng : PRNG) : IO PRNG := do
  let mut rng := rng
  for _ in [:numIter] do
    let (rng', a32) := rng.nextUInt32;  rng := rng'
    let (rng'', b32) := rng.nextUInt32;  rng := rng''
    let a : Radix.UInt32 := ⟨a32⟩
    let b : Radix.UInt32 := ⟨b32⟩
    assert (Radix.UInt32.wrappingAdd a b == Radix.UInt32.wrappingAdd b a) "u32 add comm"
    assert (Radix.UInt32.wrappingMul a b == Radix.UInt32.wrappingMul b a) "u32 mul comm"
    assert (Radix.UInt32.wrappingAdd a ⟨0⟩ == a) "u32 add identity"
    assert ((Radix.UInt32.wrappingSub a a).toNat == 0) "u32 self sub"
    assert (Radix.UInt32.band a b == Radix.UInt32.band b a) "u32 band comm"
    assert ((Radix.UInt32.bxor a a).toNat == 0) "u32 bxor self"
    assert (Radix.UInt32.bnot (Radix.UInt32.bnot a) == a) "u32 bnot invol"
    assert (Radix.UInt32.bitReverse (Radix.UInt32.bitReverse a) == a) "u32 bitReverse invol"
    assert ((Radix.UInt32.popcount a).toNat ≤ 32) "u32 popcount ≤ 32"
    assert (Radix.UInt32.wrappingNeg (Radix.UInt32.wrappingNeg a) == a) "u32 neg invol"
    let (ovR, _) := Radix.UInt32.overflowingAdd a b
    assert (Radix.UInt32.wrappingAdd a b == ovR) "u32 wrap==ovf add"
    match Radix.UInt32.checkedAdd a b with
    | some r => assert (Radix.UInt32.wrappingAdd a b == r) "u32 chk/wrap agree"
    | none   => assert ((Radix.UInt32.overflowingAdd a b).2 == true) "u32 chk none ↔ ovf"
  return rng

private def runUInt64Props (assert : Bool → String → IO Unit) (rng : PRNG) : IO PRNG := do
  let mut rng := rng
  for _ in [:numIter] do
    let (rng', a64) := rng.nextUInt64;  rng := rng'
    let (rng'', b64) := rng.nextUInt64;  rng := rng''
    let a : Radix.UInt64 := ⟨a64⟩
    let b : Radix.UInt64 := ⟨b64⟩
    assert (Radix.UInt64.wrappingAdd a b == Radix.UInt64.wrappingAdd b a) "u64 add comm"
    assert (Radix.UInt64.wrappingMul a b == Radix.UInt64.wrappingMul b a) "u64 mul comm"
    assert (Radix.UInt64.wrappingAdd a ⟨0⟩ == a) "u64 add identity"
    assert ((Radix.UInt64.wrappingSub a a).toNat == 0) "u64 self sub"
    assert ((Radix.UInt64.bxor a a).toNat == 0) "u64 bxor self"
    assert (Radix.UInt64.bnot (Radix.UInt64.bnot a) == a) "u64 bnot invol"
    assert (Radix.UInt64.bitReverse (Radix.UInt64.bitReverse a) == a) "u64 bitReverse invol"
    assert ((Radix.UInt64.popcount a).toNat ≤ 64) "u64 popcount ≤ 64"
    assert (Radix.UInt64.wrappingNeg (Radix.UInt64.wrappingNeg a) == a) "u64 neg invol"
    let (ovR, _) := Radix.UInt64.overflowingAdd a b
    assert (Radix.UInt64.wrappingAdd a b == ovR) "u64 wrap==ovf add"
  return rng

/-! ## Signed Property Runners -/

private def runInt8Props (assert : Bool → String → IO Unit) (rng : PRNG) : IO PRNG := do
  let mut rng := rng
  let zero := (0 : Radix.Int8)
  let one  := Radix.Int8.fromInt 1
  for _ in [:numIter] do
    let (rng', aRaw) := rng.nextUInt8;  rng := rng'
    let (rng'', bRaw) := rng.nextUInt8;  rng := rng''
    let a : Radix.Int8 := ⟨aRaw⟩
    let b : Radix.Int8 := ⟨bRaw⟩
    -- Commutativity
    assert (Radix.Int8.wrappingAdd a b == Radix.Int8.wrappingAdd b a) "i8 add comm"
    assert (Radix.Int8.wrappingMul a b == Radix.Int8.wrappingMul b a) "i8 mul comm"
    -- Identity
    assert (Radix.Int8.wrappingAdd a zero == a) "i8 add identity"
    assert (Radix.Int8.wrappingMul a one == a) "i8 mul identity"
    -- Self-sub
    assert ((Radix.Int8.wrappingSub a a).toInt == 0) "i8 self sub"
    -- wrapping neg double: neg(neg(x)) == x
    assert (Radix.Int8.wrappingNeg (Radix.Int8.wrappingNeg a) == a) "i8 neg invol"
    -- Bitwise
    assert (Radix.Int8.band a b == Radix.Int8.band b a) "i8 band comm"
    assert ((Radix.Int8.bxor a a).toInt == 0) "i8 bxor self"
    assert (Radix.Int8.bnot (Radix.Int8.bnot a) == a) "i8 bnot invol"
    -- Signed↔Unsigned round-trip
    assert (Radix.Int8.fromUInt8 (Radix.Int8.toUInt8 a) == a) "i8 s↔u round-trip"
    -- Checked/wrapping agreement
    let (ovR, _) := Radix.Int8.overflowingAdd a b
    assert (Radix.Int8.wrappingAdd a b == ovR) "i8 wrap==ovf add"
  return rng

private def runInt16Props (assert : Bool → String → IO Unit) (rng : PRNG) : IO PRNG := do
  let mut rng := rng
  let zero := (0 : Radix.Int16)
  let one  := Radix.Int16.fromInt 1
  for _ in [:numIter] do
    let (rng', aRaw) := rng.nextUInt16;  rng := rng'
    let (rng'', bRaw) := rng.nextUInt16;  rng := rng''
    let a : Radix.Int16 := ⟨aRaw⟩
    let b : Radix.Int16 := ⟨bRaw⟩
    assert (Radix.Int16.wrappingAdd a b == Radix.Int16.wrappingAdd b a) "i16 add comm"
    assert (Radix.Int16.wrappingAdd a zero == a) "i16 add identity"
    assert (Radix.Int16.wrappingMul a one == a) "i16 mul identity"
    assert ((Radix.Int16.wrappingSub a a).toInt == 0) "i16 self sub"
    assert (Radix.Int16.wrappingNeg (Radix.Int16.wrappingNeg a) == a) "i16 neg invol"
    assert (Radix.Int16.bnot (Radix.Int16.bnot a) == a) "i16 bnot invol"
    assert (Radix.Int16.fromUInt16 (Radix.Int16.toUInt16 a) == a) "i16 s↔u round-trip"
    let (ovR, _) := Radix.Int16.overflowingAdd a b
    assert (Radix.Int16.wrappingAdd a b == ovR) "i16 wrap==ovf add"
  return rng

private def runInt32Props (assert : Bool → String → IO Unit) (rng : PRNG) : IO PRNG := do
  let mut rng := rng
  let zero := (0 : Radix.Int32)
  let one  := Radix.Int32.fromInt 1
  for _ in [:numIter] do
    let (rng', aRaw) := rng.nextUInt32;  rng := rng'
    let (rng'', bRaw) := rng.nextUInt32;  rng := rng''
    let a : Radix.Int32 := ⟨aRaw⟩
    let b : Radix.Int32 := ⟨bRaw⟩
    assert (Radix.Int32.wrappingAdd a b == Radix.Int32.wrappingAdd b a) "i32 add comm"
    assert (Radix.Int32.wrappingAdd a zero == a) "i32 add identity"
    assert (Radix.Int32.wrappingMul a one == a) "i32 mul identity"
    assert ((Radix.Int32.wrappingSub a a).toInt == 0) "i32 self sub"
    assert (Radix.Int32.wrappingNeg (Radix.Int32.wrappingNeg a) == a) "i32 neg invol"
    assert (Radix.Int32.bnot (Radix.Int32.bnot a) == a) "i32 bnot invol"
    assert (Radix.Int32.fromUInt32 (Radix.Int32.toUInt32 a) == a) "i32 s↔u round-trip"
  return rng

private def runInt64Props (assert : Bool → String → IO Unit) (rng : PRNG) : IO PRNG := do
  let mut rng := rng
  let zero := (0 : Radix.Int64)
  let one  := Radix.Int64.fromInt 1
  for _ in [:numIter] do
    let (rng', aRaw) := rng.nextUInt64;  rng := rng'
    let (rng'', bRaw) := rng.nextUInt64;  rng := rng''
    let a : Radix.Int64 := ⟨aRaw⟩
    let b : Radix.Int64 := ⟨bRaw⟩
    assert (Radix.Int64.wrappingAdd a b == Radix.Int64.wrappingAdd b a) "i64 add comm"
    assert (Radix.Int64.wrappingAdd a zero == a) "i64 add identity"
    assert (Radix.Int64.wrappingMul a one == a) "i64 mul identity"
    assert ((Radix.Int64.wrappingSub a a).toInt == 0) "i64 self sub"
    assert (Radix.Int64.wrappingNeg (Radix.Int64.wrappingNeg a) == a) "i64 neg invol"
    assert (Radix.Int64.bnot (Radix.Int64.bnot a) == a) "i64 bnot invol"
    assert (Radix.Int64.fromUInt64 (Radix.Int64.toUInt64 a) == a) "i64 s↔u round-trip"
  return rng

/-! ## Conversion Property Tests -/

private def runConvProps (assert : Bool → String → IO Unit) (rng : PRNG) : IO PRNG := do
  let mut rng := rng
  for _ in [:numIter] do
    let (rng', v8) := rng.nextUInt8;  rng := rng'
    -- Zero extend then truncate = identity
    let ru8 : Radix.UInt8 := ⟨v8⟩
    assert (Radix.UInt16.toUInt8 (Radix.UInt8.toUInt16 ru8) == ru8) "u8→u16→u8"
    assert (Radix.UInt32.toUInt8 (Radix.UInt8.toUInt32 ru8) == ru8) "u8→u32→u8"
    assert (Radix.UInt64.toUInt8 (Radix.UInt8.toUInt64 ru8) == ru8) "u8→u64→u8"

    let (rng'', v16) := rng.nextUInt16;  rng := rng''
    let ru16 : Radix.UInt16 := ⟨v16⟩
    assert (Radix.UInt32.toUInt16 (Radix.UInt16.toUInt32 ru16) == ru16) "u16→u32→u16"
    assert (Radix.UInt64.toUInt16 (Radix.UInt16.toUInt64 ru16) == ru16) "u16→u64→u16"

    -- Signed round-trips
    let ri8 : Radix.Int8 := ⟨v8⟩
    assert ((Radix.Int16.toInt8 (Radix.Int8.toInt16 ri8)).toInt == ri8.toInt) "i8→i16→i8"
    assert ((Radix.Int32.toInt8 (Radix.Int8.toInt32 ri8)).toInt == ri8.toInt) "i8→i32→i8"
    assert ((Radix.Int64.toInt8 (Radix.Int8.toInt64 ri8)).toInt == ri8.toInt) "i8→i64→i8"

    -- Signed↔Unsigned
    assert (Radix.Int8.fromUInt8 (Radix.Int8.toUInt8 ri8) == ri8) "i8 s↔u"
  return rng

/-! ## Main Runner -/

def runWordPropertyTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Word property tests..."

  let mut rng := PRNG.new 12345
  rng ← runUInt8Props assert rng
  rng ← runUInt16Props assert rng
  rng ← runUInt32Props assert rng
  rng ← runUInt64Props assert rng
  rng ← runInt8Props assert rng
  rng ← runInt16Props assert rng
  rng ← runInt32Props assert rng
  rng ← runInt64Props assert rng
  let _ ← runConvProps assert rng

  c.get
