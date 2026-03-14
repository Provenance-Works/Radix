import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field

/-!
# Bit Property-Based Tests
## Spec References
- P4-01: Algebraic properties of bitwise operations
-/

open ComprehensiveTests

def runBitPropertyTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Bit property tests..."
  let mut rng := PRNG.new 77777

  for _ in [:numIter] do
    let (rng', a8) := rng.nextUInt8;  rng := rng'
    let (rng'', b8) := rng.nextUInt8;  rng := rng''
    let (rng3, c8) := rng.nextUInt8;   rng := rng3
    let a : Radix.UInt8 := ⟨a8⟩
    let b : Radix.UInt8 := ⟨b8⟩
    let cv : Radix.UInt8 := ⟨c8⟩
    -- AND associativity: (a & b) & c == a & (b & c)
    assert (Radix.UInt8.band (Radix.UInt8.band a b) cv ==
      Radix.UInt8.band a (Radix.UInt8.band b cv)) "u8 band assoc"
    -- OR associativity
    assert (Radix.UInt8.bor (Radix.UInt8.bor a b) cv ==
      Radix.UInt8.bor a (Radix.UInt8.bor b cv)) "u8 bor assoc"
    -- XOR associativity
    assert (Radix.UInt8.bxor (Radix.UInt8.bxor a b) cv ==
      Radix.UInt8.bxor a (Radix.UInt8.bxor b cv)) "u8 bxor assoc"
    -- Distributivity: a & (b | c) == (a & b) | (a & c)
    assert (Radix.UInt8.band a (Radix.UInt8.bor b cv) ==
      Radix.UInt8.bor (Radix.UInt8.band a b) (Radix.UInt8.band a cv)) "u8 distrib AND/OR"
    -- De Morgan: ~(a & b) == (~a) | (~b)
    assert (Radix.UInt8.bnot (Radix.UInt8.band a b) ==
      Radix.UInt8.bor (Radix.UInt8.bnot a) (Radix.UInt8.bnot b)) "u8 DeMorgan1"
    assert (Radix.UInt8.bnot (Radix.UInt8.bor a b) ==
      Radix.UInt8.band (Radix.UInt8.bnot a) (Radix.UInt8.bnot b)) "u8 DeMorgan2"
    -- XOR = (a | b) & ~(a & b)
    assert (Radix.UInt8.bxor a b ==
      Radix.UInt8.band (Radix.UInt8.bor a b)
        (Radix.UInt8.bnot (Radix.UInt8.band a b))) "u8 xor = or & ~and"
    -- popcount(a XOR b) == hammingDistance(a, b)
    assert (Radix.UInt8.popcount (Radix.UInt8.bxor a b) ==
      Radix.UInt8.hammingDistance a b) "u8 popcount(xor)=hamming"

  -- UInt32 property tests
  for _ in [:numIter] do
    let (rng', a32) := rng.nextUInt32;  rng := rng'
    let (rng'', b32) := rng.nextUInt32;  rng := rng''
    let a : Radix.UInt32 := ⟨a32⟩
    let b : Radix.UInt32 := ⟨b32⟩
    -- Fundamentals
    assert (Radix.UInt32.band a b == Radix.UInt32.band b a) "u32 band comm"
    assert (Radix.UInt32.bor a b == Radix.UInt32.bor b a) "u32 bor comm"
    assert (Radix.UInt32.bxor a b == Radix.UInt32.bxor b a) "u32 bxor comm"
    assert (Radix.UInt32.bnot (Radix.UInt32.bnot a) == a) "u32 bnot invol"
    assert ((Radix.UInt32.bxor a a).toNat == 0) "u32 xor self"
    -- popcount + complement
    assert (Radix.UInt32.popcount a + Radix.UInt32.popcount (Radix.UInt32.bnot a) == 32)
      "u32 popcount complement"

  -- UInt64 property tests
  for _ in [:numIter] do
    let (rng', a64) := rng.nextUInt64;  rng := rng'
    let (rng'', b64) := rng.nextUInt64;  rng := rng''
    let a : Radix.UInt64 := ⟨a64⟩
    let b : Radix.UInt64 := ⟨b64⟩
    assert (Radix.UInt64.band a b == Radix.UInt64.band b a) "u64 band comm"
    assert (Radix.UInt64.bnot (Radix.UInt64.bnot a) == a) "u64 bnot invol"
    assert ((Radix.UInt64.bxor a a).toNat == 0) "u64 xor self"
    assert (Radix.UInt64.popcount a + Radix.UInt64.popcount (Radix.UInt64.bnot a) == 64)
      "u64 popcount complement"

  -- Rotate round-trip property tests
  for _ in [:numIter] do
    let (rng', v8) := rng.nextUInt8;  rng := rng'
    let (rng'', sh) := rng.nextBounded 8;  rng := rng''
    let a : Radix.UInt8 := ⟨v8⟩
    let s : Radix.UInt8 := ⟨sh.toUInt8⟩
    -- rotl then rotr by same amount = identity
    assert (Radix.UInt8.rotr (Radix.UInt8.rotl a s) s == a) "u8 rotl/rotr round-trip"

  for _ in [:numIter] do
    let (rng', v32) := rng.nextUInt32;  rng := rng'
    let (rng'', sh) := rng.nextBounded 32;  rng := rng''
    let a : Radix.UInt32 := ⟨v32⟩
    let s : Radix.UInt32 := ⟨sh.toUInt32⟩
    assert (Radix.UInt32.rotr (Radix.UInt32.rotl a s) s == a) "u32 rotl/rotr round-trip"

  c.get
