import tests.ComprehensiveTests.Framework
import Radix.Bytes.Order
import Radix.Bytes.Slice

/-!
# Bytes Property-Based Tests
## Spec References
- P4-03: bswap involution, endian round-trips, write-read round-trips
-/

open ComprehensiveTests

def runBytesPropertyTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Bytes property tests..."
  let mut rng := PRNG.new 99999

  -- ## bswap involution property
  for _ in [:numIter] do
    let (rng', v16) := rng.nextUInt16;  rng := rng'
    assert (Radix.UInt16.bswap (Radix.UInt16.bswap ⟨v16⟩) == ⟨v16⟩) "u16 bswap invol"

  for _ in [:numIter] do
    let (rng', v32) := rng.nextUInt32;  rng := rng'
    assert (Radix.UInt32.bswap (Radix.UInt32.bswap ⟨v32⟩) == ⟨v32⟩) "u32 bswap invol"

  for _ in [:numIter] do
    let (rng', v64) := rng.nextUInt64;  rng := rng'
    assert (Radix.UInt64.bswap (Radix.UInt64.bswap ⟨v64⟩) == ⟨v64⟩) "u64 bswap invol"

  -- ## Endian round-trip properties
  for _ in [:numIter] do
    let (rng', v16) := rng.nextUInt16;  rng := rng'
    let x : Radix.UInt16 := ⟨v16⟩
    assert (Radix.UInt16.fromBigEndian (Radix.UInt16.toBigEndian x) == x) "u16 BE round-trip"
    assert (Radix.UInt16.fromLittleEndian (Radix.UInt16.toLittleEndian x) == x) "u16 LE round-trip"
    -- toBE == bswap(toLE) on little-endian
    assert (Radix.UInt16.toBigEndian x == Radix.UInt16.bswap (Radix.UInt16.toLittleEndian x))
      "u16 toBE == bswap(toLE)"

  for _ in [:numIter] do
    let (rng', v32) := rng.nextUInt32;  rng := rng'
    let x : Radix.UInt32 := ⟨v32⟩
    assert (Radix.UInt32.fromBigEndian (Radix.UInt32.toBigEndian x) == x) "u32 BE round-trip"
    assert (Radix.UInt32.fromLittleEndian (Radix.UInt32.toLittleEndian x) == x) "u32 LE round-trip"

  for _ in [:numIter] do
    let (rng', v64) := rng.nextUInt64;  rng := rng'
    let x : Radix.UInt64 := ⟨v64⟩
    assert (Radix.UInt64.fromBigEndian (Radix.UInt64.toBigEndian x) == x) "u64 BE round-trip"
    assert (Radix.UInt64.fromLittleEndian (Radix.UInt64.toLittleEndian x) == x) "u64 LE round-trip"

  -- ## Slice write-read round-trip properties
  for _ in [:numIter] do
    let (rng', v8) := rng.nextUInt8;  rng := rng'
    let (rng'', off) := rng.nextBounded 8;  rng := rng''
    let buf := Radix.ByteSlice.zeros 8
    match Radix.ByteSlice.checkedWriteU8 buf off.toNat v8 with
    | some s' =>
      match Radix.ByteSlice.checkedReadU8 s' off.toNat with
      | some v => assert (v == v8) "slice u8 write-read"
      | none   => assert false "slice u8 read after write none"
    | none => pure ()  -- OOB is fine, offset is in [0,8)

  for _ in [:numIter] do
    let (rng', v16) := rng.nextUInt16;  rng := rng'
    let (rng'', off) := rng.nextBounded 7;  rng := rng''
    let buf := Radix.ByteSlice.zeros 8
    for e in [Radix.Bytes.Spec.Endian.little, Radix.Bytes.Spec.Endian.big] do
      match Radix.ByteSlice.checkedWriteU16 buf off.toNat ⟨v16⟩ e with
      | some s' =>
        match Radix.ByteSlice.checkedReadU16 s' off.toNat e with
        | some v => assert (v == ⟨v16⟩) "slice u16 write-read"
        | none   => assert false "slice u16 read failed"
      | none => pure ()

  for _ in [:numIter] do
    let (rng', v32) := rng.nextUInt32;  rng := rng'
    let buf := Radix.ByteSlice.zeros 8
    for e in [Radix.Bytes.Spec.Endian.little, Radix.Bytes.Spec.Endian.big] do
      match Radix.ByteSlice.checkedWriteU32 buf 0 ⟨v32⟩ e with
      | some s' =>
        match Radix.ByteSlice.checkedReadU32 s' 0 e with
        | some v => assert (v == ⟨v32⟩) "slice u32 write-read"
        | none   => assert false "slice u32 read failed"
      | none => assert false "slice u32 write failed"

  -- ## Write preserves slice size
  for _ in [:numIter] do
    let (rng', v8) := rng.nextUInt8;  rng := rng'
    let buf := Radix.ByteSlice.zeros 16
    match Radix.ByteSlice.checkedWriteU8 buf 0 v8 with
    | some s' => assert (s'.size == 16) "write preserves size"
    | none    => assert false "write to valid offset"

  c.get
