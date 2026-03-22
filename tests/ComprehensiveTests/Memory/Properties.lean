import tests.ComprehensiveTests.Framework
import Radix.Memory.Model
import Radix.Memory.Ptr
import Radix.Bytes.Spec

/-!
# Memory Property-Based Tests
## Spec References
- P4-04: Buffer write-read round-trips, size preservation, OOB consistency
-/

open ComprehensiveTests

def runMemoryPropertyTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Memory property tests..."
  let mut rng := PRNG.new 54321

  -- ## Buffer write preserves size
  for _ in [:numIter] do
    let (rng', v8) := rng.nextUInt8;  rng := rng'
    let (rng'', off) := rng.nextBounded 32;  rng := rng''
    let buf := Radix.Memory.Buffer.zeros 32
    match Radix.Memory.Buffer.checkedWriteU8 buf off.toNat ⟨v8⟩ with
    | some b' => assert (b'.size == 32) "write u8 preserves size"
    | none    => pure ()

  -- ## Buffer write-read round-trip (u8)
  for _ in [:numIter] do
    let (rng', v8) := rng.nextUInt8;  rng := rng'
    let (rng'', off) := rng.nextBounded 32;  rng := rng''
    let buf := Radix.Memory.Buffer.zeros 32
    match Radix.Memory.Buffer.checkedWriteU8 buf off.toNat ⟨v8⟩ with
    | some b' =>
      match Radix.Memory.Buffer.checkedReadU8 b' off.toNat with
      | some v => assert (v == ⟨v8⟩) "buf u8 write-read"
      | none   => assert false "buf u8 read after write none"
    | none => pure ()

  -- ## Buffer write-read round-trip (u16 LE)
  for _ in [:numIter] do
    let (rng', v16) := rng.nextUInt16;  rng := rng'
    let (rng'', off) := rng.nextBounded 31;  rng := rng''
    let buf := Radix.Memory.Buffer.zeros 32
    match Radix.Memory.Buffer.checkedWriteU16LE buf off.toNat ⟨v16⟩ with
    | some b' =>
      match Radix.Memory.Buffer.checkedReadU16LE b' off.toNat with
      | some v => assert (v == ⟨v16⟩) "buf u16 LE write-read"
      | none   => assert false "buf u16 LE read failed"
    | none => pure ()

  -- ## Buffer write-read round-trip (u32 LE)
  for _ in [:numIter] do
    let (rng', v32) := rng.nextUInt32;  rng := rng'
    let (rng'', off) := rng.nextBounded 29;  rng := rng''
    let buf := Radix.Memory.Buffer.zeros 32
    match Radix.Memory.Buffer.checkedWriteU32LE buf off.toNat ⟨v32⟩ with
    | some b' =>
      match Radix.Memory.Buffer.checkedReadU32LE b' off.toNat with
      | some v => assert (v == ⟨v32⟩) "buf u32 LE write-read"
      | none   => assert false "buf u32 LE read failed"
    | none => pure ()

  -- ## Buffer write-read round-trip (u64 LE)
  for _ in [:numIter] do
    let (rng', v64) := rng.nextUInt64;  rng := rng'
    let buf := Radix.Memory.Buffer.zeros 32
    match Radix.Memory.Buffer.checkedWriteU64LE buf 0 ⟨v64⟩ with
    | some b' =>
      match Radix.Memory.Buffer.checkedReadU64LE b' 0 with
      | some v => assert (v == ⟨v64⟩) "buf u64 LE write-read"
      | none   => assert false "buf u64 LE read failed"
    | none => assert false "buf u64 LE write failed"

  -- ## Write doesn't affect non-overlapping reads
  for _ in [:numIter] do
    let (rng', v8) := rng.nextUInt8;  rng := rng'
    let buf := Radix.Memory.Buffer.zeros 32
    match Radix.Memory.Buffer.checkedWriteU8 buf 0 ⟨v8⟩ with
    | some b' =>
      -- byte at offset 1 should still be 0
      match Radix.Memory.Buffer.checkedReadU8 b' 1 with
      | some v => assert (v.toNat == 0) "write[0] doesn't affect [1]"
      | none   => assert false "read [1] failed"
    | none => assert false "write [0] failed"

  -- ## OOB consistency: checked always returns none beyond size
  let smallBuf := Radix.Memory.Buffer.zeros 4
  for off in [4, 5, 10, 100] do
    assert (Radix.Memory.Buffer.checkedReadU8 smallBuf off == none) s!"OOB u8 {off}"
    assert (Radix.Memory.Buffer.checkedReadU16LE smallBuf off == none) s!"OOB u16 {off}"
    assert (Radix.Memory.Buffer.checkedReadU32LE smallBuf off == none) s!"OOB u32 {off}"
    assert (Radix.Memory.Buffer.checkedReadU64LE smallBuf off == none) s!"OOB u64 {off}"

  -- ## Ptr write-read round-trip property
  for _ in [:numIter] do
    let (rng', v8) := rng.nextUInt8;  rng := rng'
    let buf := Radix.Memory.Buffer.zeros 16
    let p := Radix.Memory.Ptr.ofBuffer buf 1 (by decide)
    let pw := p.writeU8 ⟨v8⟩
    assert (pw.readU8 == ⟨v8⟩) "ptr u8 write-read"

  c.get
