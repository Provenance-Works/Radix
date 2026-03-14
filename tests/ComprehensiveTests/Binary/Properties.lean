import tests.ComprehensiveTests.Framework
import Radix.Binary.Leb128
import Radix.Binary.Format
import Radix.Binary.Parser
import Radix.Binary.Serial

/-!
# Binary Property-Based Tests
## Spec References
- P4-05: LEB128 round-trips, encoding size bounds, format parse/serialize
-/

open ComprehensiveTests

def runBinaryPropertyTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Binary property tests..."
  let mut rng := PRNG.new 31415

  -- ## LEB128 U32 round-trip property
  for _ in [:numIterHigh] do
    let (rng', v32) := rng.nextUInt32;  rng := rng'
    let enc := Radix.Binary.Leb128.encodeU32 ⟨v32⟩
    assert (enc.size ≥ 1) "encU32 size ≥ 1"
    assert (enc.size ≤ 5) "encU32 size ≤ 5"
    match Radix.Binary.Leb128.decodeU32 enc 0 with
    | some (v, consumed) =>
      assert (v == ⟨v32⟩) "U32 LEB128 round-trip"
      assert (consumed == enc.size) "U32 consumed"
    | none => assert false "U32 decode failed"

  -- ## LEB128 U64 round-trip property
  for _ in [:numIterHigh] do
    let (rng', v64) := rng.nextUInt64;  rng := rng'
    let enc := Radix.Binary.Leb128.encodeU64 ⟨v64⟩
    assert (enc.size ≥ 1) "encU64 size ≥ 1"
    assert (enc.size ≤ 10) "encU64 size ≤ 10"
    match Radix.Binary.Leb128.decodeU64 enc 0 with
    | some (v, consumed) =>
      assert (v == ⟨v64⟩) "U64 LEB128 round-trip"
      assert (consumed == enc.size) "U64 consumed"
    | none => assert false "U64 decode failed"

  -- ## LEB128 S32 round-trip property
  for _ in [:numIterHigh] do
    let (rng', raw32) := rng.nextUInt32;  rng := rng'
    let sv : Radix.Int32 := ⟨raw32⟩
    let enc := Radix.Binary.Leb128.encodeS32 sv
    assert (enc.size ≥ 1) "encS32 size ≥ 1"
    assert (enc.size ≤ 5) "encS32 size ≤ 5"
    match Radix.Binary.Leb128.decodeS32 enc 0 with
    | some (v, consumed) =>
      assert (v.toInt == sv.toInt) "S32 LEB128 round-trip"
      assert (consumed == enc.size) "S32 consumed"
    | none => assert false "S32 decode failed"

  -- ## LEB128 S64 round-trip property
  for _ in [:numIterHigh] do
    let (rng', raw64) := rng.nextUInt64;  rng := rng'
    let sv : Radix.Int64 := ⟨raw64⟩
    let enc := Radix.Binary.Leb128.encodeS64 sv
    assert (enc.size ≥ 1) "encS64 size ≥ 1"
    assert (enc.size ≤ 10) "encS64 size ≤ 10"
    match Radix.Binary.Leb128.decodeS64 enc 0 with
    | some (v, consumed) =>
      assert (v.toInt == sv.toInt) "S64 LEB128 round-trip"
      assert (consumed == enc.size) "S64 consumed"
    | none => assert false "S64 decode failed"

  -- ## Format parse/serialize round-trip for byte format
  for _ in [:numIter] do
    let (rng', v8) := rng.nextUInt8;  rng := rng'
    let fields := [Radix.Binary.FieldValue.byte "x" ⟨v8⟩]
    match Radix.Binary.serializeFormat (.byte "x") fields with
    | .ok ba =>
      match Radix.Binary.parseFormat ba (.byte "x") with
      | .ok pf =>
        match pf with
        | [.byte _ pv] => assert (pv == ⟨v8⟩) "byte format roundtrip"
        | _ => assert false "byte format wrong shape"
      | .error _ => assert false "byte format parse error"
    | .error _ => assert false "byte format serialize error"

  -- ## Format round-trip for u16
  for _ in [:numIter] do
    let (rng', v16) := rng.nextUInt16;  rng := rng'
    let fields := [Radix.Binary.FieldValue.uint16 "x" ⟨v16⟩]
    for e in [Radix.Bytes.Spec.Endian.little, Radix.Bytes.Spec.Endian.big] do
      match Radix.Binary.serializeFormat (.uint16 "x" e) fields with
      | .ok ba =>
        match Radix.Binary.parseFormat ba (.uint16 "x" e) with
        | .ok pf =>
          match pf with
          | [.uint16 _ pv] => assert (pv == ⟨v16⟩) "u16 format roundtrip"
          | _ => assert false "u16 format wrong shape"
        | .error _ => assert false "u16 format parse error"
      | .error _ => assert false "u16 format serialize error"

  -- ## Encoding size monotonicity: larger values >= same size encoding
  let size0 := (Radix.Binary.Leb128.encodeU32 ⟨0⟩).size
  let sizeMax := (Radix.Binary.Leb128.encodeU32 ⟨0xFFFFFFFF⟩).size
  assert (sizeMax ≥ size0) "U32 enc size monotonic: max ≥ 0"

  c.get
