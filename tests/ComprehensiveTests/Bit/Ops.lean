import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Bit.Ops

/-!
# Bit Operations Comprehensive Tests
## Spec References
- FR-002: Bitwise operations (band, bor, bxor, bnot, shl, shrLogical, shrArith)
-/

open ComprehensiveTests

def runBitOpsTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Bit ops tests..."

  -- ## UInt8 Bitwise Laws
  -- AND: absorption, identity, annihilation
  assert ((Radix.UInt8.band ⟨0xFF⟩ ⟨0xFF⟩).toNat == 0xFF) "u8 band self"
  assert ((Radix.UInt8.band ⟨0xFF⟩ ⟨0x00⟩).toNat == 0x00) "u8 band annihilate"
  assert ((Radix.UInt8.band ⟨0x0F⟩ ⟨0xF0⟩).toNat == 0x00) "u8 band disjoint"
  assert ((Radix.UInt8.band ⟨0x3C⟩ ⟨0x1E⟩).toNat == 0x1C) "u8 band overlap"
  -- OR: absorption, identity
  assert ((Radix.UInt8.bor ⟨0x00⟩ ⟨0x00⟩).toNat == 0x00) "u8 bor zero"
  assert ((Radix.UInt8.bor ⟨0xFF⟩ ⟨0x00⟩).toNat == 0xFF) "u8 bor identity"
  assert ((Radix.UInt8.bor ⟨0x0F⟩ ⟨0xF0⟩).toNat == 0xFF) "u8 bor complement"
  -- XOR: self-cancellation
  assert ((Radix.UInt8.bxor ⟨0xAB⟩ ⟨0xAB⟩).toNat == 0x00) "u8 bxor self"
  assert ((Radix.UInt8.bxor ⟨0x00⟩ ⟨0xAB⟩).toNat == 0xAB) "u8 bxor identity"
  -- NOT
  assert ((Radix.UInt8.bnot ⟨0x0F⟩).toNat == 0xF0) "u8 bnot 0F=F0"
  assert ((Radix.UInt8.bnot ⟨0xA5⟩).toNat == 0x5A) "u8 bnot A5=5A"

  -- ## UInt16 Bitwise
  assert ((Radix.UInt16.band ⟨0xFFFF⟩ ⟨0x0000⟩).toNat == 0) "u16 band annihilate"
  assert ((Radix.UInt16.bor ⟨0x00FF⟩ ⟨0xFF00⟩).toNat == 0xFFFF) "u16 bor fill"
  assert ((Radix.UInt16.bxor ⟨0xAAAA⟩ ⟨0x5555⟩).toNat == 0xFFFF) "u16 bxor complement"
  assert ((Radix.UInt16.bnot ⟨0x1234⟩).toNat == 0xEDCB) "u16 bnot"

  -- ## UInt32 Bitwise
  assert ((Radix.UInt32.band ⟨0xF0F0F0F0⟩ ⟨0x0F0F0F0F⟩).toNat == 0) "u32 band disjoint"
  assert ((Radix.UInt32.bor ⟨0xF0F0F0F0⟩ ⟨0x0F0F0F0F⟩).toNat == 0xFFFFFFFF) "u32 bor fill"
  assert ((Radix.UInt32.bxor ⟨0x12345678⟩ ⟨0x12345678⟩).toNat == 0) "u32 bxor self"

  -- ## De Morgan's Laws on UInt8
  -- NOT(a AND b) == (NOT a) OR (NOT b)
  let tests8 := [(0xAA : UInt8), 0x55, 0x0F, 0xF0, 0x00, 0xFF, 0x3C, 0xC3]
  for a8 in tests8 do
    for b8 in tests8 do
      let a : Radix.UInt8 := ⟨a8⟩
      let b : Radix.UInt8 := ⟨b8⟩
      let lhs := Radix.UInt8.bnot (Radix.UInt8.band a b)
      let rhs := Radix.UInt8.bor (Radix.UInt8.bnot a) (Radix.UInt8.bnot b)
      assert (lhs == rhs) s!"u8 DeMorgan1 {a8} {b8}"
      -- NOT(a OR b) == (NOT a) AND (NOT b)
      let lhs2 := Radix.UInt8.bnot (Radix.UInt8.bor a b)
      let rhs2 := Radix.UInt8.band (Radix.UInt8.bnot a) (Radix.UInt8.bnot b)
      assert (lhs2 == rhs2) s!"u8 DeMorgan2 {a8} {b8}"

  -- ## Shift Laws
  -- Shifting by type width wraps (count normalized mod width), so shl(x, width) == x
  assert ((Radix.UInt8.shl ⟨0xFF⟩ ⟨8⟩).toNat == 0xFF) "u8 shl by width wraps"
  assert ((Radix.UInt16.shl ⟨0xFFFF⟩ ⟨16⟩).toNat == 0xFFFF) "u16 shl by width wraps"
  assert ((Radix.UInt32.shl ⟨0xFFFFFFFF⟩ ⟨32⟩).toNat == 0xFFFFFFFF) "u32 shl by width wraps"
  assert ((Radix.UInt64.shl ⟨0xFFFFFFFFFFFFFFFF⟩ ⟨64⟩).toNat == 0xFFFFFFFFFFFFFFFF) "u64 shl by width wraps"

  -- Shift by 0 = identity
  assert ((Radix.UInt8.shl ⟨42⟩ ⟨0⟩).toNat == 42) "u8 shl 0"
  assert ((Radix.UInt8.shrLogical ⟨42⟩ ⟨0⟩).toNat == 42) "u8 shrL 0"
  assert ((Radix.UInt16.shl ⟨1234⟩ ⟨0⟩).toNat == 1234) "u16 shl 0"
  assert ((Radix.UInt32.shl ⟨12345⟩ ⟨0⟩).toNat == 12345) "u32 shl 0"

  -- Double shift: shr(shl(1, n), n) patterns
  for i in [:8] do
    let v := Radix.UInt8.shl ⟨1⟩ ⟨i.toUInt8⟩
    let back := Radix.UInt8.shrLogical v ⟨i.toUInt8⟩
    assert (back.toNat == 1) s!"u8 shl/shrL round-trip bit {i}"

  for i in [:16] do
    let v := Radix.UInt16.shl ⟨1⟩ ⟨i.toUInt16⟩
    let back := Radix.UInt16.shrLogical v ⟨i.toUInt16⟩
    assert (back.toNat == 1) s!"u16 shl/shrL round-trip bit {i}"

  -- ## Arithmetic Shift properties
  -- shrArith preserves sign for negative values (MSB=1)
  assert ((Radix.UInt8.shrArith ⟨0x80⟩ ⟨4⟩).toNat == 0xF8) "u8 shrA sign fill"
  assert ((Radix.UInt8.shrArith ⟨0x80⟩ ⟨7⟩).toNat == 0xFF) "u8 shrA sign fill max"
  -- shrArith == shrLogical when MSB=0
  assert ((Radix.UInt8.shrArith ⟨0x40⟩ ⟨2⟩).toNat ==
    (Radix.UInt8.shrLogical ⟨0x40⟩ ⟨2⟩).toNat) "u8 shrA==shrL when positive"
  assert ((Radix.UInt16.shrArith ⟨0x4000⟩ ⟨4⟩).toNat ==
    (Radix.UInt16.shrLogical ⟨0x4000⟩ ⟨4⟩).toNat) "u16 shrA==shrL when positive"

  c.get
