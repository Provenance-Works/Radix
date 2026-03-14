import tests.ComprehensiveTests.Framework
import Radix.Word.Arith
import Radix.Bit.Ops
import Radix.Bit.Scan

/-!
# Bit Scan Comprehensive Tests (clz, ctz, popcount)
## Spec References
- FR-002: Scan operations
-/

open ComprehensiveTests

def runBitScanTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Bit scan tests..."

  -- ## UInt8 Exhaustive clz for powers of 2
  assert (Radix.UInt8.clz ⟨0⟩ == 8) "u8 clz 0"
  for i in [:8] do
    let v : UInt8 := (1 <<< i.toUInt8)
    assert ((Radix.UInt8.clz ⟨v⟩).toNat == 7 - i) s!"u8 clz 2^{i}"

  -- ## UInt8 Exhaustive ctz for powers of 2
  assert (Radix.UInt8.ctz ⟨0⟩ == 8) "u8 ctz 0"
  for i in [:8] do
    let v : UInt8 := (1 <<< i.toUInt8)
    assert ((Radix.UInt8.ctz ⟨v⟩).toNat == i) s!"u8 ctz 2^{i}"

  -- ## UInt8 Exhaustive popcount for all 256 values
  for i in [:256] do
    let v : UInt8 := i.toUInt8
    let pc := Radix.UInt8.popcount ⟨v⟩
    assert (pc.toNat ≤ 8) s!"u8 popcount {i} ≤ 8"
    -- Verify: popcount(0) = 0
    if i == 0 then assert (pc == 0) "u8 popcount(0)=0"
    -- Verify: popcount(255) = 8
    if i == 255 then assert (pc == 8) "u8 popcount(255)=8"

  -- ## UInt16 Scan
  assert (Radix.UInt16.clz ⟨0⟩ == 16) "u16 clz 0"
  assert (Radix.UInt16.ctz ⟨0⟩ == 16) "u16 ctz 0"
  for i in [:16] do
    let v : UInt16 := (1 <<< i.toUInt16)
    assert ((Radix.UInt16.clz ⟨v⟩).toNat == 15 - i) s!"u16 clz 2^{i}"
    assert ((Radix.UInt16.ctz ⟨v⟩).toNat == i) s!"u16 ctz 2^{i}"
    assert (Radix.UInt16.popcount ⟨v⟩ == 1) s!"u16 popcount 2^{i}"

  -- ## UInt32 Scan
  assert (Radix.UInt32.clz ⟨0⟩ == 32) "u32 clz 0"
  assert (Radix.UInt32.ctz ⟨0⟩ == 32) "u32 ctz 0"
  for i in [:32] do
    let v : UInt32 := (1 <<< i.toUInt32)
    assert ((Radix.UInt32.clz ⟨v⟩).toNat == 31 - i) s!"u32 clz 2^{i}"
    assert ((Radix.UInt32.ctz ⟨v⟩).toNat == i) s!"u32 ctz 2^{i}"
    assert (Radix.UInt32.popcount ⟨v⟩ == 1) s!"u32 popcount 2^{i}"

  -- ## UInt64 Scan
  assert (Radix.UInt64.clz ⟨0⟩ == 64) "u64 clz 0"
  assert (Radix.UInt64.ctz ⟨0⟩ == 64) "u64 ctz 0"
  for i in [:64] do
    let v : UInt64 := (1 <<< i.toUInt64)
    assert ((Radix.UInt64.clz ⟨v⟩).toNat == 63 - i) s!"u64 clz 2^{i}"
    assert ((Radix.UInt64.ctz ⟨v⟩).toNat == i) s!"u64 ctz 2^{i}"
    assert (Radix.UInt64.popcount ⟨v⟩ == 1) s!"u64 popcount 2^{i}"

  -- ## Popcount relationship: popcount(a) + popcount(~a) == width
  for v in [(0x00 : UInt8), 0x55, 0xAA, 0xFF, 0x0F, 0xF0, 0x01, 0x80] do
    let a : Radix.UInt8 := ⟨v⟩
    assert (Radix.UInt8.popcount a + Radix.UInt8.popcount (Radix.UInt8.bnot a) == 8)
      s!"u8 popcount(x)+popcount(~x)=8 for {v}"

  for v in [(0x0000 : UInt16), 0xFFFF, 0xAAAA, 0x5555, 0x00FF, 0xFF00] do
    let a : Radix.UInt16 := ⟨v⟩
    assert (Radix.UInt16.popcount a + Radix.UInt16.popcount (Radix.UInt16.bnot a) == 16)
      s!"u16 popcount(x)+popcount(~x)=16"

  -- ## clz + ctz bounds: clz(x) + ctz(x) <= width for nonzero
  for v in [(1 : UInt8), 2, 3, 7, 15, 127, 128, 255] do
    let a : Radix.UInt8 := ⟨v⟩
    assert ((Radix.UInt8.clz a).toNat + (Radix.UInt8.ctz a).toNat ≤ 8) s!"u8 clz+ctz ≤ 8 for {v}"

  c.get
