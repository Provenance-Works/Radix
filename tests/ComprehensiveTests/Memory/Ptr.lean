import tests.ComprehensiveTests.Framework
import Radix.Memory.Ptr

/-!
# Memory Pointer Tests
## Spec References
- FR-004: Ptr construction, advance, retreat, cast, read/write
-/

open ComprehensiveTests

def runMemoryPtrTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Memory pointer tests..."

  -- ## Ptr construction via ofBuffer
  let buf := Radix.Memory.Buffer.zeros 32

  -- Create Ptr 1 at offset 0
  let p1 := Radix.Memory.Ptr.ofBuffer buf 1 (by native_decide)
  assert (p1.offset == 0) "Ptr1 offset 0"

  -- Create Ptr 2 at offset 0
  let p2 := Radix.Memory.Ptr.ofBuffer buf 2 (by native_decide)
  assert (p2.offset == 0) "Ptr2 offset 0"

  -- Ptr 4 and Ptr 8
  let p4 := Radix.Memory.Ptr.ofBuffer buf 4 (by native_decide)
  let p8 := Radix.Memory.Ptr.ofBuffer buf 8 (by native_decide)
  assert (p4.offset == 0) "Ptr4 offset 0"
  assert (p8.offset == 0) "Ptr8 offset 0"

  -- ## Ptr readU8 / writeU8
  let val := p1.readU8
  assert (val.toNat == 0) "Ptr1 readU8 zeros"

  let p1w := p1.writeU8 ⟨0xAB⟩
  assert (p1w.readU8.toNat == 0xAB) "Ptr1 writeU8-readU8"

  -- ## Ptr readU16/writeU16
  let v16 := p2.readU16LE
  assert (v16.toNat == 0) "Ptr2 readU16LE zeros"

  let p2w := p2.writeU16LE ⟨0x1234⟩
  assert (p2w.readU16LE == ⟨0x1234⟩) "Ptr2 writeU16LE-readU16LE"

  let p2wBE := p2.writeU16BE ⟨0xABCD⟩
  assert (p2wBE.readU16BE == ⟨0xABCD⟩) "Ptr2 writeU16BE-readU16BE"

  -- ## Ptr readU32/writeU32
  let p4w := p4.writeU32LE ⟨0xDEADBEEF⟩
  assert (p4w.readU32LE == ⟨0xDEADBEEF⟩) "Ptr4 writeU32LE-readU32LE"

  let p4wBE := p4.writeU32BE ⟨0x12345678⟩
  assert (p4wBE.readU32BE == ⟨0x12345678⟩) "Ptr4 writeU32BE-readU32BE"

  -- ## Ptr readU64/writeU64
  let p8w := p8.writeU64LE ⟨0x0102030405060708⟩
  assert (p8w.readU64LE == ⟨0x0102030405060708⟩) "Ptr8 writeU64LE-readU64LE"

  let p8wBE := p8.writeU64BE ⟨0xCAFEBABEDEADFACE⟩
  assert (p8wBE.readU64BE == ⟨0xCAFEBABEDEADFACE⟩) "Ptr8 writeU64BE-readU64BE"

  -- ## Ptr advance
  let pAdv := p1.advance 5 (by native_decide)
  assert (pAdv.offset == 5) "Ptr advance offset"

  let pAdv2 := pAdv.advance 3 (by native_decide)
  assert (pAdv2.offset == 8) "Ptr double advance"

  -- Advance and write
  let pAdvW := pAdv.writeU8 ⟨0x42⟩
  assert (pAdvW.readU8.toNat == 0x42) "Ptr advance write-read"

  -- ## Ptr retreat
  let pRet := pAdv.retreat 3 (by native_decide) (by native_decide)
  assert (pRet.offset == 2) "Ptr retreat offset"

  -- ## Ptr cast
  let pCast := p1.cast 4 (by native_decide)
  assert (pCast.offset == 0) "Ptr cast offset preserved"
  let v32 := pCast.readU32LE
  assert (v32.toNat == 0) "Ptr cast readU32LE"

  -- ## Ptr sequential writes
  -- Write bytes at sequential positions using advance
  let buf2 := Radix.Memory.Buffer.zeros 8
  let base := Radix.Memory.Ptr.ofBuffer buf2 1 (by native_decide)
  let base := base.writeU8 ⟨0x10⟩
  let next := base.advance 1 (by native_decide)
  let next := next.writeU8 ⟨0x20⟩
  let next2 := next.advance 1 (by native_decide)
  let next2 := next2.writeU8 ⟨0x30⟩
  -- Read back from beginning
  let rd := Radix.Memory.Ptr.ofBuffer next2.buf 1 (by native_decide)
  assert (rd.readU8.toNat == 0x10) "sequential write [0]"
  let rd1 := rd.advance 1 (by native_decide)
  assert (rd1.readU8.toNat == 0x20) "sequential write [1]"
  let rd2 := rd1.advance 1 (by native_decide)
  assert (rd2.readU8.toNat == 0x30) "sequential write [2]"

  c.get
