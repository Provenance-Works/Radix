import tests.ComprehensiveTests.Framework
import Radix.CRC

/-!
# CRC Tests
## Spec References
- v0.2.0: CRC-32 / CRC-16 with table-driven implementation
-/

open ComprehensiveTests
open Radix.CRC

def runCRCTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    CRC tests..."

  -- ## CRC-32 known test vectors
  -- "123456789" -> 0xCBF43926 (standard check value)
  let testData := "123456789".toUTF8
  let crc32val := CRC32.compute testData
  assert (crc32val.toNat == 0xCBF43926)
    s!"CRC-32 check value: expected 0xCBF43926, got {crc32val.toNat}"

  -- ## CRC-32 empty data
  let crc32empty := CRC32.compute ByteArray.empty
  assert (crc32empty.toNat == 0x00000000)
    s!"CRC-32 empty: expected 0, got {crc32empty.toNat}"

  -- ## CRC-32 single byte
  let crc32zero := CRC32.compute (ByteArray.mk #[0])
  -- CRC-32 of single zero byte is 0xD202EF8D
  assert (crc32zero.toNat == 0xD202EF8D)
    s!"CRC-32 single zero: expected 0xD202EF8D, got {crc32zero.toNat}"

  -- ## CRC-32 naive vs table-driven agreement
  let crc32naive := CRC32.computeNaive testData
  assert (crc32val.toNat == crc32naive.toNat)
    "CRC-32 naive == table-driven"

  -- ## CRC-32 streaming API
  let crc32stream := CRC32.finalize (CRC32.update CRC32.init testData)
  assert (crc32val.toNat == crc32stream.toNat)
    "CRC-32 streaming == oneshot"

  -- ## CRC-32 streaming multi-chunk
  let chunk1 := "1234".toUTF8
  let chunk2 := "56789".toUTF8
  let state1 := CRC32.update CRC32.init chunk1
  let state2 := CRC32.update state1 chunk2
  let crc32multi := CRC32.finalize state2
  assert (crc32val.toNat == crc32multi.toNat)
    "CRC-32 multi-chunk streaming"

  -- ## CRC-32 table size
  assert (CRC32.table.size == 256) "CRC-32 table size"

  -- ## CRC-32 detects 1-bit corruption
  let original := "Hello, World!".toUTF8
  let crcOrig := CRC32.compute original
  let mut corrupted := original
  let byte0 := corrupted.get! 0
  corrupted := corrupted.set! 0 (byte0 ^^^ 1)
  let crcCorrupted := CRC32.compute corrupted
  assert (crcOrig.toNat != crcCorrupted.toNat)
    "CRC-32 detects 1-bit error"

  -- ## CRC-16 known test vectors
  -- Note: CRC-16/CCITT (X.25) check value for "123456789" is 0x906E
  let crc16val := CRC16.compute testData
  assert (crc16val.toNat == 0x906E)
    s!"CRC-16 check value: expected 0x906E, got {crc16val.toNat}"

  -- ## CRC-16 empty data
  let crc16empty := CRC16.compute ByteArray.empty
  assert (crc16empty.toNat == 0x0000)
    s!"CRC-16 empty: expected 0, got {crc16empty.toNat}"

  -- ## CRC-16 naive vs table-driven agreement
  let crc16naive := CRC16.computeNaive testData
  assert (crc16val.toNat == crc16naive.toNat)
    "CRC-16 naive == table-driven"

  -- ## CRC-16 streaming
  let crc16stream := CRC16.finalize (CRC16.update CRC16.init testData)
  assert (crc16val.toNat == crc16stream.toNat)
    "CRC-16 streaming == oneshot"

  -- ## CRC-16 table size
  assert (CRC16.table.size == 256) "CRC-16 table size"

  -- ## CRC-16 detects 1-bit corruption
  let crc16Orig := CRC16.compute original
  let crc16Corrupted := CRC16.compute corrupted
  assert (crc16Orig.toNat != crc16Corrupted.toNat)
    "CRC-16 detects 1-bit error"

  -- ## Property: CRC of different data should differ (probabilistic)
  let mut rng := PRNG.new
  let mut collisions : Nat := 0
  for _ in [:numIter] do
    let (rng', len) := rng.nextNat 32
    rng := rng'
    let mut data1 := ByteArray.mkEmpty (len + 1)
    let mut data2 := ByteArray.mkEmpty (len + 1)
    for _ in [:(len + 1)] do
      let (rng', b1) := rng.nextUInt8
      rng := rng'
      let (rng', b2) := rng.nextUInt8
      rng := rng'
      data1 := data1.push b1
      data2 := data2.push b2
    let c1 := CRC32.compute data1
    let c2 := CRC32.compute data2
    if c1.toNat == c2.toNat && data1 != data2 then
      collisions := collisions + 1
  -- Collisions should be extremely rare (< 1%)
  assert (collisions < 3) s!"CRC-32 collision rate: {collisions}/{numIter}"

  c.get
