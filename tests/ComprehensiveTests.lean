-- Framework
import tests.ComprehensiveTests.Framework

-- Word
import tests.ComprehensiveTests.Word.UInt8
import tests.ComprehensiveTests.Word.UInt16
import tests.ComprehensiveTests.Word.UInt32
import tests.ComprehensiveTests.Word.UInt64
import tests.ComprehensiveTests.Word.Int8
import tests.ComprehensiveTests.Word.Int16
import tests.ComprehensiveTests.Word.Int32
import tests.ComprehensiveTests.Word.Int64
import tests.ComprehensiveTests.Word.UWord
import tests.ComprehensiveTests.Word.IWord
import tests.ComprehensiveTests.Word.Conversions
import tests.ComprehensiveTests.Word.Properties

-- Bit
import tests.ComprehensiveTests.Bit.Ops
import tests.ComprehensiveTests.Bit.Scan
import tests.ComprehensiveTests.Bit.Field
import tests.ComprehensiveTests.Bit.Properties

-- Bytes
import tests.ComprehensiveTests.Bytes.Order
import tests.ComprehensiveTests.Bytes.Slice
import tests.ComprehensiveTests.Bytes.Properties

-- Memory
import tests.ComprehensiveTests.Memory.Buffer
import tests.ComprehensiveTests.Memory.Ptr
import tests.ComprehensiveTests.Memory.Layout
import tests.ComprehensiveTests.Memory.Properties

-- Binary
import tests.ComprehensiveTests.Binary.Format
import tests.ComprehensiveTests.Binary.Leb128
import tests.ComprehensiveTests.Binary.Properties

-- System
import tests.ComprehensiveTests.System.Error
import tests.ComprehensiveTests.System.IO
import tests.ComprehensiveTests.System.Properties

-- Concurrency
import tests.ComprehensiveTests.Concurrency.Ordering
import tests.ComprehensiveTests.Concurrency.Atomic
import tests.ComprehensiveTests.Concurrency.Properties

-- BareMetal
import tests.ComprehensiveTests.BareMetal.Platform
import tests.ComprehensiveTests.BareMetal.MemoryMap
import tests.ComprehensiveTests.BareMetal.Startup
import tests.ComprehensiveTests.BareMetal.GCFree
import tests.ComprehensiveTests.BareMetal.Linker
import tests.ComprehensiveTests.BareMetal.Properties

/-- Run all test modules and print summary. -/
def main : IO Unit := do
  IO.println "╔══════════════════════════════════════════════════════╗"
  IO.println "║    Radix Comprehensive Test Suite                   ║"
  IO.println "╚══════════════════════════════════════════════════════╝"
  IO.println ""

  let mut totalAsserts : Nat := 0
  let mut results : Array (String × Nat) := #[]

  -- === Word Module ===
  IO.println "  ── Word Module ──"
  let n ← runUInt8Tests;       totalAsserts := totalAsserts + n; results := results.push ("Word/UInt8", n)
  let n ← runUInt16Tests;      totalAsserts := totalAsserts + n; results := results.push ("Word/UInt16", n)
  let n ← runUInt32Tests;      totalAsserts := totalAsserts + n; results := results.push ("Word/UInt32", n)
  let n ← runUInt64Tests;      totalAsserts := totalAsserts + n; results := results.push ("Word/UInt64", n)
  let n ← runInt8Tests;        totalAsserts := totalAsserts + n; results := results.push ("Word/Int8", n)
  let n ← runInt16Tests;       totalAsserts := totalAsserts + n; results := results.push ("Word/Int16", n)
  let n ← runInt32Tests;       totalAsserts := totalAsserts + n; results := results.push ("Word/Int32", n)
  let n ← runInt64Tests;       totalAsserts := totalAsserts + n; results := results.push ("Word/Int64", n)
  let n ← runUWordTests;       totalAsserts := totalAsserts + n; results := results.push ("Word/UWord", n)
  let n ← runIWordTests;       totalAsserts := totalAsserts + n; results := results.push ("Word/IWord", n)
  let n ← runConversionTests;  totalAsserts := totalAsserts + n; results := results.push ("Word/Conversions", n)
  let n ← runWordPropertyTests; totalAsserts := totalAsserts + n; results := results.push ("Word/Properties", n)
  IO.println ""

  -- === Bit Module ===
  IO.println "  ── Bit Module ──"
  let n ← runBitOpsTests;      totalAsserts := totalAsserts + n; results := results.push ("Bit/Ops", n)
  let n ← runBitScanTests;     totalAsserts := totalAsserts + n; results := results.push ("Bit/Scan", n)
  let n ← runBitFieldTests;    totalAsserts := totalAsserts + n; results := results.push ("Bit/Field", n)
  let n ← runBitPropertyTests; totalAsserts := totalAsserts + n; results := results.push ("Bit/Properties", n)
  IO.println ""

  -- === Bytes Module ===
  IO.println "  ── Bytes Module ──"
  let n ← runBytesOrderTests;    totalAsserts := totalAsserts + n; results := results.push ("Bytes/Order", n)
  let n ← runBytesSliceTests;    totalAsserts := totalAsserts + n; results := results.push ("Bytes/Slice", n)
  let n ← runBytesPropertyTests; totalAsserts := totalAsserts + n; results := results.push ("Bytes/Properties", n)
  IO.println ""

  -- === Memory Module ===
  IO.println "  ── Memory Module ──"
  let n ← runMemoryBufferTests;    totalAsserts := totalAsserts + n; results := results.push ("Memory/Buffer", n)
  let n ← runMemoryPtrTests;       totalAsserts := totalAsserts + n; results := results.push ("Memory/Ptr", n)
  let n ← runMemoryLayoutTests;    totalAsserts := totalAsserts + n; results := results.push ("Memory/Layout", n)
  let n ← runMemoryPropertyTests;  totalAsserts := totalAsserts + n; results := results.push ("Memory/Properties", n)
  IO.println ""

  -- === Binary Module ===
  IO.println "  ── Binary Module ──"
  let n ← runBinaryFormatTests;    totalAsserts := totalAsserts + n; results := results.push ("Binary/Format", n)
  let n ← runBinaryLeb128Tests;    totalAsserts := totalAsserts + n; results := results.push ("Binary/Leb128", n)
  let n ← runBinaryPropertyTests;  totalAsserts := totalAsserts + n; results := results.push ("Binary/Properties", n)
  IO.println ""

  -- === System Module ===
  IO.println "  ── System Module ──"
  let n ← runSystemErrorTests;     totalAsserts := totalAsserts + n; results := results.push ("System/Error", n)
  let n ← runSystemIOTests;        totalAsserts := totalAsserts + n; results := results.push ("System/IO", n)
  let n ← runSystemPropertyTests;  totalAsserts := totalAsserts + n; results := results.push ("System/Properties", n)
  IO.println ""

  -- === Concurrency Module ===
  IO.println "  ── Concurrency Module ──"
  let n ← runConcurrencyOrderingTests;   totalAsserts := totalAsserts + n; results := results.push ("Concurrency/Ordering", n)
  let n ← runConcurrencyAtomicTests;     totalAsserts := totalAsserts + n; results := results.push ("Concurrency/Atomic", n)
  let n ← runConcurrencyPropertyTests;   totalAsserts := totalAsserts + n; results := results.push ("Concurrency/Properties", n)
  IO.println ""

  -- === BareMetal Module ===
  IO.println "  ── BareMetal Module ──"
  let n ← runBareMetalPlatformTests;   totalAsserts := totalAsserts + n; results := results.push ("BareMetal/Platform", n)
  let n ← runBareMetalMemoryMapTests;  totalAsserts := totalAsserts + n; results := results.push ("BareMetal/MemoryMap", n)
  let n ← runBareMetalStartupTests;    totalAsserts := totalAsserts + n; results := results.push ("BareMetal/Startup", n)
  let n ← runBareMetalGCFreeTests;     totalAsserts := totalAsserts + n; results := results.push ("BareMetal/GCFree", n)
  let n ← runBareMetalLinkerTests;     totalAsserts := totalAsserts + n; results := results.push ("BareMetal/Linker", n)
  let n ← runBareMetalPropertyTests;   totalAsserts := totalAsserts + n; results := results.push ("BareMetal/Properties", n)
  IO.println ""

  -- === Summary ===
  IO.println "╔══════════════════════════════════════════════════════╗"
  IO.println "║    Test Results Summary                             ║"
  IO.println "╠══════════════════════════════════════════════════════╣"
  for (name, count) in results do
    let pad := String.ofList (List.replicate (30 - name.length) ' ')
    IO.println s!"║  ✅ {name}{pad} {count} assertions  ║"
  IO.println "╠══════════════════════════════════════════════════════╣"
  IO.println s!"║  TOTAL: {totalAsserts} assertions passed               ║"
  IO.println "║  All tests PASSED                                   ║"
  IO.println "╚══════════════════════════════════════════════════════╝"
