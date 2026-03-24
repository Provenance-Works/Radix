import tests.ComprehensiveTests.Binary.FormatBasics
import tests.ComprehensiveTests.Binary.FormatSerialization
import tests.ComprehensiveTests.Binary.FormatLayout

/-!
# Binary Format Test Aggregator
-/

def runBinaryFormatTests : IO Nat := do
  IO.println "    Binary format tests..."
  let basics ← runBinaryFormatBasicsTests
  let serialization ← runBinaryFormatSerializationTests
  let layout ← runBinaryFormatLayoutTests
  pure (basics + serialization + layout)
