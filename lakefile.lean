import Lake
open Lake DSL

package radix where
  leanOptions := #[
    -- Enable well-foundedness checks
    ⟨`autoImplicit, false⟩
  ]
  -- Enable native CPU instructions (popcnt, lzcnt, bmi, bmi2, etc.)
  moreLeancArgs := #["-march=native"]

@[default_target]
lean_lib Radix where
  srcDir := "."
  extraDepTargets := #[`radixffi]

extern_lib radixffi pkg := do
  let srcJob ← inputTextFile (pkg.dir / "c" / "radix_ffi.c")
  let oFile := pkg.buildDir / "c" / "radix_ffi.o"
  let oJob ← buildLeanO oFile srcJob #[] #["-O2", "-march=native"]
  let libFile := pkg.staticLibDir / nameToStaticLib "radixffi"
  buildStaticLib libFile #[oJob]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "06e947358d88e36af006f915f79a04a10fd43cc4"

@[default_target]
lean_exe test where
  root := `tests.Main

lean_exe proptest where
  root := `tests.PropertyTests

lean_lib ComprehensiveTestLib where
  srcDir := "."
  roots := #[`tests.ComprehensiveTests.Framework,
             `tests.ComprehensiveTests.Word.UInt8,
             `tests.ComprehensiveTests.Word.UInt16,
             `tests.ComprehensiveTests.Word.UInt32,
             `tests.ComprehensiveTests.Word.UInt64,
             `tests.ComprehensiveTests.Word.Int8,
             `tests.ComprehensiveTests.Word.Int16,
             `tests.ComprehensiveTests.Word.Int32,
             `tests.ComprehensiveTests.Word.Int64,
             `tests.ComprehensiveTests.Word.UWord,
             `tests.ComprehensiveTests.Word.IWord,
             `tests.ComprehensiveTests.Word.Conversions,
             `tests.ComprehensiveTests.Word.Properties,
             `tests.ComprehensiveTests.Bit.Ops,
             `tests.ComprehensiveTests.Bit.Scan,
             `tests.ComprehensiveTests.Bit.Field,
             `tests.ComprehensiveTests.Bit.Properties,
             `tests.ComprehensiveTests.Bytes.Order,
             `tests.ComprehensiveTests.Bytes.Slice,
             `tests.ComprehensiveTests.Bytes.Properties,
             `tests.ComprehensiveTests.Memory.Buffer,
             `tests.ComprehensiveTests.Memory.Ptr,
             `tests.ComprehensiveTests.Memory.Layout,
             `tests.ComprehensiveTests.Memory.Properties,
             `tests.ComprehensiveTests.Binary.Format,
             `tests.ComprehensiveTests.Binary.Leb128,
             `tests.ComprehensiveTests.Binary.Properties,
             `tests.ComprehensiveTests.System.Error,
             `tests.ComprehensiveTests.System.IO,
             `tests.ComprehensiveTests.System.Properties,
             `tests.ComprehensiveTests.Concurrency.Ordering,
             `tests.ComprehensiveTests.Concurrency.Atomic,
             `tests.ComprehensiveTests.Concurrency.Properties,
             `tests.ComprehensiveTests.BareMetal.Platform,
             `tests.ComprehensiveTests.BareMetal.MemoryMap,
             `tests.ComprehensiveTests.BareMetal.Startup,
             `tests.ComprehensiveTests.BareMetal.GCFree,
             `tests.ComprehensiveTests.BareMetal.Linker,
             `tests.ComprehensiveTests.BareMetal.Properties]

lean_exe comptest where
  root := `tests.ComprehensiveTests

lean_exe bench where
  root := `benchmarks.Main

lean_exe examples where
  root := `examples.Main
