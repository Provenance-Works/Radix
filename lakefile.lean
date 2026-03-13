import Lake
open Lake DSL

package radix where
  leanOptions := #[
    -- Enable well-foundedness checks
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Radix where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "06e947358d88e36af006f915f79a04a10fd43cc4"

@[default_target]
lean_exe test where
  root := `tests.Main

lean_exe proptest where
  root := `tests.PropertyTests

lean_exe bench where
  root := `benchmarks.Main

lean_exe examples where
  root := `examples.Main
