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
  "https://github.com/leanprover-community/mathlib4" @ "master"
