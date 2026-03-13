# Configuration Reference

> **Audience**: Users, Developers

## lakefile.lean

Radix uses Lake (Lean 4's build system) configured in `lakefile.lean`:

```lean
import Lake
open Lake DSL

package radix where
  leanOptions := #[
    ⟨`autoImplicit, false⟩  -- Disable auto-implicit arguments
  ]

@[default_target]
lean_lib Radix where
  srcDir := "."

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "<pinned-rev>"
```

### Package Options

| Option | Value | Description |
|--------|-------|-------------|
| `autoImplicit` | `false` | All implicit arguments must be explicitly declared. Prevents accidental free variables. |

### Build Targets

| Target | Type | Root Module | Description |
|--------|------|-------------|-------------|
| `Radix` | Library | `Radix` | Main library (default target) |
| `test` | Executable | `tests.Main` | Unit and integration tests |
| `proptest` | Executable | `tests.PropertyTests` | Property-based tests (500 iterations, LCG PRNG) |
| `bench` | Executable | `benchmarks.Main` | Performance benchmarks |
| `examples` | Executable | `examples.Main` | Usage examples |

### Running Targets

```bash
lake build              # Build the library
lake build test         # Build tests
lake exe test           # Run tests
lake exe proptest       # Run property-based tests
lake exe bench          # Run benchmarks
lake exe examples       # Run examples
```

## lean-toolchain

Pins the Lean 4 version:

```
leanprover/lean4:v4.29.0-rc4
```

> **Warning:** Changing this may break compatibility with the pinned Mathlib version.

## Dependencies

| Dependency | Source | Inherited | Purpose |
|------------|--------|-----------|---------|
| **mathlib** | `leanprover-community/mathlib4` | No | `BitVec`, algebra, tactics |
| **batteries** | `leanprover-community/batteries` | Yes (via Mathlib) | Standard library extensions |
| **plausible** | `leanprover-community/plausible` | Yes (via Mathlib) | Property-based testing |
| **aesop** | `leanprover-community/aesop` | Yes (via Mathlib) | Proof automation tactic |
| **Qq** | `leanprover-community/quote4` | Yes (via Mathlib) | Quoted expressions |
| **proofwidgets** | `leanprover-community/ProofWidgets4` | Yes (via Mathlib) | Interactive proof widgets |

## See Also

- [Installation](../getting-started/installation.md) — Setup instructions
- [Build](../development/build.md) — Build system details
- [日本語版](../../ja/reference/configuration.md) — Japanese version
