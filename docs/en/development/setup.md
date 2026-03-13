# Development Setup

> **Audience**: Contributors

## Prerequisites

| Tool | Version | Purpose |
|------|---------|---------|
| **Lean 4** | v4.29.0-rc4 | Language and compiler |
| **Lake** | (bundled with Lean 4) | Build system |
| **Git** | any recent | Version control, dependency resolution |
| **elan** | any recent | Lean version manager |

### Installing Lean 4

```bash
# Install elan (Lean version manager)
curl https://elan-init.trycloudflare.com/ -sSf | sh

# Verify
lean --version
lake --version
```

elan reads the `lean-toolchain` file and automatically installs the correct Lean version.

### Optional: C Compiler (for Benchmarks)

The C baseline benchmarks require:

| Tool | Flags | Purpose |
|------|-------|---------|
| **GCC** | `-O2 -fno-builtin` | C baseline measurements |

```bash
# Ubuntu/Debian
sudo apt install gcc

# Verify
gcc --version
```

## Cloning and Building

```bash
git clone <repo-url> radix
cd radix

# Fetch dependencies (downloads Mathlib — takes time on first run)
lake update

# Build the library
lake build
```

> **Note:** The first build downloads and compiles Mathlib4. This can take 30+ minutes and requires significant memory (≥ 8 GB). Subsequent builds are incremental and much faster.

## Verifying the Setup

```bash
# Run unit tests
lake exe test

# Run property-based tests
lake exe proptest

# Run examples
lake exe examples
```

All three should complete with zero failures.

## Editor Setup

### VS Code (Recommended)

1. Install the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
2. Open the `radix/` folder as the workspace root
3. The extension reads `lean-toolchain` and configures itself automatically
4. Lean's Language Server (LSP) provides type checking, go-to-definition, and proof state display

### Other Editors

Any editor with Lean 4 LSP support works. Set the project root to the directory containing `lakefile.lean`.

## Project Conventions

### File Organization

- Every module follows the three-layer architecture (see [Architecture](../architecture/))
- `Spec.lean` = Layer 3 (specifications and proofs)
- Implementation files = Layer 2 (pure computation)
- `Assumptions.lean` / `IO.lean` = Layer 1 (system bridge)
- `Lemmas.lean` = Layer 3 (proofs about Layer 2 implementations)

### Code Style

- `autoImplicit` is **disabled** — all implicit arguments must be explicit
- Functions use `@[inline]` for zero-cost abstraction where appropriate
- All `axiom` declarations use the `trust_` prefix and cite external specifications
- No `sorry` in any committed code
- Follows Mathlib naming conventions for lemma names

### Namespace Convention

All Radix definitions live under the `Radix` namespace:

```lean
namespace Radix.Word.UInt
-- definitions here
end Radix.Word.UInt
```

## Related Documents

- [Build](build.md) — Build system details
- [Testing](testing.md) — Test strategy
- [Project Structure](project-structure.md) — Codebase layout
