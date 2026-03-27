# Contributing to Radix

Thank you for your interest in contributing to Radix! This project aims to build a formally verified foundation for Lean 4 systems programming, and every contribution — whether it's a theorem, a bug fix, documentation, or a test — helps strengthen that foundation.

## Code of Conduct

This project follows the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you are expected to uphold this code. Please report unacceptable behavior via [GitHub Private Vulnerability Reporting](https://github.com/provenance-works/radix/security/advisories/new) or by opening a confidential issue.

## How Can I Contribute?

### Reporting Bugs

If you find a bug, please [open an issue](https://github.com/provenance-works/radix/issues/new?template=bug_report.yml) with:

- A clear description of the problem
- Steps to reproduce
- Expected vs actual behavior
- Your Lean version (`lean --version`) and OS

### Suggesting Features

Feature requests are welcome! Please [open a feature request](https://github.com/provenance-works/radix/issues/new?template=feature_request.yml) and describe:

- The problem you're trying to solve
- Your proposed solution
- How it fits into the existing module architecture

### Your First Contribution

Look for issues labeled:

- [`good first issue`](https://github.com/provenance-works/radix/labels/good%20first%20issue) — Well-scoped, beginner-friendly tasks
- [`help wanted`](https://github.com/provenance-works/radix/labels/help%20wanted) — Non-trivial but well-defined work

If you're unsure where to start, open a [Discussion](https://github.com/provenance-works/radix/discussions) and ask!

### Pull Request Process

1. **Fork** the repository and clone your fork
2. **Create a branch** from `main`:
   ```bash
   git checkout -b feat/my-feature
   ```
3. **Make your changes** following the [Style Guide](#style-guide)
4. **Install and enable pre-commit hooks**:
   ```bash
   python3 -m pip install pre-commit
   make pre-commit-install
   ```
5. **Run the local verification gate**:
   ```bash
   make check
   ```
6. **If your change is intentionally scoped, also note the narrowest command you validated with**:
   ```bash
   lake build
   lake exe test
   lake exe proptest
   ```
7. **Commit** using [Conventional Commits](#commit-messages):
   ```bash
   git commit -m "feat(word): add UInt128 wrapping arithmetic"
   ```
8. **Push** and open a Pull Request against `main`
9. Fill out the PR template completely
10. Wait for review — maintainers aim to respond within 7 days

## Development Setup

### Prerequisites

- [Lean 4](https://lean-lang.org/) v4.29.0-rc4 or later (via [elan](https://github.com/leanprover/elan))
- Git

### Setup

```bash
# Clone
git clone https://github.com/provenance-works/radix.git
cd radix

# Build (this will fetch Mathlib — first build takes a while)
lake build

# Install pre-commit hooks for stats/docs hygiene and file validation
python3 -m pip install pre-commit
make pre-commit-install

# Run tests
lake exe test

# Run property-based tests
lake exe proptest

# Run comprehensive regression tests
lake exe comptest

# Run examples
lake exe examples

# Run the full local verification gate before opening a PR
make check

# Run the same local hook suite on demand
make pre-commit-run

# Run benchmarks
lake exe bench
```

### Project Structure

```
Radix.lean              # Root import (all 18 leaf modules)
Radix/
├── Pure.lean           # Grouped import for the 14 pure Layer 2-3 modules
├── Trusted.lean        # Grouped import for Layer 1 boundary modules
├── Alignment.lean      # Alignment utilities
├── Bitmap.lean         # Dense bit arrays
├── DMA.lean            # DMA descriptor model and simulator
├── ECC.lean            # Hamming(7,4) coding helpers
├── CRC.lean            # CRC-32 / CRC-16
├── MemoryPool.lean     # Bump/slab allocator models
├── ProofAutomation.lean # Tactic helpers for common proof patterns
├── RingBuffer.lean     # Fixed-capacity circular queue
├── Timer.lean          # Monotonic clocks and deadlines
├── UTF8.lean           # Verified UTF-8 scalar model
├── Word.lean           # Fixed-width integers (UInt8–64, Int8–64, UWord, IWord)
├── Word/
│   ├── Lemmas.lean     # Aggregate import for Word lemma families
│   └── ...
├── Bit.lean            # Bitwise operations
├── Bytes.lean          # Byte order and slices
├── Memory.lean         # Memory model (Buffer, Ptr, Layout)
├── Binary.lean         # Binary format DSL and LEB128
├── System.lean         # System call interface
├── Concurrency.lean    # Concurrency model
├── BareMetal.lean      # Bare-metal support
└── <Module>/
    ├── Spec.lean       # Layer 3: Mathematical specification
    ├── *.lean          # Layer 2: Implementation with proofs
    ├── Lemmas.lean     # Verified theorems
    └── Assumptions.lean # Layer 1: Trust axioms (where needed)
tests/                  # Unit, property-based, and comprehensive tests
examples/               # 21 runnable usage examples
benchmarks/             # Microbenchmarks with C baseline
docs/                   # English and Japanese documentation
```

### Import Surfaces

- `Radix.<Module>` for a single leaf module such as `Radix.Word` or `Radix.Binary`
- `Radix.Pure` for the 14 pure modules that stay within Layers 2-3
- `Radix.Trusted` for `System`, `Concurrency`, and `BareMetal`
- `Radix.ProofAutomation` for tactic macros only
- `Radix` for the full library surface

### Pre-commit Hooks

- `pre-commit` runs generated stats refreshes before commit via `scripts/update_project_stats.py`
- It also checks YAML, JSON, merge markers, line endings, and trailing whitespace
- If hooks rewrite files, review the diff, re-stage, and run the commit again

### Three-Layer Architecture

Every contribution must follow the three-layer architecture:

| Layer | Files | Purpose |
|-------|-------|---------|
| **Spec** (Layer 3) | `*.Spec.lean` | Pure mathematical specification using Mathlib `BitVec n` |
| **Impl** (Layer 2) | `*.lean` | Computable Lean 4 code with correctness proofs |
| **Bridge** (Layer 1) | `*.IO.lean`, `*.Assumptions.lean` | System-level wrappers with named `trust_*` axioms |

## Style Guide

### Code Style

- `autoImplicit` is globally set to `false` — all variables must be explicitly declared
- Follow existing module naming conventions (`Radix.<Module>.<Component>`)
- Use `theorem` for verified propositions, `def` for computable definitions
- Proofs should be readable — prefer structured `by` tactic proofs over term-mode when complex
- No `sorry` — ever. All proofs must be complete.

### Commit Messages

This project uses [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/):

```
<type>(<scope>): <description>

[optional body]

[optional footer(s)]
```

**Types:**

| Type | When to use |
|------|-------------|
| `feat` | New feature or theorem |
| `fix` | Bug fix |
| `proof` | New or improved proof (no functional change) |
| `refactor` | Code restructuring (no functional change) |
| `test` | Adding or improving tests |
| `docs` | Documentation changes |
| `build` | Build system or dependency changes |
| `ci` | CI/CD changes |
| `chore` | Maintenance tasks |

**Scopes:** `word`, `bit`, `bytes`, `memory`, `binary`, `alignment`, `ringbuffer`, `bitmap`, `crc`, `memorypool`, `utf8`, `ecc`, `dma`, `timer`, `system`, `concurrency`, `baremetal`, `proofautomation`, `docs`, `ci`, `build`, `release`

**Examples:**
```
feat(word): add UInt128 wrapping arithmetic
proof(bit): strengthen De Morgan law to handle edge cases
fix(binary): correct LEB128 signed encoding for negative values
test(memory): add property tests for buffer read/write round-trip
docs(bytes): add byte order conversion examples
```

### Branching Strategy

Radix uses **Trunk-Based Development with Release Branches** ([ADR-004](docs/en/design/adr.md#adr-004-trunk-based-development-with-release-branches)):

- **`main`** is the trunk. All development flows through PRs to `main`.
- **Release branches** (`release/vX.Y`) are cut for stabilization and patch support.
- **Toolchain branches** (`toolchain/lean-X.Y.Z`) isolate Lean 4 / Mathlib upgrades.
- Bug fixes are implemented on `main` first, then cherry-picked to release branches.
- There is no `develop` branch.

### Branch Naming

```
feat/<short-description>           # New features
fix/<short-description>            # Bug fixes
proof/<short-description>          # New/improved proofs
docs/<short-description>           # Documentation
refactor/<short-description>       # Refactoring
test/<short-description>           # Tests
ci/<short-description>             # CI/CD changes
toolchain/lean-<version>           # Lean 4 toolchain bumps
release/v<major>.<minor>           # Release stabilization (maintainers only)
```

### Proof Guidelines

- Every new operation MUST have a specification in the `Spec.lean` file
- Every implementation MUST be proven equivalent to its specification
- Use Mathlib `BitVec n` as the canonical specification-level type
- Name theorems descriptively: `wrappingAdd_eq_bitvec_add`, `bswap_involution`
- Group related lemmas in `Lemmas.lean` files
- Prefer updating grouped import surfaces (`Radix.Pure`, `Radix.Trusted`, `Radix.<Module>`) when you add public modules
- No custom mathematical axioms — only `trust_*` axioms for external-world assumptions

### Verification Checklist

Before submitting a PR that adds functionality:

- [ ] Specification defined in `*.Spec.lean`
- [ ] Implementation proven correct against specification
- [ ] Zero `sorry` in library, tests, and examples (check with `rg -n "sorry" Radix tests examples`)
- [ ] Unit tests added to `tests/`
- [ ] Property-based tests added (if applicable)
- [ ] Examples updated (if applicable)
- [ ] Documentation updated (English and Japanese)

## Community

- **[GitHub Discussions](https://github.com/provenance-works/radix/discussions)** — Questions, ideas, and general conversation
- **[Issues](https://github.com/provenance-works/radix/issues)** — Bug reports and feature requests

## Review Process

- All PRs require at least one review from a maintainer
- PRs must pass CI (build + tests + proof verification)
- Maintainers aim to provide initial review within 7 days
- Complex changes may require multiple review rounds

## License

By contributing, you agree that your contributions will be licensed under the [Apache License 2.0](LICENSE).
