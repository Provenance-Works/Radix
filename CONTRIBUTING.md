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
4. **Build and verify** — all proofs must check:
   ```bash
   lake build
   ```
5. **Run tests**:
   ```bash
   lake exe test
   lake exe proptest
   ```
6. **Commit** using [Conventional Commits](#commit-messages):
   ```bash
   git commit -m "feat(word): add UInt128 wrapping arithmetic"
   ```
7. **Push** and open a Pull Request against `main`
8. Fill out the PR template completely
9. Wait for review — maintainers aim to respond within 7 days

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

# Run tests
lake exe test

# Run property-based tests
lake exe proptest

# Run examples
lake exe examples

# Run benchmarks
lake exe bench
```

### Project Structure

```
Radix.lean              # Root import (all 13 modules)
Radix/
├── Alignment.lean      # Alignment utilities
├── Bitmap.lean         # Dense bit arrays
├── CRC.lean            # CRC-32 / CRC-16
├── MemoryPool.lean     # Bump/slab allocator models
├── RingBuffer.lean     # Fixed-capacity circular queue
├── Word.lean           # Fixed-width integers (UInt8–64, Int8–64, UWord, IWord)
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
examples/               # 15 runnable usage examples
benchmarks/             # Microbenchmarks with C baseline
docs/                   # English and Japanese documentation
```

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

**Scopes:** `word`, `bit`, `bytes`, `memory`, `binary`, `system`, `concurrency`, `baremetal`

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
- No custom mathematical axioms — only `trust_*` axioms for external-world assumptions

### Verification Checklist

Before submitting a PR that adds functionality:

- [ ] Specification defined in `*.Spec.lean`
- [ ] Implementation proven correct against specification
- [ ] Zero `sorry` in entire codebase (check with `grep -r "sorry" Radix/`)
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
