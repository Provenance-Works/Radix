<div align="center">

# Radix

**Formally verified foundation library for Lean 4 systems programming**

[![CI](https://github.com/provenance-works/radix/actions/workflows/ci.yml/badge.svg)](https://github.com/provenance-works/radix/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Lean](https://img.shields.io/badge/Lean-4.29.0--rc4-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIyNCIgaGVpZ2h0PSIyNCI+PHRleHQgeD0iMCIgeT0iMjAiIGZvbnQtc2l6ZT0iMjAiPkw8L3RleHQ+PC9zdmc+)](https://lean-lang.org/)
[![v0.1.0](https://img.shields.io/badge/version-0.1.0-green.svg)](CHANGELOG.md)
[![Theorems](https://img.shields.io/badge/theorems-907%2B-brightgreen.svg)](#verification-status)
[![sorry-free](https://img.shields.io/badge/sorry-free-%E2%9C%93-brightgreen.svg)](#verification-status)

*907+ verified theorems. Zero `sorry`. Zero-cost abstractions.*

[Documentation](docs/en/README.md) · [Quick Start](#quick-start) · [Examples](examples/) · [Roadmap](ROADMAP.md) · [Contributing](CONTRIBUTING.md)

</div>

---

## Overview

Radix provides the lowest layer of systems programming primitives for Lean 4 — integers, bits, bytes, memory, binary formats, concurrency, and bare-metal support — with **complete formal verification** and **zero-cost abstraction**.

### Why Radix?

Systems programming requires manipulating fixed-width integers, raw bytes, memory regions, and binary formats. These are exactly the operations where subtle bugs — overflow, endianness errors, off-by-one, use-after-free — cause the most severe real-world consequences.

Radix eliminates this trade-off:

- **Complete formal verification** — every operation has a mathematical specification in Mathlib `BitVec n`, proven to match its implementation. Zero `sorry` statements.
- **Zero-cost abstraction** — proofs are erased at compile time. Runtime performance matches hand-written Lean 4 or C.
- **Pure Lean 4** — no FFI, no C code, no custom axioms. The trusted computing base is Lean's kernel plus explicitly named hardware assumptions (`trust_*`).

### Modules

| Module | Description | Theorems |
|--------|-------------|----------|
| **Word** | 10 integer types (U/Int 8–64, UWord, IWord), 4 arithmetic modes | 334 |
| **Bit** | Boolean algebra, shifts, rotates, scanning, bit fields | 264 |
| **Bytes** | Endianness, bswap, ByteSlice | 60 |
| **Memory** | Buffer, Ptr, LayoutDesc, region disjointness | 43 |
| **Binary** | Format DSL, parser, serializer, LEB128 | 92 |
| **System** | File I/O state machine, SysError, FD, withFile bracket | 34 |
| **Concurrency** | C11 memory ordering, AtomicCell, CAS, happens-before | 46 |
| **BareMetal** | Platform model, memory map, linker scripts, startup, GC-free | 34 |

### Architecture

```
┌─────────────────────────────────────────────────┐
│  Application / Domain Libraries                 │
│  (crypto, networking, ISA, file systems, ...)   │
├─────────────────────────────────────────────────┤
│  Radix — Verified Low-Level Primitives          │
│  Word │ Bit │ Bytes │ Memory │ Binary │ System  │
│  Concurrency │ BareMetal                        │
├─────────────────────────────────────────────────┤
│  Mathlib (BitVec, algebra, number theory)       │
├─────────────────────────────────────────────────┤
│  Lean 4 Runtime + Kernel                        │
└─────────────────────────────────────────────────┘
```

Every module follows a three-layer design:

| Layer | Purpose | Example |
|-------|---------|---------|
| **Spec** | Pure mathematical specification via `BitVec n` | `Word.Spec`, `Bit.Spec` |
| **Impl** | Computable Lean 4 code with correctness proofs | `Word.UInt`, `Bit.Ops` |
| **Bridge** | System-level wrappers with named trust assumptions | `System.IO`, `BareMetal.Assumptions` |

## Quick Start

### Prerequisites

- [Lean 4](https://lean-lang.org/) (v4.29.0-rc4 or later)
- [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) (bundled with Lean 4)
- Git

### Installation

Add Radix to your `lakefile.lean`:

```lean
require radix from git
  "https://github.com/provenance-works/radix" @ "v0.1.0"
```

Then fetch dependencies:

```bash
lake update
```

### Usage

Import the modules you need:

```lean
import Radix.Word    -- Fixed-width integers
import Radix.Bit     -- Bitwise operations
import Radix.Bytes   -- Byte order
import Radix.Memory  -- Memory model
import Radix.Binary  -- Binary format DSL
```

Or import everything:

```lean
import Radix
```

### Example: Safe Integer Arithmetic

```lean
import Radix.Word

-- Wrapping arithmetic (like Rust's wrapping_add)
#eval Radix.UInt8.wrappingAdd ⟨200⟩ ⟨100⟩   -- 44

-- Checked arithmetic (returns none on overflow)
#eval Radix.UInt8.checkedAdd ⟨200⟩ ⟨100⟩     -- none

-- Saturating arithmetic (clamps at bounds)
#eval Radix.UInt8.saturatingAdd ⟨200⟩ ⟨100⟩  -- 255
```

### Example: Binary Format DSL

```lean
import Radix.Binary

-- Declare a packet layout
def packetFormat : Radix.Binary.Format :=
  .seq (.u16be "magic") (.seq (.u8 "version") (.u32le "payload_size"))

-- Parse binary data using the format
-- Serialize structured data back to bytes
```

See [examples/](examples/) for 11 complete, runnable examples covering all modules.

## Verification Status

| Metric | Status |
|--------|--------|
| Total theorems | 907+ |
| `sorry` statements | **0** |
| Proof-to-code ratio | ~0.9:1 |
| Trusted computing base | Lean 4 kernel + Mathlib + named `trust_*` axioms |

All proofs are machine-checked by the Lean 4 kernel. The `trust_*` axioms are limited to external-world assumptions (POSIX behavior, hardware semantics) and are explicitly named and documented.

## Building & Testing

```bash
# Build the library
lake build

# Run unit tests (all 8 modules)
lake exe test

# Run property-based tests (500 iterations, LCG PRNG)
lake exe proptest

# Run all examples
lake exe examples

# Run benchmarks
lake exe bench
```

## Documentation

- **[English Documentation](docs/en/README.md)** — Full documentation hub
- **[日本語ドキュメント](docs/ja/README.md)** — 完全な日本語ドキュメント
- **[Architecture](docs/en/architecture/)** — Three-layer design, module dependencies, data flow
- **[API Reference](docs/en/reference/api/)** — Per-module API documentation
- **[Design Decisions](docs/en/design/adr.md)** — Architecture Decision Records
- **[Examples](examples/)** — 11 runnable examples

## Roadmap

See [ROADMAP.md](ROADMAP.md) for the full roadmap.

- **v0.1.0** (current) — 907+ theorems, 8 modules, three-layer architecture
- **v0.2.0** "Bedrock" — Ring buffers, bitmaps, CRC, numeric typeclasses, memory pools
- **v0.3.0** "Composable" — UTF-8, error correction, DMA, region algebra, timers

## Contributing

Contributions are welcome! Please read [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

- [Code of Conduct](CODE_OF_CONDUCT.md)
- [Security Policy](SECURITY.md)
- [Governance](GOVERNANCE.md)
- [Maintainers](MAINTAINERS.md)
- [Good First Issues](https://github.com/provenance-works/radix/labels/good%20first%20issue)

## License

Copyright 2026 [Provenance Works](https://github.com/provenance-works)

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) for the full text.

## Acknowledgments

- [Lean 4](https://lean-lang.org/) — The language and proof assistant
- [Mathlib](https://github.com/leanprover-community/mathlib4) — The mathematical library providing `BitVec` and algebraic foundations
- [@Aqua-218](https://github.com/Aqua-218) — Project creator and lead developer
