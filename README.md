<div align="center">

# Radix

**Formally verified foundation library for Lean 4 systems programming**

[![CI](https://github.com/provenance-works/radix/actions/workflows/ci.yml/badge.svg)](https://github.com/provenance-works/radix/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Lean](https://img.shields.io/badge/Lean-4.29.0--rc4-blue?logo=data:image/svg+xml;base64,PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHdpZHRoPSIyNCIgaGVpZ2h0PSIyNCI+PHRleHQgeD0iMCIgeT0iMjAiIGZvbnQtc2l6ZT0iMjAiPkw8L3RleHQ+PC9zdmc+)](https://lean-lang.org/)
[![v0.3.0](https://img.shields.io/badge/version-0.3.0-green.svg)](CHANGELOG.md)
[![Theorems](https://img.shields.io/badge/theorems-1123%2B-brightgreen.svg)](#verification-status)
[![sorry-free](https://img.shields.io/badge/sorry-free-%E2%9C%93-brightgreen.svg)](#verification-status)

*1123+ verified theorems. Zero `sorry`. Proofs erase at runtime.*

[Documentation](docs/en/README.md) · [Quick Start](#quick-start) · [Examples](examples/) · [Roadmap](ROADMAP.md) · [Contributing](CONTRIBUTING.md)

</div>

---

## Overview

Radix provides the lowest layer of systems programming primitives for Lean 4 — integers, bits, bytes, memory, binary formats, concurrency, and bare-metal support — with **complete formal verification** and **proof-erased abstractions**.

### Why Radix?

Systems programming requires manipulating fixed-width integers, raw bytes, memory regions, and binary formats. These are exactly the operations where subtle bugs — overflow, endianness errors, off-by-one, use-after-free — cause the most severe real-world consequences.

Radix eliminates this trade-off:

- **Complete formal verification** — every operation has a mathematical specification in Mathlib `BitVec n`, proven to match its implementation. Zero `sorry` statements.
- **Proof-erased abstractions** — proofs are erased at compile time, so verification artifacts do not add runtime overhead. The repository includes microbenchmarks and C baselines for inspection, but concrete performance still depends on workload, backend, and compiler settings.
- **Pure Lean 4** — no FFI, no C code, no custom mathematical axioms. The trusted computing base is Lean's kernel plus explicitly named external-world assumptions (`trust_*`).

### Modules

| Module | Description | Theorems |
|--------|-------------|----------|
| **Word** | 10 integer types (U/Int 8-64, UWord, IWord), 4 arithmetic modes, numeric typeclasses | 350 |
| **Bit** | Boolean algebra, shifts, rotates, scanning, bit fields | 278 |
| **Bytes** | Endianness, bswap, ByteSlice | 60 |
| **Memory** | Buffer, Ptr, LayoutDesc, region disjointness and algebra | 60 |
| **Binary** | Format DSL, parser, serializer, LEB128 | 92 |
| **System** | File I/O state machine plus trusted OS boundary wrappers | 41 |
| **Concurrency** | C11 memory ordering specification model with trusted hardware assumptions | 32 |
| **BareMetal** | Bare-metal platform formalization: memory map, linker scripts, startup, GC-free | 36 |
| **Alignment** | alignUp/Down, isAligned, power-of-two fast paths, HasAlignment typeclass | 25 |
| **RingBuffer** | Fixed-capacity circular queue, push/pop/peek, FIFO ordering proofs | 25 |
| **Bitmap** | Dense bit-array (UInt64-backed), set operations, popcount, find-first | 34 |
| **CRC** | Table-driven CRC-32/CRC-16, GF(2) polynomial spec, streaming API | 14 |
| **MemoryPool** | Bump allocator, slab allocator, no-double-free/capacity-tracking proofs | 36 |
| **UTF8** | Verified Unicode scalar model, UTF-8 encoding/decoding, well-formedness checks | 17 |
| **ECC** | Hamming(7,4) parity model, syndrome computation, single-bit correction | 6 |
| **DMA** | Region-based DMA descriptors with coherence and atomicity validation | 4 |
| **Timer** | Monotonic clocks, deadlines, timeout helpers, expiry proofs | 13 |
| **ProofAutomation** | Reusable tactic macros for arithmetic and decision procedures | 0 |

### Architecture

```
┌─────────────────────────────────────────────────┐
│  Application / Domain Libraries                 │
│  (crypto, networking, ISA, file systems, ...)   │
├─────────────────────────────────────────────────┤
│  Radix — Verified Low-Level Primitives          │
│  Word │ Bit │ Bytes │ Memory │ Binary │ UTF8    │
│  ECC │ DMA │ Timer │ ProofAutomation │ System   │
│  Concurrency │ BareMetal │ Alignment │ Bitmap   │
│  RingBuffer │ CRC │ MemoryPool                  │
├─────────────────────────────────────────────────┤
│  Mathlib (BitVec, algebra, number theory)       │
├─────────────────────────────────────────────────┤
│  Lean 4 Runtime + Kernel                        │
└─────────────────────────────────────────────────┘
```

Radix exposes 18 leaf modules plus grouped public import surfaces
(`Radix`, `Radix.Pure`, and `Radix.Trusted`). Seventeen leaf runtime and model modules follow a three-layer design, while `ProofAutomation` is a
meta-level helper module that provides tactic macros rather than a runtime
surface:

| Layer | Purpose | Example |
|-------|---------|---------|
| **Spec** | Pure mathematical specification via `BitVec n` | `Word.Spec`, `Bit.Spec` |
| **Impl** | Computable Lean 4 code with correctness proofs | `Word.UInt`, `Bit.Ops` |
| **Bridge** | System-level wrappers with named trust assumptions | `System.IO`, `BareMetal.Assumptions` |

Fourteen leaf modules stay entirely within Layers 2-3. `ProofAutomation` is also pure Lean, but it operates at elaboration time as a meta-level helper rather than as an executable runtime module. `System`, `Concurrency`, and `BareMetal` deliberately cross the trusted boundary: they formalize external OS or hardware behavior via named assumptions, and `BareMetal` is a verification model rather than a device-runtime implementation. The grouped import surfaces mirror this split directly via `Radix.Pure`, `Radix.Trusted`, and `Radix`.

## Quick Start

### Prerequisites

- [Lean 4](https://lean-lang.org/) (v4.29.0-rc4 or later)
- [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) (bundled with Lean 4)
- Git

### Installation

Add Radix to your `lakefile.lean`:

```lean
require radix from git
  "https://github.com/provenance-works/radix" @ "v0.3.0"
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

Or import grouped surfaces that match the architecture note in the docs:

```lean
import Radix.Pure             -- 14 pure Layer 2-3 modules
import Radix.Trusted          -- System, Concurrency, BareMetal
import Radix.ProofAutomation  -- tactic macros only
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

See [examples/](examples/) for 21 complete, runnable examples covering the core and composable modules.

## Verification Status

| Metric | Status |
|--------|--------|
| Total theorems | 1123+ |
| `sorry` statements | **0** |
| Proof-to-code ratio | ~0.9:1 |
| Trusted computing base | Lean 4 kernel + Mathlib + named `trust_*` axioms |

All proofs are machine-checked by the Lean 4 kernel. The `trust_*` axioms are limited to external-world assumptions (POSIX behavior, hardware semantics) and are explicitly named and documented. In particular, the `BareMetal` module models linker layout, startup, and platform invariants for verification; it does not perform real hardware I/O.

## Building & Testing

```bash
# Build the library
lake build

# Run unit tests (all 18 leaf modules)
lake exe test

# Run property-based tests (500 iterations, LCG PRNG)
lake exe proptest

# Run comprehensive regression tests
lake exe comptest

# Run all examples
lake exe examples

# Run the full local verification gate used for release prep
make check

# Run benchmarks
lake exe bench
```

## Documentation

- **[English Documentation](docs/en/README.md)** — Full documentation hub
- **[日本語ドキュメント](docs/ja/README.md)** — 完全な日本語ドキュメント
- **[Architecture](docs/en/architecture/)** — Three-layer design, module dependencies, data flow
- **[API Reference](docs/en/reference/api/)** — Per-module API documentation
- **[Design Decisions](docs/en/design/adr.md)** — Architecture Decision Records
- **[Examples](examples/)** — 21 runnable examples

## Roadmap

See [ROADMAP.md](ROADMAP.md) for the full roadmap.

- **v0.3.0** (latest release) "Composable" — 1123+ theorems, 18 leaf modules, UTF-8, error correction, DMA, region algebra, timers, proof automation
- **v0.2.1** "Bedrock" — patch release removing remaining `native_decide` usage from library proofs and CI trust-audit tracking

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
