# Vision

<!-- Last updated: 2026-03-14 -->

## One-Line

Radix is the verified foundation that every Lean 4 systems project stands on.

## The Problem

Systems programming requires manipulating fixed-width integers, raw bytes,
memory regions, binary formats, and hardware interfaces. These are exactly
the operations where subtle bugs (overflow, endianness, off-by-one,
use-after-free) cause the most severe real-world consequences — security
vulnerabilities, data corruption, undefined behavior.

Existing approaches force a choice:
- **Write in C/Rust** — fast, but verification is external and partial.
- **Write in F\*/Coq/Isabelle** — verified, but extracted code is slow and
  the ecosystem is small.
- **Use Lean 4 without verification** — productive, but leaves correctness
  to testing.

## The Vision

Radix eliminates this trade-off for Lean 4. It provides the lowest layer
of systems programming primitives — integers, bits, bytes, memory, binary
formats, concurrency, and bare-metal support — with:

1. **Complete formal verification** — every operation has a mathematical
   specification in Mathlib `BitVec n`, and every implementation is proven
   to match that specification. Zero `sorry`.
2. **Zero-cost abstraction** — proofs are erased at compile time. Runtime
   performance matches hand-written Lean 4 or C.
3. **Pure Lean 4** — no FFI, no C code, no custom axioms. The trusted
   computing base is Lean's kernel plus explicitly named hardware
   assumptions (`trust_*`).

## Positioning

Radix is a **foundation library**, not an application framework.

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

Other verified projects (cryptography, network protocols, ISA formalizations,
IEEE 754, etc.) import Radix to get proven-correct low-level building blocks
instead of re-inventing and re-verifying them independently.

## Design Principles

1. **Maximize verified, minimize trusted** — three-layer architecture.
2. **Zero-cost abstraction** — proofs erased at runtime.
3. **Pure Lean 4** — no FFI, no C, no custom axioms.
4. **BitVec as specification language** — Mathlib canonical.
5. **Modular independence** — import only what you need.
6. **Foundation, not framework** — provide primitives, not opinions.

## Success Criteria

- Other Lean 4 projects depend on Radix as their low-level layer.
- All 1123+ theorems remain `sorry`-free across Lean/Mathlib upgrades.
- Runtime performance within 2× of equivalent C on microbenchmarks.
- Tracks Lean 4 stable toolchain within one release cycle.
