# Product Roadmap

<!-- Last updated: 2026-03-14 -->

## Vision

Radix is the verified foundation that every Lean 4 systems project stands on.
It provides the lowest layer of systems programming primitives — integers,
bits, bytes, memory, binary formats, concurrency, and bare-metal support —
with complete formal verification and zero-cost abstraction.

## Strategic Pillars

1. **Proof Depth** — strengthen and expand the verified theorem base
2. **Primitive Completeness** — cover every building block a systems library needs
3. **Downstream Ergonomics** — make Radix easy to depend on and compose with
4. **Toolchain Resilience** — stay compatible with Lean 4 / Mathlib evolution

## Current Release: v0.1.0 (2026-03-14)

First verified baseline. All 8 modules implemented with the three-layer
architecture (Spec → Impl → Bridge). 702+ theorems, zero `sorry`.

### What's included

| Module | Key Capabilities |
|--------|-----------------|
| Word | 10 integer types, 4 arithmetic modes, width conversions |
| Bit | Boolean algebra, shifts, rotates, scanning, bit fields |
| Bytes | Endianness, bswap, ByteSlice |
| Memory | Buffer, Ptr, LayoutDesc, region disjointness |
| Binary | Format DSL, parser, serializer, LEB128 |
| System | File I/O state machine, SysError, FD, withFile bracket |
| Concurrency | C11 memory ordering, AtomicCell, CAS, happens-before |
| BareMetal | Platform model, memory map, linker scripts, startup, GC-free |

---

## Next Release: v0.2.0 — "Bedrock"

Theme: **Deepen the foundation — verified data structures and numeric traits**

These are the primitives that downstream projects (crypto, networking, OS)
keep re-implementing. Radix should provide them once, verified, so nobody
has to do it again.

### Committed Features

| Feature | Priority | Size | RICE | Description |
|---------|----------|------|------|-------------|
| Ring Buffer | P0 | M | 90 | Verified fixed-capacity circular queue over `Buffer`. Proof: no data loss on wrap-around, capacity invariant. Essential for IPC, driver queues, and OS kernels. |
| Bitmap / Bitset | P0 | M | 88 | Dense bit-array backed by `UInt64` array. O(1) set/clear/test, bulk operations (find-first-set, count). Proof: set/clear round-trip, population count. Core allocator and scheduler primitive. |
| CRC-32 / CRC-16 | P0 | M | 86 | Table-driven CRC with mathematical spec (polynomial division over GF(2)). Proof: CRC(CRC(data) ++ check) = 0, linearity. Not crypto — integrity checking. Every binary format needs it. |
| Numeric Typeclasses | P0 | S | 85 | `BoundedUInt`, `BoundedInt`, `FixedWidth` — generic traits across all 10 Word types. Enables downstream libraries to write code once over "any integer width". Currently each width is separate. |
| Memory Pool Model | P1 | M | 78 | Bump allocator and slab allocator specification. Proof: no double-free, no use-after-free, capacity tracking. Extends BareMetal for embedded/OS environments without GC. |
| Alignment Utilities | P1 | S | 76 | `alignUp`, `alignDown`, `isAligned`, `alignmentOf` with proofs. Currently scattered — centralize and verify. Every memory and BareMetal consumer needs these. |

### Stretch Goals

| Feature | Priority | Size | RICE | Rationale |
|---------|----------|------|------|-----------|
| Volatile Read/Write Model | P2 | S | 68 | MMIO access formalization. Extends Memory + BareMetal. Needed for device driver projects. |
| Interrupt Priority Model | P2 | S | 65 | Extends BareMetal.Spec with interrupt priority levels and nesting. Enables verified interrupt handler projects. |

### Dependencies

- Ring Buffer depends on: Memory.Buffer, Word (index arithmetic)
- Bitmap depends on: Bit.Ops, Bit.Scan, Word.UInt
- CRC depends on: Bytes, Binary.Spec (polynomial spec in BitVec)
- Numeric Typeclasses depends on: Word (all types), Bit (bitwise ops)
- Memory Pool depends on: Memory.Spec (Region), BareMetal (GCFree)
- Alignment depends on: Word, Memory.Spec

### Release Criteria

- [ ] All new features follow three-layer architecture
- [ ] Zero `sorry` across entire codebase
- [ ] Unit tests + property tests for every new feature
- [ ] Benchmark comparison with C equivalent for Ring Buffer and CRC
- [ ] Documentation (English + Japanese) for all new APIs
- [ ] Examples demonstrating each new feature

---

## Planned: v0.3.0 — "Composable"

Theme: **Composition patterns and richer verification**

| Feature | Priority | Size | RICE | Rationale |
|---------|----------|------|------|-----------|
| Verified UTF-8 Model | P1 | L | 82 | Encoding/decoding spec over Bytes. Proof: round-trip, well-formedness. Foundation for any text-handling project. |
| Error Correction Codes | P1 | M | 74 | Hamming codes, parity check — mathematical primitives over Bit/Bytes. Different from crypto; pure algebraic coding theory. |
| DMA Transfer Model | P1 | M | 72 | Source/destination region spec with atomicity and coherence constraints. Extends Memory + Concurrency for hardware DMA verification. |
| Region Algebra | P1 | M | 70 | Union, intersection, difference of `Memory.Region` with lattice proofs. Enables complex memory map reasoning in downstream OS/driver projects. |
| Timer / Clock Model | P2 | S | 66 | Monotonic clock, deadline, timeout specs for BareMetal + System. Needed for verified scheduler and real-time system projects. |
| Proof Automation Tactics | P2 | M | 64 | Custom `radix_decide` or `radix_omega` for common proof patterns (overflow checking, alignment, region disjointness). Reduce proof boilerplate for downstream users. |

---

## Future (6–12 months)

| Feature | Rationale | Depends On |
|---------|-----------|------------|
| Verified Compression Primitives (RLE, DEFLATE blocks) | Binary format building blocks | Binary, Bytes, Bit |
| Cache Line Model | Cache coherence spec for concurrent data structures | Concurrency, Memory |
| Page Table Model | Virtual → physical mapping specification | Memory, BareMetal |
| Power State Model | Sleep/wake/power-domain transitions | BareMetal, System |
| Formal Refinement Framework | Generic layer-bridging proof infrastructure | All modules |

## Vision (1–3 years)

| Capability | Strategic Rationale |
|------------|-------------------|
| Lean 4 stable toolchain tracking | Eliminate version friction for downstream |
| Mathlib `BitVec` upstream contributions | Push generic lemmas back to Mathlib |
| Extraction to C / machine code | Verified code → deployable artifacts |
| Ecosystem of dependent projects | Crypto, networking, embedded OS all on Radix |

---

## Explicitly Not Doing (and Why)

| Anti-Feature | Reason |
|-------------|--------|
| Cryptographic algorithms (SHA, AES, etc.) | Separate project — Radix provides the integer/byte primitives they build on |
| Network protocol stacks (TCP/IP, TLS) | Separate project — Radix provides Binary DSL and Bytes they use |
| ISA-specific instruction semantics | Separate project — Radix provides the platform-agnostic models |
| IEEE 754 floating-point | Separate project — different mathematical foundation |
| Application frameworks or CLI tools | Radix is a pure library, not a user-facing product |
| FFI bindings to C libraries | Violates C-001 (Strict Pure Lean 4 Policy) |

---

## Decision Log

| Date | Decision | Rationale | Alternatives | Revisit By |
|------|----------|-----------|--------------|------------|
| 2026-03-14 | Release v0.1.0 as first stable baseline | All 8 modules implemented, 702+ proofs, zero sorry | Continue as unreleased (rejected: need a stable reference point) | — |
| 2026-03-14 | Position as foundation library, not application framework | Crypto/net/ISA exist as separate projects; avoid duplication and scope explosion | Monolithic verified OS library (rejected: too broad) | 2026-Q3 |
| 2026-03-14 | v0.2.0 focuses on verified data structures + numeric traits | Downstream projects need ring buffers, bitmaps, CRCs — re-implementing is waste | Focus on proof depth only (rejected: need breadth for adoption) | — |
