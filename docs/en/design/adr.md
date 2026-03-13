# Architecture Decision Records

> **Audience**: All

## Overview

Architecture Decision Records (ADRs) capture significant architectural decisions made during Radix development. Each ADR documents the context, the decision itself, alternatives considered, and the consequences.

The canonical ADR source files are maintained under [`spec/adr/`](../../../spec/adr/).

## ADR Index

| ADR | Title | Status | Summary |
|-----|-------|--------|---------|
| [ADR-001](#adr-001-three-layer-architecture) | Three-Layer Architecture | Proposed | Maximize verified code, minimize the TCB |
| [ADR-002](#adr-002-build-on-mathlib-bitvec) | Build on Mathlib BitVec | Proposed | Use `BitVec n` as specification-level canonical representation |
| [ADR-003](#adr-003-signed-integers-via-twos-complement-wrapper) | Signed Integers via Two's Complement Wrapper | Proposed | Signed types wrap unsigned storage for zero-cost abstraction |

---

## ADR-001: Three-Layer Architecture

**Status:** Proposed

**Context:** Radix provides formally verified low-level primitives while also interfacing with real operating systems. Formal verification cannot extend to FFI calls—there is always a boundary between verified and trusted code. The architecture must maximize the verified portion and minimize the trusted portion.

**Decision:** Adopt a three-layer architecture:

- **Layer 3 (Verified Specification)** — Pure mathematical specifications and theorems. No executable code.
- **Layer 2 (Verified Implementation)** — Pure Lean 4 implementations with proofs that they satisfy Layer 3 specifications.
- **Layer 1 (System Bridge)** — Lean 4 code wrapping built-in IO APIs. Contains named trusted assumptions (`axiom` declarations) asserting that IO behavior matches `System.Spec`.

```mermaid
graph TD
    L3["Layer 3: Specification<br/>(Pure math, BitVec, Prop)"]
    L2["Layer 2: Implementation<br/>(Computable, proven correct)"]
    L1["Layer 1: System Bridge<br/>(IO, trust_* axioms)"]

    L2 -->|"imports & proves conformance"| L3
    L1 -->|"states which spec it implements"| L3
    L1 -->|"may reuse"| L2

    style L3 fill:#4CAF50,color:white
    style L2 fill:#2196F3,color:white
    style L1 fill:#FF9800,color:white
```

**Import rules:**
| Layer | May Import |
|-------|-----------|
| Layer 3 (Spec) | Nothing (self-contained) |
| Layer 2 (Impl) | Layer 3 only |
| Layer 1 (Bridge) | Layer 3, optionally Layer 2 |

**Alternatives rejected:**
1. **Single-layer** — TCB boundary unclear; FFI changes break proofs.
2. **Two-layer** (spec+impl combined) — Implementation details leak into specification; harder to reason independently.
3. **F\*-style extraction** (verify in Lean 4, extract to C) — No Lean 4-to-C extraction pipeline exists; violates C-001.

**Rationale:** Proven successful in seL4 and CertiKOS. Provides a clear TCB boundary and enables independent verification.

**Consequences:** More files to manage, but a clear audit trail for TCB (inspect `@[extern]` + `trust_*` axioms).

> **Source:** [`spec/adr/0001-three-layer-architecture.md`](../../../spec/adr/0001-three-layer-architecture.md)

---

## ADR-002: Build on Mathlib BitVec

**Status:** Proposed

**Context:** Lean 4 Mathlib provides `BitVec n`, a fixed-width bitvector type with growing arithmetic/bitwise support. Radix needs fixed-width integer types as its foundation.

**Decision:** Use Mathlib's `BitVec n` as the **specification-level** canonical representation (Layer 3). Radix types in Layer 2 are defined as wrappers proven equivalent to `BitVec` operations.

```mermaid
graph LR
    subgraph "Layer 3 — Spec"
        BV["BitVec n<br/>(Mathlib)"]
    end
    subgraph "Layer 2 — Impl"
        U32["Radix.UInt32"]
        I32["Radix.Int32"]
    end
    U32 -->|"toBitVec / fromBitVec<br/>(proven equivalence)"| BV
    I32 -->|"toBitVec / fromBitVec<br/>(proven equivalence)"| BV
    style BV fill:#4CAF50,color:white
    style U32 fill:#2196F3,color:white
    style I32 fill:#2196F3,color:white
```

**Alternatives rejected:**
1. **Use `BitVec` directly everywhere** — No control over API; Mathlib upgrades may break everything.
2. **Completely independent implementation** — Massive proof duplication; lose community investment.

**Rationale:** Mathlib's `BitVec` is actively maintained with growing proof coverage. However, its API is designed for mathematical reasoning, not systems programming. Radix wrapper types provide a systems-friendly API while leveraging Mathlib proofs.

**Consequences:**
- Mathlib is a required dependency
- Radix types carry a proof of `BitVec` equivalence
- Users can drop down to `BitVec` when they need Mathlib lemmas directly

> **Source:** [`spec/adr/0002-build-on-mathlib-bitvec.md`](../../../spec/adr/0002-build-on-mathlib-bitvec.md)

---

## ADR-003: Signed Integers via Two's Complement Wrapper

**Status:** Proposed

**Context:** Lean 4 has no built-in signed fixed-width integer types. Its `Int` is arbitrary-precision. Systems programming requires `Int8`–`Int64` with two's complement semantics matching C's `int8_t`–`int64_t`.

**Decision:** Define signed integer types as structs wrapping Lean 4's built-in unsigned integer types:

```lean
structure Int8 where
  val : UInt8

structure Int32 where
  val : _root_.UInt32
```

The sign is determined by the MSB. Operations map directly to Lean 4's built-in `UIntX` operations (which compile to single C instructions), with correctness proven against a `BitVec` interpretation model.

**Alternatives rejected:**
1. **Wrapper around `Int` with bounds proof** — e.g., `(val : Int) (h : -128 ≤ val ∧ val ≤ 127)`. Every operation needs bounds proofs; not bit-compatible; completely fails NFR-002 (zero-cost abstractions).
2. **Wrapper around `BitVec`** — Lean 4's compiler does not currently map `BitVec` directly to C primitives. Every arithmetic operation would allocate objects, destroying performance.

**Rationale:** Zero-cost abstraction (NFR-002) is a hard constraint. Wrapping Lean 4's built-in `UIntX` types is the only way to guarantee that basic arithmetic compiles to raw CPU instructions. Using `BitVec` as the common foundation for both signed and unsigned types at the proof layer means shared proofs for bitwise operations.

**Consequences:**
- `Int8.bits` and `UInt8.bits` are the same type (`BitVec 8`)
- Casting between signed/unsigned is free (same bits, different interpretation)
- Sign-dependent operations (comparison, division, arithmetic right shift) need separate implementations with separate proofs

> **Source:** [`spec/adr/0003-signed-integers-twos-complement.md`](../../../spec/adr/0003-signed-integers-twos-complement.md)

---

## Template

For new ADRs, use the template at [`spec/adr/template.md`](../../../spec/adr/template.md).

## Related Documents

- [Principles](principles.md) — Design philosophy
- [Patterns](patterns.md) — Recurring patterns derived from these decisions
- [Architecture Overview](../architecture/) — System design
