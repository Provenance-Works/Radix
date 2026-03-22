# Design Principles

> **Audience**: All

## Core Philosophy

Radix is a formally verified low-level systems programming library for Lean 4. Its design is guided by a clear hierarchy of priorities:

```
Correctness > Safety > Performance > Ergonomics
```

Every design decision is evaluated against this hierarchy. Correctness is never sacrificed for performance; safety is never sacrificed for ergonomics.

## Principles

### 1. Maximize Verified, Minimize Trusted

Inspired by seL4 and CertiKOS, Radix's three-layer architecture maximizes the formally verified portion of the codebase and minimizes the Trusted Computing Base (TCB).

- **Layers 2–3** (specifications, implementations, proofs): Fully verified by Lean 4's kernel. Zero trust needed.
- **Layer 1** (system bridge): Minimal code that wraps Lean 4's built-in IO APIs. Contains named trusted axioms (`trust_*`) citing external specifications. This is the only part of Radix that requires human audit.
- **Mathlib**: Formally verified. Does NOT expand the TCB.

The TCB consists solely of: Lean 4 compiler/runtime, `trust_*` axiom declarations, and Lean 4's default axioms (`propext`, `Quot.sound`, `Classical.choice`).

### 2. Zero-Cost Abstraction (NFR-002)

Types and operations must compile to efficient machine code:

- Radix's `UInt32` wraps Lean 4's built-in `_root_.UInt32`, which compiles to C's `uint32_t`. The wrapper is erased at compile time.
- All `@[inline]` functions are inlined by the compiler.
- Proofs are erased at runtime — Tier 1 (proof-carrying) APIs have zero overhead versus Tier 2 (checked) APIs.
- Signed types (`Int8`–`Int64`) wrap unsigned types — same storage, different interpretation. No heap allocation for sign representation.

### 3. Strict Pure Lean 4 Policy (C-001)

Radix **strictly prohibits** custom C code, FFI bindings, and `@[extern]` calls to custom C ABI shims. All OS interaction goes through Lean 4's built-in IO libraries (`IO.FS`, `IO.Process`, etc.).

**Rationale:** Custom C interop risks memory leaks, use-after-free, and file descriptor recycling bugs due to imperfect interaction with Lean 4's reference-counting runtime. By staying within Lean 4's managed IO boundary, Radix maintains full safety guarantees.

### 4. BitVec as Specification Language (ADR-002)

Mathlib's `BitVec n` is the canonical specification-level representation for all Radix integer types:

- **Layer 3**: Specifications are written in terms of `BitVec n`
- **Layer 2**: Implementations use Lean 4 built-in types for performance
- **Proofs**: Equivalence between Layer 2 operations and Layer 3 `BitVec` specifications is formally proven

This gives users two paths: use Radix types for efficient computation, or drop to `BitVec` for Mathlib-powered reasoning.

### 5. Tiered API Design

Every module that involves bounds or validity checking offers two API tiers:

| Tier | Style | Cost | Use When |
|------|-------|------|----------|
| **Tier 1** | Proof-carrying: caller provides proof of precondition | Zero runtime cost (proof erased) | Bounds known at compile time |
| **Tier 2** | Checked: returns `Option` or wraps/saturates | Minimal runtime cost (one branch) | Bounds determined at runtime |

Example:
```lean
-- Tier 1: zero-cost, proof required
def Buffer.readU8 (buf : Buffer) (offset : Nat) (h : offset < buf.size) : UInt8

-- Tier 2: convenience, returns Option
def Buffer.checkedReadU8 (buf : Buffer) (offset : Nat) : Option UInt8
```

### 6. Named Trusted Assumptions (C-004a)

All axioms about the external world follow a strict discipline:

- Must be `axiom` declarations (not `opaque`, not `constant`)
- Must use the `trust_` prefix
- Must be `Prop`-typed
- Must cite the external specification grounding the assumption (POSIX, ARM manual, etc.)
- Must be collected in dedicated `Assumptions.lean` files
- Must be auditable: each `trust_*` axiom is a clear, reviewable claim about external behavior

### 7. No Mathematical Axioms Beyond Lean 4 Defaults (C-004)

Radix does not introduce custom mathematical axioms. The `trust_*` axioms in Layer 1 are assertions about the physical world (OS behavior, hardware semantics), not mathematical claims. The distinction is fundamental: mathematical axioms affect proof soundness globally; external-world axioms are localized trust assumptions.

### 8. Modular Independence

Modules are designed for independent use:

- `Word` has zero internal dependencies — it is the foundation
- Each module can be imported individually (`import Radix.Word`)
- Dependencies flow strictly upward: `Word → Bit → Bytes → Memory → Binary`
- `Concurrency` and `BareMetal` are standalone model modules with no inter-dependencies

### 9. Shift Count Normalization (FR-002.1a)

All shift and rotate operations normalize by `count % bitWidth`, matching Rust's semantics. This is a deliberate design choice:

- C leaves behavior of out-of-range shifts **undefined**
- Rust normalizes (wraps the count)
- Radix follows Rust: defined, predictable behavior for all inputs

### 10. Complete Signed Division Handling (FR-001.2a/b)

The `MIN / -1` edge case (signed overflow) is handled explicitly in all 4 arithmetic modes:

| Mode | `MIN / -1` result | `MIN % -1` result |
|------|-------------------|-------------------|
| Wrapping | `MIN` (wraps) | `0` |
| Saturating | `MAX` (clamps) | `0` |
| Checked | `none` | `none` |
| Overflowing | `(MIN, true)` | `(0, true)` |

This is formally specified in `Word.Spec` and proven for all signed types in `Word.Lemmas.Overflow`.

## Related Documents

- [Architecture Overview](../architecture/) — Three-layer architecture
- [Patterns](patterns.md) — Design patterns
- [ADRs](adr.md) — Decision records
