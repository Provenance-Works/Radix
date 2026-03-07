# ADR-002: Build on Mathlib BitVec

## Status
Proposed

## Context
Lean4's Mathlib provides `BitVec n`, a fixed-width bitvector type with
growing support for arithmetic and bitwise operations. Radix needs
fixed-width integer types as its foundation.

We need to decide whether to build on Mathlib's `BitVec` or create
our own from scratch.

## Decision
Use Mathlib's `BitVec n` as the **specification-level** canonical
representation (Layer 3).

Radix types in Layer 2 are defined as wrappers that are proven
equivalent to `BitVec` operations.

Mathlib is formally verified, so using it does NOT expand the TCB.
Radix MAY depend on Mathlib extensively for algebraic structures,
tactics, and existing proofs.

## Alternatives Considered
1. **Build entirely on BitVec (no wrappers)**
   - Overview: Use `BitVec n` directly everywhere
   - Pros: No duplication; direct Mathlib lemma reuse
   - Cons: No control over API; `BitVec` API may not match
     systems programming patterns; upgrading Mathlib may break everything

2. **Completely independent implementation**
   - Overview: Define Radix types from scratch, ignore Mathlib
   - Pros: Full control; no Mathlib dependency
   - Cons: Massive proof duplication; lose community investment;
     interop with Lean4 ecosystem is harder

3. **BitVec for specs, wrappers for impl (chosen)**
   - Overview: BitVec is the specification; Radix types are the ergonomic API
   - Pros: Leverage existing proofs; clean API; controlled interop
   - Cons: Need to prove equivalence between wrapper operations and BitVec

## Rationale
Mathlib's `BitVec` is actively maintained and has growing proof coverage.
Re-implementing all of that from scratch would be wasteful.

However, `BitVec`'s API is designed for mathematical reasoning, not for
systems programming. Radix needs types like `Int16` (signed) and operations
like `wrappingAdd` that `BitVec` does not prioritize.

By using `BitVec` at the spec level and providing Radix-specific wrappers,
we get the best of both worlds: Mathlib's proof library and a
systems-programming-friendly API.

## Consequences
- Mathlib is a required dependency
- Radix types carry a proof of `BitVec` equivalence
- Mathlib version upgrades need testing but should be manageable
- Users can drop down to `BitVec` when they need Mathlib lemmas directly
