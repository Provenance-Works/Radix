# ADR-001: Three-Layer Architecture

## Status
Proposed

## Context
Radix needs to provide formally verified low-level primitives while also
interfacing with real operating systems. Formal verification cannot extend
to FFI calls -- there is always a boundary between verified and trusted code.

We need an architecture that maximizes the verified portion and minimizes
the trusted (unverified) portion.

## Decision
Adopt a three-layer architecture:

- **Layer 3 (Verified Specification):** Pure mathematical specifications and
  theorems defining correct behavior. No executable code.
- **Layer 2 (Verified Implementation):** Pure Lean4 implementations with proofs
  that they satisfy Layer 3 specifications.
- **Layer 1 (System Bridge):** Lean4 code wrapping built-in IO APIs and
  (minimally) `@[extern]` bindings. Contains named trusted assumptions
  (`axiom` declarations, see C-004a) asserting that IO behavior matches
  `System.Spec`. The assumptions are part of the TCB; the Lean4 wrapping
  logic is verified code.

Layer interaction rules:
- Layer 3 (Spec) MUST NOT import Layers 2 or 1
- Layer 2 (Impl) MUST import Layer 3 (to prove conformance to specs)
- Layer 2 (Impl) MUST NOT import Layer 1 (pure computation, no IO)
- Layer 1 (Bridge) MUST import Layer 3 (to state which spec it implements)
- Layer 1 (Bridge) MAY import Layer 2 (to reuse verified pure logic)

User code imports:
- Layer 2 for pure verified computation (Word, Bit, Bytes, Memory, Binary)
- Layer 1 for effectful OS operations (System.IO, System.FFI)
- Layer 3 for reasoning and proof

## Alternatives Considered
1. **Single-layer approach (everything mixed)**
   - Overview: Specs, proofs, and FFI in the same modules
   - Pros: Simpler file structure
   - Cons: TCB boundary unclear; changes to FFI can break proofs;
     no clean separation of concerns

2. **Two-layer approach (spec+impl combined, separate FFI)**
   - Overview: Combine specifications and implementations, separate FFI
   - Pros: Fewer layers to manage
   - Cons: Harder to reason about specifications independently;
     implementation details leak into specification

3. **F*-style extraction (verify in Lean4, extract to C)**
   - Overview: Write verified code, generate C for execution
   - Pros: Native C performance
   - Cons: Requires a Lean4-to-C extraction pipeline that doesn't exist;
     massive engineering effort; violates project constraint C-001

## Rationale
The three-layer approach is proven successful in seL4 and CertiKOS.
It provides a clear TCB boundary, enables independent verification of
specifications, and allows different teams to work on different layers.

The clean separation also means that if Lean4's FFI mechanism changes,
only Layer 1 needs to be updated -- the verified core is unaffected.

## Consequences
- More files and directories to manage
- Clear audit trail for TCB (inspect `@[extern]` + `trust_*` assumptions)
- Specifications can be reviewed independently of implementation
- Proofs are robust against implementation changes (as long as the spec is stable)
