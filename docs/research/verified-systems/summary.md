# Research: Verified Systems Programming

Version: 0.1.0-draft
Last updated: 2026-03-07

## 1. F* / Low* / HACL* / EverParse (Microsoft Research)

### Overview
F* is a dependently-typed language designed for program verification.
Low* is a subset of F* that compiles to C via KaKrml.
HACL* is a formally verified cryptographic library built on Low*.
EverParse generates verified parsers for binary formats.

### Architecture
- High-level specifications in F* (functional style)
- Low-level implementations in Low* (imperative, C-like)
- Proofs that implementation matches specification
- Extraction to C for execution

### What Radix Can Learn
- The two-layer (spec + impl) approach works well
- Memory modeled via monadic state (HyperStack)
- Separating format descriptions from parser/serializer implementations
- Round-trip proofs are essential for binary formats

### What Radix Does Differently
- No extraction to C -- stay in Lean4's compilation pipeline
- Use Lean4's type system directly (dependent types, tactics)
- Build on Mathlib's existing algebraic hierarchy
- Target a broader scope than just crypto

### Assessment
HACL* is the gold standard for verified crypto. Radix does not aim to
replace it, but to provide the foundation on which equivalent libraries
could be built in the Lean4 ecosystem.

## 2. seL4 (Data61 / UNSW)

### Overview
First formally verified microkernel. Verified in Isabelle/HOL.
Proves functional correctness, integrity, and confidentiality.

### Architecture
- Abstract specification (Haskell-like functional model)
- Executable specification (Haskell prototype)
- C implementation
- Refinement proofs: abstract spec -> executable spec -> C

### What Radix Can Learn
- Refinement-based verification scales to large systems
- Abstract models of hardware/OS behavior are essential
- The abstract spec is more valuable than the implementation

### Assessment
seL4's refinement approach (spec -> impl -> low-level) maps well to
Radix's three-layer architecture.

## 3. CertiKOS (Yale)

### Overview
Verified concurrent OS kernel built in Coq.
Uses Certified Abstraction Layers (CAL) as core technique.

### Architecture
- Stack of abstraction layers, each verified separately
- Each layer provides a cleaner interface than the one below
- Composition theorem: if each layer is correct, the whole stack is correct

### What Radix Can Learn
- Layered abstraction is key to managing proof complexity
- Each module should define its own abstraction layer
- Composition of verified modules is a first-class concern

### Assessment
CAL is directly applicable to Radix's module architecture.
Each Radix module should be verifiable independently.

## 4. Verus (VMware Research / CMU)

### Overview
Automated verification tool for Rust. Uses SMT solvers (Z3) for proof
discharge. Designed for systems code verification.

### Architecture
- Rust code with verification annotations
- Ghost code (erased at runtime) for proofs
- SMT-based automation handles most proof obligations

### What Radix Can Learn
- Automation is critical for adoption
- Users should not need to write manual proofs for simple properties
- Ghost/erased proof terms are a good pattern

### Assessment
Verus shows that verification can be practical for systems code.
Radix should invest heavily in automation tactics.

## 5. Mathlib BitVec (Lean4)

### Overview
Mathlib provides `BitVec n` -- fixed-width bitvectors with some operations.

### Current State
- Basic arithmetic (+, -, *, /, %)
- Bitwise operations (AND, OR, XOR, NOT, shifts)
- Some proofs of basic properties
- Active development -- growing but incomplete

### Gaps That Radix Fills
- No signed integer abstraction
- No wrapping/saturating/checked arithmetic modes
- No bit scanning (clz, ctz, popcount)
- No rotate operations
- No endianness conversion
- No binary format tools
- No memory model
- No system call abstractions

### Integration Strategy
- Radix's specification layer uses `BitVec n` as the canonical representation
- Radix's implementation layer provides efficient wrappers
- Proofs establish equivalence between Radix operations and BitVec semantics
