# ADR-003: Signed Integers via Two's Complement Wrapper

## Status
Proposed

## Context
Lean4 has no built-in signed fixed-width integer types.
Lean4's `Int` is arbitrary-precision.
Systems programming requires `Int8`, `Int16`, `Int32`, `Int64` with
two's complement semantics matching C's `int8_t`, `int16_t`, etc.

## Decision
Define signed integer types as a struct wrapping Lean 4's built-in 
unsigned integer types, with a formal specification linking them to `BitVec`.

```lean
structure Int8 where
  val : UInt8
```

The sign is determined by the MSB of the underlying unsigned value.
Operations are mapped directly to Lean 4's built-in `UIntX` operations
(which compile down to single C instructions), and their correctness
is proven against a `BitVec` interpretation model.

## Alternatives Considered
1. **Wrapper around Lean4's `Int` with modular reduction**
   - Overview: `structure Int8 := (val : Int) (h : -128 <= val /\ val <= 127)`
   - Pros: Simple definition; familiar integer semantics
   - Cons: Every operation needs bounds proofs; not bit-compatible;
     no direct relationship to hardware representation; completely fails
     NFR-002 (Zero-cost abstractions).

2. **Wrapper around unsigned types (chosen)**
   - Overview: `structure Int8 := (val : UInt8)`
   - Pros: Maps directly to Lean 4 runtime and therefore directly to C primitives
     (`uint8_t`), achieving NFR-002 (Zero-cost abstractions).
   - Cons: Sign interpretation is external; proof burden for sign-dependent
     operations (comparison, division, right shift) requires wrapping them in
     `@[extern]` or relying on bitwise implementations where native ones are missing.

3. **Wrapper around BitVec**
   - Overview: `structure Int8 := (bits : BitVec 8)`
   - Pros: Bit-level reasoning is natural; Mathlib support.
   - Cons: **Rejected due to NFR-002 violation.** Lean 4's compiler does not
     currently map `BitVec` directly to C primitives. This would cause every
     arithmetic operation to allocate objects and call library functions,
     destroying system programming performance.

## Rationale
Zero-cost abstraction (NFR-002) is a hard constraint for a system programming
library. Wrapping Lean 4's built-in `UIntX` types is the *only* way to guarantee
that basic arithmetic compiles down to raw CPU instructions in the current
Lean 4 compiler backend. Mathlib's `BitVec` will be used extensively in the
*proof* layer (Layer 3) to model the semantics of these operations, but the
*computational* layer (Layer 2) MUST use the built-in primitive types.

Using `BitVec` as the common foundation for both signed and unsigned types
also means shared proofs for bitwise operations (AND, OR, XOR, shifts)
that don't depend on sign interpretation.

## Consequences
- `Int8.bits` and `UInt8.bits` are the same type (`BitVec 8`)
- Casting between signed/unsigned is free (same bits, different interpretation)
- Bitwise operations share implementations
- Sign-dependent operations (comparison, division, arithmetic right shift) need
  separate implementations with separate proofs
