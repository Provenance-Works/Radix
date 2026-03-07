# Non-Functional Requirements

Version: 0.1.0-draft
Last updated: 2026-03-07

## NFR-001: Proof Quality

All proofs MUST be Mathlib-grade quality.

- No `sorry` in released code
- No `native_decide` for non-trivial propositions where avoidable
- Proofs SHOULD be structured and readable, not just tactic golf
- Lemma names MUST follow Mathlib naming conventions

## NFR-002: Performance

Radix MUST NOT introduce unreasonable overhead for operations that have direct hardware equivalents.

### NFR-002.1: Performance Goals

- Bitwise operations SHOULD compile to the corresponding CPU instructions via Lean4's compiler
- Arithmetic operations MUST NOT be slower than **1.5x** native C equivalents for the same operation.
  For basic integer math (+, -, *, &, |, ^), the overhead MUST be exactly 0 (same instruction count).
- Zero-cost abstractions where possible: proofs are erased at runtime; structural
  wrappers around scalar types vanish during compilation.

### NFR-002.2: Measurement Method

Performance claims MUST be verified by reproducible benchmarks.

**Target platform for benchmarks:**
- OS: Linux x86_64 (Ubuntu 22.04 or later)
- Lean4: stable toolchain (version pinned in lean-toolchain)
- C baseline: GCC or Clang with `-O2`, same machine

**Benchmark workload:**
- Microbenchmarks for individual operations (add, mul, div, shift, popcount, etc.)
- Each benchmark runs the operation 10^6 times in a tight loop
- Measure wall-clock time with `IO.monoNanosNow`
- C baseline uses equivalent loop with `clock_gettime(CLOCK_MONOTONIC)`

**Anti-optimization (DCE/LICM) countermeasures:**

Pure arithmetic in tight loops is subject to Dead Code Elimination (DCE)
and Loop Invariant Code Motion (LICM) by both LLVM and GCC at `-O2`.
A loop whose result is never observed can be deleted entirely, producing
meaningless 0ns measurements.

All benchmarks MUST apply the following countermeasures:
- **Accumulator sink:** Each iteration feeds its result into the next
  iteration's input (e.g., `acc = f(acc, data[i])`). The final accumulator
  MUST be written to a `volatile` variable (C) or passed to an `@[noinline]`
  function / `IO.println` (Lean4) to force materialization.
- **Input-dependent operands:** Operands MUST NOT be compile-time constants.
  Use a pre-generated array of pseudo-random values and index into it per
  iteration. This defeats constant folding and loop-invariant hoisting.
- **Validation step:** Each benchmark MUST print the final accumulator value.
  If the printed value is 0 for a non-trivial workload, the benchmark is
  considered invalid (likely optimized away) and MUST be investigated.
- **C baseline flags:** C benchmarks MUST use the exact flags
  `-O2 -fno-builtin` and verify that the generated assembly contains
  the expected loop (via `objdump -d` spot check, documented per release).
- **Lean4 code gen check:** Inspect `build/ir/` output (Lean4's generated C)
  to confirm the loop body contains the target operation. If the operation
  is absent, the benchmark is invalid.

**Acceptance criteria:**
- Lean4-compiled Radix basic arithmetic operation time <= 1.5x C baseline time
- Measured as median of 5 runs, after 2 warmup runs
- Results recorded in `benchmarks/results/` with date, toolchain version, and hardware

**Code generation verification:**
- For critical operations (bitwise, shifts, arithmetic), inspect Lean4's generated C code
  (via `lake build` intermediate output) to confirm expected primitive mapping (`uint8_t`, etc.).
- The baseline math operations MUST NOT result in heap allocations or `lean_dec / lean_inc` calls.
- Document any operation that does NOT map to a single instruction

**When to run:**
- Before each release
- After any change to core arithmetic implementations
- Results stored in version control for regression tracking

## NFR-003: Ergonomics

Radix MUST be usable by Lean4 developers who are not proof experts.

- Common operations SHOULD work without manual proof obligations
- `decide` and automation tactics SHOULD discharge simple proof obligations automatically
- Clear error messages when proof obligations cannot be automatically discharged

## NFR-004: Modularity

Radix MUST be modular so users can depend on only what they need.

- Each major component (Word, Bit, Bytes, Memory, Binary, System) MUST be independently importable
- Minimal inter-module dependencies
- No circular dependencies between modules

## NFR-005: Compatibility

- Radix MUST be compatible with Mathlib's `BitVec` and related types
- Radix MUST provide conversion functions to/from Lean4 built-in types
- Radix SHOULD interoperate with Lean4's `ByteArray` without copying

## NFR-006: Documentation

- Every public definition MUST have a docstring
- Every module MUST have a module docstring explaining its purpose
- Important lemmas MUST have usage examples in the examples/ directory

## NFR-007: Testing

- Property-based testing for all arithmetic operations
- Cross-validation against known-correct C implementations where applicable
- Proof checking via `lake build` is the primary correctness mechanism

## NFR-008: Lean4 Version Compatibility

- Radix MUST target Lean4 stable toolchain
- Breaking changes in Lean4 SHOULD be tracked and adapted promptly
- Mathlib version dependency MUST be explicitly specified
