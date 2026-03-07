# Glossary

Version: 0.1.0-draft
Last updated: 2026-03-07

| Term | Definition |
|------|-----------|
| TCB | Trusted Computing Base. The set of components whose correctness is assumed, not proven. In Radix: (1) Lean4 compiler/runtime, (2) Lean4 IO behavior assumptions, (3) default axioms, (4) any `@[extern]` declarations, (5) C ABI shims in `ffi/radix_ffi.c`, (6) named trusted assumptions (`trust_*` axiom declarations in System.Assumptions). See architecture.md Section 5 for the complete definition. |
| Layer 1 (System Bridge) | The Lean4 code that connects verified logic to OS operations. Uses Lean4 IO APIs and (minimally) `@[extern]`. Contains named trusted assumptions about IO behavior. The assumptions are part of the TCB; the Lean4 wrapping logic is not. |
| Layer 2 (Verified Implementation) | Pure Lean4 implementation of low-level primitives with proofs. |
| Layer 3 (Verified Specification) | Formal specifications and theorems defining correct behavior. |
| Wrapping arithmetic | Arithmetic that wraps around modulo 2^n on overflow. |
| Saturating arithmetic | Arithmetic that clamps to the type's min/max value on overflow. |
| Checked arithmetic | Arithmetic that returns `none` on overflow. |
| Two's complement | The standard representation of signed integers where the most significant bit represents the sign. All modern hardware uses this. |
| Endianness | Byte ordering. Big-endian: most significant byte first. Little-endian: least significant byte first. |
| BitField | A contiguous range of bits within a larger integer, used to pack multiple values into a single word. |
| Packed struct | A data structure with explicitly specified memory layout, no implicit padding. |
| Provenance | Metadata tracking which allocation a pointer originates from. Used to prevent pointer arithmetic across allocation boundaries. |
| `sorry` | A Lean4 axiom that admits any proposition without proof. MUST NOT appear in released Radix code. |
| DSL | Domain-Specific Language. In Radix, refers to embedded Lean4 syntax for describing binary formats. |
| Wire format | The exact byte-level representation of data as transmitted over a network or stored in a file. |
| Round-trip property | The property that serialization followed by deserialization (or vice versa) is the identity function. |
| Refinement | A formal relationship between an abstract specification and a concrete implementation proving that the implementation correctly realizes the specification. |
| POSIX | Portable Operating System Interface. The standard API for Unix-like operating systems. |
