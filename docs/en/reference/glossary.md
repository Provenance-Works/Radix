# Glossary

> **Audience**: All

| Term | Definition |
|------|-----------|
| **TCB** | Trusted Computing Base. The set of components whose correctness is assumed, not proven. In Radix: Lean 4 compiler/runtime, IO behavior assumptions, default axioms, and `trust_*` axiom declarations in `System.Assumptions`. |
| **Layer 1 (System Bridge)** | Lean 4 code connecting verified logic to OS operations. Uses Lean 4 IO APIs. Contains named trusted assumptions. |
| **Layer 2 (Verified Implementation)** | Pure Lean 4 implementation of low-level primitives with proofs of correctness. |
| **Layer 3 (Verified Specification)** | Formal specifications and theorems defining correct behavior. No executable code. |
| **BitVec n** | Mathlib's fixed-width bitvector type. Used as the canonical specification-level representation for all Radix integer types. |
| **Wrapping arithmetic** | Arithmetic that wraps around modulo 2^n on overflow. E.g., `UInt8: 255 + 1 = 0`. |
| **Saturating arithmetic** | Arithmetic that clamps to the type's min/max value on overflow. E.g., `UInt8: 255 + 1 = 255`. |
| **Checked arithmetic** | Arithmetic that returns `none` on overflow. E.g., `UInt8: checkedAdd 255 1 = none`. |
| **Overflowing arithmetic** | Arithmetic returning both the wrapping result and a Boolean overflow flag. E.g., `UInt8: overflowingAdd 255 1 = (0, true)`. |
| **Two's complement** | The standard representation of signed integers where the MSB represents the sign. All modern hardware uses this. Radix's `Int8`–`Int64` use this encoding. |
| **Endianness** | Byte ordering. Big-endian: most significant byte first. Little-endian: least significant byte first. |
| **bswap** | Byte swap — reverses the byte order of a multi-byte integer. Involution: `bswap(bswap(x)) = x`. |
| **BitField** | A contiguous range of bits within a larger integer, used to pack multiple values into a single word. |
| **ByteSlice** | A bounds-checked, zero-copy view into a `ByteArray` with proof of valid bounds. |
| **Packed struct** | A data structure with explicitly specified memory layout, no implicit padding. Modeled by `Memory.Layout`. |
| **Provenance** | Metadata tracking which allocation a pointer originates from. Used in `Memory.Ptr`. |
| **LEB128** | Little Endian Base 128. A variable-length integer encoding used in WebAssembly, DWARF, Protocol Buffers. |
| **Round-trip property** | The property that serialization followed by deserialization is the identity function. Formally proven for all Radix encode/decode operations. |
| **DSL** | Domain-Specific Language. In Radix, the `Binary.Format` inductive for describing binary wire formats. |
| **Wire format** | The exact byte-level representation of data as transmitted or stored. |
| **Refinement** | A formal relationship between an abstract specification and a concrete implementation proving that the implementation correctly realizes the specification. |
| **POSIX** | Portable Operating System Interface (IEEE Std 1003.1). The standard API for Unix-like operating systems. |
| **sorry** | A Lean 4 axiom that admits any proposition without proof. **MUST NOT** appear in released Radix code. |
| **PlatformWidth** | A typeclass constraining a natural number to `n = 32 ∨ n = 64`, used to parameterize `UWord`/`IWord`. |
| **Tier 1 API** | Proof-carrying API requiring precondition proofs. Zero runtime cost (proofs erased at compile time). |
| **Tier 2 API** | Convenience API without proof requirements. Uses `Option`, wrapping, saturation, or overflow flags. |
| **MemoryOrder** | Memory ordering for atomic operations: `relaxed`, `acquire`, `release`, `acqRel`, `seqCst`. |
| **AtomicCell** | Abstract model of an atomic memory location supporting load/store/CAS/fetch operations. |
| **GCFree** | A constraint ensuring code uses no garbage-collected heap allocations, required for bare-metal environments. |
| **LinkerScript** | A model of ELF linker scripts specifying section placement, symbols, and memory regions. |

## See Also

- [Architecture Overview](../architecture/README.md) — System design context
- [Errors](errors.md) — Error types reference
- [日本語版](../../ja/reference/glossary.md) — Japanese version
