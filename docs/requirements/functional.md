# Functional Requirements

Version: 0.1.0-draft
Last updated: 2026-03-07

## FR-001: Fixed-Width Integer Arithmetic

Radix MUST provide signed and unsigned fixed-width integer types with full arithmetic operations.

### FR-001.1: Types

- `UInt8`, `UInt16`, `UInt32`, `UInt64` (unsigned)
- `Int8`, `Int16`, `Int32`, `Int64` (signed, two's complement)
- `UWord`, `IWord` (platform-sized pointer-width integers)

Lean4 has unsigned types built in but with limited operations.
Lean4 does NOT have signed fixed-width integers.
Radix MUST provide signed types with correct two's complement semantics.

### FR-001.1a: Platform-Sized Types (`UWord` / `IWord`)

`UWord` and `IWord` are pointer-width integers whose bit width depends on
the target platform (32 or 64 bits). They are intentionally named to avoid
shadowing Lean 4's built-in `USize`.

#### Parameterized Width Design

To support cross-compilation and proof portability, Radix MUST NOT hard-code
the platform pointer width via `System.Platform.numBits`.

`System.Platform.numBits` is resolved at **compile time on the host machine**.
If the host is 64-bit and the target is 32-bit, proofs and types would silently
bind to the wrong width.

Instead, Radix introduces an explicit width parameter:

```
-- Core definitions are parametric over platform width
variable (platformWidth : Nat) [h : PlatformWidth platformWidth]

-- PlatformWidth typeclass constrains width to realistic values
class PlatformWidth (n : Nat) where
  isValid : n = 32 ∨ n = 64
```

- All UWord/IWord definitions and proofs MUST be parametric over `platformWidth`
- A default instance resolves to `System.Platform.numBits` for native builds
- Cross-compilation targets provide an explicit width at instantiation time
- Proofs that hold for both 32 and 64 bits need not be duplicated
- Proofs that require a specific width MUST be gated by the `PlatformWidth` constraint

#### Type Definitions

- `UWord platformWidth` is defined as `BitVec platformWidth`
- `IWord platformWidth` is defined as `BitVec platformWidth` with signed interpretation
- For native builds, `UWord` (without argument) resolves via the default instance
- All operations defined for fixed-width types MUST also be defined for UWord/IWord

`UWord`/`IWord` are essential for:
- Array indexing
- Pointer arithmetic (see FR-006)
- System call arguments (see FR-007)
- Memory layout offset computation (see FR-004.3)

Radix MUST define `USize`/`ISize` in Phase 1 alongside other word types,
not defer them to a later phase.

### FR-001.2a: Division Edge Cases

The following table defines behavior for `/` edge cases.
All cells MUST be formally proven to match this specification.

**`x / 0` (division by zero):**

Division by zero is **not overflow** -- it is a fundamentally undefined
operation. Because pure functions in Lean 4 cannot halt execution via
exceptions, Lean's `panic!` macro does NOT abort the program; instead,
it returns a default value configured by the `Inhabited` typeclass
(which is `0` for numeric types). 

Because a silent return of `0` creates a massive security risk in
systems programming (buffer-start access, null-pointer deref), and
because `panic!` cannot prevent this, **no Tier 2 function may panic.**

Instead, the `Option` returned by `Checked` is the **only** safe fallback
for zero division in an unproven context. The `Wrapping`, `Saturating`,
and `Overflowing` variants MUST require a proof of non-zero divisor,
just like Tier 1.

| Mode        | Signature Requirement                     |
|-------------|-------------------------------------------|  
| Proof-based | `div (x y) (h : y != 0) : UIntN`          |
| Checked     | `checkedDiv (x y) : Option UIntN`         |

*(Note: Wrapping, Saturating, and Overflowing modes are omitted for division and remainder, as those operations do not wrap in the arithmetic sense and treating a zero-division by enforcing a proof perfectly defeats the purpose of the Tier 2 convenience wrapper. `checkedDiv` serves as the sole safe fallback.)*

This diverges from Rust (where wrapping/saturating div crash on 0)
precisely because Lean cannot crash safely in pure contexts. The only
total function over the full domain without proofs is `checkedDiv`.

**`Int(n).MIN / -1` (signed overflow):**

| Mode        | Result      | Flag/Option      | Rust comparison             |
|-------------|-------------|------------------|-----------------------------|  
| Wrapping    | MIN (wraps) | --               | Same as Rust wrapping_div   |
| Saturating  | MAX (clamps)| --               | Same as Rust saturating_div |
| Checked     | `none`      | --               | Same as Rust checked_div    |
| Overflowing | (MIN, true) | overflowed=true  | Same as Rust overflowing_div|

### FR-001.2b: Remainder Edge Cases

**`x % 0` (remainder by zero):**

| Mode        | Signature Requirement                     |
|-------------|-------------------------------------------|  
| Proof-based | `rem (x y) (h : y != 0) : UIntN`          |
| Checked     | `checkedRem (x y) : Option UIntN`         |

Same rationale as division by zero: Lean's `panic!` cannot trap safely,
therefore all modes except `Checked` MUST demand a proof of `y != 0`.

**`Int(n).MIN % -1` (signed overflow):**

Mathematically the result is 0 (no remainder). However, on some hardware
this triggers the same trap as `MIN / -1` because division and remainder
are computed together.

| Mode        | Result | Flag/Option      | Rust comparison                |
|-------------|--------|------------------|--------------------------------|
| Wrapping    | 0      | --               | Same as Rust wrapping_rem      |
| Saturating  | 0      | --               | Same as Rust (result fits)     |
| Checked     | `none` | --               | Same as Rust checked_rem       |
| Overflowing | (0, true)| overflowed=true| Same as Rust overflowing_rem   |

Radix treats `MIN % -1` as overflow in Checked and Overflowing modes for
consistency with Rust and to avoid masking the paired division overflow.
The mathematical result (0) is still returned in Wrapping/Saturating since
it fits in range.

### FR-001.3: Proofs

Each operation MUST have the following properties formally proven:

- Commutativity, associativity, distributivity where applicable
- Overflow behavior matches specification
- Wrapping arithmetic forms a ring (mod 2^n)
- Signed/unsigned conversion is bit-preserving

## FR-002: Bitwise Operations

Radix MUST provide bitwise operations with formal proofs.

### FR-002.1: Basic Operations

- AND, OR, XOR, NOT
- Left shift, right shift (logical and arithmetic)
- Rotate left, rotate right

### FR-002.1a: Shift and Rotate Edge Cases

All shift/rotate operations take a `UInt` shift count.
Behavior when `count >= bitWidth`:

| Operation         | count >= bitWidth behavior          |
|-------------------|-------------------------------------|
| Logical left shift  | `count % bitWidth` (Rust semantics) |
| Logical right shift | `count % bitWidth` (Rust semantics) |
| Arithmetic right shift | `count % bitWidth` (Rust semantics) |
| Rotate left       | `count % bitWidth` (rotate is naturally modular) |
| Rotate right      | `count % bitWidth` (rotate is naturally modular) |

Rationale: Rust's `wrapping_shl`/`wrapping_shr` mask the shift count to
`count % bitWidth`. This is defined, portable, and matches what most
hardware does (x86 masks to 5/6 bits for 32/64-bit shifts).
C leaves shift-by-width as undefined behavior; we explicitly reject that.

Each shift/rotate operation MUST be formally proven to satisfy this table.

### FR-002.2: Bit Scanning

- `clz` (count leading zeros)
- `ctz` (count trailing zeros)
- `popcount` (population count / Hamming weight)
- `bitReverse`

### FR-002.3: Proofs

- De Morgan's laws
- Shift/rotate identities
- `popcount` properties (e.g., `popcount(x XOR y) = Hamming distance`)
- Relationship between `clz`/`ctz` and `log2`

## FR-003: Byte Order and Endianness

Radix MUST provide endianness-aware byte manipulation.

### FR-003.1: Conversion Functions

- `toBigEndian` / `fromBigEndian`
- `toLittleEndian` / `fromLittleEndian`
- `toNativeEndian` / `fromNativeEndian`
- `byteSwap`

### FR-003.2: Proofs

- Round-trip property: `fromBigEndian (toBigEndian x) = x`
- `byteSwap (byteSwap x) = x` (involution)
- Relationship between big/little endian conversions

## FR-004: Binary Data Manipulation

Radix MUST provide tools for working with raw binary data.

### FR-004.1: ByteSlice

- Bounds-checked view into `ByteArray`
- Zero-copy slicing with proof of bounds
- Read/write operations at arbitrary offsets for all fixed-width types

### FR-004.2: BitField

- Define bit fields within integers
- Extract and insert fields with proof of bit-correctness
- Named field access via structure-like syntax

### FR-004.3: Packed Struct Layout

- Declarative specification of memory layout
- Field offset and size computation
- Alignment specification
- Serialization/deserialization with correctness proofs

### FR-004.4: Proofs

- Slice bounds are always valid
- Field extraction/insertion is lossless round-trip
- Packed struct layout matches specification exactly

## FR-005: Binary Format DSL

Radix MUST provide a declarative DSL for specifying binary wire formats.

### FR-005.1: Format Description

- Specify fields with types, sizes, endianness
- Conditional fields (dependent on previous field values)
- Repeated fields (arrays with length from another field)
- Alignment and padding

### FR-005.2: Code Generation

- Generate verified parser from format description
- Generate verified serializer from format description
- Parser and serializer MUST be proven inverses of each other

## FR-006: Abstract Memory Model

Radix MUST provide an abstract memory model for formal reasoning.

### FR-006.1: Memory Regions

- Model memory as typed regions
- Bounds tracking at the type level
- Non-overlapping region proofs

### FR-006.2: Pointer Abstraction

- Abstract pointer type with provenance tracking
- Pointer arithmetic with bounds proofs
- Cast between pointer types with alignment proofs

### FR-006.3: Proofs

- Memory safety: all accesses within bounds
- No aliasing violations in verified code
- Alignment correctness

## FR-007: System Call Model

Radix MUST provide an abstract model of POSIX system calls.

### FR-007.1: File Operations

- `open`, `close`, `read`, `write`, `seek`
- File descriptor abstraction
- Error code modeling  

### FR-007.2: Process & Environment (Deferred)

- Out of scope for Phase 1. To be defined in later phases depending on Lean 4 IO capabilities.

### FR-007.3: Implementation Strategy

  - File operations and strictly all OS interactions MUST use Lean4 builtin IO.FS API.
  - The use of @[extern], C language FFI, and custom ABI shims is strictly forbidden across the entire project to guarantee absolute memory safety and elimination of TCB corruption (ADR C-001).
  - Operations lacking pure Lean4 API equivalents (e.g., custom mmap, mprotect) are explicitly out of scope for Layer 1.

### FR-007.4: Proofs and Error Handling

- Abstract model in System.Spec defines idealized POSIX semantics
- Resource lifecycle (open -> use -> close) MUST be modeled
- Error handling strategy:
  - Radix defines `Radix.System.Error`, a normalized error type that covers
    common POSIX error classes (permission denied, not found, IO error, etc.)
  - Lean4's `IO.FS` does NOT expose raw POSIX errno values. Radix MUST NOT
    claim full POSIX errno coverage when using `IO.FS`-based operations.
  - For `IO.FS`-based operations (open, close, read, write, seek):
    Radix maps Lean4's `IO.Error` to `Radix.System.Error`. Coverage is
    limited to what Lean4 exposes. This limitation is a documented trusted
    assumption in `System.Assumptions`.

## FR-008: Atomicity and Memory Ordering (Future Phase)

### FR-008.1: Memory Ordering
- Model of atomic load/store/CAS
- Memory ordering model (Relaxed, Acquire, Release, SeqCst)

### FR-008.2: Proofs
- Linearizability of atomic operations
- Absence of data races in verified code
