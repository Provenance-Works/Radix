# Architecture Overview

> **Audience**: Developers, Architects, Contributors

## System Context

Radix is a formally verified low-level systems programming library for Lean 4. It provides C-equivalent capabilities — fixed-width integers, bitwise operations, byte order conversions, memory abstractions, binary format DSL, system I/O, concurrency models, and bare-metal support — all with Mathlib-grade formal proofs.

```mermaid
graph TD
    UserCode["User Code<br/>(Lean 4 Application)"] -->|"imports"| Radix["Radix Library"]
    Radix -->|"depends on"| Mathlib["Mathlib<br/>(BitVec, Algebraic Structures)"]
    Radix -->|"Layer 1 wraps"| Lean4IO["Lean 4 Runtime<br/>(IO.FS, IO.Process)"]
    Lean4IO -->|"delegates to"| OS["Operating System<br/>(POSIX / Linux)"]
    style Radix fill:#4CAF50,color:white
    style Mathlib fill:#2196F3,color:white
    style Lean4IO fill:#FF9800,color:white
    style OS fill:#9E9E9E,color:white
```

## Three-Layer Architecture

Radix adopts a three-layer architecture inspired by seL4, CertiKOS, and F*/Low*:

```mermaid
graph TD
    subgraph "Layer 3: Verified Specification"
        L3["Pure mathematical definitions and theorems.<br/>No executable code — only specifications and proofs.<br/><i>'What does correct behavior mean?'</i>"]
    end
    subgraph "Layer 2: Verified Implementation"
        L2["Pure Lean 4 implementations proven to satisfy Layer 3 specs.<br/>Computable functions with attached correctness proofs.<br/><i>'An implementation that is provably correct.'</i>"]
    end
    subgraph "Layer 1: System Bridge"
        L1["Wrappers around Lean 4 built-in IO APIs.<br/>Contains named trusted assumptions (axiom declarations).<br/><i>'The minimal trusted boundary.'</i>"]
    end
    subgraph "Hardware / OS"
        HW["Operating System via Lean 4 Runtime"]
    end
    L3 --- L2
    L2 --- L1
    L1 --- HW
    style L3 fill:#4CAF50,color:white
    style L2 fill:#2196F3,color:white
    style L1 fill:#FF9800,color:white
    style HW fill:#9E9E9E,color:white
```

### Layer Interaction Rules

1. Layer 3 (Spec) **MUST NOT** import Layers 2 or 1
2. Layer 2 (Impl) **MUST** import Layer 3 (to prove conformance to specs)
3. Layer 2 (Impl) **MUST NOT** import Layer 1 (pure computation, no IO)
4. Layer 1 (Bridge) **MUST** import Layer 3 (to state which spec it implements)
5. Layer 1 (Bridge) **MAY** import Layer 2 (to reuse verified pure logic)

### How Each Module Maps to Layers

| Module | Layer 3 (Spec) | Layer 2 (Impl) | Layer 1 (Bridge) |
|--------|---------------|----------------|-----------------|
| Word | `Word.Spec`, `Word.Lemmas.*` | `Word.UInt`, `Word.Int`, `Word.Arith`, `Word.Conv`, `Word.Size`, `Word.Numeric` | — |
| Bit | `Bit.Spec` | `Bit.Ops`, `Bit.Scan`, `Bit.Field` | — |
| Bytes | `Bytes.Spec` | `Bytes.Order`, `Bytes.Slice` | — |
| Memory | `Memory.Spec` | `Memory.Model`, `Memory.Ptr`, `Memory.Layout` | — |
| Binary | `Binary.Spec`, `Leb128.Spec` | `Binary.Format`, `Binary.Parser`, `Binary.Serial`, `Leb128` | — |
| System | `System.Spec` | `System.Error`, `System.FD` | `System.IO`, `System.Assumptions` |
| Concurrency | `Concurrency.Spec` | `Concurrency.Ordering`, `Concurrency.Atomic` | `Concurrency.Assumptions` |
| BareMetal | `BareMetal.Spec` | `BareMetal.GCFree`, `BareMetal.Linker`, `BareMetal.Startup` | `BareMetal.Assumptions` |
| Alignment | `Alignment.Spec`, `Alignment.Lemmas` | `Alignment.Ops` | — |
| RingBuffer | `RingBuffer.Spec`, `RingBuffer.Lemmas` | `RingBuffer.Impl` | — |
| Bitmap | `Bitmap.Spec`, `Bitmap.Lemmas` | `Bitmap.Ops` | — |
| CRC | `CRC.Spec`, `CRC.Lemmas` | `CRC.Ops` | — |
| MemoryPool | `MemoryPool.Spec`, `MemoryPool.Lemmas` | `MemoryPool.Model` | — |
| UTF8 | `UTF8.Spec`, `UTF8.Lemmas` | `UTF8.Ops` | — |
| ECC | `ECC.Spec`, `ECC.Lemmas` | `ECC.Ops` | — |
| DMA | `DMA.Spec`, `DMA.Lemmas` | `DMA.Ops` | — |
| Timer | `Timer.Spec`, `Timer.Lemmas` | `Timer.Ops` | — |
| ProofAutomation | — | — | Meta-level tactic macros |

> **Note:** Fourteen modules are fully pure in v0.3.0: Word, Bit, Bytes, Memory, Binary, Alignment, RingBuffer, Bitmap, CRC, MemoryPool, UTF8, ECC, DMA, and Timer. Only System, Concurrency, and BareMetal cross the Layer 1 trusted boundary, while `ProofAutomation` remains a meta-level support module. This split is also exposed directly in the import surface as `Radix.Pure` and `Radix.Trusted`.

## Module Dependency Graph

```mermaid
graph TD
    Bit["Bit<br/>(Bitwise Ops)"] --> Word["Word<br/>(Fixed-Width Integers)"]
    Bytes["Bytes<br/>(Byte Order)"] --> Word
    Bytes --> Bit
    Numeric["Word.Numeric<br/>(Numeric Typeclasses)"] --> Word
    Numeric --> Bit
    Memory["Memory<br/>(Abstract Memory)"] --> Word
    Memory --> Bytes
    Binary["Binary<br/>(Format DSL)"] --> Word
    Binary --> Memory
    Binary --> Bit
    Binary --> Bytes
    Alignment["Alignment<br/>(Address Alignment)"] --> Word
    RingBuffer["RingBuffer<br/>(Circular Queue)"] --> Memory
    Bitmap["Bitmap<br/>(Dense Bitset)"] --> Word
    Bitmap --> Bit
    CRC["CRC<br/>(Checksums)"] --> Word
    CRC --> Bit
    MemoryPool["MemoryPool<br/>(Allocator Models)"] --> Memory
    MemoryPool --> Word
    UTF8["UTF8<br/>(Unicode Scalars)"]
    ECC["ECC<br/>(Error Correction)"]
    DMA["DMA<br/>(Transfer Model)"] --> Memory
    DMA -.->|"uses ordering model"| Concurrency
    Timer["Timer<br/>(Deadlines + Timeouts)"]
    ProofAutomation["ProofAutomation<br/>(Tactic Macros)"]
    System["System<br/>(OS Interface)"] --> Word
    System --> Bytes
    System --> Memory
    Concurrency["Concurrency<br/>(Atomic Ops)"] -.->|"models only"| Word
    BareMetal["BareMetal<br/>(No-OS Support)"] -.->|"models only"| Memory
    style Word fill:#4CAF50,color:white
    style Bit fill:#4CAF50,color:white
    style Bytes fill:#2196F3,color:white
    style Memory fill:#2196F3,color:white
    style Binary fill:#2196F3,color:white
    style Numeric fill:#66BB6A,color:white
    style Alignment fill:#66BB6A,color:white
    style RingBuffer fill:#2196F3,color:white
    style Bitmap fill:#2196F3,color:white
    style CRC fill:#2196F3,color:white
    style MemoryPool fill:#2196F3,color:white
    style UTF8 fill:#26A69A,color:white
    style ECC fill:#26A69A,color:white
    style DMA fill:#26A69A,color:white
    style Timer fill:#26A69A,color:white
    style ProofAutomation fill:#5C6BC0,color:white
    style System fill:#FF9800,color:white
    style Concurrency fill:#9C27B0,color:white
    style BareMetal fill:#9C27B0,color:white
```

Dependencies still flow upward from `Word`, but the current release now includes two extension layers: the v0.2.0 data-structure cluster (`Alignment`, `RingBuffer`, `Bitmap`, `CRC`, `MemoryPool`, and `Word.Numeric`) and the v0.3.0 composable cluster (`UTF8`, `ECC`, `DMA`, and `Timer`). Region algebra extends `Memory`, and `ProofAutomation` provides meta-level proof helpers outside the runtime layer stack.

## Trusted Computing Base (TCB)

The TCB is the set of components whose correctness is **assumed, not proven**:

| Component | Status |
|-----------|--------|
| Lean 4 compiler and runtime | Accepted as platform |
| Lean 4's built-in IO implementation | Trusted via named axioms |
| Lean 4's default axioms (`propext`, `Quot.sound`, `Classical.choice`) | Standard |
| `trust_*` axioms in `System.Assumptions` | Audited per release |
| `trust_*` axioms in `Concurrency.Assumptions` | Audited per release |
| `trust_*` axioms in `BareMetal.Assumptions` | Audited per release |

**Explicitly NOT in the TCB:**
- Mathlib (formally verified)
- Radix Layers 2–3 (proven)
- Radix Layer 1 Lean 4 code (verified; only the *assumption about IO behavior* is in the TCB)

## Key Design Decisions

| Decision | Summary | ADR |
|----------|---------|-----|
| Three-layer architecture | Maximize verified code, minimize trusted code | [ADR-001](../design/adr.md) |
| Build on Mathlib BitVec | Use `BitVec n` as spec-level canonical representation | [ADR-002](../design/adr.md) |
| Signed integers via two's complement | Wrap unsigned types, interpret MSB as sign | [ADR-003](../design/adr.md) |

## Related Documents

- [Components](components.md) — Detailed component breakdown
- [Module Dependencies](module-dependency.md) — Full dependency graph
- [Data Model](data-model.md) — Core data structures
- [Data Flow](data-flow.md) — Data flow through the system
- [Design Principles](../design/principles.md) — Guiding philosophy
