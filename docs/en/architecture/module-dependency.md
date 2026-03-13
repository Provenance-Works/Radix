# Module Dependency Graph

> **Audience**: Developers, Contributors

## High-Level Dependencies

```mermaid
graph LR
    Word["Word"]
    Bit["Bit"] --> Word
    Bytes["Bytes"] --> Word
    Bytes --> Bit
    Memory["Memory"] --> Word
    Memory --> Bytes
    Binary["Binary"] --> Word
    Binary --> Bit
    Binary --> Bytes
    Binary --> Memory
    System["System"] --> Word
    System --> Bytes
    System --> Memory
    Concurrency["Concurrency"]
    BareMetal["BareMetal"]
    style Word fill:#4CAF50,color:white
    style Bit fill:#66BB6A,color:white
    style Bytes fill:#42A5F5,color:white
    style Memory fill:#29B6F6,color:white
    style Binary fill:#26C6DA,color:white
    style System fill:#FFA726,color:white
    style Concurrency fill:#AB47BC,color:white
    style BareMetal fill:#8D6E63,color:white
```

## Detailed Submodule Dependencies

```mermaid
graph TD
    subgraph "Word Module"
        WSpec["Word.Spec<br/>(Layer 3)"]
        WUInt["Word.UInt<br/>(Layer 2)"] --> WSpec
        WInt["Word.Int<br/>(Layer 2)"] --> WUInt
        WSize["Word.Size<br/>(Layer 2)"] --> WSpec
        WArith["Word.Arith<br/>(Layer 2)"] --> WUInt
        WArith --> WInt
        WArith --> WSize
        WConv["Word.Conv<br/>(Layer 2)"] --> WUInt
        WConv --> WInt
        WConv --> WSize
        WLemmas["Word.Lemmas.*<br/>(Layer 3)"] --> WArith
        WLemmas --> WConv
    end
    subgraph "Bit Module"
        BSpec["Bit.Spec<br/>(Layer 3)"]
        BOps["Bit.Ops<br/>(Layer 2)"] --> WUInt
        BOps --> WInt
        BOps --> WSize
        BScan["Bit.Scan<br/>(Layer 2)"] --> BOps
        BField["Bit.Field<br/>(Layer 2)"] --> BOps
        BLemmas["Bit.Lemmas<br/>(Layer 3)"] --> BScan
        BLemmas --> BField
    end
    subgraph "Bytes Module"
        BySpec["Bytes.Spec<br/>(Layer 3)"]
        ByOrd["Bytes.Order<br/>(Layer 2)"] --> WUInt
        ByOrd --> WInt
        BySlice["Bytes.Slice<br/>(Layer 2)"] --> ByOrd
        ByLemmas["Bytes.Lemmas<br/>(Layer 3)"] --> BySlice
    end
    subgraph "Memory Module"
        MSpec["Memory.Spec<br/>(Layer 3)"]
        MModel["Memory.Model<br/>(Layer 2)"] --> ByOrd
        MPtr["Memory.Ptr<br/>(Layer 2)"] --> MModel
        MLay["Memory.Layout<br/>(Layer 2)"]
        MLemmas["Memory.Lemmas<br/>(Layer 3)"] --> MModel
        MLemmas --> MPtr
        MLemmas --> MLay
    end
    subgraph "Binary Module"
        BnSpec["Binary.Spec<br/>(Layer 3)"]
        BnFmt["Binary.Format<br/>(Layer 2)"] --> BnSpec
        BnParser["Binary.Parser<br/>(Layer 2)"] --> BnFmt
        BnParser --> BySlice
        BnSerial["Binary.Serial<br/>(Layer 2)"] --> BnFmt
        BnLeb["Binary.Leb128<br/>(Layer 2)"] --> WUInt
        BnLeb --> WInt
        BnLemmas["Binary.Lemmas<br/>(Layer 3)"] --> BnParser
        BnLemmas --> BnSerial
    end
    subgraph "System Module"
        SSpec["System.Spec<br/>(Layer 3)"]
        SErr["System.Error<br/>(Layer 2)"]
        SFD["System.FD<br/>(Layer 2)"] --> SErr
        SIO["System.IO<br/>(Layer 1)"] --> SFD
        SIO --> SSpec
        SAssume["System.Assumptions<br/>(Layer 1)"] --> SSpec
    end
```

## External Dependencies

| Dependency | Source | Purpose |
|------------|--------|---------|
| **Mathlib** | `leanprover-community/mathlib4` | `BitVec n`, algebraic structures, proof tactics |
| **Batteries** | `leanprover-community/batteries` | Standard library extensions (transitive via Mathlib) |
| **Plausible** | `leanprover-community/plausible` | Property-based testing (transitive via Mathlib) |

## Dependency Principles

- **Word** has zero internal dependencies — it is the foundation
- **Bit** depends only on Word types (not on Word.Arith)
- **Bytes** depends on Word and Bit
- **Memory** depends on Word and Bytes (not on Bit directly)
- **Binary** depends on Word, Bit, Bytes, and Memory
- **System** depends on Word, Bytes, and Memory
- **Concurrency** and **BareMetal** are standalone model modules

## Related Documents

- [Architecture Overview](README.md) — High-level architecture
- [Components](components.md) — Component breakdown
- [Data Flow](data-flow.md) — Data flow between layers
