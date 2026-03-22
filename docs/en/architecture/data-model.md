# Data Model

> **Audience**: Developers, Contributors

## Core Type Hierarchy

```mermaid
classDiagram
    class BitVec_n {
        <<Mathlib>>
        +toNat() Nat
        +toInt() Int
        +toFin() Fin (2^n)
    }
    class UInt8 {
        +val : _root_.UInt8
        +toBitVec() BitVec 8
        +toNat() Nat
        +toBuiltin() _root_.UInt8
    }
    class UInt16 {
        +val : _root_.UInt16
        +toBitVec() BitVec 16
        +toNat() Nat
    }
    class UInt32 {
        +val : _root_.UInt32
        +toBitVec() BitVec 32
        +toNat() Nat
    }
    class UInt64 {
        +val : _root_.UInt64
        +toBitVec() BitVec 64
        +toNat() Nat
    }
    class Int8 {
        +val : _root_.UInt8
        +toBitVec() BitVec 8
        +toInt() Int
    }
    class Int16 {
        +val : _root_.UInt16
        +toBitVec() BitVec 16
        +toInt() Int
    }
    class Int32 {
        +val : _root_.UInt32
        +toBitVec() BitVec 32
        +toInt() Int
    }
    class Int64 {
        +val : _root_.UInt64
        +toBitVec() BitVec 64
        +toInt() Int
    }
    class UWord {
        +val : BitVec w
        +toBitVec() BitVec w
    }
    class IWord {
        +val : BitVec w
        +toBitVec() BitVec w
    }
    BitVec_n <|-- UInt8 : spec equivalence
    BitVec_n <|-- UInt16 : spec equivalence
    BitVec_n <|-- UInt32 : spec equivalence
    BitVec_n <|-- UInt64 : spec equivalence
    BitVec_n <|-- Int8 : spec equivalence
    BitVec_n <|-- Int16 : spec equivalence
    BitVec_n <|-- Int32 : spec equivalence
    BitVec_n <|-- Int64 : spec equivalence
    BitVec_n <|-- UWord : spec equivalence
    BitVec_n <|-- IWord : spec equivalence
```

## Memory Data Structures

```mermaid
erDiagram
    Buffer ||--o{ ByteArray : wraps
    Buffer {
        ByteArray bytes
        Nat size
    }
    ByteSlice ||--o{ ByteArray : references
    ByteSlice {
        ByteArray data
        Nat start
        Nat len
        Proof valid
    }
    Ptr ||--|| Buffer : "points into"
    Ptr {
        Buffer buf
        Nat offset
        Proof inBounds
    }
    Region {
        Nat start
        Nat size
    }
    LayoutDesc ||--|{ FieldDesc : contains
    LayoutDesc {
        List_FieldDesc fields
        Nat totalSize
    }
    FieldDesc {
        String name
        Nat offset
        Nat size
    }
```

## Binary Format Types

```mermaid
erDiagram
    FormatSpec ||--|{ FieldSpec : contains
    FormatSpec {
        List_FieldSpec fields
    }
    FieldSpec {
        String name
        PrimType type
        Endian endian
        Nat offset
    }
    Format {
        inductive byte
        inductive uint16
        inductive uint32
        inductive uint64
        inductive padding
        inductive array
        inductive seq
    }
    FieldValue {
        inductive byte
        inductive uint16
        inductive uint32
        inductive uint64
        inductive array
    }
```

## System Types

```mermaid
stateDiagram-v2
    [*] --> Open : open file
    Open --> Open : read / write / seek
    Open --> Closed : close
    Closed --> [*]
```

```mermaid
erDiagram
    FD {
        Handle handle
        Ownership ownership
    }
    SysError {
        inductive permissionDenied
        inductive notFound
        inductive alreadyExists
        inductive resourceBusy
        inductive invalidArgument
        inductive noSpace
        inductive ioError
        inductive interrupted
        inductive endOfFile
        inductive invalidState
    }
```

## Concurrency Types

```mermaid
classDiagram
    class MemoryOrder {
        <<enumeration>>
        relaxed
        acquire
        release
        acqRel
        seqCst
    }
    class AtomicCell {
        +val : Nat
        +new(v) AtomicCell
    }
    class MemoryEvent {
        +thread : ThreadId
        +location : LocationId
        +kind : EventKind
        +order : MemoryOrder
    }
```

## v0.2.0 Data Structures

```mermaid
classDiagram
    class RingBuf {
        +buf : Memory.Buffer
        +capacity : Nat
        +head : Nat
        +tail : Nat
        +count : Nat
    }
    class Bitmap {
        +numBits : Nat
        +words : Array UInt64
        +hSize : words.size = wordsNeeded numBits
    }
    class BumpPool {
        +buf : Memory.Buffer
        +capacity : Nat
        +cursor : Nat
    }
    class SlabPool {
        +buf : Memory.Buffer
        +blockSize : Nat
        +blockCount : Nat
        +freeList : List Nat
        +allocated : List Nat
    }
    class CRCParams {
        +width : Nat
        +poly : Nat
        +init : Nat
        +xorOut : Nat
        +reflectIn : Bool
        +reflectOut : Bool
    }
    class HasAlignment {
        <<typeclass>>
        +alignment : Nat
    }
    class BoundedUInt {
        <<typeclass>>
        +minVal : α
        +maxVal : α
        +toNat(x) Nat
    }
    class BoundedInt {
        <<typeclass>>
        +minVal : α
        +maxVal : α
        +toInt(x) Int
    }
    RingBuf --> Buffer : uses
    Bitmap --> UInt64 : stores words in
    BumpPool --> Buffer : uses
    SlabPool --> Buffer : uses
```

These structures are the main v0.2.0 additions: queue state in `RingBuf`, dense bit storage in `Bitmap`, arena and slab allocation state in `BumpPool` and `SlabPool`, CRC parameterization in `CRCParams`, and width-generic abstractions via `HasAlignment`, `BoundedUInt`, and `BoundedInt`.

## Relationship: Radix Types ↔ BitVec

Every Radix integer type has a proven equivalence with `BitVec n`:

| Radix Type | Internal Storage | BitVec Width | Conversion |
|------------|-----------------|--------------|------------|
| `UInt8` | `_root_.UInt8` | `BitVec 8` | `toBitVec` / `fromBitVec` |
| `UInt16` | `_root_.UInt16` | `BitVec 16` | `toBitVec` / `fromBitVec` |
| `UInt32` | `_root_.UInt32` | `BitVec 32` | `toBitVec` / `fromBitVec` |
| `UInt64` | `_root_.UInt64` | `BitVec 64` | `toBitVec` / `fromBitVec` |
| `Int8` | `_root_.UInt8` | `BitVec 8` | `toBitVec` / `fromBitVec` |
| `Int16` | `_root_.UInt16` | `BitVec 16` | `toBitVec` / `fromBitVec` |
| `Int32` | `_root_.UInt32` | `BitVec 32` | `toBitVec` / `fromBitVec` |
| `Int64` | `_root_.UInt64` | `BitVec 64` | `toBitVec` / `fromBitVec` |
| `UWord` | `BitVec w` | `BitVec w` | `toBitVec` / `fromBitVec` |
| `IWord` | `BitVec w` | `BitVec w` | `toBitVec` / `fromBitVec` |

## Related Documents

- [Architecture Overview](README.md) — Three-layer architecture
- [Components](components.md) — Module breakdown
- [API Reference](../reference/api/) — Full API documentation
