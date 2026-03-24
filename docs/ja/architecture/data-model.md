# データモデル

> **対象読者**: 開発者、コントリビューター

## コア型階層

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
    BitVec_n <|-- UInt8 : 仕様等価性
    BitVec_n <|-- UInt16 : 仕様等価性
    BitVec_n <|-- UInt32 : 仕様等価性
    BitVec_n <|-- UInt64 : 仕様等価性
    BitVec_n <|-- Int8 : 仕様等価性
    BitVec_n <|-- Int16 : 仕様等価性
    BitVec_n <|-- Int32 : 仕様等価性
    BitVec_n <|-- Int64 : 仕様等価性
    BitVec_n <|-- UWord : 仕様等価性
    BitVec_n <|-- IWord : 仕様等価性
```

## メモリデータ構造

```mermaid
erDiagram
    Buffer ||--o{ ByteArray : ラップ
    Buffer {
        ByteArray bytes
        Nat size
    }
    ByteSlice ||--o{ ByteArray : 参照
    ByteSlice {
        ByteArray data
        Nat start
        Nat len
        Proof valid
    }
    Ptr ||--|| Buffer : "を指す"
    Ptr {
        Buffer buf
        Nat offset
        Proof inBounds
    }
    Region {
        Nat start
        Nat size
    }
    LayoutDesc ||--|{ FieldDesc : 含む
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

## バイナリフォーマット型

```mermaid
erDiagram
    FormatSpec ||--|{ FieldSpec : 含む
    FormatSpec {
        List_FieldSpec fields
    }
    FieldSpec {
        String name
        FieldType type
        Nat offset
    }
    Format {
        inductive byte
        inductive uint16
        inductive uint32
        inductive uint64
        inductive bytes
        inductive lengthPrefixedBytes
        inductive countPrefixedArray
        inductive constBytes
        inductive padding
        inductive align
        inductive array
        inductive seq
    }
    FieldValue {
        inductive byte
        inductive uint16
        inductive uint32
        inductive uint64
        inductive bytes
        inductive array
    }
```

## システム型

```mermaid
stateDiagram-v2
    [*] --> Open : ファイルを開く
    Open --> Open : 読み取り / 書き込み / シーク
    Open --> Closed : クローズ
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

## 並行処理型

```mermaid
classDiagram
    class MemoryOrder {
        <<列挙型>>
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

## v0.2.0 のデータ構造

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

これらは v0.2.0 の主要追加型です。`RingBuf` は FIFO キュー状態、`Bitmap` は高密度ビット格納、`BumpPool` と `SlabPool` はアロケータ状態、`CRCParams` は CRC アルゴリズムの設定、`HasAlignment`・`BoundedUInt`・`BoundedInt` は幅非依存 API の型クラスを表します。

## 関連ドキュメント

- [アーキテクチャ概要](README.md) — システム設計のコンテキスト
- [コンポーネント](components.md) — モジュール詳細
- [APIリファレンス](../reference/api/) — 詳細なAPI
