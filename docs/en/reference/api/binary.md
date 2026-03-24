# Binary Module API Reference

> **Module**: `Radix.Binary`
> **Source**: `Radix/Binary/`

## Overview

Provides a declarative DSL for specifying binary wire formats, with format-driven parser and serializer generation. Also includes LEB128 variable-length integer encoding. All round-trip properties are formally proven.

## Format DSL (`Binary.Format`)

```lean
inductive Format where
  | byte (name : String)                          -- 1 byte
  | uint16 (name : String) (endian : Endian)     -- 2 bytes with endianness
  | uint32 (name : String) (endian : Endian)     -- 4 bytes with endianness
  | uint64 (name : String) (endian : Endian)     -- 8 bytes with endianness
  | bytes (name : String) (count : Nat)          -- fixed-size raw byte blob
  | lengthPrefixedBytes (name : String) (prefixBytes : Nat) (endian : Endian)
                                                 -- raw byte blob with computed length prefix
  | countPrefixedArray (name : String) (prefixBytes : Nat) (endian : Endian) (elem : Format)
                                                 -- array whose element count is stored in a prefix
  | constBytes (value : ByteArray)               -- fixed bytes that must match exactly
  | padding (n : Nat)                             -- n zero bytes
  | align (n : Nat)                               -- zero bytes up to the next n-byte boundary
  | array (name : String) (len : Nat) (elem : Format)  -- repeated element
  | seq (a b : Format)                            -- sequential composition
```

### DSL Helpers

```lean
def u16be : Format := .uint16 .big
def u16le : Format := .uint16 .little
def u32be : Format := .uint32 .big
def u32le : Format := .uint32 .little
def u64be : Format := .uint64 .big
def u64le : Format := .uint64 .little
def pad (n : Nat) : Format := .padding n
```

`align n` inserts the minimum zero-filled gap needed to align the next field to
an `n`-byte boundary relative to the current offset.

`lengthPrefixedBytes name prefixBytes endian` stores a raw byte blob together
with a computed length prefix of width 1, 2, 4, or 8 bytes. Parsing decodes the
prefix and reads exactly that many payload bytes. Serialization computes the
prefix from the payload length.

`countPrefixedArray name prefixBytes endian elem` stores an array whose element
count is encoded in a 1, 2, 4, or 8 byte prefix. Parsing decodes the count and
parses that many `elem` values. Serialization computes the count from the
provided `FieldValue.array` length.

`constBytes value` encodes fixed header bytes directly in the format. Parsing
requires the input bytes to match `value`, and serialization emits `value`
without consuming any named field.

### Format Properties

```lean
def Format.fixedSize : Format → Option Nat  -- Total byte size (none if variable)
def Format.fieldNames : Format → List String
def Format.fieldCount : Format → Nat
def Format.toFormatSpec : Format → FormatSpec
```

For variable-length formats, `Format.toFormatSpec` records minimum layout
metadata. `totalSize` is the minimum required prefix size, and field offsets
after variable fields should be treated as lower bounds rather than exact
positions.

## Parser (`Binary.Parser`)

```lean
inductive ParseError where
  | outOfBounds
  | unsupportedLengthPrefix
  | constantMismatch
  | trailingBytes
  | internal

inductive FieldValue where
  | byte (v : UInt8)
  | uint16 (v : UInt16)
  | uint32 (v : UInt32)
  | uint64 (v : UInt64)
  | bytes (v : ByteArray)
  | array (vs : List FieldValue)

def parsePrefix (data : ByteArray) (fmt : Format) : Except ParseError (List FieldValue × Nat)
def parseSplit (data : ByteArray) (fmt : Format) : Except ParseError (List FieldValue × ByteArray)
def parseFormat (data : ByteArray) (fmt : Format) : Except ParseError (List FieldValue)
def parseFormatExact (data : ByteArray) (fmt : Format) : Except ParseError (List FieldValue)
```

`parseFormat` performs prefix parsing and ignores trailing bytes.
`parseSplit` performs prefix parsing and returns the unconsumed suffix.
`parseFormatExact` rejects trailing input with `trailingBytes`.

`bytes name count` models a fixed-size raw blob without forcing callers to wrap
it as an array of single-byte fields.

`lengthPrefixedBytes` models a dynamic blob while keeping the decoded value in a
plain `FieldValue.bytes` entry.

`countPrefixedArray` models dynamic repeated structure while keeping the decoded
value in the existing `FieldValue.array` shape.

`constBytes` is useful for magic values, signatures, and fixed protocol tags.
It validates the prefix declaratively instead of requiring a manual post-parse
check.

## Serializer (`Binary.Serial`)

```lean
inductive SerialError where
  | missingField
  | typeMismatch
  | unsupportedLengthPrefix
  | lengthOverflow
  | unexpectedField

def serializeFormat (fmt : Format) (values : List FieldValue) : Except SerialError ByteArray
def writePadding (n : Nat) (arr : ByteArray) : ByteArray
```

Serialization consumes exactly one matching field for each format node. If the
input contains values that are never consumed, `serializeFormat` returns
`unexpectedField`.

When a `lengthPrefixedBytes` payload does not fit into its configured prefix
width, serialization returns `lengthOverflow`.

## LEB128 (`Binary.Leb128`)

### Encoding

```lean
@[inline] def encodeU32 (x : UInt32) : ByteArray   -- 1-5 bytes
@[inline] def encodeU64 (x : UInt64) : ByteArray   -- 1-10 bytes
@[inline] def encodeS32 (x : Int32) : ByteArray    -- 1-5 bytes
@[inline] def encodeS64 (x : Int64) : ByteArray    -- 1-10 bytes
```

### Decoding

```lean
def decodeU32 (data : ByteArray) (offset : Nat) : Option (UInt32 × Nat)
def decodeU64 (data : ByteArray) (offset : Nat) : Option (UInt64 × Nat)
def decodeS32 (data : ByteArray) (offset : Nat) : Option (Int32 × Nat)
def decodeS64 (data : ByteArray) (offset : Nat) : Option (Int64 × Nat)
```

Returns `(value, bytesConsumed)` or `none` on malformed input.

### LEB128 Specification (`Binary.Leb128.Spec`)

```lean
def unsignedDecodeValue : List UInt8 → Nat    -- Mathematical definition
def signedDecodeValue : List UInt8 → Int      -- Mathematical definition
def isValidUnsignedEncoding : List UInt8 → Prop
def isValidU32Encoding : List UInt8 → Prop
```

## Proofs

### Format Proofs (`Binary.Lemmas`)
- `PrimType.byteSize_pos`
- `Format.fixedSize` correctness per constructor
- `FormatSpec.empty_isValid`
- `Serial.writePadding_size`
- `Parser.parse_padding_ok`

### LEB128 Proofs (`Binary.Leb128.Lemmas`)
- **Round-trip**: `decodeU32 (encodeU32 x) 0 = some (x, (encodeU32 x).size)`
- **Round-trip**: `decodeU64 (encodeU64 x) 0 = some (x, (encodeU64 x).size)`
- **Round-trip**: `decodeS32 (encodeS32 x) 0 = some (x, (encodeS32 x).size)`
- **Round-trip**: `decodeS64 (encodeS64 x) 0 = some (x, (encodeS64 x).size)`
- **Size bounds**: `(encodeU32 x).size ≤ 5`, `(encodeU64 x).size ≤ 10`
- **Non-empty**: `(encodeU32 x).size > 0`

## Related Documents

- [Memory](memory.md) — Buffer used for binary data
- [Bytes](bytes.md) — Endianness primitives
