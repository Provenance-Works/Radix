/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# LEB128 Specification (Layer 3)

Mathematical specification of LEB128 (Little Endian Base 128) variable-length
integer encoding. Used in Wasm binary format, DWARF, Protocol Buffers (varint),
Android DEX, and other binary formats.

## Encoding Rules

- Each byte contributes 7 data bits (bits [6:0])
- Bit 7 is a continuation flag: 1 = more bytes follow, 0 = final byte
- Unsigned: value = sum of (byte[i] & 0x7F) << (7*i)
- Signed: final byte's bit 6 is the sign bit; sign-extend to target width
- Wasm constraints: unsigned 32-bit max 5 bytes, 64-bit max 10 bytes

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- WebAssembly spec, Section 5.2.2 (Integers)
- DWARF v5, Section 7.6
-/

namespace Radix.Binary.Leb128

/-! ================================================================ -/
/-! ## Unsigned LEB128 Specification                                  -/
/-! ================================================================ -/

/-- Abstract specification of unsigned LEB128 decoding from a byte sequence.
    Given bytes `[b0, b1, ..., bn]` where bn has bit 7 clear,
    the decoded value is `sum_{i=0}^{n} (b_i & 0x7F) << (7*i)`. -/
def unsignedDecodeValue (bytes : List UInt8) : Nat :=
  let rec go (bs : List UInt8) (i : Nat) (acc : Nat) : Nat :=
    match bs with
    | [] => acc
    | b :: rest => go rest (i + 1) (acc + ((b.toNat &&& 0x7F) <<< (7 * i)))
  go bytes 0 0

/-- A valid unsigned LEB128 encoding has the continuation bit set on all
    bytes except the last. -/
def isValidUnsignedEncoding (bytes : List UInt8) : Prop :=
  bytes.length > 0 ∧
  (∀ i, i < bytes.length - 1 → (bytes[i]!.toNat &&& 0x80) = 0x80) ∧
  ((bytes[bytes.length - 1]!.toNat &&& 0x80) = 0)

/-- Unsigned LEB128 encoding for 32-bit values MUST NOT exceed 5 bytes. -/
def isValidU32Encoding (bytes : List UInt8) : Prop :=
  isValidUnsignedEncoding bytes ∧ bytes.length ≤ 5

/-- Unsigned LEB128 encoding for 64-bit values MUST NOT exceed 10 bytes. -/
def isValidU64Encoding (bytes : List UInt8) : Prop :=
  isValidUnsignedEncoding bytes ∧ bytes.length ≤ 10

/-! ================================================================ -/
/-! ## Signed LEB128 Specification                                    -/
/-! ================================================================ -/

/-- Abstract specification of signed LEB128 decoding.
    Same as unsigned, but the final byte's bit 6 determines sign extension. -/
def signedDecodeValue (bytes : List UInt8) (targetBits : Nat) : Int :=
  let raw := unsignedDecodeValue bytes
  let shift := 7 * bytes.length
  if shift < targetBits && (bytes[bytes.length - 1]!.toNat &&& 0x40) != 0 then
    Int.ofNat raw - Int.ofNat (1 <<< shift)
  else
    Int.ofNat raw

/-- Signed LEB128 encoding for 32-bit values MUST NOT exceed 5 bytes. -/
def isValidS32Encoding (bytes : List UInt8) : Prop :=
  isValidUnsignedEncoding bytes ∧ bytes.length ≤ 5

/-- Signed LEB128 encoding for 64-bit values MUST NOT exceed 10 bytes. -/
def isValidS64Encoding (bytes : List UInt8) : Prop :=
  isValidUnsignedEncoding bytes ∧ bytes.length ≤ 10

end Radix.Binary.Leb128
