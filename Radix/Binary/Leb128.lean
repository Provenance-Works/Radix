/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Int

/-!
# LEB128 Implementation (Layer 2)

Verified implementation of LEB128 (Little Endian Base 128) variable-length
integer encoding and decoding.

All decode functions return `Option` on malformed input (overlong encoding,
overflow, or truncated input). All encode functions are total.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- WebAssembly spec, Section 5.2.2
- docs/design/wasm-support-plan.md, Section 3.3
-/

namespace Radix.Binary.Leb128

/-! ================================================================ -/
/-! ## Unsigned LEB128 Encoding                                       -/
/-! ================================================================ -/

/-- Core unsigned LEB128 encoder. Each call appends one byte;
    recurses until the remaining value fits in 7 bits. -/
def encodeUnsigned (n : Nat) (acc : ByteArray) : ByteArray :=
  if h : n < 128 then
    acc.push n.toUInt8
  else
    have : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
    encodeUnsigned (n / 128) (acc.push (n % 128 ||| 0x80).toUInt8)
termination_by n

/-- Encode a `UInt32` as unsigned LEB128. Result is 1-5 bytes. -/
@[inline] def encodeU32 (x : Radix.UInt32) : ByteArray :=
  encodeUnsigned x.toNat ByteArray.empty

/-- Encode a `UInt64` as unsigned LEB128. Result is 1-10 bytes. -/
@[inline] def encodeU64 (x : Radix.UInt64) : ByteArray :=
  encodeUnsigned x.toNat ByteArray.empty

/-! ================================================================ -/
/-! ## Unsigned LEB128 Decoding                                       -/
/-! ================================================================ -/

/-- Decode an unsigned LEB128-encoded `UInt32` from `data` at `offset`.
    Returns `(value, bytesConsumed)` or `none` on error.
    Maximum 5 bytes (Wasm constraint). -/
def decodeU32 (data : ByteArray) (offset : Nat) : Option (Radix.UInt32 × Nat) :=
  go 0 0 0
where
  go (result : Nat) (shift : Nat) (i : Nat) : Option (Radix.UInt32 × Nat) :=
    if i >= 5 then none
    else
      let pos := offset + i
      if h : pos < data.size then
        let byte := data[pos].toNat
        let value := byte &&& 0x7F
        -- On 5th byte (i=4), only lower 4 bits are valid for u32
        if i == 4 && value > 0x0F then none
        else
          let result' := result ||| (value <<< shift)
          if byte &&& 0x80 == 0 then
            some (Radix.UInt32.fromBitVec (BitVec.ofNat 32 result'), i + 1)
          else
            go result' (shift + 7) (i + 1)
      else none
  termination_by 5 - i

/-- Decode an unsigned LEB128-encoded `UInt64` from `data` at `offset`.
    Returns `(value, bytesConsumed)` or `none` on error.
    Maximum 10 bytes (Wasm constraint). -/
def decodeU64 (data : ByteArray) (offset : Nat) : Option (Radix.UInt64 × Nat) :=
  go 0 0 0
where
  go (result : Nat) (shift : Nat) (i : Nat) : Option (Radix.UInt64 × Nat) :=
    if i >= 10 then none
    else
      let pos := offset + i
      if h : pos < data.size then
        let byte := data[pos].toNat
        let value := byte &&& 0x7F
        -- On 10th byte (i=9), only lowest bit valid for u64
        if i == 9 && value > 0x01 then none
        else
          let result' := result ||| (value <<< shift)
          if byte &&& 0x80 == 0 then
            some (Radix.UInt64.fromBitVec (BitVec.ofNat 64 result'), i + 1)
          else
            go result' (shift + 7) (i + 1)
      else none
  termination_by 10 - i

/-! ================================================================ -/
/-! ## Signed LEB128 Encoding                                         -/
/-! ================================================================ -/

/-- Core signed LEB128 encoder. Uses fuel for termination.
    Uses `%` (Euclidean mod) and `Int.shiftRight` (arithmetic shift)
    to avoid bitwise ops which lack `AndOp Int` in Lean 4 core. -/
def encodeSigned (n : Int) (acc : ByteArray) (fuel : Nat) : ByteArray :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    let byte := (n % 128).toNat      -- low 7 bits as Nat [0,128)
    let rest := n.shiftRight 7        -- arithmetic shift right
    let signBit := byte / 64          -- bit 6: 0 or 1
    if (rest == 0 && signBit == 0) || (rest == -1 && signBit != 0) then
      acc.push byte.toUInt8
    else
      encodeSigned rest (acc.push (byte ||| 0x80).toUInt8) fuel'

/-- Encode an `Int32` as signed LEB128. Result is 1-5 bytes. -/
@[inline] def encodeS32 (x : Radix.Int32) : ByteArray :=
  encodeSigned x.toInt ByteArray.empty 5

/-- Encode an `Int64` as signed LEB128. Result is 1-10 bytes. -/
@[inline] def encodeS64 (x : Radix.Int64) : ByteArray :=
  encodeSigned x.toInt ByteArray.empty 10

/-! ================================================================ -/
/-! ## Signed LEB128 Decoding                                         -/
/-! ================================================================ -/

/-- Decode a signed LEB128-encoded `Int32` from `data` at `offset`.
    Returns `(value, bytesConsumed)` or `none` on error.
    Maximum 5 bytes (Wasm constraint). -/
def decodeS32 (data : ByteArray) (offset : Nat) : Option (Radix.Int32 × Nat) :=
  go 0 0 0
where
  go (result : Nat) (shift : Nat) (i : Nat) : Option (Radix.Int32 × Nat) :=
    if i >= 5 then none
    else
      let pos := offset + i
      if h : pos < data.size then
        let byte := data[pos].toNat
        let value := byte &&& 0x7F
        -- On 5th byte (i=4): bits 4-6 must be sign extension of bit 3
        -- Valid values: 0x00-0x07 (positive) or 0x78-0x7F (negative)
        if i == 4 && value > 0x07 && value < 0x78 then none
        else
          let result' := result ||| (value <<< shift)
          if byte &&& 0x80 == 0 then
            let shift' := shift + 7
            -- Sign-extend if bit 6 of final byte is set
            let final :=
              if shift' < 32 && (byte &&& 0x40) != 0 then
                result' ||| (0xFFFFFFFF - ((1 <<< shift') - 1))
              else
                result'
            some (Radix.Int32.fromBitVec (BitVec.ofNat 32 final), i + 1)
          else
            go result' (shift + 7) (i + 1)
      else none
  termination_by 5 - i

/-- Decode a signed LEB128-encoded `Int64` from `data` at `offset`.
    Returns `(value, bytesConsumed)` or `none` on error.
    Maximum 10 bytes (Wasm constraint). -/
def decodeS64 (data : ByteArray) (offset : Nat) : Option (Radix.Int64 × Nat) :=
  go 0 0 0
where
  go (result : Nat) (shift : Nat) (i : Nat) : Option (Radix.Int64 × Nat) :=
    if i >= 10 then none
    else
      let pos := offset + i
      if h : pos < data.size then
        let byte := data[pos].toNat
        let value := byte &&& 0x7F
        -- On 10th byte (i=9): all 7 bits must be same (sign extension)
        -- Valid values: 0x00 (positive) or 0x7F (negative)
        if i == 9 && value != 0x00 && value != 0x7F then none
        else
          let result' := result ||| (value <<< shift)
          if byte &&& 0x80 == 0 then
            let shift' := shift + 7
            let final :=
              if shift' < 64 && (byte &&& 0x40) != 0 then
                result' ||| (0xFFFFFFFFFFFFFFFF - ((1 <<< shift') - 1))
              else
                result'
            some (Radix.Int64.fromBitVec (BitVec.ofNat 64 final), i + 1)
          else
            go result' (shift + 7) (i + 1)
      else none
  termination_by 10 - i

end Radix.Binary.Leb128
