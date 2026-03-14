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

/-- Fast UInt32 LEB128 encoder using native bitwise ops.
    Fully unrolled with value-range branching for optimal CPU pipelining.
    All comparisons are on the original value (no serial dependencies).
    Continuation bytes skip redundant AND-mask (decoder extracts bits anyway). -/
@[inline] private def encodeU32_go (n : _root_.UInt32) (acc : ByteArray) : ByteArray :=
  if n < 0x80 then
    acc.push n.toUInt8
  else if n < 0x4000 then
    (acc.push (n.toUInt8 ||| 0x80)).push (n >>> 7).toUInt8
  else if n < 0x200000 then
    ((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push (n >>> 14).toUInt8
  else if n < 0x10000000 then
    (((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push
     ((n >>> 14).toUInt8 ||| 0x80)).push (n >>> 21).toUInt8
  else
    ((((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push
     ((n >>> 14).toUInt8 ||| 0x80)).push
     ((n >>> 21).toUInt8 ||| 0x80)).push (n >>> 28).toUInt8

@[inline] private def encodeU32_fast (x : Radix.UInt32) : ByteArray :=
  encodeU32_go x.val (ByteArray.emptyWithCapacity 5)

/-- Encode a `UInt32` as unsigned LEB128. Result is 1-5 bytes. -/
@[implemented_by encodeU32_fast]
def encodeU32 (x : Radix.UInt32) : ByteArray :=
  encodeUnsigned x.toNat ByteArray.empty

@[inline] private def encodeU32Append_fast (x : Radix.UInt32) (buf : ByteArray) : ByteArray :=
  encodeU32_go x.val buf

/-- Encode a `UInt32` as unsigned LEB128, appending to an existing `ByteArray`.
    Use this instead of `encodeU32` when encoding multiple values
    into a single buffer (avoids per-call allocation). -/
@[implemented_by encodeU32Append_fast]
def encodeU32Append (x : Radix.UInt32) (buf : ByteArray) : ByteArray :=
  encodeUnsigned x.toNat buf

/-- Fast UInt64 LEB128 encoder using native bitwise ops.
    Fully unrolled with value-range branching for optimal CPU pipelining. -/
@[inline] private def encodeU64_go (n : _root_.UInt64) (acc : ByteArray) : ByteArray :=
  if n < 0x80 then
    acc.push n.toUInt8
  else if n < 0x4000 then
    (acc.push (n.toUInt8 ||| 0x80)).push (n >>> 7).toUInt8
  else if n < 0x200000 then
    ((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push (n >>> 14).toUInt8
  else if n < 0x10000000 then
    (((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push
     ((n >>> 14).toUInt8 ||| 0x80)).push (n >>> 21).toUInt8
  else if n < 0x800000000 then
    ((((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push
     ((n >>> 14).toUInt8 ||| 0x80)).push
     ((n >>> 21).toUInt8 ||| 0x80)).push (n >>> 28).toUInt8
  else if n < 0x40000000000 then
    (((((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push
     ((n >>> 14).toUInt8 ||| 0x80)).push
     ((n >>> 21).toUInt8 ||| 0x80)).push
     ((n >>> 28).toUInt8 ||| 0x80)).push (n >>> 35).toUInt8
  else if n < 0x2000000000000 then
    ((((((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push
     ((n >>> 14).toUInt8 ||| 0x80)).push
     ((n >>> 21).toUInt8 ||| 0x80)).push
     ((n >>> 28).toUInt8 ||| 0x80)).push
     ((n >>> 35).toUInt8 ||| 0x80)).push (n >>> 42).toUInt8
  else if n < 0x100000000000000 then
    (((((((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push
     ((n >>> 14).toUInt8 ||| 0x80)).push
     ((n >>> 21).toUInt8 ||| 0x80)).push
     ((n >>> 28).toUInt8 ||| 0x80)).push
     ((n >>> 35).toUInt8 ||| 0x80)).push
     ((n >>> 42).toUInt8 ||| 0x80)).push (n >>> 49).toUInt8
  else if n < 0x8000000000000000 then
    ((((((((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push
     ((n >>> 14).toUInt8 ||| 0x80)).push
     ((n >>> 21).toUInt8 ||| 0x80)).push
     ((n >>> 28).toUInt8 ||| 0x80)).push
     ((n >>> 35).toUInt8 ||| 0x80)).push
     ((n >>> 42).toUInt8 ||| 0x80)).push
     ((n >>> 49).toUInt8 ||| 0x80)).push (n >>> 56).toUInt8
  else
    (((((((((acc.push (n.toUInt8 ||| 0x80)).push
     ((n >>> 7).toUInt8 ||| 0x80)).push
     ((n >>> 14).toUInt8 ||| 0x80)).push
     ((n >>> 21).toUInt8 ||| 0x80)).push
     ((n >>> 28).toUInt8 ||| 0x80)).push
     ((n >>> 35).toUInt8 ||| 0x80)).push
     ((n >>> 42).toUInt8 ||| 0x80)).push
     ((n >>> 49).toUInt8 ||| 0x80)).push
     ((n >>> 56).toUInt8 ||| 0x80)).push (n >>> 63).toUInt8

@[inline] private def encodeU64_fast (x : Radix.UInt64) : ByteArray :=
  encodeU64_go x.val (ByteArray.emptyWithCapacity 10)

/-- Encode a `UInt64` as unsigned LEB128. Result is 1-10 bytes. -/
@[implemented_by encodeU64_fast]
def encodeU64 (x : Radix.UInt64) : ByteArray :=
  encodeUnsigned x.toNat ByteArray.empty

@[inline] private def encodeU64Append_fast (x : Radix.UInt64) (buf : ByteArray) : ByteArray :=
  encodeU64_go x.val buf

/-- Encode a `UInt64` as unsigned LEB128, appending to an existing `ByteArray`. -/
@[implemented_by encodeU64Append_fast]
def encodeU64Append (x : Radix.UInt64) (buf : ByteArray) : ByteArray :=
  encodeUnsigned x.toNat buf

/-! ================================================================ -/
/-! ## Unsigned LEB128 Decoding                                       -/
/-! ================================================================ -/

/-- Decode an unsigned LEB128-encoded `UInt32` from `data` at `offset`.
    Returns `(value, bytesConsumed)` or `none` on error.
    Maximum 5 bytes (Wasm constraint).

    Fully unrolled: eliminates recursion and per-byte function call overhead.
    Each byte path is straight-line code with constant shift amounts. -/
@[inline] private def decodeU32_fast (data : ByteArray) (offset : Nat) : Option (Radix.UInt32 × Nat) :=
  let sz := data.size
  let p0 := offset
  if h0 : p0 < sz then
    let b0 := data[p0]
    let r0 : _root_.UInt32 := b0.toUInt32 &&& 0x7F
    if b0 &&& 0x80 == 0 then some (⟨r0⟩, 1)
    else
    let p1 := p0 + 1
    if h1 : p1 < sz then
      let b1 := data[p1]
      let r1 := r0 ||| ((b1.toUInt32 &&& 0x7F) <<< 7)
      if b1 &&& 0x80 == 0 then some (⟨r1⟩, 2)
      else
      let p2 := p1 + 1
      if h2 : p2 < sz then
        let b2 := data[p2]
        let r2 := r1 ||| ((b2.toUInt32 &&& 0x7F) <<< 14)
        if b2 &&& 0x80 == 0 then some (⟨r2⟩, 3)
        else
        let p3 := p2 + 1
        if h3 : p3 < sz then
          let b3 := data[p3]
          let r3 := r2 ||| ((b3.toUInt32 &&& 0x7F) <<< 21)
          if b3 &&& 0x80 == 0 then some (⟨r3⟩, 4)
          else
          let p4 := p3 + 1
          if h4 : p4 < sz then
            let b4 := data[p4]
            -- Byte 4: only low 4 bits valid, no continuation allowed
            if b4 > 0x0F then none
            else some (⟨r3 ||| (b4.toUInt32 <<< 28)⟩, 5)
          else none
        else none
      else none
    else none
  else none

@[implemented_by decodeU32_fast]
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
    Maximum 10 bytes (Wasm constraint).

    Fully unrolled: each byte is straight-line code with constant shifts. -/
@[inline] private def decodeU64_fast (data : ByteArray) (offset : Nat) : Option (Radix.UInt64 × Nat) :=
  let sz := data.size
  let p0 := offset
  if h0 : p0 < sz then
    let b0 := data[p0]
    let r0 : _root_.UInt64 := b0.toUInt64 &&& 0x7F
    if b0 &&& 0x80 == 0 then some (⟨r0⟩, 1)
    else
    let p1 := p0 + 1
    if h1 : p1 < sz then
      let b1 := data[p1]
      let r1 := r0 ||| ((b1.toUInt64 &&& 0x7F) <<< 7)
      if b1 &&& 0x80 == 0 then some (⟨r1⟩, 2)
      else
      let p2 := p1 + 1
      if h2 : p2 < sz then
        let b2 := data[p2]
        let r2 := r1 ||| ((b2.toUInt64 &&& 0x7F) <<< 14)
        if b2 &&& 0x80 == 0 then some (⟨r2⟩, 3)
        else
        let p3 := p2 + 1
        if h3 : p3 < sz then
          let b3 := data[p3]
          let r3 := r2 ||| ((b3.toUInt64 &&& 0x7F) <<< 21)
          if b3 &&& 0x80 == 0 then some (⟨r3⟩, 4)
          else
          let p4 := p3 + 1
          if h4 : p4 < sz then
            let b4 := data[p4]
            let r4 := r3 ||| ((b4.toUInt64 &&& 0x7F) <<< 28)
            if b4 &&& 0x80 == 0 then some (⟨r4⟩, 5)
            else
            let p5 := p4 + 1
            if h5 : p5 < sz then
              let b5 := data[p5]
              let r5 := r4 ||| ((b5.toUInt64 &&& 0x7F) <<< 35)
              if b5 &&& 0x80 == 0 then some (⟨r5⟩, 6)
              else
              let p6 := p5 + 1
              if h6 : p6 < sz then
                let b6 := data[p6]
                let r6 := r5 ||| ((b6.toUInt64 &&& 0x7F) <<< 42)
                if b6 &&& 0x80 == 0 then some (⟨r6⟩, 7)
                else
                let p7 := p6 + 1
                if h7 : p7 < sz then
                  let b7 := data[p7]
                  let r7 := r6 ||| ((b7.toUInt64 &&& 0x7F) <<< 49)
                  if b7 &&& 0x80 == 0 then some (⟨r7⟩, 8)
                  else
                  let p8 := p7 + 1
                  if h8 : p8 < sz then
                    let b8 := data[p8]
                    let r8 := r7 ||| ((b8.toUInt64 &&& 0x7F) <<< 56)
                    if b8 &&& 0x80 == 0 then some (⟨r8⟩, 9)
                    else
                    let p9 := p8 + 1
                    if h9 : p9 < sz then
                      let b9 := data[p9]
                      -- Byte 9: only lowest bit valid, no continuation
                      if b9 > 0x01 then none
                      else some (⟨r8 ||| (b9.toUInt64 <<< 63)⟩, 10)
                    else none
                  else none
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

@[implemented_by decodeU64_fast]
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

/-- Fast Int32 signed LEB128 encoder using native bitwise ops on underlying UInt32.
    Fully unrolled: no recursion, no fuel parameter. -/
@[inline] private def encodeS32_fast (x : Radix.Int32) : ByteArray :=
  let n := x.val
  let acc : ByteArray := ⟨Array.mkEmpty 5⟩
  -- Inline helper: arithmetic right shift by 7 for UInt32 (sign-extend from bit 31)
  let arsh7 (v : _root_.UInt32) : _root_.UInt32 :=
    (v >>> 7) ||| (if v &&& 0x80000000 != 0 then 0xFE000000 else 0)
  let isDone (rest : _root_.UInt32) (byte : _root_.UInt8) : Bool :=
    let signBitSet := byte &&& 0x40 != 0
    (rest == 0 && !signBitSet) || (rest == 0xFFFFFFFF && signBitSet)
  -- Byte 0
  let b0 := (n &&& 0x7F).toUInt8
  let r0 := arsh7 n
  if isDone r0 b0 then acc.push b0
  else
  let acc := acc.push (b0 ||| 0x80)
  -- Byte 1
  let b1 := (r0 &&& 0x7F).toUInt8
  let r1 := arsh7 r0
  if isDone r1 b1 then acc.push b1
  else
  let acc := acc.push (b1 ||| 0x80)
  -- Byte 2
  let b2 := (r1 &&& 0x7F).toUInt8
  let r2 := arsh7 r1
  if isDone r2 b2 then acc.push b2
  else
  let acc := acc.push (b2 ||| 0x80)
  -- Byte 3
  let b3 := (r2 &&& 0x7F).toUInt8
  let r3 := arsh7 r2
  if isDone r3 b3 then acc.push b3
  else
  let acc := acc.push (b3 ||| 0x80)
  -- Byte 4 (always terminal)
  acc.push (r3 &&& 0x7F).toUInt8

/-- Encode an `Int32` as signed LEB128. Result is 1-5 bytes. -/
@[implemented_by encodeS32_fast]
def encodeS32 (x : Radix.Int32) : ByteArray :=
  encodeSigned x.toInt ByteArray.empty 5

/-- Fast Int64 signed LEB128 encoder using native bitwise ops on underlying UInt64.
    Fully unrolled: no recursion, no fuel parameter. -/
@[inline] private def encodeS64_fast (x : Radix.Int64) : ByteArray :=
  let n := x.val
  let acc : ByteArray := ⟨Array.mkEmpty 10⟩
  -- Inline helper: arithmetic right shift by 7 for UInt64 (sign-extend from bit 63)
  let arsh7 (v : _root_.UInt64) : _root_.UInt64 :=
    (v >>> 7) ||| (if v &&& 0x8000000000000000 != 0 then 0xFE00000000000000 else 0)
  let isDone (rest : _root_.UInt64) (byte : _root_.UInt8) : Bool :=
    let signBitSet := byte &&& 0x40 != 0
    (rest == 0 && !signBitSet) || (rest == 0xFFFFFFFFFFFFFFFF && signBitSet)
  -- Byte 0
  let b0 := (n &&& 0x7F).toUInt8
  let r0 := arsh7 n
  if isDone r0 b0 then acc.push b0
  else
  let acc := acc.push (b0 ||| 0x80)
  -- Byte 1
  let b1 := (r0 &&& 0x7F).toUInt8
  let r1 := arsh7 r0
  if isDone r1 b1 then acc.push b1
  else
  let acc := acc.push (b1 ||| 0x80)
  -- Byte 2
  let b2 := (r1 &&& 0x7F).toUInt8
  let r2 := arsh7 r1
  if isDone r2 b2 then acc.push b2
  else
  let acc := acc.push (b2 ||| 0x80)
  -- Byte 3
  let b3 := (r2 &&& 0x7F).toUInt8
  let r3 := arsh7 r2
  if isDone r3 b3 then acc.push b3
  else
  let acc := acc.push (b3 ||| 0x80)
  -- Byte 4
  let b4 := (r3 &&& 0x7F).toUInt8
  let r4 := arsh7 r3
  if isDone r4 b4 then acc.push b4
  else
  let acc := acc.push (b4 ||| 0x80)
  -- Byte 5
  let b5 := (r4 &&& 0x7F).toUInt8
  let r5 := arsh7 r4
  if isDone r5 b5 then acc.push b5
  else
  let acc := acc.push (b5 ||| 0x80)
  -- Byte 6
  let b6 := (r5 &&& 0x7F).toUInt8
  let r6 := arsh7 r5
  if isDone r6 b6 then acc.push b6
  else
  let acc := acc.push (b6 ||| 0x80)
  -- Byte 7
  let b7 := (r6 &&& 0x7F).toUInt8
  let r7 := arsh7 r6
  if isDone r7 b7 then acc.push b7
  else
  let acc := acc.push (b7 ||| 0x80)
  -- Byte 8
  let b8 := (r7 &&& 0x7F).toUInt8
  let r8 := arsh7 r7
  if isDone r8 b8 then acc.push b8
  else
  let acc := acc.push (b8 ||| 0x80)
  -- Byte 9 (always terminal)
  acc.push (r8 &&& 0x7F).toUInt8

/-- Encode an `Int64` as signed LEB128. Result is 1-10 bytes. -/
@[implemented_by encodeS64_fast]
def encodeS64 (x : Radix.Int64) : ByteArray :=
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
