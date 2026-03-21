/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Bytes.Order
import Radix.Memory.Spec

/-!
# Memory Buffer Model (Layer 2)

This module implements the concrete memory buffer abstraction built on
Lean 4's native `ByteArray`. All access is bounds-checked at the type
level (Tier 1) or via `Option` (Tier 2).

## Architecture

This is a **Layer 2 (Verified Implementation)** module.
- Imports Layer 3 (`Memory.Spec`) for specification reference.
- All memory lifetime is managed by Lean's GC (ADR C-001).

## References

- FR-004: Memory Safety
- Memory Interface design doc
-/

namespace Radix.Memory

/-! ## Buffer Structure -/

/-- A bounds-safe memory buffer backed by `ByteArray`.
    All access methods require proof of in-bounds access (Tier 1)
    or return `Option` (Tier 2). -/
structure Buffer where
  bytes : ByteArray

namespace Buffer

/-! ## Construction -/

/-- Create a buffer of `n` zero-initialized bytes. -/
@[inline] def zeros (n : Nat) : Buffer :=
  ⟨⟨.replicate n 0⟩⟩

/-- Create a buffer from an existing `ByteArray`. -/
@[inline] def ofByteArray (arr : ByteArray) : Buffer := ⟨arr⟩

/-- Create an empty buffer. -/
@[inline] def empty : Buffer := ⟨ByteArray.empty⟩

/-- The number of bytes in the buffer. -/
@[inline] def size (buf : Buffer) : Nat := buf.bytes.size

/-! ## Internal helpers -/

theorem set_size_eq (a : ByteArray) (i : Nat) (v : _root_.UInt8)
    (h : i < a.size) : (a.set i v h).size = a.size := by
  unfold ByteArray.set ByteArray.size; simp

/-! ## Tier 1: Proof-bounded access -/

/-- Read a single byte at `offset` with a proof of bounds. -/
@[inline] def readU8 (buf : Buffer) (offset : Nat)
    (h : offset < buf.bytes.size) : Radix.UInt8 :=
  ⟨buf.bytes.get offset h⟩

/-- Write a single byte at `offset` with a proof of bounds. -/
@[inline] def writeU8 (buf : Buffer) (offset : Nat) (val : Radix.UInt8)
    (h : offset < buf.bytes.size) : Buffer :=
  ⟨buf.bytes.set offset val.val h⟩

/-- Read a UInt16 (big-endian) at `offset` with bounds proof. -/
@[inline] def readU16BE (buf : Buffer) (offset : Nat)
    (h : offset + 2 ≤ buf.bytes.size) : Radix.UInt16 :=
  let b0 := buf.bytes.get offset (by omega)
  let b1 := buf.bytes.get (offset + 1) (by omega)
  ⟨(b0.toUInt16 <<< 8) ||| b1.toUInt16⟩

/-- Read a UInt16 (little-endian) at `offset` with bounds proof. -/
@[inline] def readU16LE (buf : Buffer) (offset : Nat)
    (h : offset + 2 ≤ buf.bytes.size) : Radix.UInt16 :=
  let b0 := buf.bytes.get offset (by omega)
  let b1 := buf.bytes.get (offset + 1) (by omega)
  ⟨b0.toUInt16 ||| (b1.toUInt16 <<< 8)⟩

/-- Read a UInt32 (big-endian) at `offset` with bounds proof. -/
@[inline] def readU32BE (buf : Buffer) (offset : Nat)
    (h : offset + 4 ≤ buf.bytes.size) : Radix.UInt32 :=
  let b0 := buf.bytes.get offset (by omega)
  let b1 := buf.bytes.get (offset + 1) (by omega)
  let b2 := buf.bytes.get (offset + 2) (by omega)
  let b3 := buf.bytes.get (offset + 3) (by omega)
  ⟨(b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) |||
   (b2.toUInt32 <<< 8)  ||| b3.toUInt32⟩

/-- Read a UInt32 (little-endian) at `offset` with bounds proof. -/
@[inline] def readU32LE (buf : Buffer) (offset : Nat)
    (h : offset + 4 ≤ buf.bytes.size) : Radix.UInt32 :=
  let b0 := buf.bytes.get offset (by omega)
  let b1 := buf.bytes.get (offset + 1) (by omega)
  let b2 := buf.bytes.get (offset + 2) (by omega)
  let b3 := buf.bytes.get (offset + 3) (by omega)
  ⟨b0.toUInt32 ||| (b1.toUInt32 <<< 8) |||
   (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)⟩

/-- Read a UInt64 (big-endian) at `offset` with bounds proof. -/
@[inline] def readU64BE (buf : Buffer) (offset : Nat)
    (h : offset + 8 ≤ buf.bytes.size) : Radix.UInt64 :=
  let b0 := buf.bytes.get offset (by omega)
  let b1 := buf.bytes.get (offset + 1) (by omega)
  let b2 := buf.bytes.get (offset + 2) (by omega)
  let b3 := buf.bytes.get (offset + 3) (by omega)
  let b4 := buf.bytes.get (offset + 4) (by omega)
  let b5 := buf.bytes.get (offset + 5) (by omega)
  let b6 := buf.bytes.get (offset + 6) (by omega)
  let b7 := buf.bytes.get (offset + 7) (by omega)
  ⟨(b0.toUInt64 <<< 56) ||| (b1.toUInt64 <<< 48) |||
   (b2.toUInt64 <<< 40) ||| (b3.toUInt64 <<< 32) |||
   (b4.toUInt64 <<< 24) ||| (b5.toUInt64 <<< 16) |||
   (b6.toUInt64 <<< 8)  ||| b7.toUInt64⟩

/-- Read a UInt64 (little-endian) at `offset` with bounds proof. -/
@[inline] def readU64LE (buf : Buffer) (offset : Nat)
    (h : offset + 8 ≤ buf.bytes.size) : Radix.UInt64 :=
  let b0 := buf.bytes.get offset (by omega)
  let b1 := buf.bytes.get (offset + 1) (by omega)
  let b2 := buf.bytes.get (offset + 2) (by omega)
  let b3 := buf.bytes.get (offset + 3) (by omega)
  let b4 := buf.bytes.get (offset + 4) (by omega)
  let b5 := buf.bytes.get (offset + 5) (by omega)
  let b6 := buf.bytes.get (offset + 6) (by omega)
  let b7 := buf.bytes.get (offset + 7) (by omega)
  ⟨b0.toUInt64 ||| (b1.toUInt64 <<< 8)  |||
   (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
   (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) |||
   (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)⟩

/-- Write a UInt16 (big-endian) at `offset` with bounds proof. -/
@[inline] def writeU16BE (buf : Buffer) (offset : Nat) (val : Radix.UInt16)
    (h : offset + 2 ≤ buf.bytes.size) : Buffer :=
  let v := val.val
  let a1 := buf.bytes.set offset (v >>> 8).toUInt8 (by omega)
  let a2 := a1.set (offset + 1) v.toUInt8 (by rw [set_size_eq]; omega)
  ⟨a2⟩

/-- Write a UInt16 (little-endian) at `offset` with bounds proof. -/
@[inline] def writeU16LE (buf : Buffer) (offset : Nat) (val : Radix.UInt16)
    (h : offset + 2 ≤ buf.bytes.size) : Buffer :=
  let v := val.val
  let a1 := buf.bytes.set offset v.toUInt8 (by omega)
  let a2 := a1.set (offset + 1) (v >>> 8).toUInt8 (by rw [set_size_eq]; omega)
  ⟨a2⟩

/-- Write a UInt32 (big-endian) at `offset` with bounds proof. -/
@[inline] def writeU32BE (buf : Buffer) (offset : Nat) (val : Radix.UInt32)
    (h : offset + 4 ≤ buf.bytes.size) : Buffer :=
  let v := val.val
  let a1 := buf.bytes.set offset (v >>> 24).toUInt8 (by omega)
  let a2 := a1.set (offset + 1) (v >>> 16).toUInt8 (by rw [set_size_eq]; omega)
  let a3 := a2.set (offset + 2) (v >>> 8).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; omega)
  let a4 := a3.set (offset + 3) v.toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  ⟨a4⟩

/-- Write a UInt32 (little-endian) at `offset` with bounds proof. -/
@[inline] def writeU32LE (buf : Buffer) (offset : Nat) (val : Radix.UInt32)
    (h : offset + 4 ≤ buf.bytes.size) : Buffer :=
  let v := val.val
  let a1 := buf.bytes.set offset v.toUInt8 (by omega)
  let a2 := a1.set (offset + 1) (v >>> 8).toUInt8 (by rw [set_size_eq]; omega)
  let a3 := a2.set (offset + 2) (v >>> 16).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; omega)
  let a4 := a3.set (offset + 3) (v >>> 24).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  ⟨a4⟩

/-- Write a UInt64 (big-endian) at `offset` with bounds proof. -/
@[inline] def writeU64BE (buf : Buffer) (offset : Nat) (val : Radix.UInt64)
    (h : offset + 8 ≤ buf.bytes.size) : Buffer :=
  let v := val.val
  let a1 := buf.bytes.set offset (v >>> 56).toUInt8 (by omega)
  let a2 := a1.set (offset + 1) (v >>> 48).toUInt8 (by rw [set_size_eq]; omega)
  let a3 := a2.set (offset + 2) (v >>> 40).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; omega)
  let a4 := a3.set (offset + 3) (v >>> 32).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  let a5 := a4.set (offset + 4) (v >>> 24).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  let a6 := a5.set (offset + 5) (v >>> 16).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  let a7 := a6.set (offset + 6) (v >>> 8).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  let a8 := a7.set (offset + 7) v.toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  ⟨a8⟩

/-- Write a UInt64 (little-endian) at `offset` with bounds proof. -/
@[inline] def writeU64LE (buf : Buffer) (offset : Nat) (val : Radix.UInt64)
    (h : offset + 8 ≤ buf.bytes.size) : Buffer :=
  let v := val.val
  let a1 := buf.bytes.set offset v.toUInt8 (by omega)
  let a2 := a1.set (offset + 1) (v >>> 8).toUInt8 (by rw [set_size_eq]; omega)
  let a3 := a2.set (offset + 2) (v >>> 16).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; omega)
  let a4 := a3.set (offset + 3) (v >>> 24).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  let a5 := a4.set (offset + 4) (v >>> 32).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  let a6 := a5.set (offset + 5) (v >>> 40).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  let a7 := a6.set (offset + 6) (v >>> 48).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  let a8 := a7.set (offset + 7) (v >>> 56).toUInt8 (by rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; rw [set_size_eq]; omega)
  ⟨a8⟩

/-! ## Tier 2: Checked (Option-returning) access -/

@[inline] def checkedReadU8 (buf : Buffer) (offset : Nat) : Option Radix.UInt8 :=
  if h : offset < buf.bytes.size then some (buf.readU8 offset h) else none

@[inline] def checkedWriteU8 (buf : Buffer) (offset : Nat) (val : Radix.UInt8) : Option Buffer :=
  if h : offset < buf.bytes.size then some (buf.writeU8 offset val h) else none

@[inline] def checkedReadU16BE (buf : Buffer) (offset : Nat) : Option Radix.UInt16 :=
  if h : offset + 2 ≤ buf.bytes.size then some (buf.readU16BE offset h) else none

@[inline] def checkedReadU16LE (buf : Buffer) (offset : Nat) : Option Radix.UInt16 :=
  if h : offset + 2 ≤ buf.bytes.size then some (buf.readU16LE offset h) else none

@[inline] def checkedReadU32BE (buf : Buffer) (offset : Nat) : Option Radix.UInt32 :=
  if h : offset + 4 ≤ buf.bytes.size then some (buf.readU32BE offset h) else none

@[inline] def checkedReadU32LE (buf : Buffer) (offset : Nat) : Option Radix.UInt32 :=
  if h : offset + 4 ≤ buf.bytes.size then some (buf.readU32LE offset h) else none

@[inline] def checkedReadU64BE (buf : Buffer) (offset : Nat) : Option Radix.UInt64 :=
  if h : offset + 8 ≤ buf.bytes.size then some (buf.readU64BE offset h) else none

@[inline] def checkedReadU64LE (buf : Buffer) (offset : Nat) : Option Radix.UInt64 :=
  if h : offset + 8 ≤ buf.bytes.size then some (buf.readU64LE offset h) else none

@[inline] def checkedWriteU16BE (buf : Buffer) (offset : Nat) (val : Radix.UInt16) : Option Buffer :=
  if h : offset + 2 ≤ buf.bytes.size then some (buf.writeU16BE offset val h) else none

@[inline] def checkedWriteU16LE (buf : Buffer) (offset : Nat) (val : Radix.UInt16) : Option Buffer :=
  if h : offset + 2 ≤ buf.bytes.size then some (buf.writeU16LE offset val h) else none

@[inline] def checkedWriteU32BE (buf : Buffer) (offset : Nat) (val : Radix.UInt32) : Option Buffer :=
  if h : offset + 4 ≤ buf.bytes.size then some (buf.writeU32BE offset val h) else none

@[inline] def checkedWriteU32LE (buf : Buffer) (offset : Nat) (val : Radix.UInt32) : Option Buffer :=
  if h : offset + 4 ≤ buf.bytes.size then some (buf.writeU32LE offset val h) else none

@[inline] def checkedWriteU64BE (buf : Buffer) (offset : Nat) (val : Radix.UInt64) : Option Buffer :=
  if h : offset + 8 ≤ buf.bytes.size then some (buf.writeU64BE offset val h) else none

@[inline] def checkedWriteU64LE (buf : Buffer) (offset : Nat) (val : Radix.UInt64) : Option Buffer :=
  if h : offset + 8 ≤ buf.bytes.size then some (buf.writeU64LE offset val h) else none

/-! ## Utility -/

/-- Extract the underlying `ByteArray` from the buffer. -/
@[inline] def toByteArray (buf : Buffer) : ByteArray := buf.bytes

/-- Copy a sub-range of the buffer into a new `ByteArray`. -/
@[inline] def slice (buf : Buffer) (start len : Nat)
    (_h : start + len ≤ buf.bytes.size) : ByteArray :=
  buf.bytes.extract start (start + len)

end Buffer

end Radix.Memory
