/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Size
import Radix.Memory.Model

/-!
# Pointer Abstraction (Layer 2)

This module provides a typed pointer abstraction over `Memory.Buffer`.
Pointers track provenance (which buffer they reference) and carry
compile-time bounds information.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.
- All pointers are logical references — no FFI, no raw addresses (C-001).
- Pointer arithmetic is bounds-checked at the type level.

## References

- FR-004: Memory Safety
- P2-07 specification
-/

namespace Radix.Memory

/-! ## Typed Pointer -/

/-- A typed pointer into a `Buffer`. Carries the current offset and a proof
    that the offset is within bounds. The type parameter `n` is the byte
    width of the pointed-to type. -/
structure Ptr (n : Nat) where
  /-- The underlying buffer. -/
  buf    : Buffer
  /-- The byte offset into the buffer. -/
  offset : Nat
  /-- Proof that reading `n` bytes at `offset` is in bounds. -/
  hbound : offset + n ≤ buf.bytes.size

namespace Ptr

/-- Create a pointer to the start of a buffer, requiring that the buffer
    is large enough to hold the pointed-to type. -/
@[inline] def ofBuffer (buf : Buffer) (n : Nat) (h : n ≤ buf.bytes.size) : Ptr n :=
  ⟨buf, 0, by omega⟩

/-- Advance the pointer by `k` bytes. -/
@[inline] def advance {n : Nat} (p : Ptr n) (k : Nat) (h : p.offset + k + n ≤ p.buf.bytes.size) : Ptr n :=
  ⟨p.buf, p.offset + k, h⟩

/-- Move the pointer back by `k` bytes. -/
@[inline] def retreat {n : Nat} (p : Ptr n) (k : Nat) (_h : k ≤ p.offset)
    (hb : p.offset - k + n ≤ p.buf.bytes.size) : Ptr n :=
  ⟨p.buf, p.offset - k, hb⟩

/-- Cast the pointer to a different byte width. -/
@[inline] def cast {n : Nat} (p : Ptr n) (m : Nat) (h : p.offset + m ≤ p.buf.bytes.size) : Ptr m :=
  ⟨p.buf, p.offset, h⟩

/-- Read a single byte through the pointer. -/
@[inline] def readU8 (p : Ptr 1) : Radix.UInt8 :=
  p.buf.readU8 p.offset (by have := p.hbound; omega)

/-- Write a single byte through the pointer. -/
@[inline] def writeU8 (p : Ptr 1) (val : Radix.UInt8) : Ptr 1 :=
  let buf' := p.buf.writeU8 p.offset val (by have := p.hbound; omega)
  ⟨buf', p.offset, by
    show p.offset + 1 ≤ buf'.bytes.size
    simp only [buf']
    unfold Buffer.writeU8 ByteArray.set ByteArray.size
    simp
    exact p.hbound⟩

/-- Read a UInt16 (big-endian) through the pointer. -/
@[inline] def readU16BE (p : Ptr 2) : Radix.UInt16 :=
  p.buf.readU16BE p.offset p.hbound

/-- Write a UInt16 (big-endian) through the pointer. -/
@[inline] def writeU16BE (p : Ptr 2) (val : Radix.UInt16) : Ptr 2 :=
  let buf' := p.buf.writeU16BE p.offset val p.hbound
  ⟨buf', p.offset, by
    show p.offset + 2 ≤ buf'.bytes.size
    simp only [buf']
    unfold Buffer.writeU16BE ByteArray.set ByteArray.size; simp
    exact p.hbound⟩

/-- Read a UInt32 (big-endian) through the pointer. -/
@[inline] def readU32BE (p : Ptr 4) : Radix.UInt32 :=
  p.buf.readU32BE p.offset p.hbound

/-- Write a UInt32 (big-endian) through the pointer. -/
@[inline] def writeU32BE (p : Ptr 4) (val : Radix.UInt32) : Ptr 4 :=
  let buf' := p.buf.writeU32BE p.offset val p.hbound
  ⟨buf', p.offset, by
    show p.offset + 4 ≤ buf'.bytes.size
    simp only [buf']
    unfold Buffer.writeU32BE ByteArray.set ByteArray.size; simp
    exact p.hbound⟩

/-- Read a UInt64 (big-endian) through the pointer. -/
@[inline] def readU64BE (p : Ptr 8) : Radix.UInt64 :=
  p.buf.readU64BE p.offset p.hbound

/-- Write a UInt64 (big-endian) through the pointer. -/
@[inline] def writeU64BE (p : Ptr 8) (val : Radix.UInt64) : Ptr 8 :=
  let buf' := p.buf.writeU64BE p.offset val p.hbound
  ⟨buf', p.offset, by
    show p.offset + 8 ≤ buf'.bytes.size
    simp only [buf']
    unfold Buffer.writeU64BE ByteArray.set ByteArray.size; simp
    exact p.hbound⟩

/-- Read a UInt16 (little-endian) through the pointer. -/
@[inline] def readU16LE (p : Ptr 2) : Radix.UInt16 :=
  p.buf.readU16LE p.offset p.hbound

/-- Write a UInt16 (little-endian) through the pointer. -/
@[inline] def writeU16LE (p : Ptr 2) (val : Radix.UInt16) : Ptr 2 :=
  let buf' := p.buf.writeU16LE p.offset val p.hbound
  ⟨buf', p.offset, by
    show p.offset + 2 ≤ buf'.bytes.size
    simp only [buf']
    unfold Buffer.writeU16LE ByteArray.set ByteArray.size; simp
    exact p.hbound⟩

/-- Read a UInt32 (little-endian) through the pointer. -/
@[inline] def readU32LE (p : Ptr 4) : Radix.UInt32 :=
  p.buf.readU32LE p.offset p.hbound

/-- Write a UInt32 (little-endian) through the pointer. -/
@[inline] def writeU32LE (p : Ptr 4) (val : Radix.UInt32) : Ptr 4 :=
  let buf' := p.buf.writeU32LE p.offset val p.hbound
  ⟨buf', p.offset, by
    show p.offset + 4 ≤ buf'.bytes.size
    simp only [buf']
    unfold Buffer.writeU32LE ByteArray.set ByteArray.size; simp
    exact p.hbound⟩

/-- Read a UInt64 (little-endian) through the pointer. -/
@[inline] def readU64LE (p : Ptr 8) : Radix.UInt64 :=
  p.buf.readU64LE p.offset p.hbound

/-- Write a UInt64 (little-endian) through the pointer. -/
@[inline] def writeU64LE (p : Ptr 8) (val : Radix.UInt64) : Ptr 8 :=
  let buf' := p.buf.writeU64LE p.offset val p.hbound
  ⟨buf', p.offset, by
    show p.offset + 8 ≤ buf'.bytes.size
    simp only [buf']
    unfold Buffer.writeU64LE ByteArray.set ByteArray.size; simp
    exact p.hbound⟩

end Ptr

end Radix.Memory
