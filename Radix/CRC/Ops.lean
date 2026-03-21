/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Arith
import Radix.Bit.Ops
import Radix.CRC.Spec

/-!
# CRC Implementation (Layer 2)

Table-driven CRC-32 and CRC-16 implementations for high-throughput
checksum computation.

## Supported Algorithms

- **CRC-32/ISO-HDLC**: Ethernet, gzip, PNG, MPEG-2
  - Polynomial: 0xEDB88320 (reflected)
  - Init: 0xFFFFFFFF, XorOut: 0xFFFFFFFF
  - Check value for "123456789": 0xCBF43926

- **CRC-16/CCITT**: X.25, HDLC, Bluetooth
  - Polynomial: 0x8408 (reflected)
  - Init: 0xFFFF, XorOut: 0xFFFF
  - Check value for "123456789": 0x906E

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- v0.2.0 Roadmap: CRC-32 / CRC-16
- Ross N. Williams, "A Painless Guide to CRC Error Detection Algorithms"
- NFR-002: Zero-cost abstractions
-/

namespace Radix.CRC

/-! ================================================================ -/
/-! ## CRC-32                                                         -/
/-! ================================================================ -/

namespace CRC32

/-- CRC-32 polynomial in reflected (LSB-first) representation. -/
@[inline] def poly : _root_.UInt32 := 0xEDB88320

/-- Initial CRC-32 register value (all ones). -/
@[inline] def initVal : _root_.UInt32 := 0xFFFFFFFF

/-- Build one entry of the CRC-32 lookup table.
    Processes a byte value through 8 bits of polynomial division. -/
private def buildTableEntry (byte : _root_.UInt32) : _root_.UInt32 :=
  go byte 8
where
  go (crc : _root_.UInt32) : Nat → _root_.UInt32
    | 0 => crc
    | fuel + 1 =>
      if crc &&& 1 != 0 then
        go ((crc >>> 1) ^^^ poly) fuel
      else
        go (crc >>> 1) fuel

/-- Precomputed CRC-32 lookup table (256 entries). -/
def table : Array _root_.UInt32 :=
  Array.ofFn (n := 256) fun i => buildTableEntry i.val.toUInt32

/-- Update CRC-32 with a single byte using table lookup.
    Core operation: `crc = table[(crc ^ byte) & 0xFF] ^ (crc >> 8)` -/
@[inline] def updateByte (crc : _root_.UInt32) (byte : _root_.UInt8) : _root_.UInt32 :=
  let index := ((crc ^^^ byte.toUInt32) &&& 0xFF).toNat
  match table[index]? with
  | some entry => entry ^^^ (crc >>> 8)
  | none => crc  -- Unreachable: index is always < 256

/-- Compute CRC-32 of a `ByteArray`.
    This is the primary entry point for CRC-32 computation. -/
@[inline] def compute (data : ByteArray) : Radix.UInt32 :=
  let result := data.foldl (init := initVal) fun crc byte =>
    updateByte crc byte
  ⟨result ^^^ initVal⟩

/-- Update a running CRC-32 with additional data (for streaming).
    Call `init` to start, `update` for each chunk, `finalize` to finish. -/
@[inline] def init : _root_.UInt32 := initVal

/-- Feed more data into a running CRC-32 computation. -/
@[inline] def update (crc : _root_.UInt32) (data : ByteArray) : _root_.UInt32 :=
  data.foldl (init := crc) fun c byte => updateByte c byte

/-- Finalize a running CRC-32 computation. -/
@[inline] def finalize (crc : _root_.UInt32) : Radix.UInt32 := ⟨crc ^^^ initVal⟩

/-- Compute CRC-32 bit-by-bit (reference implementation, no table).
    Used for verification against the table-driven version. -/
def computeNaive (data : ByteArray) : Radix.UInt32 :=
  let result := data.foldl (init := initVal) fun crc byte =>
    updateByteNaive crc byte
  ⟨result ^^^ initVal⟩
where
  /-- Process one byte bit-by-bit through the CRC-32 register. -/
  updateByteNaive (crc : _root_.UInt32) (byte : _root_.UInt8) : _root_.UInt32 :=
    let init := crc ^^^ byte.toUInt32
    go init 8
  go (crc : _root_.UInt32) : Nat → _root_.UInt32
    | 0 => crc
    | fuel + 1 =>
      if crc &&& 1 != 0 then
        go ((crc >>> 1) ^^^ poly) fuel
      else
        go (crc >>> 1) fuel

end CRC32

/-! ================================================================ -/
/-! ## CRC-16/CCITT                                                   -/
/-! ================================================================ -/

namespace CRC16

/-- CRC-16/CCITT polynomial in reflected (LSB-first) representation. -/
@[inline] def poly : _root_.UInt16 := 0x8408

/-- Initial CRC-16 register value (all ones). -/
@[inline] def initVal : _root_.UInt16 := 0xFFFF

/-- Build one entry of the CRC-16 lookup table. -/
private def buildTableEntry (byte : _root_.UInt16) : _root_.UInt16 :=
  go byte 8
where
  go (crc : _root_.UInt16) : Nat → _root_.UInt16
    | 0 => crc
    | fuel + 1 =>
      if crc &&& 1 != 0 then
        go ((crc >>> 1) ^^^ poly) fuel
      else
        go (crc >>> 1) fuel

/-- Precomputed CRC-16 lookup table (256 entries). -/
def table : Array _root_.UInt16 :=
  Array.ofFn (n := 256) fun i => buildTableEntry i.val.toUInt16

/-- Update CRC-16 with a single byte using table lookup. -/
@[inline] def updateByte (crc : _root_.UInt16) (byte : _root_.UInt8) : _root_.UInt16 :=
  let index := ((crc ^^^ byte.toUInt16) &&& 0xFF).toNat
  match table[index]? with
  | some entry => entry ^^^ (crc >>> 8)
  | none => crc  -- Unreachable: index is always < 256

/-- Compute CRC-16/CCITT of a `ByteArray`. -/
@[inline] def compute (data : ByteArray) : Radix.UInt16 :=
  let result := data.foldl (init := initVal) fun crc byte =>
    updateByte crc byte
  ⟨result ^^^ initVal⟩

/-- Initialize a streaming CRC-16 computation. -/
@[inline] def init : _root_.UInt16 := initVal

/-- Feed more data into a running CRC-16 computation. -/
@[inline] def update (crc : _root_.UInt16) (data : ByteArray) : _root_.UInt16 :=
  data.foldl (init := crc) fun c byte => updateByte c byte

/-- Finalize a running CRC-16 computation. -/
@[inline] def finalize (crc : _root_.UInt16) : Radix.UInt16 := ⟨crc ^^^ initVal⟩

/-- Compute CRC-16 bit-by-bit (reference implementation, no table). -/
def computeNaive (data : ByteArray) : Radix.UInt16 :=
  let result := data.foldl (init := initVal) fun crc byte =>
    updateByteNaive crc byte
  ⟨result ^^^ initVal⟩
where
  updateByteNaive (crc : _root_.UInt16) (byte : _root_.UInt8) : _root_.UInt16 :=
    let init := crc ^^^ byte.toUInt16
    go init 8
  go (crc : _root_.UInt16) : Nat → _root_.UInt16
    | 0 => crc
    | fuel + 1 =>
      if crc &&& 1 != 0 then
        go ((crc >>> 1) ^^^ poly) fuel
      else
        go (crc >>> 1) fuel

end CRC16

end Radix.CRC
