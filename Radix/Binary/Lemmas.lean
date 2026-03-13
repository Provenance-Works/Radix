/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Binary.Parser
import Radix.Binary.Serial
import Radix.Binary.Spec
import Radix.Binary.Format

/-!
# Binary Format Proofs (Layer 3)

This module contains proofs for:
- Format size computation properties
- PrimType byte size positivity
- FormatSpec validity properties
- Padding serialization correctness

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- P2-14 specification
-/

namespace Radix.Binary

open Spec

/-! ## PrimType Properties -/

theorem PrimType.byteSize_pos (p : PrimType) : 0 < p.byteSize := by
  cases p <;> simp [PrimType.byteSize]

/-! ## Format Size Properties -/

theorem Format.fixedSize_byte (name : String) :
    (Format.byte name).fixedSize = some 1 := rfl

theorem Format.fixedSize_uint16 (name : String) (e : Spec.Endian) :
    (Format.uint16 name e).fixedSize = some 2 := rfl

theorem Format.fixedSize_uint32 (name : String) (e : Spec.Endian) :
    (Format.uint32 name e).fixedSize = some 4 := rfl

theorem Format.fixedSize_uint64 (name : String) (e : Spec.Endian) :
    (Format.uint64 name e).fixedSize = some 8 := rfl

theorem Format.fixedSize_padding (n : Nat) :
    (Format.padding n).fixedSize = some n := rfl

/-! ## FormatSpec Properties -/

theorem FormatSpec.empty_isValid :
    FormatSpec.isValid ⟨[], 0⟩ := by
  constructor
  · intro f hf; simp at hf
  · intro f hf; simp at hf

/-! ## Field name properties -/

theorem Format.fieldNames_byte (name : String) :
    (Format.byte name).fieldNames = [name] := rfl

theorem Format.fieldNames_padding (n : Nat) :
    (Format.padding n).fieldNames = [] := rfl

/-! ## Field count properties -/

theorem Format.fieldCount_byte (name : String) :
    (Format.byte name).fieldCount = 1 := rfl

theorem Format.fieldCount_padding (n : Nat) :
    (Format.padding n).fieldCount = 0 := rfl

theorem Format.fieldCount_seq (a b : Format) :
    (Format.seq a b).fieldCount = a.fieldCount + b.fieldCount := rfl

/-! ## Padding serialization produces correct length -/

private theorem ByteArray.size_push (a : ByteArray) (v : _root_.UInt8) :
    (a.push v).size = a.size + 1 := by
  unfold ByteArray.push ByteArray.size; simp [Array.size_push]

theorem Serial.writePadding_size (acc : ByteArray) (n : Nat) :
    (Serial.writePadding acc n).size = acc.size + n := by
  induction n generalizing acc with
  | zero => simp [Serial.writePadding]
  | succ k ih =>
    unfold Serial.writePadding
    rw [ih]
    rw [ByteArray.size_push]
    omega

/-! ## Parse/serialize padding round-trip -/

theorem Parser.parse_padding_ok (data : ByteArray) (offset n : Nat)
    (h : offset + n ≤ data.size) :
    Parser.parse data (.padding n) offset = .ok ([], offset + n) := by
  simp [Parser.parse, h]

end Radix.Binary
