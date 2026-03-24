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

-- ════════════════════════════════════════════════════════════════════
-- PrimType Byte Size Properties
-- ════════════════════════════════════════════════════════════════════

/-- byteSize for byte type is exactly 1. -/
theorem PrimType.byteSize_byte : PrimType.byte.byteSize = 1 := rfl

/-- byteSize for uint16 is exactly 2 regardless of endianness. -/
theorem PrimType.byteSize_uint16 (e : Spec.Endian) :
    (PrimType.uint16 e).byteSize = 2 := rfl

/-- byteSize for uint32 is exactly 4 regardless of endianness. -/
theorem PrimType.byteSize_uint32 (e : Spec.Endian) :
    (PrimType.uint32 e).byteSize = 4 := rfl

/-- byteSize for uint64 is exactly 8 regardless of endianness. -/
theorem PrimType.byteSize_uint64 (e : Spec.Endian) :
    (PrimType.uint64 e).byteSize = 8 := rfl

/-- All byte sizes are powers of 2 (or 1). -/
theorem PrimType.byteSize_isPow2Or1 (p : PrimType) :
    p.byteSize = 1 ∨ p.byteSize = 2 ∨ p.byteSize = 4 ∨ p.byteSize = 8 := by
  cases p <;> simp [PrimType.byteSize]

/-- byteSize is at most 8. -/
theorem PrimType.byteSize_le_8 (p : PrimType) : p.byteSize ≤ 8 := by
  cases p <;> simp [PrimType.byteSize]

-- ════════════════════════════════════════════════════════════════════
-- FormatSpec Validity Properties
-- ════════════════════════════════════════════════════════════════════

/-- A single-field format is valid when the field fits within totalSize. -/
theorem FormatSpec.singleton_isValid (f : Spec.FieldSpec) (h : f.endOffset ≤ f.endOffset) :
    FormatSpec.isValid { fields := [f], totalSize := f.endOffset } := by
  constructor
  · intro g hg
    simp at hg; subst hg
    exact Nat.le_refl _
  · intro a ha b hb hab
    simp at ha hb
    subst ha; subst hb
    exact absurd rfl hab

/-- Fields in bounds is preserved when growing totalSize. -/
theorem FormatSpec.fieldsInBounds_mono (spec : FormatSpec) (n : Nat)
    (h : spec.fieldsInBounds) (hge : spec.totalSize ≤ n) :
    (FormatSpec.mk spec.fields n).fieldsInBounds := by
  intro f hf
  exact Nat.le_trans (h f hf) hge

-- ════════════════════════════════════════════════════════════════════
-- BitField Properties
-- ════════════════════════════════════════════════════════════════════

/-- Extracting from zero always yields zero. -/
theorem BitFieldSpec.extract_zero (bf : Spec.BitFieldSpec) :
    bf.extract 0 = 0 := by
  simp [Spec.BitFieldSpec.extract]

/-- BitField disjointness is symmetric. -/
theorem BitFieldSpec.disjoint_symm (a b : Spec.BitFieldSpec)
    (h : Spec.BitFieldSpec.disjoint a b) :
    Spec.BitFieldSpec.disjoint b a := by
  cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

/-- A register with no fields is trivially valid. -/
theorem RegisterSpec.empty_isValid (w : Nat) :
    Spec.RegisterSpec.isValid { bitWidth := w, fields := [] } := by
  constructor
  · intro nf hf; simp at hf
  · intro a ha; simp at ha

-- ════════════════════════════════════════════════════════════════════
-- Padding and Alignment Properties
-- ════════════════════════════════════════════════════════════════════

/-- paddingToAlign with alignment 0 or 1 is always 0. -/
theorem paddingToAlign_trivial (offset : Nat) :
    Spec.paddingToAlign offset 0 = 0 ∧ Spec.paddingToAlign offset 1 = 0 := by
  simp [Spec.paddingToAlign]

/-- Already-aligned offsets need no padding. -/
theorem paddingToAlign_zero_of_aligned (n alignment : Nat) (ha : 1 < alignment)
    (h : n % alignment = 0) :
    Spec.paddingToAlign n alignment = 0 := by
  unfold Spec.paddingToAlign
  split
  · omega
  · rw [h]; simp

/-- alignedOffset is at least the original offset. -/
theorem alignedOffset_ge (offset alignment : Nat) :
    offset ≤ Spec.alignedOffset offset alignment := by
  unfold Spec.alignedOffset Spec.paddingToAlign
  split <;> omega
-- ════════════════════════════════════════════════════════════════════
-- Format Sequence Properties
-- ════════════════════════════════════════════════════════════════════

/-- fieldNames of a seq is the concatenation of sub-format fieldNames. -/
theorem Format.fieldNames_seq (a b : Format) :
    (Format.seq a b).fieldNames = a.fieldNames ++ b.fieldNames := rfl

/-- fieldNames of uint16 contains just the field name. -/
theorem Format.fieldNames_uint16 (name : String) (e : Spec.Endian) :
    (Format.uint16 name e).fieldNames = [name] := rfl

/-- fieldNames of uint32 contains just the field name. -/
theorem Format.fieldNames_uint32 (name : String) (e : Spec.Endian) :
    (Format.uint32 name e).fieldNames = [name] := rfl

/-- fieldNames of uint64 contains just the field name. -/
theorem Format.fieldNames_uint64 (name : String) (e : Spec.Endian) :
    (Format.uint64 name e).fieldNames = [name] := rfl

/-- fixedSize of a seq with two known sizes is their sum. -/
theorem Format.fixedSize_seq (a b : Format) (sa sb : Nat)
    (ha : a.fixedSize = some sa) (hb : b.fixedSize = some sb) :
    (Format.seq a b).fixedSize = some (sa + sb) := by
  simp [Format.fixedSize, ha, hb]

/-- fieldCount of a singleton byte format is 1. -/
theorem Format.fieldCount_uint16 (name : String) (e : Spec.Endian) :
    (Format.uint16 name e).fieldCount = 1 := rfl

theorem Format.fieldCount_uint32 (name : String) (e : Spec.Endian) :
    (Format.uint32 name e).fieldCount = 1 := rfl

theorem Format.fieldCount_uint64 (name : String) (e : Spec.Endian) :
    (Format.uint64 name e).fieldCount = 1 := rfl

end Radix.Binary
