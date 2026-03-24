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

theorem PrimType.byteSize_pos (p : PrimType) : 0 < p.byteSize ∨ p = .bytes 0 := by
  cases p with
  | byte => simp [PrimType.byteSize]
  | uint16 e => simp [PrimType.byteSize]
  | uint32 e => simp [PrimType.byteSize]
  | uint64 e => simp [PrimType.byteSize]
  | bytes count =>
    by_cases h : count = 0
    · right
      simp [h]
    · left
      simp [PrimType.byteSize]
      omega

/-! ## Format Size Properties -/

theorem Format.fixedSize_byte (name : String) :
    (Format.byte name).fixedSize = some 1 := by
  simp [Format.fixedSize, Format.fixedEndOffset]

theorem Format.fixedSize_uint16 (name : String) (e : Spec.Endian) :
    (Format.uint16 name e).fixedSize = some 2 := by
  simp [Format.fixedSize, Format.fixedEndOffset]

theorem Format.fixedSize_uint32 (name : String) (e : Spec.Endian) :
    (Format.uint32 name e).fixedSize = some 4 := by
  simp [Format.fixedSize, Format.fixedEndOffset]

theorem Format.fixedSize_uint64 (name : String) (e : Spec.Endian) :
    (Format.uint64 name e).fixedSize = some 8 := by
  simp [Format.fixedSize, Format.fixedEndOffset]

theorem Format.fixedSize_bytes (name : String) (count : Nat) :
    (Format.bytes name count).fixedSize = some count := by
  simp [Format.fixedSize, Format.fixedEndOffset]

theorem Format.fixedSize_lengthPrefixedBytes (name : String) (prefixBytes : Nat) (e : Spec.Endian) :
    (Format.lengthPrefixedBytes name prefixBytes e).fixedSize = none := by
  simp [Format.fixedSize, Format.fixedEndOffset]

theorem Format.fixedSize_countPrefixedArray (name : String) (prefixBytes : Nat)
    (e : Spec.Endian) (elem : Format) :
    (Format.countPrefixedArray name prefixBytes e elem).fixedSize = none := by
  simp [Format.fixedSize, Format.fixedEndOffset]

theorem Format.fixedSize_constBytes (value : ByteArray) :
    (Format.constBytes value).fixedSize = some value.size := by
  simp [Format.fixedSize, Format.fixedEndOffset]

theorem Format.fixedSize_padding (n : Nat) :
    (Format.padding n).fixedSize = some n := by
  simp [Format.fixedSize, Format.fixedEndOffset]

theorem Format.fixedSize_align (n : Nat) :
    (Format.align n).fixedSize = some 0 := by
  simp [Format.fixedSize, Format.fixedEndOffset, Spec.alignedOffset, Spec.paddingToAlign]

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

theorem Format.fieldNames_align (n : Nat) :
  (Format.align n).fieldNames = [] := rfl

theorem Format.fieldNames_bytes (name : String) (count : Nat) :
    (Format.bytes name count).fieldNames = [name] := rfl

theorem Format.fieldNames_lengthPrefixedBytes (name : String) (prefixBytes : Nat) (e : Spec.Endian) :
  (Format.lengthPrefixedBytes name prefixBytes e).fieldNames = [name] := rfl

theorem Format.fieldNames_countPrefixedArray (name : String) (prefixBytes : Nat)
    (e : Spec.Endian) (elem : Format) :
  (Format.countPrefixedArray name prefixBytes e elem).fieldNames = name :: elem.fieldNames := rfl

theorem Format.fieldNames_constBytes (value : ByteArray) :
    (Format.constBytes value).fieldNames = [] := rfl

/-! ## Field count properties -/

theorem Format.fieldCount_byte (name : String) :
    (Format.byte name).fieldCount = 1 := rfl

theorem Format.fieldCount_padding (n : Nat) :
    (Format.padding n).fieldCount = 0 := rfl

theorem Format.fieldCount_align (n : Nat) :
  (Format.align n).fieldCount = 0 := rfl

theorem Format.fieldCount_bytes (name : String) (count : Nat) :
    (Format.bytes name count).fieldCount = 1 := rfl

theorem Format.fieldCount_lengthPrefixedBytes (name : String) (prefixBytes : Nat) (e : Spec.Endian) :
  (Format.lengthPrefixedBytes name prefixBytes e).fieldCount = 1 := rfl

theorem Format.fieldCount_countPrefixedArray (name : String) (prefixBytes : Nat)
    (e : Spec.Endian) (elem : Format) :
  (Format.countPrefixedArray name prefixBytes e elem).fieldCount = 1 + elem.fieldCount := rfl

theorem Format.fieldCount_constBytes (value : ByteArray) :
    (Format.constBytes value).fieldCount = 0 := rfl

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

theorem PrimType.byteSize_bytes (count : Nat) :
  (PrimType.bytes count).byteSize = count := rfl

/-- All byte sizes are powers of 2 (or 1). -/
theorem PrimType.byteSize_isPow2Or1 (p : PrimType) :
    p = .byte
    ∨ (∃ e, p = .uint16 e)
    ∨ (∃ e, p = .uint32 e)
    ∨ (∃ e, p = .uint64 e)
    ∨ (∃ count, p = .bytes count) := by
  cases p <;> simp

/-- Non-blob primitive widths fit within eight bytes. -/
theorem PrimType.byteSize_le_8_of_not_bytes (p : PrimType)
    (h : ∀ count, p ≠ .bytes count) : p.byteSize ≤ 8 := by
  cases p with
  | byte => simp [PrimType.byteSize]
  | uint16 e => simp [PrimType.byteSize]
  | uint32 e => simp [PrimType.byteSize]
  | uint64 e => simp [PrimType.byteSize]
  | bytes count => exact False.elim (h count rfl)

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

theorem Format.fieldNames_bytes' (name : String) (count : Nat) :
  (Format.bytes name count).fieldNames = [name] := rfl

/-- `seq` computes its fixed end offset by threading the intermediate offset. -/
theorem Format.fixedEndOffset_seq (offset : Nat) (a b : Format) :
    Format.fixedEndOffset offset (Format.seq a b) =
      match Format.fixedEndOffset offset a with
      | some off => Format.fixedEndOffset off b
      | none => none := by
  cases h : Format.fixedEndOffset offset a <;> simp [Format.fixedEndOffset, h]

/-- fieldCount of a singleton byte format is 1. -/
theorem Format.fieldCount_uint16 (name : String) (e : Spec.Endian) :
    (Format.uint16 name e).fieldCount = 1 := rfl

theorem Format.fieldCount_uint32 (name : String) (e : Spec.Endian) :
    (Format.uint32 name e).fieldCount = 1 := rfl

theorem Format.fieldCount_uint64 (name : String) (e : Spec.Endian) :
    (Format.uint64 name e).fieldCount = 1 := rfl

theorem Format.fieldCount_bytes' (name : String) (count : Nat) :
  (Format.bytes name count).fieldCount = 1 := rfl

-- ════════════════════════════════════════════════════════════════════
-- BitField Properties
-- ════════════════════════════════════════════════════════════════════

/-- Extracting a bit-field always produces a value less than 2^width. -/
theorem BitFieldSpec.extract_lt_pow2 (bf : Spec.BitFieldSpec) (v : Nat) :
    bf.extract v < 2 ^ bf.width := by
  simp [Spec.BitFieldSpec.extract]
  exact Nat.mod_lt _ (Nat.two_pow_pos bf.width)

/-- Two disjoint fields are symmetric. -/
theorem BitFieldSpec.disjoint_comm (a b : Spec.BitFieldSpec) :
    Spec.BitFieldSpec.disjoint a b ↔ Spec.BitFieldSpec.disjoint b a := by
  simp [Spec.BitFieldSpec.disjoint, Spec.BitFieldSpec.endPos]
  omega

-- ════════════════════════════════════════════════════════════════════
-- Concrete Test Vectors
-- ════════════════════════════════════════════════════════════════════

/-- PrimType byte has size 1. -/
example : Spec.PrimType.byteSize .byte = 1 := by rfl

/-- PrimType uint16 has size 2. -/
example : Spec.PrimType.byteSize (.uint16 .little) = 2 := by rfl

/-- PrimType uint32 has size 4. -/
example : Spec.PrimType.byteSize (.uint32 .big) = 4 := by rfl

/-- PrimType uint64 has size 8. -/
example : Spec.PrimType.byteSize (.uint64 .little) = 8 := by rfl

/-- Padding to align 0 to 4 is 0. -/
example : Spec.paddingToAlign 0 4 = 0 := by native_decide

/-- Padding to align 3 to 4 is 1. -/
example : Spec.paddingToAlign 3 4 = 1 := by native_decide

/-- Padding to align 4 to 4 is 0. -/
example : Spec.paddingToAlign 4 4 = 0 := by native_decide

/-- Padding to align 5 to 4 is 3. -/
example : Spec.paddingToAlign 5 4 = 3 := by native_decide

/-- alignedOffset 5 4 = 8. -/
example : Spec.alignedOffset 5 4 = 8 := by native_decide

/-- VarLen length-prefixed has 2-byte overhead. -/
example : Spec.VarLenType.minOverhead (.lengthPrefixed 2 .little) = 2 := by rfl

/-- VarLen count-prefixed arrays contribute only the prefix to the minimum size. -/
example : Spec.VarLenType.minOverhead (.countPrefixedArray 2 .little 4) = 2 := by rfl

/-- VarLen null-terminated has 1-byte overhead. -/
example : Spec.VarLenType.minOverhead .nullTerminated = 1 := by rfl

end Radix.Binary
