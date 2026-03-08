/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt

/-!
# Platform-Width Types (Layer 2)

This module defines `UWord` and `IWord`, platform-width integer types
parameterized by a `PlatformWidth` typeclass. This approach avoids
hard-coding `System.Platform.numBits`, enabling cross-compilation safety.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.

## References

- FR-001.1a: Platform-Sized Types
- NFR-002: Zero-cost abstractions
-/

namespace Radix

/-- Typeclass constraining the platform pointer width to realistic values (32 or 64).
    This enables cross-compilation: proofs are parametric over width,
    and a default instance resolves to the host's `System.Platform.numBits`. -/
class PlatformWidth (n : Nat) where
  isValid : n = 32 ∨ n = 64

/-- Default instance: resolve to host platform width.
    For cross-compilation, provide an explicit instance instead. -/
instance : PlatformWidth System.Platform.numBits where
  isValid := by native_decide

/-- Unsigned platform-width integer wrapping Lean 4's `USize`.
    All definitions and proofs are parametric over `platformWidth`. -/
structure UWord where
  val : _root_.USize
  deriving DecidableEq

namespace UWord

instance : Inhabited UWord := ⟨⟨0⟩⟩
instance : BEq UWord := ⟨fun a b => a.val == b.val⟩
instance : Ord UWord := ⟨fun a b => compare a.val b.val⟩
instance : ToString UWord := ⟨fun a => toString a.val⟩
instance : Repr UWord := ⟨fun a n => reprPrec a.val n⟩
instance {n : Nat} : OfNat UWord n := ⟨⟨OfNat.ofNat n⟩⟩

@[inline] def toBuiltin (x : UWord) : USize := x.val
@[inline] def fromBuiltin (x : USize) : UWord := ⟨x⟩
@[inline] def toNat (x : UWord) : Nat := x.val.toNat

/-- Convert to `BitVec System.Platform.numBits`. -/
@[inline] def toBitVec (x : UWord) : BitVec System.Platform.numBits :=
  x.val.toBitVec

@[inline] instance : Add UWord := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub UWord := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul UWord := ⟨fun a b => ⟨a.val * b.val⟩⟩

end UWord

/-- Signed platform-width integer wrapping Lean 4's `USize` (2's complement).
    Sign is determined by the MSB of the underlying unsigned value. -/
structure IWord where
  val : _root_.USize
  deriving DecidableEq

namespace IWord

instance : Inhabited IWord := ⟨⟨0⟩⟩
instance : BEq IWord := ⟨fun a b => a.val == b.val⟩
instance : Ord IWord := ⟨fun a b => compare a.val b.val⟩
instance : ToString IWord := ⟨fun a => toString a.val.toBitVec.toInt⟩
instance : Repr IWord := ⟨fun a _ => Repr.addAppParen ("IWord.mk " ++ repr a.val) 0⟩
instance {n : Nat} : OfNat IWord n := ⟨⟨OfNat.ofNat n⟩⟩

@[inline] def toUWord (x : IWord) : UWord := ⟨x.val⟩
@[inline] def fromUWord (x : UWord) : IWord := ⟨x.val⟩

/-- Interpret the underlying bits as a signed integer. -/
@[inline] def toInt (x : IWord) : Int :=
  x.val.toBitVec.toInt

/-- Convert to `BitVec System.Platform.numBits`. -/
@[inline] def toBitVec (x : IWord) : BitVec System.Platform.numBits :=
  x.val.toBitVec

@[inline] instance : Add IWord := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub IWord := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul IWord := ⟨fun a b => ⟨a.val * b.val⟩⟩

end IWord

end Radix
