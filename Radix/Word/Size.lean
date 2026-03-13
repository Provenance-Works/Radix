/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Word.UInt
import Radix.Word.Spec

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
    For cross-compilation, provide an explicit instance instead.
    `native_decide` is appropriate here: it is a closed ground proposition
    on `System.Platform.numBits` (always 32 or 64 in supported toolchains). -/
instance : PlatformWidth System.Platform.numBits where
  isValid := by native_decide

/-- Unsigned platform-width integer.
    All definitions and proofs are parametric over `platformWidth`. -/
structure UWord (w : Nat := System.Platform.numBits) [PlatformWidth w] where
  val : BitVec w
  deriving DecidableEq

namespace UWord

variable {w : Nat} [PlatformWidth w]

instance : Inhabited (UWord w) := ⟨⟨0⟩⟩
instance : BEq (UWord w) := ⟨fun a b => a.val == b.val⟩
instance : Ord (UWord w) := ⟨fun a b => compare a.val.toNat b.val.toNat⟩
instance : ToString (UWord w) := ⟨fun a => toString a.val.toNat⟩
instance : Repr (UWord w) := ⟨fun a _ => Repr.addAppParen ("UWord.mk " ++ repr a.val) 0⟩
instance {n : Nat} : OfNat (UWord w) n := ⟨⟨BitVec.ofNat w n⟩⟩

@[inline] def toNat (x : UWord w) : Nat := x.val.toNat

/-- Convert to `BitVec w`. -/
@[inline] def toBitVec (x : UWord w) : BitVec w :=
  x.val

@[inline] def fromBitVec (x : BitVec w) : UWord w := ⟨x⟩

@[inline] instance : Add (UWord w) := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub (UWord w) := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul (UWord w) := ⟨fun a b => ⟨a.val * b.val⟩⟩

@[inline] def maxVal : UWord w := ⟨BitVec.ofNat w (2^w - 1)⟩
@[inline] def minVal : UWord w := ⟨0⟩

end UWord

/-- Signed platform-width integer (2's complement).
    Sign is determined by the MSB of the underlying unsigned value. -/
structure IWord (w : Nat := System.Platform.numBits) [PlatformWidth w] where
  val : BitVec w
  deriving DecidableEq

namespace IWord

variable {w : Nat} [PlatformWidth w]

instance : Inhabited (IWord w) := ⟨⟨0⟩⟩
instance : BEq (IWord w) := ⟨fun a b => a.val == b.val⟩
instance : Ord (IWord w) := ⟨fun a b => compare a.val.toInt b.val.toInt⟩
instance : ToString (IWord w) := ⟨fun a => toString a.val.toInt⟩
instance : Repr (IWord w) := ⟨fun a _ => Repr.addAppParen ("IWord.mk " ++ repr a.val) 0⟩
instance {n : Nat} : OfNat (IWord w) n := ⟨⟨BitVec.ofNat w n⟩⟩

@[inline] def toUWord (x : IWord w) : UWord w := ⟨x.val⟩
@[inline] def fromUWord (x : UWord w) : IWord w := ⟨x.val⟩

/-- Interpret the underlying bits as a signed integer. -/
@[inline] def toInt (x : IWord w) : Int :=
  x.val.toInt

/-- Convert to `BitVec w`. -/
@[inline] def toBitVec (x : IWord w) : BitVec w :=
  x.val

@[inline] def fromBitVec (x : BitVec w) : IWord w := ⟨x⟩

@[inline] instance : Add (IWord w) := ⟨fun a b => ⟨a.val + b.val⟩⟩
@[inline] instance : Sub (IWord w) := ⟨fun a b => ⟨a.val - b.val⟩⟩
@[inline] instance : Mul (IWord w) := ⟨fun a b => ⟨a.val * b.val⟩⟩
@[inline] instance : Neg (IWord w) := ⟨fun a => ⟨0 - a.val⟩⟩

@[inline] def maxVal : IWord w := ⟨BitVec.ofInt w (2^(w - 1) - 1)⟩
@[inline] def minVal : IWord w := ⟨BitVec.ofInt w (-(2^(w - 1)))⟩

@[inline] def overflowsAdd (x y : IWord w) : Bool :=
  Word.Spec.signedAddOverflows x.toBitVec y.toBitVec
@[inline] def overflowsSub (x y : IWord w) : Bool :=
  Word.Spec.signedSubOverflows x.toBitVec y.toBitVec
@[inline] def overflowsMul (x y : IWord w) : Bool :=
  Word.Spec.signedMulOverflows x.toBitVec y.toBitVec
@[inline] def divOverflows (x y : IWord w) : Bool :=
  x == minVal && y == ⟨BitVec.ofInt w (-1)⟩

end IWord

/-! ## FixedWidth instances for platform-width types -/

instance {w : Nat} [PlatformWidth w] : FixedWidth (UWord w) where
  bitWidth := w
  toBitVec := UWord.toBitVec
  fromBitVec := UWord.fromBitVec

instance {w : Nat} [PlatformWidth w] : FixedWidth (IWord w) where
  bitWidth := w
  toBitVec := IWord.toBitVec
  fromBitVec := IWord.fromBitVec

end Radix
