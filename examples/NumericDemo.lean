import Radix.Word.Numeric

/-!
# Example: Numeric Typeclasses

Demonstrates writing generic code over any integer width using the
`BoundedUInt`, `BoundedInt`, and `BitwiseOps` typeclasses.

- Generic functions that work with UInt8, UInt16, UInt32, UInt64
- Generic signed integer bounds checking
- Generic bitwise operations
-/

namespace Examples.NumericDemo

open Radix (BoundedUInt BoundedInt BitwiseOps FixedWidth isZero isMax)

/-! ## Generic Unsigned Arithmetic -/

/-- Generic helper: display bounds for a BoundedUInt type. -/
def showBounds (name : String) {α : Type} [inst : BoundedUInt α] : IO Unit := do
  IO.println s!"  {name}: min = {inst.toNat inst.minVal}, max = {inst.toNat inst.maxVal}, bits = {FixedWidth.bitWidth (α := α)}"

/-- Generic helper: display bounds for a BoundedInt type. -/
def showSignedBounds (name : String) {α : Type} [inst : BoundedInt α] : IO Unit := do
  IO.println s!"  {name}: min = {inst.toInt inst.minVal}, max = {inst.toInt inst.maxVal}, bits = {FixedWidth.bitWidth (α := α)}"

/-- Generic zero check via typeclass. -/
def demonstrateZeroCheck {α : Type} [inst : BoundedUInt α] (name : String) : IO Unit := do
  let z := inst.minVal
  let m := inst.maxVal
  IO.println s!"  {name}: isZero(minVal) = {isZero z}, isZero(maxVal) = {isZero m}"
  IO.println s!"  {name}: isMax(minVal) = {isMax z}, isMax(maxVal) = {isMax m}"

/-- Generic wrapping add demonstration. -/
def demonstrateWrapping {α : Type} [inst : BoundedUInt α] (name : String) : IO Unit := do
  let m := inst.maxVal
  -- Compute 1 generically: minVal - maxVal = 0 - (2^n - 1) = 1 (mod 2^n)
  let one := inst.wrappingSub inst.minVal m
  let wrapped := inst.wrappingAdd m one
  IO.println s!"  {name}: maxVal + 1 (wrapping) = {inst.toNat wrapped}"

def main : IO Unit := do
  IO.println "=== Numeric Typeclasses: BoundedUInt ==="
  showBounds "UInt8"  (α := Radix.UInt8)
  showBounds "UInt16" (α := Radix.UInt16)
  showBounds "UInt32" (α := Radix.UInt32)
  showBounds "UInt64" (α := Radix.UInt64)

  IO.println ""
  IO.println "=== Numeric Typeclasses: BoundedInt ==="
  showSignedBounds "Int8"  (α := Radix.Int8)
  showSignedBounds "Int16" (α := Radix.Int16)
  showSignedBounds "Int32" (α := Radix.Int32)
  showSignedBounds "Int64" (α := Radix.Int64)

  IO.println ""
  IO.println "=== Generic Zero/Max Check ==="
  demonstrateZeroCheck (α := Radix.UInt8)  "UInt8"
  demonstrateZeroCheck (α := Radix.UInt16) "UInt16"
  demonstrateZeroCheck (α := Radix.UInt32) "UInt32"
  demonstrateZeroCheck (α := Radix.UInt64) "UInt64"

  IO.println ""
  IO.println "=== Generic Wrapping Arithmetic ==="
  demonstrateWrapping (α := Radix.UInt8)  "UInt8"
  demonstrateWrapping (α := Radix.UInt16) "UInt16"
  demonstrateWrapping (α := Radix.UInt32) "UInt32"

  IO.println ""
  IO.println "=== BitwiseOps: Generic Popcount ==="
  IO.println s!"  UInt8  popcount(0xFF) = {(BitwiseOps.popcount (⟨0xFF⟩ : Radix.UInt8)).toNat}"
  IO.println s!"  UInt16 popcount(0xAAAA) = {(BitwiseOps.popcount (⟨0xAAAA⟩ : Radix.UInt16)).toNat}"
  IO.println s!"  UInt32 popcount(0xDEADBEEF) = {(BitwiseOps.popcount (⟨0xDEADBEEF⟩ : Radix.UInt32)).toNat}"

  IO.println ""
  IO.println "Numeric typeclass demo complete."

end Examples.NumericDemo
