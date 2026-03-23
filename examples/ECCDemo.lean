import Radix.ECC

/-!
# Example: Hamming(7,4)
-/

namespace Examples.ECCDemo

def main : IO Unit := do
  IO.println "━━━ ECC Example ━━━"
  let nibble : Radix.ECC.Nibble := ⟨0xD, by decide⟩
  let encoded := Radix.ECC.encodeNibble nibble
  let corrupted := encoded ^^^ 0x20
  IO.println s!"  Encoded:   {encoded.toNat}"
  IO.println s!"  Corrupted: {corrupted.toNat}"
  IO.println s!"  Syndrome:  {Radix.ECC.syndrome corrupted}"
  match (Radix.ECC.correct corrupted : Option UInt8) with
  | some corrected =>
      IO.println s!"  Corrected: {corrected.toNat}"
      IO.println s!"  Decoded:   {Radix.ECC.decode corrected}"
  | none =>
      throw (IO.userError "received byte is not a valid 7-bit codeword")

end Examples.ECCDemo
