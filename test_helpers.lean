import Radix.Binary.Leb128

-- fromBitVec roundtrip
example (x : Radix.UInt32) :
    Radix.UInt32.fromBitVec (BitVec.ofNat 32 x.toNat) = x := by
  simp [Radix.UInt32.fromBitVec, Radix.UInt32.toNat]

-- Also check UInt64, Int32, Int64
example (x : Radix.UInt64) :
    Radix.UInt64.fromBitVec (BitVec.ofNat 64 x.toNat) = x := by
  simp [Radix.UInt64.fromBitVec, Radix.UInt64.toNat]

-- Int32: fromBitVec (ofInt 32 x.toInt) = x
-- Int32 wrapper: val : _root_.UInt8 with toInt via toBitVec.toInt
-- Actually let's check
-- Int32.fromBitVec works on BitVec 32
-- The decode returns Radix.Int32.fromBitVec (BitVec.ofNat 32 final)
-- We need fromBitVec (ofNat 32 (toBitVec.toNat)) = x for unsigned encoding

-- Let's also check the Nat ring tactic alternative
example (n : Nat) : 7 * (n + 1) = 7 * n + 7 := by omega
example (n : Nat) : 7 * n + 7 = 7 * (n + 1) := by omega
