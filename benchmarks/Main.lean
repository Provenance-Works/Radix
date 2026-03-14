import Radix.Word.Arith
import Radix.Word.Int
import Radix.Word.Conv
import Radix.Bit.Ops
import Radix.Bit.Scan
import Radix.Bit.Field
import Radix.Bytes
import Radix.Bytes.Order
import Radix.Binary.Leb128

/-!
# Radix Phase 4 — Microbenchmarks (P4-02)

Microbenchmarks for individual operations per NFR-002.2.

## Anti-DCE/LICM Countermeasures (NFR-002.2)

1. **Accumulator sink**: Each iteration feeds its result into
   the next iteration's input.
2. **Input-dependent operands**: Pre-generated pseudo-random arrays
   indexed per iteration.
3. **Validation step**: Final accumulator is printed. If 0 for
   a non-trivial workload, the benchmark is invalid.

## Measurement

- Each benchmark runs 10^6 iterations in a tight loop.
- Wall-clock time measured with `IO.monoNanosNow`.
- Results printed as ns/op.

## References

- NFR-002.2: Measurement Method
- P4-02: Benchmarks
-/

set_option autoImplicit false

/-! ## PRNG for input generation -/

private structure PRNG where
  state : UInt64

private def PRNG.new (seed : UInt64 := 42) : PRNG := { state := seed }

private def PRNG.next (rng : PRNG) : PRNG × UInt64 :=
  let a : UInt64 := 6364136223846793005
  let c : UInt64 := 1442695040888963407
  let s := rng.state * a + c
  ({ state := s }, s)

/-! ## Configuration -/

/-- Number of iterations per benchmark. -/
private def numIter : Nat := 1000000

/-- Generate an array of N random UInt64 values. -/
private def genRandomArray (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut rng := PRNG.new seed
  let mut arr := Array.mkEmpty n
  for _ in [:n] do
    let (rng', v) := rng.next
    rng := rng'
    arr := arr.push v
  return arr

/-- Prevent DCE by printing the accumulator (noinline-equivalent). -/
@[noinline] private def sink (label : String) (value : UInt64) : IO Unit :=
  IO.println s!"  {label}: accumulator = {value}"

@[noinline] private def sinkU32 (label : String) (value : UInt32) : IO Unit :=
  IO.println s!"  {label}: accumulator = {value}"

/-- Run a benchmark: time N iterations, print ns/op. -/
private def bench (label : String) (action : IO UInt64) : IO Unit := do
  -- Warmup (2 runs)
  let _ ← action
  let _ ← action
  -- Measured runs (5 runs, take median)
  let mut times : Array Nat := #[]
  for _ in [:5] do
    let t0 ← IO.monoNanosNow
    let acc ← action
    let t1 ← IO.monoNanosNow
    times := times.push (t1 - t0)
    sink label acc
  -- Sort and take median
  let sorted := times.qsort (· < ·)
  let median := sorted[2]!
  let nsPerOp := median / numIter
  IO.println s!"  {label}: {nsPerOp} ns/op (median of 5, {numIter} iters)"

/-! ================================================================ -/
/-! ## UInt32 Arithmetic Benchmarks                                  -/
/-! ================================================================ -/

private def benchUInt32Arith : IO Unit := do
  IO.println "UInt32 Arithmetic:"
  let data := genRandomArray numIter 1

  bench "wrappingAdd" do
    let mut acc : Radix.UInt32 := ⟨1⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := Radix.UInt32.wrappingAdd acc x
    return acc.val.toUInt64

  bench "wrappingSub" do
    let mut acc : Radix.UInt32 := ⟨4294967295⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := Radix.UInt32.wrappingSub acc x
    return acc.val.toUInt64

  bench "wrappingMul" do
    let mut acc : Radix.UInt32 := ⟨1⟩
    for v in data do
      let x : Radix.UInt32 := ⟨((v % 100) + 1).toUInt32⟩
      acc := Radix.UInt32.wrappingMul acc x
    return acc.val.toUInt64

  bench "saturatingAdd" do
    let mut acc : Radix.UInt32 := ⟨0⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := Radix.UInt32.saturatingAdd acc x
    return acc.val.toUInt64

  bench "checkedAdd" do
    let mut acc : UInt64 := 0
    for v in data do
      let a : Radix.UInt32 := ⟨(v % 100).toUInt32⟩
      let b : Radix.UInt32 := ⟨((v / 100) % 100).toUInt32⟩
      match Radix.UInt32.checkedAdd a b with
      | some r => acc := acc + r.val.toUInt64
      | none => acc := acc + 1
    return acc

/-! ================================================================ -/
/-! ## UInt64 Arithmetic Benchmarks                                  -/
/-! ================================================================ -/

private def benchUInt64Arith : IO Unit := do
  IO.println "UInt64 Arithmetic:"
  let data := genRandomArray numIter 2

  bench "wrappingAdd" do
    let mut acc : Radix.UInt64 := ⟨1⟩
    for v in data do
      let x : Radix.UInt64 := ⟨v⟩
      acc := Radix.UInt64.wrappingAdd acc x
    return acc.val

  bench "wrappingSub" do
    let mut acc : Radix.UInt64 := ⟨18446744073709551615⟩
    for v in data do
      let x : Radix.UInt64 := ⟨v⟩
      acc := Radix.UInt64.wrappingSub acc x
    return acc.val

  bench "wrappingMul" do
    let mut acc : Radix.UInt64 := ⟨1⟩
    for v in data do
      let x : Radix.UInt64 := ⟨(v % 100) + 1⟩
      acc := Radix.UInt64.wrappingMul acc x
    return acc.val

/-! ================================================================ -/
/-! ## Bitwise Operation Benchmarks                                  -/
/-! ================================================================ -/

private def benchBitwise : IO Unit := do
  IO.println "Bitwise Operations (UInt32):"
  let data := genRandomArray numIter 3

  bench "band" do
    let mut acc : Radix.UInt32 := ⟨4294967295⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := Radix.UInt32.band acc x
    return acc.val.toUInt64

  bench "bor" do
    let mut acc : Radix.UInt32 := ⟨0⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := Radix.UInt32.bor acc x
    return acc.val.toUInt64

  bench "bxor" do
    let mut acc : Radix.UInt32 := ⟨0⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := Radix.UInt32.bxor acc x
    return acc.val.toUInt64

  bench "shl" do
    let mut acc : Radix.UInt32 := ⟨1⟩
    for v in data do
      let shift : Radix.UInt32 := ⟨(v % 32).toUInt32⟩
      acc := Radix.UInt32.bxor acc (Radix.UInt32.shl ⟨v.toUInt32⟩ shift)
    return acc.val.toUInt64

  bench "popcount" do
    let mut acc : UInt64 := 0
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := acc + (Radix.UInt32.popcount x).val.toUInt64
    return acc

  bench "clz" do
    let mut acc : UInt64 := 0
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := acc + (Radix.UInt32.clz x).val.toUInt64
    return acc

  bench "rotl" do
    let mut acc : Radix.UInt32 := ⟨1⟩
    for v in data do
      let shift : Radix.UInt32 := ⟨(v % 32).toUInt32⟩
      acc := Radix.UInt32.rotl acc shift
    return acc.val.toUInt64

/-! ================================================================ -/
/-! ## Byte Order Benchmarks                                         -/
/-! ================================================================ -/

private def benchByteOrder : IO Unit := do
  IO.println "Byte Order (UInt32):"
  let data := genRandomArray numIter 4

  bench "bswap" do
    let mut acc : Radix.UInt32 := ⟨0⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := Radix.UInt32.bxor acc (Radix.UInt32.bswap x)
    return acc.val.toUInt64

  bench "toBigEndian" do
    let mut acc : Radix.UInt32 := ⟨0⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := Radix.UInt32.bxor acc (Radix.UInt32.toBigEndian x)
    return acc.val.toUInt64

  bench "toLittleEndian" do
    let mut acc : Radix.UInt32 := ⟨0⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := Radix.UInt32.bxor acc (Radix.UInt32.toLittleEndian x)
    return acc.val.toUInt64

/-! ================================================================ -/
/-! ## Conversion Benchmarks                                         -/
/-! ================================================================ -/

private def benchConversions : IO Unit := do
  IO.println "Width Conversions:"
  let data := genRandomArray numIter 5

  bench "u8→u32 zeroExtend" do
    let mut acc : UInt64 := 0
    for v in data do
      let x : Radix.UInt8 := ⟨v.toUInt8⟩
      acc := acc + (Radix.UInt8.toUInt32 x).val.toUInt64
    return acc

  bench "u32→u8 truncate" do
    let mut acc : UInt64 := 0
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := acc + (Radix.UInt32.toUInt8 x).val.toUInt64
    return acc

  bench "u32→u64 zeroExtend" do
    let mut acc : UInt64 := 0
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      acc := acc + (Radix.UInt32.toUInt64 x).val
    return acc

/-! ================================================================ -/
/-! ## LEB128 Benchmarks                                             -/
/-! ================================================================ -/

private def benchLeb128 : IO Unit := do
  IO.println "LEB128:"
  let data := genRandomArray numIter 6

  bench "encodeU32" do
    let mut buf := ⟨Array.mkEmpty (numIter * 5)⟩
    for v in data do
      let x : Radix.UInt32 := ⟨v.toUInt32⟩
      buf := Radix.Binary.Leb128.encodeU32Append x buf
    return buf.size.toUInt64

  bench "decodeU32" do
    -- Pre-encode a set of values (power of 2 for fast modulo via bitmask)
    let encodedArr := Id.run do
      let mut arr : Array ByteArray := #[]
      for i in [:1024] do
        let v := data[i]!
        let x : Radix.UInt32 := ⟨v.toUInt32⟩
        arr := arr.push (Radix.Binary.Leb128.encodeU32 x)
      return arr
    let mut acc : UInt64 := 0
    for i in [:numIter] do
      let encoded := encodedArr[i &&& 1023]!
      match Radix.Binary.Leb128.decodeU32 encoded 0 with
      | some (val, _) => acc := acc + val.val.toUInt64
      | none => acc := acc + 1
    return acc

/-! ================================================================ -/
/-! ## Signed Arithmetic Benchmarks                                  -/
/-! ================================================================ -/

private def benchSignedArith : IO Unit := do
  IO.println "Int32 Arithmetic:"
  let data := genRandomArray numIter 7

  bench "wrappingAdd" do
    let mut acc : Radix.Int32 := ⟨1⟩
    for v in data do
      let x : Radix.Int32 := ⟨v.toUInt32⟩
      acc := Radix.Int32.wrappingAdd acc x
    return acc.val.toUInt64

  bench "wrappingMul" do
    let mut acc : Radix.Int32 := ⟨1⟩
    for v in data do
      let x : Radix.Int32 := ⟨((v % 100) + 1).toUInt32⟩
      acc := Radix.Int32.wrappingMul acc x
    return acc.val.toUInt64

  bench "wrappingNeg" do
    let mut acc : Radix.Int32 := ⟨1⟩
    for v in data do
      let x : Radix.Int32 := ⟨v.toUInt32⟩
      acc := Radix.Int32.wrappingAdd acc (Radix.Int32.wrappingNeg x)
    return acc.val.toUInt64

/-! ================================================================ -/
/-! ## Main                                                          -/
/-! ================================================================ -/

def main : IO Unit := do
  IO.println "Radix Microbenchmarks (NFR-002.2)"
  IO.println s!"Iterations per benchmark: {numIter}"
  IO.println ""

  benchUInt32Arith
  IO.println ""
  benchUInt64Arith
  IO.println ""
  benchBitwise
  IO.println ""
  benchByteOrder
  IO.println ""
  benchConversions
  IO.println ""
  benchLeb128
  IO.println ""
  benchSignedArith
  IO.println ""

  IO.println "Benchmarks complete."
  IO.println ""
  IO.println "NOTE: For valid results, verify that:"
  IO.println "  1. All accumulator values are non-zero"
  IO.println "  2. build/ir/ output contains expected operations"
  IO.println "  3. Results are compared against C baseline (-O2 -fno-builtin)"
