import Radix.Bit.Field
import Radix.Bit.Scan
import Radix.Bit.Ops

/-!
# Example: Bit Flags & Hardware Registers

Demonstrates bit-level manipulation of flags and hardware registers:

- Unix file permission bits
- Hardware status register with packed fields
- Bit field extraction and insertion
-/

namespace Examples.BitFlags

/-! ## 1. Unix File Permissions

Standard Unix permission model: rwxrwxrwx (owner/group/other). -/

/-- Permission flag constants. -/
private def ownerRead  : Nat := 8  -- bit 8
private def ownerWrite : Nat := 7  -- bit 7
private def ownerExec  : Nat := 6  -- bit 6
private def groupRead  : Nat := 5  -- bit 5
private def groupWrite : Nat := 4  -- bit 4
private def groupExec  : Nat := 3  -- bit 3
private def otherRead  : Nat := 2  -- bit 2
private def otherWrite : Nat := 1  -- bit 1
private def otherExec  : Nat := 0  -- bit 0

/-- Create permissions from an octal value like 0o755. -/
private def permsFromOctal (octal : Nat) : Radix.UInt32 :=
  ⟨octal.toUInt32⟩

/-- Format permissions in ls-style string. -/
private def permsToString (p : Radix.UInt32) : String :=
  let r (bit : Nat) := if Radix.UInt32.testBit p bit then "r" else "-"
  let w (bit : Nat) := if Radix.UInt32.testBit p bit then "w" else "-"
  let x (bit : Nat) := if Radix.UInt32.testBit p bit then "x" else "-"
  r ownerRead ++ w ownerWrite ++ x ownerExec ++
  r groupRead ++ w groupWrite ++ x groupExec ++
  r otherRead ++ w otherWrite ++ x otherExec

/-! ## 2. Hardware Status Register

Packed 32-bit register with named fields:
- [1:0]   state    (2 bits: 0=idle, 1=running, 2=error, 3=done)
- [5:2]   errorCode (4 bits)
- [6]     irqPending
- [7]     enabled
- [15:8]  counter  (8 bits)
- [31:16] reserved -/

private def stateField : Nat × Nat := (0, 2)        -- bits [1:0]
private def errorField : Nat × Nat := (2, 6)        -- bits [5:2]
private def irqBit : Nat := 6
private def enabledBit : Nat := 7
private def counterField : Nat × Nat := (8, 16)     -- bits [15:8]

private def stateName (s : Nat) : String :=
  match s with
  | 0 => "IDLE"
  | 1 => "RUNNING"
  | 2 => "ERROR"
  | 3 => "DONE"
  | _ => "UNKNOWN"

def run : IO Unit := do
  IO.println "=== Bit Flags & Hardware Registers ==="
  IO.println ""

  -- Unix permissions demo
  IO.println "  1. Unix File Permissions"
  IO.println "  ---"

  let perm755 := permsFromOctal 0o755
  IO.println s!"    0755 = {permsToString perm755}"

  let perm644 := permsFromOctal 0o644
  IO.println s!"    0644 = {permsToString perm644}"

  let perm777 := permsFromOctal 0o777
  IO.println s!"    0777 = {permsToString perm777}"

  -- Union (OR) and intersect (AND)
  let combined := Radix.UInt32.bor perm755 perm644
  IO.println s!"    0755 | 0644 = {permsToString combined}"

  let common := Radix.UInt32.band perm755 perm644
  IO.println s!"    0755 & 0644 = {permsToString common}"

  -- Apply umask: remove bits that umask sets
  let umask := permsFromOctal 0o022
  let masked := Radix.UInt32.band perm777 (Radix.UInt32.bnot umask)
  IO.println s!"    0777 & ~0022 = {permsToString masked} (umask applied)"

  -- Count permission bits set
  IO.println s!"    Bits set in 0755: {(Radix.UInt32.popcount perm755).toNat}"
  IO.println ""

  -- Hardware register demo
  IO.println "  2. Hardware Status Register"
  IO.println "  ---"

  -- Start with a zeroed register
  let mut reg : Radix.UInt32 := ⟨0⟩

  -- Enable the device (set bit 7)
  reg := Radix.UInt32.setBit reg enabledBit
  IO.println s!"    After enable: 0x{String.ofList (Nat.toDigits 16 reg.toNat)}"

  -- Set state to RUNNING (1)
  reg := Radix.UInt32.insertBits reg (⟨1⟩ : Radix.UInt32) 0 2 ⟨by omega, by omega⟩
  IO.println s!"    After set RUNNING: 0x{String.ofList (Nat.toDigits 16 reg.toNat)}"

  -- Set counter to 42
  reg := Radix.UInt32.insertBits reg (⟨42⟩ : Radix.UInt32) 8 16 ⟨by omega, by omega⟩
  IO.println s!"    After set counter=42: 0x{String.ofList (Nat.toDigits 16 reg.toNat)}"

  -- Read back fields
  let state := (Radix.UInt32.extractBits reg 0 2 ⟨by omega, by omega⟩).toNat
  let counter := (Radix.UInt32.extractBits reg 8 16 ⟨by omega, by omega⟩).toNat
  let enabled := Radix.UInt32.testBit reg enabledBit
  let irq := Radix.UInt32.testBit reg irqBit
  IO.println ""
  IO.println "    Register readback:"
  IO.println s!"      State: {stateName state} ({state})"
  IO.println s!"      Counter: {counter}"
  IO.println s!"      Enabled: {enabled}"
  IO.println s!"      IRQ Pending: {irq}"

  -- Simulate an error: set state=ERROR(2), errorCode=5, irqPending
  reg := Radix.UInt32.insertBits reg (⟨2⟩ : Radix.UInt32) 0 2 ⟨by omega, by omega⟩
  reg := Radix.UInt32.insertBits reg (⟨5⟩ : Radix.UInt32) 2 6 ⟨by omega, by omega⟩
  reg := Radix.UInt32.setBit reg irqBit

  let state2 := (Radix.UInt32.extractBits reg 0 2 ⟨by omega, by omega⟩).toNat
  let errCode := (Radix.UInt32.extractBits reg 2 6 ⟨by omega, by omega⟩).toNat
  let irq2 := Radix.UInt32.testBit reg irqBit
  IO.println ""
  IO.println "    After error event:"
  IO.println s!"      State: {stateName state2}"
  IO.println s!"      Error code: {errCode}"
  IO.println s!"      IRQ Pending: {irq2}"

  -- Toggle IRQ to acknowledge
  reg := Radix.UInt32.toggleBit reg irqBit
  IO.println s!"      After IRQ ack: IRQ={Radix.UInt32.testBit reg irqBit}"

  IO.println ""

end Examples.BitFlags
