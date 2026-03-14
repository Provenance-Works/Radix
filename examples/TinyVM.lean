import Radix.Memory
import Radix.Word.Arith
import Radix.Bit.Ops

/-!
# Example: Tiny Stack-Based Virtual Machine

A minimal stack-based VM with a compact instruction set, built using
Radix's memory buffer for program/data storage. Demonstrates:

- Buffer-backed program memory with PC-relative reads
- Wrapping arithmetic for register operations
- Bitwise operations for ALU instructions
-/

namespace Examples.TinyVM

/-! ## Instruction Set

All instructions are 1 byte opcode, with optional immediate operands.

| Opcode | Name   | Operand | Description                    |
|--------|--------|---------|--------------------------------|
| 0x01   | PUSH8  | u8      | Push 8-bit immediate           |
| 0x02   | PUSH16 | u16le   | Push 16-bit immediate          |
| 0x10   | ADD    | -       | Pop a,b; push a+b (wrapping)   |
| 0x11   | SUB    | -       | Pop a,b; push b-a (wrapping)   |
| 0x12   | MUL    | -       | Pop a,b; push a*b (wrapping)   |
| 0x20   | AND    | -       | Pop a,b; push a&b              |
| 0x21   | OR     | -       | Pop a,b; push a|b              |
| 0x22   | XOR    | -       | Pop a,b; push a^b              |
| 0x23   | NOT    | -       | Pop a; push ~a                 |
| 0x30   | DUP    | -       | Duplicate top of stack          |
| 0x31   | SWAP   | -       | Swap top two stack elements     |
| 0x32   | POP    | -       | Discard top of stack            |
| 0x40   | JMP    | u16le   | Jump to address                 |
| 0x41   | JZ     | u16le   | Jump if top == 0 (pops)        |
| 0x50   | PRINT  | -       | Pop and print top of stack      |
| 0xFF   | HALT   | -       | Stop execution                  |
-/

/-- VM state. -/
structure VM where
  program : Radix.Memory.Buffer  -- Program memory
  pc : Nat                        -- Program counter
  stack : Array Nat               -- Operand stack
  halted : Bool
  output : List Nat               -- Collected output values

namespace VM

/-- Create a VM loaded with a program. -/
def load (prog : ByteArray) : VM :=
  { program := Radix.Memory.Buffer.ofByteArray prog
    pc := 0
    stack := #[]
    halted := false
    output := [] }

/-- Read a byte from program memory at current PC and advance. -/
def fetchByte (vm : VM) : Option (Nat × VM) :=
  match Radix.Memory.Buffer.checkedReadU8 vm.program vm.pc with
  | some v => some (v.toNat, { vm with pc := vm.pc + 1 })
  | none => none

/-- Read a 16-bit LE value from program memory and advance PC by 2. -/
def fetchU16LE (vm : VM) : Option (Nat × VM) :=
  match Radix.Memory.Buffer.checkedReadU8 vm.program vm.pc,
        Radix.Memory.Buffer.checkedReadU8 vm.program (vm.pc + 1) with
  | some lo, some hi =>
    let val := lo.toNat + hi.toNat * 256
    some (val, { vm with pc := vm.pc + 2 })
  | _, _ => none

/-- Push a value onto the stack. -/
def push (vm : VM) (val : Nat) : VM :=
  { vm with stack := vm.stack.push val }

/-- Pop the top value from the stack. -/
def pop (vm : VM) : Option (Nat × VM) :=
  if vm.stack.isEmpty then none
  else
    let val := vm.stack.back!
    some (val, { vm with stack := vm.stack.pop })

/-- Execute one instruction. Returns the updated VM or none on error. -/
def step (vm : VM) : Option VM := do
  if vm.halted then return vm
  let (opcode, vm) ← vm.fetchByte
  match opcode with
  -- PUSH8
  | 0x01 =>
    let (val, vm) ← vm.fetchByte
    return vm.push val
  -- PUSH16
  | 0x02 =>
    let (val, vm) ← vm.fetchU16LE
    return vm.push val
  -- ADD
  | 0x10 =>
    let (a, vm) ← vm.pop
    let (b, vm) ← vm.pop
    let r := Radix.UInt32.wrappingAdd ⟨(b.toUInt32)⟩ ⟨(a.toUInt32)⟩
    return vm.push r.toNat
  -- SUB
  | 0x11 =>
    let (a, vm) ← vm.pop
    let (b, vm) ← vm.pop
    let r := Radix.UInt32.wrappingSub ⟨(b.toUInt32)⟩ ⟨(a.toUInt32)⟩
    return vm.push r.toNat
  -- MUL
  | 0x12 =>
    let (a, vm) ← vm.pop
    let (b, vm) ← vm.pop
    let r := Radix.UInt32.wrappingMul ⟨(b.toUInt32)⟩ ⟨(a.toUInt32)⟩
    return vm.push r.toNat
  -- AND
  | 0x20 =>
    let (a, vm) ← vm.pop
    let (b, vm) ← vm.pop
    let r := Radix.UInt32.band ⟨(b.toUInt32)⟩ ⟨(a.toUInt32)⟩
    return vm.push r.toNat
  -- OR
  | 0x21 =>
    let (a, vm) ← vm.pop
    let (b, vm) ← vm.pop
    let r := Radix.UInt32.bor ⟨(b.toUInt32)⟩ ⟨(a.toUInt32)⟩
    return vm.push r.toNat
  -- XOR
  | 0x22 =>
    let (a, vm) ← vm.pop
    let (b, vm) ← vm.pop
    let r := Radix.UInt32.bxor ⟨(b.toUInt32)⟩ ⟨(a.toUInt32)⟩
    return vm.push r.toNat
  -- NOT
  | 0x23 =>
    let (a, vm) ← vm.pop
    let r := Radix.UInt32.bnot ⟨(a.toUInt32)⟩
    return vm.push r.toNat
  -- DUP
  | 0x30 =>
    let (a, vm) ← vm.pop
    return (vm.push a).push a
  -- SWAP
  | 0x31 =>
    let (a, vm) ← vm.pop
    let (b, vm) ← vm.pop
    return (vm.push a).push b
  -- POP
  | 0x32 =>
    let (_, vm) ← vm.pop
    return vm
  -- JMP
  | 0x40 =>
    let (addr, vm) ← vm.fetchU16LE
    return { vm with pc := addr }
  -- JZ (jump if zero)
  | 0x41 =>
    let (addr, vm) ← vm.fetchU16LE
    let (val, vm) ← vm.pop
    if val == 0 then return { vm with pc := addr }
    else return vm
  -- PRINT
  | 0x50 =>
    let (val, vm) ← vm.pop
    return { vm with output := vm.output ++ [val] }
  -- HALT
  | 0xFF => return { vm with halted := true }
  | _ => none  -- Unknown opcode

/-- Run the VM until halted or error, with a step limit. -/
def run (vm : VM) (maxSteps : Nat := 10000) : VM := Id.run do
  let mut current := vm
  for _ in [:maxSteps] do
    if current.halted then break
    match current.step with
    | some vm' => current := vm'
    | none => break
  return current

end VM

/-! ## Helper: Assemble simple programs -/

/-- Assemble a program from instruction mnemonics. -/
private def assemble (instrs : List (List Nat)) : ByteArray :=
  let bytes := instrs.flatten
  ByteArray.mk (bytes.toArray.map fun n => n.toUInt8)

def run : IO Unit := do
  IO.println "=== Tiny Stack VM ==="
  IO.println ""

  -- Program 1: (2 + 3) * 4 = 20
  IO.println "  1. Arithmetic: (2 + 3) * 4"
  IO.println "  ---"
  let prog1 := assemble [
    [0x01, 2],     -- PUSH8 2
    [0x01, 3],     -- PUSH8 3
    [0x10],        -- ADD        -> 5
    [0x01, 4],     -- PUSH8 4
    [0x12],        -- MUL        -> 20
    [0x50],        -- PRINT
    [0xFF]         -- HALT
  ]
  let vm1 := VM.run (VM.load prog1)
  IO.println s!"    Output: {vm1.output}"
  if vm1.output != [20] then throw (IO.userError "expected [20]")
  IO.println "    ✓ Correct"
  IO.println ""

  -- Program 2: Bitwise AND (0xFF & 0x0F = 0x0F = 15)
  IO.println "  2. Bitwise: 0xFF AND 0x0F"
  IO.println "  ---"
  let prog2 := assemble [
    [0x01, 0xFF],  -- PUSH8 255
    [0x01, 0x0F],  -- PUSH8 15
    [0x20],        -- AND       -> 15
    [0x50],        -- PRINT
    [0xFF]         -- HALT
  ]
  let vm2 := VM.run (VM.load prog2)
  IO.println s!"    Output: {vm2.output}"
  if vm2.output != [15] then throw (IO.userError "expected [15]")
  IO.println "    ✓ Correct"
  IO.println ""

  -- Program 3: DUP and MUL (square of 7)
  IO.println "  3. Stack: 7 squared"
  IO.println "  ---"
  let prog3 := assemble [
    [0x01, 7],     -- PUSH8 7
    [0x30],        -- DUP        -> 7, 7
    [0x12],        -- MUL        -> 49
    [0x50],        -- PRINT
    [0xFF]         -- HALT
  ]
  let vm3 := VM.run (VM.load prog3)
  IO.println s!"    Output: {vm3.output}"
  if vm3.output != [49] then throw (IO.userError "expected [49]")
  IO.println "    ✓ Correct"
  IO.println ""

  -- Program 4: 16-bit push (300 + 700 = 1000)
  IO.println "  4. 16-bit: 300 + 700"
  IO.println "  ---"
  let prog4 := assemble [
    [0x02, 0x2C, 0x01],  -- PUSH16 300 (0x012C LE)
    [0x02, 0xBC, 0x02],  -- PUSH16 700 (0x02BC LE)
    [0x10],               -- ADD -> 1000
    [0x50],               -- PRINT
    [0xFF]                -- HALT
  ]
  let vm4 := VM.run (VM.load prog4)
  IO.println s!"    Output: {vm4.output}"
  if vm4.output != [1000] then throw (IO.userError "expected [1000]")
  IO.println "    ✓ Correct"
  IO.println ""

  -- Program 5: Conditional jump (if 0 then print 1 else print 2)
  IO.println "  5. Control flow: JZ"
  IO.println "  ---"
  let prog5 := assemble [
    [0x01, 0],            -- PUSH8 0 (condition: zero)
    [0x41, 0x09, 0x00],  -- JZ -> addr 9
    [0x01, 99],           -- PUSH8 99 (not taken)
    [0x50],               -- PRINT
    [0xFF],               -- HALT
    -- addr 7:
    [0x01, 42],           -- PUSH8 42 (taken)
    [0x50],               -- PRINT
    [0xFF]                -- HALT
  ]
  let vm5 := VM.run (VM.load prog5)
  IO.println s!"    Output: {vm5.output}"
  if vm5.output != [42] then throw (IO.userError "expected [42]")
  IO.println "    ✓ Correct (jumped to print 42)"
  IO.println ""

  -- Program 6: Wrapping overflow (255 + 1 in u32 = 256, not overflow)
  IO.println "  6. Wrapping arithmetic"
  IO.println "  ---"
  let prog6 := assemble [
    [0x02, 0xFF, 0xFF],  -- PUSH16 65535
    [0x01, 1],            -- PUSH8 1
    [0x10],               -- ADD (wrapping u32: 65536)
    [0x50],               -- PRINT
    [0xFF]                -- HALT
  ]
  let vm6 := VM.run (VM.load prog6)
  IO.println s!"    Output: {vm6.output}"
  IO.println s!"    65535 + 1 = {vm6.output.head!} (u32 wrapping)"
  IO.println ""

  -- Summary
  IO.println "  VM instruction set: 16 opcodes"
  IO.println "  All programs executed successfully ✓"
  IO.println ""

end Examples.TinyVM
