import Radix.Memory

/-!
# Example: Ring Buffer (Circular Queue)

A fixed-capacity circular queue built on top of `Radix.Memory.Buffer`.
Demonstrates:

- Buffer-backed data structures
- Wrapping index arithmetic
- Bounds-checked read/write
-/

namespace Examples.RingBuffer

/-- A fixed-capacity ring buffer storing bytes. -/
structure RingBuf where
  buf : Radix.Memory.Buffer
  capacity : Nat
  head : Nat  -- Index of next read position
  tail : Nat  -- Index of next write position
  count : Nat -- Number of elements currently stored

/-- Create a new ring buffer with given capacity. -/
def RingBuf.new (capacity : Nat) : RingBuf :=
  { buf := Radix.Memory.Buffer.zeros capacity
    capacity := capacity
    head := 0
    tail := 0
    count := 0 }

/-- Check if the ring buffer is empty. -/
def RingBuf.isEmpty (rb : RingBuf) : Bool := rb.count == 0

/-- Check if the ring buffer is full. -/
def RingBuf.isFull (rb : RingBuf) : Bool := rb.count == rb.capacity

/-- Push a byte onto the ring buffer. Returns none if full. -/
def RingBuf.push (rb : RingBuf) (val : Radix.UInt8) : Option RingBuf :=
  if rb.isFull then none
  else
    match Radix.Memory.Buffer.checkedWriteU8 rb.buf rb.tail val with
    | some buf' =>
      some { rb with
        buf := buf'
        tail := (rb.tail + 1) % rb.capacity
        count := rb.count + 1 }
    | none => none

/-- Pop a byte from the ring buffer. Returns none if empty. -/
def RingBuf.pop (rb : RingBuf) : Option (Radix.UInt8 × RingBuf) :=
  if rb.isEmpty then none
  else
    match Radix.Memory.Buffer.checkedReadU8 rb.buf rb.head with
    | some val =>
      some (val, { rb with
        head := (rb.head + 1) % rb.capacity
        count := rb.count - 1 })
    | none => none

/-- Peek at the front element without removing it. -/
def RingBuf.peek (rb : RingBuf) : Option Radix.UInt8 :=
  if rb.isEmpty then none
  else Radix.Memory.Buffer.checkedReadU8 rb.buf rb.head

/-- Push multiple bytes. Returns updated buffer and count of pushed items. -/
def RingBuf.pushMany (rb : RingBuf) (vals : List Radix.UInt8) : RingBuf × Nat := Id.run do
  let mut current := rb
  let mut pushed := 0
  for v in vals do
    match current.push v with
    | some rb' =>
      current := rb'
      pushed := pushed + 1
    | none => break
  return (current, pushed)

/-- Pop multiple bytes. Returns the values and updated buffer. -/
def RingBuf.popMany (rb : RingBuf) (n : Nat) : List Radix.UInt8 × RingBuf := Id.run do
  let mut current := rb
  let mut result : List Radix.UInt8 := []
  for _ in [:n] do
    match current.pop with
    | some (v, rb') =>
      result := result ++ [v]
      current := rb'
    | none => break
  return (result, current)

def run : IO Unit := do
  IO.println "=== Ring Buffer (Circular Queue) ==="
  IO.println ""

  -- Create a small ring buffer
  let mut rb := RingBuf.new 8
  IO.println s!"  Capacity: {rb.capacity}"
  IO.println s!"  Empty: {rb.isEmpty}, Full: {rb.isFull}"
  IO.println ""

  -- Push some values
  IO.println "  Pushing values: 10, 20, 30, 40, 50"
  let vals : List Radix.UInt8 := [⟨10⟩, ⟨20⟩, ⟨30⟩, ⟨40⟩, ⟨50⟩]
  let (rb', pushed) := rb.pushMany vals
  rb := rb'
  IO.println s!"  Pushed: {pushed}, Count: {rb.count}"
  IO.println ""

  -- Peek
  match rb.peek with
  | some v => IO.println s!"  Peek (front): {v.toNat}"
  | none => IO.println "  Peek: empty"

  -- Pop three values
  IO.println "  Popping 3 values:"
  let (popped, rb') := rb.popMany 3
  rb := rb'
  let poppedNats := popped.map Radix.UInt8.toNat
  IO.println s!"    Got: {poppedNats}"
  IO.println s!"    Remaining count: {rb.count}"
  IO.println ""

  -- Fill it up to demonstrate wrapping
  IO.println "  Filling to capacity (wraps around):"
  let moreVals : List Radix.UInt8 := [⟨60⟩, ⟨70⟩, ⟨80⟩, ⟨90⟩, ⟨100⟩, ⟨110⟩]
  let (rb', pushed2) := rb.pushMany moreVals
  rb := rb'
  IO.println s!"    Pushed: {pushed2} of {moreVals.length} offered"
  IO.println s!"    Count: {rb.count}, Full: {rb.isFull}"
  IO.println ""

  -- Try to push when full
  match rb.push ⟨255⟩ with
  | some _ => IO.println "  Push when full: accepted (unexpected)"
  | none => IO.println "  Push when full: rejected ✓"

  -- Drain entirely
  IO.println ""
  IO.println "  Draining all:"
  let (all, rb') := rb.popMany rb.count
  rb := rb'
  let allNats := all.map Radix.UInt8.toNat
  IO.println s!"    Values: {allNats}"
  IO.println s!"    Empty: {rb.isEmpty} ✓"
  IO.println ""

end Examples.RingBuffer
