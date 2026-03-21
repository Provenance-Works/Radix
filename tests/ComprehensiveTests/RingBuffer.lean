import tests.ComprehensiveTests.Framework
import Radix.RingBuffer

/-!
# Ring Buffer Tests
## Spec References
- v0.2.0: Lock-free-ready ring buffer with push/pop/peek
-/

open ComprehensiveTests
open Radix.RingBuffer

def runRingBufferTests : IO Nat := do
  let c ← IO.mkRef 0
  let assert := mkAssert c
  IO.println "    Ring buffer tests..."

  -- ## Construction
  let rb := RingBuf.new 8
  assert (rb.capacity == 8) "new capacity"
  assert (rb.count == 0) "new count"
  assert (rb.isEmpty) "new isEmpty"
  assert (!rb.isFull) "new not isFull"

  -- ## Push/Pop round-trip
  match rb.push ⟨42⟩ with
  | none => assert false "push to empty should succeed"
  | some rb1 =>
    assert (rb1.count == 1) "push count 1"
    assert (!rb1.isEmpty) "push not isEmpty"
    match rb1.peek with
    | none => assert false "peek after push should succeed"
    | some v => assert (v.toNat == 42) "peek value"
    match rb1.pop with
    | none => assert false "pop after push should succeed"
    | some (v, rb2) =>
      assert (v.toNat == 42) "pop value"
      assert (rb2.count == 0) "pop count back to 0"
      assert (rb2.isEmpty) "pop back to isEmpty"

  -- ## Fill to capacity
  let mut rbFill := RingBuf.new 4
  for i in [:4] do
    match rbFill.push ⟨i.toUInt8⟩ with
    | none => assert false s!"push [{i}] to buffer should succeed"
    | some rb' => rbFill := rb'
  assert (rbFill.count == 4) "filled count"
  assert (rbFill.isFull) "filled isFull"

  -- Push when full should fail
  assert (rbFill.push ⟨99⟩ |>.isNone) "push to full returns none"

  -- Pop all in FIFO order
  for i in [:4] do
    match rbFill.pop with
    | none => assert false s!"pop [{i}] should succeed"
    | some (v, rb') =>
      assert (v.toNat == i) s!"FIFO order: pop [{i}] = {i}"
      rbFill := rb'
  assert (rbFill.isEmpty) "empty after draining"

  -- Pop from empty should fail
  assert (rbFill.pop |>.isNone) "pop from empty returns none"

  -- ## pushForce (overwrite mode)
  let mut rbForce := RingBuf.new 3
  for i in [:3] do
    match rbForce.push ⟨i.toUInt8⟩ with
    | some rb' => rbForce := rb'
    | none => assert false s!"initial push [{i}] failed"
  -- Force push when full: overwrites oldest
  let rbForce2 := rbForce.pushForce ⟨10⟩
  assert (rbForce2.count == 3) "pushForce preserves count"

  -- ## pushMany / popMany
  let mut rbBulk := RingBuf.new 16
  let data : List Radix.UInt8 := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩]
  rbBulk := (rbBulk.pushMany data).1
  assert (rbBulk.count == 5) "pushMany count"

  let (popped, rbBulk') := rbBulk.popMany 3
  assert (popped.length == 3) "popMany 3 length"
  assert (rbBulk'.count == 2) "popMany remaining count"
  -- FIFO: first 3 should be 1,2,3
  match popped with
  | [a, b, c'] =>
    assert (a.toNat == 1) "popMany[0]"
    assert (b.toNat == 2) "popMany[1]"
    assert (c'.toNat == 3) "popMany[2]"
  | _ => assert false "popMany unexpected length"

  -- ## clear
  let rbClear := rbBulk'.clear
  assert (rbClear.count == 0) "clear count"
  assert (rbClear.isEmpty) "clear isEmpty"
  assert (rbClear.capacity == 16) "clear preserves capacity"

  -- ## drain
  let mut rbDrain := RingBuf.new 4
  rbDrain := (rbDrain.pushMany [⟨10⟩, ⟨20⟩, ⟨30⟩]).1
  let (all, rbDrained) := rbDrain.drain
  assert (all.length == 3) "drain length"
  assert (rbDrained.isEmpty) "drain empty"

  -- ## toList
  let mut rbList := RingBuf.new 4
  rbList := (rbList.pushMany [⟨7⟩, ⟨8⟩, ⟨9⟩]).1
  let lst := rbList.toList
  assert (lst.length == 3) "toList length"

  -- ## Zero capacity
  let rbZero := RingBuf.new 0
  assert (rbZero.capacity == 0) "zero cap capacity"
  assert (rbZero.isFull) "zero cap isFull"
  assert (rbZero.push ⟨1⟩ |>.isNone) "zero cap push fails"

  c.get
