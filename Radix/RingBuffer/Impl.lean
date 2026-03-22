/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.Memory.Model
import Radix.RingBuffer.Spec

/-!
# Ring Buffer Implementation (Layer 2)

A verified fixed-capacity circular queue backed by `Radix.Memory.Buffer`.
All access is bounds-checked. Index arithmetic wraps at capacity.

## Architecture

This is a **Layer 2 (Verified Implementation)** module.
- Imports `Memory.Buffer` for backing storage.
- Imports `RingBuffer.Spec` for specification reference.

## Key Invariants (maintained by all operations)

1. `count ≤ capacity`
2. `head < capacity` (when `capacity > 0`)
3. `tail < capacity` (when `capacity > 0`)
4. `tail = (head + count) % capacity` (when `capacity > 0`)
5. Buffer size equals capacity

## References

- v0.2.0 Roadmap: Ring Buffer
- FR-004: Memory Safety
-/

namespace Radix.RingBuffer

/-- A fixed-capacity ring buffer storing bytes, backed by `Memory.Buffer`.
    The buffer uses `head` as the read index and `tail` as the write index,
    wrapping around at `capacity`. -/
structure RingBuf where
  /-- Backing memory buffer. -/
  buf : Memory.Buffer
  /-- Maximum number of elements. -/
  capacity : Nat
  /-- Index of the next element to read (oldest element). -/
  head : Nat
  /-- Index of the next write position. -/
  tail : Nat
  /-- Number of elements currently stored. -/
  count : Nat
  /-- Invariant: count never exceeds capacity. -/
  hCount : count ≤ capacity
  /-- Invariant: head is within bounds (or capacity is 0). -/
  hHead : capacity > 0 → head < capacity
  /-- Invariant: tail is within bounds (or capacity is 0). -/
  hTail : capacity > 0 → tail < capacity
  /-- Invariant: buffer size matches capacity. -/
  hSize : buf.size = capacity

namespace RingBuf

@[inline] private def wrapSuccFast (idx capacity : Nat) : Nat :=
  let next := idx + 1
  if next = capacity then 0 else next

private theorem wrapSuccFast_lt {idx capacity : Nat}
    (hcap : capacity > 0) (hidx : idx < capacity) :
    wrapSuccFast idx capacity < capacity := by
  simp [wrapSuccFast]
  by_cases hEq : idx + 1 = capacity
  · simp [hEq, hcap]
  · simp [hEq]
    omega

@[inline] private def pushFast (rb : RingBuf) (val : Radix.UInt8) : Option RingBuf :=
  if h : rb.count < rb.capacity then
    have hcap : rb.capacity > 0 := by omega
    have htail_valid : rb.tail < rb.buf.bytes.size := by
      have h1 := rb.hSize; simp [Memory.Buffer.size] at h1
      have h2 := rb.hTail hcap; omega
    let buf' := rb.buf.writeU8 rb.tail val htail_valid
    let newTail := wrapSuccFast rb.tail rb.capacity
    some {
      buf := buf'
      capacity := rb.capacity
      head := rb.head
      tail := newTail
      count := rb.count + 1
      hCount := by omega
      hHead := rb.hHead
      hTail := by
        intro hcap'
        simpa [newTail] using wrapSuccFast_lt hcap' (rb.hTail hcap')
      hSize := by
        show (Memory.Buffer.writeU8 rb.buf rb.tail val htail_valid).size = rb.capacity
        unfold Memory.Buffer.writeU8 Memory.Buffer.size
        rw [Memory.Buffer.set_size_eq]
        exact rb.hSize
    }
  else
    none

@[inline] private def popFast (rb : RingBuf) : Option (Radix.UInt8 × RingBuf) :=
  if h : rb.count > 0 then
    have hcap : rb.capacity > 0 := by have := rb.hCount; omega
    have hhead_valid : rb.head < rb.buf.bytes.size := by
      have h1 := rb.hSize; simp [Memory.Buffer.size] at h1
      have h2 := rb.hHead hcap; omega
    let val := rb.buf.readU8 rb.head hhead_valid
    let newHead := wrapSuccFast rb.head rb.capacity
    some (val, {
      buf := rb.buf
      capacity := rb.capacity
      head := newHead
      tail := rb.tail
      count := rb.count - 1
      hCount := by have := rb.hCount; omega
      hHead := by
        intro hcap'
        simpa [newHead] using wrapSuccFast_lt hcap' (rb.hHead hcap')
      hTail := rb.hTail
      hSize := rb.hSize
    })
  else
    none

/-! ## Construction -/

/-- Create a new ring buffer with the given capacity, initialized to zeros. -/
def new (capacity : Nat) : RingBuf :=
  { buf := Memory.Buffer.zeros capacity
    capacity := capacity
    head := 0
    tail := 0
    count := 0
    hCount := Nat.zero_le _
    hHead := fun h => h
    hTail := fun h => h
    hSize := by simp [Memory.Buffer.zeros, Memory.Buffer.size, ByteArray.size] }

/-! ## Queries -/

/-- Check if the ring buffer is empty. -/
@[inline] def isEmpty (rb : RingBuf) : Bool := rb.count == 0

/-- Check if the ring buffer is full. -/
@[inline] def isFull (rb : RingBuf) : Bool := rb.count == rb.capacity

/-- Remaining free capacity. -/
@[inline] def remaining (rb : RingBuf) : Nat := rb.capacity - rb.count

/-! ## Push (Enqueue) -/

/-- Push a byte onto the tail of the ring buffer.
    Returns `none` if the buffer is full. -/
@[implemented_by pushFast] def push (rb : RingBuf) (val : Radix.UInt8) : Option RingBuf :=
  if h : rb.count < rb.capacity then
    -- tail is valid because count < capacity
    have hcap : rb.capacity > 0 := by omega
    have htail_valid : rb.tail < rb.buf.bytes.size := by
      have h1 := rb.hSize; simp [Memory.Buffer.size] at h1
      have h2 := rb.hTail hcap; omega
    let buf' := rb.buf.writeU8 rb.tail val htail_valid
    let newTail := (rb.tail + 1) % rb.capacity
    some {
      buf := buf'
      capacity := rb.capacity
      head := rb.head
      tail := newTail
      count := rb.count + 1
      hCount := by omega
      hHead := rb.hHead
      hTail := fun hcap => Nat.mod_lt _ hcap
      hSize := by
        show (Memory.Buffer.writeU8 rb.buf rb.tail val htail_valid).size = rb.capacity
        unfold Memory.Buffer.writeU8 Memory.Buffer.size
        rw [Memory.Buffer.set_size_eq]
        exact rb.hSize
    }
  else none

/-- Push a byte, silently dropping the oldest element if full (overwrite mode). -/
def pushForce (rb : RingBuf) (val : Radix.UInt8) : RingBuf :=
  if rb.count < rb.capacity then
    match rb.push val with
    | some rb' => rb'
    | none => rb  -- unreachable: count < capacity implies push succeeds
  else
    if hcap : rb.capacity > 0 then
      -- Overwrite oldest: advance head, then write at tail
      have htail_valid : rb.tail < rb.buf.bytes.size := by
        have h1 := rb.hSize; simp [Memory.Buffer.size] at h1
        have h2 := rb.hTail hcap; omega
      let buf' := rb.buf.writeU8 rb.tail val htail_valid
      let newTail := (rb.tail + 1) % rb.capacity
      let newHead := (rb.head + 1) % rb.capacity
      { buf := buf'
        capacity := rb.capacity
        head := newHead
        tail := newTail
        count := rb.count
        hCount := rb.hCount
        hHead := fun hcap => Nat.mod_lt _ hcap
        hTail := fun hcap => Nat.mod_lt _ hcap
        hSize := by
          show (Memory.Buffer.writeU8 rb.buf rb.tail val htail_valid).size = rb.capacity
          unfold Memory.Buffer.writeU8 Memory.Buffer.size
          rw [Memory.Buffer.set_size_eq]
          exact rb.hSize }
    else rb  -- capacity = 0: no-op

/-! ## Pop (Dequeue) -/

/-- Pop a byte from the head of the ring buffer.
    Returns `none` if the buffer is empty. -/
@[implemented_by popFast] def pop (rb : RingBuf) : Option (Radix.UInt8 × RingBuf) :=
  if h : rb.count > 0 then
    have hcap : rb.capacity > 0 := by have := rb.hCount; omega
    have hhead_valid : rb.head < rb.buf.bytes.size := by
      have h1 := rb.hSize; simp [Memory.Buffer.size] at h1
      have h2 := rb.hHead hcap; omega
    let val := rb.buf.readU8 rb.head hhead_valid
    let newHead := (rb.head + 1) % rb.capacity
    some (val, {
      buf := rb.buf
      capacity := rb.capacity
      head := newHead
      tail := rb.tail
      count := rb.count - 1
      hCount := by have := rb.hCount; omega
      hHead := fun hcap => Nat.mod_lt _ hcap
      hTail := rb.hTail
      hSize := rb.hSize
    })
  else none

/-! ## Peek -/

/-- Peek at the front element without removing it. -/
def peek (rb : RingBuf) : Option Radix.UInt8 :=
  if h : rb.count > 0 then
    have hcap : rb.capacity > 0 := by have := rb.hCount; omega
    have hhead_valid : rb.head < rb.buf.bytes.size := by
      have h1 := rb.hSize; simp [Memory.Buffer.size] at h1
      have h2 := rb.hHead hcap; omega
    some (rb.buf.readU8 rb.head hhead_valid)
  else none

/-! ## Bulk Operations -/

/-- Push multiple bytes. Returns the updated buffer and count of bytes pushed. -/
def pushMany (rb : RingBuf) (vals : List Radix.UInt8) : RingBuf × Nat :=
  go rb vals 0
where
  go (rb : RingBuf) : List Radix.UInt8 → Nat → RingBuf × Nat
    | [], pushed => (rb, pushed)
    | v :: vs, pushed =>
      match rb.push v with
      | some rb' => go rb' vs (pushed + 1)
      | none => (rb, pushed)

/-- Pop multiple bytes. Returns the values and updated buffer. -/
def popMany (rb : RingBuf) (n : Nat) : List Radix.UInt8 × RingBuf :=
  go rb n []
where
  go (rb : RingBuf) : Nat → List Radix.UInt8 → List Radix.UInt8 × RingBuf
    | 0, acc => (acc, rb)
    | n + 1, acc =>
      match rb.pop with
      | some (v, rb') => go rb' n (acc ++ [v])
      | none => (acc, rb)

/-- Drain all elements from the buffer. -/
def drain (rb : RingBuf) : List Radix.UInt8 × RingBuf :=
  rb.popMany rb.count

/-- Clear the ring buffer (reset to empty, keeping capacity). -/
def clear (rb : RingBuf) : RingBuf :=
  { rb with
    head := 0
    tail := 0
    count := 0
    hCount := Nat.zero_le _
    hHead := fun h => h
    hTail := fun h => h }

/-- Convert the logical contents to a list (oldest first). -/
def toList (rb : RingBuf) : List Radix.UInt8 :=
  (rb.drain).1

end RingBuf
end Radix.RingBuffer
