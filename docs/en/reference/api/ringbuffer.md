# RingBuffer Module API Reference

> **Module**: `Radix.RingBuffer`
> **Source**: `Radix/RingBuffer/`

## Overview

Provides a verified fixed-capacity ring buffer (circular buffer) backed by `Memory.Buffer`. The implementation carries proof-level invariants ensuring indices stay within bounds and count tracks the actual number of elements. Supports both checked and force-overwrite push semantics, with a full spec layer proving FIFO ordering.

## Specification (`RingBuffer.Spec`)

Abstract specification modeling the ring buffer as a pure list with bounded capacity:

```lean
structure RingBufferState (α : Type) where
  contents : List α
  capacity : Nat
```

### Spec Operations

```lean
def pushSpec (s : RingBufferState α) (val : α) : Option (RingBufferState α)
def popSpec (s : RingBufferState α) : Option (α × RingBufferState α)
def peekSpec (s : RingBufferState α) : Option α
```

### Spec Properties

- **Invariant preservation**: all operations maintain `contents.length ≤ capacity`
- **FIFO ordering**: `popSpec` returns elements in the order they were pushed

## Implementation (`RingBuffer.Impl`)

### Structure

```lean
structure RingBuf where
  buf      : Memory.Buffer
  capacity : Nat
  head     : Nat
  tail     : Nat
  count    : Nat
  hCount   : count ≤ capacity
  hHead    : head < capacity
  hTail    : tail < capacity
  hSize    : buf.bytes.size = capacity
```

The structure carries four proof-carrying invariants ensuring:
- `hCount` — element count never exceeds capacity
- `hHead` — read index is valid
- `hTail` — write index is valid
- `hSize` — underlying buffer matches declared capacity

### Construction

```lean
def RingBuf.new (capacity : Nat) : RingBuf
```

Creates a zero-initialized ring buffer with the given capacity.

### Queries

```lean
def RingBuf.isEmpty (rb : RingBuf) : Bool       -- count == 0
def RingBuf.isFull (rb : RingBuf) : Bool         -- count == capacity
def RingBuf.remaining (rb : RingBuf) : Nat       -- capacity - count
```

### Single-Element Operations

```lean
def RingBuf.push (rb : RingBuf) (val : Radix.UInt8) : Option RingBuf
def RingBuf.pushForce (rb : RingBuf) (val : Radix.UInt8) : RingBuf
def RingBuf.pop (rb : RingBuf) : Option (Radix.UInt8 × RingBuf)
def RingBuf.peek (rb : RingBuf) : Option Radix.UInt8
```

- `push` returns `none` if the buffer is full.
- `pushForce` overwrites the oldest element when full, advancing `head`.
- `pop` returns `none` if the buffer is empty.
- `peek` reads the front element without removing it.

### Bulk Operations

```lean
def RingBuf.pushMany (rb : RingBuf) (data : List Radix.UInt8) : RingBuf × Nat
def RingBuf.popMany (rb : RingBuf) (n : Nat) : List Radix.UInt8 × RingBuf
def RingBuf.drain (rb : RingBuf) : List Radix.UInt8 × RingBuf
def RingBuf.clear (rb : RingBuf) : RingBuf
def RingBuf.toList (rb : RingBuf) : List Radix.UInt8
```

- `pushMany` pushes elements sequentially, returning the buffer and count of elements actually pushed.
- `popMany` pops up to `n` elements, returning them in FIFO order.
- `drain` pops all elements, equivalent to `popMany rb rb.count`.
- `clear` resets head, tail, and count to zero.
- `toList` returns the current contents in FIFO order without mutation.

## Proofs (`RingBuffer.Lemmas`)

- `new_invariant`: `RingBuf.new` satisfies all structural invariants
- `push_count`: `(rb.push val).count = rb.count + 1` (when not full)
- `pop_count`: `(rb.pop).count = rb.count - 1` (when not empty)
- `push_pop_roundtrip`: push then pop on an empty buffer yields the pushed value
- `capacity_preserved`: all operations preserve `rb.capacity`

## Examples

```lean
-- Create and use a ring buffer
let rb := RingBuf.new 4
let rb := (rb.push 0x41).get!       -- push 'A'
let rb := (rb.push 0x42).get!       -- push 'B'
let (val, rb) := rb.pop.get!        -- pop → 0x41
#eval val                             -- 65 (0x41)

-- Force-push overwrites oldest on full buffer
let rb := RingBuf.new 2
let rb := (rb.push 0x01).get!
let rb := (rb.push 0x02).get!
let rb := rb.pushForce 0x03          -- overwrites 0x01
let (val, _) := rb.pop.get!
#eval val                             -- 2 (0x02)
```

## Related Documents

- [Memory](memory.md) — Underlying buffer used by the ring buffer
- [Bytes](bytes.md) — Byte-level operations and endianness
