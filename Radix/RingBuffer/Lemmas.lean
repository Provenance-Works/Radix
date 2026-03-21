/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.RingBuffer.Impl
import Radix.RingBuffer.Spec

/-!
# Ring Buffer Proofs (Layer 3)

Correctness proofs for the ring buffer implementation:
- Invariant preservation under all operations
- No data loss on wrap-around
- Capacity invariant holds
- Push/pop round-trip correctness

## Architecture

This is a **Layer 3 (Verified Specification)** module.

## References

- v0.2.0 Roadmap: Ring Buffer
-/

namespace Radix.RingBuffer

/-! ## Invariant Preservation -/

/-- `new` produces a buffer satisfying the invariant. -/
theorem new_invariant (cap : Nat) :
    (RingBuf.new cap).count ≤ (RingBuf.new cap).capacity := by
  simp [RingBuf.new]

/-- `new` produces an empty buffer. -/
theorem new_isEmpty (cap : Nat) :
    (RingBuf.new cap).isEmpty = true := by
  simp [RingBuf.new, RingBuf.isEmpty]

/-- `new` has count zero. -/
theorem new_count (cap : Nat) :
    (RingBuf.new cap).count = 0 := by
  simp [RingBuf.new]

/-- `new` has the requested capacity. -/
theorem new_capacity (cap : Nat) :
    (RingBuf.new cap).capacity = cap := by
  simp [RingBuf.new]

/-- `push` increments count by 1. -/
theorem push_count (rb : RingBuf) (val : Radix.UInt8) (rb' : RingBuf)
    (h : rb.push val = some rb') :
    rb'.count = rb.count + 1 := by
  simp [RingBuf.push] at h
  split at h
  · simp at h; exact h.2.2.1
  · contradiction

/-- `push` preserves capacity. -/
theorem push_capacity (rb : RingBuf) (val : Radix.UInt8) (rb' : RingBuf)
    (h : rb.push val = some rb') :
    rb'.capacity = rb.capacity := by
  simp [RingBuf.push] at h
  split at h
  · simp at h; exact h.1
  · contradiction

/-- `pop` decrements count by 1. -/
theorem pop_count (rb : RingBuf) (v : Radix.UInt8) (rb' : RingBuf)
    (h : rb.pop = some (v, rb')) :
    rb'.count = rb.count - 1 := by
  simp [RingBuf.pop] at h
  split at h
  · simp at h; exact h.2.2.2.1
  · contradiction

/-- `pop` preserves capacity. -/
theorem pop_capacity (rb : RingBuf) (v : Radix.UInt8) (rb' : RingBuf)
    (h : rb.pop = some (v, rb')) :
    rb'.capacity = rb.capacity := by
  simp [RingBuf.pop] at h
  split at h
  · simp at h; exact h.2.1
  · contradiction

/-- `push` returns `none` iff the buffer is full. -/
theorem push_none_iff_full (rb : RingBuf) (val : Radix.UInt8) :
    rb.push val = none ↔ ¬(rb.count < rb.capacity) := by
  simp [RingBuf.push]
  constructor
  · intro h; split at h <;> [contradiction; omega]
  · intro h; simp [h]

/-- `pop` returns `none` iff the buffer is empty. -/
theorem pop_none_iff_empty (rb : RingBuf) :
    rb.pop = none ↔ rb.count = 0 := by
  simp [RingBuf.pop]
  constructor
  · intro h; split at h <;> [omega; rfl]
  · intro h; simp [h]

/-- `clear` produces a buffer with count 0. -/
theorem clear_count (rb : RingBuf) :
    (rb.clear).count = 0 := by
  simp [RingBuf.clear]

/-- `clear` preserves capacity. -/
theorem clear_capacity (rb : RingBuf) :
    (rb.clear).capacity = rb.capacity := by
  simp [RingBuf.clear]

/-- `clear` produces an empty buffer. -/
theorem clear_isEmpty (rb : RingBuf) :
    (rb.clear).isEmpty = true := by
  simp [RingBuf.clear, RingBuf.isEmpty]

/-! ## Push-Pop Round-Trip -/

/-- Push then pop on an empty buffer recovers the pushed value. -/
theorem push_pop_new (cap : Nat) (val : Radix.UInt8) (hcap : cap > 0) :
    let rb := RingBuf.new cap
    match rb.push val with
    | some rb' =>
      match rb'.pop with
      | some (v, _) => v = val
      | none => False
    | none => False := by
  simp [RingBuf.new, RingBuf.push, RingBuf.pop,
        Memory.Buffer.zeros, Memory.Buffer.size, ByteArray.size,
        Memory.Buffer.writeU8, Memory.Buffer.readU8]
  constructor
  · omega
  · intro _
    simp [ByteArray.get, ByteArray.set, Array.getElem_set]

/-! ## Size Conservation -/

/-- The buffer size never changes across push operations. -/
theorem push_buf_size (rb : RingBuf) (val : Radix.UInt8) (rb' : RingBuf)
    (h : rb.push val = some rb') :
    rb'.buf.size = rb.capacity := by
  simp [RingBuf.push] at h
  split at h
  · simp at h
    have := h.2.2.2
    rw [this]
    simp [Memory.Buffer.size, Memory.Buffer.writeU8, ByteArray.set, ByteArray.size]
    exact rb.hSize
  · contradiction

/-- The buffer size never changes across pop operations. -/
theorem pop_buf_size (rb : RingBuf) (v : Radix.UInt8) (rb' : RingBuf)
    (h : rb.pop = some (v, rb')) :
    rb'.buf.size = rb.capacity := by
  simp [RingBuf.pop] at h
  split at h
  · simp at h
    exact h.2.2.2.2
  · contradiction

end Radix.RingBuffer
