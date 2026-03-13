# Concurrency Module API Reference

> **Module**: `Radix.Concurrency`
> **Source**: `Radix/Concurrency/`

## Overview

Models concurrent atomic operations following the C11/C++11 memory model. This is a **pure model** — no actual hardware interaction. All operations are modeled as state transitions on abstract atomic cells.

## Memory Ordering (`Concurrency.Spec`)

```lean
inductive MemoryOrder where
  | relaxed  -- No inter-thread ordering guarantees
  | acquire  -- Subsequent reads/writes cannot move before this load
  | release  -- Previous reads/writes cannot move after this store
  | acqRel   -- Both acquire and release (for RMW operations)
  | seqCst   -- Total global ordering across all threads

def MemoryOrder.strength : MemoryOrder → Nat
def MemoryOrder.isAtLeast (a b : MemoryOrder) : Bool
```

## Atomic Cell (`Concurrency.Atomic`)

```lean
structure AtomicCell where
  val : Nat

def AtomicCell.new (v : Nat) : AtomicCell

-- Operations return results + new cell state
def atomicLoad (cell : AtomicCell) (order : MemoryOrder) : LoadResult × AtomicCell
def atomicStore (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : StoreResult × AtomicCell
def atomicCAS (cell : AtomicCell) (expected new_ : Nat) (succ fail : MemoryOrder) : CASResult × AtomicCell
def atomicExchange (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell

-- Fetch-and-modify
def fetchAdd (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
def fetchSub (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
def fetchAnd (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
def fetchOr  (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
def fetchXor (cell : AtomicCell) (val : Nat) (order : MemoryOrder) : FetchResult × AtomicCell
```

## Ordering Utilities (`Concurrency.Ordering`)

```lean
def strengthen (order : MemoryOrder) : MemoryOrder
def combineLoadStore (load store : MemoryOrder) : MemoryOrder
def hasAcquireSemantics (order : MemoryOrder) : Bool
def hasReleaseSemantics (order : MemoryOrder) : Bool
def validOrderForAccess (kind : AccessKind) (order : MemoryOrder) : Bool
```

## Proofs (`Concurrency.Lemmas`)

- Ordering strength proofs and transitivity
- CAS success/failure behavior
- Fetch operation correctness
- Store-load round-trip
- `programOrder` transitivity
- Single-thread linearizability
- Empty/singleton trace data-race freedom

## Trusted Assumptions (`Concurrency.Assumptions`)

| Axiom | Asserts |
|-------|---------|
| `trust_atomic_word_access` | Word-sized atomic operations are indivisible |
| `trust_cas_atomicity` | CAS is atomic (compare + swap in one step) |
| `trust_seqcst_total_order` | SeqCst operations have a total global order |
| `trust_acquire_release_sync` | Acquire/Release pairs synchronize threads |
| `trust_fence_ordering` | Fence instructions enforce memory ordering |

## Related Documents

- [BareMetal](baremetal.md) — Bare metal support (no OS)
- [Architecture: Components](../../en/architecture/components.md#concurrency) — Module overview
