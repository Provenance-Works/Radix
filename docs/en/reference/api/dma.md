# DMA Module API Reference

> **Module**: `Radix.DMA`
> **Source**: `Radix/DMA/`

## Overview

Models DMA transfers as relations between source and destination memory regions, parameterized by memory ordering, cache coherence, and transfer atomicity. The executable layer can validate descriptors and simulate their copy behavior over `ByteArray` buffers.

## Specification (`DMA.Spec`)

```lean
inductive Coherence where
  | coherent
  | nonCoherent

inductive Atomicity where
  | whole
  | burst (bytes : Nat)

structure Descriptor where
  source : Radix.Memory.Spec.Region
  destination : Radix.Memory.Spec.Region
  order : Radix.Concurrency.Spec.MemoryOrder
  coherence : Coherence
  atomicity : Atomicity

def fenceOrderSufficient (d : Descriptor) : Prop
def atomicityValid (d : Descriptor) : Prop
def Descriptor.valid (d : Descriptor) : Prop
def Descriptor.bytesMoved (d : Descriptor) : Nat
def Descriptor.stepCount (d : Descriptor) : Nat
```

### Validity Rules

- Source and destination regions must have equal positive sizes.
- Burst atomicity must use a positive chunk size no larger than the region size.
- Non-coherent transfers require `seqCst` ordering.

The executable simulator interprets source and destination offsets relative to
separate buffers, so overlap between the two region descriptors is allowed.

## Operations (`DMA.Ops`)

```lean
abbrev Descriptor := Spec.Descriptor
abbrev Coherence := Spec.Coherence
abbrev Atomicity := Spec.Atomicity

def isValid (d : Descriptor) : Bool
def bytesMoved (d : Descriptor) : Nat
def stepCount (d : Descriptor) : Nat
def simulateCopy (src dst : ByteArray) (d : Descriptor) : Option ByteArray
```

### Simulation Notes

- `simulateCopy` preserves the destination buffer size.
- Simulation fails when the descriptor is invalid or either region falls out of bounds.
- `stepCount` reflects visibility steps, not individual byte copies.

## Proofs (`DMA.Lemmas`)

- `isValid_iff_valid`: boolean validation agrees with the specification predicate
- `bytesMoved_pos`: valid descriptors always move a positive number of bytes
- `stepCount_pos`: valid descriptors always require at least one visibility step
- `simulateCopy_eq_some`: successful simulation returns the expected destination splice

## Examples

```lean
import Radix.DMA

def descriptor : Radix.DMA.Descriptor :=
  { source := { start := 0, size := 4 }
  , destination := { start := 8, size := 4 }
  , order := .seqCst
  , coherence := .nonCoherent
  , atomicity := .burst 2
  }
```

## Related Documents

- [Memory](memory.md) — region operations reused by descriptor validation
- [Concurrency](concurrency.md) — memory-ordering model used for fence requirements
