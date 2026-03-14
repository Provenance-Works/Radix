import Radix.Concurrency

/-!
# Example: Lock-Free Data Structure Patterns

Demonstrates lock-free programming patterns using Radix's C11-style
atomic memory model. Shows:

- Atomic load/store with memory ordering
- Compare-and-swap (CAS) for lock-free updates
- Fetch-and-add for atomic counters
- Lock-free stack (Treiber stack) simulation
- Spinlock protocol
-/

namespace Examples.LockFree

open Radix.Concurrency.Spec
open Radix.Concurrency.Ordering
open Radix.Concurrency.Atomic

/-! ## 1. Atomic Counter -/

structure AtomicCounter where
  cell : AtomicCell
  history : List Nat

namespace AtomicCounter

def new (initial : Nat := 0) : AtomicCounter :=
  { cell := AtomicCell.new initial, history := [initial] }

def get (c : AtomicCounter) : Nat × AtomicCounter :=
  let (result, cell') := atomicLoad c.cell .acquire
  (result.value, { c with cell := cell' })

def increment (c : AtomicCounter) : AtomicCounter :=
  let (result, cell') := fetchAdd c.cell 1 .seqCst
  { cell := cell', history := c.history ++ [result.previous + 1] }

def add (c : AtomicCounter) (n : Nat) : AtomicCounter :=
  let (result, cell') := fetchAdd c.cell n .seqCst
  { cell := cell', history := c.history ++ [result.previous + n] }

def decrement (c : AtomicCounter) : AtomicCounter :=
  let (result, cell') := fetchSub c.cell 1 .seqCst
  { cell := cell', history := c.history ++ [result.previous - 1] }

end AtomicCounter

/-! ## 2. Treiber Stack (model)

Simulates CAS-based lock-free stack protocol. -/

structure TreiberStack where
  head : AtomicCell
  nodes : Array (Nat × Nat)  -- (value, next_index)
  nextFree : Nat

namespace TreiberStack

def new : TreiberStack :=
  { head := AtomicCell.new 0
    nodes := #[(0, 0)]  -- Index 0 = null sentinel
    nextFree := 1 }

def push (s : TreiberStack) (value : Nat) : TreiberStack :=
  let nodeIdx := s.nextFree
  let (loadResult, headCell) := atomicLoad s.head .acquire
  let oldHead := loadResult.value
  let nodes' := s.nodes.push (value, oldHead)
  let (_, headCell') := atomicCAS headCell oldHead nodeIdx .release
  { head := headCell', nodes := nodes', nextFree := nodeIdx + 1 }

def pop (s : TreiberStack) : Option (Nat × TreiberStack) :=
  let (loadResult, headCell) := atomicLoad s.head .acquire
  let oldHead := loadResult.value
  if oldHead == 0 then none
  else if h : oldHead < s.nodes.size then
    let (value, next) := s.nodes[oldHead]
    let (_, headCell') := atomicCAS headCell oldHead next .release
    some (value, { s with head := headCell' })
  else none

def isEmpty (s : TreiberStack) : Bool :=
  let (result, _) := atomicLoad s.head .relaxed
  result.value == 0

end TreiberStack

/-! ## 3. Spinlock (model) -/

structure SpinLock where
  lock : AtomicCell
  owner : String

namespace SpinLock

def new : SpinLock :=
  { lock := AtomicCell.new 0, owner := "" }

def tryAcquire (sl : SpinLock) (who : String) : Bool × SpinLock :=
  let (result, cell') := atomicCAS sl.lock 0 1 .acquire
  if result.success then
    (true, { lock := cell', owner := who })
  else
    (false, { sl with lock := cell' })

def release (sl : SpinLock) : SpinLock :=
  let (_, cell') := atomicStore sl.lock 0 .release
  { lock := cell', owner := "" }

def isLocked (sl : SpinLock) : Bool :=
  let (result, _) := atomicLoad sl.lock .relaxed
  result.value != 0

end SpinLock

/-! ## Demo -/

def run : IO Unit := do
  IO.println "=== Lock-Free Data Structure Patterns ==="
  IO.println ""

  -- 1. Memory ordering analysis
  IO.println "  1. Memory Ordering Model"
  IO.println "  ---"
  IO.println "    Ordering strengths:"
  let orderings : List (MemoryOrder × String) :=
    [(.relaxed, "relaxed"), (.acquire, "acquire"), (.release, "release"),
     (.acqRel, "acqRel"), (.seqCst, "seqCst")]
  for (ord, name) in orderings do
    IO.println s!"      {name} (strength={ord.strength})"

  IO.println ""
  IO.println "    Properties:"
  IO.println s!"      SeqCst has acquire: {hasAcquireSemantics .seqCst}"
  IO.println s!"      SeqCst has release: {hasReleaseSemantics .seqCst}"
  IO.println s!"      Relaxed has acquire: {hasAcquireSemantics .relaxed}"
  IO.println s!"      AcqRel has both: {hasAcquireSemantics .acqRel && hasReleaseSemantics .acqRel}"
  IO.println ""

  -- 2. Atomic counter
  IO.println "  2. Atomic Counter"
  IO.println "  ---"
  let mut counter := AtomicCounter.new 0
  IO.println s!"    Initial: {counter.cell.val}"

  for _ in [:5] do
    counter := counter.increment
  IO.println s!"    After 5 increments: {counter.cell.val}"

  counter := counter.add 10
  IO.println s!"    After add(10): {counter.cell.val}"

  for _ in [:3] do
    counter := counter.decrement
  IO.println s!"    After 3 decrements: {counter.cell.val}"

  let (finalVal, _) := counter.get
  IO.println s!"    Final value: {finalVal}"
  IO.println s!"    History: {counter.history}"
  if finalVal != 12 then throw (IO.userError "expected 12")
  IO.println ""

  -- 3. Fetch-and-modify operations
  IO.println "  3. Fetch-and-Modify Operations"
  IO.println "  ---"
  let cell := AtomicCell.new 0xFF
  IO.println s!"    Initial: 0x{String.ofList (Nat.toDigits 16 cell.val)}"

  let (res1, cell1) := fetchOr cell 0x0F00 .seqCst
  IO.println s!"    fetchOr 0x0F00: prev=0x{String.ofList (Nat.toDigits 16 res1.previous)}, now=0x{String.ofList (Nat.toDigits 16 cell1.val)}"

  let (res2, cell2) := fetchAnd cell1 0x0FF0 .seqCst
  IO.println s!"    fetchAnd 0x0FF0: prev=0x{String.ofList (Nat.toDigits 16 res2.previous)}, now=0x{String.ofList (Nat.toDigits 16 cell2.val)}"

  let (res3, _) := fetchXor cell2 0xFFFF .seqCst
  IO.println s!"    fetchXor 0xFFFF: prev=0x{String.ofList (Nat.toDigits 16 res3.previous)}"
  IO.println ""

  -- 4. Treiber stack
  IO.println "  4. Lock-Free Treiber Stack"
  IO.println "  ---"
  let mut stack := TreiberStack.new
  IO.println s!"    Empty: {stack.isEmpty}"

  IO.println "    Pushing: 10, 20, 30, 40, 50"
  for v in [10, 20, 30, 40, 50] do
    stack := stack.push v

  IO.println s!"    Empty: {stack.isEmpty}"

  let mut popOrder : List Nat := []
  for _ in [:5] do
    match stack.pop with
    | some (val, stack') =>
      popOrder := popOrder ++ [val]
      stack := stack'
    | none => break
  IO.println s!"    Pop order (LIFO): {popOrder}"
  if popOrder != [50, 40, 30, 20, 10] then
    throw (IO.userError "LIFO order violated")
  IO.println "    ✓ LIFO order maintained"
  IO.println ""

  -- 5. Spinlock
  IO.println "  5. Spinlock Protocol"
  IO.println "  ---"
  let mut lock := SpinLock.new
  IO.println s!"    Locked: {lock.isLocked}"

  let (ok, lock') := SpinLock.tryAcquire lock "ThreadA"
  lock := lock'
  IO.println s!"    ThreadA acquire: {ok}"

  let (ok2, lock2) := SpinLock.tryAcquire lock "ThreadB"
  lock := lock2
  IO.println s!"    ThreadB acquire (while held): {ok2}"
  if ok2 then throw (IO.userError "rival should fail")

  lock := lock.release
  IO.println s!"    ThreadA release"

  let (ok3, lock3) := SpinLock.tryAcquire lock "ThreadB"
  lock := lock3
  IO.println s!"    ThreadB acquire (after release): {ok3}"
  if !ok3 then throw (IO.userError "should succeed now")

  lock := lock.release
  IO.println s!"    Final: locked={lock.isLocked}"
  IO.println ""

end Examples.LockFree
