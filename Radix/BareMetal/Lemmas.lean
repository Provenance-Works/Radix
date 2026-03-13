/-
Copyright (c) 2026 Radix Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Radix.BareMetal.Spec
import Radix.BareMetal.GCFree
import Radix.BareMetal.Linker
import Radix.BareMetal.Startup

/-!
# Bare Metal Proofs (Layer 3)

This module contains proofs for the bare-metal subsystem:

- Memory region disjointness and containment
- Memory map validity properties
- Startup sequence correctness
- GC-free constraint composition
- Linker script properties
- Address alignment properties

## Architecture

This is a **Layer 3 (Verified Specification)** module containing proofs.

## References

- P5-02: Bare metal support
-/

set_option autoImplicit false

namespace Radix.BareMetal

open Spec
open GCFree
open Linker
open Startup

/-! ## Memory Region Properties -/

theorem MemRegion.disjoint_comm (a b : MemRegion) :
    MemRegion.disjoint a b ↔ MemRegion.disjoint b a := by
  simp only [MemRegion.disjoint, MemRegion.endAddr]
  exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

theorem MemRegion.disjoint_of_endAddr_le (a b : MemRegion)
    (h : a.endAddr ≤ b.baseAddr) :
    MemRegion.disjoint a b := by
  exact Or.inl h

theorem MemRegion.not_contains_of_disjoint (a b : MemRegion) (addr : Nat)
    (hDisjoint : MemRegion.disjoint a b)
    (hContains : MemRegion.contains a addr) :
    ¬MemRegion.contains b addr := by
  intro hb
  simp only [MemRegion.disjoint, MemRegion.endAddr] at hDisjoint
  simp only [MemRegion.contains, MemRegion.endAddr] at hContains hb
  cases hDisjoint with
  | inl h => omega
  | inr h => omega

theorem MemRegion.endAddr_eq (r : MemRegion) :
    r.endAddr = r.baseAddr + r.size := rfl

/-! ## Empty Memory Map -/

theorem MemoryMap.empty_isValid (p : Platform) :
    (MemoryMap.mk [] p).isValid := by
  constructor
  · intro a ha; simp at ha
  · intro r hr; simp at hr

theorem MemoryMap.empty_totalSize (p : Platform) :
    (MemoryMap.mk [] p).totalSize = 0 := rfl

theorem MemoryMap.empty_findRegion (p : Platform) (addr : Nat) :
    (MemoryMap.mk [] p).findRegion addr = none := rfl

/-! ## Section Properties -/

theorem Section.disjoint_comm (a b : Section) :
    Section.disjoint a b ↔ Section.disjoint b a := by
  simp only [Section.disjoint, Section.endAddr]
  exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

theorem Section.endAddr_eq (s : Section) :
    s.endAddr = s.vma + s.size := rfl

/-! ## Linker Script Properties -/

theorem LinkerScript.empty_isNonOverlapping (p : Platform) :
    (LinkerScript.mk [] [] "" p).isNonOverlapping := by
  intro _ h; simp at h

theorem LinkerScript.empty_totalSize (p : Platform) :
    (LinkerScript.mk [] [] "" p).totalSize = 0 := rfl

/-! ## Alignment Properties -/

theorem alignUp_ge (addr align : Nat) (hA : align > 0) :
    alignUp addr align ≥ addr := by
  unfold alignUp
  split
  · omega
  · have hmod := Nat.mod_lt (addr + align - 1) hA
    have hdiv := Nat.div_add_mod (addr + align - 1) align
    rw [Nat.mul_comm] at hdiv
    omega

theorem alignDown_le (addr align : Nat) (_hA : align > 0) :
    alignDown addr align ≤ addr := by
  unfold alignDown
  split
  · omega
  · have hdiv := Nat.div_add_mod addr align
    rw [Nat.mul_comm] at hdiv
    omega

theorem alignUp_zero (align : Nat) (hA : align > 0) :
    alignUp 0 align = 0 := by
  unfold alignUp
  split
  · rfl
  · have h1 : 0 + align - 1 = align - 1 := by omega
    rw [h1]
    have h2 : (align - 1) / align = 0 := Nat.div_eq_of_lt (by omega)
    simp [h2]

theorem alignDown_zero (align : Nat) (_hA : align > 0) :
    alignDown 0 align = 0 := by
  unfold alignDown
  split
  · rfl
  · simp [Nat.zero_div]

theorem isAligned_zero (align : Nat) :
    isAligned 0 align = true := by
  unfold isAligned
  split
  · rfl
  · rfl

/-! ## GC-Free Properties -/

theorem AllocStrategy.all_isGCFree (s : AllocStrategy) :
    s.isGCFree = true := by
  cases s <;> rfl

theorem GCFreeConstraint.default_allows_static :
    AllocStrategy.static ∈ GCFreeConstraint.default.allowedStrategies := by
  simp [GCFreeConstraint.default]

theorem GCFreeConstraint.default_allows_stack :
    AllocStrategy.stack ∈ GCFreeConstraint.default.allowedStrategies := by
  simp [GCFreeConstraint.default]

theorem GCFreeConstraint.default_forbids_arena :
    AllocStrategy.arena ∉ GCFreeConstraint.default.allowedStrategies := by
  simp [GCFreeConstraint.default]

theorem GCFreeConstraint.withArena_allows_arena :
    AllocStrategy.arena ∈ (GCFreeConstraint.withArena 8192).allowedStrategies := by
  simp [GCFreeConstraint.withArena]

theorem checkModule_empty (c : GCFreeConstraint) :
    checkModule c [] = [] := rfl

/-! ## Stack Frame Properties -/

theorem StackFrame.totalSize_eq (f : StackFrame) :
    f.totalSize = f.localBytes + f.savedRegs + f.padding := rfl

theorem worstCaseStackDepth_nil :
    worstCaseStackDepth [] = 0 := rfl

private theorem foldl_totalSize_shift (xs : List StackFrame) (n : Nat) :
    xs.foldl (fun acc f => acc + f.totalSize) n =
    xs.foldl (fun acc f => acc + f.totalSize) 0 + n := by
  induction xs generalizing n with
  | nil => simp [List.foldl]
  | cons x xs ih =>
    simp only [List.foldl]
    rw [ih (n + x.totalSize), ih (0 + x.totalSize)]
    omega

theorem worstCaseStackDepth_cons (f : StackFrame) (fs : List StackFrame) :
    worstCaseStackDepth (f :: fs) =
    worstCaseStackDepth fs + f.totalSize := by
  simp only [worstCaseStackDepth, List.foldl, Nat.zero_add]
  exact foldl_totalSize_shift fs f.totalSize

/-! ## Startup Validation Properties -/

theorem minimalStartup_startsWithInterruptsDisabled
    (st bb bs dl dv ds e : Nat) :
    startsWithInterruptsDisabled
      (minimalStartupActions st bb bs dl dv ds e) = true := rfl

theorem minimalStartup_endsWithJump
    (st bb bs dl dv ds e : Nat) :
    endsWithJump
      (minimalStartupActions st bb bs dl dv ds e) = true := rfl

theorem minimalStartup_isValid
    (st bb bs dl dv ds e : Nat) :
    isValidStartupSequence
      (minimalStartupActions st bb bs dl dv ds e) = true := by
  rfl

theorem fullStartup_isValid
    (st bb bs dl dv ds vt e : Nat) :
    isValidStartupSequence
      (fullStartupActions st bb bs dl dv ds vt e) = true := by
  rfl

/-! ## Platform Properties -/

theorem Platform.wordBits_pos (p : Platform) : p.wordBits > 0 := by
  cases p <;> decide

theorem Platform.naturalAlign_pos (p : Platform) : p.naturalAlign > 0 := by
  cases p <;> decide

/-! ## Startup Phase Properties -/

theorem StartupPhase.reset_precedes_appEntry :
    StartupPhase.precedes .reset .appEntry = true := by
  decide

theorem StartupPhase.order_injective (a b : StartupPhase)
    (h : a.order = b.order) : a = b := by
  cases a <;> cases b <;> simp [StartupPhase.order] at h <;> first | rfl | omega

end Radix.BareMetal
