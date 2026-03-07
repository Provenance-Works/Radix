# Constraints

Version: 0.1.0-draft
Last updated: 2026-03-07

## C-001: Strict Prohibition of Custom C Code and FFI

Radix MUST NOT contain ANY C source code, custom C ABI shims, or custom `@[extern]` FFI bindings.
The project is strictly limited to 100% pure Lean 4 and Mathlib.
All bounds-checking, hardware representations, and interactions with the operating system MUST be performed exclusively through Lean 4's built-in APIs (such as `ByteArray`, `IO.FS`, `IO.Process`).

This constraint represents an absolute project requirement (Zero C-dependency / No FFI) to eliminate the risk of memory leaks, Use-After-Free (UAF), and vulnerabilities in the Trusted Computing Base (TCB).

The System module MUST use Lean4's built-in IO APIs completely. Any functions that would require external C implementation (e.g. raw `mmap`, raw `sysOpen`) are strictly forbidden from being implemented via FFI.

Note: Lean4's own runtime is written in C. This is outside Radix's control
and is accepted as part of the language platform.

## C-002: No GPL-Family Licenses

Radix MUST NOT depend on any library with GPL, LGPL, or AGPL license.
Radix itself MUST be licensed under Apache 2.0 or MIT.

*Exception*: Dynamically linked OS foundation libraries (such as glibc) are explicitly excluded from this restriction, as standard OS boundaries fall outside the library licensing scope.

## C-003: Lean4 Only

Radix MUST be implementable in pure Lean4 + Mathlib for Layers 2-3.
No code generation to other languages (unlike F*/Low* which generates C).

## C-004: No Mathematical Axioms Beyond Lean4 Defaults

Radix MUST NOT introduce custom **mathematical** axioms.
The only mathematical axioms allowed are those already in Lean4's core and Mathlib:
- `propext`
- `Quot.sound`
- `Classical.choice` (only where necessary, prefer constructive proofs)

### C-004a: Layer 1 External-World Axioms (Sole Exception)

Layer 1 (System.IO) needs to assert that Lean4's IO and any
`@[extern]` calls satisfy the abstract model defined in System.Spec.
These assertions concern the **external world** (OS behavior, hardware
semantics) and **cannot be proven** within Lean4's type system.

Layer 1 MAY use Lean4 `axiom` declarations to represent these assumptions.
This is the **sole permitted exception** to C-004's no-custom-axioms rule.

**Why `axiom` and not `opaque`?**
Lean 4's `opaque` requires a concrete definition body -- it only hides the
definition from the kernel's reducer. For a proposition like "the OS `read`
syscall obeys POSIX semantics", there is no proof term that can be
constructed within Lean's type system. `axiom` is the correct mechanism:
it introduces a declaration without requiring a proof. Using `opaque` would
require either `sorry` (which defeats formal verification) or a fabricated
value (which is unsound).

Each trusted assumption MUST:
- Be an `axiom` declaration (NOT `opaque`, NOT `constant`)
- Be declared in a dedicated file (`Radix/System/Assumptions.lean`)
- Have a docstring explaining what is assumed and why it cannot be proven
- Reference the POSIX or Lean4 runtime specification that justifies it
- Be prefixed with `trust_` in the name (e.g., `trust_read_posix_semantics`)
- Be typed as a **proposition** (return type : `Prop`)
- Be listed in the TCB audit inventory (see architecture.md Section 5)

These axioms assert properties of the external world, NOT mathematical truths.
They expand the TCB but do not weaken the mathematical foundation of Layers 2-3.

The total number of trusted assumptions is a key quality metric.
Every release MUST report the count and list of trusted assumptions.

## C-005: Target Platforms

Initial target: Linux x86_64.
Radix's pure modules (Word, Bit, Bytes, Memory, Binary) MUST be platform-independent.
Only the System module's IO/FFI layer is platform-specific.
USize/ISize are parametric over `System.Platform.numBits` and work on all platforms.

## C-006: Mathlib Dependency

Radix MAY depend on Mathlib freely.
Mathlib is formally verified code -- it does NOT expand the TCB.
Radix MUST specify the exact Mathlib version in lakefile.lean.
Radix MAY use Mathlib's algebraic structures, `BitVec`, and proof tactics.
