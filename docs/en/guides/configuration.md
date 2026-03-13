# Configuration Guide

> **Audience**: Users, Developers

## Adding Radix as a Dependency

Add Radix to your project's `lakefile.lean`:

```lean
import Lake
open Lake DSL

package myProject where
  leanOptions := #[⟨`autoImplicit, false⟩]

require radix from git
  "https://github.com/user/radix" @ "main"

@[default_target]
lean_lib MyLib where
  srcDir := "."
```

Then resolve dependencies:

```bash
lake update
lake build
```

## Lean 4 Toolchain

Radix pins its toolchain in `lean-toolchain`:

```
leanprover/lean4:v4.29.0-rc4
```

Your project's toolchain must be compatible. If you use a different version, Mathlib may fail to build.

> **Warning:** Do not change Radix's `lean-toolchain` unless you also update the Mathlib revision in `lakefile.lean`.

## Package Options

Radix sets the following Lean options in its `lakefile.lean`:

| Option | Value | Effect |
|--------|-------|--------|
| `autoImplicit` | `false` | Disables automatic implicit argument inference. All implicit arguments must be explicitly declared. Prevents accidental free variables. |

If your project depends on Radix, you are not required to use the same options. However, `autoImplicit := false` is recommended for any project doing formal verification.

## Build Targets

Radix defines the following Lake targets:

| Target | Command | Description |
|--------|---------|-------------|
| `Radix` (default) | `lake build` | Build the library |
| `test` | `lake build test && lake exe test` | Unit and integration tests |
| `proptest` | `lake build proptest && lake exe proptest` | Property-based tests (500 iterations, LCG PRNG) |
| `bench` | `lake build bench && lake exe bench` | Performance benchmarks |
| `examples` | `lake build examples && lake exe examples` | Usage examples with assertions |

## Import Granularity

You can import the entire library or individual modules:

```lean
-- Import everything
import Radix

-- Import specific modules
import Radix.Word       -- Integer types and arithmetic
import Radix.Bit        -- Bitwise operations
import Radix.Bytes      -- Endianness and byte slices
import Radix.Memory     -- Buffer, pointer, layout
import Radix.Binary     -- Format DSL, parser, serializer, LEB128
import Radix.System     -- File I/O, error handling
import Radix.Concurrency -- Atomic operations model
import Radix.BareMetal   -- Bare metal support model
```

All definitions are in the `Radix` namespace. Use `open Radix` to access them without prefix:

```lean
import Radix
open Radix

#eval UInt32.wrappingAdd 100 200  -- 300
```

## Dependencies

Radix depends on Mathlib. Lake resolves this automatically. The first build downloads and compiles Mathlib4, which takes significant time.

| Dependency | Inherited | Purpose |
|------------|-----------|---------|
| **mathlib** | No | `BitVec n`, algebraic structures, proof tactics |
| **batteries** | Yes (via Mathlib) | Standard library extensions |
| **plausible** | Yes (via Mathlib) | Property-based testing |
| **aesop** | Yes (via Mathlib) | Proof automation tactic |
| **Qq** | Yes (via Mathlib) | Quoted expressions |
| **proofwidgets** | Yes (via Mathlib) | Interactive proof widgets |

> **Note:** Mathlib is formally verified. It does NOT expand the Trusted Computing Base.

## Local Development

For developing Radix alongside a dependent project, use a local path dependency:

```lean
require radix from ".." / "radix"
```

This avoids Git fetches and lets you iterate on both projects simultaneously.

## Related Documents

- [Installation](../getting-started/installation.md) — First-time setup
- [Configuration Reference](../reference/configuration.md) — Full option reference
- [Build](../development/build.md) — Build system details
