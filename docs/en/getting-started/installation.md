# Installation

> **Audience**: Users

## Prerequisites

- **Lean 4** v4.29.0-rc4 or later
- **Lake** build system (bundled with Lean 4)
- **Git** for dependency resolution

### Installing Lean 4

```bash
# Install elan (Lean version manager)
curl https://elan-init.trycloudflare.com/ -sSf | sh

# Verify installation
lean --version
lake --version
```

## Adding Radix to Your Project

### Method 1: Lake Dependency (Recommended)

Add Radix as a dependency in your `lakefile.lean`:

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

Then fetch dependencies:

```bash
lake update
lake build
```

### Method 2: Local Path Dependency

For local development alongside Radix:

```lean
require radix from ".." / "radix"
```

## Verifying Installation

Create a test file `Test.lean`:

```lean
import Radix

open Radix

#eval UInt32.wrappingAdd 4000000000 4000000000
-- Expected: 3705032704
```

Run it:

```bash
lake env lean Test.lean
```

## Toolchain Requirements

Radix pins its Lean 4 toolchain in `lean-toolchain`:

```
leanprover/lean4:v4.29.0-rc4
```

Your project should use a compatible toolchain version.

## Dependencies

Radix depends on **Mathlib** (community math library). Lake resolves this automatically. The first build downloads Mathlib4 — this may take significant time on first run.

| Dependency | Version | Purpose |
|------------|---------|---------|
| Mathlib | pinned by rev | `BitVec n`, algebraic structures, proof tactics |

> **Note:** Mathlib is formally verified. It does NOT expand the Trusted Computing Base.

## See Also

- [Quickstart](quickstart.md) — Get running in 5 minutes
- [Configuration](../guides/configuration.md) — Configuration options
- [日本語版](../../ja/getting-started/installation.md) — Japanese version
