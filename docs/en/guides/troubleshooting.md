# Troubleshooting

> **Audience**: All

## Build Issues

### `lake build` fails on first run with Mathlib errors

**Cause:** Mathlib download or compilation failed partway through.

**Solution:**
```bash
lake clean
lake update
lake build
```

If Mathlib is very slow to compile, check that you have sufficient memory (≥ 8 GB recommended). Mathlib compilation is memory-intensive.

### Toolchain version mismatch

**Symptom:** Errors like `unknown package 'Init'` or `import Mathlib failed`.

**Cause:** Your project's `lean-toolchain` doesn't match Radix's pinned toolchain (`leanprover/lean4:v4.29.0-rc4`).

**Solution:** Align your project's `lean-toolchain` with Radix's:
```
leanprover/lean4:v4.29.0-rc4
```

### `unknown identifier 'Radix.UInt32'`

**Cause:** Missing `open Radix` or incomplete import.

**Solution:**
```lean
import Radix
open Radix

-- Now UInt32.wrappingAdd is available without prefix
```

Or use the fully qualified name:
```lean
import Radix
#eval Radix.UInt32.wrappingAdd 100 200
```

### `ambiguous, possible interpretations` for `UInt8`, `UInt16`, etc.

**Cause:** Radix's `UInt8` etc. shadow Lean 4's built-in types of the same name.

**Solution:** Within `open Radix`, Radix's types take precedence. If you need the built-in type, use `_root_.UInt8`. To convert between them:
```lean
let radixVal : Radix.UInt32 := ...
let builtinVal : _root_.UInt32 := radixVal.toBuiltin
let backToRadix : Radix.UInt32 := Radix.UInt32.fromBuiltin builtinVal
```

## Type Errors

### `type mismatch: expected BitVec n, got UInt32`

**Cause:** Mixing Radix types (Layer 2) with Mathlib's `BitVec` (Layer 3) without conversion.

**Solution:** Use `toBitVec` / `fromBitVec`:
```lean
let x : UInt32 := ...
let bv : BitVec 32 := x.toBitVec    -- Layer 2 → Layer 3
let y : UInt32 := UInt32.fromBitVec bv  -- Layer 3 → Layer 2
```

### Tier 1 API: `failed to synthesize proof`

**Cause:** Tier 1 (proof-carrying) APIs require compile-time bound proofs. If the proof obligation can't be discharged automatically, you get this error.

**Solution:** Either provide the proof manually or use Tier 2 (checked) APIs:
```lean
-- Tier 1: requires proof
let result := buf.readU8 0 (by omega)  -- proof via omega

-- Tier 2: no proof needed, returns Option
let result := buf.checkedReadU8 0  -- returns Option UInt8
```

### `sorry` in proofs

**Symptom:** Warning about axiom `sorry` after building.

**Cause:** An unfinished proof exists somewhere in the dependency chain.

**Solution:** Radix releases MUST have zero `sorry`. If you see this warning, ensure you're using an official release, not a development branch.

## System I/O Errors

### `SysError.permissionDenied` when writing files

**Cause:** The target path lacks write permissions or is on a read-only filesystem.

**Solution:** Check file permissions:
```bash
ls -la /path/to/file
chmod u+w /path/to/file
```

### `SysError.notFound` when reading files

**Cause:** The specified file does not exist.

**Solution:** Verify the path and check file existence first:
```lean
let exists ← System.IO.sysFileExists "myfile.bin"
match exists with
| .ok true => -- file exists, safe to read
| _ => -- handle missing file
```

### `SysError.endOfFile` during `sysRead`

**Cause:** Attempted to read past the end of a file.

**Solution:** This is expected behavior. `sysRead` returns `endOfFile` when no more data is available. Check the result:
```lean
let result ← System.IO.sysRead fd 1024
match result with
| .ok bytes => if bytes.size == 0 then /- EOF -/ else /- process bytes -/
| .error .endOfFile => /- explicitly reached EOF -/
| .error e => /- other error -/
```

## Performance Issues

### Operations seem slow compared to C

**Cause:** Radix wraps Lean 4's built-in types, but the Lean 4 runtime has overhead compared to bare C (GC, reference counting).

**Solution:**
- Ensure you're building with optimizations: use `lake build` (release mode)
- Use `@[inline]` operations (most Radix operations are already inlined)
- For hot loops, consider the wrapping arithmetic variants (no branch overhead)
- See the [benchmarks](../../benchmarks/) for baseline comparison against C

### Property tests are slow

**Cause:** Property-based tests run 500 iterations per test by default.

**Solution:** This is by design for thorough coverage. If you need faster iteration during development, you can temporarily reduce iteration counts in your test code.

## LEB128 Issues

### `decodeU32` returns `none`

**Causes:**
- Truncated input (byte sequence ends before a final byte with continue bit = 0)
- Overlong encoding (more than 5 bytes for U32, 10 for U64)
- Overflow (decoded value exceeds the type's range)

**Solution:** Ensure the input contains a valid LEB128 encoding. The encoding must terminate with a byte where bit 7 is clear.

## Related Documents

- [Errors Reference](../reference/errors.md) — Full error catalog
- [Configuration](configuration.md) — Build configuration
- [Installation](../getting-started/installation.md) — Setup instructions
