# Error Reference

> **Audience**: All

## System Errors (`Radix.System.Error.SysError`)

Radix models OS-level errors via the `SysError` inductive type with 11 variants. These are mapped from Lean 4's `IO.Error` through `SysError.fromIOError`.

| Variant | Parameter | Description | Common Causes |
|---------|-----------|-------------|---------------|
| `permissionDenied` | `msg : String` | Access denied by the OS | File permissions, read-only filesystem |
| `notFound` | `msg : String` | Resource does not exist | Missing file, invalid path |
| `alreadyExists` | `msg : String` | Resource already exists | Creating a file that exists |
| `resourceBusy` | `msg : String` | Resource in use | Locked file, busy device |
| `invalidArgument` | `msg : String` | Invalid parameter | Negative offset, empty path |
| `noSpace` | `msg : String` | No space on device | Full disk |
| `ioError` | `msg : String` | General I/O failure | Hardware error, network failure |
| `interrupted` | `msg : String` | Operation interrupted | Signal received |
| `endOfFile` | (none) | End of file reached | Read past end of file |
| `invalidState` | `msg : String` | Invalid resource state | Operating on closed file |
| `unsupported` | `msg : String` | Operation not supported in pure backend | Negative SEEK_CUR, features requiring FFI |

### Error Handling Pattern

All `System.IO` functions return `IO (Except SysError α)`:

```lean
-- Pattern: explicit error handling
let result ← System.IO.sysRead fd 1024
match result with
| .ok bytes => -- process bytes
| .error e  => -- handle SysError
```

### Mapping from Lean 4 IO.Error

`SysError.fromIOError` provides a complete mapping from all `IO.Error` constructors. Coverage is limited to what Lean 4 exposes — raw POSIX `errno` values are not directly accessible.

## Binary Parse Errors (`Radix.Binary.Parser.ParseError`)

| Variant | Description |
|---------|-------------|
| `outOfBounds` | Attempted to read beyond the input ByteArray |
| `trailingBytes` | The format parsed successfully but extra bytes remained |
| `internal` | Internal parser inconsistency |

## Binary Serialization Errors (`Radix.Binary.Serial.SerialError`)

| Variant | Description |
|---------|-------------|
| `missingField` | Required field not provided |
| `typeMismatch` | Field value type doesn't match format |
| `unexpectedField` | A provided field remained unused after serialization |

## LEB128 Decode Failures

LEB128 decode functions return `Option` — `none` indicates:
- Truncated input (bytes end before final byte)
- Overlong encoding (more bytes than maximum: 5 for U32, 10 for U64)
- Overflow (decoded value exceeds type range)

## See Also

- [Glossary](glossary.md) — Term definitions
- [Troubleshooting](../guides/troubleshooting.md) — Common problems
- [日本語版](../../ja/reference/errors.md) — Japanese version
