# Benchmark Results Template

## Environment

- **Date**: YYYY-MM-DD
- **Lean Toolchain**: `leanprover/lean4:v4.x.y`
- **Hardware**: CPU model, cores, clock speed
- **OS**: Linux distribution/version
- **C Compiler**: gcc/clang version, flags: `-O2 -fno-builtin`

## Methodology

- 10^6 iterations per benchmark
- 5 measured runs, 2 warmup runs
- Median ns/op reported
- Anti-DCE: accumulator sink (printed), input-dependent operands (PRNG array)

## Results

### UInt32 Arithmetic

| Operation      | Lean (ns/op) | C Baseline (ns/op) | Ratio |
|----------------|-------------|--------------------:|------:|
| wrappingAdd    |             |                     |       |
| wrappingSub    |             |                     |       |
| wrappingMul    |             |                     |       |
| saturatingAdd  |             |                     |       |
| checkedAdd     |             |                     |       |

### UInt64 Arithmetic

| Operation      | Lean (ns/op) | C Baseline (ns/op) | Ratio |
|----------------|-------------|--------------------:|------:|
| wrappingAdd    |             |                     |       |
| wrappingSub    |             |                     |       |
| wrappingMul    |             |                     |       |

### Bitwise Operations (UInt32)

| Operation | Lean (ns/op) | C Baseline (ns/op) | Ratio |
|-----------|-------------|--------------------:|------:|
| band      |             |                     |       |
| bor       |             |                     |       |
| bxor      |             |                     |       |
| shl       |             |                     |       |
| popcount  |             |                     |       |
| clz       |             |                     |       |
| rotl      |             |                     |       |

### Byte Order (UInt32)

| Operation      | Lean (ns/op) | C Baseline (ns/op) | Ratio |
|----------------|-------------|--------------------:|------:|
| bswap          |             |                     |       |
| toBigEndian    |             |                     |       |
| toLittleEndian |             |                     |       |

### Width Conversions

| Operation         | Lean (ns/op) |
|-------------------|-------------|
| u8→u32 zeroExtend |             |
| u32→u8 truncate   |             |
| u32→u64 zeroExtend|             |

### LEB128

| Operation  | Lean (ns/op) |
|------------|-------------|
| encodeU32  |             |
| decodeU32  |             |

### Int32 Arithmetic

| Operation    | Lean (ns/op) |
|--------------|-------------|
| wrappingAdd  |             |
| wrappingMul  |             |
| wrappingNeg  |             |

## Notes

- Record any anomalies or observations here
- Verify: all accumulator values non-zero
- Inspect `build/ir/benchmarks/Main.c` for expected operations
