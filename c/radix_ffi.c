/*
 * Radix FFI: Hardware-accelerated intrinsics via compiler builtins.
 *
 * These functions are called from Lean via @[extern] and compile to
 * single hardware instructions (LZCNT) with -march=native on x86-64.
 *
 * Copyright (c) 2026 Radix Contributors. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 */

#include <stdint.h>

/* CLZ (Count Leading Zeros) using __builtin_clz / __builtin_clzll.
 *
 * __builtin_clz is undefined for x == 0, so we handle it explicitly.
 * The x == 0 branch is perfectly predicted (almost never taken in practice)
 * and the compiler emits LZCNT which handles x == 0 natively on BMI1+ CPUs,
 * so the branch is typically eliminated entirely.
 */

uint8_t radix_clz8(uint8_t x) {
    return x == 0 ? 8 : (uint8_t)(__builtin_clz((uint32_t)x) - 24);
}

uint16_t radix_clz16(uint16_t x) {
    return x == 0 ? 16 : (uint16_t)(__builtin_clz((uint32_t)x) - 16);
}

uint32_t radix_clz32(uint32_t x) {
    return x == 0 ? 32 : (uint32_t)__builtin_clz(x);
}

uint64_t radix_clz64(uint64_t x) {
    return x == 0 ? 64 : (uint64_t)__builtin_clzll(x);
}
