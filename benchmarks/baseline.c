/*
 * Radix C Baseline Microbenchmarks
 *
 * Compile: gcc -O2 -fno-builtin -o baseline baseline.c
 *          clang -O2 -fno-builtin -o baseline baseline.c
 *
 * These baselines measure the same operations as the Lean benchmarks
 * to provide a comparison point per NFR-002.2.
 */

#include <stdio.h>
#include <stdint.h>
#include <time.h>

#define NUM_ITER 1000000
#define NUM_RUNS 5
#define WARMUP_RUNS 2

/* PRNG (same as Lean benchmarks: Knuth MMIX) */
static uint64_t prng_state;

static void prng_seed(uint64_t seed) {
    prng_state = seed;
}

static uint64_t prng_next(void) {
    prng_state = prng_state * 6364136223846793005ULL + 1442695040888963407ULL;
    return prng_state;
}

/* Timing */
static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

static int cmp_u64(const void *a, const void *b) {
    uint64_t va = *(const uint64_t *)a;
    uint64_t vb = *(const uint64_t *)b;
    return (va > vb) - (va < vb);
}

/* Pre-generated random data */
static uint64_t data[NUM_ITER];

static void gen_data(uint64_t seed) {
    prng_seed(seed);
    for (int i = 0; i < NUM_ITER; i++)
        data[i] = prng_next();
}

/* Popcount (software) */
static uint32_t sw_popcount32(uint32_t x) {
    uint32_t count = 0;
    while (x) { count += x & 1; x >>= 1; }
    return count;
}

/* CLZ (software) */
static uint32_t sw_clz32(uint32_t x) {
    if (x == 0) return 32;
    uint32_t n = 0;
    while (!(x & 0x80000000U)) { n++; x <<= 1; }
    return n;
}

/* Rotl */
static uint32_t rotl32(uint32_t x, uint32_t c) {
    c &= 31;
    return (x << c) | (x >> (32 - c));
}

/* Bswap */
static uint32_t bswap32(uint32_t x) {
    return ((x >> 24) & 0xFF)
         | ((x >> 8) & 0xFF00)
         | ((x << 8) & 0xFF0000)
         | ((x << 24) & 0xFF000000U);
}

/* Benchmark runner */
typedef uint64_t (*bench_fn)(void);

static void run_bench(const char *label, bench_fn fn) {
    uint64_t times[NUM_RUNS];

    /* Warmup */
    for (int i = 0; i < WARMUP_RUNS; i++) {
        uint64_t acc = fn();
        printf("  %s: accumulator = %lu\n", label, (unsigned long)acc);
    }

    /* Measured */
    for (int i = 0; i < NUM_RUNS; i++) {
        uint64_t t0 = now_ns();
        uint64_t acc = fn();
        uint64_t t1 = now_ns();
        times[i] = t1 - t0;
        printf("  %s: accumulator = %lu\n", label, (unsigned long)acc);
    }

    qsort(times, NUM_RUNS, sizeof(uint64_t), cmp_u64);
    uint64_t median = times[NUM_RUNS / 2];
    printf("  %s: %lu ns/op (median of %d, %d iters)\n",
           label, (unsigned long)(median / NUM_ITER), NUM_RUNS, NUM_ITER);
}

/* ================================================================ */
/* UInt32 Arithmetic                                                 */
/* ================================================================ */

static uint64_t bench_u32_wrapping_add(void) {
    uint32_t acc = 1;
    for (int i = 0; i < NUM_ITER; i++)
        acc += (uint32_t)(data[i] % UINT32_MAX);
    return acc;
}

static uint64_t bench_u32_wrapping_sub(void) {
    uint32_t acc = UINT32_MAX;
    for (int i = 0; i < NUM_ITER; i++)
        acc -= (uint32_t)(data[i] % UINT32_MAX);
    return acc;
}

static uint64_t bench_u32_wrapping_mul(void) {
    uint32_t acc = 1;
    for (int i = 0; i < NUM_ITER; i++)
        acc *= (uint32_t)((data[i] % 100) + 1);
    return acc;
}

/* ================================================================ */
/* Bitwise                                                           */
/* ================================================================ */

static uint64_t bench_u32_band(void) {
    uint32_t acc = UINT32_MAX;
    for (int i = 0; i < NUM_ITER; i++)
        acc &= (uint32_t)(data[i] % UINT32_MAX);
    return acc;
}

static uint64_t bench_u32_bor(void) {
    uint32_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++)
        acc |= (uint32_t)(data[i] % UINT32_MAX);
    return acc;
}

static uint64_t bench_u32_bxor(void) {
    uint32_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++)
        acc ^= (uint32_t)(data[i] % UINT32_MAX);
    return acc;
}

static uint64_t bench_u32_popcount(void) {
    uint64_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++)
        acc += sw_popcount32((uint32_t)(data[i] % UINT32_MAX));
    return acc;
}

static uint64_t bench_u32_clz(void) {
    uint64_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++)
        acc += sw_clz32((uint32_t)(data[i] % UINT32_MAX));
    return acc;
}

static uint64_t bench_u32_rotl(void) {
    uint32_t acc = 1;
    for (int i = 0; i < NUM_ITER; i++)
        acc = rotl32(acc, (uint32_t)(data[i] % 32));
    return acc;
}

/* ================================================================ */
/* Byte Order                                                        */
/* ================================================================ */

static uint64_t bench_u32_bswap(void) {
    uint32_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++)
        acc ^= bswap32((uint32_t)(data[i] % UINT32_MAX));
    return acc;
}

/* ================================================================ */
/* Main                                                              */
/* ================================================================ */

int main(void) {
    printf("Radix C Baseline Microbenchmarks\n");
    printf("Iterations per benchmark: %d\n\n", NUM_ITER);

    printf("UInt32 Arithmetic:\n");
    gen_data(1);
    run_bench("wrappingAdd", bench_u32_wrapping_add);
    run_bench("wrappingSub", bench_u32_wrapping_sub);
    run_bench("wrappingMul", bench_u32_wrapping_mul);
    printf("\n");

    printf("Bitwise Operations (UInt32):\n");
    gen_data(3);
    run_bench("band", bench_u32_band);
    run_bench("bor", bench_u32_bor);
    run_bench("bxor", bench_u32_bxor);
    run_bench("popcount", bench_u32_popcount);
    run_bench("clz", bench_u32_clz);
    run_bench("rotl", bench_u32_rotl);
    printf("\n");

    printf("Byte Order (UInt32):\n");
    gen_data(4);
    run_bench("bswap", bench_u32_bswap);
    printf("\n");

    printf("C Baseline complete.\n");
    return 0;
}
