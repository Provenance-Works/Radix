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
#include <stdlib.h>
#include <string.h>
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
        printf("  %s: %.3f ns/op (median of %d, %d iters)\n",
            label, (double)median / (double)NUM_ITER, NUM_RUNS, NUM_ITER);
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
/* Ring Buffer (Circular Queue)                                      */
/* ================================================================ */

#define RINGBUF_CAP 1024

typedef struct {
    uint8_t buf[RINGBUF_CAP];
    int head;
    int tail;
    int count;
    int capacity;
} RingBuf;

static void ringbuf_init(RingBuf *rb, int cap) {
    rb->head = 0;
    rb->tail = 0;
    rb->count = 0;
    rb->capacity = cap;
    for (int i = 0; i < cap; i++) rb->buf[i] = 0;
}

static __attribute__((noinline)) int ringbuf_push(RingBuf *rb, uint8_t val) {
    if (rb->count >= rb->capacity) return 0;
    rb->buf[rb->tail] = val;
    rb->tail = (rb->tail + 1) % rb->capacity;
    rb->count++;
    return 1;
}

static __attribute__((noinline)) int ringbuf_pop(RingBuf *rb, uint8_t *out) {
    if (rb->count == 0) return 0;
    *out = rb->buf[rb->head];
    rb->head = (rb->head + 1) % rb->capacity;
    rb->count--;
    return 1;
}

static __attribute__((noinline)) void ringbuf_push_force(RingBuf *rb, uint8_t val) {
    if (rb->count < rb->capacity) {
        ringbuf_push(rb, val);
    } else {
        rb->buf[rb->tail] = val;
        rb->tail = (rb->tail + 1) % rb->capacity;
        rb->head = (rb->head + 1) % rb->capacity;
    }
}

static uint64_t bench_ringbuf_push(void) {
    RingBuf rb;
    ringbuf_init(&rb, NUM_ITER < RINGBUF_CAP ? NUM_ITER : RINGBUF_CAP);
    uint64_t acc = 0;
    /* Push into a large-capacity buffer */
    ringbuf_init(&rb, RINGBUF_CAP);
    for (int i = 0; i < NUM_ITER; i++) {
        uint8_t byte = (uint8_t)(data[i] & 0xFF);
        /* Reset when full to keep pushing */
        if (rb.count >= rb.capacity) {
            rb.head = 0; rb.tail = 0; rb.count = 0;
        }
        if (ringbuf_push(&rb, byte)) {
            int last = (rb.tail + rb.capacity - 1) % rb.capacity;
            acc += (uint64_t)rb.buf[last] + (uint64_t)rb.tail + (uint64_t)rb.count;
        }
    }
    return acc;
}

static uint64_t bench_ringbuf_pop(void) {
    RingBuf rb;
    ringbuf_init(&rb, RINGBUF_CAP);
    /* Fill buffer */
    for (int i = 0; i < RINGBUF_CAP; i++)
        ringbuf_push(&rb, (uint8_t)(data[i % NUM_ITER] & 0xFF));
    uint64_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++) {
        uint8_t val;
        if (ringbuf_pop(&rb, &val)) {
            acc += val;
        } else {
            /* Refill */
            ringbuf_init(&rb, RINGBUF_CAP);
            for (int j = 0; j < RINGBUF_CAP; j++)
                ringbuf_push(&rb, (uint8_t)(data[j % NUM_ITER] & 0xFF));
        }
    }
    return acc;
}

static uint64_t bench_ringbuf_pushforce(void) {
    RingBuf rb;
    ringbuf_init(&rb, 256);
    uint64_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++) {
        uint8_t byte = (uint8_t)(data[i] & 0xFF);
        ringbuf_push_force(&rb, byte);
        int last = (rb.tail + rb.capacity - 1) % rb.capacity;
        acc += (uint64_t)rb.buf[last] + (uint64_t)rb.head + (uint64_t)rb.tail;
    }
    return acc;
}

/* ================================================================ */
/* CRC-32 (Table-driven, reflected)                                  */
/* ================================================================ */

#define CRC32_POLY 0xEDB88320U
#define CRC32_INIT 0xFFFFFFFFU

static uint32_t crc32_table[256];

static void crc32_init_table(void) {
    for (uint32_t i = 0; i < 256; i++) {
        uint32_t crc = i;
        for (int j = 0; j < 8; j++) {
            if (crc & 1)
                crc = (crc >> 1) ^ CRC32_POLY;
            else
                crc >>= 1;
        }
        crc32_table[i] = crc;
    }
}

static uint32_t crc32_compute(const uint8_t *buf, size_t len) {
    uint32_t crc = CRC32_INIT;
    for (size_t i = 0; i < len; i++)
        crc = crc32_table[(crc ^ buf[i]) & 0xFF] ^ (crc >> 8);
    return crc ^ CRC32_INIT;
}

/* Pre-generated CRC workloads */
#define CRC_BLOCK_VARIANTS 1024
static uint8_t crc_blocks_1k[CRC_BLOCK_VARIANTS][1024];
static uint8_t crc_blocks_64[CRC_BLOCK_VARIANTS][64];

static void gen_crc_blocks(void) {
    prng_seed(42);
    for (int block = 0; block < CRC_BLOCK_VARIANTS; block++) {
        for (int i = 0; i < 1024; i++) {
            uint8_t byte = (uint8_t)(prng_next() & 0xFF);
            crc_blocks_1k[block][i] = byte;
            if (i < 64) {
                crc_blocks_64[block][i] = byte;
            }
        }
    }
}

static uint64_t bench_crc32_1kb(void) {
    uint64_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++) {
        const uint8_t *block = crc_blocks_1k[i & (CRC_BLOCK_VARIANTS - 1)];
        acc += (uint64_t)crc32_compute(block, 1024) + 1ULL;
    }
    return acc;
}

static uint64_t bench_crc32_streaming_4x256(void) {
    uint64_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++) {
        const uint8_t *block = crc_blocks_1k[i & (CRC_BLOCK_VARIANTS - 1)];
        uint32_t crc = CRC32_INIT;
        for (int c = 0; c < 4; c++) {
            const uint8_t *chunk = block + c * 256;
            for (int j = 0; j < 256; j++)
                crc = crc32_table[(crc ^ chunk[j]) & 0xFF] ^ (crc >> 8);
        }
        acc += (uint64_t)(crc ^ CRC32_INIT) + 1ULL;
    }
    return acc;
}

static uint64_t bench_crc32_byte_at_a_time_64(void) {
    uint64_t acc = 0;
    for (int i = 0; i < NUM_ITER; i++) {
        const uint8_t *block = crc_blocks_64[i & (CRC_BLOCK_VARIANTS - 1)];
        acc += (uint64_t)crc32_compute(block, 64) + 1ULL;
    }
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

    printf("Ring Buffer:\n");
    gen_data(10);
    run_bench("push", bench_ringbuf_push);
    run_bench("pop", bench_ringbuf_pop);
    run_bench("pushForce", bench_ringbuf_pushforce);
    printf("\n");

    printf("CRC-32:\n");
    crc32_init_table();
    gen_crc_blocks();
    run_bench("compute-1KB", bench_crc32_1kb);
    run_bench("streaming-4x256B", bench_crc32_streaming_4x256);
    run_bench("byte-at-a-time-64B", bench_crc32_byte_at_a_time_64);
    printf("\n");

    printf("C Baseline complete.\n");
    return 0;
}
