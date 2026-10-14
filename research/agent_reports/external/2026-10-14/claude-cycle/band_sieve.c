// Exact prime counts in open square bands (R^2, (R+1)^2) for R = 1..RMAX.
// Odd-only segmented sieve of Eratosthenes, two threads, integer arithmetic only.
// Output: binary uint32 array P[0..RMAX] (P[0] unused) to argv[2].
// Usage: band_sieve RMAX out.bin
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <pthread.h>

static uint64_t RMAX, NMAX;            // NMAX = (RMAX+1)^2
static uint32_t *small_primes; static size_t n_small;

static uint64_t isqrt64(uint64_t n) {
    uint64_t r = (uint64_t)sqrtl((long double)n);
    while (r * r > n) r--;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

typedef struct { uint64_t lo, hi; uint32_t *counts; uint64_t total; } job_t;

#define SEG (1u << 19)   // odd numbers per segment (covers 2^20 integers)

static void *worker(void *arg) {
    job_t *J = (job_t *)arg;
    uint8_t *seg = malloc(SEG);
    // n ranges over odd numbers in [lo, hi), lo odd.
    uint64_t lo = J->lo | 1ULL;
    uint64_t R = isqrt64(lo);
    uint64_t next_sq = (R + 1) * (R + 1);
    for (uint64_t base = lo; base < J->hi; base += 2ULL * SEG) {
        uint64_t top = base + 2ULL * SEG; if (top > J->hi) top = J->hi;
        uint64_t len = (top - base + 1) / 2;   // odd numbers base, base+2, ...
        memset(seg, 1, len);
        for (size_t k = 0; k < n_small; k++) {
            uint64_t p = small_primes[k];
            if (p * p >= top) break;
            uint64_t start = p * p;
            if (start < base) {
                uint64_t m = (base + p - 1) / p * p;   // first multiple >= base
                if ((m & 1ULL) == 0) m += p;           // make it odd
                start = m;
            }
            for (uint64_t n = start; n < top; n += 2 * p) seg[(n - base) >> 1] = 0;
        }
        for (uint64_t i = 0; i < len; i++) {
            uint64_t n = base + 2 * i;
            if (n >= next_sq) { while (n >= next_sq) { R++; next_sq = (R + 1) * (R + 1); } }
            if (seg[i] && n > 1) {
                if (R <= RMAX) J->counts[R]++;
                J->total++;
            }
        }
    }
    free(seg);
    return NULL;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage\n"); return 1; }
    RMAX = strtoull(argv[1], 0, 10);
    NMAX = (RMAX + 1) * (RMAX + 1);
    uint64_t lim = isqrt64(NMAX) + 1;
    uint8_t *s = calloc(lim + 1, 1);
    small_primes = malloc(sizeof(uint32_t) * (lim / 2 + 10)); n_small = 0;
    for (uint64_t i = 2; i <= lim; i++) {
        if (!s[i]) { if (i > 2) small_primes[n_small++] = (uint32_t)i; for (uint64_t j = i * i; j <= lim; j += i) s[j] = 1; }
    }
    free(s);
    // split [3, NMAX) into two halves aligned to even boundaries
    uint64_t mid = (3 + NMAX) / 2; mid |= 1ULL;
    job_t J[2];
    J[0].lo = 3; J[0].hi = mid; J[1].lo = mid; J[1].hi = NMAX;
    for (int t = 0; t < 2; t++) { J[t].counts = calloc(RMAX + 2, sizeof(uint32_t)); J[t].total = 0; }
    pthread_t th[2];
    for (int t = 0; t < 2; t++) pthread_create(&th[t], 0, worker, &J[t]);
    for (int t = 0; t < 2; t++) pthread_join(th[t], 0);
    uint32_t *P = calloc(RMAX + 2, sizeof(uint32_t));
    for (uint64_t r = 0; r <= RMAX; r++) P[r] = J[0].counts[r] + J[1].counts[r];
    // prime 2 lies in band R=1: (1,4) contains 2 and 3. Add the even prime.
    P[1] += 1;
    uint64_t pi_total = 1 + J[0].total + J[1].total;  // includes 2
    FILE *f = fopen(argv[2], "wb"); fwrite(P, sizeof(uint32_t), RMAX + 1, f); fclose(f);
    printf("RMAX=%llu NMAX=%llu pi(NMAX-1)=%llu\n", (unsigned long long)RMAX,
           (unsigned long long)NMAX, (unsigned long long)pi_total);
    return 0;
}
