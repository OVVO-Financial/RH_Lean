/* Explicit main-term subtraction versus window-mean (bridge) subtraction.
 *
 * research/CANONICAL_GAP_PREFIX_GRAM_SCAN.md removes the coherent increment mode by
 * subtracting each sequence's window mean (the Brownian-bridge construction) and
 * finds that at long windows the separate bridge energies still exceed the budget:
 * Q^o_BB/(H N^2) is 0.65, 11.1, 27.5 at [1000,2000), [5000,10000), [10000,20000).
 *
 * That is a statement about mean subtraction.  This program tests the other candidate:
 * subtracting an explicit arithmetic main term rather than an empirical window mean.
 *
 * RESULT: it is much better and still not enough.  At H = N and N = 1000 .. 40000,
 * Q_BB/(H N^2) is
 *
 *   raw           104.75  1232.00  3552.50  11071.62  33339.64    ~ N^1.56
 *   window mean     0.65    11.14    27.50    105.21    266.31    ~ N^1.64
 *   minus Cpred     0.071    0.253    0.973     1.009     4.434    ~ N^1.08
 *
 * All three normalized sequences rise over the tested range. This is a finite
 * route diagnostic, not a proof of asymptotic divergence. Do not read the
 * 0.973 -> 1.009 step as convergence; the next point is 4.434.
 * The main term is the prime-density prediction of the balanced prime-pair count,
 *
 *   Cpred(n) = - sum_{u prime <= n} |W_u(n)| / log(mid W_u(n)),
 *
 * where W_u(n) is the interval of v with u < v < 2u and n^2 <= u v < (n+1)^2.  It
 * carries no Mobius input and does not depend on the window, so unlike the bridge it
 * can track a drift that is not linear across the window.
 *
 * Reports, for each window, Q_BB/(H N^2) and Q_EE/(H N^2) under three treatments:
 * raw, bridge, and minus-Cpred.  Q_tot is unchanged by either subtraction, since
 * whatever is taken from the balanced half is returned to the extreme half.
 *
 * Build: cc -O2 -o main_term_vs_bridge main_term_vs_bridge.c -lm
 * Usage: ./main_term_vs_bridge N H
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

#define SEG (1u << 22)

static uint64_t isqrt_u64(__uint128_t x) {
  uint64_t r = (uint64_t)sqrtl((long double)x);
  while ((__uint128_t)(r + 1) * (r + 1) <= x) r++;
  while ((__uint128_t)r * r > x) r--;
  return r;
}

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s N H\n", argv[0]); return 1; }
  uint64_t N = strtoull(argv[1], NULL, 10);
  uint64_t H = strtoull(argv[2], NULL, 10);
  uint64_t nmax = N + H;                       /* blocks [N, nmax) */
  uint64_t XLO = N * N, XHI = nmax * nmax;     /* sources m in [XLO, XHI) */

  /* primes up to sqrt(XHI), for both the segmented sieve and Cpred */
  uint64_t plim = isqrt_u64((__uint128_t)XHI) + 1;
  char *cs = calloc(plim + 1, 1);
  uint64_t *primes = malloc((plim + 1) * sizeof(uint64_t));
  uint64_t np = 0;
  for (uint64_t i = 2; i <= plim; i++) {
    if (!cs[i]) { primes[np++] = i; for (uint64_t j = i * i; j <= plim; j += i) cs[j] = 1; }
  }

  double *b = calloc(H, sizeof(double));       /* balanced block increments */
  double *e = calloc(H, sizeof(double));       /* extreme  block increments */
  double *cp = calloc(H, sizeof(double));      /* Cpred, the explicit main term */

  int8_t *mu = malloc(SEG);
  uint64_t *prod = malloc(SEG * sizeof(uint64_t));
  uint64_t *lpf = malloc(SEG * sizeof(uint64_t));
  if (!b || !e || !cp || !mu || !prod || !lpf) { fprintf(stderr, "oom\n"); return 1; }

  for (uint64_t lo = XLO; lo < XHI; lo += SEG) {
    uint64_t hi = lo + SEG; if (hi > XHI) hi = XHI;
    uint32_t len = (uint32_t)(hi - lo);
    memset(mu, 1, len);
    for (uint32_t i = 0; i < len; i++) { prod[i] = 1; lpf[i] = 1; }
    for (uint64_t k = 0; k < np; k++) {
      uint64_t p = primes[k];
      if ((__uint128_t)p * p >= hi) break;
      for (uint64_t j = ((lo + p - 1) / p) * p; j < hi; j += p) {
        uint32_t i = (uint32_t)(j - lo);
        mu[i] = (int8_t)-mu[i]; prod[i] *= p; lpf[i] = p;
      }
      __uint128_t pp = (__uint128_t)p * p;
      if (pp < hi) {
        uint64_t p2 = (uint64_t)pp;
        for (uint64_t j = ((lo + p2 - 1) / p2) * p2; j < hi; j += p2) mu[(uint32_t)(j - lo)] = 0;
      }
    }
    for (uint32_t i = 0; i < len; i++) {
      if (!mu[i]) continue;
      uint64_t m = lo + i, q, muv = 0;
      int s = mu[i];
      if (prod[i] != m) { uint64_t r = m / prod[i]; s = -s; q = r > lpf[i] ? r : lpf[i]; }
      else q = lpf[i];
      (void)muv;
      uint64_t c = m / q;
      uint64_t u = c < q ? c : q, v = c < q ? q : c, d = v - u;
      uint64_t n = isqrt_u64((__uint128_t)m);
      if (n < N || n >= nmax) continue;
      if (d > 0 && d < u) b[n - N] += s; else e[n - N] += s;
    }
  }

  /* Cpred: prime-density prediction of the balanced prime-pair count per block */
  for (uint64_t n = N; n < nmax; n++) {
    __uint128_t blo = (__uint128_t)n * n, bhi = (__uint128_t)(n + 1) * (n + 1);
    double s = 0.0;
    for (uint64_t k = 0; k < np; k++) {
      uint64_t u = primes[k];
      if (u > n) break;
      uint64_t vlo = (uint64_t)((blo + u - 1) / u);          /* ceil(n^2 / u) */
      if (u + 1 > vlo) vlo = u + 1;
      uint64_t vhi = (uint64_t)((bhi + u - 1) / u) - 1;      /* ceil((n+1)^2/u) - 1 */
      if (2 * u - 1 < vhi) vhi = 2 * u - 1;
      if (vhi < vlo) continue;
      double mid = 0.5 * ((double)vlo + (double)vhi);
      if (mid > 2.0) s += (double)(vhi - vlo + 1) / log(mid);
    }
    cp[n - N] = -s;
  }

  double budget = (double)H * (double)N * (double)N;
  double *PB = malloc(H * sizeof(double)), *PE = malloc(H * sizeof(double));
  double *QB = malloc(H * sizeof(double)), *QE = malloc(H * sizeof(double));
  double sb = 0, se = 0, sqb = 0, sqe = 0;
  for (uint64_t r = 0; r < H; r++) {
    sb += b[r]; se += e[r];
    sqb += b[r] - cp[r]; sqe += e[r] + cp[r];
    PB[r] = sb; PE[r] = se; QB[r] = sqb; QE[r] = sqe;
  }

  double rawBB = 0, rawEE = 0, tot = 0, briBB = 0, briEE = 0, cpBB = 0, cpEE = 0;
  for (uint64_t r = 0; r < H; r++) {
    rawBB += PB[r] * PB[r]; rawEE += PE[r] * PE[r];
    tot += (PB[r] + PE[r]) * (PB[r] + PE[r]);
    double fb = PB[r] - (double)(r + 1) / (double)H * PB[H - 1];
    double fe = PE[r] - (double)(r + 1) / (double)H * PE[H - 1];
    briBB += fb * fb; briEE += fe * fe;
    cpBB += QB[r] * QB[r]; cpEE += QE[r] * QE[r];
  }

  printf("window [%llu,%llu)  H/N = %.2f   sources m in [%llu,%llu)\n",
         (unsigned long long)N, (unsigned long long)nmax, (double)H / (double)N,
         (unsigned long long)XLO, (unsigned long long)XHI);
  printf("  Q_tot/(H N^2)                  = %12.5f\n", tot / budget);
  printf("  raw            Q_BB = %12.4f   Q_EE = %12.4f\n", rawBB / budget, rawEE / budget);
  printf("  bridge (mean)  Q_BB = %12.4f   Q_EE = %12.4f\n", briBB / budget, briEE / budget);
  printf("  minus Cpred    Q_BB = %12.4f   Q_EE = %12.4f\n", cpBB / budget, cpEE / budget);
  fflush(stdout);
  return 0;
}
