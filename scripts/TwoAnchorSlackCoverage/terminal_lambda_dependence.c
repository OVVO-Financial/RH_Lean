/* Does the cutoff Lambda buy anything in the terminal statement?
 *
 * ProjectedRenewalQuadraticBoundedStatement(Lambda) is equivalent to
 * CanonicalHighUniformLocalBoundedStatement(Lambda), which unfolds to
 *
 *   localSequenceEnergy (canonicalHighPrefix Lambda) N H  <=  C H N^(2+eps),
 *
 * where localSequenceEnergy f N H = sum_{h<H} |f(N+h)|^2 and canonicalHighPrefix is
 * the GLOBAL prefix from block 0:
 *
 *   S^high_n(Lambda) = sum_{j<=n} sum_{m in [j^2,(j+1)^2), |2Y_m| > 2 Lambda j} mu(m).
 *
 * Note this is the global prefix, not the window-local one used by
 * prefix_gram_cross.c and main_term_vs_bridge.c.  The two differ by the offset
 * S^high_{N-1}, and the RH-strength content sits in that offset.  This program
 * measures the actual terminal quantity.
 *
 * The question: the project proved an unconditional low-band counting theorem
 * (SignedCanonicalHeight.card_le), which gives |d_n^low| <= 1 + floor(Lambda) and hence
 * |S^low_n| = O(Lambda n).  Since the target allows n^{1+eps}, that band is already
 * harmless.  So does raising Lambda -- removing more low-height mass -- actually reduce
 * the constant in the terminal estimate, or is the difficulty Lambda-independent?
 *
 * Predeclared reading:
 *   - if the ratio falls substantially with Lambda, the low/high split is buying
 *     something for the terminal estimate and Lambda is a real parameter to tune;
 *   - if the ratio is essentially flat in Lambda, the split buys nothing here;
 *   - if the ratio rises, larger cutoffs are counterproductive on the tested range.
 * In either non-improving branch, the counting theorem does not reduce the remaining
 * difficulty and effort on low-band refinement should stop absent a new mechanism.
 *
 * Build: cc -O2 -o terminal_lambda_dependence terminal_lambda_dependence.c -lm
 * Usage: ./terminal_lambda_dependence N H
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

#define SEG (1u << 22)
#define NLAM 6
static const double LAMBDAS[NLAM] = {0.0, 1.0, 2.0, 5.0, 10.0, 25.0};

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
  uint64_t nmax = N + H;
  uint64_t XHI = nmax * nmax;              /* need every source from 1: global prefix */

  uint64_t plim = isqrt_u64((__uint128_t)XHI) + 1;
  char *cs = calloc(plim + 1, 1);
  uint64_t *primes = malloc((plim + 1) * sizeof(uint64_t));
  uint64_t np = 0;
  for (uint64_t i = 2; i <= plim; i++)
    if (!cs[i]) { primes[np++] = i; for (uint64_t j = i * i; j <= plim; j += i) cs[j] = 1; }

  /* per-block high increments, one array per Lambda */
  double *incr[NLAM];
  for (int k = 0; k < NLAM; k++) incr[k] = calloc(nmax + 1, sizeof(double));

  int8_t *mu = malloc(SEG);
  uint64_t *prod = malloc(SEG * sizeof(uint64_t));
  uint64_t *lpf = malloc(SEG * sizeof(uint64_t));
  if (!mu || !prod || !lpf) { fprintf(stderr, "oom\n"); return 1; }

  for (uint64_t lo = 1; lo < XHI; lo += SEG) {
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
        for (uint64_t j = ((lo + p2 - 1) / p2) * p2; j < hi; j += p2)
          mu[(uint32_t)(j - lo)] = 0;
      }
    }
    for (uint32_t i = 0; i < len; i++) {
      if (!mu[i]) continue;
      uint64_t m = lo + i, q;
      int s = mu[i];
      if (m == 1) continue;
      if (prod[i] != m) { uint64_t r = m / prod[i]; s = -s; q = r > lpf[i] ? r : lpf[i]; }
      else q = lpf[i];
      uint64_t c = m / q;
      uint64_t u = c < q ? c : q, v = c < q ? q : c, d = v - u;
      uint64_t n = isqrt_u64((__uint128_t)m);
      if (n > nmax) continue;
      double h2 = (double)d * (double)(u + v);        /* |2 Y_m| */
      for (int k = 0; k < NLAM; k++)
        if (h2 > 2.0 * LAMBDAS[k] * (double)n) incr[k][n] += s;
    }
  }

  double budget = (double)H * (double)N * (double)N;
  printf("window [%llu,%llu)  H/N = %.2f   GLOBAL prefix (the terminal quantity)\n",
         (unsigned long long)N, (unsigned long long)nmax, (double)H / (double)N);
  printf("  %8s %16s %14s %12s\n", "Lambda", "Q/(H N^2)", "max|S^high|/N", "sources kept");
  for (int k = 0; k < NLAM; k++) {
    double S = 0.0, Q = 0.0, worst = 0.0;
    long long kept = 0;
    for (uint64_t n = 0; n <= nmax; n++) {
      S += incr[k][n];
      kept += (long long)llabs((long long)incr[k][n]);
      if (n >= N && n < nmax) Q += S * S;
      if (n >= N && fabs(S) / (double)n > worst) worst = fabs(S) / (double)n;
    }
    printf("  %8.1f %16.5f %14.5f %12lld\n", LAMBDAS[k], Q / budget, worst, kept);
  }
  return 0;
}
