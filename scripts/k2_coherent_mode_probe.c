/* Finite coherent-mode probe for the signed second-Selberg kernel
 *
 *   K2(n) = (Lambda * Lambda)(n) - Lambda(n) log n.
 *
 * Support:
 *   K2(p^a)       = -(log p)^2
 *   K2(p^a q^b)   =  2 log p log q
 * and zero elsewhere.
 *
 * The compiled identity in
 * RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourBridge is
 *
 *   sum_{n<=x} K2(n) = -2 (psi(x) - x) log x + O(x).
 *
 * This program checks the next-order centering
 *
 *   sum_{n<=x} K2(n) + 2 gamma x   ~   -2 log x (psi(x) - x)
 *
 * by a Pearson regression on sample points from XMIN to N.
 * Default range: 10^4 .. 2*10^7.  Diagnostic only; not a proof.
 *
 * Build: cc -O2 -o k2_coherent_mode_probe scripts/k2_coherent_mode_probe.c -lm
 * Usage: ./k2_coherent_mode_probe [N=20000000] [XMIN=10000]
 */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifndef M_GAMMA
#define M_GAMMA 0.5772156649015328606
#endif

int main(int argc, char **argv) {
  uint64_t N = 20000000ull;
  uint64_t xmin = 10000ull;
  if (argc >= 2) N = strtoull(argv[1], NULL, 10);
  if (argc >= 3) xmin = strtoull(argv[2], NULL, 10);
  if (N < 3 || xmin < 2 || xmin > N) {
    fprintf(stderr, "usage: %s [N] [XMIN]  with 2 <= XMIN <= N\n", argv[0]);
    return 1;
  }

  /* lpf sieve */
  uint32_t *lpf = calloc((size_t)N + 1, sizeof(uint32_t));
  if (!lpf) {
    fprintf(stderr, "oom\n");
    return 1;
  }
  uint32_t *primes = malloc(((size_t)N / 5 + 16) * sizeof(uint32_t));
  if (!primes) {
    fprintf(stderr, "oom\n");
    return 1;
  }
  uint64_t np = 0;
  for (uint64_t i = 2; i <= N; i++) {
    if (lpf[i] == 0) {
      lpf[i] = (uint32_t)i;
      primes[np++] = (uint32_t)i;
    }
    for (uint64_t j = 0; j < np; j++) {
      uint64_t p = primes[j];
      uint64_t v = i * p;
      if (v > N) break;
      lpf[v] = (uint32_t)p;
      if (i % p == 0) break;
    }
  }

  /* Running psi and K2.  Record a sample every step = max(1, N/2000)
   * starting at xmin, plus the endpoint. */
  uint64_t step = N / 2000;
  if (step < 1) step = 1;

  uint64_t nsample_max = (N - xmin) / step + 8;
  double *xs = malloc(nsample_max * sizeof(double));
  double *lhs = malloc(nsample_max * sizeof(double));
  double *rhs = malloc(nsample_max * sizeof(double));
  if (!xs || !lhs || !rhs) {
    fprintf(stderr, "oom\n");
    return 1;
  }

  double psi = 0.0;
  double k2 = 0.0;
  uint64_t ns = 0;
  uint64_t next_sample = xmin;

  printf("# K2 coherent-mode probe   N=%llu  xmin=%llu  samples every %llu\n",
         (unsigned long long)N, (unsigned long long)xmin,
         (unsigned long long)step);
  printf("# columns: x  S=sum K2  S+2g x  -2 log x (psi-x)  (S+2gx)/x  "
         "(S + 2 E log x)/x\n");

  for (uint64_t n = 2; n <= N; n++) {
    uint64_t m = n;
    uint32_t p = lpf[m];
    while (m % p == 0) m /= p;
    if (m == 1) {
      /* n = p^a */
      double lp = log((double)p);
      psi += lp;
      k2 -= lp * lp;
    } else {
      uint32_t q = lpf[m];
      while (m % q == 0) m /= q;
      if (m == 1 && q != p) {
        /* n = p^a q^b */
        double lp = log((double)p);
        double lq = log((double)q);
        k2 += 2.0 * lp * lq;
      }
    }

    if (n == next_sample || n == N) {
      double x = (double)n;
      double E = psi - x;
      double lx = log(x);
      double centered = k2 + 2.0 * M_GAMMA * x;
      double target = -2.0 * lx * E;
      double raw_resid = (k2 + 2.0 * E * lx) / x;
      printf("%llu  %.6f  %.6f  %.6f  %.6f  %.6f\n",
             (unsigned long long)n, k2, centered, target, centered / x,
             raw_resid);
      if (n >= xmin) {
        xs[ns] = x;
        lhs[ns] = centered;
        rhs[ns] = target;
        ns++;
      }
      if (n == next_sample) {
        next_sample += step;
        if (next_sample > N) next_sample = N;
      }
    }
  }

  /* Pearson correlation of (S+2 gamma x) against -2 log x (psi-x). */
  double mx = 0.0, my = 0.0;
  for (uint64_t i = 0; i < ns; i++) {
    mx += lhs[i];
    my += rhs[i];
  }
  mx /= (double)ns;
  my /= (double)ns;
  double num = 0.0, vx = 0.0, vy = 0.0;
  for (uint64_t i = 0; i < ns; i++) {
    double dx = lhs[i] - mx;
    double dy = rhs[i] - my;
    num += dx * dy;
    vx += dx * dx;
    vy += dy * dy;
  }
  double corr = num / sqrt(vx * vy);

  /* OLS slope: lhs ~ a + b rhs, expect b ~ 1. */
  double bhat = num / vy;
  double ahat = mx - bhat * my;

  printf("# samples=%llu  pearson(S+2gamma x, -2 log x (psi-x)) = %.6f\n",
         (unsigned long long)ns, corr);
  printf("# OLS: S+2gamma x = %.6f + %.6f * (-2 log x (psi-x))\n", ahat, bhat);
  printf("# last x=%llu  psi-x=%.6f  (S + 2 E log x)/x = %.6f\n",
         (unsigned long long)N, psi - (double)N,
         (k2 + 2.0 * (psi - (double)N) * log((double)N)) / (double)N);

  free(lpf);
  free(primes);
  free(xs);
  free(lhs);
  free(rhs);
  return 0;
}
