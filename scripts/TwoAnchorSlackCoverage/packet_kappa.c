/* kappa diagnostics for the dyadic (p,q) prime-packet decomposition.
 *
 * Packet coordinates follow CanonicalGapAncestryPrimePacketScales:
 *
 *   q = P+(m)  the distinguished prime,   k = Nat.log 2 q
 *   c = m/q    the core,                  p = P+(c),   j = Nat.log 2 p
 *
 * with j <= k giving the triangular support.  Every squarefree m lands in exactly
 * one packet, so the packet prefixes sum to the full square-block Mobius prefix --
 * the terminal quantity at Lambda = 0.  Prefixes are GLOBAL (from block 0), matching
 * localSequenceEnergy (canonicalHighPrefix 0).
 *
 * Reports, on the window of blocks [N, N+H):
 *
 *   kappa_raw = sum_{j,k} ||Z_{j,k}||^2  /  ||sum Z||^2       full packet square function
 *   kappa_q   = sum_k     ||Y_k||^2      /  ||sum Y||^2       Y_k = sum_j Z_{j,k}
 *
 * A positive square-function strategy needs kappa << N^eps.  By the exact identity
 *
 *   2 sum_{a<b} <Z_a,Z_b> / D  =  1/kappa - 1,
 *
 * a large kappa means the aggregate cross term sits near -D/2, i.e. the decomposition
 * is cancellation-dominated and a positive diagonal bound discards the cancellation
 * responsible for the small target.
 *
 * Finite data cannot disprove kappa <<_eps N^eps -- constants absorb any finite range.
 * These are route-falsification diagnostics under the repository's predeclared
 * standard, not theorems.
 *
 * Build: cc -O2 -o packet_kappa packet_kappa.c -lm
 * Usage: ./packet_kappa N H
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

#define SEG (1u << 22)
#define MAXS 40                     /* dyadic scales; log2(6.4e9) < 33 */

static uint64_t isqrt_u64(__uint128_t x) {
  uint64_t r = (uint64_t)sqrtl((long double)x);
  while ((__uint128_t)(r + 1) * (r + 1) <= x) r++;
  while ((__uint128_t)r * r > x) r--;
  return r;
}

static int ilog2_u64(uint64_t v) { int s = 0; while (v > 1) { v >>= 1; s++; } return s; }

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s N H\n", argv[0]); return 1; }
  uint64_t N = strtoull(argv[1], NULL, 10);
  uint64_t H = strtoull(argv[2], NULL, 10);
  uint64_t nmax = N + H, XHI = nmax * nmax;

  uint64_t plim = isqrt_u64((__uint128_t)XHI) + 1;
  char *cs = calloc(plim + 1, 1);
  uint64_t *primes = malloc((plim + 1) * sizeof(uint64_t));
  uint64_t np = 0;
  for (uint64_t i = 2; i <= plim; i++)
    if (!cs[i]) { primes[np++] = i; for (uint64_t t = i * i; t <= plim; t += i) cs[t] = 1; }

  /* per-packet per-block increments, flattened [j][k][n] */
  size_t nb = (size_t)nmax + 1;
  size_t npk = (size_t)MAXS * MAXS;
  float *incr = calloc(npk * nb, sizeof(float));
  if (!incr) { fprintf(stderr, "oom: need %.1f MB\n", npk * nb * 4.0 / 1e6); return 1; }

  int8_t *mu = malloc(SEG);
  uint64_t *prod = malloc(SEG * sizeof(uint64_t));
  uint64_t *lpf = malloc(SEG * sizeof(uint64_t));

  for (uint64_t lo = 1; lo < XHI; lo += SEG) {
    uint64_t hi = lo + SEG; if (hi > XHI) hi = XHI;
    uint32_t len = (uint32_t)(hi - lo);
    memset(mu, 1, len);
    for (uint32_t i = 0; i < len; i++) { prod[i] = 1; lpf[i] = 1; }
    for (uint64_t t = 0; t < np; t++) {
      uint64_t p = primes[t];
      if ((__uint128_t)p * p >= hi) break;
      for (uint64_t x = ((lo + p - 1) / p) * p; x < hi; x += p) {
        uint32_t i = (uint32_t)(x - lo);
        mu[i] = (int8_t)-mu[i]; prod[i] *= p; lpf[i] = p;
      }
      __uint128_t pp = (__uint128_t)p * p;
      if (pp < hi) {
        uint64_t p2 = (uint64_t)pp;
        for (uint64_t x = ((lo + p2 - 1) / p2) * p2; x < hi; x += p2)
          mu[(uint32_t)(x - lo)] = 0;
      }
    }
    for (uint32_t i = 0; i < len; i++) {
      if (!mu[i]) continue;
      uint64_t m = lo + i;
      if (m == 1) continue;
      int s = mu[i];
      uint64_t q;
      if (prod[i] != m) { uint64_t r = m / prod[i]; s = -s; q = r > lpf[i] ? r : lpf[i]; }
      else q = lpf[i];
      uint64_t c = m / q;
      /* p = P+(c), by trial division over the sieve primes (c is squarefree) */
      uint64_t pp2 = 1, t2 = c;
      for (uint64_t t = 0; t < np && primes[t] * primes[t] <= t2; t++)
        while (t2 % primes[t] == 0) { pp2 = primes[t]; t2 /= primes[t]; }
      if (t2 > 1) pp2 = t2;
      int k = ilog2_u64(q), j = ilog2_u64(pp2 < 1 ? 1 : pp2);
      if (k >= MAXS) k = MAXS - 1;
      if (j >= MAXS) j = MAXS - 1;
      uint64_t n = isqrt_u64((__uint128_t)m);
      if (n > nmax) continue;
      incr[((size_t)j * MAXS + k) * nb + n] += (float)s;
    }
  }

  double budget = (double)H * (double)N * (double)N;
  /* global prefixes; accumulate energy on [N, N+H) */
  double Draw = 0.0, Dq = 0.0, Etot = 0.0;
  int live = 0;
  double *Yk = calloc(MAXS * nb, sizeof(double));       /* q-fibre increments */
  double *tot = calloc(nb, sizeof(double));

  for (size_t j = 0; j < MAXS; j++)
    for (size_t k = 0; k < MAXS; k++) {
      float *a = incr + ((size_t)j * MAXS + k) * nb;
      double S = 0.0, E = 0.0; int any = 0;
      for (size_t n = 0; n < nb; n++) {
        S += a[n];
        if (a[n] != 0.0f) any = 1;
        Yk[k * nb + n] += a[n];
        tot[n] += a[n];
        if (n >= N) E += S * S;
      }
      if (any) { live++; Draw += E; }
    }
  for (size_t k = 0; k < MAXS; k++) {
    double S = 0.0, E = 0.0; int any = 0;
    for (size_t n = 0; n < nb; n++) {
      S += Yk[k * nb + n];
      if (Yk[k * nb + n] != 0.0) any = 1;
      if (n >= N) E += S * S;
    }
    if (any) Dq += E;
  }
  { double S = 0.0; for (size_t n = 0; n < nb; n++) { S += tot[n]; if (n >= N) Etot += S * S; } }

  printf("window [%llu,%llu)  H/N = %.2f   global prefixes, Lambda = 0\n",
         (unsigned long long)N, (unsigned long long)nmax, (double)H / (double)N);
  printf("  live (j,k) packets           : %d   (bound log2(B)^2 ~ %d)\n",
         live, ilog2_u64(XHI) * ilog2_u64(XHI));
  printf("  ||sum Z||^2 / (H N^2)        : %12.5f\n", Etot / budget);
  printf("  D_raw / (H N^2)              : %12.5f\n", Draw / budget);
  printf("  D_q   / (H N^2)              : %12.5f\n", Dq / budget);
  printf("  kappa_raw = D_raw / E        : %12.2f   cross/D = %+.4f\n",
         Draw / Etot, Etot / Draw - 1.0);
  printf("  kappa_q   = D_q   / E        : %12.2f   cross/D = %+.4f\n",
         Dq / Etot, Etot / Dq - 1.0);
  return 0;
}
