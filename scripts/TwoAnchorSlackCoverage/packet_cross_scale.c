/* Exact cross-scale cancellation diagnostics for the dyadic q-fibres.
 *
 * For each squarefree m, let q = P+(m), k = floor(log_2 q), and place mu(m)
 * in square block n = floor(sqrt(m)).  The global q-fibre prefix is
 *
 *   F_k(n) = sum_{m < (n+1)^2, floor(log_2 P+(m)) = k} mu(m).
 *
 * On the window n in [N, N+H), this program forms the exact integer Gram matrix
 *
 *   G_{k,l} = sum_n F_k(n) F_l(n),
 *   D = sum_k G_{k,k},
 *   E = sum_{k,l} G_{k,l} = ||sum_k F_k||_2^2.
 *
 * The locality diagnostic uses the unambiguous unordered-pair convention
 *
 *   eta_w = -2 sum_{k<l, l-k <= w} G_{k,l} / (D-E),
 *
 * so eta_w = 1 at full width whenever D != E.
 *
 * The gatekeeper-aware top-row diagnostic uses the dynamic top scale
 *
 *   k_top(n) = floor(log_2 ((n+1)^2 - 1))
 *
 * and
 *
 *   theta_w = -2 sum_n sum_{0<|l-k_top(n)|<=w}
 *                 F_{k_top(n)}(n) F_l(n)
 *             / sum_n F_{k_top(n)}(n)^2.
 *
 * theta_share_w divides the same numerator by its full-width value, measuring
 * geometric localization of the observed top-row cancellation independently of
 * how much of the top diagonal is cancelled in total.
 *
 * All increments, prefixes, Gram entries, and cumulative cancellation masses are
 * computed with integer arithmetic.  __int128 is used for quadratic sums.
 *
 * The program also audits the merged Lean gatekeeper numerically on every window
 * point by checking that the dynamic top fibre equals the pure prime contribution
 * in that scale.
 *
 * Build: cc -O3 -std=c11 -Wall -Wextra -o packet_cross_scale packet_cross_scale.c -lm
 * Usage: ./packet_cross_scale N H
 */

#include <errno.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SEG (1u << 22)
#define MAXS 40
#define I128_BUF 96

static uint64_t isqrt_u128(__uint128_t x) {
  uint64_t r = (uint64_t)sqrtl((long double)x);
  while ((__uint128_t)(r + 1) * (r + 1) <= x) r++;
  while ((__uint128_t)r * r > x) r--;
  return r;
}

static int ilog2_u64(uint64_t v) {
  int s = 0;
  while (v > 1) {
    v >>= 1;
    s++;
  }
  return s;
}

static void i128_to_string(__int128 x, char out[I128_BUF]) {
  char tmp[I128_BUF];
  size_t p = 0;
  int neg = x < 0;
  __uint128_t u = neg ? (__uint128_t)(-x) : (__uint128_t)x;
  if (u == 0) {
    strcpy(out, "0");
    return;
  }
  while (u > 0 && p + 1 < sizeof(tmp)) {
    tmp[p++] = (char)('0' + (u % 10));
    u /= 10;
  }
  size_t q = 0;
  if (neg) out[q++] = '-';
  while (p > 0) out[q++] = tmp[--p];
  out[q] = '\0';
}

static long double i128_to_ld(__int128 x) {
  return (long double)x;
}

static long double ratio128(__int128 a, __int128 b) {
  if (b == 0) return NAN;
  return i128_to_ld(a) / i128_to_ld(b);
}

static void *xcalloc(size_t n, size_t z, const char *what) {
  void *p = calloc(n, z);
  if (!p) {
    fprintf(stderr, "oom allocating %s (%zu bytes)\n", what, n * z);
    exit(2);
  }
  return p;
}

static void *xmalloc(size_t n, const char *what) {
  void *p = malloc(n);
  if (!p) {
    fprintf(stderr, "oom allocating %s (%zu bytes)\n", what, n);
    exit(2);
  }
  return p;
}

struct OffsetContribution {
  int delta;
  __int128 mass;
};

static int compare_offset_desc(const void *aa, const void *bb) {
  const struct OffsetContribution *a = (const struct OffsetContribution *)aa;
  const struct OffsetContribution *b = (const struct OffsetContribution *)bb;
  long double av = fabsl(i128_to_ld(a->mass));
  long double bv = fabsl(i128_to_ld(b->mass));
  if (av < bv) return 1;
  if (av > bv) return -1;
  return a->delta - b->delta;
}

static int first_width_at(const long double *v, int maxw, long double target) {
  for (int w = 1; w <= maxw; w++)
    if (v[w] >= target) return w;
  return -1;
}

static int stable_width_within(const long double *v, int maxw, long double center,
                               long double tol) {
  for (int w = 1; w <= maxw; w++) {
    int ok = 1;
    for (int u = w; u <= maxw; u++) {
      if (!isfinite(v[u]) || fabsl(v[u] - center) > tol) {
        ok = 0;
        break;
      }
    }
    if (ok) return w;
  }
  return -1;
}

static __int128 abs128(__int128 x) { return x < 0 ? -x : x; }

static int block_id(int k, int width, int phase) {
  return (k + phase) / width;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s N H\n", argv[0]);
    return 1;
  }
  errno = 0;
  uint64_t N = strtoull(argv[1], NULL, 10);
  uint64_t H = strtoull(argv[2], NULL, 10);
  if (errno || H == 0 || N + H < N) {
    fprintf(stderr, "invalid N or H\n");
    return 1;
  }
  uint64_t nmax = N + H;
  __uint128_t xhi128 = (__uint128_t)nmax * nmax;
  if (xhi128 > UINT64_MAX) {
    fprintf(stderr, "(N+H)^2 exceeds uint64_t\n");
    return 1;
  }
  uint64_t XHI = (uint64_t)xhi128;
  size_t nb = (size_t)nmax + 1;

  uint64_t plim = isqrt_u128(XHI) + 1;
  char *composite = xcalloc(plim + 1, 1, "prime sieve");
  uint64_t *primes = xmalloc((plim + 1) * sizeof(uint64_t), "prime list");
  uint64_t np = 0;
  for (uint64_t i = 2; i <= plim; i++) {
    if (!composite[i]) {
      primes[np++] = i;
      if (i <= plim / i)
        for (uint64_t t = i * i; t <= plim; t += i) composite[t] = 1;
    }
  }

  int32_t *qinc = xcalloc((size_t)MAXS * nb, sizeof(int32_t), "q increments");
  int32_t *primeinc = xcalloc((size_t)MAXS * nb, sizeof(int32_t), "prime increments");
  int8_t *mu = xmalloc(SEG * sizeof(int8_t), "segmented mu");
  uint64_t *prod = xmalloc((size_t)SEG * sizeof(uint64_t), "segmented product");
  uint64_t *lpf = xmalloc((size_t)SEG * sizeof(uint64_t), "segmented lpf");

  for (uint64_t lo = 1; lo < XHI; lo += SEG) {
    uint64_t hi = lo + SEG;
    if (hi > XHI) hi = XHI;
    uint32_t len = (uint32_t)(hi - lo);
    memset(mu, 1, len * sizeof(int8_t));
    for (uint32_t i = 0; i < len; i++) {
      prod[i] = 1;
      lpf[i] = 1;
    }
    for (uint64_t t = 0; t < np; t++) {
      uint64_t p = primes[t];
      if ((__uint128_t)p * p >= hi) break;
      uint64_t first = ((lo + p - 1) / p) * p;
      for (uint64_t x = first; x < hi; x += p) {
        uint32_t i = (uint32_t)(x - lo);
        mu[i] = (int8_t)-mu[i];
        prod[i] *= p;
        lpf[i] = p;
      }
      __uint128_t pp = (__uint128_t)p * p;
      if (pp < hi) {
        uint64_t p2 = (uint64_t)pp;
        uint64_t first2 = ((lo + p2 - 1) / p2) * p2;
        for (uint64_t x = first2; x < hi; x += p2)
          mu[(uint32_t)(x - lo)] = 0;
      }
    }

    for (uint32_t i = 0; i < len; i++) {
      if (mu[i] == 0) continue;
      uint64_t m = lo + i;
      if (m == 1) continue;
      int s = mu[i];
      uint64_t q;
      if (prod[i] != m) {
        uint64_t r = m / prod[i];
        s = -s;
        q = r > lpf[i] ? r : lpf[i];
      } else {
        q = lpf[i];
      }
      uint64_t c = m / q;
      int k = ilog2_u64(q);
      if (k >= MAXS) k = MAXS - 1;
      uint64_t n = isqrt_u128(m);
      if (n >= nmax) continue;
      qinc[(size_t)k * nb + n] += (int32_t)s;
      if (c == 1) primeinc[(size_t)k * nb + n] += (int32_t)s;
    }
  }

  int64_t *path = xcalloc((size_t)MAXS * (size_t)H, sizeof(int64_t), "window paths");
  int64_t *primepath = xcalloc((size_t)MAXS * (size_t)H, sizeof(int64_t), "prime paths");
  int live[MAXS] = {0};
  int kmin = MAXS, kmax = -1;
  int64_t qprefix[MAXS] = {0};
  int64_t pprefix[MAXS] = {0};

  for (uint64_t n = 0; n < nmax; n++) {
    for (int k = 0; k < MAXS; k++) {
      int32_t qi = qinc[(size_t)k * nb + n];
      int32_t pi = primeinc[(size_t)k * nb + n];
      qprefix[k] += qi;
      pprefix[k] += pi;
      if (qi != 0) {
        live[k] = 1;
        if (k < kmin) kmin = k;
        if (k > kmax) kmax = k;
      }
      if (n >= N) {
        size_t r = (size_t)(n - N);
        path[(size_t)k * H + r] = qprefix[k];
        primepath[(size_t)k * H + r] = pprefix[k];
      }
    }
  }

  if (kmax < 0) {
    fprintf(stderr, "no live q scales\n");
    return 3;
  }

  __int128 G[MAXS][MAXS];
  memset(G, 0, sizeof(G));
  __int128 E_direct = 0;
  __int128 D = 0;
  __int128 topDiag = 0;
  __int128 topByOffset[2 * MAXS + 1];
  memset(topByOffset, 0, sizeof(topByOffset));
  uint64_t topAuditFailures = 0;
  uint64_t topAuditFirstN = 0;
  int64_t topAuditGot = 0, topAuditExpected = 0;
  long double maxAbsFOverN = 0.0L;
  int argK = 0;
  uint64_t argN = N;

  for (uint64_t r = 0; r < H; r++) {
    __int128 total = 0;
    for (int k = 0; k < MAXS; k++) {
      int64_t vk = path[(size_t)k * H + r];
      total += vk;
      uint64_t n = N + r;
      long double norm = n == 0 ? fabsl((long double)vk) : fabsl((long double)vk) / n;
      if (norm > maxAbsFOverN) {
        maxAbsFOverN = norm;
        argK = k;
        argN = n;
      }
      for (int l = k; l < MAXS; l++) {
        int64_t vl = path[(size_t)l * H + r];
        G[k][l] += (__int128)vk * vl;
      }
    }
    E_direct += total * total;

    uint64_t n = N + r;
    uint64_t endpoint = (n + 1) * (n + 1) - 1;
    int kt = ilog2_u64(endpoint);
    int64_t ft = path[(size_t)kt * H + r];
    int64_t pt = primepath[(size_t)kt * H + r];
    if (ft != pt) {
      if (topAuditFailures == 0) {
        topAuditFirstN = n;
        topAuditGot = ft;
        topAuditExpected = pt;
      }
      topAuditFailures++;
    }
    topDiag += (__int128)ft * ft;
    for (int l = 0; l < MAXS; l++) {
      if (l == kt) continue;
      int delta = l - kt;
      topByOffset[delta + MAXS] += -2 * (__int128)ft * path[(size_t)l * H + r];
    }
  }

  for (int k = 0; k < MAXS; k++) {
    D += G[k][k];
    for (int l = k + 1; l < MAXS; l++) G[l][k] = G[k][l];
  }
  __int128 E_from_gram = D;
  __int128 byDist[MAXS];
  memset(byDist, 0, sizeof(byDist));
  for (int k = 0; k < MAXS; k++) {
    for (int l = k + 1; l < MAXS; l++) {
      E_from_gram += 2 * G[k][l];
      byDist[l - k] += -2 * G[k][l];
    }
  }

  __int128 globalNeed = D - E_from_gram;
  __int128 topFull = 0;
  __int128 topByDist[MAXS];
  memset(topByDist, 0, sizeof(topByDist));
  for (int delta = -MAXS + 1; delta <= MAXS - 1; delta++) {
    if (delta == 0) continue;
    __int128 m = topByOffset[delta + MAXS];
    topFull += m;
    int d = delta < 0 ? -delta : delta;
    topByDist[d] += m;
  }

  long double eta[MAXS];
  long double theta[MAXS];
  long double thetaShare[MAXS];
  memset(eta, 0, sizeof(eta));
  memset(theta, 0, sizeof(theta));
  memset(thetaShare, 0, sizeof(thetaShare));
  __int128 cumGlobal = 0;
  __int128 cumTop = 0;
  for (int w = 1; w < MAXS; w++) {
    cumGlobal += byDist[w];
    cumTop += topByDist[w];
    eta[w] = ratio128(cumGlobal, globalNeed);
    theta[w] = ratio128(cumTop, topDiag);
    thetaShare[w] = ratio128(cumTop, topFull);
  }

  int w50 = first_width_at(eta, MAXS - 1, 0.50L);
  int w90 = first_width_at(eta, MAXS - 1, 0.90L);
  int w99 = first_width_at(eta, MAXS - 1, 0.99L);
  int tw50 = first_width_at(thetaShare, MAXS - 1, 0.50L);
  int tw90 = first_width_at(thetaShare, MAXS - 1, 0.90L);
  int tw99 = first_width_at(thetaShare, MAXS - 1, 0.99L);
  int etaStable10 = stable_width_within(eta, MAXS - 1, 1.0L, 0.10L);
  int etaStable05 = stable_width_within(eta, MAXS - 1, 1.0L, 0.05L);
  int etaStable01 = stable_width_within(eta, MAXS - 1, 1.0L, 0.01L);
  int topStable10 = stable_width_within(thetaShare, MAXS - 1, 1.0L, 0.10L);
  int topStable05 = stable_width_within(thetaShare, MAXS - 1, 1.0L, 0.05L);
  int topStable01 = stable_width_within(thetaShare, MAXS - 1, 1.0L, 0.01L);

  __int128 globalTailTV[MAXS];
  __int128 topTailTV[MAXS];
  memset(globalTailTV, 0, sizeof(globalTailTV));
  memset(topTailTV, 0, sizeof(topTailTV));
  __int128 gtail = 0, ttail = 0;
  for (int d = MAXS - 1; d >= 1; d--) {
    globalTailTV[d - 1] = gtail + abs128(byDist[d]);
    topTailTV[d - 1] = ttail + abs128(topByDist[d]);
    gtail = globalTailTV[d - 1];
    ttail = topTailTV[d - 1];
  }

  char sD[I128_BUF], sE[I128_BUF], sNeed[I128_BUF], sTopD[I128_BUF], sTopFull[I128_BUF];
  i128_to_string(D, sD);
  i128_to_string(E_from_gram, sE);
  i128_to_string(globalNeed, sNeed);
  i128_to_string(topDiag, sTopD);
  i128_to_string(topFull, sTopFull);

  int liveCount = 0;
  for (int k = 0; k < MAXS; k++) liveCount += live[k];

  printf("window [%" PRIu64 ",%" PRIu64 ")  H/N = %.6Lf\n",
         N, nmax, N == 0 ? 0.0L : (long double)H / N);
  printf("  live q scales                : %d  range=[%d,%d]\n", liveCount, kmin, kmax);
  printf("  max |F_k(n)| / n             : %.6Lf at (k,n)=(%d,%" PRIu64 ")\n",
         maxAbsFOverN, argK, argN);
  printf("  D = sum_k G_kk               : %s\n", sD);
  printf("  E = ||sum_k F_k||^2          : %s\n", sE);
  printf("  D-E required negative cross  : %s\n", sNeed);
  printf("  Gram identity check          : %s\n", E_direct == E_from_gram ? "PASS" : "FAIL");
  printf("  top gatekeeper audit         : %s", topAuditFailures == 0 ? "PASS" : "FAIL");
  if (topAuditFailures != 0)
    printf(" (%" PRIu64 " failures; first n=%" PRIu64 ", got=%" PRId64 ", prime=%" PRId64 ")",
           topAuditFailures, topAuditFirstN, topAuditGot, topAuditExpected);
  printf("\n");
  printf("  top diagonal                 : %s\n", sTopD);
  printf("  full top-row cancellation    : %s  theta_full=%.6Lf\n",
         sTopFull, ratio128(topFull, topDiag));
  printf("\n");
  printf("  locality thresholds\n");
  printf("    eta first-cross 50/90/99%%  : %d / %d / %d\n", w50, w90, w99);
  printf("    top first-cross 50/90/99%%  : %d / %d / %d\n", tw50, tw90, tw99);
  printf("    eta stable within 10/5/1%%  : %d / %d / %d\n",
         etaStable10, etaStable05, etaStable01);
  printf("    top stable within 10/5/1%%  : %d / %d / %d\n",
         topStable10, topStable05, topStable01);
  printf("\n");
  printf("  w        eta_w       theta_w   theta_share_w   global_tail_TV   top_tail_TV\n");
  __int128 pg = 0, pt = 0;
  int maxPrint = kmax - kmin;
  if (maxPrint < 1) maxPrint = 1;
  for (int w = 1; w <= maxPrint; w++) {
    pg += byDist[w];
    pt += topByDist[w];
    printf("  %2d  %12.6Lf  %12.6Lf  %15.6Lf  %14.6Lf  %11.6Lf\n",
           w, eta[w], theta[w], thetaShare[w],
           ratio128(globalTailTV[w], abs128(globalNeed)),
           ratio128(topTailTV[w], abs128(topFull)));
  }

  printf("\n");
  printf("  disjoint contiguous q-blocks: k maps to floor((k+phase)/width)\n");
  printf("    width  phase0_kappa    best_kappa  best_phase  worst_kappa  top23_coverage\n");
  for (int width = 2; width <= 16; width++) {
    long double phase0 = NAN, best = INFINITY, worst = -INFINITY;
    int bestPhase = 0;
    long double bestCoverage = 0.0L;
    for (int phase = 0; phase < width; phase++) {
      __int128 Db = D;
      for (int k = 0; k < MAXS; k++)
        for (int l = k + 1; l < MAXS; l++)
          if (block_id(k, width, phase) == block_id(l, width, phase))
            Db += 2 * G[k][l];
      __int128 covered = 0;
      for (uint64_t r = 0; r < H; r++) {
        uint64_t n = N + r;
        uint64_t endpoint = (n + 1) * (n + 1) - 1;
        int kt = ilog2_u64(endpoint);
        int b = block_id(kt, width, phase);
        if (kt >= 3 && block_id(kt - 2, width, phase) == b &&
            block_id(kt - 3, width, phase) == b) {
          int64_t ft = path[(size_t)kt * H + r];
          covered += (__int128)ft * ft;
        }
      }
      long double kap = ratio128(Db, E_from_gram);
      if (phase == 0) phase0 = kap;
      if (kap < best) {
        best = kap;
        bestPhase = phase;
        bestCoverage = ratio128(covered, topDiag);
      }
      if (kap > worst) worst = kap;
    }
    printf("    %5d  %12.3Lf  %12.3Lf  %10d  %12.3Lf  %14.6Lf\n",
           width, phase0, best, bestPhase, worst, bestCoverage);
  }

  struct OffsetContribution offsets[2 * MAXS - 2];
  int noff = 0;
  for (int delta = -MAXS + 1; delta <= MAXS - 1; delta++) {
    if (delta == 0) continue;
    offsets[noff].delta = delta;
    offsets[noff].mass = topByOffset[delta + MAXS];
    noff++;
  }
  qsort(offsets, (size_t)noff, sizeof(offsets[0]), compare_offset_desc);
  printf("\n");
  printf("  largest dynamic-top compensator offsets by |cancellation mass|\n");
  printf("    delta=l-k_top     mass       share_of_top_full\n");
  int shown = 0;
  for (int i = 0; i < noff && shown < 12; i++) {
    if (offsets[i].mass == 0) continue;
    char sm[I128_BUF];
    i128_to_string(offsets[i].mass, sm);
    printf("    %+4d         %16s      %+.6Lf\n",
           offsets[i].delta, sm, ratio128(offsets[i].mass, topFull));
    shown++;
  }

  free(composite);
  free(primes);
  free(qinc);
  free(primeinc);
  free(mu);
  free(prod);
  free(lpf);
  free(path);
  free(primepath);
  return (E_direct == E_from_gram && topAuditFailures == 0) ? 0 : 4;
}
