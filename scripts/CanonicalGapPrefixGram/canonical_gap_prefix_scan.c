#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <inttypes.h>

#define SEG (1u << 22)
#define NMODE 7
#define NWIDTH 4

static const char *mode_name[NMODE] = {
  "all", "Lambda=1", "Lambda=4", "Lambda=16",
  "delta=1/8", "delta=1/4", "delta=1/2"
};

static uint64_t isqrt_u64(uint64_t x) {
  uint64_t r = (uint64_t)sqrtl((long double)x);
  while ((__uint128_t)(r + 1) * (r + 1) <= x) r++;
  while ((__uint128_t)r * r > x) r--;
  return r;
}

static uint64_t iroot4_u64(uint64_t x) { return isqrt_u64(isqrt_u64(x)); }
static uint64_t iroot8_u64(uint64_t x) { return isqrt_u64(iroot4_u64(x)); }

static __uint128_t threshold_K(int mode, uint64_t n) {
  switch (mode) {
    case 0: return 0;
    case 1: return (__uint128_t)2 * n;
    case 2: return (__uint128_t)8 * n;
    case 3: return (__uint128_t)32 * n;
    case 4: return (__uint128_t)2 * n * iroot8_u64(n);
    case 5: return (__uint128_t)2 * n * iroot4_u64(n);
    case 6: return (__uint128_t)2 * n * isqrt_u64(n);
    default: return 0;
  }
}

static long double i128_to_ld(__int128 x) {
  return (long double)x;
}

static void print_i128(__int128 x) {
  if (x == 0) { putchar('0'); return; }
  if (x < 0) { putchar('-'); x = -x; }
  char buf[64]; int k = 0;
  while (x > 0) { buf[k++] = (char)('0' + x % 10); x /= 10; }
  while (k--) putchar(buf[k]);
}

typedef struct {
  __int128 qbb, qee, qbe, qtot;
  int64_t Bend, Eend;
} Energy;

static Energy energy_range(const int64_t *PB, const int64_t *PE,
                           const __int128 *SB, const __int128 *SE,
                           const __int128 *SBB, const __int128 *SEE,
                           const __int128 *SBE,
                           uint64_t s, uint64_t w) {
  uint64_t a = s + 1, z = s + w;
  __int128 sumB = SB[z] - SB[a - 1];
  __int128 sumE = SE[z] - SE[a - 1];
  __int128 sumBB = SBB[z] - SBB[a - 1];
  __int128 sumEE = SEE[z] - SEE[a - 1];
  __int128 sumBE = SBE[z] - SBE[a - 1];
  __int128 b0 = PB[s], e0 = PE[s];
  Energy R;
  R.qbb = sumBB - 2 * b0 * sumB + (__int128)w * b0 * b0;
  R.qee = sumEE - 2 * e0 * sumE + (__int128)w * e0 * e0;
  R.qbe = sumBE - b0 * sumE - e0 * sumB + (__int128)w * b0 * e0;
  R.qtot = R.qbb + 2 * R.qbe + R.qee;
  R.Bend = PB[z] - PB[s];
  R.Eend = PE[z] - PE[s];
  return R;
}

typedef struct {
  __int128 qbb, qee, qbe, qtot;
} BridgeEnergy;

static BridgeEnergy bridge_energy_range(const int64_t *PB, const int64_t *PE,
                                         const __int128 *SB, const __int128 *SE,
                                         const __int128 *SBB, const __int128 *SEE,
                                         const __int128 *SBE,
                                         const __int128 *STB, const __int128 *STE,
                                         uint64_t s, uint64_t w) {
  uint64_t a = s + 1, z = s + w;
  __int128 sumB = SB[z] - SB[a - 1];
  __int128 sumE = SE[z] - SE[a - 1];
  __int128 sumBB = SBB[z] - SBB[a - 1];
  __int128 sumEE = SEE[z] - SEE[a - 1];
  __int128 sumBE = SBE[z] - SBE[a - 1];
  __int128 sumjB = STB[z] - STB[a - 1];
  __int128 sumjE = STE[z] - STE[a - 1];
  __int128 b0 = PB[s], e0 = PE[s];
  __int128 dB = PB[z] - PB[s], dE = PE[z] - PE[s];
  __int128 sumt = (__int128)w * (w + 1) / 2;
  __int128 sumt2 = (__int128)w * (w + 1) * (2 * (__int128)w + 1) / 6;
  __int128 localBB = sumBB - 2 * b0 * sumB + (__int128)w * b0 * b0;
  __int128 localEE = sumEE - 2 * e0 * sumE + (__int128)w * e0 * e0;
  __int128 localBE = sumBE - b0 * sumE - e0 * sumB + (__int128)w * b0 * e0;
  __int128 tB = sumjB - (__int128)s * sumB - b0 * sumt;
  __int128 tE = sumjE - (__int128)s * sumE - e0 * sumt;
  BridgeEnergy R;
  R.qbb = (__int128)w * w * localBB - 2 * (__int128)w * dB * tB + dB * dB * sumt2;
  R.qee = (__int128)w * w * localEE - 2 * (__int128)w * dE * tE + dE * dE * sumt2;
  R.qbe = (__int128)w * w * localBE - (__int128)w * dE * tB
          - (__int128)w * dB * tE + dB * dE * sumt2;
  R.qtot = R.qbb + 2 * R.qbe + R.qee;
  return R;
}

static int cmp_ld(const void *a, const void *b) {
  long double x = *(const long double*)a, y = *(const long double*)b;
  return (x > y) - (x < y);
}

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s N H\n", argv[0]);
    return 2;
  }
  uint64_t N = strtoull(argv[1], NULL, 10);
  uint64_t H = strtoull(argv[2], NULL, 10);
  if (N < 2 || H < 1 || N + H < N) {
    fprintf(stderr, "invalid N,H\n"); return 2;
  }
  uint64_t nmax = N + H;
  __uint128_t lo128 = (__uint128_t)N * N;
  __uint128_t hi128 = (__uint128_t)nmax * nmax;
  if (hi128 > UINT64_MAX) { fprintf(stderr, "range too large\n"); return 2; }
  uint64_t XLO = (uint64_t)lo128, XHI = (uint64_t)hi128;

  uint64_t root = isqrt_u64(XHI - 1) + 1;
  uint8_t *comp = calloc(root + 1, 1);
  uint32_t *primes = malloc(sizeof(uint32_t) * (root / 2 + 16));
  uint32_t np = 0;
  for (uint64_t i = 2; i <= root; i++) {
    if (!comp[i]) {
      primes[np++] = (uint32_t)i;
      if (i * i <= root)
        for (uint64_t j = i * i; j <= root; j += i) comp[j] = 1;
    }
  }
  free(comp);

  int64_t **B = malloc(NMODE * sizeof(*B));
  int64_t **E = malloc(NMODE * sizeof(*E));
  for (int k = 0; k < NMODE; k++) {
    B[k] = calloc(H, sizeof(int64_t));
    E[k] = calloc(H, sizeof(int64_t));
  }
  int64_t *direct = calloc(H, sizeof(int64_t));
  uint64_t *sqcount = calloc(H, sizeof(uint64_t));

  int8_t *mu = malloc(SEG * sizeof(int8_t));
  uint64_t *prod = malloc(SEG * sizeof(uint64_t));
  uint64_t *lpf = malloc(SEG * sizeof(uint64_t));
  uint64_t sf = 0;
  uint64_t cur_n = N;
  uint64_t next_sq = (N + 1) * (N + 1);

  for (uint64_t lo = XLO; lo < XHI; lo += SEG) {
    uint64_t hi = lo + SEG; if (hi > XHI) hi = XHI;
    uint32_t len = (uint32_t)(hi - lo);
    memset(mu, 1, len);
    for (uint32_t i = 0; i < len; i++) { prod[i] = 1; lpf[i] = 1; }

    for (uint32_t kk = 0; kk < np; kk++) {
      uint64_t p = primes[kk];
      if ((__uint128_t)p * p >= hi) break;
      uint64_t start = (lo + p - 1) / p * p;
      for (uint64_t j = start; j < hi; j += p) {
        uint32_t i = (uint32_t)(j - lo);
        mu[i] = (int8_t)(-mu[i]);
        prod[i] *= p;
        lpf[i] = p;
      }
      __uint128_t pp128 = (__uint128_t)p * p;
      if (pp128 < hi) {
        uint64_t pp = (uint64_t)pp128;
        uint64_t s2 = (lo + pp - 1) / pp * pp;
        for (uint64_t j = s2; j < hi; j += pp) mu[(uint32_t)(j - lo)] = 0;
      }
    }

    for (uint32_t i = 0; i < len; i++) {
      uint64_t m = lo + i;
      while (m >= next_sq) {
        cur_n++;
        next_sq = (cur_n + 1) * (cur_n + 1);
      }
      uint64_t bi = cur_n - N;
      if (bi >= H) { fprintf(stderr, "block index overflow\n"); return 3; }
      int muv = mu[i];
      if (muv == 0) continue;
      uint64_t q;
      if (prod[i] != m) {
        uint64_t r = m / prod[i];
        muv = -muv;
        q = r > lpf[i] ? r : lpf[i];
      } else {
        q = lpf[i];
      }
      if (m <= 1 || q <= 1) continue;
      uint64_t c = m / q;
      uint64_t u = c < q ? c : q;
      uint64_t v = c < q ? q : c;
      uint64_t d = v - u;
      __uint128_t h2 = (__uint128_t)d * (u + v);
      int bal = (d > 0 && d < u);
      direct[bi] += muv;
      sqcount[bi]++;
      sf++;
      for (int k = 0; k < NMODE; k++) {
        if (h2 > threshold_K(k, cur_n)) {
          if (bal) B[k][bi] += muv;
          else E[k][bi] += muv;
        }
      }
    }
  }

  uint64_t mismatch = 0;
  for (uint64_t i = 0; i < H; i++)
    if (B[0][i] + E[0][i] != direct[i]) mismatch++;

  printf("# Canonical-gap prefix Gram scan\n\n");
  printf("range: square blocks [%" PRIu64 ", %" PRIu64 ")\n", N, N + H);
  printf("integer interval: [%" PRIu64 ", %" PRIu64 ")\n", XLO, XHI);
  printf("squarefree canonical sources: %" PRIu64 "\n", sf);
  printf("all-source reconstruction mismatches: %" PRIu64 "\n", mismatch);
  printf("thresholds use doubled height h2 = |q-c|(q+c) = 2Z:\n");
  printf("  all: h2 > 0; Lambda=L: h2 > 2Ln; delta=a: h2 > 2n floor(n^a).\n\n");

  uint64_t widths[NWIDTH] = {64, 256, 1024, H};
  for (int k = 0; k < NMODE; k++) {
    int64_t *PB = calloc(H + 1, sizeof(int64_t));
    int64_t *PE = calloc(H + 1, sizeof(int64_t));
    __int128 *SB = calloc(H + 1, sizeof(__int128));
    __int128 *SE = calloc(H + 1, sizeof(__int128));
    __int128 *SBB = calloc(H + 1, sizeof(__int128));
    __int128 *SEE = calloc(H + 1, sizeof(__int128));
    __int128 *SBE = calloc(H + 1, sizeof(__int128));
    __int128 *STB = calloc(H + 1, sizeof(__int128));
    __int128 *STE = calloc(H + 1, sizeof(__int128));
    for (uint64_t i = 0; i < H; i++) {
      PB[i+1] = PB[i] + B[k][i];
      PE[i+1] = PE[i] + E[k][i];
      SB[i+1] = SB[i] + PB[i+1];
      SE[i+1] = SE[i] + PE[i+1];
      SBB[i+1] = SBB[i] + (__int128)PB[i+1] * PB[i+1];
      SEE[i+1] = SEE[i] + (__int128)PE[i+1] * PE[i+1];
      SBE[i+1] = SBE[i] + (__int128)PB[i+1] * PE[i+1];
      STB[i+1] = STB[i] + (__int128)(i + 1) * PB[i+1];
      STE[i+1] = STE[i] + (__int128)(i + 1) * PE[i+1];
    }

    printf("## threshold %s\n\n", mode_name[k]);
    printf("| width | windows | cross<0 | total<min(parts) | median rho | median cancellation | detrended cross<0 | median detrended rho | median detrended cancellation | representative QBB | QEE | 2QBE | QTOT |\n");
    printf("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n");
    for (int wi = 0; wi < NWIDTH; wi++) {
      uint64_t w = widths[wi]; if (w > H) continue;
      uint64_t nw = H - w + 1;
      long double *rhos = malloc(nw * sizeof(long double));
      long double *cans = malloc(nw * sizeof(long double));
      long double *brhos = malloc(nw * sizeof(long double));
      long double *bcans = malloc(nw * sizeof(long double));
      uint64_t neg = 0, below = 0, bneg = 0;
      long double minrho = 2, maxrho = -2;
      Energy rep = energy_range(PB,PE,SB,SE,SBB,SEE,SBE,0,w);
      for (uint64_t s = 0; s < nw; s++) {
        Energy R = energy_range(PB,PE,SB,SE,SBB,SEE,SBE,s,w);
        BridgeEnergy C = bridge_energy_range(PB,PE,SB,SE,SBB,SEE,SBE,STB,STE,s,w);
        if (R.qbe < 0) neg++;
        if (C.qbe < 0) bneg++;
        if (R.qtot < (R.qbb < R.qee ? R.qbb : R.qee)) below++;
        long double rho = 0;
        if (R.qbb > 0 && R.qee > 0)
          rho = i128_to_ld(R.qbe) / sqrtl(i128_to_ld(R.qbb) * i128_to_ld(R.qee));
        long double den = i128_to_ld(R.qbb + R.qee);
        long double can = den > 0 ? 1.0L - i128_to_ld(R.qtot) / den : 0;
        long double brho = 0;
        if (C.qbb > 0 && C.qee > 0)
          brho = i128_to_ld(C.qbe) / sqrtl(i128_to_ld(C.qbb) * i128_to_ld(C.qee));
        long double bden = i128_to_ld(C.qbb + C.qee);
        long double can = bden > 0 ? 1.0L - i128_to_ld(C.qtot) / bden : 0;
        rhos[s] = rho; cans[s] = can; brhos[s] = brho; bcans[s] = bcan;
        if (rho < minrho) minrho = rho;
        if (rho > maxrho) maxrho = rho;
      }
      qsort(rhos,nw,sizeof(long double),cmp_ld);
      qsort(cans,nw,sizeof(long double),cmp_ld);
      qsort(brhos,nw,sizeof(long double),cmp_ld);
      qsort(bcans,nw,sizeof(long double),cmp_ld);
      long double medrho = rhos[nw/2], medcan = cans[nw/2];
      long double medbrho = brhos[nw/2], medbcan = bcans[nw/2];
      printf("| %" PRIu64 " | %" PRIu64 " | %.2Lf%% | %.2Lf%% | %.6Lf | %.2Lf%% | %.2Lf%% | %.6Lf | %.2Lf%% | ",
             w,nw,100.0L*neg/nw,100.0L*below/nw,medrho,100.0L*medcan,
             100.0L*bneg/nw,medbrho,100.0L*medbcan);
      print_i128(rep.qbb); printf(" | "); print_i128(rep.qee); printf(" | ");
      print_i128(2*rep.qbe); printf(" | "); print_i128(rep.qtot); printf(" |\n");
      free(rhos); free(cans); free(brhos); free(bcans);
    }
    Energy F = energy_range(PB,PE,SB,SE,SBB,SEE,SBE,0,H);
    long double rhoF = (F.qbb > 0 && F.qee > 0) ?
      i128_to_ld(F.qbe)/sqrtl(i128_to_ld(F.qbb)*i128_to_ld(F.qee)) : 0;
    long double canF = (F.qbb+F.qee)>0 ?
      1.0L - i128_to_ld(F.qtot)/i128_to_ld(F.qbb+F.qee) : 0;
    BridgeEnergy CF = bridge_energy_range(PB,PE,SB,SE,SBB,SEE,SBE,STB,STE,0,H);
    long double brhoF = (CF.qbb > 0 && CF.qee > 0) ?
      i128_to_ld(CF.qbe)/sqrtl-®ιάjΧ