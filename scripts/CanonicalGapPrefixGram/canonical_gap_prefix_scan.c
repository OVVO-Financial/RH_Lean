#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <inttypes.h>

#define SEG (1u << 22)
#define NMODE 4

static const char *mode_name[NMODE] = {
  "all", "Lambda=16", "delta=1/4", "delta=1/2"
};

static uint64_t isqrt_u64(uint64_t x) {
  uint64_t r = (uint64_t)sqrtl((long double)x);
  while ((__uint128_t)(r + 1) * (r + 1) <= x) r++;
  while ((__uint128_t)r * r > x) r--;
  return r;
}
static uint64_t iroot4_u64(uint64_t x) { return isqrt_u64(isqrt_u64(x)); }

static __uint128_t threshold_K(int mode, uint64_t n) {
  switch (mode) {
    case 0: return 0;
    case 1: return (__uint128_t)32 * n;
    case 2: return (__uint128_t)2 * n * iroot4_u64(n);
    case 3: return (__uint128_t)2 * n * isqrt_u64(n);
    default: return 0;
  }
}

static long double i128_to_ld(__int128 x) { return (long double)x; }

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

typedef struct {
  __int128 qbb, qee, qbe, qtot;
} BridgeEnergy;

typedef struct {
  __int128 qbb_num, qee_num, qbe_num, qtot_num;
  __int128 slopeB_num, slopeE_num, denom;
} OrthEnergy;

static Energy raw_energy(const int64_t *PB, const int64_t *PE, uint64_t H) {
  Energy R = {0};
  for (uint64_t i = 1; i <= H; i++) {
    R.qbb += (__int128)PB[i] * PB[i];
    R.qee += (__int128)PE[i] * PE[i];
    R.qbe += (__int128)PB[i] * PE[i];
  }
  R.qtot = R.qbb + 2 * R.qbe + R.qee;
  R.Bend = PB[H]; R.Eend = PE[H];
  return R;
}

static BridgeEnergy bridge_energy(const int64_t *PB, const int64_t *PE, uint64_t H) {
  BridgeEnergy R = {0};
  int64_t bend = PB[H], eend = PE[H];
  for (uint64_t i = 1; i <= H; i++) {
    __int128 b = (__int128)H * PB[i] - (__int128)i * bend;
    __int128 e = (__int128)H * PE[i] - (__int128)i * eend;
    R.qbb += b * b; R.qee += e * e; R.qbe += b * e;
  }
  R.qtot = R.qbb + 2 * R.qbe + R.qee;
  return R;
}

static OrthEnergy orth_energy(const int64_t *PB, const int64_t *PE, uint64_t H) {
  OrthEnergy R = {0};
  __int128 t2 = (__int128)H * (H + 1) * (2 * (__int128)H + 1) / 6;
  __int128 qbb = 0, qee = 0, qbe = 0, tB = 0, tE = 0;
  for (uint64_t i = 1; i <= H; i++) {
    qbb += (__int128)PB[i] * PB[i];
    qee += (__int128)PE[i] * PE[i];
    qbe += (__int128)PB[i] * PE[i];
    tB += (__int128)i * PB[i];
    tE += (__int128)i * PE[i];
  }
  R.qbb_num = t2 * qbb - tB * tB;
  R.qee_num = t2 * qee - tE * tE;
  R.qbe_num = t2 * qbe - tB * tE;
  R.qtot_num = R.qbb_num + 2 * R.qbe_num + R.qee_num;
  R.slopeB_num = tB; R.slopeE_num = tE; R.denom = t2;
  return R;
}

int main(int argc, char **argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s N H\n", argv[0]); return 2;
  }
  uint64_t N = strtoull(argv[1], NULL, 10);
  uint64_t H = strtoull(argv[2], NULL, 10);
  if (N < 2 || H < 1 || N + H < N) return 2;
  uint64_t nmax = N + H;
  __uint128_t lo128 = (__uint128_t)N * N;
  __uint128_t hi128 = (__uint128_t)nmax * nmax;
  if (hi128 > UINT64_MAX) return 2;
  uint64_t XLO = (uint64_t)lo128, XHI = (uint64_t)hi128;

  uint64_t root = isqrt_u64(XHI - 1) + 1;
  uint8_t *comp = calloc(root + 1, 1);
  uint32_t *primes = malloc(sizeof(uint32_t) * (root / 2 + 16));
  uint32_t np = 0;
  for (uint64_t i = 2; i <= root; i++) if (!comp[i]) {
    primes[np++] = (uint32_t)i;
    if (i * i <= root) for (uint64_t j = i * i; j <= root; j += i) comp[j] = 1;
  }
  free(comp);

  int64_t *B[NMODE], *E[NMODE];
  for (int k = 0; k < NMODE; k++) {
    B[k] = calloc(H, sizeof(int64_t)); E[k] = calloc(H, sizeof(int64_t));
  }
  int64_t *direct = calloc(H, sizeof(int64_t));
  int8_t *mu = malloc(SEG); uint64_t *prod = malloc(SEG * sizeof(uint64_t));
  uint64_t *lpf = malloc(SEG * sizeof(uint64_t));
  uint64_t sf = 0, cur_n = N, next_sq = (N + 1) * (N + 1);

  for (uint64_t lo = XLO; lo < XHI; lo += SEG) {
    uint64_t hi = lo + SEG; if (hi > XHI) hi = XHI;
    uint32_t len = (uint32_t)(hi - lo);
    memset(mu, 1, len);
    for (uint32_t i = 0; i < len; i++) { prod[i] = 1; lpf[i] = 1; }
    for (uint32_t kk = 0; kk < np; kk++) {
      uint64_t p = primes[kk]; if ((__uint128_t)p * p >= hi) break;
      uint64_t start = (lo + p - 1) / p * p;
      for (uint64_t j = start; j < hi; j += p) {
        uint32_t i = (uint32_t)(j - lo); mu[i] = (int8_t)-mu[i]; prod[i] *= p; lpf[i] = p;
      }
      __uint128_t pp128 = (__uint128_t)p * p;
      if (pp128 < hi) {
        uint64_t pp = (uint64_t)pp128, s2 = (lo + pp - 1) / pp * pp;
        for (uint64_t j = s2; j < hi; j += pp) mu[(uint32_t)(j - lo)] = 0;
      }
    }
    for (uint32_t i = 0; i < len; i++) {
      uint64_t m = lo + i;
      while (m >= next_sq) { cur_n++; next_sq = (cur_n + 1) * (cur_n + 1); }
      uint64_t bi = cur_n - N;
      int muv = mu[i]; if (muv == 0) continue;
      uint64_t q;
      if (prod[i] != m) { uint64_t r = m / prod[i]; muv = -muv; q = r > lpf[i] ? r : lpf[i]; }
      else q = lpf[i];
      if (m <= 1 || q <= 1) continue;
      uint64_t c = m / q, u = c < q ? c : q, v = c < q ? q : c, d = v - u;
      __uint128_t h2 = (__uint128_t)d * (u + v);
      int balanced = d > 0 && d < u;
      direct[bi] += muv; sf++;
      for (int k = 0; k < NMODE; k++) if (h2 > threshold_K(k, cur_n)) {
        if (balanced) B[k][bi] += muv; else E[k][bi] += muv;
      }
    }
  }

  uint64_t mismatch = 0;
  for (uint64_t i = 0; i < H; i++) if (B[0][i] + E[0][i] != direct[i]) mismatch++;
  printf("range=[%" PRIu64 ",%" PRIu64 "), sources=%" PRIu64 ", reconstruction_mismatches=%" PRIu64 "\n",
         N, N + H, sf, mismatch);

  for (int k = 0; k < NMODE; k++) {
    int64_t *PB = calloc(H + 1, sizeof(int64_t)), *PE = calloc(H + 1, sizeof(int64_t));
    for (uint64_t i = 0; i < H; i++) { PB[i+1] = PB[i] + B[k][i]; PE[i+1] = PE[i] + E[k][i]; }
    Energy R = raw_energy(PB, PE, H);
    BridgeEnergy C = bridge_energy(PB, PE, H);
    OrthEnergy O = orth_energy(PB, PE, H);
    long double raw_rho = i128_to_ld(R.qbe) / sqrtl(i128_to_ld(R.qbb) * i128_to_ld(R.qee));
    long double raw_can = 1 - i128_to_ld(R.qtot) / i128_to_ld(R.qbb + R.qee);
    long double bridge_rho = i128_to_ld(C.qbe) / sqrtl(i128_to_ld(C.qbb) * i128_to_ld(C.qee));
    long double bridge_can = 1 - i128_to_ld(C.qtot) / i128_to_ld(C.qbb + C.qee);
    long double orth_rho = i128_to_ld(O.qbe_num) / sqrtl(i128_to_ld(O.qbb_num) * i128_to_ld(O.qee_num));
    long double orth_can = 1 - i128_to_ld(O.qtot_num) / i128_to_ld(O.qbb_num + O.qee_num);
    long double coh_den = i128_to_ld(O.slopeB_num * O.slopeB_num + O.slopeE_num * O.slopeE_num);
    long double coh_can = 1 - i128_to_ld((O.slopeB_num + O.slopeE_num) * (O.slopeB_num + O.slopeE_num)) / coh_den;
    long double target = (long double)H * N * N;
    long double bridge_target = (long double)H * H * target;
    long double orth_target = i128_to_ld(O.denom) * target;
    printf("\n[%s] endpoints B=%" PRId64 " E=%" PRId64 " total=%" PRId64 "\n", mode_name[k], R.Bend, R.Eend, R.Bend + R.Eend);
    printf("raw rho=%.12Lf cancel=%.6Lf%% normalized=(%.9Lf,%.9Lf,%.9Lf)\n",
           raw_rho, 100*raw_can, i128_to_ld(R.qbb)/target, i128_to_ld(R.qee)/target, i128_to_ld(R.qtot)/target);
    printf("bridge rho=%.12Lf cancel=%.6Lf%% normalized=(%.9Lf,%.9Lf,%.9Lf)\n",
           bridge_rho, 100*bridge_can, i128_to_ld(C.qbb)/bridge_target, i128_to_ld(C.qee)/bridge_target, i128_to_ld(C.qtot)/bridge_target);
    printf("orth slopes=(%.9Le,%.9Le) coherent_cancel=%.6Lf%% residual_rho=%.12Lf residual_cancel=%.6Lf%% residual_normalized=(%.9Lf,%.9Lf,%.9Lf)\n",
           i128_to_ld(O.slopeB_num)/i128_to_ld(O.denom), i128_to_ld(O.slopeE_num)/i128_to_ld(O.denom), 100*coh_can,
           orth_rho, 100*orth_can, i128_to_ld(O.qbb_num)/orth_target, i128_to_ld(O.qee_num)/orth_target, i128_to_ld(O.qtot_num)/orth_target);
    if (k == 0) {
      printf("exact raw ledger QBB="); print_i128(R.qbb); printf(" QEE="); print_i128(R.qee);
      printf(" 2QBE="); print_i128(2*R.qbe); printf(" QTOT="); print_i128(R.qtot); printf("\n");
    }
    free(PB); free(PE);
  }

  for (int k = 0; k < NMODE; k++) { free(B[k]); free(E[k]); }
  free(direct); free(mu); free(prod); free(lpf); free(primes);
  return mismatch ? 1 : 0;
}
