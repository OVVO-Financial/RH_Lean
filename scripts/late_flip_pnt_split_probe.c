/* Finite probe of the late-flip PNT split at the production endpoint
 *
 *   X = R^2 - 1,   R >= 56.
 *
 * Late-flip channel (PrimeCombReciprocalBandCancellation):
 *
 *   h(k)   = 2 (1 - M(k)),                  h(1) = 0,
 *   N_R(k) = #{p prime : R < p <= X, floor(X/p) = k},
 *   H_R    = sum_{k=2}^{R-1} h(k) N_R(k),
 *   B_root = M(X) - H_R.
 *
 * Li model of the same band populations, with L(t) = int_2^t du/log u:
 *
 *   Nbar_R(k) = L(u_k) - L(l_k),  u_k = floor(X/k),
 *                                 l_k = max(R, floor(X/(k+1))),
 *   Hbar_R    = sum_{k=2}^{R-1} h(k) Nbar_R(k),
 *   eta_R     = H_R - Hbar_R,
 *   A_R       = (B_root - M(R-1) + Q_R) + Hbar_R = G_R + Q_R - eta_R.
 *
 * Contract objects (CURRENT_PROOF_CONTRACT.md):
 *
 *   G_R = M(X) - M(R-1),   Q_R = sum_q M(floor(X/q^2))/q,
 *   E_R = sum_q M(floor(X/q^2))^2   (q odd prime, q^2 < R),
 *   D_R = sum_{n<=X} w_R(n)^2 mu(n)^2,
 *         w_R(n) = [n >= R] + sum_{q : n <= floor(X/q^2)} 1/q,
 *   FinalStokes_R = (G_R + Q_R)^2 - D_R,
 *   K_R = max(1, max_{y<R} (M(y)-1)^2/(y+1))   (least admissible envelope).
 *
 * Checked exact relations (integers exactly, reals to rounding):
 *
 *   H_R  = 2(pi(X)-pi(R)) - 2 sum_{c<R} mu(c)(pi(floor(X/c)) - pi(R))
 *          (cofactor-first form of the same prime tail),
 *   eta_R = -2 sum_{k=2}^{R-1} mu(k) Delta(floor(X/k))
 *           - 2 (1 - M(R-1)) Delta(R),          Delta = pi - L,
 *   eta_R = 2 (Delta(X) - Delta(R)) - 2 PNTError(R, X),
 *
 * where PNTError(R, X) = sum_{k=1}^{R-1} M(k)(N_R(k) - Nbar_R(k)) is the
 * reciprocal-interval form of RHLean.Analysis.primeSievePNTError R X.
 *
 * The summary also regresses eta_R on M(X), before and after removing the
 * deterministic prime-square term that pi - Li inherits from -li(sqrt t)/2:
 *
 *   Bsq_R = sum_{k=2}^{R-1} mu(k) li(sqrt(X/k)) + (1 - M(R-1)) li(sqrt R).
 *
 * The regression is a finite description, not an asymptotic statement.
 *
 * Diagnostic only.  Finite evaluations do not certify a uniform constant.
 *
 * Build: cc -std=c11 -O2 -o late_flip_pnt_split_probe \
 *          scripts/late_flip_pnt_split_probe.c -lm
 * Usage: ./late_flip_pnt_split_probe [RMAX=3000] [RMIN=56] [rows]
 *   With the literal word "rows" as third argument, one line per R is
 *   printed before the summary.
 */

#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef M_GAMMA
#define M_GAMMA 0.5772156649015328606
#endif

static int8_t *mu;
static int32_t *mert;  /* M(n) */
static int32_t *pic;   /* pi(n) */
static int32_t *sqf;   /* number of squarefree m <= n */

/* li(x) for x > 1 by the positive series gamma + log log x + sum t^n/(n n!). */
static long double li(long double x) {
  long double t = logl(x);
  long double term = 1.0L, sum = 0.0L;
  for (int n = 1; n < 400; n++) {
    term *= t / n;
    long double add = term / n;
    sum += add;
    if (add < 1e-24L * sum) break;
  }
  return (long double)M_GAMMA + logl(t) + sum;
}

static long double li2;
static long double Lfun(uint64_t x) { return li((long double)x) - li2; }

static void sieve(uint64_t N) {
  mu = malloc(N + 1);
  uint8_t *comp = calloc(N + 1, 1);
  uint32_t *primes = malloc(sizeof(uint32_t) * (N / 2 + 16));
  mert = malloc(sizeof(int32_t) * (N + 1));
  pic = malloc(sizeof(int32_t) * (N + 1));
  sqf = malloc(sizeof(int32_t) * (N + 1));
  if (!mu || !comp || !primes || !mert || !pic || !sqf) {
    fprintf(stderr, "allocation failed\n");
    exit(1);
  }
  uint64_t np = 0;
  mu[0] = 0;
  if (N >= 1) mu[1] = 1;
  for (uint64_t i = 2; i <= N; i++) {
    if (!comp[i]) {
      primes[np++] = (uint32_t)i;
      mu[i] = -1;
    }
    for (uint64_t j = 0; j < np; j++) {
      uint64_t p = primes[j];
      uint64_t ip = i * p;
      if (ip > N) break;
      comp[ip] = 1;
      if (i % p == 0) {
        mu[ip] = 0;
        break;
      }
      mu[ip] = (int8_t)(-mu[i]);
    }
  }
  mert[0] = 0;
  pic[0] = 0;
  sqf[0] = 0;
  for (uint64_t i = 1; i <= N; i++) {
    mert[i] = mert[i - 1] + mu[i];
    pic[i] = pic[i - 1] + ((i >= 2 && !comp[i]) ? 1 : 0);
    sqf[i] = sqf[i - 1] + (mu[i] != 0 ? 1 : 0);
  }
  free(comp);
  free(primes);
}

static int is_prime(uint64_t n) { return n >= 2 && pic[n] != pic[n - 1]; }

typedef struct {
  double n, sx, sy, sxx, syy, sxy;
} Corr;

static void corr_add(Corr *c, double x, double y) {
  c->n += 1;
  c->sx += x;
  c->sy += y;
  c->sxx += x * x;
  c->syy += y * y;
  c->sxy += x * y;
}

static double corr_r(const Corr *c) {
  double vx = c->sxx - c->sx * c->sx / c->n;
  double vy = c->syy - c->sy * c->sy / c->n;
  double cxy = c->sxy - c->sx * c->sy / c->n;
  return cxy / sqrt(vx * vy);
}

static double corr_slope(const Corr *c) {
  double vx = c->sxx - c->sx * c->sx / c->n;
  double cxy = c->sxy - c->sx * c->sy / c->n;
  return cxy / vx;
}

static double corr_intercept(const Corr *c) {
  return (c->sy - corr_slope(c) * c->sx) / c->n;
}

/* Root-mean-square residual of the least-squares line. */
static double corr_resid(const Corr *c) {
  double vy = c->syy - c->sy * c->sy / c->n;
  double r = corr_r(c);
  return sqrt(vy * (1 - r * r) / c->n);
}

int main(int argc, char **argv) {
  uint64_t Rmax = 3000, Rmin = 56;
  int rows = 0;
  if (argc >= 2) Rmax = strtoull(argv[1], NULL, 10);
  if (argc >= 3) Rmin = strtoull(argv[2], NULL, 10);
  if (argc >= 4 && strcmp(argv[3], "rows") == 0) rows = 1;
  if (Rmin < 3 || Rmax < Rmin || Rmax > 20000) {
    fprintf(stderr, "need 3 <= RMIN <= RMAX <= 20000\n");
    return 2;
  }
  uint64_t N = Rmax * Rmax - 1;
  sieve(N);
  li2 = li(2.0L);

  long double *Lu = malloc(sizeof(long double) * (Rmax + 2));
  uint64_t *u = malloc(sizeof(uint64_t) * (Rmax + 2));
  if (!Lu || !u) return 1;

  /* Running least envelope over y < R. */
  long double Kmin = 1.0L;
  uint64_t ynext = 0;

  double worst_cF = -1e300, worst_cModel = -1e300;
  double worst_F = -1e300;
  uint64_t worst_cF_R = 0, worst_cModel_R = 0;
  double max_gq = 0, max_eta = 0, max_A = 0, max_Z = 0, max_Hbar = 0;
  double ss_gq = 0, ss_eta = 0, ss_A = 0, ss_mx = 0;
  double max_idErr = 0;
  uint64_t count = 0, model_worse = 0;
  Corr c_eta_A = {0}, c_eta_mx = {0}, c_A_mx = {0}, c_eta_gq = {0};
  Corr c_etab_mx = {0};

  if (rows)
    printf("# R X M(X) G Q E D K H Hbar eta A Z FinalStokes ModelStokes "
           "Bsq\n");

  for (uint64_t R = 3; R <= Rmax; R++) {
    /* Advance the least envelope through y = R-1. */
    while (ynext < R) {
      long double m1 = (long double)mert[ynext] - 1.0L;
      long double v = m1 * m1 / (long double)(ynext + 1);
      if (v > Kmin) Kmin = v;
      ynext++;
    }
    if (R < Rmin) continue;
    uint64_t X = R * R - 1;
    long double MX = mert[X], MR1 = mert[R - 1];
    long double G = MX - MR1;

    /* Low q^2 owners: odd primes q with q*q < R. */
    uint64_t owners[64];
    int m = 0;
    for (uint64_t q = 3; q * q < R; q += 2)
      if (is_prime(q)) owners[m++] = q;
    long double Q = 0, E = 0;
    for (int i = 0; i < m; i++) {
      long double v = mert[X / (owners[i] * owners[i])];
      Q += v / owners[i];
      E += v * v;
    }
    /* D = sum mu^2 (T + S)^2, T = [n >= R], S = sum_q [n <= c_q]/q. */
    long double D = (long double)(sqf[X] - sqf[R - 1]);
    for (int i = 0; i < m; i++) {
      uint64_t ci = X / (owners[i] * owners[i]);
      D += 2.0L * (sqf[ci] - sqf[R - 1]) / owners[i];
      for (int j = 0; j < m; j++) {
        uint64_t cj = X / (owners[j] * owners[j]);
        uint64_t cm = ci < cj ? ci : cj;
        D += (long double)sqf[cm] / ((long double)owners[i] * owners[j]);
      }
    }
    long double GQ = G + Q;
    long double F = GQ * GQ - D;

    /* Band endpoints: u_k = X/k for k = 1..R-1, and u_R := R = l_{R-1}. */
    for (uint64_t k = 1; k < R; k++) u[k] = X / k;
    u[R] = R;
    for (uint64_t k = 1; k <= R; k++) Lu[k] = Lfun(u[k]);
    /* Sanity: l_k = max(R, X/(k+1)) equals u[k+1] for 1 <= k <= R-1. */
    for (uint64_t k = 1; k < R; k++) {
      uint64_t lk = X / (k + 1);
      if (lk < R) lk = R;
      if (lk != u[k + 1]) {
        fprintf(stderr, "band endpoint mismatch R=%llu k=%llu\n",
                (unsigned long long)R, (unsigned long long)k);
        return 1;
      }
    }
    int64_t H = 0;
    long double Hbar = 0, pntErr = 0, etaTel = 0;
    for (uint64_t k = 1; k < R; k++) {
      int64_t Nk = (int64_t)pic[u[k]] - pic[u[k + 1]];
      long double Nbar = Lu[k] - Lu[k + 1];
      int64_t hk = 2 * (1 - (int64_t)mert[k]);
      if (k == 1 && hk != 0) {
        fprintf(stderr, "h(1) != 0\n");
        return 1;
      }
      if (k >= 2) {
        H += hk * Nk;
        Hbar += hk * Nbar;
        etaTel += -2.0L * mu[k] * ((long double)pic[u[k]] - Lu[k]);
      }
      pntErr += (long double)mert[k] * ((long double)Nk - Nbar);
    }
    long double Bsq = (1.0L - MR1) * li(sqrtl((long double)R));
    for (uint64_t k = 2; k < R; k++)
      if (mu[k]) Bsq += mu[k] * li(sqrtl((long double)X / (long double)k));
    long double DeltaR = (long double)pic[R] - Lu[R];
    long double DeltaX = (long double)pic[X] - Lu[1];
    etaTel += -2.0L * (1.0L - MR1) * DeltaR;

    /* Cofactor-first form of the same integer. */
    int64_t Hcof = 2 * ((int64_t)pic[X] - pic[R]);
    for (uint64_t c = 1; c < R; c++)
      Hcof -= 2 * (int64_t)mu[c] * ((int64_t)pic[X / c] - pic[R]);
    if (Hcof != H) {
      fprintf(stderr, "H band/cofactor mismatch at R=%llu\n",
              (unsigned long long)R);
      return 1;
    }

    long double Broot = MX - (long double)H;
    long double eta = (long double)H - Hbar;
    long double etaBridge = 2.0L * (DeltaX - DeltaR) - 2.0L * pntErr;
    long double Z = Broot - MR1 + Q;
    long double A = Z + Hbar;
    double idErr = fabsl(eta - etaTel);
    if (fabsl(eta - etaBridge) > idErr) idErr = fabsl(eta - etaBridge);
    if (fabsl(A - (GQ - eta)) > idErr) idErr = fabsl(A - (GQ - eta));
    if (idErr > max_idErr) max_idErr = idErr;

    long double Fm = A * A - D;
    long double R2K = (long double)R * R * Kmin;
    double cF = (double)((F - 2.25L * E) / R2K);
    double cM = (double)((Fm - 2.25L * E) / R2K);
    if (cF > worst_cF) { worst_cF = cF; worst_cF_R = R; }
    if (cM > worst_cModel) { worst_cModel = cM; worst_cModel_R = R; }
    if ((double)(F / R2K) > worst_F) worst_F = (double)(F / R2K);
    if (Fm > F) model_worse++;

    double r = (double)R;
    if (fabs((double)GQ) / r > max_gq) max_gq = fabs((double)GQ) / r;
    if (fabs((double)eta) / r > max_eta) max_eta = fabs((double)eta) / r;
    if (fabs((double)A) / r > max_A) max_A = fabs((double)A) / r;
    if (fabs((double)Z) / (r * r) > max_Z) max_Z = fabs((double)Z) / (r * r);
    if (fabs((double)Hbar) / (r * r) > max_Hbar)
      max_Hbar = fabs((double)Hbar) / (r * r);
    ss_gq += (double)(GQ * GQ) / (r * r);
    ss_eta += (double)(eta * eta) / (r * r);
    ss_A += (double)(A * A) / (r * r);
    ss_mx += (double)(MX * MX) / (r * r);
    corr_add(&c_eta_A, (double)eta / r, (double)A / r);
    corr_add(&c_eta_mx, (double)MX / r, (double)eta / r);
    corr_add(&c_A_mx, (double)MX / r, (double)A / r);
    corr_add(&c_eta_gq, (double)GQ / r, (double)eta / r);
    corr_add(&c_etab_mx, (double)MX / r, (double)(eta - Bsq) / r);
    count++;

    if (rows)
      printf("%llu %llu %d %.0Lf %.6Lf %.0Lf %.6Lf %.6Lf %lld %.6Lf %.6Lf "
             "%.6Lf %.6Lf %.6Lf %.6Lf %.6Lf\n",
             (unsigned long long)R, (unsigned long long)X, mert[X], G, Q, E,
             D, Kmin, (long long)H, Hbar, eta, A, Z, F, Fm, Bsq);
  }

  printf("# range R=%llu..%llu samples=%llu\n", (unsigned long long)Rmin,
         (unsigned long long)Rmax, (unsigned long long)count);
  printf("# max identity residual (eta tel/bridge, A=G+Q-eta) = %.3e\n",
         max_idErr);
  printf("# max (FinalStokes - 9/4 E)/(R^2 K) = %.6f at R=%llu\n", worst_cF,
         (unsigned long long)worst_cF_R);
  printf("# max (A^2 - D - 9/4 E)/(R^2 K)     = %.6f at R=%llu\n",
         worst_cModel, (unsigned long long)worst_cModel_R);
  printf("# model Stokes exceeds FinalStokes on %llu of %llu roots\n",
         (unsigned long long)model_worse, (unsigned long long)count);
  printf("# max |G+Q|/R = %.4f  max |eta|/R = %.4f  max |A|/R = %.4f\n",
         max_gq, max_eta, max_A);
  printf("# max |Z|/R^2 = %.4f  max |Hbar|/R^2 = %.4f\n", max_Z, max_Hbar);
  printf("# rms |G+Q|/R = %.4f  rms |eta|/R = %.4f  rms |A|/R = %.4f"
         "  rms |M(X)|/R = %.4f\n",
         sqrt(ss_gq / count), sqrt(ss_eta / count), sqrt(ss_A / count),
         sqrt(ss_mx / count));
  printf("# pearson(eta, A) = %.4f\n", corr_r(&c_eta_A));
  printf("# pearson(M(X), eta) = %.4f  slope(eta on M(X)) = %.4f\n",
         corr_r(&c_eta_mx), corr_slope(&c_eta_mx));
  printf("# fit eta/R ~ a + b M(X)/R: a = %.4f  b = %.4f  resid = %.4f\n",
         corr_intercept(&c_eta_mx), corr_slope(&c_eta_mx),
         corr_resid(&c_eta_mx));
  printf("# fit (eta-Bsq)/R ~ a + b M(X)/R: a = %.4f  b = %.4f  r = %.4f"
         "  resid = %.4f\n",
         corr_intercept(&c_etab_mx), corr_slope(&c_etab_mx),
         corr_r(&c_etab_mx), corr_resid(&c_etab_mx));
  printf("# pearson(M(X), A) = %.4f  slope(A on M(X)) = %.4f\n",
         corr_r(&c_A_mx), corr_slope(&c_A_mx));
  printf("# pearson(G+Q, eta) = %.4f  slope(eta on G+Q) = %.4f\n",
         corr_r(&c_eta_gq), corr_slope(&c_eta_gq));
  return 0;
}
