/* Exact all-prefix anchor-coverage scan of the last three primorial blocks.
 *
 * Build and run:
 *     gcc -O2 -o block_scan block_scan.c -lm && ./block_scan
 *
 * Runtime is a few minutes: a segmented odd-part Moebius sieve over every
 * integer up to 29# = 6469693230.  Memory is a few tens of megabytes.
 *
 * For every n <= 29# the sieve produces
 *
 *     muo(n) = mu(oddpart(n)),
 *     mu(n)  = muo(n) if v2(n)=0,  -muo(n) if v2(n)=1,  0 otherwise,
 *
 * and accumulates M(x) = sum mu, Q(x) = sum |mu|, together with the
 * distinguished prime-2 fibre statistics
 *
 *     P_2(x) = -(3/4) sum_{L<n<=x} (-1)^n muo(n),
 *     m_2(x) =  (3/4) #{L<n<=x : muo(n) != 0}.
 *
 * The anchor diagnostics test the hypotheses of
 * RHLean/Proof/TwoAnchorSlackCoverage.lean directly.  With y = M(x) and an
 * anchor value c taken from a frozen or completed endpoint,
 *
 *     c covers y        <->  c (y - c) <= 0,
 *     obligation at c   :    c^2 + (y - c)^2 <= K^2 Q(x),
 *
 * uniformly for left and right anchors.  The scan reports, per block, how many
 * prefixes each anchor set covers and the exact constant
 *
 *     K_anchor = max_x sqrt( min_{covering c} (c^2 + (M(x)-c)^2) / Q(x) )
 *
 * that the cross-term-free reduction requires, next to the true constant
 * K_* = max_x |M(x)| / sqrt(Q(x)).
 *
 * Exact integer arithmetic throughout; ratios are compared by cross
 * multiplication in __int128.  Floating point is used only for display.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define SEG (1u << 21)
#define NPRIM 10
#define TABLE_HALF 40000            /* |M| stays far below this on these blocks */
#define TABLE_SIZE (2 * TABLE_HALF + 1)

static const uint64_t primorial[NPRIM] = {
    2ULL, 6ULL, 30ULL, 210ULL, 2310ULL, 30030ULL,
    510510ULL, 9699690ULL, 223092870ULL, 6469693230ULL};
static const char *pname[NPRIM] = {
    "2#", "3#", "5#", "7#", "11#", "13#", "17#", "19#", "23#", "29#"};
/* exact values, recomputed and re-verified by this program at run time */
static const long long expectedM[NPRIM] = {0, -1, -3, -1, -1, 16, -25, 278, 3516, -5012};

#define NBLOCK 3                    /* blocks (17#,19#], (19#,23#], (23#,29#] */
static const int blockLo[NBLOCK] = {6, 7, 8};
static const int blockHi[NBLOCK] = {7, 8, 9};

/* strict comparison n1/d1 > n2/d2 for nonnegative n and positive d */
static int frac_gt(long long n1, long long d1, long long n2, long long d2) {
    return (__int128)n1 * d2 > (__int128)n2 * d1;
}

/* obligation table: best[y + TABLE_HALF] = min over covering anchors c of
 * c^2 + (y-c)^2, or -1 when no anchor in the set covers y. */
static void build_table(const long long *anchors, int na, long long *best) {
    for (int i = 0; i < TABLE_SIZE; i++) {
        long long y = (long long)i - TABLE_HALF;
        long long b = -1;
        for (int k = 0; k < na; k++) {
            long long c = anchors[k];
            if (c * (y - c) <= 0) {              /* c covers y */
                long long v = c * c + (y - c) * (y - c);
                if (b < 0 || v < b) b = v;
            }
        }
        best[i] = b;
    }
}

int main(void) {
    const uint64_t N = primorial[NPRIM - 1];
    uint32_t root = (uint32_t)sqrt((double)N) + 2;

    char *comp = calloc(root + 1, 1);
    uint32_t *primes = malloc(sizeof(uint32_t) * (root / 4 + 100));
    uint32_t np = 0;
    for (uint32_t i = 2; i <= root; i++) {
        if (!comp[i]) {
            primes[np++] = i;
            for (uint64_t j = (uint64_t)i * i; j <= root; j += i) comp[j] = 1;
        }
    }

    /* per block: two-endpoint table and all-frozen-endpoint table */
    long long *tabPair[NBLOCK], *tabAll[NBLOCK];
    for (int t = 0; t < NBLOCK; t++) {
        long long pair[2] = {expectedM[blockLo[t]], expectedM[blockHi[t]]};
        long long all[NPRIM];
        int na = 0;
        for (int i = 0; i <= blockHi[t]; i++) all[na++] = expectedM[i];
        tabPair[t] = malloc(sizeof(long long) * TABLE_SIZE);
        tabAll[t] = malloc(sizeof(long long) * TABLE_SIZE);
        build_table(pair, 2, tabPair[t]);
        build_table(all, na, tabAll[t]);
    }

    int8_t *muo = malloc(SEG);
    uint64_t *prod = malloc(sizeof(uint64_t) * SEG);

    long long M = 0, Q = 0;
    long long Mp[NPRIM], Qp[NPRIM];
    /* per-block accumulators */
    long long bM[NBLOCK], bQ[NBLOCK]; uint64_t bX[NBLOCK];
    long long trough[NBLOCK], crest[NBLOCK]; uint64_t troughX[NBLOCK], crestX[NBLOCK];
    long long cover2[NBLOCK], uncover2[NBLOCK], coverA[NBLOCK], uncoverA[NBLOCK];
    long long p2N[NBLOCK], p2D[NBLOCK], paN[NBLOCK], paD[NBLOCK];
    uint64_t p2X[NBLOCK], paX[NBLOCK];
    int seen[NBLOCK];
    long long overflow = 0;
    for (int t = 0; t < NBLOCK; t++) {
        bM[t] = 0; bQ[t] = 1; bX[t] = 0; seen[t] = 0;
        trough[t] = crest[t] = 0; troughX[t] = crestX[t] = 0;
        cover2[t] = uncover2[t] = coverA[t] = uncoverA[t] = 0;
        p2N[t] = paN[t] = 0; p2D[t] = paD[t] = 1; p2X[t] = paX[t] = 0;
    }
    /* fibre statistics on (23#, x] */
    long long T = 0, A2 = 0, Tstar = 0, A2star = 0, Mstar = 0, Qstar = 0;
    const uint64_t L23 = primorial[8], XSTAR = 1109331447ULL;

    for (uint64_t lo = 0; lo <= N; lo += SEG) {
        uint64_t hi = lo + SEG; if (hi > N + 1) hi = N + 1;
        uint32_t len = (uint32_t)(hi - lo);
        memset(muo, 1, len);
        for (uint32_t i = 0; i < len; i++) prod[i] = 1;

        for (uint32_t k = 1; k < np; k++) {          /* odd base primes */
            uint64_t p = primes[k];
            uint64_t start = (lo + p - 1) / p * p;
            if (start < p) start = p;
            for (uint64_t j = start; j < hi; j += p) {
                uint32_t i = (uint32_t)(j - lo);
                muo[i] = (int8_t)(-muo[i]);
                prod[i] *= p;
            }
            uint64_t pp = p * p;
            if (pp < hi) {
                uint64_t s2 = (lo + pp - 1) / pp * pp;
                if (s2 < pp) s2 = pp;
                for (uint64_t j = s2; j < hi; j += pp) muo[(uint32_t)(j - lo)] = 0;
            }
        }

        for (uint32_t i = 0; i < len; i++) {
            uint64_t n = lo + i;
            if (n == 0) continue;
            int v = __builtin_ctzll(n);
            uint64_t m = n >> v;
            int8_t mo = muo[i];
            if (mo != 0 && prod[i] != m) mo = (int8_t)(-mo);
            int mu = (v == 0) ? mo : ((v == 1) ? -mo : 0);

            M += mu;
            Q += (mu != 0);

            for (int t = 0; t < NPRIM; t++)
                if (n == primorial[t]) { Mp[t] = M; Qp[t] = Q; }
            if (n > L23) { T += (n & 1ULL) ? -mo : mo; A2 += (mo != 0); }
            if (n == XSTAR) { Mstar = M; Qstar = Q; Tstar = T; A2star = A2; }

            for (int t = 0; t < NBLOCK; t++) {
                if (n < primorial[blockLo[t]] || n > primorial[blockHi[t]]) continue;
                if (!seen[t]) {
                    seen[t] = 1; bM[t] = M; bQ[t] = Q; bX[t] = n;
                    trough[t] = crest[t] = M; troughX[t] = crestX[t] = n;
                }
                if (frac_gt(M * M, Q, bM[t] * bM[t], bQ[t])) {
                    bM[t] = M; bQ[t] = Q; bX[t] = n;
                }
                if (M < trough[t]) { trough[t] = M; troughX[t] = n; }
                if (M > crest[t]) { crest[t] = M; crestX[t] = n; }

                if (M > TABLE_HALF || M < -TABLE_HALF) { overflow++; continue; }
                long long v2 = tabPair[t][M + TABLE_HALF];
                long long va = tabAll[t][M + TABLE_HALF];
                if (v2 < 0) uncover2[t]++;
                else {
                    cover2[t]++;
                    if (frac_gt(v2, Q, p2N[t], p2D[t])) { p2N[t] = v2; p2D[t] = Q; p2X[t] = n; }
                }
                if (va < 0) uncoverA[t]++;
                else {
                    coverA[t]++;
                    if (frac_gt(va, Q, paN[t], paD[t])) { paN[t] = va; paD[t] = Q; paX[t] = n; }
                }
            }
        }
    }

    printf("# Exact anchor-coverage scan through 29#\n\n");
    printf("## Mertens and squarefree counts at primorial endpoints\n\n");
    printf("| endpoint | M | Q | expected M | status |\n|---|---:|---:|---:|---|\n");
    for (int t = 0; t < NPRIM; t++)
        printf("| %s | %lld | %lld | %lld | %s |\n", pname[t], Mp[t], Qp[t],
               expectedM[t], Mp[t] == expectedM[t] ? "ok" : "MISMATCH");

    printf("\n## Consecutive endpoint sign products\n\n");
    printf("| pair | M(prev)*M(next) | anchor pair |\n|---|---:|---|\n");
    for (int t = 1; t < NPRIM; t++)
        printf("| %s x %s | %lld | %s |\n", pname[t - 1], pname[t],
               Mp[t - 1] * Mp[t],
               Mp[t - 1] * Mp[t] <= 0 ? "opposite: total coverage"
                                      : "same sign: gap case");

    for (int t = 0; t < NBLOCK; t++) {
        long long a = Mp[blockLo[t]], b = Mp[blockHi[t]];
        double Kstar = fabs((double)bM[t]) / sqrt((double)bQ[t]);
        double K2 = sqrt((double)p2N[t] / (double)p2D[t]);
        double KA = sqrt((double)paN[t] / (double)paD[t]);
        printf("\n## Block (%s, %s]\n\n", pname[blockLo[t]], pname[blockHi[t]]);
        printf("  anchors            M(L) = %lld   M(U) = %lld   product = %lld\n",
               a, b, a * b);
        printf("  K_*                %.12f at x = %llu  (M = %lld, Q = %lld)\n",
               Kstar, (unsigned long long)bX[t], bM[t], bQ[t]);
        printf("  trough             M = %lld at x = %llu\n", trough[t],
               (unsigned long long)troughX[t]);
        printf("  crest              M = %lld at x = %llu\n", crest[t],
               (unsigned long long)crestX[t]);
        printf("  two endpoints      covered %lld   uncovered %lld\n",
               cover2[t], uncover2[t]);
        printf("                     K_anchor = %.12f at x = %llu   (K_anchor/K_* = %.6f)\n",
               K2, (unsigned long long)p2X[t], K2 / Kstar);
        printf("  all frozen ends    covered %lld   uncovered %lld\n",
               coverA[t], uncoverA[t]);
        printf("                     K_anchor = %.12f at x = %llu   (K_anchor/K_* = %.6f)\n",
               KA, (unsigned long long)paX[t], KA / Kstar);
    }

    printf("\n## Distinguished prime-2 fibre at the 29# bottleneck x_* = %llu\n\n",
           (unsigned long long)XSTAR);
    printf("  M = %lld   Q = %lld   A = %lld   B = %lld\n",
           Mstar, Qstar, Mstar - Mp[8], Mp[9] - Mstar);
    printf("  left  cross -2 M(23#) A = %lld  (favourable)\n",
           -2 * Mp[8] * (Mstar - Mp[8]));
    printf("  right cross  2 M(29#) B = %lld  (unfavourable)\n",
           2 * Mp[9] * (Mp[9] - Mstar));
    printf("  P_2 = %.4f   A_2 = %lld   m_2 = %.4f\n",
           -0.75 * (double)Tstar, A2star, 0.75 * (double)A2star);
    printf("  |P_2|/sqrt(m_2) = %.12f    P_2/(M(x_*)-M(23#)) = %.10f\n",
           0.75 * fabs((double)Tstar) / sqrt(0.75 * (double)A2star),
           (-0.75 * (double)Tstar) / (double)(Mstar - Mp[8]));
    if (overflow) printf("\n  WARNING: %lld prefixes exceeded the table range\n", overflow);
    return 0;
}
