#!/usr/bin/env python3
"""Kill-or-continue gate for the prime-root / smooth split of M(R^2 - 1).

Compiled definitions (RHLean/Proof/SquareRootAncestryRoot.lean,
ReplacementFibreOrientationSplit.lean, SquareRootAncestrySuccessor.lean):

    P_R = -sum_{q prime <= X} M(min(q - 1, X // q))          X = R^2 - 1
        = -sum_{1 <= c < R} mu(c) [pi(X // c) - pi(c)]      (cofactor form)
    S_R = sum over squarefree 2 <= n <= X with P+(n) < n / P+(n) of mu(n)

Root orientation is the reverse strict inequality, so the census splits
squarefree n >= 2 into P (P+(n) > n/P+(n)) and S.  Checked exactly:
P_R + S_R = M(X) - 1, and the tails split at R:
P^{<R} + S^{<R} = M(R-1) - 1,  P^{>=R} + S^{>=R} = M(X) - M(R-1) = G_R.
Diagnostics only.
"""
import argparse


def tables(limit):
    mu = [1] * (limit + 1)
    spf = [0] * (limit + 1)
    primes = []
    mu[0] = 0
    for n in range(2, limit + 1):
        if spf[n] == 0:
            spf[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            m = n * p
            if p > spf[n] or m > limit:
                break
            spf[m] = p
            mu[m] = 0 if p == spf[n] else -mu[n]
    lpf = [0] * (limit + 1)  # largest prime factor
    for n in range(2, limit + 1):
        p = spf[n]
        lpf[n] = max(p, lpf[n // p]) if n // p > 1 else p
    return mu, lpf


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-root", type=int, default=3000)
    ap.add_argument("--census-max-root", type=int, default=3000)
    args = ap.parse_args()
    lim = args.max_root ** 2 - 1
    mu, lpf = tables(lim)
    M = [0] * (lim + 1)
    pi = [0] * (lim + 1)
    for n in range(1, lim + 1):
        M[n] = M[n - 1] + mu[n]
        pi[n] = pi[n - 1] + (1 if n > 1 and lpf[n] == n else 0)
    # Running root-oriented / smooth census prefix (for the split at R).
    rootpre = [0] * (lim + 1)
    smoothpre = [0] * (lim + 1)
    for n in range(1, lim + 1):
        r = s = 0
        if n >= 2 and mu[n]:
            q = lpf[n]
            if q > n // q:
                r = mu[n]
            else:
                s = mu[n]
        rootpre[n] = rootpre[n - 1] + r
        smoothpre[n] = smoothpre[n - 1] + s
    K, Kmax = {}, 0.0
    for y in range(args.max_root):
        Kmax = max(Kmax, (M[y] - 1) ** 2 / (y + 1))
        K[y + 1] = Kmax
    rows = []
    for R in range(56, args.max_root + 1):
        X = R * R - 1
        P = -sum(mu[c] * (pi[X // c] - pi[c]) for c in range(1, R) if mu[c])
        S = M[X] - 1 - P
        if R <= args.census_max_root:
            assert P == rootpre[X] and S == smoothpre[X], R
            assert rootpre[R - 1] + smoothpre[R - 1] == M[R - 1] - 1
        Plo, Slo = rootpre[R - 1], smoothpre[R - 1]
        Phi, Shi = P - Plo, S - Slo
        assert Phi + Shi == M[X] - M[R - 1], R
        s = R * K[R] ** 0.5
        rows.append((R, P / s, S / s, (P + S) / s, Phi / s, Shi / s,
                     abs(P + S) / (abs(P) + abs(S)),
                     -2 * P * S / (P * P + S * S), abs(Phi + Shi) / (abs(Phi) + abs(Shi))))
    for R in (56, 100, 300, 1000, 2000, args.max_root):
        r = next(x for x in rows if x[0] == R)
        print("R=%d P/RvK=%.1f S/RvK=%.1f (P+S)/RvK=%.3f Phi/RvK=%.1f Shi/RvK=%.1f rho=%.2e eta=%.6f rho_tail=%.2e" % r)
    print("min |P|/RvK = %.1f, min |S|/RvK = %.1f, max |P+S|/RvK = %.3f" % (
        min(abs(r[1]) for r in rows), min(abs(r[2]) for r in rows), max(abs(r[3]) for r in rows)))
    print("min |P_tail|/RvK = %.1f, min |S_tail|/RvK = %.1f, max rho = %.2e, max rho_tail = %.2e" % (
        min(abs(r[4]) for r in rows), min(abs(r[5]) for r in rows),
        max(r[6] for r in rows), max(r[8] for r in rows)))
    print("Exact: P+S = M(X)-1, low split = M(R-1)-1, tail split = G_R at every root.")


if __name__ == "__main__":
    main()
