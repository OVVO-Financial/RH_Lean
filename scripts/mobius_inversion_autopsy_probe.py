#!/usr/bin/env python3
"""Exact finite check of research/MOBIUS_INVERSION_GLOBAL_CANCELLATION.lean.

Every quantity is transcribed from its compiled definition at X = R^2 - 1:

    bornSmooth  = sum_{m <= X, P+(m) <= R, P+(m) <= m / P+(m)} mu(m)
    positive    = sum_{m <= X, P+(m) <= R, m / P+(m) < P+(m)} mu(m)
    near        = sum_{R < q <= R+7, q prime} M(X // q)
    farT        = sum_{R+8 <= q <= X, q prime} M(X // q),  farSurvivor = -farT
    T           = sum_{2 <= q <= R, q prime} M(q - 1)
    low / comp  = Mobius-inversion columns over primes d < R+8 / composites
    E_root      = near + T

(P+(0) = P+(1) = 1, as in `canonicalLargestPrimeFactor`.)  Asserted exactly:

    positive = -T
    M(X) + low + farT + comp = 1
    bornSmooth + farSurvivor = M(X) + E_root
    bornSmooth = 1 - comp - low + E_root

Reference values from the same formulas (C, exact integers):
    R = 5561: M(X) = -2544, bornSmooth = -127748, farSurvivor = 124378,
              bornSmooth + farSurvivor = -3370, E_root = -826
    R = 2000: M(X) = 192, bornSmooth + farSurvivor = -335, E_root = -527
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
    lpf = [1] * (limit + 1)
    for n in range(2, limit + 1):
        r = n // spf[n]
        lpf[n] = max(spf[n], lpf[r]) if r > 1 else spf[n]
    return mu, spf, lpf


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-root", type=int, default=300)
    args = ap.parse_args()
    lim = args.max_root ** 2 - 1
    mu, spf, lpf = tables(lim)
    M = [0] * (lim + 1)
    for n in range(1, lim + 1):
        M[n] = M[n - 1] + mu[n]
    for R in range(56, args.max_root + 1):
        X = R * R - 1
        born = pos = 0
        for m in range(X + 1):
            q = lpf[m]
            if q <= R:
                if q <= m // q:
                    born += mu[m]
                else:
                    pos += mu[m]
        near = far = low = comp = 0
        for d in range(2, X + 1):
            v = M[X // d]
            if spf[d] == d:
                if d < R + 8:
                    low += v
                    if d > R:
                        near += v
                else:
                    far += v
            else:
                comp += v
        T = sum(M[q - 1] for q in range(2, R + 1) if spf[q] == q)
        e_root = near + T
        assert pos == -T, R
        assert M[X] + low + far + comp == 1, R
        assert born - far == M[X] + e_root, R
        assert born == 1 - comp - low + e_root, R
        if R in (56, 100, 200, args.max_root):
            print(f"R={R} M(X)={M[X]} bornSmooth={born} farSurvivor={-far} "
                  f"sum={born - far} E_root={e_root} comp={comp} low={low}")
    print("All four exact Mobius-inversion identities hold at every root.")


if __name__ == "__main__":
    main()
