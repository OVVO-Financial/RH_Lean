#!/usr/bin/env python3
"""Exact integer NNS Co-Div regression on the moving prime-window source.

No random signs, Li approximation, external libraries or inferred analytic bound.
The source is the native integer Euler/Mobius population, NOT the original
Eisenstein-ideal Gaussian/OAI compensated source.
"""
from bisect import bisect_left, bisect_right
from math import isqrt

H_WINDOWS = (128, 256, 512)
ANCHORS = (317, 1027)


def mobius_prime_tables(limit):
    mu = [0] * (limit + 1)
    lp = [0] * (limit + 1)
    primes = []
    mu[1] = 1
    for n in range(2, limit + 1):
        if lp[n] == 0:
            lp[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            k = n * p
            if k > limit or p > lp[n]:
                break
            lp[k] = p
            mu[k] = 0 if p == lp[n] else -mu[n]
    M = [0] * (limit + 1)
    pi = [0] * (limit + 1)
    for n in range(1, limit + 1):
        M[n] = M[n - 1] + mu[n]
        pi[n] = pi[n - 1] + int(n >= 2 and lp[n] == n)
    return mu, lp, primes, M, pi


def endpoint_states(root, primes, M, pi):
    X = root * root - 1
    debt = sum(M[X // p] for p in primes[
        bisect_left(primes, root):bisect_right(primes, X)])
    low = M[X] + debt
    top = -(pi[X] - pi[X // 2])
    middle = -debt - top
    assert low + middle + top == M[X]
    return low, middle, top, debt


def regression():
    max_root = max(2 * max(H_WINDOWS), *ANCHORS)
    N = max_root * max_root - 1
    mu, lp, primes, M, pi = mobius_prime_tables(N)
    states = {r: endpoint_states(r, primes, M, pi)
              for r in range(min(H_WINDOWS), 2 * max(H_WINDOWS) + 1)}

    print("H,low_E,middle_E,top_E,cross_LM,cross_LT,cross_MT,"
          "shell_E,cofactor_diag,cofactor_Co,cofactor_Div,cofactor_E,"
          "root_prime_gate_E,birth_gate_E")
    expected = {
        128: (3962, 72230, 39838, -12482, 15882, -81808, 37622, 301212, 30540),
        256: (20400, 390469, 247965, -98242, 92884, -543260, 110216, 1850483, 96119),
        512: (94961, 2371730, 1595492, -542974, 520364, -3552638, 486935, 11703523, 414321),
    }
    for H in H_WINDOWS:
        eL = eM = eP = lm = lp_cross = mp = energy = 0
        diag = co = div = ea = eg = eb = 0
        for R in range(H, 2 * H):
            low, mid, top, debt = states[R]
            low2, mid2, top2, debt2 = states[R + 1]
            l, m, p = low2 - low, mid2 - mid, top2 - top
            eL += l * l
            eM += m * m
            eP += p * p
            lm += 2 * l * m
            lp_cross += 2 * l * p
            mp += 2 * m * p
            energy += (l + m + p) ** 2

            X, Y = R * R - 1, (R + 1) ** 2 - 1
            pos = neg = d = 0
            for c in range(1, R):
                if mu[c] == 0:
                    continue
                count = pi[Y // c] - pi[X // c]
                d += count * count
                if mu[c] == 1:
                    pos += count
                else:
                    neg += count
            A = pos - neg
            G = M[R - 1] if lp[R] == R else 0
            B = mu[R] * (int(lp[R + 1] == R + 1)
                         + int(lp[R + 2] == R + 2))
            assert debt2 - debt == A - G + B, ("gate identity", R)
            diag += d
            co += (pos * pos + neg * neg - d) // 2
            div += pos * neg
            ea += A * A
            eg += G * G
            eb += B * B
            assert (l + m + p) == M[Y] - M[X]

        assert energy == eL + eM + eP + lm + lp_cross + mp
        assert ea == diag + 2 * (co - div)
        assert (eL, eM, eP, lm, lp_cross, mp, energy, diag, ea) == expected[H]
        print(H, eL, eM, eP, lm, lp_cross, mp, energy,
              diag, co, div, ea, eg, eb, sep=",")

    print("R,X,M(X),M(R-1),historical_D,weighted_Co,weighted_Div,historical_Q")
    for R in ANCHORS:
        X = R * R - 1
        d = co = div = 0
        for b in range(1, R):
            d += M[b] ** 2 * (X // (b * b) - X // ((b + 1) ** 2))
            if mu[b] == 0:
                continue
            for a in range(1, b):
                if mu[a] == 0:
                    continue
                w = X // (a * b) - X // (b * b)
                if mu[a] == mu[b]:
                    co += w
                else:
                    div += w
        Q = d + 2 * (co - div)
        assert Q == 2 * M[R - 1] - M[X], ("Euler endpoint", R)
        print(R, X, M[X], M[R - 1], d, co, div, Q, sep=",")


if __name__ == "__main__":
    regression()
