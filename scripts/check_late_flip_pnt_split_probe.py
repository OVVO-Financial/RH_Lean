#!/usr/bin/env python3
"""Check the late-flip PNT split probe.

This is a finite diagnostic, not a Lean certificate or an RH estimate.

For small roots the checker rebuilds every quantity from literal definitions:
the all-plus prime comb after the primes through R, the prime-first late-flip
sum, the prime-first PNT error, and the site-by-site physical diagonal.  It
then compares the probe's per-root rows and reproduces the documented summary
on the default range.
"""

import math
from pathlib import Path
import re
import subprocess
import sys

GAMMA = 0.5772156649015329


def li(x):
    t = math.log(x)
    term, total = 1.0, 0.0
    for n in range(1, 400):
        term *= t / n
        add = term / n
        total += add
        if add < 1e-18 * total:
            break
    return GAMMA + math.log(t) + total


LI2 = li(2.0)


def L(x):
    return li(float(x)) - LI2


def tables(n_max):
    """Mobius and primality by trial factorisation (independent of the C sieve)."""
    mu = [0] * (n_max + 1)
    prime = [False] * (n_max + 1)
    mu[1] = 1
    for n in range(2, n_max + 1):
        m, sign, d, sqfree = n, 1, 2, True
        while d * d <= m:
            if m % d == 0:
                m //= d
                if m % d == 0:
                    sqfree = False
                    break
                sign = -sign
            d += 1
        if not sqfree:
            continue
        if m > 1:
            sign = -sign
        mu[n] = sign
        prime[n] = sign == -1 and all(n % p for p in range(2, math.isqrt(n) + 1))
    mert = [0] * (n_max + 1)
    pi = [0] * (n_max + 1)
    for n in range(1, n_max + 1):
        mert[n] = mert[n - 1] + mu[n]
        pi[n] = pi[n - 1] + (1 if prime[n] else 0)
    return mu, prime, mert, pi


def literal_row(R, mu, prime, mert, pi):
    X = R * R - 1
    small_primes = [p for p in range(2, R + 1) if prime[p]]
    # Literal all-plus comb: start at +1, first-power hits flip, p^2 kills.
    all_plus = 0
    for n in range(1, X + 1):
        s = 1
        for p in small_primes:
            if n % p == 0:
                if n % (p * p) == 0:
                    s = 0
                    break
                s = -s
        all_plus += s
    b_root = all_plus - 2 * (pi[X] - pi[R])
    # Prime-first late-flip sum; the top half contributes 2(1 - M(1)) = 0.
    H = 0
    for p in range(R + 1, X + 1):
        if prime[p]:
            H += 2 * (1 - mert[X // p])
            if 2 * p > X:
                assert X // p == 1 and 2 * (1 - mert[1]) == 0
    assert mert[X] == b_root + H, (R, mert[X], b_root, H)
    # Band Li model and prime-first PNT error.
    Hbar = 0.0
    for k in range(2, R):
        lo = max(R, X // (k + 1))
        Hbar += 2 * (1 - mert[k]) * (L(X // k) - L(lo))
    pnt_err = 0.0
    for q in range(R + 1, X + 1):
        ind = 1.0 if prime[q] else 0.0
        pnt_err += (ind - (L(q) - L(q - 1))) * mert[X // q]
    eta = H - Hbar
    delta = lambda t: pi[t] - L(t)
    eta_bridge = 2 * (delta(X) - delta(R)) - 2 * pnt_err
    assert abs(eta - eta_bridge) < 1e-6, (R, eta, eta_bridge)
    eta_tel = -2 * sum(mu[k] * delta(X // k) for k in range(2, R)) \
        - 2 * (1 - mert[R - 1]) * delta(R)
    assert abs(eta - eta_tel) < 1e-6, (R, eta, eta_tel)
    # Contract objects from literal definitions.
    owners = [q for q in range(3, R, 2) if prime[q] and q * q < R]
    Q = sum(mert[X // (q * q)] / q for q in owners)
    E = sum(mert[X // (q * q)] ** 2 for q in owners)
    D = 0.0
    for n in range(1, X + 1):
        if mu[n]:
            w = (1 if n >= R else 0) + sum(1 / q for q in owners if n <= X // (q * q))
            D += w * w
    G = mert[X] - mert[R - 1]
    K = max(1.0, max((mert[y] - 1) ** 2 / (y + 1) for y in range(R)))
    Z = b_root - mert[R - 1] + Q
    A = Z + Hbar
    assert abs(A - (G + Q - eta)) < 1e-6
    F = (G + Q) ** 2 - D
    # Prime-square term inherited by pi - Li from -li(sqrt t)/2.
    bsq = (1 - mert[R - 1]) * li(math.sqrt(R)) + sum(
        mu[k] * li(math.sqrt(X / k)) for k in range(2, R) if mu[k])
    return dict(R=R, X=X, MX=mert[X], G=G, Q=Q, E=E, D=D, K=K, H=H,
                Hbar=Hbar, eta=eta, A=A, Z=Z, F=F, Fm=A * A - D, Bsq=bsq)


def run(binary, *args):
    return subprocess.check_output([str(binary), *map(str, args)], text=True)


def main():
    binary = Path(sys.argv[1]).resolve()
    r_lo, r_hi = 56, 90
    mu, prime, mert, pi = tables(r_hi * r_hi)
    cols = "R X MX G Q E D K H Hbar eta A Z F Fm Bsq".split()
    rows = [dict(zip(cols, map(float, line.split())))
            for line in run(binary, r_hi, r_lo, "rows").splitlines()
            if line and not line.startswith("#")]
    assert [int(r["R"]) for r in rows] == list(range(r_lo, r_hi + 1))
    for row in rows:
        ref = literal_row(int(row["R"]), mu, prime, mert, pi)
        for key in cols:
            assert math.isclose(row[key], ref[key], rel_tol=1e-9, abs_tol=1e-5), \
                (int(row["R"]), key, row[key], ref[key])
    print(f"Every probe row for R={r_lo}..{r_hi} agrees with the literal all-plus "
          "comb, prime-first sums, and site-by-site diagonal.")

    output = run(binary)
    expect = {
        r"max identity residual .* = ([\d.e+-]+)": (0.0, 1e-9),
        r"max \(FinalStokes - 9/4 E\)/\(R\^2 K\) = (-?[\d.]+)": (-0.330422, 1e-5),
        r"max \(A\^2 - D - 9/4 E\)/\(R\^2 K\) *= (-?[\d.]+)": (-0.097865, 1e-5),
        r"rms \|G\+Q\|/R = ([\d.]+)": (0.1794, 1e-4),
        r"rms \|eta\|/R = ([\d.]+)": (0.4117, 1e-4),
        r"rms \|A\|/R = ([\d.]+)": (0.3398, 1e-4),
        r"pearson\(M\(X\), eta\) = ([\d.]+)": (0.9682, 1e-4),
        r"slope\(eta on M\(X\)\) = ([\d.]+)": (1.3352, 1e-4),
        r"fit eta/R ~ a \+ b M\(X\)/R: a = (-?[\d.]+)": (-0.3282, 1e-4),
        r"fit \(eta-Bsq\)/R ~ a \+ b M\(X\)/R: a = (-?[\d.]+)": (-0.0393, 1e-4),
        r"fit \(eta-Bsq\)/R .* b = ([\d.]+)": (1.3376, 1e-4),
        r"fit \(eta-Bsq\)/R .* r = ([\d.]+)": (0.9899, 1e-4),
    }
    for pattern, (value, tol) in expect.items():
        match = re.search(pattern, output)
        assert match, pattern
        assert abs(float(match[1]) - value) <= tol, (pattern, match[1], value)
    match = re.search(r"model Stokes exceeds FinalStokes on (\d+) of (\d+)", output)
    assert match and (int(match[1]), int(match[2])) == (2730, 2945), match
    print("\n".join(line for line in output.splitlines() if line.startswith("#")))
    print("Finite diagnostics reproduced; no uniform bound is certified.")


if __name__ == "__main__":
    main()
