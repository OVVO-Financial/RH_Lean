#!/usr/bin/env python3
"""Adversarial check of the proposed #919 GATE-2 split.

GATE-2 writes, for complex row amplitudes Z_u and (X_u, Y_u) = Phi(Z_u),

    sum_u |Z_u|^2 = sum_u X_u Y_u + (1/2) sum_u (X_u - Y_u)^2,

and proposes to read sum_u X_u Y_u = sum_u Re(Z_u^2) as the signed VF
Co/Div channel.  This script measures that channel on genuine character
families with genuine Moebius coefficients.  It is a finite diagnostic, not
a proof; the exact statements are kernel-checked in
research/VF_MID_919_OAI_GATE2_GAUGE_NO_GO.lean.

Checks:
  1. Natural gauge, full Dirichlet family mod a prime q, coefficients mu(n)
     on 2 <= n <= N with N^2 <= q: the signed channel is exactly zero, so the
     anti-diagonal carries the whole Hermitian energy (q-1) * #{mu(n) != 0}.
  2. Natural gauge, N^2 > q: the signed channel equals
     (q-1) * sum_{m n = 1 mod q} mu(m) mu(n), a product-inverse correlation,
     not the diagonal m = n counted by the Hermitian energy.
  3. Gauge sweep: multiplying the rows by unimodular constants (which leaves
     every |Z_u| unchanged) moves the signed channel across [-H, H].
  4. Sextic orbit: the six sextic-unit gauges of one family sum to a zero
     signed channel and to 6 H of energy.
"""
import cmath
import math

Q = 10009          # prime, Q = 1 (mod 6)
SHORT_N = 100      # SHORT_N^2 = 10000 <= Q
LONG_N = 3000      # LONG_N^2 > Q


def mobius_upto(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    is_comp = bytearray(limit + 1)
    primes = []
    for i in range(2, limit + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > limit:
                break
            is_comp[i * p] = 1
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def primitive_root(p):
    phi = p - 1
    factors = []
    m, d = phi, 2
    while d * d <= m:
        if m % d == 0:
            factors.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        factors.append(m)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in factors):
            return g
    raise ValueError("no primitive root")


def discrete_logs(p, g):
    logs = [None] * p
    x = 1
    for k in range(p - 1):
        logs[x] = k
        x = x * g % p
    return logs


def rows(p, logs, coeffs, ks):
    """Z_k = sum_n a_n chi_k(n), chi_k(g^j) = exp(2 pi i j k / (p-1))."""
    phi = p - 1
    out = []
    for k in ks:
        z = 0j
        for n, a in coeffs:
            z += a * cmath.exp(2j * math.pi * (logs[n % p] * k % phi) / phi)
        out.append(z)
    return out


def split(zs):
    signed = sum((z * z).real for z in zs)
    anti = sum(((z.real - z.imag) - (z.real + z.imag)) ** 2 / 2 for z in zs)
    energy = sum(abs(z) ** 2 for z in zs)
    return signed, anti, energy


def main():
    mu = mobius_upto(LONG_N)
    g = primitive_root(Q)
    logs = discrete_logs(Q, g)
    phi = Q - 1
    all_k = range(phi)
    tol = 1e-6

    # 1. Short support: signed channel vanishes identically.
    short = [(n, mu[n]) for n in range(2, SHORT_N + 1) if mu[n] != 0]
    zs = rows(Q, logs, short, all_k)
    s, a, h = split(zs)
    expected_h = phi * len(short)
    assert abs(h - expected_h) < tol * expected_h, (h, expected_h)
    assert abs(s) < tol * expected_h, s
    assert abs(a - h) < tol * expected_h
    print("VF919_GATE2 short q=%d N=%d support=%d: signed=%.3e "
          "anti=%.1f energy=%.1f (= (q-1)*support)"
          % (Q, SHORT_N, len(short), s, a, h))

    # 2. Long support: signed channel is the product-inverse correlation.
    long_ = [(n, mu[n]) for n in range(2, LONG_N + 1) if mu[n] != 0]
    zs_long = rows(Q, logs, long_, all_k)
    s2, a2, h2 = split(zs_long)
    inverse_corr = 0
    diag = 0
    for m, am in long_:
        for n, an in long_:
            if m * n % Q == 1:
                inverse_corr += am * an
            if m % Q == n % Q:
                diag += am * an
    assert abs(s2 - phi * inverse_corr) < tol * h2
    assert abs(h2 - phi * diag) < tol * h2
    assert abs(s2 + a2 - h2) < tol * h2
    print("VF919_GATE2 long  q=%d N=%d: signed=%.1f = (q-1)*%d "
          "[mn=1 mod q], energy=%.1f = (q-1)*%d [m=n], "
          "signed/energy=%.4f"
          % (Q, LONG_N, s2, inverse_corr, h2, diag, s2 / h2))

    # 3. Gauge sweep on the long family: |Z_u| fixed, signed channel moves.
    aligned = [abs(z) for z in zs_long]
    anti_aligned = [1j * abs(z) for z in zs_long]
    rotated = [1j * z for z in zs_long]
    sa, aa, ha = split(aligned)
    sn, an_, hn = split(anti_aligned)
    sr, ar, hr = split(rotated)
    for hh in (ha, hn, hr):
        assert abs(hh - h2) < tol * h2
    assert abs(sa - h2) < tol * h2 and abs(aa) < tol * h2
    assert abs(sn + h2) < tol * h2 and abs(an_ - 2 * h2) < tol * h2
    assert abs(sr + s2) < tol * h2
    print("VF919_GATE2 gauge: energy fixed at %.1f; signed channel "
          "natural=%.1f, times i=%.1f, aligned=%.1f, anti-aligned=%.1f"
          % (h2, s2, sr, sa, sn))

    # 4. Sextic-unit orbit: signed channel averages to zero.
    zeta = cmath.exp(2j * math.pi / 6)
    orbit_signed = 0.0
    orbit_energy = 0.0
    for j in range(6):
        sj, _, hj = split([zeta ** j * z for z in zs_long])
        orbit_signed += sj
        orbit_energy += hj
    assert abs(orbit_signed) < tol * h2
    assert abs(orbit_energy - 6 * h2) < tol * h2
    print("VF919_GATE2 sextic orbit: signed sum=%.3e, energy sum=%.1f "
          "(= 6 H)" % (orbit_signed, orbit_energy))

    print("PASS: the GATE-2 signed channel is gauge-dependent and, in the "
          "natural gauge, measures mn = 1 (mod q) rather than the diagonal. "
          "On short supports it vanishes for every coefficient vector. It "
          "cannot carry or certify the Hermitian moment.")


if __name__ == "__main__":
    main()
