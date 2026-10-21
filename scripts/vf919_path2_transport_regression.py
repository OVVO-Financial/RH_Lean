#!/usr/bin/env python3
"""Finite Path-2 source checks, NOT an asymptotic 7/8 certificate.

Individually labelled squarefree Eisenstein ideals are enumerated with
split, inert and ramified primes. Norm fibres are checked against the
independently calculated arithmetic convolution mu*(chi_3*mu).
Quadrature checks the fixed-profile FTC and prime-parent reindexing.
The scales 317 and 1027 are P, not square-block roots.
"""
from __future__ import annotations
import json
import math
from dataclasses import dataclass
import numpy as np

A, B, C = 5.0 / 4.0, 8.0 / 5.0, 4.0 / 5.0
GX, GW = np.polynomial.legendre.leggauss(128)
T, TW = (GX + 1.0) / 2.0, GW / 2.0


def eta(x):
    x = np.asarray(x, dtype=float)
    z = (2.0 * x - A - B) / (B - A)
    ans = np.zeros_like(z)
    mask = np.abs(z) < 1.0
    ans[mask] = np.exp(-1.0 / (1.0 - z[mask] ** 2))
    return ans


def window(x):
    """Integral of eta(v)/v from C*x to x: F(x)-F(C*x)."""
    x = np.asarray(x, dtype=float)
    lo = np.maximum(C * x, A)
    hi = np.minimum(x, B)
    width = np.maximum(hi - lo, 0.0)
    grid = lo[..., None] + width[..., None] * T
    return width * np.sum(eta(grid) / grid * TW, axis=-1)


def mobius_sieve(n):
    mu = np.ones(n + 1, dtype=np.int64)
    mu[0] = 0
    composite = np.zeros(n + 1, dtype=bool)
    primes = []
    for p in range(2, n + 1):
        if not composite[p]:
            primes.append(p)
            composite[p::p] = True
            mu[p::p] *= -1
            if p * p <= n:
                mu[p * p::p * p] = 0
    return mu, primes


def chi(n):
    n = np.asarray(n, dtype=np.int64)
    return np.where(n % 3 == 1, 1, np.where(n % 3 == 2, -1, 0))


@dataclass(frozen=True)
class Ideal:
    norm: int
    sign: int
    factors: tuple[tuple[int, str], ...]


def squarefree_ideals(n, primes):
    ans = [Ideal(1, 1, ())]
    prime_ideals = []
    for p in primes:
        if p == 3:
            prime_ideals.append((3, (p, 'ramified')))
        elif p % 3 == 1:
            prime_ideals.extend([(p, (p, 'split+')), (p, (p, 'split-'))])
        elif p * p <= n:
            prime_ideals.append((p * p, (p, 'inert')))
    for norm, label in prime_ideals:
        previous = list(ans)
        ans.extend(Ideal(v.norm * norm, -v.sign, v.factors + (label,))
                   for v in previous if v.norm * norm <= n)
    return ans, prime_ideals


def check_scale(p_scale):
    nmax = 2 * p_scale
    mu, primes = mobius_sieve(nmax)
    a_f = np.zeros(nmax + 1, dtype=np.int64)
    for d in range(1, nmax + 1):
        quot = np.arange(1, nmax // d + 1)
        a_f[d * quot] += int(mu[d]) * chi(quot) * mu[quot]
    ideals, prime_ideals = squarefree_ideals(nmax, primes)
    fibres = np.zeros(nmax + 1, dtype=np.int64)
    for ideal in ideals:
        fibres[ideal.norm] += ideal.sign
    if not np.array_equal(a_f, fibres):
        raise AssertionError('Ideal norm fibre differs from arithmetic convolution')
    rational = float(np.dot(mu[1:], window(np.arange(1, nmax + 1) / p_scale)))
    cofactor_at_norm = np.zeros(nmax + 1)
    dipole_at_norm = np.zeros(nmax + 1)
    max_site_error = 0.0
    for m in range(1, nmax + 1):
        ds = np.arange(1, nmax // m + 1)
        cofactor_at_norm[m] = np.dot(chi(ds), window(ds * m / p_scale))
        qs = np.arange(1, nmax // m + 1, 3)
        # Split at exact support endpoints to resolve narrow endpoint pieces.
        def component(scale):
            lo = np.maximum(0.0, A * p_scale / (scale * m) - qs)
            hi = np.minimum(1.0, B * p_scale / (scale * m) - qs)
            width = np.maximum(hi - lo, 0.0)
            qt = qs[:, None] + lo[:, None] + width[:, None] * T
            return width * np.sum(eta(scale * m / p_scale * qt) / qt * TW, axis=1)
        val = component(C) - component(1.0)
        exact = window(qs * m / p_scale) - window((qs + 1) * m / p_scale)
        if len(qs):
            max_site_error = max(max_site_error, float(np.max(np.abs(val - exact))))
        dipole_at_norm[m] = np.sum(val)
    lifted = math.fsum(v.sign * cofactor_at_norm[v.norm] for v in ideals)
    reconstructed = math.fsum(v.sign * dipole_at_norm[v.norm] for v in ideals)
    tolerance = 5e-8
    if abs(lifted - rational) > tolerance or abs(reconstructed - rational) > tolerance:
        raise AssertionError((p_scale, rational, lifted, reconstructed))
    reindex_errors = {}
    selected = [x for x in prime_ideals if x[1][0] in (2, 3, 7, 13)]
    for pnorm, label in selected:
        parents = [v for v in ideals if label not in v.factors and v.norm * pnorm <= nmax]
        children = [(v.norm * pnorm, -v.sign, tuple(sorted(v.factors + (label,))))
                    for v in parents]
        if len({v[2] for v in children}) != len(parents):
            raise AssertionError('Parent-child map is not injective on ideal labels')
        child_sum = math.fsum(sgn * float(window(norm / p_scale))
                             for norm, sgn, _ in children)
        parent_sum = math.fsum(v.sign * float(window(v.norm / (p_scale / pnorm)))
                              for v in parents)
        err = abs(child_sum + parent_sum)
        if err > tolerance:
            raise AssertionError(('marked reindex', label, err))
        reindex_errors[str(label)] = err
    return dict(scale=p_scale, largest_physical_integer=nmax,
                labelled_squarefree_ideals=len(ideals), norm_fibres_exact=True,
                original_mobius_sum=rational, labelled_ideal_cofactor_sum=lifted,
                fixed_dipole_reconstruction=reconstructed,
                max_single_dipole_error=max_site_error,
                marked_reindex_errors=reindex_errors)


def main():
    results = [check_scale(p) for p in (317, 1027)]
    print(json.dumps({'status': 'PASS', 'claim': 'finite identities only, not a 7/8 bound',
                      'quadrature_order': len(T), 'results': results}, indent=2))


if __name__ == '__main__':
    main()
