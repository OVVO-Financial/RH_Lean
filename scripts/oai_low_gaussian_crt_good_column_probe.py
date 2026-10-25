#!/usr/bin/env python3
"""Finite CRT Gauss-factor sanity check for the s*I primitive-column strategy.

This checks local split-prime residue-field factors, not the entire Eisenstein
ideal ring, calibrated OpenAI detector, physical windows or an exponent.
No third-party dependencies.
"""
from cmath import exp, pi
from math import isclose, sqrt

def primitive_root(p):
    factors = []
    m = p - 1
    for d in range(2, m+1):
        if m % d == 0 and all(d % j for j in range(2, int(sqrt(d)) + 1)):
            factors.append(d)
    for g in range(2, p):
        if all(pow(g, m//q, p) != 1 for q in factors):
            return g
    raise AssertionError("prime not supported")

def transform(p, exponent):
    g = primitive_root(p)
    discrete_log = {pow(g, k, p): k % 6 for k in range(p-1)}
    assert len(discrete_log) == p-1 and (p-1) % 6 == 0
    chi = [0j] + [
        exp(2j*pi*exponent*discrete_log[x]/6)
        for x in range(1, p)
    ]
    return [sum(chi[x] * exp(2j*pi*k*x/p) for x in range(p))
            for k in range(p)]

def main():
    # Low slot s=7 has exponent -1=5. Column I=13 and odd J overlap:
    # 1+3*v_13(J)=4 (nonprincipal order 3). Additional p=37 in J
    # with even v_37(J) has a principal-on-units zero/nonunit mask.
    factors = [(7, 5), (13, 4), (37, 0)]
    fhat = {p: transform(p, e) for p, e in factors}
    for p, e in factors:
        f = fhat[p]
        if e != 0:
            assert abs(f[0]) < 1e-8
            assert all(isclose(abs(f[k]), sqrt(p), rel_tol=1e-9, abs_tol=1e-8)
                       for k in range(1, p))
        else:
            assert isclose(abs(f[0]), p-1, abs_tol=1e-8)
            assert all(isclose(abs(f[k]), 1, abs_tol=1e-8)
                       for k in range(1, p))
        print(f"p={p}, sextic exponent={e}, zero={abs(f[0]):.3g}, "
              f"max={max(map(abs,f)):.9f}")
    crt_max = 1
    for p, _ in factors:
        crt_max *= max(map(abs, fhat[p]))
    assert isclose(crt_max, (37-1)*sqrt(7*13), rel_tol=1e-9)
    assert crt_max <= 37*sqrt(7*13)
    print("PASS exact local-prime Gauss norms, zero mode, "
          "CRT product <= N(H)*sqrt(N(s*I))")
    for v in range(12):
        assert (1 + 3*v) % 6 in (1, 4)
    print("PASS all tested I/J overlaps nonprincipal")

if __name__ == "__main__":
    main()
