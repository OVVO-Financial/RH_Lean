#!/usr/bin/env python3
"""Exact rational/integer regression for the RH_Lean/Alpoge cost-replication seam.

No probabilistic assumptions. Does NOT verify any prime/theta/automorphic
error estimate, nor the RH-strength semivariance hypothesis.
"""
from fractions import Fraction as Q

for m in (1, 2, 3, 8, 30, 100, 1000):
    prefix = [-j for j in range(1, m + 1)]
    negative_lpm2 = sum(max(-x, 0) ** 2 for x in prefix)
    positive_upm2 = sum(max(x, 0) ** 2 for x in prefix)
    exact = m * (m + 1) * (2 * m + 1) // 6
    assert negative_lpm2 == exact
    assert positive_upm2 == 0
    assert Q(negative_lpm2, m) >= Q(m**2, 3)
    print(f"m={m:4}  input_energy={m:7}  negative_LPM2={exact:11}  "
          f"energy_ratio={Q(exact, m)}  positive_UPM2=0")

# Alpoge's abstract size-window parameter identities, not a claimed
# realization by the arithmetic source.
for r, u in ((10, 1), (10, 2), (100, 2), (100, 4)):
    x = Q(r * r)
    n = Q(r * u)
    T = n / (2 * u)
    delta = Q(1, u)
    m = Q(r)
    k = x * m
    b = Q(1)
    a = 2 * x * b

    # All the transformed SizeWindows hypotheses used for the analytic bound.
    assert r >= 1 and u >= 1
    assert m * u >= r and m <= r * u
    assert delta * u >= 1
    assert n <= 2 * u * T
    assert x * m <= k <= n * n * r / u
    assert 0 <= a <= 2 * x * b

    bracket = T*a*(1+m*m/k) + m*(2*n*m*b*u + delta*k*b*u*u/n)
    normalized = bracket / (T * m * b * delta)
    exact_expansion = a/(m*b*delta)*(1+m*m/k) + (
        2*n*m*u/(T*delta) + k*u*u/(n*T)
    )
    assert normalized == exact_expansion
    assert normalized <= 10*r*u**4
    print(f"r={r:4} u={u:2} normalized_cost={normalized}"
          f"  10*r*u**4={10*r*u**4}")

print("PASS exact negative-cone prefix cost and normalized size-window algebra")
