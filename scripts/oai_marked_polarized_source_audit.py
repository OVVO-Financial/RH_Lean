#!/usr/bin/env python3
"""Exact-formula regression for #997 polarized pre-norm NNS fourth moments.

Four sextic exponents come from RH_Lean's certified finite ideal witnesses.
The derivative-profile weights below are illustrative log norm weights,
not a claim to be OAI's annular logProfile source.
"""
import cmath
import math

ZETA = [cmath.exp(math.pi * 1j * k / 3) for k in range(6)]
WITNESSES = [
    ("x317", (5, 5, 1, 1), 2, -2),
    ("x1027", (1, 3, 3, 5), -1, 1),
    ("R317", (0, 4, 2, 0), 1, -1),
    ("R1027", (3, 1, 5, 3), -1, 1),
]

def near(a, b):
    return math.isclose(a, b, rel_tol=1e-10, abs_tol=1e-8)

def energy(a):
    z = sum(a)
    return abs(z) ** 2

def nns_parts(a):
    K = sum(abs(z) ** 2 for z in a)
    P, N = 0.0, 0.0
    for i in range(len(a)):
        for j in range(i + 1, len(a)):
            zi, zj = a[i], a[j]
            xi, yi = (zi.real - zi.imag, zi.real + zi.imag)
            xj, yj = (zj.real - zj.imag, zj.real + zj.imag)
            signed = (xi * xj + yi * yj) / 2
            P += max(signed, 0)
            N += max(-signed, 0)
    E = energy(a)
    assert near(E, K + 2 * (P - N))
    return E, K, P, N

def polarized(a, b):
    Ej, Kj, Pj, Nj = nns_parts(a)
    Ek, Kk, Pk, Nk = nns_parts(b)
    diagonal = Kj * Kk
    positive = 2 * (Kj * Pk + Kk * Pj)
    negative = -2 * (Kj * Nk + Kk * Nj)
    residual = 4 * (Pj - Nj) * (Pk - Nk)
    assert near(Ej * Ek, diagonal + positive + negative + residual)
    return diagonal, positive, negative, residual, Ej * Ek

S = [0.0] * 5
for name, exps, expected, expected_selected in WITNESSES:
    atoms = [ZETA[i] for i in exps]
    total = sum(atoms)
    selected = sum(-ZETA[(-i) % 6] for i in exps)
    assert near(total.real, expected) and near(total.imag, 0)
    assert near(selected.real, expected_selected)
    E, K, P, N = nns_parts(atoms)
    D, pos, neg, res, moment = polarized(atoms, atoms)
    assert near(moment, abs(total) ** 4)
    for j, k in ((0,0), (0,1), (1,0), (0,2), (1,1), (2,0)):
        logs = [math.log(7 + 2 * r) for r in range(len(atoms))]
        aj = [a * l**j for a, l in zip(atoms, logs)]
        ak = [a * l**k for a, l in zip(atoms, logs)]
        d, p, n, q, mk = polarized(aj, ak)
        assert near(mk, energy(aj)*energy(ak))
    for x, item in enumerate((D, pos, neg, res, moment)):
        S[x] += item
    print(f"{name}: K={K:.0f}, pairUPM={P:.1f}, pairLPM={N:.1f}, "
          f"negative_payment={neg:.0f}, fourth={moment:.0f}")
assert all(near(v, ref) for v, ref in zip(S, (64, 80, -152, 27, 19))), S
print("Four native ideal phase fibres: 19 = 64 + 80 - 152 + 27")

# Mixed derivative rows need not have a positive polarized residual.
d, p, n, q, moment = polarized([1, 1], [1, -1])
assert q < 0 and near(moment, 0)
print(f"Mixed polarized residual can be negative: {q:.0f}")

# A full character family gives Parseval/Jensen; an incomplete subfamily does not.
# Group Z/2, coefficient (1,-1), its trivial and sign characters.
f_trivial, f_sign = 1 - 1, 1 + 1
convolution = (1*1 + (-1)*(-1), 1*(-1) + (-1)*1)
resonant = sum(abs(x)**2 for x in convolution)
assert near(resonant, 8)
assert near((abs(f_trivial)**4 + abs(f_sign)**4)/2, resonant)
assert abs(f_trivial)**4 == 0 < resonant
print("Orthogonal full-dual fourth=8, incomplete trivial-only fourth=0, resonant=8")

# Euler prime-toggle: equal scalar weights do not cancel phase -1.
W = 3 + 2j
phase = -1
twisted = W - phase * W
scalar_difference = W - W
phase_correction = (1 - phase) * W
assert abs(twisted - scalar_difference - phase_correction) < 1e-12
assert near(abs(twisted), 2*abs(W))

# Same [U,2U] dyadic cutoff admits no paired interior for prime norm >= 2.
U = 100
for prime_norm in (2, 3, 5):
    overlap = [n for n in range(U, 2*U+1) if U <= prime_norm*n <= 2*U]
    assert overlap == ([U] if prime_norm==2 else [])
print("Same dyadic window has no interior prime-toggle pairing for norm >= 2")
print("PASS exact polarized fourth, genuine phase arrays, Parseval caveat, twisted Euler pairing")
