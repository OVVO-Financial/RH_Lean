#!/usr/bin/env python3
"""Exact rational exponent audit for genuine OAI local source at a=3/4.

This DOES NOT establish Hecke family admission, row spread, actual Mellin
normalization, or the high-row detector. Finite power accounting only.
"""
from fractions import Fraction as F

A = F(3, 4)
Z = F(17, 50)
E_MAX = F(1, 1000)


def cubic_exponents(a: F, k: F):
    """U=P^k; row norm cap/mean ratio not included."""
    return {
        "row": 1 - 2*a,
        "cube_count": 2 - 2*a - F(2, 3)*k,
        "mixed": F(5, 3) - 2*a - k/F(3),
    }


def sextic_exponents(k: F):
    """n=6 sieve, square norm P^-1 at e=0, per U row volume."""
    return {
        "row": -1,
        "prime_count": -1 + (1-k),
        "first_cross": -1 + F(1, 3) - k/F(6),
        "second_cross": -1 + F(5, 6) - F(2, 3)*k,
    }


def actual_tiers(a: F, z: F, e: F):
    """Coherent dyadic AMPLITUDE exponents; row-principal handled as amplitude."""
    x = a + 16*e
    w = 1-a-6*e
    return {
        "BR_amplitude": 1 + 4 - 5*x - 6*z,
        "BKV_amplitude": 1 + 1 - w - 6*z,
        "principal_amplitude": 1 - x - 2*w,
        "D_sq_tail_amplitude": 1 - 2*x,
        "V_tail_amplitude": 1 - 6*z,
    }


for k, expected_c, expected_s in [
    (F(5, 4), F(-1, 4), F(-7, 8)),
    (F(2), F(-1, 2), F(-1)),
]:
    cub = cubic_exponents(A, k)
    sex = sextic_exponents(k)
    assert max(cub.values()) == expected_c, (k, cub)
    assert max(sex.values()) == expected_s, (k, sex)
    print(f"U=P^{k} cubic E/W: {cub} -> P^{expected_c}")
    print(f"U=P^{k} sextic E/W: {sex} -> P^{expected_s}")

at_zero = actual_tiers(A, Z, F(0))
at_max = actual_tiers(A, Z, E_MAX)
assert at_zero == {
    "BR_amplitude": F(-79, 100),
    "BKV_amplitude": F(-29, 100),
    "principal_amplitude": F(-1, 4),
    "D_sq_tail_amplitude": F(-1, 2),
    "V_tail_amplitude": F(-26, 25),
}, at_zero
assert all(v < 0 for v in at_zero.values())
assert all(v < 0 for v in at_max.values())
assert at_max["BKV_amplitude"] == F(-71, 250)
print(f"a=3/4, z=17/50, e=0 absolute tiers: {at_zero}")
print(f"a=3/4, z=17/50, e=1/1000 absolute tiers: {at_max}")
print("PASS: local exponent arithmetic. Does not imply a full-source power saving.")

# Fourth-moment replacement for the missing per-fiber spread estimate:
# H(u)^2 reindexes as a cubic character sum over cube-free p*q, norm P^2.
# Collision cap <=2 gives squared pair coefficients P^(2-4a).
def cubic_pair_fourth_exponents(a: F, k: F):
    return {
        "rows": 2-4*a,
        "pair_modulus": 2-4*a + 2-k,
        "mixed": 2-4*a + F(2,3)*(k+2)-k,
    }

for k, expected_fourth, delta_threshold in [
    (F(5,4),F(-1,12),F(1,15)),
    (F(2),F(-1,3),F(1,6)),
]:
    four=cubic_pair_fourth_exponents(A,k)
    assert max(four.values()) == expected_fourth, (k,four)
    # Physical W-fourth overhead U^delta; Holder square root gives
    # energy / U exponent <= (k*delta+expected_fourth)/2.
    assert (k*delta_threshold + expected_fourth)/2 == 0
    assert (k*0 + expected_fourth)/2 < 0
    print(f"U=P^{k} pair-lift cubic H^4/U: {four} -> P^{expected_fourth}; "
          f"weighted energy power survives when delta < {delta_threshold}")
print("PASS: exact pair-lift arithmetic; physical fourth moment/family matching still open.")
