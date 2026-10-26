#!/usr/bin/env python3
"""Finite-field falsifier for original OAI composite-s Gauss / quadratic-J CRT.

Standard library only. Tests local finite fields F_7,F_13,F_19,F_25,F_121.
This does NOT evaluate the full compensated detector or prove its bounds.
"""
from cmath import exp, pi
from fractions import Fraction as F
from math import sqrt


class Field:
    def __init__(self, p, degree=1):
        assert degree in (1, 2)
        if degree == 2:
            assert p % 3 == 2  # omega^2 + omega + 1 irreducible
        self.p = p
        self.degree = degree
        self.elements = [
            (a,) if degree == 1 else (a, b)
            for a in range(p)
            for b in (range(p) if degree == 2 else [0])
        ]
        self.zero = (0,) * degree
        self.one = (1,) + (0,) * (degree - 1)
        self.q = len(self.elements)
        assert (self.q - 1) % 6 == 0

        def multiply(a, b):
            if degree == 1:
                return ((a[0] * b[0]) % p,)
            x, y = a
            z, w = b
            return ((x * z - y * w) % p, (x * w + y * z - y * w) % p)

        self.multiply = multiply

        def power(a, n):
            result = self.one
            for _ in range(n):
                result = multiply(result, a)
            return result

        self.power = power
        self.generator = next(
            g for g in self.elements
            if g != self.zero and
            len({power(g, k) for k in range(self.q - 1)}) == self.q - 1
        )
        self.logs = {power(self.generator, k): k for k in range(self.q - 1)}

    def character(self, x, exponent):
        # Even exponent 0 is the PRINCIPAL multiplicative character:
        # zero on nonunits, one on units.
        if x == self.zero:
            return 0j
        return exp(2j * pi * ((self.logs[x] * exponent) % 6) / 6)

    def psi(self, x):
        trace = x[0] if self.degree == 1 else (2 * x[0] - x[1]) % self.p
        return exp(2j * pi * trace / self.p)

    def transform(self, values):
        return {
            xi: sum(
                values[x] * self.psi(self.multiply(xi, x)).conjugate()
                for x in self.elements
            )
            for xi in self.elements
        }


def test_local():
    for p, degree in [(7, 1), (13, 1), (19, 1), (5, 2), (11, 2)]:
        field = Field(p, degree)
        q = field.q
        max_ratio = 0.0

        for outer_exp in range(1, 13):
            gauss = {
                n: sum(
                    field.character(x, outer_exp) *
                    field.psi(field.multiply(n, x))
                    for x in field.elements
                )
                for n in field.elements
            }
            second = field.transform(gauss)
            assert max(
                abs(second[xi] - q * field.character(xi, outer_exp))
                for xi in field.elements
            ) < 1e-8 * q
            assert abs(second[field.zero]) < 1e-8 * q

            for col_incidence in (0, 1):
                for j_valuation in range(6):
                    if outer_exp >= 2 and (col_incidence or j_valuation):
                        # The original source vanishes: outer deficiency
                        # forces a shared I/J prime to divide m.
                        continue
                    e = col_incidence + 3 * j_valuation
                    local = {
                        n: gauss[n] * field.character(n, e)
                        if e else gauss[n]
                        for n in field.elements
                    }
                    coeffs = field.transform(local)
                    largest = max(abs(z) for z in coeffs.values())
                    budget = q ** (1 + col_incidence / 2 + j_valuation / 2)
                    max_ratio = max(max_ratio, largest / budget)
                    assert largest <= budget * (1 + 1e-10), (
                        q, outer_exp, col_incidence, j_valuation,
                        largest, budget
                    )
                    if outer_exp == 1 and col_incidence == 1 and j_valuation % 2 == 0:
                        # Principal s|I resonance REALLY needs the sqrt(q)
                        # allowance in the global sqrt(N(I)) ledger.
                        assert largest >= .7 * q * sqrt(q)
        print(f"F_{q}: Gauss double transform and all admitted local cases PASS; "
              f"max/budget={max_ratio:.12f}")


def test_exponents():
    eta = F(1, 384)
    lam = F(1, 384)
    for sigma in (F(0), F(1, 8), F(1, 6)):
        old = F(5, 32) + (sigma + eta) / 3 + F(7, 2) * lam
        new = -F(1, 96) + (sigma + eta) / 6 + 4 * lam
        assert new < F(3, 16)
        print(f"sigma={sigma}: previous={old} improved={new}, "
              f"margin={F(3, 16)-new}")
    assert F(5, 32) - F(1, 8) / 6 == F(13, 96)
    print("Exact rational exponent ledger PASS")



def test_prime_power_lift():
    # The actual prime-power Gauss sum has support p^(a-1)|m,
    # and reduces to p^(a-1) times the local prime Gauss factor.
    # Includes the sixth-principal exponent a=6.
    fld = Field(7, 1)
    p = fld.p
    for a in (1, 2, 3, 6):
        modulus = p ** a
        def chi(x):
            return fld.character((x % p,), a)
        def g(m):
            return sum(chi(x) * exp(2j*pi*((m*x) % modulus)/modulus)
                       for x in range(modulus))
        for m in (1, p ** (a-1), 2*p ** (a-1), 0):
            if m % (p ** (a-1)):
                expected = 0j
            else:
                n = m // (p ** (a-1))
                expected = p ** (a-1) * sum(
                    chi(x) * exp(2j*pi*((n*x) % p)/p)
                    for x in range(p)
                )
            actual = g(m)
            assert abs(actual-expected) < 1e-8*(1+abs(expected)), (a,m,actual,expected)
        print(f"p=7, outer exponent {a}: exact prime-power lift PASS")

if __name__ == "__main__":
    test_local()
    test_prime_power_lift()
    test_exponents()
