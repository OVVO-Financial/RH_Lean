#!/usr/bin/env python3
"""Exact constants for section 4 of the absolute-A research audit.

This certifies arithmetic constants, not the external Hurst theorem or Lean.
The full all-integer base is checked by absolute_a_signed_estimate_audit.cpp.
"""
from fractions import Fraction


def main():
    a = Fraction(43, 100)
    beta_upper = Fraction(82, 125)
    b = Fraction(1837, 1000)
    delta = Fraction(1)
    for p in (2, 3, 5, 7):
        delta *= 1 - Fraction(1, p * p)
    assert delta == Fraction(768, 1225)
    assert a < beta_upper**2
    assert delta < Fraction(627, 1000)
    assert beta_upper * b / 2 + delta / 4 + 16 < 17
    upper = beta_upper * b + Fraction(627, 1000) + Fraction(17, 10000)
    assert upper == Fraction(458443, 250000)
    assert upper < b < Fraction(1837625, 1000000)
    assert Fraction(3, 2) < b**2
    print(f"a={a}; B={b}; delta={delta}; induction_upper={upper}")
    print(f"exact induction slack={b-upper}; all rational checks passed")


if __name__ == "__main__":
    main()
