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
    # Six-prime first-crossing certificate (section 4.3).
    delta6 = Fraction(1)
    for p in (2, 3, 5, 7, 11, 13):
        delta6 *= 1 - Fraction(1, p * p)
    assert delta6 == Fraction(442368, 715715)
    for threshold, barrier in (
        (Fraction(1837, 1000), Fraction(4356, 10000)),
        (Fraction(14701, 8000), Fraction(4357, 10000)),
    ):
        residual = threshold - delta6 - (delta6 / 4 + 64) / 10000
        denominator = threshold * (1 + Fraction(1, 20000))
        assert residual > 0
        ratio = (residual / denominator) ** 2
        assert ratio > barrier
        print(
            f"first-crossing B={threshold}; delta6={delta6}; "
            f"ratio={ratio}; decimal={float(ratio):.17f}; "
            f"strict_barrier={barrier}"
        )



if __name__ == "__main__":
    main()
