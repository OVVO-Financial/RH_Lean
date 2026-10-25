#!/usr/bin/env python3
"""Finite Eisenstein 2D sixth-power count: the P^(1/6) ABSOLUTE
exceptional-frequency exponent cannot be improved by sparsity alone.

All nonzero sixth powers satisfy the original ExceptionalFrequency
valuation condition for EVERY fixed conductor. This probe verifies the
constructive lower bound for a wedge of the Eisenstein lattice.

The bound concerns an ABSOLUTE sum of nonnegative Fourier weights;
it is NOT a lower bound for the signed Gram/source sum itself.
"""
from math import isclose


def eis_mul(x, y):
    a, b = x
    c, d = y
    return (a*c - b*d, a*d + b*c - b*d)


def eis_pow(x, e):
    z = (1, 0)
    for _ in range(e):
        z = eis_mul(z, x)
    return z


def eis_norm(x):
    a, b = x
    return a*a - a*b + b*b


def check(M):
    # Sector a>=2b>0 and a<=3b has angular width < pi/3;
    # multiplication by sixth roots of unity cannot identify distinct
    # nonzero points inside it.
    points = [(a, b) for b in range(1, M + 1)
              for a in range(2*b, 3*b + 1)]
    sixths = [eis_pow(z, 6) for z in points]
    expected = M * (M + 3) // 2
    assert len(points) == expected
    assert len(set(sixths)) == expected, "sixth-power injection failed"
    Hroot = 7 * M * M
    H = Hroot ** 6
    for z, k in zip(points, sixths):
        assert eis_norm(z) <= Hroot
        assert eis_norm(k) == eis_norm(z) ** 6
        assert eis_norm(k) <= H
    weighted = sum(1.0 / (1.0 + eis_norm(k) / H) ** 2
                   for k in sixths)
    lower = expected / 4.0
    assert weighted + 1e-9 >= lower
    ratio = weighted / Hroot
    assert ratio >= (M + 3) / (56 * M) - 1e-9
    print(f"M={M:3d} sixth_frequencies={expected:6d} "
          f"H_1_6={Hroot:6d} weight={weighted:9.4f} "
          f"weight/H_1_6={ratio:.7f} >= {1/56:.7f}")


def main():
    for M in (1, 2, 3, 5, 10, 25, 50, 100):
        check(M)
    # The construction gives arbitrary large M, and the analytical
    # counting lower bound is #points/4 >= H^(1/6)/56.
    print("PASS: explicit Eisenstein sixth-power family has absolute "
          "weighted mass >= H^(1/6)/56 at unbounded H.")
    print("NO assertion about signed exceptional coefficients or 7/8.")


if __name__ == "__main__":
    main()
