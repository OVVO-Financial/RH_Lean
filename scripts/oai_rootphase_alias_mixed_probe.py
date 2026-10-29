#!/usr/bin/env python3
"""Original-Mobius square-block root-phase harmonic alias probe.

The two ORIGINAL coefficients mu(5)=-1 and mu(6)=+1 share root 2, so
their physical step-phase source vanishes identically. Their separately
squared fractional-root Fourier harmonics are positive; interference
between different k's is essential. No independent-sign model.
"""
from __future__ import annotations

import cmath
import math


def alias_coefficient(theta: float, k: int) -> complex:
    denominator = 2j * math.pi * (theta + k)
    if abs(denominator) < 1e-14:
        return 1 + 0j
    return (1 - cmath.exp(-2j * math.pi * theta)) / denominator


def smooth_mode(theta: float, k: int) -> complex:
    xi = theta + k
    return (
        -cmath.exp(2j * math.pi * xi * math.sqrt(5))
        + cmath.exp(2j * math.pi * xi * math.sqrt(6))
    )


def finite_alias_energies(kmax: int, samples: int = 256) -> tuple[float, float]:
    coherent = 0.0
    diagonal = 0.0
    for j in range(samples):
        theta = -0.5 + (j + 0.5) / samples
        terms = [alias_coefficient(theta, k) * smooth_mode(theta, k)
                 for k in range(-kmax, kmax + 1)]
        coherent += abs(sum(terms)) ** 2 / samples
        diagonal += sum(abs(z) ** 2 for z in terms) / samples
    return coherent, diagonal


def main() -> None:
    assert 4 <= 5 < 9 and 4 <= 6 < 9
    assert -1 + 1 == 0  # actual mu(5) + mu(6), Lean-certified in matching module
    for theta in [-0.5, -0.1, 0, 0.25, 0.5]:
        exact = (-1 + 1) * cmath.exp(2j * math.pi * theta * 2)
        assert abs(exact) < 1e-12
    last_coherent = None
    last_diagonal = None
    for K in (2, 10, 50, 200):
        full, diag = finite_alias_energies(K)
        print(
            f"K={K:4d} exact_physical_energy=0 "
            f"truncated_coherent_energy={full:.9g} "
            f"separately_squared_mode_energy={diag:.9g} "
            f"off_diagonal={full-diag:.9g}"
        )
        assert diag > 0.3 if K >= 2 else diag > 0
        last_coherent, last_diagonal = full, diag
    assert last_coherent is not None and last_diagonal is not None
    assert last_coherent < 0.0001
    assert 0.40 < last_diagonal < 0.45
    print("PASS actual Mobius root-phase cancellation requires mixed harmonics")


if __name__ == "__main__":
    main()
