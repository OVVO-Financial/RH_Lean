"""Exact finite regressions; not a substitute for GitHub Actions Lean proofs."""

from fractions import Fraction as Q


def energy(k, f):
    return sum((f(m) ** 2 / (m * (m + 1)) for m in range(k, 3 * k + 1)), Q(0))


def residue(k, m):
    return Q(m % k, k)


def correction(d, z, m):
    return z - sum((a * residue(k, m) for k, a in d.items()), Q(0))


def main():
    counts = {"variance": 0, "energy_bounds": 0, "source_coordinates": 0}
    for k in [*range(1, 65), 101, 127]:
        weights = [Q(1, m * (m + 1)) for m in range(k, 3 * k + 1)]
        first_moment = sum((Q(m) * w for m, w in zip(range(k, 3 * k + 1), weights)), Q(0))
        for lam in [Q(-7, 3), Q(0), Q(1), Q(11, 5)]:
            optimal_center = lam * first_moment / sum(weights, Q(0))
            for z in [Q(-13, 7), Q(0), 2 * k * lam, optimal_center]:
                actual = sum(((z - lam * m) ** 2 for m in range(k, 3 * k + 1)), Q(0))
                variance = (2 * k + 1) * (z - 2 * k * lam) ** 2
                variance += lam ** 2 * Q(k * (k + 1) * (2 * k + 1), 3)
                assert actual == variance
                sharp = lam ** 2 * Q((k + 1) * (2 * k + 1), 9 * (3 * k + 1))
                coarse = lam ** 2 * Q(6 * k, 81)
                assert energy(k, lambda m: z - lam * m) >= sharp >= coarse
                counts["variance"] += 1
                counts["energy_bounds"] += 1
    for k in range(1, 33):
        d = {3 * k + 1: Q(7, 3), 6 * k: Q(-5, 2)}
        moment = sum((a / n for n, a in d.items()), Q(0))
        center = sum((a * Q(n - 1, 2 * n) for n, a in d.items()), Q(0))
        for z in [Q(-2), Q(0), center]:
            for m in range(0, 3 * k + 1):
                assert correction(d, z, m) == z - moment * m
                counts["source_coordinates"] += 1
            assert energy(k, lambda m: correction(d, z, m)) >= Q(6 * k, 81) * moment ** 2
        for m in range(1, 12 * k + 1):
            centered = -sum((a * (residue(n, m) - Q(n - 1, 2 * n))
                             for n, a in d.items()), Q(0))
            assert correction(d, center, m) == centered
    # Dropping high support is false, even with the actual periodic centering.
    wrong_support = energy(4, lambda m: correction({2: Q(1)}, Q(1, 4), m))
    assert wrong_support == Q(9, 832) < Q(2, 27)
    print("PASS:", counts)
    print("Support falsifier: actual 9/832 < claimed 2/27 when high support is omitted.")
    print("Rational arithmetic only; no local Lean or all-scale numerical inference.")


if __name__ == "__main__":
    main()
