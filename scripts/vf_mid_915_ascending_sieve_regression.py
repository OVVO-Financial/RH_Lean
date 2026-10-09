#!/usr/bin/env python3
"""#915 forward-from-2 arithmetic reconstruction (NOT an RH proof).

Reconstruct both original anchored physical partial-moment coordinates using
only the parity candidate set and distinct, ascending least-prime removals.
These are degree-one physical equalities; this test does NOT establish a
pair-level historical/child-run return or the first-bad sharp payment.

The provisional prefix stages are *not* actual prime configurations, and
their cone slacks need not be nonnegative.
"""
from bisect import bisect_right
from collections import Counter
import math

from vf_mid_sector_six_direct_probe import Arithmetic


SAMPLES = {
    # (cone slack after owner 2, after owner 3, at complete cutoff R)
    18: (89.6259, 165.9134, 104.4918),
    317: (-10120.5805, 25572.5803, 13423.7847),
    1027: (-173464.1413, 211608.3885, 105561.2814),
}


def close(actual, expected, atol=0.06):
    assert math.isclose(actual, expected, rel_tol=1e-9, abs_tol=atol), (
        actual, expected
    )


def stage(R, D, w, removed):
    """Provisional original-carrier signed mass, abs mass, and cone slack."""
    signed = -D + (w - 1) * R + removed
    absolute = abs(D) + (1 - w) * R + (2 * w - 1) * removed
    return signed, absolute, absolute**2 - 2 * signed**2


def square_vf_mid(R):
    return sum((2 * r + 1) / math.log(r * r + r + 0.5)
               for r in range(2, R))


def verify_block(a, R, expected):
    # The completed square endpoint: pi(R^2) minus the native VF midpoint.
    D = bisect_right(a._prime_list, R * R) - square_vf_mid(R)
    w = (2 * R + 1) / (R * math.log(R * R + R + 0.5))
    assert 0 < w < 1, (R, w)

    # Exactly R odd seats after owner 2; every removed seat has a single
    # *least* odd-prime owner. Occurrences are never copied or deduplicated.
    odd_seats = [n for n in range(R * R + 1, (R + 1) ** 2) if n % 2]
    assert len(odd_seats) == R
    owner = Counter(a.spf[n] for n in odd_seats if a.spf[n])
    assert 2 not in owner
    primes = [n for n in odd_seats if a.prime(n)]
    P = len(primes)
    assert sum(owner.values()) + P == R

    # Explicit direct physical charges and original absolute denominator.
    charges = [w - int(a.prime(n)) for n in odd_seats]
    U = max(-D, 0) + sum(max(z, 0) for z in charges)
    L = max(D, 0) + sum(max(-z, 0) for z in charges)
    G_direct = U - L
    T_direct = U + L
    G_final, T_final, B_final = stage(R, D, w, R - P)
    close(G_final, G_direct, 1e-7)
    close(T_final, T_direct, 1e-7)
    close(B_final, 6 * U * L - U * U - L * L, 1e-6)

    # Direct physical recurrence, with no assumed/conjured returned parent.
    VF_R = w * R
    D_next = D + P - VF_R
    close(G_final, -D_next, 1e-7)

    # Each step exposes cross-owner interaction with the entire accumulated
    # source. A child's positive/negative masses need not be cone-admissible.
    C = 0
    observed = {2: stage(R, D, w, 0)[2]}
    for p in a.primes_to(R):
        if p <= 2:
            continue
        d = owner.get(p, 0)
        G_before, T_before, B_before = stage(R, D, w, C)
        G_after, T_after, B_after = stage(R, D, w, C + d)
        close(G_after - G_before, d, 1e-7)
        close(T_after - T_before, (2 * w - 1) * d, 1e-7)
        delta = (2 * d * ((2 * w - 1) * T_before - 2 * G_before)
                 + d * d * ((2 * w - 1) ** 2 - 2))
        close(B_after - B_before, delta, 1e-6)
        C += d
        if p == 3:
            observed[3] = B_after

    assert C == R - P
    observed[R] = stage(R, D, w, C)[2]
    for p, target in zip((2, 3, R), expected):
        close(observed[p], target)
    if R in (317, 1027):
        assert observed[2] < 0 < observed[3]
    assert observed[R] > 0
    print(
        f"R={R}: owner 2 B={observed[2]:.4f}; owner 3 "
        f"B={observed[3]:.4f}; finished B={observed[R]:.4f}; "
        f"original G={G_final:.6f}, abs={T_final:.6f}; PASS"
    )


def main():
    a = Arithmetic((max(SAMPLES) + 1) ** 2)
    for R, values in SAMPLES.items():
        verify_block(a, R, values)
    print("PASS: ascending owner reconstruction preserves signed/abs mass.")
    print("UNPROVED: genuine occurrence-matched pair returns and first-bad payment.")


if __name__ == "__main__":
    main()
