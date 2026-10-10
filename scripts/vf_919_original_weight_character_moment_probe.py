#!/usr/bin/env python3
"""Exact character-orthogonality test of ORIGINAL VF physical weights.

A=2634, B=5267; real prime semiprime cells A<p<q, pq<B^2.
For a small prime modulus m, all these p*q are units mod m.
For S_a=sum_(pq=a mod m) w(sqrt(pq)), orthogonality proves
  sum_(chi != principal) |sum_(p<q) w(pq)*chi(pq)|^2
      = (m-1) * sum_(a=1 to m-1) (S_a - mean S)^2.
Compare to a CONSTANT weight equal to the ACTUAL mean w so
overall scaling does NOT masquerade as spectral cancellation.

This is a REAL finite spectral diagnostic, NOT OpenAI's sextic
Hecke moment and NOT the full signed Sector Six Gram.
"""
import math

A, B = 2634, 5267
MAX = 4 * A
MODS = (5, 7, 11, 13, 17, 19, 31, 37, 61, 101, 257)


def sieve(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if flags[p]:
            flags[p * p::p] = b"\x00" * ((limit - p * p) // p + 1)
    return flags


def main():
    prime = sieve(MAX)
    counts = {m: [0] * (m - 1) for m in MODS}
    weights = {m: [0.0] * (m - 1) for m in MODS}
    n_pairs, total_w = 0, 0.0

    for p in range(A + 1, B):
        if not prime[p]:
            continue
        upper = (B * B - 1) // p
        for q in range(p + 1, upper + 1):
            if not prime[q]:
                continue
            r = math.isqrt(p * q)
            w = (2 * r + 1) / (r * math.log(r * r + r + 0.5))
            n_pairs += 1
            total_w += w
            for m in MODS:
                cls = (p * q) % m
                assert cls != 0, (p, q, m)
                counts[m][cls - 1] += 1
                weights[m][cls - 1] += w

    assert n_pairs == 125272
    meanw = total_w / n_pairs
    ratios = {}
    for m in MODS:
        mean_n = n_pairs / (m - 1)
        mean_weight = total_w / (m - 1)
        flat_variance = sum((x - mean_n) ** 2 for x in counts[m])
        weighted_variance = sum((x - mean_weight) ** 2 for x in weights[m])
        assert flat_variance > 0
        normalized_ratio = weighted_variance / (meanw ** 2 * flat_variance)
        ratios[m] = normalized_ratio

    assert abs(ratios[5] - 1.033473) < 0.0005
    assert abs(ratios[7] - 1.014375) < 0.0005
    assert abs(ratios[13] - 0.975033) < 0.0005
    assert abs(ratios[31] - 0.997693) < 0.0005
    assert abs(ratios[61] - 0.990516) < 0.0005
    assert abs(ratios[257] - 1.003298) < 0.0005

    print("VF919_CHAR_MOMENT original_vs_flat A=%d B=%d "
          "semiprimes=%d mean_original_weight=%.12f" %
          (A, B, n_pairs, meanw))
    for m in MODS:
        print(" modulus=%3d nonprincipal_second_moment_ratio=%.6f" %
              (m, ratios[m]))
    print("PASS: original VF weights yield no systematic extra "
          "nonprincipal cancellation in these FINITE fixed-modulus "
          "tests; no asymptotic conclusion is justified, and a new "
          "SIGNED historical/CoDiv cross-moment estimate is still open.")


if __name__ == "__main__":
    main()
