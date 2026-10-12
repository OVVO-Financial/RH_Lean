#!/usr/bin/env python3
"""#919: exact norm-quotient cutoff returns, without unsigned per-norm spending.

The coefficient constructor checks the Euler vs Dirichlet constructions before
this probe uses the returned excluded-six coefficients. Each physical norm is
assigned to exactly one quotient bucket. Two successive signed groupings:

  sum_m a6[m] k(X//m)
    = sum_t k(t) B_X(t)
    = sum_t F(t) (B_X(t)-B_X(t+1)), F(t)=sum_{j=1}^t k(j), |F| <=4.

Finite measurements are NOT a proof of uniform signed variation or first-bad
payment; especially, 36-packets can have either sign.
"""

from array import array
import sys

from vf919_principal_coefficient_check import coefficients, quotient_kernel

EXPECTED = {
    # R: (M, raw_abs, bucket_abs, packet_abs, signed_bucket_variation)
    317: (-28, 22026, 670, 104, 1507),
    548: (234, 65796, 1100, 384, 3296),
    1027: (367, 231177, 2535, 901, 7622),
    3000: (-340, 1972000, 9288, 1810, 24671),
}


def run(roots: tuple[int, ...]) -> None:
    k = [quotient_kernel(t) for t in range(36)]
    primitive = [sum(k[1:t+1]) for t in range(36)]
    assert sum(k) == 0
    assert min(primitive) == -4 and max(primitive) == 4
    assert all(primitive[t % 36] - primitive[(t - 1) % 36]
               == quotient_kernel(t) for t in range(1, 3000))

    # Once a fixed norm has entered the physical support, every 36*m
    # consecutive cutoff sites complete an EXACT zero-sum return cycle.
    # These are temporal returns, not simultaneous owner-to-owner payments.
    for m in (1, 7, 13, 31, 97, 503):
        for start in (1, 5, 317):
            samples = [quotient_kernel(x // m)
                       for x in range(m * start, m * (start + 36))]
            assert sum(samples) == 0
            assert sum(max(z, 0) for z in samples) == 10 * m
            assert sum(min(z, 0) for z in samples) == -10 * m

    upper = max(roots) ** 2 - 1
    mu, grouped = coefficients(upper)
    print('R,M,raw_abs,bucket_abs,period36_abs,bucket_variation,positive_packets,negative_packets')

    for r in roots:
        x = r * r - 1
        bucket = array('q', [0]) * (x + 2)
        raw_abs = 0
        for m in range(1, x + 1):
            a = grouped[m] if m % 2 and m % 3 else 0
            if a:
                t = x // m
                term = a * quotient_kernel(t)
                bucket[t] += a
                raw_abs += abs(term)

        msum = sum(mu[1:x + 1]); signed_bucket = 0; signed_abel = 0
        bucket_abs = 0; signed_variation = 0
        for t in range(1, x + 1):
            term = quotient_kernel(t) * bucket[t]
            delta = bucket[t] - bucket[t + 1]
            signed_bucket += term
            signed_abel += primitive[t % 36] * delta
            bucket_abs += abs(term)
            signed_variation += abs(delta)
        assert signed_bucket == signed_abel == msum
        assert abs(msum) <= 4 * signed_variation
        assert bucket[x + 1] == 0

        packets = [sum(quotient_kernel(t) * bucket[t]
                       for t in range(36 * i + 1, min(x + 1, 36 * (i + 1) + 1)))
                   for i in range((x + 35) // 36)]
        assert sum(packets) == msum
        packet_abs = sum(map(abs, packets))
        assert abs(msum) <= packet_abs <= bucket_abs <= raw_abs
        assert any(z > 0 for z in packets) and any(z < 0 for z in packets)
        obtained = (msum, raw_abs, bucket_abs, packet_abs, signed_variation)
        assert obtained == EXPECTED[r], (r, obtained, EXPECTED[r])
        print(f'{r},{msum},{raw_abs},{bucket_abs},{packet_abs},'
              f'{signed_variation},{sum(z > 0 for z in packets)},'
              f'{sum(z < 0 for z in packets)}')

    print('Every tested quotient occurrence, exact signed Abel return, 36m clock and two-sided packet sign checked.')
    print('No bound uniform in R and no historical Sector Six first-bad payment is asserted.')


if __name__ == '__main__':
    run((317, 548, 1027, 3000) if '--extended' in sys.argv else (317, 548, 1027))
