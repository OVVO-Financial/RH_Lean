"""Exact finite checks for CP1 sampling, not all-scale proof evidence."""

from fractions import Fraction
from math import isqrt


def mobius_prefix(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    prime = [True] * (limit + 1)
    prime[0:2] = [False, False]
    for p in range(2, limit + 1):
        if not prime[p]:
            continue
        for n in range(p, limit + 1, p):
            mu[n] = -mu[n]
            if n > p:
                prime[n] = False
        for n in range(p * p, limit + 1, p * p):
            mu[n] = 0
    prefix = [0] * (limit + 1)
    for n in range(1, limit + 1):
        prefix[n] = prefix[n - 1] + mu[n]
    return prefix, prime


def main():
    roots = list(range(2, 129)) + [256, 317, 1027]
    maximum = (max(roots) + 1) ** 2
    mertens, prime = mobius_prefix(maximum)
    parent_count = daughter_count = divisible_count = birth_count = 0
    nonzero_error = None
    nonmultiple_failure = None
    for r in roots:
        endpoint = r * r - 1
        # Exact left endpoint and points immediately before the next block.
        samples = [Fraction(endpoint), Fraction(endpoint) + Fraction(1, 3),
                   Fraction(r * r + r, 1), Fraction((r + 1) ** 2 - 1) - Fraction(1, 7)]
        for x in samples:
            root = isqrt((x + 1).__floor__())
            assert root == r
            n = x.__floor__()
            assert endpoint <= n <= endpoint + 2 * r
            parent_error = mertens[endpoint] - mertens[r - 1] - mertens[n]
            assert parent_error * parent_error <= 16 * x
            parent_count += 1
            for q in range(1, isqrt(r) + 2):
                active = q * q < r
                literal = mertens[endpoint // (q * q)] if active else 0
                dilated = mertens[(x / (q * q)).__floor__()] if active else 0
                error = literal - dilated
                assert error * error * q**4 <= (16 * x if active else 0)
                if active:
                    assert abs(error) * q * q <= 3 * r
                if active and error and nonzero_error is None and q > 2 and prime[q]:
                    nonzero_error = (r, q, str(x), literal, dilated)
                daughter_count += 1
        for q in range(1, min(r, 41) + 1):
            literal = endpoint // (q * q)
            rounded = max((r // q) ** 2 - 1, 0)
            if r % q == 0:
                assert literal == rounded
                divisible_count += 1
            elif literal != rounded and nonmultiple_failure is None:
                nonmultiple_failure = (r, q, literal, rounded)
    for q in range(1, 41):
        birth = q * q + 1
        assert ((birth * birth - 1) // (q * q)) == q * q + 2
        if q > 2 and prime[q]:
            def admitted(r):
                return q <= r - 1 and q * q < r
            assert not admitted(q * q)
            assert admitted(birth)
            birth_count += 1
    assert nonzero_error is not None
    assert nonmultiple_failure is not None
    print(f"PASS: {parent_count} exact rational parent samples; {daughter_count} masked daughter samples")
    print(f"PASS: {divisible_count} divisible-root identities; {birth_count} odd-prime births")
    print(f"Nonzero genuine daughter sampling error (r,q,x,literal,dilated): {nonzero_error}")
    print(f"Divisibility hypothesis cannot be dropped (r,q,literal,rounded): {nonmultiple_failure}")
    print("Finite regressions only; universal certification requires Lean Actions.")


if __name__ == "__main__":
    main()
