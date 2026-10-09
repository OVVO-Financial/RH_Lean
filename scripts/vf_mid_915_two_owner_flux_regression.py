#!/usr/bin/env python3
"""#915: exact physical two-owner exit-return flux and positive-response curvature.

Uses actual primes and the original signed VF active-seat weights. This checks
the one-dimensional zero-extended toggle carrier, NOT a proved isomorphism to
the historical/current first-owner quadratic Co/Div source.
"""
import math


def prime_table(N):
    prime = bytearray(b'\x01') * (N + 1)
    prime[:2] = b'\x00\x00'
    for p in range(2, math.isqrt(N) + 1):
        if prime[p]:
            prime[p * p:N + 1:p] = b'\x00' * ((N - p * p) // p + 1)
    return prime


def squarefree_table(N, prime):
    sqfree = bytearray(b'\x01') * (N + 1)
    sqfree[0] = 0
    for p in range(2, math.isqrt(N) + 1):
        if prime[p]:
            sqfree[p * p:N + 1:p * p] = b'\x00' * ((N - p * p) // (p * p) + 1)
    return sqfree


def toggle(p, n):
    return n // p if n % p == 0 else p * n


def response(R, m):
    lo, hi = R * R, (R + 1) ** 2
    return math.fsum(math.log(t) for t in range(lo // m + 1, hi // m + 1))


def active_weight(R, t, prime):
    if not (R * R < t < (R + 1) ** 2) or t % 2 == 0:
        return 0.
    w = (2 * R + 1) / (R * math.log(R * R + R + .5))
    return w - int(bool(prime[t]))


def signed_flux(R, prime, sqfree, p, q):
    """Enumerate all nonzero exclusive-path terminal occurrences for p,q.

    An explicitly squarefree terminal t has exactly one of p,q, and the initial state
    n is obtained by replacing that factor with the other prime. Each (n,t)
    is enumerated once for this fixed ordered owner pair, not identified
    with any signed historical pair of #915.
    """
    X = (R + 1) ** 2 - 1
    sums = [0., 0.]
    count = [0, 0]
    prime_terminal = [0, 0]
    examples = []
    for t in range((R * R + 1) | 1, X + 1, 2):
        if not sqfree[t]:
            continue
        w = active_weight(R, t, prime)
        for d, other in ((p, q), (q, p)):
            if t % d or t % other == 0 or t % (d * d) == 0:
                continue
            k = t // d
            n = k * other
            if n <= 0 or n > X:
                continue
            assert sqfree[n]
            after_p = toggle(p, n)
            after_q = toggle(q, n)
            terminal_pq = toggle(q, after_p)
            terminal_qp = toggle(p, after_q)
            assert terminal_pq == terminal_qp == t
            first = after_p <= X
            second = after_q <= X
            # Checked exclusive-intermediate signed Stokes formula.
            assert first != second
            contribution = w * (int(first) - int(second))
            if contribution > 0:
                count[0] += 1
                sums[0] += contribution
                prime_terminal[0] += int(prime[t])
            elif contribution < 0:
                count[1] += 1
                sums[1] += contribution
                prime_terminal[1] += int(prime[t])
            if len(examples) < 2:
                examples.append((n, t, after_p, after_q, round(contribution, 9)))
    # Every terminal having a low-prime owner is an ACTUAL COMPOSITE.
    assert prime_terminal == [0, 0]
    # For p<q, the original current-block active weight of each nonzero
    # exclusive path is positive, not an automatically favorable CoDiv mate.
    assert count[1] == 0 and sums[1] == 0.
    return count, sums, examples


def curvature(R, m, p, q):
    # Independent direct four-term physical response.
    direct = (response(R, m) - response(R, m * p) -
              response(R, m * q) + response(R, m * p * q))
    lo, hi = R * R, (R + 1) ** 2
    counts = [0, 0, 0, 0]
    terms = []
    for t in range(lo // m + 1, hi // m + 1):
        bp, bq = t % p == 0, t % q == 0
        if not bp and not bq:
            counts[0] += 1
            terms.append(math.log(t))
        elif bp and not bq:
            counts[1] += 1
            terms.append(math.log(p))
        elif bq and not bp:
            counts[2] += 1
            terms.append(math.log(q))
        else:
            counts[3] += 1
    # Exact Boolean atom identity, checked against the actual cofactor
    # response; the difference is floating-point evaluation only.
    rhs = math.fsum(terms)
    assert abs(direct-rhs) < 4e-8 * max(1, abs(rhs)), (R,m,p,q,direct,rhs)
    assert rhs >= 0
    return rhs, counts


def main():
    primes = prime_table(1028 ** 2)
    sqfree = squarefree_table(1028 ** 2, primes)
    for R in (8, 18, 56, 317, 1027):
        pairs = [(3, 5), (5, 7), (11, 13)]
        if R >= 23:
            pairs.append((19, 23))
        for p, q in pairs:
            if q > R:
                continue
            counts, weights, examples = signed_flux(R, primes, sqfree, p, q)
            print('FLUX R=%d p=%d q=%d firstOnly=%d reverseOnly=%d '
                  'signed=%.9f example=%s PASS'
                  % (R,p,q,*counts,sum(weights),examples))
        for m in (1, 2, 3, 5, 7, 11):
            if m >= R:
                continue
            for p, q in ((3,5),(5,7),(11,13)):
                if q > R:
                    continue
                value, classes = curvature(R,m,p,q)
                assert value >= 0
                print('CURV R=%d m=%d p=%d q=%d value=%.6f bins=%s PASS'
                      % (R,m,p,q,value,classes))
    print('PASS finite geometric signed path flux and mixed physical log curvature')
    print('OPEN first-owner incidence to historical/current anchored CoDiv transport')


if __name__ == '__main__':
    main()
