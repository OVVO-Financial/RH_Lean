"""Exact prime-log arithmetic for the original changed-low Nyman source.

These finite checks are not a Lean execution or an asymptotic norm proof.
"""

from fractions import Fraction as Q


def add(a, b):
    out = a.copy()
    for p, v in b.items():
        out[p] = out.get(p, Q(0)) + v
    return {p: v for p, v in out.items() if v}


def scale(a, c):
    return {p: v * c for p, v in a.items() if v * c}


def sub(a, b):
    return add(a, scale(b, -1))


def total(xs):
    out = {}
    for x in xs:
        out = add(out, x)
    return out


def factors(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def mu(n):
    fs = factors(n)
    return 0 if any(e > 1 for e in fs.values()) else (-1) ** len(fs)


def log(n):
    assert n >= 1
    return {p: Q(e) for p, e in factors(n).items()}


def kernel(n, h, k):
    return scale(sub(log(n), log(max(h, k))), mu(k))


def tail(b, m):
    return total(scale(sub(log(b), log(k)), mu(k) * (m // k))
                 for k in range(b + 1, m + 1))


def verify(n, h, correction):
    ell = sub(log(n), log(h))
    flat = {k: kernel(n, h, k) for k in range(1, n + 1)}
    moment = total(scale(flat[k], Q(1, k)) for k in flat)
    hmoment = total(scale(correction.get(k, {}), Q(1, k))
                    for k in range(2, n + 1))
    defect = sub(moment, hmoment)
    low_zero = all(not correction.get(k) for k in range(2, h + 1))
    count = 0
    head = []
    for m in range(1, 2 * n + 2):
        direct = sub(ell, total(
            scale(sub(correction.get(k, {}), flat[k]), Q(m % k, k))
            for k in range(2, n + 1)))
        returned = add(scale(defect, m), add(sub(tail(n, m), tail(h, m)),
            total(scale(correction.get(k, {}), m // k)
                  for k in range(2, n + 1))))
        assert direct == returned, (n, h, m, direct, returned)
        if m <= h:
            head.append(not direct)
            if low_zero and not defect:
                assert not direct
        count += 1
    if low_zero:
        assert all(head) == (not defect)
    return count


def main():
    counts = {"arbitrary_corrections": 0, "two_band_returns": 0,
              "two_band_moments": 0, "head_cases": 0}
    for n in range(2, 25):
        for h in range(1, n):
            for correction in ({}, {n: log(2)}, {2: log(3), n: log(5)}):
                counts["arbitrary_corrections"] += verify(n, h, correction)
    for k0 in range(1, 7):
        n = 6 * k0
        i1, i2 = range(3 * k0 + 1, 4 * k0 + 1), range(5 * k0 + 1, n + 1)
        s1, s2 = sum((Q(1, k) for k in i1), Q(0)), sum((Q(1, k) for k in i2), Q(0))
        assert s1 - s2 > Q(1, 20)
        for h in range(2, n // 2 + 1):
            ell = sub(log(n), log(h))
            flat = {k: kernel(n, h, k) for k in range(1, n + 1)}
            u = total(scale(flat[k], Q(1, k)) for k in flat)
            v = add(scale(ell, 2), total(flat.values()))
            a = scale(sub(u, scale(v, s2 / k0)), 1 / (s1 - s2))
            z = scale(sub(scale(v, s1 / k0), u), 1 / (s1 - s2))
            correction = {k: a for k in i1} | {k: z for k in i2}
            assert total(scale(correction.get(k, {}), Q(1, k)) for k in range(2, n + 1)) == u
            assert total(correction.values()) == v
            # Check both original coefficient moments without dividing by ell.
            numerators = {k: sub(correction.get(k, {}), flat[k]) for k in range(2, n + 1)}
            assert total(scale(x, Q(1, k)) for k, x in numerators.items()) == ell
            assert total(scale(x, Q(k - 1, 2 * k)) for k, x in numerators.items()) == ell
            counts["two_band_moments"] += 1
            counts["head_cases"] += h
            counts["two_band_returns"] += verify(n, h, correction)
    # m=0 is outside the positive-index theorem: the residual is exactly one.
    assert sub(log(6), log(2))
    print("PASS:", counts)
    print("Exact prime-log vectors; no floating point or local Lean execution.")


if __name__ == "__main__":
    main()
