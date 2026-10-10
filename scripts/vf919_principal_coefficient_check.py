#!/usr/bin/env python3
"""Independent finite arithmetic checks for #919's principal coefficient map.

Integer Euler factors and Dirichlet convolution are computed independently.
These checks reproduce the cancellation census; they assert no uniform bound.
The corresponding all-cutoff algebraic identities are checked separately in Lean.
"""

from array import array


def chi(n: int) -> int:
    return (0, 1, -1)[n % 3]


def character_prefix(n: int) -> int:
    return int(n % 3 == 1)


def quotient_kernel(n: int) -> int:
    return (character_prefix(n) - character_prefix(n // 3)
            - character_prefix(n // 4) + character_prefix(n // 12))


def coefficients(limit: int) -> tuple[array, array]:
    """Actual rational mu and grouped ideal mu from local Euler polynomials."""
    spf = array('i', [0]) * (limit + 1)
    mu = array('i', [0]) * (limit + 1)
    primes: list[int] = []
    mu[1] = 1
    for n in range(2, limit + 1):
        if not spf[n]:
            spf[n] = n
            primes.append(n)
            mu[n] = -1
        for p in primes:
            if p * n > limit:
                break
            spf[p * n] = p
            if n % p == 0:
                break
            mu[p * n] = -mu[n]

    grouped = array('i', [0]) * (limit + 1)
    grouped[1] = 1
    for n in range(2, limit + 1):
        p = spf[n]
        parent, exponent = n, 0
        while parent % p == 0:
            parent //= p
            exponent += 1
        if p == 3:  # 1 - t, with norm 3
            local = -1 if exponent == 1 else 0
        elif p % 3 == 1:  # (1 - t)^2, two distinct split ideals
            local = -2 if exponent == 1 else 1 if exponent == 2 else 0
        else:  # 1 - t^2, one inert ideal of norm p^2
            local = -1 if exponent == 2 else 0
        grouped[n] = local * grouped[parent]

    # Second construction: a_F = mu * (chi pointwise mu).
    convolution = array('i', [0]) * (limit + 1)
    for d in range(1, limit + 1):
        factor = chi(d) * mu[d]
        if factor:
            for m in range(1, limit // d + 1):
                convolution[d * m] += factor * mu[m]
    assert grouped == convolution, 'Euler factors disagree with convolution'
    return mu, grouped


def check() -> None:
    expected = {317: (10999, -11027, -28),
                548: (33015, -32781, 234),
                1027: (115772, -115405, 367)}
    mu, grouped = coefficients(max(expected) ** 2 - 1)
    excluded = array('i', (a if n % 2 and n % 3 else 0
                           for n, a in enumerate(grouped)))

    residues = [quotient_kernel(j) for j in range(36)]
    assert min(residues) == -2 and max(residues) == 1
    assert sum(residues) == 0
    running = 0
    for n in range(1, 4097):
        running += chi(n)
        assert running == character_prefix(n)
        assert quotient_kernel(n) == quotient_kernel(n + 36)

    # Check the literal excluded factors at every tested norm, not only totals.
    for n in range(1, len(grouped)):
        restored = excluded[n]
        if n % 3 == 0:
            restored -= excluded[n // 3]
        if n % 4 == 0:
            restored -= excluded[n // 4]
        if n % 12 == 0:
            restored += excluded[n // 12]
        assert restored == grouped[n], n

    print('R,positive,negative,net,absolute_contribution')
    for r, target in expected.items():
        x = r * r - 1
        positive = negative = 0
        for m in range(1, x + 1):
            term = excluded[m] * quotient_kernel(x // m)
            positive += max(term, 0)
            negative += min(term, 0)
        net = sum(mu[1:x + 1])
        assert (positive, negative, net) == target
        assert positive + negative == net
        print(f'{r},{positive},{negative},{net},{positive - negative}')


if __name__ == '__main__':
    check()
