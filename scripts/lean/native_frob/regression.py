"""Finite independent enumeration, including degenerate factors and noninjective images."""

from math import gcd, isqrt

primes = [p for p in range(2, 44) if all(p % d for d in range(2, isqrt(p) + 1))]
moduli = pairs = powers = images = 0
for n in range(1, 193):
    moduli += 1
    units = {x for x in range(n) if gcd(x, n) == 1}
    for p in primes:
        pairs += 1
        b = n
        while b % p == 0:
            b //= p
        a = n // b
        f = (1 + a * (((p - 1) * pow(a, -1, b)) % b)) % n
        assert {x for x in units if x % a == 1 % a and x % b == p % b} == {f}
        kernel = {x for x in units if x % b == 1 % b}
        phi_a = sum(gcd(x, a) == 1 for x in range(a))
        for i in range(6):
            powers += 1
            fibre = {x for x in units if x % b == pow(p, i, b)}
            assert fibre == {(v * pow(f, i, n)) % n for v in kernel}
            assert len(fibre) == phi_a
            squared = {x*x % n for x in units}
            shift = pow(pow(f, 2*i, n), -1, n)
            image_kernel = {v*v % n for v in kernel}
            assert {g for g in squared if g*shift % n in image_kernel} == {u*u % n for u in fibre}
            images += 1
assert (moduli, pairs, powers, images) == (192, 2688, 16128, 16128)
print(f'{moduli} moduli; {pairs} unique CRT witnesses; {powers} raw fibres; {images} square-map images')
