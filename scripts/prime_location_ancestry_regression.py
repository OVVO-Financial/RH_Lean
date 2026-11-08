#!/usr/bin/env python3
"""Independent genuine-prime spatial ancestry falsifiers at LARGE square roots.
No Mathlib data, no stochastic model, no unproven asymptotic prime theorem.
"""
from math import gcd, isqrt

ROOTS = {
    2857: (183, 183), 2858: (174, 174), 2859: (167, 191),
    8524: (467, 467), 8525: (463, 512),
    8911: (503, 503), 8912: (512, 467),
}

def sieve(n):
    prime = bytearray(b"\x01") * (n + 1)
    prime[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if prime[p]:
            prime[p*p:n+1:p] = b"\x00" * ((n - p*p) // p + 1)
    return prime

def phase_counts(prime, r):
    a = r*r+1
    b = a+r
    c = (r+1)*(r+1)
    return sum(prime[a:b]), sum(prime[b:c])

def wheel_counts(r, modulus):
    a = r*r+1
    b = a+r
    c = (r+1)*(r+1)
    return (sum(gcd(x, modulus)==1 for x in range(a,b)),
            sum(gcd(x, modulus)==1 for x in range(b,c)))

def main():
    prime = sieve((max(ROOTS)+1)**2)
    for r, expected in ROOTS.items():
        got = phase_counts(prime,r)
        assert got == expected, (r,got,expected)
        print(f"actual R={r}, left={got[0]}, right={got[1]}, difference={got[0]-got[1]}")
    # This is an arbitrarily large exact FIXED-WHEEL arithmetic mechanism,
    # NOT an example of supercritical spatial imbalance of actual primes.
    for k in [1,2,3,17,100,1000,10000]:
        r=6*k+4
        old=wheel_counts(r,2)
        new=wheel_counts(r,6)
        assert old[0]==old[1] and new[0]-new[1]==1, (r,old,new)
        print(f"wheel R={r}: parity left/right={old}, 2x3 left/right={new}")
    # Every fixed period is spatially regular to O(W); larger prime
    # ownership is needed for any supercritical relative clustering.
    for w in [2,6,30,210,2310]:
        for r in [1000,1001,3657,8912,10000]:
            left,right=wheel_counts(r,w)
            assert abs(left-right) < w, (w,r,left,right)
    print("PASS all genuine-prime and finite-wheel checks")

if __name__=="__main__":
    main()
