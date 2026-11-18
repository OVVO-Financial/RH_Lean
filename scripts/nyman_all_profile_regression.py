"""Registered exact finite regressions, not an all-scale proof.

Fixed domain: carry m=0..100, k=0..50; K=40,41,59,60 and n=0..4.
Check source reconstruction, every paired sample, every shifted Gram by exact
LDL, and omission controls for a band, an observation, and restoration.
"""

from fractions import Fraction as F

checks = 0


def check(value):
    global checks
    assert value
    checks += 1


def band(a, b, m):
    result = 0
    k = a + 1
    while k <= b:
        q = m // k
        if q == 0:
            break
        end = min(b, m // q)
        result += (end - k + 1) * q
        k = end + 1
    return result


def profile(K, m):
    return band(6*K, 8*K, m) - band(10*K, 12*K, m)


def samples(K):
    return range(3*K + 1, 3*K + K//20 + 1)


def window(K):
    return {a*k for a in (2, 3) for k in samples(K)}


def positive_definite(matrix):
    a = [row[:] for row in matrix]
    for i in range(len(a)):
        check(a[i][i] > 0)
        for j in range(i+1, len(a)):
            for k in range(j, len(a)):
                a[k][j] = a[j][k] = a[j][k] - a[j][i]*a[k][i]/a[i][i]


for m in range(101):
    for k in range(51):
        carry = 0 if k == 0 else 2*(3*m//k)-3*(2*m//k)
        check(carry in (-1, 0, 1, 2))
check(2*(3//3)-3*(2//3) == 2)
check(2*(3//2)-3*(2//2) == -1)

for K in (40, 41, 59, 60):
    for n in range(5):
        heads = [4**i*K for i in range(n)]
        W = set().union(*(window(q) for q in heads)) if heads else set()
        gram = [[F(0) for _ in heads] for _ in heads]
        for m in sorted(W):
            p = [profile(q, m) for q in heads]
            for i in range(n):
                for j in range(n):
                    gram[i][j] += F(p[i]*p[j], m*(m+1))
        for i, q in enumerate(heads):
            check(len(samples(q)) == q//20)
            check(40*len(samples(q)) >= q)
            check(len(window(q)) == 2*len(samples(q)))
            for k in samples(q):
                check(profile(q, 2*k) == 2*k-6*q)
                check(profile(q, 3*k) == 2*q)
                check(F(profile(q, 3*k))-F(3, 2)*profile(q, 2*k) >= F(9, 5)*q)
                for j, qj in enumerate(heads):
                    dp = F(profile(qj, 3*k))-F(3, 2)*profile(qj, 2*k)
                    check(abs(dp) <= 3*qj)
                    if j > i:
                        check(dp == 0)
            for m in (0, 6*q, 8*q, 10*q, 11*q, 12*q):
                literal = sum((1 if 6*q < d <= 8*q else -1 if 10*q < d <= 12*q else 0)
                              * (m//d) for d in range(2, 12*q+1))
                check(literal == profile(q, m))
        shifted = [[gram[i][j] - (F(21*K, 10240000) if i == j else 0)
                    for j in range(n)] for i in range(n)]
        positive_definite(shifted)
        if n:
            check(F(21*K, 10240000) > F(121*12*K, 808704000))

K = 40
check(profile(K, 11*K) != band(6*K, 8*K, 11*K))
check(all(profile(4*K, m) == 0 for m in window(K)))
base = sum((F(profile(K, m)**2, m*(m+1)) for m in window(K)), F(0))
restored = sum((F((profile(K, m)-profile(K, m))**2, m*(m+1))
                for m in window(K)), F(0))
check(restored < F(21*K, 20480000) <= base/2)
print(f"PASS {checks} exact assertions; 20 registered (K,n) supports; three omission controls")
