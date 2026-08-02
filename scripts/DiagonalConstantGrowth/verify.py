#!/usr/bin/env python3
"""Exact verifier for the required-constant growth test of the diagonal family.

Discharges the criterion predeclared in `research/GRAM_LYAPUNOV_DICHOTOMY.md`:
a separating certificate closes a Gram family only if the required constant
`c_k = b_k / phi(W_k)` grows along the extension chain.

Two exact rational certificates are checked, for the canonical test family (all
realized prefix states of the block, used both as test vectors and budget cuts):

* `30 -> 210`   a DUAL-feasible point, proving   b_1 >= 7819/216;
* `210 -> 2310` a PRIMAL-feasible point, proving b_2 <= 23511351/250000.

Together these give `c_2 < c_1` — the constant falls, so the certificate method
exhibits no growth and the diagonal family is NOT closed.

Only the Python standard library is used.
"""

from fractions import Fraction as F


# ---------------------------------------------------------------- arithmetic

def mobius_sieve(n: int) -> list[int]:
    mu = [1] * (n + 1)
    primes: list[int] = []
    composite = [False] * (n + 1)
    for i in range(2, n + 1):
        if not composite[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            composite[i * p] = True
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def walsh(mask: int, coordinate: int) -> int:
    return -1 if ((mask & coordinate).bit_count() % 2) else 1


def euler_phi(n: int) -> int:
    result, x, p = n, n, 2
    while p * p <= x:
        if x % p == 0:
            while x % p == 0:
                x //= p
            result -= result // p
        p += 1
    if x > 1:
        result -= result // x
    return result


def prefix_states(L: int, U: int, primes: tuple[int, ...]) -> list[tuple[int, ...]]:
    """Distinct flip states s(u) for L < u <= U, in a deterministic order."""
    dim = 1 << len(primes)
    mu = mobius_sieve(U)
    s = [0] * dim
    seen = []
    for n in range(L + 1, U + 1):
        if mu[n]:
            m = sum((1 << i) for i, q in enumerate(primes) if n % q == 0)
            for d in range(dim):
                s[d] += mu[n] * walsh(m, d)
        seen.append(tuple(s))
    return sorted(set(seen))


# ------------------------------------------------------- embedded certificates

# 30 -> 210: exact DUAL-feasible point (support 10) proving a lower bound on b_1.
LEVEL1_LAMBDA = {92: F(11, 8), 93: F(20831, 6912), 94: F(10043, 2304), 102: F(29, 216)}
LEVEL1_MU = {82: F(13, 192), 93: F(443, 768), 94: F(821, 768), 103: F(5, 48), 106: F(5, 24)}
LEVEL1_NU = {0: F(1)}
LEVEL1_BOUND = F(7819, 216)

# 210 -> 2310: exact PRIMAL-feasible point proving an upper bound on b_2.
LEVEL2_X = [
    "27977/1000000", "0", "0", "53541/250000", "0", "1377/200000", "0", "71081/200000",
    "0", "0", "0", "0", "0", "0", "0", "884993/1000000", "0", "0", "433/500000",
    "99503/1000000", "0", "0", "0", "150031/500000", "179/31250", "14151/1000000",
    "0", "0", "0", "287/250000", "0",
]
LEVEL2_Y = [
    "40971/250000", "0", "1027/200000", "127/250000", "6419/200000", "69/125000",
    "767/1000000", "0", "56037/1000000", "0", "0", "0", "0", "0", "0", "0",
]
LEVEL2_BOUND = F(23511351, 250000)


# ------------------------------------------------------------------- checking

def check_level1_dual() -> F:
    """Verify dual feasibility at 30 -> 210, returning the certified lower bound."""
    primes = (2, 3, 5, 7)
    dim, half, p = 16, 8, 7
    tests = prefix_states(30, 210, primes)
    cuts = tests
    assert len(tests) == 110, len(tests)

    lam = {tests[i]: v for i, v in LEVEL1_LAMBDA.items()}
    mu = {tests[i]: v for i, v in LEVEL1_MU.items()}
    nu = {cuts[i]: v for i, v in LEVEL1_NU.items()}
    assert all(v >= 0 for v in list(lam.values()) + list(mu.values()) + list(nu.values()))

    # dual row for each child weight x_D, D != 0
    for D in range(1, dim):
        lhs = sum((c * v[D] ** 2 for v, c in lam.items()), F(0)) \
            - sum((c * v[D] ** 2 for v, c in mu.items()), F(0))
        assert lhs <= 0, (D, lhs)

    # dual row for each parent weight y_C
    for C in range(half):
        lhs = F(p - 1, 2) * sum((c * (v[C] ** 2 + v[C + half] ** 2) for v, c in mu.items()), F(0)) \
            - sum((c * F(u[C] ** 2 + u[C + half] ** 2, 2) for u, c in nu.items()), F(0))
        assert lhs <= 0, (C, lhs)

    # dual row for b
    assert sum(nu.values(), F(0)) <= 1

    bound = sum((c * v[0] ** 2 for v, c in lam.items()), F(0))
    assert bound == LEVEL1_BOUND, (bound, LEVEL1_BOUND)
    return bound


def check_level2_primal() -> F:
    """Verify primal feasibility at 210 -> 2310, returning the certified upper bound."""
    primes = (2, 3, 5, 7, 11)
    dim, half, p = 32, 16, 11
    tests = prefix_states(210, 2310, primes)
    cuts = tests
    assert len(tests) == 1231, len(tests)

    x = [F(t) for t in LEVEL2_X]          # weights for coordinates D = 1..31
    y = [F(t) for t in LEVEL2_Y]
    assert len(x) == dim - 1 and len(y) == half
    assert all(t >= 0 for t in x + y)

    def qx(v):
        return sum((x[D - 1] * v[D] ** 2 for D in range(1, dim)), F(0))

    def qy(v):
        return sum((y[C] * (v[C] ** 2 + v[C + half] ** 2) for C in range(half)), F(0))

    for v in tests:
        assert qx(v) >= v[0] ** 2, ("output domination", v[0])
        assert F(p - 1, 2) * qy(v) >= qx(v), "extension compatibility"

    bound = max(qy(u) / 2 for u in cuts)
    assert bound == LEVEL2_BOUND, (bound, LEVEL2_BOUND)
    return bound


def check_interval_mismatch() -> None:
    """The two components of the enlarged state live on different intervals."""
    rows = ((6, 30, 7), (30, 210, 11), (210, 2310, 13))
    for prev, W, p in rows:
        # A sums over the child block (W, pW]; B over the dilate (W/p, U/p].
        assert F(W, p) != prev, (W, p, prev)
        print(f"  ({W},{p * W}]: A on (W,pW] length {p * W - W}; "
              f"B on (W/p,W] = ({float(F(W, p)):.2f},{W}]; parent block ({prev},{W}] "
              f"length {W - prev}  ->  W/p != W_prev")

    # Scale separation over all 180 cuts of (30,210].
    states = prefix_states(30, 210, (2, 3, 5, 7))
    mA = max(abs((v[C] + v[C + 8]) // 2) for v in states for C in range(8))
    mB = max(abs((v[C + 8] - v[C]) // 2) for v in states for C in range(8))
    assert (mA, mB) == (92, 11), (mA, mB)
    print(f"  scale separation over (30,210]: max|A_C| = {mA} (child) vs "
          f"max|B_C| = {mB} (parent), under a declared budget of 16")


def main() -> None:
    b1 = check_level1_dual()
    phi1 = euler_phi(30)
    c1 = b1 / phi1
    print(f"[1] 30 -> 210    exact dual certificate:   b_1 >= {b1} = {float(b1):.6f}")
    print(f"[1]              phi(30) = {phi1}          c_1 >= {c1} = {float(c1):.7f}")

    b2 = check_level2_primal()
    phi2 = euler_phi(210)
    c2 = b2 / phi2
    print(f"[2] 210 -> 2310  exact primal certificate: b_2 <= {b2} = {float(b2):.6f}")
    print(f"[2]              phi(210) = {phi2}         c_2 <= {c2} = {float(c2):.7f}")

    assert c2 < c1
    print(f"[3] RESULT: c_2 <= {float(c2):.7f} < {float(c1):.7f} <= c_1   "
          f"(ratio at most {float(c2 / c1):.4f})")
    print("[3] The required constant FALLS across the first two primorial extensions.")
    print("[3] Predeclared criterion: closure requires UNBOUNDED c_k.  Not exhibited.")
    print("[3] CLASSIFICATION: the non-circular diagonal family is NOT closed; PR #176")
    print("    remains OPEN AT A LARGER CONSTANT.")
    print("[3] These are bounds for the declared finite test family only; they do NOT")
    print("    prove the true minimal constants decrease.  See the report's confounds.")

    print("[4] State-closure obstruction (interval mismatch):")
    check_interval_mismatch()

    print("\nALL EXACT CHECKS PASSED")


if __name__ == "__main__":
    main()
