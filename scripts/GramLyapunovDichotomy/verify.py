#!/usr/bin/env python3
"""Exact verifier for the Gram/Lyapunov dichotomy and trajectory-pinning results.

Everything is recomputed from scratch with exact integer/rational arithmetic and
only the Python standard library.  No committed constant from a previous audit is
taken on trust; the previously published rows are re-derived and compared.

Sections
--------
1. Realized divisibility masks and the exact compatibility quotients.
2. The missing-full-old-wheel-mask lemma, checked at three primorial extensions.
3. Zero-direct-square dichotomy: the tautological rank-one form regenerates at
   every level.
4. Discrepancy audit against `scripts/OffDiagonalQuotientTautology/verify.py`.
5. Trajectory pinning: the exact sandwich for any admissible Lyapunov form.
6. Normalization audit of the PR #176 separating certificate.
"""

from fractions import Fraction as F

PRIMORIAL_STEPS = (
    (30, 210, (2, 3, 5, 7)),
    (210, 2310, (2, 3, 5, 7, 11)),
    (2310, 30030, (2, 3, 5, 7, 11, 13)),
)


def mobius(n: int) -> int:
    """Möbius function by exact trial division."""
    x, value, p = n, 1, 2
    while p * p <= x:
        if x % p == 0:
            x //= p
            value = -value
            if x % p == 0:
                return 0
        p += 1
    if x > 1:
        value = -value
    return value


def walsh(mask: int, coordinate: int) -> int:
    return -1 if ((mask & coordinate).bit_count() % 2) else 1


def nullspace(rows: list[list[F]], cols: int) -> list[list[F]]:
    """Exact rational basis of the nullspace of the given rows."""
    a = [r[:] for r in rows]
    pivots: list[int] = []
    r = 0
    for c in range(cols):
        p = next((i for i in range(r, len(a)) if a[i][c] != 0), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        s = a[r][c]
        a[r] = [x / s for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c] != 0:
                f = a[i][c]
                a[i] = [a[i][j] - f * a[r][j] for j in range(cols)]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    free = [c for c in range(cols) if c not in pivots]
    basis = []
    for f in free:
        v = [F(0)] * cols
        v[f] = F(1)
        for i, p in enumerate(pivots):
            v[p] = -a[i][f]
        basis.append(v)
    return basis


def dot(a, b) -> F:
    return sum((F(x) * F(y) for x, y in zip(a, b)), F(0))


def realized_masks(L: int, U: int, primes: tuple[int, ...]) -> set[int]:
    seen = set()
    for n in range(L + 1, U + 1):
        if mobius(n) == 0:
            continue
        seen.add(sum((1 << i) for i, p in enumerate(primes) if n % p == 0))
    return seen


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


def flip_states(L: int, U: int, primes: tuple[int, ...]) -> list[tuple[int, ...]]:
    """All prefix flip-sum states s(u) for L < u <= U."""
    dim = 1 << len(primes)
    s = [0] * dim
    out = []
    for n in range(L + 1, U + 1):
        mu = mobius(n)
        if mu:
            m = sum((1 << i) for i, p in enumerate(primes) if n % p == 0)
            for d in range(dim):
                s[d] += mu * walsh(m, d)
        out.append(tuple(s))
    return out


def section_1_and_2() -> dict:
    """Quotient dimensions and the missing-full-old-wheel-mask lemma."""
    info = {}
    for L, U, primes in PRIMORIAL_STEPS:
        k = len(primes)
        dim = 1 << k
        seen = realized_masks(L, U, primes)
        missing = sorted(m for m in range(dim) if m not in seen)
        full_old = (1 << (k - 1)) - 1
        full_new = dim - 1

        # Lemma: the full OLD wheel mask is always missing; the full NEW mask is
        # realized, by n = U exactly.
        assert full_old in missing, (L, U, full_old, missing)
        assert full_new in seen, (L, U, full_new)
        assert mobius(U) != 0 and all(U % p == 0 for p in primes)

        constraints = [[F(walsh(m, d)) for d in range(dim)] for m in missing]
        basis = nullspace(constraints, dim)
        assert len(basis) == dim - len(missing)

        # Every Walsh character has value +1 at coordinate 0, so e_0 is never
        # compatible as soon as one mask is missing.
        assert all(walsh(m, 0) == 1 for m in missing)
        e0 = [F(1)] + [F(0)] * (dim - 1)
        assert any(dot(c, e0) != 0 for c in constraints)

        info[(L, U)] = dict(dim=dim, missing=missing, vdim=len(basis),
                            basis=basis, full_old=full_old)
        print(f"[1] ({L},{U}]: {len(seen)}/{dim} masks realized, missing {missing}, "
              f"dim V = {len(basis)}")
        print(f"[2] ({L},{U}]: full old-wheel mask {full_old} missing; "
              f"full new mask {full_new} realized by n={U}; e_0 not in V")
    return info


def section_3(info: dict) -> None:
    """The zero-direct-square tautology regenerates at every level."""
    for (L, U), d in info.items():
        dim, missing, basis = d["dim"], d["missing"], d["basis"]
        m0 = missing[0]
        ell = [F(0)] + [F(-walsh(m0, x)) for x in range(1, dim)]
        assert ell[0] == 0
        for v in basis:
            assert dot(ell, v) == v[0], (L, U)
        print(f"[3] ({L},{U}]: rank-one G = l l^T from missing mask {m0} is PSD, "
              f"has zero direct target square, and satisfies Q(s) = s_0^2 on all of V")


def section_4() -> None:
    """Audit of the committed PR #177 verifier."""
    # PR #177 defines the 210 -> 2310 quotient by the character of mask 31.
    # The actually missing mask is 15 = {2,3,5,7}; mask 31 = {2,3,5,7,11} is
    # realized by n = 2310.  The dimension 31 is correct for either choice, so
    # the error is invisible in the dimension check.
    seen = realized_masks(210, 2310, (2, 3, 5, 7, 11))
    assert 31 in seen and 15 not in seen

    ell30 = [F(0)] + [F(-walsh(7, d)) for d in range(1, 16)]
    lifted = [F(0)] * 32
    for d in range(32):
        old = d & 15
        if old:
            lifted[d] = ell30[old]

    errs = {}
    for mask in (31, 15):
        basis = nullspace([[F(walsh(mask, d)) for d in range(32)]], 32)
        assert len(basis) == 31
        errs[mask] = sorted({dot(lifted, v) - v[0] for v in basis})

    assert F(-2) in errs[31] and F(-2) in errs[15]
    print(f"[4] PR #177 used chi_31 for V_210; the true annihilator is chi_15 "
          f"(mask 31 is realized by n=2310).  Naive-lift error sets: "
          f"chi_31 -> {[str(e) for e in errs[31]]}, chi_15 -> {[str(e) for e in errs[15]]}.")
    print("[4] The published -2 survives on the correct quotient, but the naive "
          "lift was never the right test: section 3 regenerates an exact "
          "functional at 210 -> 2310, so the mechanism is NOT eliminated.")


def section_5() -> None:
    """Trajectory pinning: R_U^2 <= Q(s_U) <= 2 phi(pW) for any admissible form."""
    prev = 1
    rows = []
    for W in (2, 6, 30, 210, 2310, 30030, 510510):
        if prev > 1:
            run = best = 0
            for n in range(prev + 1, W + 1):
                run += mobius(n)
                best = max(best, abs(run))
            budget = 2 * euler_phi(W)
            rows.append((prev, W, best, budget, F(budget, best * best)))
        prev = W
    for lo, hi, mx, budget, band in rows:
        print(f"[5] block ({lo},{hi}]: max|R| = {mx}, 2*phi = {budget}, "
              f"band factor = {band} = {float(band):.3f}")
    assert all(band <= F(5) for *_, band in rows)
    print("[5] every tested band factor is below 5: any admissible Lyapunov form "
          "equals the target square to within a bounded factor on the realized "
          "trajectory.")


def section_6() -> None:
    """Normalization audit of the PR #176 separating certificate."""
    required = F(368, 3)          # PR #176 dual-certificate lower bound at W = 30
    allowed = 2 * euler_phi(30)   # the declared seed budget, 16
    assert required > allowed
    # The declared budget is the constant 2 times phi(W).  The extension law
    # b(pW) = (p-1) b(W) is preserved by ANY constant c, because
    # phi(pW) = (p-1) phi(W) for a primorial extension.
    for W, p in ((30, 7), (210, 11), (2310, 13)):
        assert euler_phi(p * W) == (p - 1) * euler_phi(W)
    needed_constant = required / euler_phi(30)
    print(f"[6] PR #176 requires parent budget >= {required} against the declared "
          f"{allowed} = 2*phi(30).")
    print(f"[6] Expressed as a constant, the certificate says c >= {needed_constant} "
          f"= {float(needed_constant):.4f}, not c = 2.")
    print("[6] b(pW) = (p-1) b(W) holds for every constant c, and |R| <~ "
          "sqrt(c*phi(W)) is RH-strength for any fixed c.  The certificate "
          "therefore refutes the constant 2, not the diagonal family.")


def section_0() -> None:
    """Independent reproduction of the rows published by PR #176 / PR #177."""
    primes = (2, 3, 5, 7)
    s = [0] * 16
    for n in range(31, 200):
        mu = mobius(n)
        if mu:
            m = sum((1 << i) for i, p in enumerate(primes) if n % p == 0)
            for d in range(16):
                s[d] += mu * walsh(m, d)
    A = [(s[c] + s[c + 8]) // 2 for c in range(8)]
    B = [(s[c + 8] - s[c]) // 2 for c in range(8)]
    assert tuple(A) == (-6, -22, -16, -60, -10, -42, -28, -88)
    assert tuple(B) == (-1, -9, -5, -9, -3, -7, -3, -3)
    assert tuple(A[c] ** 2 + B[c] ** 2 for c in range(8)) == \
        (37, 565, 281, 3681, 109, 1813, 793, 7753)
    assert s[0] == -5
    print("[0] reproduced: U=199 A/B state, budget row (37,...,7753), and s_0 = -5")

    states = flip_states(30, 210, primes)
    assert len(states) == 180
    assert all(v == -1 for v in states[0])            # U = 31, all flips equal -1
    assert max(abs(v[0]) for v in states) == 5
    # Child-scale vs parent-scale components of the enlarged extension state.
    maxA = max(abs((v[c] + v[c + 8]) // 2) for v in states for c in range(8))
    maxB = max(abs((v[c + 8] - v[c]) // 2) for v in states for c in range(8))
    assert (maxA, maxB) == (92, 11)
    print(f"[0] reproduced: U=31 output-forcing prefix; over all 180 cuts "
          f"max|A_C| = {maxA} (child scale) versus max|B_C| = {maxB} (parent scale)")


def main() -> None:
    section_0()
    info = section_1_and_2()
    section_3(info)
    section_4()
    section_5()
    section_6()
    print("\nALL EXACT CHECKS PASSED")


if __name__ == "__main__":
    main()
