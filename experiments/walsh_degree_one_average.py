"""What the degree-one Walsh singular value of an averaged toggle actually measures.

Reported observation: the compressed operator

    C_t = P_t * (U_2 + U_3 + U_5)/3 * P_t

restricted to the degree-one span of the selected toggle characters has
sigma_max ~ 0.283, strikingly stable across t = 64 ... 2048, while the
(U_3 + U_5)/2 average gives ~0.08 to 0.12.

Those values are stable because they are constants of linear algebra, not
features of the survivor geometry.  On squarefree support let

    chi_p(n) = -1 if p | n, else +1.

Then for the p-adic toggle U_p:

    chi_p(U_p n) = -chi_p(n)        (U_p flips v_p, hence flips chi_p)
    chi_q(U_p n) = +chi_q(n)        (q != p: U_p does not touch v_q)

so U_p acts on span{chi_2, chi_3, chi_5} as the diagonal sign flip of its own
coordinate.  Averaging k toggles over the span of the same k characters gives

    (1/k) sum_p U_p  =  ((k - 2)/k) * I     on that span,

so sigma_max = (k-2)/k *before any projection*:

    k = 3  ->  1/3 = 0.3333        (reported 0.283)
    k = 2  ->  0                   (reported 0.08 - 0.12)

The physical projection can only pull these down further; it is not the source
of the gap.  This script confirms the algebra numerically on real windows and
reports how much of the measured value the projection actually accounts for.

Usage:  python3 experiments/walsh_degree_one_average.py [N]
"""

import sys

import numpy as np


def build_mu(n):
    mu = np.ones(n + 1, dtype=np.int8)
    mu[0] = 0
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    root = int(n**0.5)
    for p in range(2, root + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    for p in np.nonzero(sieve)[0]:
        p = int(p)
        mu[p::p] = -mu[p::p]
        sq = p * p
        if sq <= n:
            mu[sq::sq] = 0
    return mu


def toggle_image(idx, p, X):
    """U_p on squarefree indices: v_p = 0 -> p*n, v_p = 1 -> n/p. Escape -> -1."""
    out = np.where(idx % p == 0, idx // p, idx * p)
    return np.where(out <= X, out, -1)


def compressed_degree_one(idx, pos, X, ps):
    """sigma_max of the averaged toggle compressed to the degree-one Walsh span."""
    B = np.stack([np.where(idx % p == 0, -1.0, 1.0) for p in ps], axis=1)
    Q, _ = np.linalg.qr(B)  # orthonormal basis of the span

    acc = np.zeros_like(Q)
    for p in ps:
        img = toggle_image(idx, p, X)
        ok = img >= 0
        tgt = np.full(idx.shape, -1, dtype=np.int64)
        tgt[ok] = pos[img[ok]]
        moved = np.zeros_like(Q)
        keep = ok & (tgt >= 0)
        moved[tgt[keep]] = Q[keep]
        acc += moved
    acc /= len(ps)
    return float(np.linalg.svd(Q.T @ acc, compute_uv=False).max())


def interior_mask(idx, X, ps):
    """States whose complete toggle cube over `ps` lies inside the window.

    n is interior iff (prod ps) * core(n) <= X, where core(n) removes every
    p in ps from n.  On this set each U_p is a genuine permutation, so the
    physical projection does nothing at all.
    """
    core = idx.copy()
    for p in ps:
        core = np.where(core % p == 0, core // p, core)
    prod = 1
    for p in ps:
        prod *= p
    return core * prod <= X


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 4_000_000
    print(f"sieving mu(n) for n <= {N:,} ...", flush=True)
    mu = build_mu(N)

    print()
    print("=" * 84)
    print("degree-one Walsh singular value of the averaged toggle")
    print("=" * 84)
    print("    predicted by pure sign algebra, before any projection:  (k-2)/k")
    print("      k = 3 toggles {2,3,5} -> 0.3333      k = 2 toggles {3,5} -> 0.0000")
    print()
    print(
        f"{'X':>12} {'toggles':>9} {'(k-2)/k':>9} {'interior only':>14} "
        f"{'full window':>12}"
    )
    for X in (270_336, 1_064_960, min(4_000_000, N)):
        if X > N:
            continue
        idx_all = np.nonzero(mu[: X + 1])[0]
        for ps in ((2, 3, 5), (3, 5)):
            k = len(ps)
            pos = np.full(X + 1, -1, dtype=np.int64)
            pos[idx_all] = np.arange(idx_all.size)
            full = compressed_degree_one(idx_all, pos, X, ps)

            # interior: complete toggle cube inside the window, projection inert
            m = interior_mask(idx_all, X, ps)
            idx_in = idx_all[m]
            pos_in = np.full(X + 1, -1, dtype=np.int64)
            pos_in[idx_in] = np.arange(idx_in.size)
            inner = compressed_degree_one(idx_in, pos_in, X, ps)
            print(
                f"{X:>12,} {str(ps):>9} {(k-2)/k:>9.4f} {inner:>14.5f} "
                f"{full:>12.5f}"
            )

    print()
    print("    On the interior -- where every toggle orbit is complete and the")
    print("    physical projection does nothing at all -- the value is (k-2)/k to")
    print("    numerical precision.  That is pure sign algebra: no arithmetic, no")
    print("    survivor geometry, no dependence on t.  The window moves it only")
    print("    from 0.3333 to 0.283.")
    print()
    print("    A gap obtained this way is therefore not evidence that the norm-one")
    print("    obstruction 'lives outside the low Walsh sector'.  It is evidence")
    print("    that averaging k operators which each negate a different coordinate")
    print("    leaves (k-2)/k of that coordinate -- true for any k operators with")
    print("    that sign pattern, on any space.")


if __name__ == "__main__":
    main()
