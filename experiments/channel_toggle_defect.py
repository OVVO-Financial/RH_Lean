"""Channel-space toggle defect: testing the one variant the l^2 no-go leaves open.

`experiments/compression_escape_defect.py` kills the compression-escape proposal
on the full window state, for two reasons:

  * sigma_max(P U P) = 1 identically (intact toggle orbits), so no uniform
    coercivity exists;
  * converting an l^2 mass contraction into an amplitude bound costs
    Cauchy-Schwarz against a space of dimension ~X, losing a full power of X.

Both objections weaken on a *low-dimensional channel space*: there the
Cauchy-Schwarz tax is the channel count `s`, not `X`.  This is the setting of
`RHLean/Proof/SurvivorResidueCovarianceCriterion.lean` (which pays only s = 2).

`RHLean/Proof/SurvivorResiduePrimeToggle.lean` proves the transport law on
height residues,

    u  |->  ell^2 * u + (1 - ell^2) * q^2   (mod s),

so when `ell^2 = 1 mod s` the toggle preserves each fibre while flipping the
sign: it acts as `-I`, commutes with every projection, and has compression
defect identically zero.  The remaining hope is `ell^2 != 1 mod s`, where the
transport genuinely moves fibres.

This script tests that hope and refutes it.  In Mertens coordinates the
statistic is `r(n) = n mod s`, transported by `n -> ell*n` as `u -> ell*u`; the
fibre-preserving case is `ell = 1 mod s`.

  S1  The transport is an isometry.  For gcd(ell, s) = 1 the map `u -> ell*u` is
      a permutation of Z/s, so it preserves the channel norm exactly.  An
      isometry has zero compression defect, whether or not it moves fibres.
      Verified exactly.

  S2  Consequently the measured "retained / input" ratio is nothing but the
      ratio of channel energies at two different scales.  It fluctuates over
      more than an order of magnitude and exceeds 1 regularly, so no contraction
      inequality holds in either direction.

  S3  The one case where the norm does drop, gcd(ell, s) > 1, is a channel
      *merge*, not a defect: it is the coarser partition mod s/gcd, reachable
      without any toggle.

Usage:  python3 experiments/channel_toggle_defect.py [N]
"""

import math
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


def channel_vector(mu32, X, s, ell, transported=False):
    """Channel amplitudes  sum_{n <= X, ell !| n} mu(n)  bucketed mod s.

    transported=False buckets by  n mod s   (the input state);
    transported=True  buckets by  ell*n mod s (the toggled state).
    """
    n = np.arange(0, X + 1, dtype=np.int64)
    w = mu32[: X + 1].astype(np.int64).copy()
    w[ell::ell] = 0  # the toggle acts only on n with ell !| n
    key = (n * ell) % s if transported else n % s
    return np.bincount(key, weights=w, minlength=s)


def square_prefix_endpoint(t):
    return (t + 1) * (t + 1) - 1


def hr(title):
    print()
    print("=" * 88)
    print(title)
    print("=" * 88)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000
    print(f"sieving mu(n) for n <= {N:,} ...", flush=True)
    mu32 = build_mu(N).astype(np.int32)
    M = np.concatenate(([0], np.cumsum(mu32)))

    cases = [
        (s, ell)
        for s in (2, 3, 5, 8, 12)
        for ell in (2, 3, 5, 7, 11, 13)
        if ell % s != 0
    ]

    # ------------------------------------------------------------------ S1
    hr("S1  the fibre transport is an isometry of channel space")
    print("    if u -> ell*u is a permutation of Z/s (gcd(ell,s) = 1) then bucketing")
    print("    by ell*n mod s is a relabelling of bucketing by n mod s, so the two")
    print("    channel vectors have identical norm -- zero compression defect, and")
    print("    the fibre-moving / fibre-preserving distinction is invisible to it")
    print()
    X = square_prefix_endpoint(2000)
    print(
        f"{'s':>4} {'ell':>4} {'gcd':>4} {'fibre':>7} {'||transported||^2':>19} "
        f"{'||untransported||^2':>21} {'isometry':>9}"
    )
    for s, ell in cases:
        Y = X // ell
        b = channel_vector(mu32, Y, s, ell, transported=True)
        a = channel_vector(mu32, Y, s, ell, transported=False)
        nb, na = float(b @ b), float(a @ a)
        g = math.gcd(ell, s)
        fibre = "fixed" if ell % s == 1 % s else "moving"
        print(
            f"{s:>4} {ell:>4} {g:>4} {fibre:>7} {nb:>19,.0f} {na:>21,.0f} "
            f"{str(abs(nb - na) < 1e-6):>9}"
        )
    print()
    print("    isometry holds in every gcd = 1 row, for moving and fixed fibres")
    print("    alike.  The transport therefore contributes no energy defect at all.")

    # ------------------------------------------------------------------ S2
    hr("S2  what the retained/input ratio actually measures")
    print("    rho = ||retained||^2 / ||input||^2 is therefore just the ratio of")
    print("    channel energies at scales X/ell and X.  It carries no information")
    print("    about the toggle, the projection, or their commutator.")
    print()
    print("    rho*ell normalizes out the trivial 1/ell change of scale; a genuine")
    print("    defect would sit well below 1.  Values above 1 mean the 'retained'")
    print("    energy exceeds the input -- impossible for a true compression.")
    print()
    for t in (2000, 3000):
        X = square_prefix_endpoint(t)
        if X > N:
            continue
        MX = int(M[X + 1])
        print(f"  X = {X:,}   M(X) = {MX}")
        print(
            f"    {'s':>3} {'ell':>4} {'fibre':>7} {'||a||^2':>13} {'||b||^2':>13} "
            f"{'rho':>8} {'rho*ell':>9} {'rho>1':>6}"
        )
        over = 0
        total = 0
        for s, ell in cases:
            if math.gcd(ell, s) != 1:
                continue
            a = channel_vector(mu32, X, s, ell, transported=False)
            b = channel_vector(mu32, X // ell, s, ell, transported=True)
            na, nb = float(a @ a), float(b @ b)
            if na == 0:
                continue
            rho = nb / na
            total += 1
            over += rho > 1
            print(
                f"    {s:>3} {ell:>4} "
                f"{('fixed' if ell % s == 1 % s else 'moving'):>7} "
                f"{na:>13,.0f} {nb:>13,.0f} {rho:>8.4f} {rho*ell:>9.4f} "
                f"{str(rho > 1):>6}"
            )
        print(f"    -> rho > 1 in {over} of {total} cases")
        print()

    # ------------------------------------------------------------------ S3
    hr("S3  the only norm drop is a channel merge, not a defect")
    print("    when gcd(ell, s) = g > 1 the map u -> ell*u is not a permutation: it")
    print("    collapses Z/s onto a subgroup of index g.  The norm drops, but that")
    print("    is exactly the coarser partition mod s/g, available directly with no")
    print("    toggle at all -- and it reduces sum_u a_u^2 while preserving sum_u a_u,")
    print("    so it is a change of bookkeeping, not new cancellation.")
    print()
    X = square_prefix_endpoint(2000)
    print(
        f"{'s':>4} {'ell':>4} {'gcd':>4} {'||transported||^2':>19} "
        f"{'||coarser s/g||^2':>19} {'same':>6}"
    )
    for s, ell in cases:
        g = math.gcd(ell, s)
        if g == 1:
            continue
        Y = X // ell
        b = channel_vector(mu32, Y, s, ell, transported=True)
        coarse = channel_vector(mu32, Y, s // g, ell, transported=False)
        nb, nc = float(b @ b), float(coarse @ coarse)
        print(
            f"{s:>4} {ell:>4} {g:>4} {nb:>19,.0f} {nc:>19,.0f} "
            f"{str(abs(nb - nc) < 1e-6):>6}"
        )

    hr("verdict")
    print("    The channel-space variant is dead for a reason independent of the")
    print("    l^2 no-go: the fibre transport is an isometry, so P U P has no")
    print("    compression defect on channel space regardless of whether")
    print("    ell^2 = 1 mod s.  There is no surviving version of the")
    print("    escape-energy mechanism inside the single-variable toggle family.")


if __name__ == "__main__":
    main()
