#!/usr/bin/env python3
"""Finite diagnostic for the returned-core completion gate.

The `research/GLOBAL_RETURNED_CORE_*` chain proves a `2/9` contraction on a
positive square mass extracted from *completed* incidence four-corners. Whether
that contraction acts on an order-one share of its own natural square currency,
or on an asymptotically negligible sliver of it, is a finite question. This
script answers it.

Every quantity below is transcribed from a compiled definition, not from prose
about one. `AGENTS.md` rule 5 is the reason: a numerical harness built from a
description of the carrier tests a lookalike, and a lookalike that agrees to
three digits is worse than no experiment at all. The chain, with its source:

    primesUpTo X                    = {p prime : p <= X}
                                      RHLean/Arithmetic/PrimesUpToFrontier.lean:11
    squareRootEndpoint R            = R^2 - 1
                                      RHLean/Analysis/TwoABPrimeDilation.lean:106
    rawQ2ChildCutoff R q            = squareRootEndpoint R / (q*q)     [Nat div]
                                      RHLean/Proof/SignedTransportAmplificationAudit.lean:301
    canonicalRoughHighQ2Owners R    = ((primesUpTo (R-1)).erase 2).filter (R <= q*q)
    canonicalRoughLowQ2Owners R     = ((primesUpTo (R-1)).erase 2) \\ high
                                      research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean:34
    lowOwnerReciprocalDaughterWeight R n
                                    = sum over q in lowOwners of (1/q if n <= cutoff R q else 0)
                                      research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean:32
    lowOwnerThresholdPotential R n  = daughterWeight R n - (1 if n < R else 0)
                                      research/GLOBAL_RETURNED_CORE_THRESHOLD_INCIDENCE_KERNEL.lean:52
    lowOwnerThresholdOwnerIncidenceWeight R p n
                                    = potential R n - potential R (p*n)
                                      research/GLOBAL_RETURNED_CORE_THRESHOLD_RECIPROCAL_INTERTWINING.lean:68
    lowOwnerThresholdSecondOwnerDifference R p r n
                                    = incidenceWeight R p n - incidenceWeight R p (r*n)
                                      research/GLOBAL_RETURNED_CORE_THRESHOLD_RECIPROCAL_INTERTWINING.lean:95
    lowOwnerRawParentThresholdSignedSite R p r n
                                    = realMoebiusStep n * secondOwnerDifference R p r n
                                      research/GLOBAL_RETURNED_CORE_RAW_PARENT_PREFIX_STAR_ENERGY.lean:86

The four-corner factorizes,

    weightedMoebiusFreshPrimeFourCornerMass w r a b = u(a) * u(b),

    research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean:50  (expand and collect: the
    four terms are (A+A')(B+B') with A = w a * mu*(a), A' = w(ra) * mu*(ra))

so both the signed ledger and its square are quadratic forms in the single site
vector `u`, and no pair enumeration is needed. That factorization is also
recorded in the file's own docstring: "Fresh-prime Moebius sign reversal turns
the full Gram square into a product of one-dimensional owner differences."

The completion filter separates. `LowOwnerCompletedPolarizationBlock`
(research/GLOBAL_RETURNED_CORE_COMPLETED_POLARIZATION_AGGREGATE.lean:42) is

    r.Prime AND not r | a AND not r | b
      AND a <= X AND p*a <= X AND r*a <= X AND p*(r*a) <= X
      AND b <= X AND p*b <= X AND r*b <= X AND p*(r*b) <= X

whose every conjunct after `r.Prime` touches `a` alone or `b` alone. Since
`p*r*n <= X` implies the other three, it is `r.Prime AND Q(a) AND Q(b)` with

    Q(n)  <=>  r does not divide n  AND  n <= X/(p*r).

So completion is a range shrink by `p*r` in each coordinate, and nothing else.

WHAT THE SITE VECTOR LOOKS LIKE
------------------------------
Two exact facts about `u` shape every number this script prints, and both are
worth knowing before reading a ratio.

`Phi_R` reaches `n` only from owners with `X/q^2 >= n`, so its support ends at
`X/q_min^2 = X/9` (`q_min = 3`, the smallest odd owner clearing `q^2 < R`).
Above that every one of the four potentials in `u` vanishes, so `u` does too.
The completion cutoff `X/(p*r)` therefore does not bind at all when `p*r <= 9`,
which only `(p, r) = (2, 3)` satisfies: there every share is 1 by support rather
than by survival, and the diagnostic is measuring nothing.

Above `n = X/25` only `q = 3` still reaches, so `Phi(n) = 1/3`, while `p*n`,
`r*n` and `p*r*n` are all past the support and contribute zero. Hence

    u(n) = mu(n) / 3     exactly,  for n > X/25

-- measured as a single distinct value `|u| = 1/3` across all 237,766 sites
above 0.45 of the support at R = 3200. `X/25` is the fraction `9/25 = 0.36` of
the support, and the constant 25 is `q_2^2` for the *second* smallest owner, so
it comes from the gap between the two smallest entries of
`canonicalRoughLowQ2Owners`, not from the owner pair.

The mass below that fraction drains as `R` grows (the lowest tenth of the
support carries 0.561 of the `u^4` mass at R=800 and 0.039 at R=25600). It is
tempting to conclude the region above is uniform and read off a limiting share
of `max(0, (9/(p*r) - 9/25) / (1 - 9/25))`. That is wrong, and measurably so:
the `u^4` profile has a spike at the `q = 5` dropout, 0.2522 in the bucket
holding `9/25` against 0.1151 uniform, so the mass above the threshold is not
flat. Measured against that formula at R = 25600:

    (2,5) 0.818 vs 0.844   (2,7) 0.375 vs 0.442   (3,5) 0.540 vs 0.375
    (3,7) 0.379 vs 0.107   (5,7) 0.264 vs 0.000   (7,11) 0.032 vs 0.000

Every pair converges to a positive constant and none vanishes, so no `p*r`
threshold separates them. Per-fibre power-law fits measure the transient
drainage below `X/25`, not an asymptotic exponent, which is why they come out
non-monotone in `p*r`. Do not read a decay into a single fibre.

The decay is global, not per-fibre. See `--global-share`.

WHAT THIS DOES NOT DO
---------------------
It reports shares of a local `(p, sig, r)` ledger. It says nothing about the
global aggregation over `r`, which has no canonical theorem yet: `r` is a
chronological owner coordinate and summing it blindly risks counting
overlapping stages of the filtration. A share near one here does not prove the
route closes; it only removes one way for the route to be dead.
"""

from __future__ import annotations

import argparse
import bisect
from dataclasses import dataclass


def mobius_sieve(limit: int) -> list[int]:
    """mu(n) for n <= limit, by smallest-prime-factor factorisation."""

    spf = list(range(limit + 1))
    i = 2
    while i * i <= limit:
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    mu = [0] * (limit + 1)
    if limit >= 0:
        mu[0] = 0
    if limit >= 1:
        mu[1] = 1
    for n in range(2, limit + 1):
        p = spf[n]
        m = n // p
        if m % p == 0:
            mu[n] = 0          # p^2 | n
        else:
            mu[n] = -mu[m]
    return mu


def primes_up_to(limit: int) -> list[int]:
    if limit < 2:
        return []
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    i = 2
    while i * i <= limit:
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
        i += 1
    return [i for i in range(2, limit + 1) if sieve[i]]


@dataclass
class Potential:
    """`lowOwnerThresholdPotential R` as a callable, O(log) per evaluation.

    The daughter weight is a sum of `1/q` over low owners whose cutoff reaches
    `n`. Sorting the cutoffs turns that into one suffix sum plus a bisect,
    rather than a loop over owners at every site.
    """

    R: int
    X: int
    cutoffs: list[int]
    suffix: list[float]
    low_owners: list[int]

    @classmethod
    def build(cls, R: int) -> "Potential":
        X = R * R - 1
        # canonicalRoughLowQ2Owners R: odd primes q <= R-1 with q*q < R.
        low = [q for q in primes_up_to(R - 1) if q != 2 and q * q < R]
        pairs = sorted((X // (q * q), 1.0 / q) for q in low)
        cutoffs = [c for c, _ in pairs]
        # suffix[i] = sum of 1/q over owners with cutoff >= cutoffs[i]
        suffix = [0.0] * (len(pairs) + 1)
        for i in range(len(pairs) - 1, -1, -1):
            suffix[i] = suffix[i + 1] + pairs[i][1]
        return cls(R=R, X=X, cutoffs=cutoffs, suffix=suffix, low_owners=low)

    def __call__(self, n: int) -> float:
        i = bisect.bisect_left(self.cutoffs, n)
        value = self.suffix[i]
        if n < self.R:
            value -= 1.0
        return value

    @property
    def support_bound(self) -> int:
        """Largest `n` at which the daughter-weight part can be nonzero."""

        return self.cutoffs[-1] if self.cutoffs else 0


def site_vector(R: int, p: int, r: int, upto: int, mu: list[int], phi: Potential):
    """`lowOwnerRawParentThresholdSignedSite R p r n` for n <= upto.

    Yields `(n, u)` only on the branch site carrier: squarefree, `p` does not
    divide `n`, `r` does not divide `n`. Squarefreeness is `mu(n) != 0`; the
    two non-divisibilities are the `PFree_p` and `not r | n` conditions the
    completed block and the telescope both impose.
    """

    for n in range(1, upto + 1):
        m = mu[n]
        if m == 0 or n % p == 0 or n % r == 0:
            continue
        second = (phi(n) - phi(p * n)) - (phi(r * n) - phi(p * r * n))
        if second:
            yield n, m * second


def probe(R: int, p: int, r: int, buckets: int = 20) -> dict:
    X = R * R - 1
    x_r = X // r
    x_pr = X // (p * r)
    phi = Potential.build(R)
    # `u` vanishes above the daughter-weight support: there the weight part of
    # every one of the four potentials is zero, and the `-[n < R]` part is zero
    # too because the support bound X/q_min^2 exceeds R for R > q_min^2. So the
    # scan and the sieve both stop at the support, not at x_r -- for r < 9 that
    # is the difference between sieving X/r and X/9.
    scan = min(x_r, phi.support_bound)
    mu = mobius_sieve(scan + 1)

    # Prefix accumulators. For consecutive (p, r) the equal-revealed-key fibres
    # are singletons, so the general per-key cumulative sums collapse to these.
    tot = {k: 0.0 for k in ("u", "abs", "sq", "quart")}
    cut = {k: 0.0 for k in ("u", "abs", "sq", "quart")}
    profile = [0.0] * (buckets + 1)
    sites = 0
    last_nonzero = 0

    for n, u in site_vector(R, p, r, scan, mu, phi):
        sites += 1
        last_nonzero = n
        a, s = abs(u), u * u
        tot["u"] += u
        tot["abs"] += a
        tot["sq"] += s
        tot["quart"] += s * s
        if n <= x_pr:
            cut["u"] += u
            cut["abs"] += a
            cut["sq"] += s
            cut["quart"] += s * s
        profile[min(buckets, (n * buckets) // X)] += s

    def ratio(num: float, den: float) -> float:
        return num / den if den else float("nan")

    return {
        "R": R,
        "p": p,
        "r": r,
        "X": X,
        "x_r": x_r,
        "x_pr": x_pr,
        "low_owners": len(phi.low_owners),
        "phi_support_bound": phi.support_bound,
        "sites": sites,
        "last_nonzero_site": last_nonzero,
        "rho_signed": ratio(cut["sq"], tot["sq"]),
        "rho_abs": ratio(cut["abs"] ** 2, tot["abs"] ** 2),
        "rho_2_9": ratio(cut["quart"], tot["quart"]),
        "sq_mass": tot["sq"],
        "quart_mass": tot["quart"],
        "signed_sum": tot["u"],
        "profile": profile,
    }


def global_share(R: int, p: int) -> dict:
    """Completed share summed over the whole canonical greatest-owner schedule.

    This is the quantity the architecture actually licenses. Per-fibre shares
    cannot simply be added up unless the fibres partition the carrier, and they
    do: `lowOwnerFirstOwnerAdmittedPair_existsUnique_greatestOwner`
    (research/GLOBAL_RETURNED_CORE_UNIQUE_GREATEST_OWNER_ASSEMBLY.lean:111)
    gives every admitted off-diagonal pair exactly one greatest owner
    `r in primesUpTo (squareRootEndpoint R)` with `p < r`, and
    `lowOwnerFirstOwnerAdmittedGreatestOwnerPairUnion_eq_offDiagonal`
    (research/GLOBAL_RETURNED_CORE_UNIQUE_OWNER_PAIR_FUBINI.lean:61) identifies
    the union of those fibres with the whole off-diagonal carrier. Duplicate-free
    and exhaustive, so the sum is the honest global object.

    The first owner `p` likewise runs over every prime:
    `lowOwnerZeroFrequencyMobiusGram_eq_sum_firstOwnerGram`
    (research/GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM.lean:137) partitions the
    Gram over `primesUpTo (squareRootEndpoint R)` with no `erase 2`. So `p = 2`
    is an ordinary member, and `(2, 3)` is one fibre of thousands rather than a
    sector with special standing.
    """

    X = R * R - 1
    phi = Potential.build(R)
    supp = phi.support_bound
    mu = mobius_sieve(supp + 1)
    num = den = 0.0
    fibres = live = 0
    for r in primes_up_to(supp):
        if r <= p:
            continue
        fibres += 1
        x_pr = X // (p * r)
        fib_num = fib_den = 0.0
        for n, u in site_vector(R, p, r, supp, mu, phi):
            q = (u * u) ** 2
            fib_den += q
            if n <= x_pr:
                fib_num += q
        num += fib_num
        den += fib_den
        if fib_num > 0:
            live += 1
    return {
        "R": R,
        "p": p,
        "fibres": fibres,
        "fibres_with_completed_mass": live,
        "global_rho_2_9": num / den if den else float("nan"),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--pairs", default="2,3", help="owner pairs, e.g. '2,3;3,5;5,7'")
    ap.add_argument(
        "--scales",
        default="200,400,800,1600,3200",
        help="geometric sequence of R",
    )
    ap.add_argument("--profile", action="store_true", help="print the u^2 mass profile")
    ap.add_argument(
        "--global-share",
        action="store_true",
        help="sum over the whole greatest-owner schedule instead of one fibre",
    )
    ap.add_argument("--first-owners", default="2,3", help="values of p for --global-share")
    args = ap.parse_args()

    pairs = []
    for chunk in args.pairs.split(";"):
        a, b = chunk.split(",")
        pairs.append((int(a), int(b)))
    scales = [int(s) for s in args.scales.split(",")]

    if args.global_share:
        print("RETURNED-CORE COMPLETION GATE -- GLOBAL SCHEDULE SHARE")
        print("=" * 78)
        print("Summed over every greatest-owner fibre, which the unique-owner")
        print("Fubini licenses. A single fibre is not representative: the schedule")
        print("has pi(X/9) entries and the completed cutoff X/(p*r) shrinks like")
        print("1/r, so the handful of small-r fibres that keep an order-one share")
        print("are a vanishing fraction of it.")
        print()
        print(f"{'R':>7} {'p':>3} {'fibres':>8} {'nonempty':>9} {'global rho_2/9':>16}")
        for R in scales:
            for p in [int(x) for x in args.first_owners.split(",")]:
                g = global_share(R, p)
                print(
                    f"{R:>7} {p:>3} {g['fibres']:>8,} "
                    f"{g['fibres_with_completed_mass']:>9,} "
                    f"{g['global_rho_2_9']:>16.6f}"
                )
        return 0

    print("RETURNED-CORE COMPLETION GATE PROBE")
    print("=" * 78)
    print("Shares of one local (p, sig, r) ledger. Carriers transcribed from the")
    print("compiled definitions cited in the module docstring, not from prose.")
    print()

    for p, r in pairs:
        print(f"owner pair (p, r) = ({p}, {r})")
        print("-" * 78)
        print(
            f"{'R':>7} {'X':>12} {'sites':>9} {'supp/X':>8} "
            f"{'x_pr/X':>7} {'rho_signed':>11} {'rho_abs':>9} {'rho_2/9':>9}"
        )
        for R in scales:
            out = probe(R, p, r)
            supp = out["last_nonzero_site"] / out["X"] if out["X"] else 0.0
            print(
                f"{R:>7} {out['X']:>12,} {out['sites']:>9,} {supp:>8.4f} "
                f"{out['x_pr'] / out['X']:>7.4f} "
                f"{out['rho_signed']:>11.6f} {out['rho_abs']:>9.6f} "
                f"{out['rho_2_9']:>9.6f}"
            )
            if args.profile:
                total = sum(out["profile"]) or 1.0
                print("         u^2 mass by n/X:", end="")
                for i, v in enumerate(out["profile"][:-1]):
                    if v:
                        print(f" [{i / 20:.2f}]{v / total:.3f}", end="")
                print()
        print()

    print("Reading the numbers")
    print("-" * 78)
    print("  supp/X is where the site vector actually stops being nonzero. If it")
    print("  falls below x_pr/X the completion cutoff never binds, and the shares")
    print("  are 1 by support, not by cancellation -- a real result, but one that")
    print("  says the diagnostic is not measuring what it was designed to measure.")
    print("  rho_2/9 is the route-selection statistic: near zero kills the gate")
    print("  route, order one leaves it open.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
