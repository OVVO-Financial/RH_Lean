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
    mu = mobius_sieve(x_r + 1)

    # Prefix accumulators. For consecutive (p, r) the equal-revealed-key fibres
    # are singletons, so the general per-key cumulative sums collapse to these.
    tot = {k: 0.0 for k in ("u", "abs", "sq", "quart")}
    cut = {k: 0.0 for k in ("u", "abs", "sq", "quart")}
    profile = [0.0] * (buckets + 1)
    sites = 0
    last_nonzero = 0

    for n, u in site_vector(R, p, r, x_r, mu, phi):
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


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--pairs", default="2,3", help="owner pairs, e.g. '2,3;3,5;5,7'")
    ap.add_argument(
        "--scales",
        default="200,400,800,1600,3200",
        help="geometric sequence of R",
    )
    ap.add_argument("--profile", action="store_true", help="print the u^2 mass profile")
    args = ap.parse_args()

    pairs = []
    for chunk in args.pairs.split(";"):
        a, b = chunk.split(",")
        pairs.append((int(a), int(b)))
    scales = [int(s) for s in args.scales.split(",")]

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
