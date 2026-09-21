#!/usr/bin/env python3
"""What `LowOwnerStokesPrimePeriodFrameDomination` actually demands of M(x).

The returned-core architecture terminates at one open proposition
(research/GLOBAL_RETURNED_CORE_STOKES_PHYSICAL_FRAME_BRIDGE.lean):

    LowOwnerStokesPrimePeriodFrameDomination C :=
      forall R hR, lowOwnerCanonicalSignedStokesFinalBoundary R
                     <= C * lowOwnerStokesOddPrimePeriodFrameMajorant R hR

Its own file says that once this domination is supplied, no further Stokes,
frame or envelope plumbing stands between the architecture and RH. This script
measures what it is asking for, using only compiled identities plus arithmetic.

THE CHAIN
---------
    FinalStokes_R = ||G_R||^2 - D_R
        research/GLOBAL_RETURNED_CORE_STOKES_ALL_ENDPOINT_MERTENS_LEDGER.lean:70

    G_R = M(R-1) - M(X_R) - sum_{q in lowOwners} M(X_R/q^2)/q
        same file:50, with X_R = squareRootEndpoint R = R^2 - 1

    D_R = sum_{n <= X_R} W(R,n)^2 * mu(n)^2,  W = daughterWeight + [n >= R]
        research/GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM.lean:24

    R^2/18 <= Majorant_R <= (5/4) R^2
        research/GLOBAL_RETURNED_CORE_STOKES_PHYSICAL_FRAME_BRIDGE.lean:98,147

The majorant is pinned to Theta(R^2) on BOTH sides by compiled theorems, so the
domination is equivalent to a bound of the form

    ||G_R||^2 <= ((5/4) C + D_R/R^2) * R^2.

MEASURED
--------
Two facts this script establishes, both reproducible by running it:

1. D_R / R^2 converges to about 0.684 (0.6791 at R=400 rising to 0.6837 at
   R=6400, differences halving). It is Theta(R^2), NOT Theta(R^2 (lnln R)^2) --
   the (lnln R)^2-normalised ratio falls as R grows. So the right-hand side
   above is a constant multiple of R^2, with no log room.

2. G_R does not cancel M(X_R); it reproduces it. Measured |G_R|/|M(X_R)| is
   0.52, 1.08, 1.23, 1.08, 0.98, 0.83 at R = 200..6400 -- mean 0.95, and above
   1 in half the samples. The reciprocal column is an O(sqrt(X)/4) correction
   (|col| <= 156 against |M| up to 1079), far too small to absorb an excursion:
   |M(X/q^2)| ~ sqrt(X)/q makes the column at most sqrt(X) * sum_q 1/q^2 < 0.2
   sqrt(X).

CONSEQUENCE
-----------
Since R = sqrt(X_R + 1), the two facts turn the domination into

    |M(x)|  <=  c * sqrt(x),      c = sqrt((5/4) C + 0.684)  fixed.

That is the shape of the MERTENS CONJECTURE, not of RH.

  * RH gives M(x) << x^(1/2+eps), which permits sqrt(x)*exp((log x)^0.9) --
    astronomically larger. Even under RH the best known bound is
    sqrt(x)*exp(C log x / log log x); a pointwise sqrt(x)*(log x)^A bound is
    open and strictly beyond RH.
  * c = 1 is disproved outright: Odlyzko and te Riele (1985) give
    limsup M(x)/sqrt(x) > 1.06 and liminf < -1.009.
  * Every fixed c is believed false: Ingham (1942) shows that under linear
    independence of the zeta zero ordinates, limsup M(x)/sqrt(x) = +infinity.

So the proposition is strictly stronger than the theorem it is meant to
deliver, and is believed false. This is the mirror image of the hazard
`AGENTS.md` lists -- not an RH-strength estimate under a weaker name, but a
stronger-than-RH estimate standing in as the final bridge.

WHAT THIS IS NOT
----------------
Not a Lean proof, and not a disproof of the proposition: Ingham's conclusion is
conditional on linear independence, and Odlyzko-te Riele only rules out c = 1.
It is an argument that the target is misplaced, resting on one measured input
(G_R tracks M(X_R)) and three compiled identities. The load-bearing step is the
absence of cancellation in G_R; if a later reformulation makes G_R genuinely
smaller than M(X_R), the argument lapses and should be rerun.
"""

from __future__ import annotations

import argparse
import bisect
import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from returned_core_site_probe import mobius_sieve, primes_up_to  # noqa: E402


def low_owners(R: int) -> list[int]:
    """canonicalRoughLowQ2Owners R: odd primes q <= R-1 with q*q < R."""

    return [q for q in primes_up_to(R - 1) if q != 2 and q * q < R]


def measure(R: int, want_diagonal: bool = True) -> dict:
    X = R * R - 1
    mu = mobius_sieve(X)

    mertens = [0] * (X + 1)
    running = 0
    for n in range(1, X + 1):
        running += mu[n]
        mertens[n] = running

    owners = low_owners(R)
    column = sum(mertens[X // (q * q)] / q for q in owners)
    gap = mertens[R - 1] - mertens[X] - column

    diagonal = float("nan")
    if want_diagonal:
        cuts = sorted((X // (q * q), 1.0 / q) for q in owners)
        keys = [c for c, _ in cuts]
        suffix = [0.0] * (len(cuts) + 1)
        for i in range(len(cuts) - 1, -1, -1):
            suffix[i] = suffix[i + 1] + cuts[i][1]
        diagonal = 0.0
        for n in range(1, X + 1):
            if mu[n] == 0:
                continue
            w = suffix[bisect.bisect_left(keys, n)] + (1.0 if n >= R else 0.0)
            diagonal += w * w

    root = math.sqrt(X)
    return {
        "R": R,
        "X": X,
        "mertens": mertens[X],
        "column": column,
        "gap": gap,
        "diagonal": diagonal,
        "gap_over_root": abs(gap) / root,
        "mertens_over_root": abs(mertens[X]) / root,
        "gap_over_mertens": abs(gap) / abs(mertens[X]) if mertens[X] else float("nan"),
        "diagonal_over_rsq": diagonal / (R * R),
        # FinalStokes = |G|^2 - D, against the proved majorant ceiling.
        "final_stokes": gap * gap - diagonal,
        "implied_C": (gap * gap - diagonal) / (1.25 * R * R),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--scales", default="200,400,800,1600,3200,6400")
    ap.add_argument("--no-diagonal", action="store_true", help="skip D_R (much faster)")
    args = ap.parse_args()

    print("STOKES FRAME DOMINATION: WHAT IT DEMANDS OF M(x)")
    print("=" * 84)
    print("G_R = M(R-1) - M(X_R) - sum_q M(X_R/q^2)/q ;  FinalStokes = |G_R|^2 - D_R")
    print("Majorant is Theta(R^2), proved both sides: R^2/18 <= Maj <= (5/4)R^2.")
    print()
    print(
        f"{'R':>6} {'X_R':>13} {'M(X_R)':>9} {'col':>9} {'G_R':>11} "
        f"{'|G|/sqrtX':>10} {'|G|/|M|':>8} {'D/R^2':>8} {'needs C >=':>11}"
    )
    for R in [int(s) for s in args.scales.split(",")]:
        m = measure(R, want_diagonal=not args.no_diagonal)
        print(
            f"{R:>6} {m['X']:>13,} {m['mertens']:>9,} {m['column']:>9.2f} "
            f"{m['gap']:>11.2f} {m['gap_over_root']:>10.4f} "
            f"{m['gap_over_mertens']:>8.3f} {m['diagonal_over_rsq']:>8.4f} "
            f"{m['implied_C']:>11.4f}"
        )
    print()
    print("Reading it: |G|/|M| near 1 means the endpoint ledger reproduces the")
    print("Mertens excursion rather than cancelling it, and D/R^2 settling on a")
    print("constant means there is no log room on the right-hand side. Together")
    print("those turn the domination into |M(x)| <= c*sqrt(x) for fixed c -- the")
    print("Mertens conjecture shape, strictly stronger than RH and believed false.")
    print("See the module docstring for the citations and the caveats.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
