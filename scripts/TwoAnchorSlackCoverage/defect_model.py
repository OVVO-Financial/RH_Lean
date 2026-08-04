#!/usr/bin/env python3
"""Local defect model for the stage energy recurrence `E_q <= A E_{q^-} + C x`.

The programme asks, for each tested prime `q`, for "the smallest `A` for which
`sup_N (E_q(N) - A E_{q^-}(N)) / x` is bounded".  On a finite prefix range both
directions of that question have a **one-pass closed form**, so no search is
needed:

    C_min(A) = max_N ( E_q(N) - A E_{q^-}(N) ) / x(N)          additive cost at A
    A_min(c) = max_N ( E_q(N) - c x(N) ) / E_{q^-}(N)          inflation at budget c

Both are exact, both are computed in one sweep, and they are inverse to each
other: `C_min(A_min(c)) <= c` and `A_min(C_min(A)) <= A`.  `A_min(0)` is the pure
multiplicative constant `max_N E_q(N)/E_{q^-}(N)` — the quantity reported as
`A_q^emp` — so the whole trade-off curve is available at the same cost as that
single number.

What this module does **not** contain is the energy itself.  `E_q(N)` is the
squared `l^2` mass of the resolved `{C,S,W}^j` components,

    E_j(N) = sum over sigma in {C,S,W}^j of |Z_sigma(N)|^2,

and the definition of `Z_sigma` — equivalently, the three operators `C_q`, `S_q`,
`W_q` as they act on a packet — is not recorded anywhere in this repository.  It
lives only in the originating computation.  Supply it through the callback
protocol in `stage_energies` and every diagnostic below runs unchanged.

Everything here is exact rational or float-free integer arithmetic where the
input allows it; the self-test at the bottom runs on synthetic data.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence


# ---------------------------------------------------------------------------
# input protocol
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class StageSeries:
    """Per-prefix data for one resolution stage.

    ``energy[i]`` is ``E_q(N_i)`` and ``location[i]`` is ``x = L + N_i``.  Both
    are indexed by the same prefix list.  ``mass[i]`` is the accumulated support
    mass ``m_2(N_i)``, used only by the maturity filter.
    """

    energy: Sequence[float]
    location: Sequence[float]
    mass: Sequence[float]

    def __post_init__(self) -> None:
        n = len(self.energy)
        if len(self.location) != n or len(self.mass) != n:
            raise ValueError("energy, location and mass must have equal length")


def stage_energies(
    prefixes: Sequence[int],
    resolve: Callable[[int, int], Sequence[float]],
    q: int,
) -> Sequence[float]:
    """Energy of the stage-`q` resolution at each prefix.

    ``resolve(q, N)`` must return the resolved components ``Z_sigma(N)`` for
    ``sigma in {C,S,W}^j``, i.e. `3^j` numbers whose signed sum is the fibre
    value `P_2(N)`.  This is the one piece the repository does not define.
    """
    return [sum(z * z for z in resolve(q, N)) for N in prefixes]


# ---------------------------------------------------------------------------
# the two exact one-pass formulas
# ---------------------------------------------------------------------------


def additive_cost(prev: StageSeries, cur: StageSeries, A: float) -> tuple[float, int]:
    """`C_min(A) = max_N (E_q(N) - A E_{q^-}(N))/x(N)`, with the maximizing index."""
    best, arg = None, -1
    for i, (ec, ep, x) in enumerate(zip(cur.energy, prev.energy, cur.location)):
        if x <= 0:
            continue
        v = (ec - A * ep) / x
        if best is None or v > best:
            best, arg = v, i
    if best is None:
        raise ValueError("no prefix with positive location")
    return best, arg


def inflation_at_budget(prev: StageSeries, cur: StageSeries, c: float) -> tuple[float, int]:
    """`A_min(c) = max_N (E_q(N) - c x(N))/E_{q^-}(N)`, with the maximizing index."""
    best, arg = None, -1
    for i, (ec, ep, x) in enumerate(zip(cur.energy, prev.energy, cur.location)):
        if ep <= 0:
            continue
        v = (ec - c * x) / ep
        if best is None or v > best:
            best, arg = v, i
    if best is None:
        raise ValueError("no prefix with positive previous-stage energy")
    return best, arg


def multiplicative_A(prev: StageSeries, cur: StageSeries) -> tuple[float, int]:
    """The pure multiplicative constant `max_N E_q(N)/E_{q^-}(N)` (`A_q^emp`)."""
    return inflation_at_budget(prev, cur, 0.0)


def tradeoff_curve(
    prev: StageSeries, cur: StageSeries, budgets: Sequence[float]
) -> list[tuple[float, float, int]]:
    """`(c, A_min(c), argmax)` for each additive budget `c`.

    A steep curve means the observed inflation is carried by a few prefixes and a
    small additive allowance buys a large reduction in `A`; a flat curve means the
    inflation is bulk behaviour.  That is exactly the boundary-versus-bulk question.
    """
    return [(c, *inflation_at_budget(prev, cur, c)) for c in budgets]


# ---------------------------------------------------------------------------
# regime separation
# ---------------------------------------------------------------------------


def restrict(series: StageSeries, keep: Sequence[bool]) -> StageSeries:
    return StageSeries(
        energy=[e for e, k in zip(series.energy, keep) if k],
        location=[x for x, k in zip(series.location, keep) if k],
        mass=[m for m, k in zip(series.mass, keep) if k],
    )


def mature_mask(series: StageSeries, min_mass: float) -> list[bool]:
    """Prefixes whose accumulated support mass has reached `min_mass`.

    The reported constants use `m_2 >= 1000`; without the restriction the short
    initial prefixes dominate and report a larger inflation.
    """
    return [m >= min_mass for m in series.mass]


def period_split(prefixes: Sequence[int], q: int) -> tuple[list[int], list[int]]:
    """Split each prefix `N` into complete `q^2` periods and a terminal remainder.

    Returns `(complete, terminal)` where `complete[i] * q*q + terminal[i] == N_i`.
    The complete part is the piece for which the exact fibre contraction laws
    apply; the terminal part is where an incomplete-period defect can appear, and
    is the candidate explanation for a large observed inflation.
    """
    period = q * q
    complete = [N // period for N in prefixes]
    terminal = [N % period for N in prefixes]
    return complete, terminal


def terminal_defect_share(
    prev: StageSeries,
    cur: StageSeries,
    prefixes: Sequence[int],
    q: int,
    A: float,
) -> dict[str, float]:
    """How much of the observed defect at inflation `A` sits at incomplete periods.

    Reports the maximal normalized defect over prefixes that end on a complete
    `q^2` period, and over those that do not.  If the second dominates, the
    inflation is a boundary artifact rather than bulk behaviour.
    """
    _, terminal = period_split(prefixes, q)
    on_period = [t == 0 for t in terminal]
    off_period = [not m for m in on_period]
    out: dict[str, float] = {}
    if any(on_period):
        c, _ = additive_cost(restrict(prev, on_period), restrict(cur, on_period), A)
        out["complete_period"] = c
    if any(off_period):
        c, _ = additive_cost(restrict(prev, off_period), restrict(cur, off_period), A)
        out["terminal_defect"] = c
    return out


# ---------------------------------------------------------------------------
# self-test on synthetic data
# ---------------------------------------------------------------------------


def _self_test() -> None:
    print("## defect-model harness self-test (synthetic data)")
    n = 500
    prefixes = list(range(1, n + 1))
    loc = [1000.0 + N for N in prefixes]
    mass = [0.75 * N for N in prefixes]

    # a bulk stage: E_q = 1.4 E_{q^-} everywhere
    prev = StageSeries([float(N) for N in prefixes], loc, mass)
    bulk = StageSeries([1.4 * N for N in prefixes], loc, mass)
    # a boundary stage: 1.1 everywhere except one short spike
    spike = [1.1 * N for N in prefixes]
    spike[3] = 4.0 * prefixes[3]
    boundary = StageSeries(spike, loc, mass)

    a_bulk, _ = multiplicative_A(prev, bulk)
    a_bnd, i_bnd = multiplicative_A(prev, boundary)
    print(f"   bulk stage      A_mult = {a_bulk:.6f}")
    print(f"   boundary stage  A_mult = {a_bnd:.6f} at prefix index {i_bnd}")
    assert abs(a_bulk - 1.4) < 1e-9
    assert abs(a_bnd - 4.0) < 1e-9

    # the trade-off curve separates them: a tiny additive budget collapses the
    # boundary constant but leaves the bulk constant almost unchanged
    for c in (0.0, 0.01, 0.1):
        ab, _ = inflation_at_budget(prev, bulk, c)
        an, _ = inflation_at_budget(prev, boundary, c)
        print(f"   budget c = {c:<5} A_min(bulk) = {ab:.6f}   A_min(boundary) = {an:.6f}")
    a0, _ = inflation_at_budget(prev, boundary, 0.0)
    a1, _ = inflation_at_budget(prev, boundary, 0.1)
    assert a1 < a0, "an additive budget must reduce the required inflation"

    # duality of the two formulas
    for c in (0.0, 0.05, 0.5):
        a, _ = inflation_at_budget(prev, boundary, c)
        cc, _ = additive_cost(prev, boundary, a)
        assert cc <= c + 1e-9, (c, a, cc)
    print("   C_min and A_min are inverse to each other:                       ok")

    # maturity filter
    keep = mature_mask(boundary, 100.0)
    a_mature, _ = multiplicative_A(restrict(prev, keep), restrict(boundary, keep))
    print(f"   boundary stage, mature prefixes only: A_mult = {a_mature:.6f}")
    assert abs(a_mature - 1.1) < 1e-9, "the maturity filter must drop the short spike"

    # period split
    complete, terminal = period_split(prefixes, 3)
    assert all(c * 9 + t == N for c, t, N in zip(complete, terminal, prefixes))
    print("   period split reconstructs every prefix:                          ok")
    print("\nAll self-tests passed.")
    print("\nTo run this on the real object, supply `resolve(q, N)` returning the")
    print("3^j components Z_sigma(N); see the module docstring.")


if __name__ == "__main__":
    _self_test()
