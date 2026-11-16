#!/usr/bin/env python3
"""Exact finite checks of the original native gcd/history/powerful source.

Default range: every integer R from 2 through 64, inclusive.  All arithmetic
is integer arithmetic and this module uses only the Python standard library.

FINITE-CHECK-ONLY STATUS
    A successful run verifies the specified finite identities on the stated
    roots.  It does not establish an all-scale theorem, asymptotic estimate,
    exponent improvement, independent specialist acceptance, or Lean proof.

Source definitions (the original ordered occurrence carrier is retained):
    N = R - 1, X = R*R - 1, M(t) = sum_{1 <= n <= t} mu(n).
    C(g) = sum_{1 <= a,b < R, gcd(a,b)=g} mu(a)mu(b) floor(X/(ab)).
    B_d = floor(N/d); H_d = {h <= B_d : every prime of h divides d}.
    A_h = floor(B_d/h); T = floor(X/(d*d*h*k)).
    U(d) = mu(d)^2 sum_{h,k in H_d}
           [M(A_h) + M(A_k) - 1_{T < R} M(T)].
    H(g) = sum_{k <= N/g} mu(k) U(g*k).
    E(g) = sum_{powerful q <= N} a(q) M(floor(X/q))
           1_{g | rad(q)} mu(rad(q)/g),
    where a(q) = product_{p^e || q}(e-1), and q=1 has a(1)=rad(1)=1.

C is reconstructed directly from all ordered pairs.  H is reconstructed
from smooth pairs, with smoothness tested by gcd stripping.  E is separately
reconstructed by trial factorization of powerful integers, including q=1.
No one of these three vectors is defined by subtracting the other two.
The run also regroups the powerful terms into their actual radical
coefficients A(d), verifies every admitted radical Gram entry directly,
and checks the complete Gram against E's squared norm.  The default range
includes the first diagonal-equality failure (R=5) and the first diagonal
upper-bound failure (R=10), with all earlier roots checked for minimality.

Inspected main: 076195b75278869d4f18fd924b9ebdaedf723108.
Paper definitions: agent-reports:research/agent_reports/2026-11-11/
30-finite-wheel.md, blob c9989449a814a1a7ee799791c73450872f4c7d3c,
GD1 and PD1-PD2.  Independent paper review: the same date's
50-adversarial-referee.md, blob c288a925fd064a551a0d2bd70b27d82acc9fe926,
NP/HR, at their stated scopes.  These are paper sources, not Lean declarations.

CLI:
    python native_identity_check.py
    python native_identity_check.py --min-r 2 --max-r 64 --json

Combined-checker API:
    summary = run_native_identity_checks(r_min=2, r_max=64)
The API returns a JSON-serializable dictionary, or raises AssertionError on
the first failed identity.  Importing this module runs no check and writes
no file.  reconstruct_native_source(R) exposes the exact vectors separately.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from itertools import accumulate
import json
from math import gcd, isqrt
from typing import Any, Sequence


STATUS = "PASS_FINITE_EXACT_ONLY"
SCOPE = (
    "Exact finite source identities only; no all-scale bound, exponent gain, "
    "independent review of this checker, or Lean certification."
)


@dataclass(frozen=True)
class PowerfulTerm:
    q: int
    radical: int
    multiplicity: int
    quotient: int


@dataclass(frozen=True)
class NativeSource:
    """Vectors use their gcd label as index; coordinate zero is unused."""

    r: int
    x: int
    c: tuple[int, ...]
    h: tuple[int, ...]
    e: tuple[int, ...]
    u: tuple[int, ...]
    powerful_terms: tuple[PowerfulTerm, ...]
    mertens_n: int
    mertens_x: int


def factorization(n: int) -> tuple[tuple[int, int], ...]:
    """Trial factorization; the unit has the empty factorization."""
    if n < 1:
        raise ValueError("factorization requires n >= 1")
    factors: list[tuple[int, int]] = []
    remainder = n
    p = 2
    while p * p <= remainder:
        exponent = 0
        while remainder % p == 0:
            remainder //= p
            exponent += 1
        if exponent:
            factors.append((p, exponent))
        p = 3 if p == 2 else p + 2
    if remainder > 1:
        factors.append((remainder, 1))
    return tuple(factors)


def mobius_and_mertens(limit: int) -> tuple[list[int], list[int]]:
    """Linear-sieve Mobius values and exact complete prefix sums through limit."""
    if limit < 1:
        raise ValueError("limit must be at least 1")
    mu = [0] * (limit + 1)
    mu[1] = 1
    composite = [False] * (limit + 1)
    primes: list[int] = []
    for n in range(2, limit + 1):
        if not composite[n]:
            primes.append(n)
            mu[n] = -1
        for p in primes:
            product = n * p
            if product > limit:
                break
            composite[product] = True
            if n % p == 0:
                mu[product] = 0
                break
            mu[product] = -mu[n]
    # mu[0] = 0 makes the prefix at index 0 exactly M(0) = 0.
    return mu, list(accumulate(mu))


def is_d_smooth(h: int, d: int) -> bool:
    """Test prime support by gcd stripping, independently of factorization."""
    remainder = h
    while remainder > 1:
        common = gcd(remainder, d)
        if common == 1:
            return False
        remainder //= common
    return True


def direct_gcd_rows(r: int, mu: Sequence[int]) -> tuple[int, ...]:
    """Reconstruct C from all ordered (a,b), never from H or E."""
    x = r * r - 1
    c = [0] * r
    for a in range(1, r):
        for b in range(1, r):
            c[gcd(a, b)] += mu[a] * mu[b] * (x // (a * b))
    return tuple(c)


def historical_rows(
    r: int, mu: Sequence[int], mertens: Sequence[int]
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Reconstruct H and U with the literal T < R historical mask."""
    n = r - 1
    x = r * r - 1
    u = [0] * r
    for d in range(1, r):
        if mu[d] == 0:
            continue  # The original coefficient mu(d)^2 is exactly zero.
        b_d = n // d
        smooth = [h for h in range(1, b_d + 1) if is_d_smooth(h, d)]
        subtotal = 0
        for h in smooth:
            for k in smooth:  # Both ordered orientations are retained.
                a_h = b_d // h
                a_k = b_d // k
                t = x // (d * d * h * k)
                historical_m = mertens[t] if t < r else 0
                subtotal += mertens[a_h] + mertens[a_k] - historical_m
        u[d] = mu[d] * mu[d] * subtotal
    h_rows = [0] * r
    for g in range(1, r):
        h_rows[g] = sum(mu[k] * u[g * k] for k in range(1, n // g + 1))
    return tuple(h_rows), tuple(u)


def powerful_rows(
    r: int, mu: Sequence[int], mertens: Sequence[int]
) -> tuple[tuple[int, ...], tuple[PowerfulTerm, ...]]:
    """Reconstruct the complete E from powerful q <= R-1, including q=1."""
    x = r * r - 1
    e = [0] * r
    terms: list[PowerfulTerm] = []
    for q in range(1, r):
        factors = factorization(q)
        if any(exponent < 2 for _, exponent in factors):
            continue
        radical = 1
        multiplicity = 1
        for p, exponent in factors:
            radical *= p
            multiplicity *= exponent - 1
        # For q=1 the empty products give radical=multiplicity=1.
        quotient = x // q
        terms.append(PowerfulTerm(q, radical, multiplicity, quotient))
        coefficient = multiplicity * mertens[quotient]
        for g in range(1, radical + 1):
            if radical % g == 0:
                e[g] += coefficient * mu[radical // g]
    return tuple(e), tuple(terms)


def reconstruct_native_source(
    r: int,
    *,
    mobius: Sequence[int] | None = None,
    mertens: Sequence[int] | None = None,
) -> NativeSource:
    """Construct C,H,E separately; optional tables permit reuse across roots."""
    if r < 2:
        raise ValueError("R must be at least 2")
    x = r * r - 1
    if (mobius is None) != (mertens is None):
        raise ValueError("provide both Mobius and Mertens tables, or neither")
    if mobius is None:
        mobius, mertens = mobius_and_mertens(x)
    if mertens is None or len(mobius) <= x or len(mertens) <= x:
        raise ValueError("tables must include every index through X = R^2-1")
    c = direct_gcd_rows(r, mobius)
    h, u = historical_rows(r, mobius, mertens)
    e, terms = powerful_rows(r, mobius, mertens)
    return NativeSource(r, x, c, h, e, u, terms, mertens[r - 1], mertens[x])


def _require_equal(actual: Any, expected: Any, *, label: str, r: int) -> None:
    # Explicit checks still execute under python -O, unlike assert statements.
    if actual != expected:
        raise AssertionError(
            f"R={r}: {label} failed: actual={actual!r}, expected={expected!r}"
        )


def run_native_identity_checks(r_min: int = 2, r_max: int = 64) -> dict[str, Any]:
    """Check every root in an inclusive range; return a finite-only audit summary."""
    if r_min < 2 or r_max < r_min:
        raise ValueError("require 2 <= r_min <= r_max")
    limit = r_max * r_max - 1
    mu, mertens = mobius_and_mertens(limit)

    # Independently validate the shared genuine arithmetic input.  The sieve
    # and trial-factorization algorithms do not share a primality table.
    for n in range(1, limit + 1):
        factors = factorization(n)
        expected_mu = 0 if any(e > 1 for _, e in factors) else (-1) ** len(factors)
        if mu[n] != expected_mu:
            raise AssertionError(f"Mobius input mismatch at n={n}")

    coordinate_checks = 0
    ordered_pairs = 0
    powerful_terms = 0
    unit_omission_witness: dict[str, int] | None = None
    radical_kernel_checks = 0
    radical_regrouping_checks = 0
    first_diagonal_equality_failure: dict[str, Any] | None = None
    first_diagonal_upper_bound_failure: dict[str, Any] | None = None
    known_diagonal_controls_checked = 0
    for r in range(r_min, r_max + 1):
        source = reconstruct_native_source(r, mobius=mu, mertens=mertens)
        for g in range(1, r):
            _require_equal(
                source.c[g], source.h[g] - source.e[g], label=f"C=H-E at g={g}", r=r
            )
            coordinate_checks += 1
        _require_equal(sum(source.h), 2 * source.mertens_n, label="sum H=2M(N)", r=r)
        _require_equal(sum(source.e), source.mertens_x, label="sum E=M(X)", r=r)
        _require_equal(
            sum(source.c), 2 * source.mertens_n - source.mertens_x,
            label="sum C=2M(N)-M(X)", r=r,
        )

        d_g = sum(value * value for value in source.c)
        historical_norm = sum(value * value for value in source.h)
        powerful_norm = sum(value * value for value in source.e)
        mixed = sum(h * e for h, e in zip(source.h, source.e))
        _require_equal(
            d_g, historical_norm + powerful_norm - 2 * mixed,
            label="complete squared-norm identity", r=r,
        )

        # Reconstruct the actual A(d) from powerful terms and Mertens values,
        # not from E's coordinates.  Include every possible radical, even
        # when its actual coefficient vanishes by cancellation.
        radicals = tuple(d for d in range(1, isqrt(r - 1) + 1) if mu[d] != 0)
        radical_coefficients = dict.fromkeys(radicals, 0)
        for term in source.powerful_terms:
            if term.radical not in radical_coefficients:
                raise AssertionError(f"R={r}: radical outside d^2 <= R-1")
            radical_coefficients[term.radical] += term.multiplicity * mertens[term.quotient]

        for g in range(1, r):
            regrouped = sum(
                radical_coefficients[d] * mu[d // g]
                for d in radicals if d % g == 0
            )
            _require_equal(regrouped, source.e[g], label=f"radical regrouping at g={g}", r=r)
            radical_regrouping_checks += 1

        kernels: dict[tuple[int, int], int] = {}
        for d in radicals:
            for e in radicals:
                direct_inner_product = sum(
                    mu[d // g] * mu[e // g]
                    for g in range(1, r) if d % g == 0 and e % g == 0
                )
                kernel = mu[d] * mu[e] * 2 ** len(factorization(gcd(d, e)))
                _require_equal(
                    direct_inner_product, kernel,
                    label=f"radical Gram kernel d={d}, e={e}", r=r,
                )
                kernels[d, e] = kernel
                radical_kernel_checks += 1

        gram = sum(
            radical_coefficients[d] * radical_coefficients[e] * kernels[d, e]
            for d in radicals for e in radicals
        )
        diagonal = sum(
            radical_coefficients[d] ** 2 * 2 ** len(factorization(d))
            for d in radicals
        )
        unit_nonunit_cross = 2 * source.mertens_x * sum(
            mu[d] * radical_coefficients[d] for d in radicals if d > 1
        )
        nonunit_cross = 2 * sum(
            radical_coefficients[d] * radical_coefficients[e] * kernels[d, e]
            for d in radicals for e in radicals if 1 < d < e
        )
        _require_equal(gram, powerful_norm, label="complete radical Gram energy", r=r)
        _require_equal(
            gram, diagonal + unit_nonunit_cross + nonunit_cross,
            label="radical Gram with both kinds of cross terms restored", r=r,
        )

        diagonal_control = {
            "R": r,
            "X": source.x,
            "A": {str(d): a for d, a in radical_coefficients.items()},
            "norm_E_squared": powerful_norm,
            "radical_diagonal": diagonal,
            "unit_nonunit_cross": unit_nonunit_cross,
            "nonunit_cross": nonunit_cross,
        }
        if first_diagonal_equality_failure is None and powerful_norm != diagonal:
            first_diagonal_equality_failure = diagonal_control
        if first_diagonal_upper_bound_failure is None and powerful_norm > diagonal:
            first_diagonal_upper_bound_failure = diagonal_control

        if r == 5:
            _require_equal(
                (radical_coefficients, powerful_norm, diagonal, unit_nonunit_cross, nonunit_cross),
                ({1: -2, 2: -1}, 2, 6, -4, 0),
                label="R=5 genuine diagonal-equality counterexample", r=r,
            )
            known_diagonal_controls_checked += 1
        if r == 10:
            _require_equal(
                (radical_coefficients, powerful_norm, diagonal, unit_nonunit_cross, nonunit_cross),
                ({1: 1, 2: -6, 3: -2}, 121, 81, 16, 24),
                label="R=10 genuine diagonal-upper-bound counterexample", r=r,
            )
            known_diagonal_controls_checked += 1

        _require_equal(
            source.powerful_terms[0], PowerfulTerm(1, 1, 1, source.x),
            label="q=1 unit term with coefficient one", r=r,
        )
        for term in source.powerful_terms:
            if not (1 <= term.q <= r - 1 and term.quotient > r):
                raise AssertionError(f"R={r}: original powerful mask failed for {term}")
        for g in range(1, r):
            if g * g > r - 1:
                _require_equal(source.e[g], 0, label=f"powerful support at g={g}", r=r)

        # A negative control: deleting q=1 must break reconstruction whenever
        # M(X) is nonzero.  This is a finite sensitivity check, not a theorem
        # that M(X) never vanishes.  The default range detects it already at R=2.
        e_without_unit = list(source.e)
        e_without_unit[1] -= source.mertens_x
        omitted_reconstruction = tuple(h - e for h, e in zip(source.h, e_without_unit))
        if source.mertens_x != 0:
            if omitted_reconstruction == source.c:
                raise AssertionError(f"R={r}: omission of nonzero unit term went undetected")
            if unit_omission_witness is None:
                unit_omission_witness = {
                    "R": r, "X": source.x, "M_X": source.mertens_x,
                    "g_1_error_after_omission": omitted_reconstruction[1] - source.c[1],
                }

        ordered_pairs += (r - 1) ** 2
        powerful_terms += len(source.powerful_terms)

    if r_min == 2 and r_max >= 5:
        _require_equal(
            None if first_diagonal_equality_failure is None else first_diagonal_equality_failure["R"],
            5, label="smallest diagonal-equality failure over all roots from 2", r=5,
        )
    if r_min == 2 and r_max >= 10:
        _require_equal(
            None if first_diagonal_upper_bound_failure is None else first_diagonal_upper_bound_failure["R"],
            10, label="smallest diagonal-upper-bound failure over all roots from 2", r=10,
        )

    roots = r_max - r_min + 1
    return {
        "status": STATUS,
        "scope": SCOPE,
        "range": {"R_min": r_min, "R_max": r_max, "inclusive": True},
        "roots_checked": roots,
        "mobius_values_independently_checked": limit,
        "gcd_coordinate_identities_checked": coordinate_checks,
        "ordered_pairs_evaluated": ordered_pairs,
        "scalar_sum_identities_checked": 3 * roots,
        "complete_norm_identities_checked": roots,
        "powerful_terms_evaluated": powerful_terms,
        "unit_term_and_source_mask_checks": roots,
        "unit_omission_witness": unit_omission_witness,
        "radical_regrouping_coordinate_checks": radical_regrouping_checks,
        "radical_gram_kernel_entries_checked": radical_kernel_checks,
        "complete_radical_gram_energy_checks": roots,
        "unit_and_nonunit_gram_expansion_checks": roots,
        "known_R5_R10_diagonal_controls_checked": known_diagonal_controls_checked,
        "first_diagonal_equality_failure_in_checked_range": first_diagonal_equality_failure,
        "first_diagonal_upper_bound_failure_in_checked_range": first_diagonal_upper_bound_failure,
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--min-r", type=int, default=2, help="first root, inclusive (default: 2)")
    parser.add_argument("--max-r", type=int, default=64, help="last root, inclusive (default: 64)")
    parser.add_argument("--json", action="store_true", help="print a JSON audit summary")
    args = parser.parse_args(argv)
    try:
        summary = run_native_identity_checks(args.min_r, args.max_r)
    except ValueError as exc:
        parser.error(str(exc))
    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print(
            f"PASS: exact native C/H/E identities for every integer "
            f"R={args.min_r}..{args.max_r} ({summary['roots_checked']} roots)."
        )
        print(
            f"Checked {summary['gcd_coordinate_identities_checked']:,} gcd coordinates, "
            f"{summary['ordered_pairs_evaluated']:,} ordered (a,b) pairs, "
            f"{summary['scalar_sum_identities_checked']} scalar sums, and "
            f"{summary['complete_norm_identities_checked']} complete norm identities."
        )
        print(
            f"Independently checked mu(1)..mu({summary['mobius_values_independently_checked']}); "
            f"retained {summary['powerful_terms_evaluated']} powerful terms, including q=1 at every root."
        )
        print(f"Unit-omission negative control: {summary['unit_omission_witness']}")
        print(
            f"Checked {summary['radical_gram_kernel_entries_checked']} exact radical Gram entries "
            f"and {summary['complete_radical_gram_energy_checks']} complete radical energies."
        )
        print(
            "First diagonal-equality failure in checked range: "
            f"{summary['first_diagonal_equality_failure_in_checked_range']}"
        )
        print(
            "First diagonal-upper-bound failure in checked range: "
            f"{summary['first_diagonal_upper_bound_failure_in_checked_range']}"
        )
        print(f"STATUS: {summary['status']}. {summary['scope']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
