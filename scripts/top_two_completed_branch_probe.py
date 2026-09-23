#!/usr/bin/env python3
"""Exact finite audit of the post-795 branch / top-two composition.

Three independent finite constructions are compared: completed branch fibre
squares, the literal two-toggle Stokes decrements, and the common-clock Gram.
Integer numerators over the reciprocal-owner common denominator are used.
These checks are diagnostics, not a uniform contraction proof.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction
from math import prod

from returned_core_site_probe import mobius_sieve, primes_up_to


def measure(root: int) -> dict[str, Fraction | int]:
    endpoint = root * root - 1
    primes = primes_up_to(endpoint)
    top, second = primes[-1], primes[-2]
    owners = [p for p in primes if p != 2 and p * p < root]
    denom = prod(owners)
    mu = mobius_sieve(endpoint)
    sites = [n for n in range(1, endpoint + 1) if mu[n]]
    weight = [0] * (endpoint + 1)
    for n in range(1, endpoint + 1):
        weight[n] = (denom if n >= root else 0) + sum(
            denom // p for p in owners if n <= endpoint // (p * p)
        )

    def physical(n: int) -> int:
        return weight[n] if n <= endpoint else 0

    def unextended(n: int) -> int:
        return weight[n] if n <= endpoint else denom

    def toggle(p: int, n: int) -> int:
        return n // p if n % p == 0 else n * p

    # For squarefree n this is an exact encoding of its lower prime signature.
    lower_signature = [1] * (endpoint + 1)
    threshold_energy = endpoint_completion = same_branch = incidence_energy = 0
    first_step = second_step = terminal = signed_cells = top_cell = 0
    for p in primes:
        cells: dict[int, list[int]] = defaultdict(list)
        for n in sites:
            if n % p:
                cells[lower_signature[n]].append(n)
        for carrier in cells.values():
            base = sum(mu[n] * physical(n) for n in carrier)
            returned = sum(mu[n] * physical(p * n) for n in carrier)
            cell = -2 * base * returned
            signed_cells += cell
            if p == top:
                top_cell += cell
                terminal += cell
                continue

            branch = [n for n in carrier if n % top]
            b = sum(mu[n] * (physical(n) - physical(top * n)) for n in branch)
            j = sum(mu[n] * (physical(p * n) - physical(p * top * n)) for n in branch)
            h = sum(mu[n] * (
                unextended(n) - unextended(p * n) -
                unextended(top * n) + unextended(p * top * n)
            ) for n in branch)
            inc_sq, same = (b - j) ** 2, b * b + j * j
            assert inc_sq - same == cell, (root, p, "branch/cell")
            incidence_energy += inc_sq
            threshold_energy += h * h
            endpoint_completion += inc_sq - h * h
            same_branch += same

            # Literal top-toggle interior. Its mixed scalar is the product of
            # the two separately assembled toggle-difference amplitudes.
            support = set(carrier)
            interior = [n for n in carrier if toggle(top, n) in support]

            def db(n: int) -> int:
                return physical(n) - physical(toggle(top, n))

            def dj(n: int) -> int:
                return physical(p * n) - physical(p * toggle(top, n))

            ib = sum(mu[n] * db(n) for n in interior)
            ij = sum(mu[n] * dj(n) for n in interior)
            assert (-2 * ib * ij) % 4 == 0
            after_top = (-2 * ib * ij) // 4
            first_step += cell - after_top
            if p == second:
                terminal += after_top
            else:
                interior_set = set(interior)
                twice = [n for n in interior if toggle(second, n) in interior_set]
                assert not twice, (root, p, "nonempty two-toggle interior")
                second_step += after_top

        for n in range(p, endpoint + 1, p):
            lower_signature[n] *= p

    mertens = [0] * (endpoint + 1)
    for n in range(1, endpoint + 1):
        mertens[n] = mertens[n - 1] + mu[n]
    column_num = sum((denom // p) * mertens[endpoint // (p * p)] for p in owners)
    gap_num = denom * (mertens[endpoint] - mertens[root - 1])
    amplitude = sum(mu[n] * weight[n] for n in sites)
    diagonal = sum(weight[n] ** 2 for n in sites)
    final = amplitude * amplitude - diagonal
    remainder = gap_num * gap_num + 2 * column_num * gap_num - diagonal
    clip = first_step + second_step
    assert amplitude == column_num + gap_num
    assert incidence_energy == threshold_energy + endpoint_completion
    assert incidence_energy - same_branch + top_cell == final
    assert clip + terminal == signed_cells == final
    assert final == column_num * column_num + remainder
    assert terminal <= 4 * denom * denom
    # Here the terminal can also be evaluated without cell or pair enumeration.
    assert terminal == 2 * denom * denom - 4 * weight[1] * denom
    energy = sum(mertens[endpoint // (p * p)] ** 2 for p in owners)
    values = {
        "threshold_energy": threshold_energy,
        "endpoint_completion": endpoint_completion,
        "incidence_energy": incidence_energy,
        "same_branch": same_branch,
        "top_cell": top_cell,
        "first_toggle": first_step,
        "second_toggle": second_step,
        "terminal": terminal,
        "clip": clip,
        "final": final,
        "column_square": column_num * column_num,
        "signed_remainder": remainder,
    }
    result: dict[str, Fraction | int] = {"R": root, "X": endpoint, "q2_energy": energy}
    result.update({k: Fraction(v, denom * denom) for k, v in values.items()})
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--roots", default="56,64,99")
    args = parser.parse_args()
    for root in map(int, args.roots.split(",")):
        if root < 56:
            parser.error("the top-two consumer requires R >= 56")
        data = measure(root)
        print(" ".join(f"{key}={value}" for key, value in data.items()), flush=True)
    print("All exact branch, two-toggle, endpoint, and Gram identities agree.")


if __name__ == "__main__":
    main()
