#!/usr/bin/env python3
"""Exhaustively inspect the low-prime displacement forest.

The scan mirrors the arithmetic child carrier used by the Lean development.
For each (R,K,U) it

* builds the complete owned signed response-child set;
* performs the increasing fresh-prime matching and records the unique selected
  mate and removal prime of every deleted child;
* classifies each terminal child by born/high channel and by whether its
  canonical owner-parent was absent initially or displaced earlier;
* follows the alternating path formed by the selected matching and the
  canonical owner toggle;
* verifies that a path ends either at another terminal child of opposite
  Moebius sign or outside the original carrier;
* classifies every outside endpoint by the exact owner/root/endpoint support
  dichotomies formalized in Lean.

No probabilistic model or prime-number estimate is used.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


def sieve(n: int) -> Tuple[List[int], List[int], List[int]]:
    """Return primes, Moebius values, and largest-prime factors through n."""
    mu = [1] * (n + 1)
    lpf = [1] * (n + 1)
    is_prime = bytearray(b"\x01") * (n + 1)
    if n >= 0:
        is_prime[0] = 0
    if n >= 1:
        is_prime[1] = 0
    primes: List[int] = []
    mu[0] = 0
    for p in range(2, n + 1):
        if is_prime[p]:
            primes.append(p)
            for m in range(p, n + 1, p):
                lpf[m] = p
                mu[m] *= -1
                if m > p:
                    is_prime[m] = 0
            pp = p * p
            if pp <= n:
                for m in range(pp, n + 1, pp):
                    mu[m] = 0
    return primes, mu, lpf


@dataclass(frozen=True)
class Atom:
    cofactor: int
    partner: int
    channel: str

    @property
    def child(self) -> int:
        return self.cofactor * self.partner


@dataclass
class ScanResult:
    R: int
    K: int
    U: int
    endpoint: int
    child_count: int
    terminal_count: int
    terminal_signed_mass: int
    born_terminal: int
    high_terminal: int
    born_no_toggle: int
    high_no_toggle: int
    born_unstable: int
    high_unstable: int
    alternating_boundary_paths: int
    alternating_terminal_pairs: int
    max_alternating_matching_edges: int
    owner_boundary_endpoints: int
    root_crossing_endpoints: int
    endpoint_crossing_endpoints: int
    roughness_endpoints: int
    unclassified_endpoints: int


def build_atoms(R: int, K: int, U: int) -> Tuple[Dict[int, Atom], List[int], List[int], List[int]]:
    X = R * R - 1
    primes, mu, lpf = sieve(X)
    prime_set = set(primes)
    atoms: Dict[int, Atom] = {}

    for c in range(1, X + 1):
        if mu[c] == 0 or not (K < lpf[c] <= U):
            continue

        for q in primes:
            if q > R:
                break
            if lpf[c] < q <= c and c * q <= X:
                atom = Atom(c, q, "born")
                prior = atoms.setdefault(atom.child, atom)
                if prior != atom:
                    raise AssertionError(("child collision", prior, atom))

        max_q = X // c
        for q in primes:
            if q <= R:
                continue
            if q > max_q:
                break
            atom = Atom(c, q, "high")
            prior = atoms.setdefault(atom.child, atom)
            if prior != atom:
                raise AssertionError(("child collision", prior, atom))

    for n, atom in atoms.items():
        assert n == atom.child
        assert atom.partner in prime_set
        assert lpf[n] == atom.partner
        assert n // lpf[n] == atom.cofactor

    return atoms, primes, mu, lpf


def sequential_match(
    children: Set[int], fresh_primes: Sequence[int]
) -> Tuple[Set[int], Dict[int, int], Dict[int, int], Dict[int, Set[int]]]:
    current = set(children)
    mate: Dict[int, int] = {}
    removed_at: Dict[int, int] = {}
    before: Dict[int, Set[int]] = {}

    for p in fresh_primes:
        before[p] = set(current)
        lower = {n for n in current if n % p != 0 and p * n in current}
        upper = {p * n for n in lower}
        assert lower.isdisjoint(upper)
        for n in lower:
            m = p * n
            assert n not in mate and m not in mate
            mate[n] = m
            mate[m] = n
            removed_at[n] = p
            removed_at[m] = p
        current.difference_update(lower)
        current.difference_update(upper)

    assert set(mate) == children - current
    for n, m in mate.items():
        assert mate[m] == n
        assert removed_at[m] == removed_at[n]
    return current, mate, removed_at, before


def toggle(n: int, p: int) -> int:
    return n // p if n % p == 0 else p * n


def alternating_endpoint(
    start: int,
    pivot: int,
    children: Set[int],
    terminal: Set[int],
    mate: Dict[int, int],
) -> Tuple[str, int, int, List[int]]:
    """Follow P, M, P, M, ... from an M-unmatched terminal child."""
    assert start in terminal
    z = start
    path = [start]
    matching_edges = 0
    seen = {start}

    while True:
        w = toggle(z, pivot)
        path.append(w)
        if w not in children:
            return "boundary", w, matching_edges, path
        if w in terminal:
            return "terminal", w, matching_edges, path
        if w not in mate:
            raise AssertionError(("nonterminal without mate", start, pivot, w))
        z = mate[w]
        path.append(z)
        matching_edges += 1
        if z in seen:
            return "cycle", z, matching_edges, path
        seen.add(z)


def classify_boundary(
    missing: int,
    partner: int,
    channel: str,
    R: int,
    K: int,
    U: int,
    endpoint: int,
    mu: Sequence[int],
    lpf: Sequence[int],
) -> str:
    if missing <= 0 or missing % partner != 0:
        return "unclassified"
    d = missing // partner
    if d <= 0:
        return "unclassified"
    if d >= len(mu) or mu[d] == 0:
        return "nonsquarefree"
    if not (K < lpf[d] <= U):
        return "owner"
    if d * partner > endpoint:
        return "endpoint"
    if channel == "high":
        return "unclassified"
    if lpf[d] >= partner:
        return "roughness"
    if d < partner:
        return "root"
    return "unclassified"


def scan(R: int, K: int, U: Optional[int] = None) -> ScanResult:
    if R < 3:
        raise ValueError("R must be at least 3")
    if U is None:
        U = R - math.isqrt(R)
    if not (1 <= K <= U < R):
        raise ValueError((R, K, U))

    atoms, primes, mu, lpf = build_atoms(R, K, U)
    children = set(atoms)
    fresh = [p for p in primes if K < p <= U]
    terminal, mate, removed_at, before = sequential_match(children, fresh)

    born_terminal = high_terminal = 0
    born_no = high_no = born_unstable = high_unstable = 0
    boundary_paths = terminal_pairs = 0
    max_edges = 0
    boundary_counts = {
        "owner": 0,
        "root": 0,
        "endpoint": 0,
        "roughness": 0,
        "unclassified": 0,
    }

    for n in sorted(terminal):
        atom = atoms[n]
        if atom.channel == "born":
            born_terminal += 1
        else:
            high_terminal += 1

        p = lpf[atom.cofactor]
        assert K < p <= U and atom.cofactor % p == 0
        parent = n // p
        if parent not in children:
            if atom.channel == "born":
                born_no += 1
            else:
                high_no += 1
        else:
            assert parent in removed_at
            assert removed_at[parent] < p, (R, K, U, n, p, removed_at[parent])
            if atom.channel == "born":
                born_unstable += 1
            else:
                high_unstable += 1

        kind, endpoint_value, edge_count, path = alternating_endpoint(
            n, p, children, terminal, mate
        )
        max_edges = max(max_edges, edge_count)
        if kind == "cycle":
            raise AssertionError(("alternating cycle", R, K, U, n, p, path))
        if kind == "terminal":
            terminal_pairs += 1
            other = endpoint_value
            assert other != n
            assert mu[other] == -mu[n], (n, other, path)
        else:
            boundary_paths += 1
            bkind = classify_boundary(
                endpoint_value,
                atom.partner,
                atom.channel,
                R,
                K,
                U,
                R * R - 1,
                mu,
                lpf,
            )
            if bkind == "nonsquarefree":
                raise AssertionError(("fresh path lost squarefreeness", n, p, path))
            boundary_counts[bkind] = boundary_counts.get(bkind, 0) + 1

    signed_mass = sum(mu[n] for n in terminal)
    return ScanResult(
        R=R,
        K=K,
        U=U,
        endpoint=R * R - 1,
        child_count=len(children),
        terminal_count=len(terminal),
        terminal_signed_mass=signed_mass,
        born_terminal=born_terminal,
        high_terminal=high_terminal,
        born_no_toggle=born_no,
        high_no_toggle=high_no,
        born_unstable=born_unstable,
        high_unstable=high_unstable,
        alternating_boundary_paths=boundary_paths,
        alternating_terminal_pairs=terminal_pairs,
        max_alternating_matching_edges=max_edges,
        owner_boundary_endpoints=boundary_counts["owner"],
        root_crossing_endpoints=boundary_counts["root"],
        endpoint_crossing_endpoints=boundary_counts["endpoint"],
        roughness_endpoints=boundary_counts["roughness"],
        unclassified_endpoints=boundary_counts["unclassified"],
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--r-min", type=int, default=16)
    parser.add_argument("--r-max", type=int, default=80)
    parser.add_argument("--k", type=int, default=5)
    parser.add_argument("--output", type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    results = [scan(R, args.k) for R in range(args.r_min, args.r_max + 1)]
    payload = {
        "parameters": {
            "r_min": args.r_min,
            "r_max": args.r_max,
            "k": args.k,
            "terminal_cutoff": "R-floor(sqrt(R))",
        },
        "results": [asdict(result) for result in results],
        "maxima": {
            field: max(getattr(result, field) for result in results)
            for field in ScanResult.__dataclass_fields__
            if field not in {"R", "K", "U", "endpoint"}
        },
    }
    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text + "\n")
    else:
        print(text)


if __name__ == "__main__":
    main()
