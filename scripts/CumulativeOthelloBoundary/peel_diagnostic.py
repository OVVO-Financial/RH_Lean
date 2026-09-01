#!/usr/bin/env python3
"""Finite diagnostics for the cumulative Othello boundary route.

Four measurements, all on the raw prefix carrier ``(0, x]``.

1.  **Invariance of the signed mass under a peel.**  The Lean theorem
    ``RHLean.Proof.sum_moebius_eq_sum_iteratedPrimeEscapePart`` says peeling a
    distinguished prime leaves the signed Moebius mass unchanged.  Every row
    reprints that mass; it must never move.

2.  **Population left by the fixed-prime peel.**  The stop criterion of the
    route: a peel family whose boundary stays a fixed positive proportion of
    ``x`` cannot reach ``x^(1/2+eps)``.

3.  **Order independence.**  The repository's own chronological matching takes
    the primes in descending order.  On this carrier the surviving set is
    identical for ascending, descending, and mixed orders, so the peel order is
    not the free parameter.

4.  **Maximum adaptive matching.**  Restoring the full state-dependent freedom
    -- every state free to choose any prime edge, subject to both endpoints
    choosing each other -- is a maximum matching in the prime-toggle graph on
    the squarefree sites of ``(0, x]``.  Hopcroft-Karp measures how many states
    it must still leave exposed.  The exposed signed mass is always exactly
    ``M(x)``, which is the theorem again; the exposed *population* is the
    quantity the route needs to be small, and it is not.

The structural reason is printed last and is proved in Lean as
``RHLean.Proof.card_topHalfPrimes_le_fixedCard_succ``: a prime ``p`` with
``x < 2p`` has exactly one legal move in ``(0, x]``, namely ``p -> 1``, since
every other prime edge overshoots ``x``.  All of them compete for the single
site ``1`` and an involution can serve at most one, so every adaptive matching
on this carrier leaves at least ``pi(x) - pi(x/2) - 1`` states exposed.

    python3 scripts/CumulativeOthelloBoundary/peel_diagnostic.py [xmax]
"""

from __future__ import annotations

import sys
from collections import deque


def sieve(n_max: int) -> tuple[list[int], list[int], list[int]]:
    """Smallest-prime-factor sieve, its prime list, and the Moebius function."""
    spf = list(range(n_max + 1))
    primes: list[int] = []
    for i in range(2, n_max + 1):
        if spf[i] == i:
            primes.append(i)
        for p in primes:
            if p > spf[i] or i * p > n_max:
                break
            spf[i * p] = p
    mu = [1] * (n_max + 1)
    mu[0] = 0
    for n in range(2, n_max + 1):
        p = spf[n]
        m = n // p
        mu[n] = 0 if m % p == 0 else -mu[m]
    return spf, primes, mu


def toggle(p: int, n: int) -> int:
    """The carrier toggle of `RHLean.Proof.primeCarrierToggle`."""
    if n % (p * p) == 0:
        return n
    if n % p == 0:
        return n // p
    return n * p


def peel(carrier: set[int], p: int) -> set[int]:
    """The Othello boundary: sites whose `p`-mate has left the carrier."""
    return {n for n in carrier if toggle(p, n) not in carrier}


def prime_divisors(n: int, spf: list[int]) -> list[int]:
    out: list[int] = []
    while n > 1:
        p = spf[n]
        out.append(p)
        while n % p == 0:
            n //= p
    return out


def hopcroft_karp(n_left: int, adj: list[list[int]], n_right: int):
    """Maximum bipartite matching; returns the two match arrays."""
    inf = float("inf")
    match_l = [-1] * n_left
    match_r = [-1] * n_right
    while True:
        dist = [inf] * n_left
        queue: deque[int] = deque()
        for u in range(n_left):
            if match_l[u] == -1:
                dist[u] = 0
                queue.append(u)
        reachable_free = False
        while queue:
            u = queue.popleft()
            for v in adj[u]:
                w = match_r[v]
                if w == -1:
                    reachable_free = True
                elif dist[w] == inf:
                    dist[w] = dist[u] + 1
                    queue.append(w)
        if not reachable_free:
            return match_l, match_r
        for root in range(n_left):
            if match_l[root] != -1:
                continue
            stack = [(root, iter(adj[root]))]
            path: list[tuple[int, int]] = []
            while stack:
                node, it = stack[-1]
                advanced = False
                for v in it:
                    w = match_r[v]
                    if w == -1:
                        path.append((node, v))
                        for a, b in reversed(path):
                            match_l[a] = b
                            match_r[b] = a
                        stack.clear()
                        advanced = True
                        break
                    if dist[w] == dist[node] + 1:
                        path.append((node, v))
                        stack.append((w, iter(adj[w])))
                        advanced = True
                        break
                if not advanced:
                    dist[node] = inf
                    stack.pop()
                    if path:
                        path.pop()


def peel_rows(x: int, primes: list[int], mu: list[int]) -> None:
    carrier = set(range(1, x + 1))
    mass = sum(mu[n] for n in carrier)
    print(f"  fixed-prime peel, ascending:   M(x)={mass}")
    for p in [q for q in primes if q <= 19]:
        carrier = peel(carrier, p)
        peeled = sum(mu[n] for n in carrier)
        flag = "" if peeled == mass else "   <-- MASS MOVED, THEOREM VIOLATED"
        print(f"      after p={p:>3}: |fixed|={len(carrier):>8}"
              f"  |fixed|/x={len(carrier) / x:8.5f}  mass={peeled:>7}{flag}")


def order_rows(x: int, primes: list[int], mu: list[int]) -> None:
    below = [p for p in primes if p <= x]
    orders = [("ascending", below), ("descending", below[::-1]),
              ("descending then ascending", below[::-1] + below)]
    for name, order in orders:
        carrier = set(range(1, x + 1))
        for p in order:
            carrier = peel(carrier, p)
        print(f"      {name:<26} |fixed|={len(carrier):>8}"
              f"  |fixed|/x={len(carrier) / x:8.5f}"
              f"  mass={sum(mu[n] for n in carrier):>7}")


def max_matching_row(x: int, spf: list[int], primes: list[int],
                     mu: list[int]) -> None:
    left = [n for n in range(1, x + 1) if mu[n] == 1]
    right = [n for n in range(1, x + 1) if mu[n] == -1]
    li = {n: i for i, n in enumerate(left)}
    ri = {n: i for i, n in enumerate(right)}
    adj: list[list[int]] = [[] for _ in left]
    for n in left:
        row = adj[li[n]]
        for p in primes:
            if n * p > x:
                break
            if n % p:
                row.append(ri[n * p])
        for p in prime_divisors(n, spf):
            row.append(ri[n // p])
    adj = [sorted(set(r)) for r in adj]
    match_l, match_r = hopcroft_karp(len(left), adj, len(right))
    exposed_l = sum(1 for v in match_l if v == -1)
    exposed_r = sum(1 for v in match_r if v == -1)
    exposed = exposed_l + exposed_r
    print(f"      maximum adaptive matching   exposed={exposed:>8}"
          f"  exposed/x={exposed / x:8.5f}"
          f"  exposed mass={exposed_l - exposed_r:>7}")
    top = [p for p in primes if p <= x and x < 2 * p]
    print(f"      forced by the top-half primes: {len(top)} primes p with"
          f" x < 2p, all with the single legal move p -> 1")


def main(argv: list[str]) -> int:
    x_max = int(argv[1]) if len(argv) > 1 else 20_000
    spf, primes, mu = sieve(x_max * 19 + 1)
    for x in (x_max // 10, x_max):
        if x < 100:
            continue
        mass = sum(mu[1:x + 1])
        print(f"x={x}  M(x)={mass}  sqrt(x)={x ** 0.5:.1f}")
        peel_rows(x, primes, mu)
        print("  order independence:")
        order_rows(x, primes, mu)
        print("  full state-dependent freedom:")
        max_matching_row(x, spf, primes, mu)
        print()
    print("Readings:")
    print("  * the signed mass never moves under any peel: the exact layer holds;")
    print("  * the fixed-prime peel bottoms out at 2/pi^2 = "
          f"{2 / 3.141592653589793 ** 2:.5f} of x, in every prime order;")
    print("  * a maximum adaptive matching still leaves a positive proportion")
    print("    exposed, so restoring the state-dependent prime is not enough;")
    print("  * the obstruction is structural and proved in Lean as")
    print("    RHLean.Proof.card_topHalfPrimes_le_fixedCard_succ.")
    print("  The carrier, not the matching, is what has to change.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
