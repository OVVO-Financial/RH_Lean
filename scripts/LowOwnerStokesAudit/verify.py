#!/usr/bin/env python3
"""Exact integer audit of the complete descending raw Stokes chronology.

This independently executes the finite carrier/coefficient definitions. It is
not a proof of LOW-A. Run from the repository root:
    python3 scripts/LowOwnerStokesAudit/verify.py 56 57 100 200 500
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction


def audit(root: int) -> dict:
    if root < 2:
        raise ValueError("root must be at least two")
    endpoint = root * root - 1
    mu = [1] * (endpoint + 1)
    mu[0] = 0
    largest = [0] * (endpoint + 1)
    largest[1] = 1
    primes = []
    for p in range(2, endpoint + 1):
        if largest[p] == 0:
            primes.append(p)
            for n in range(p, endpoint + 1, p):
                largest[n] = p
                mu[n] = -mu[n]
            for n in range(p * p, endpoint + 1, p * p):
                mu[n] = 0

    mertens = [0] * (endpoint + 1)
    prime_count = [0] * (endpoint + 1)
    for n in range(1, endpoint + 1):
        mertens[n] = mertens[n - 1] + mu[n]
        prime_count[n] = prime_count[n - 1] + (n >= 2 and largest[n] == n)

    partners = [0] * (endpoint + 1)
    for c in range(1, endpoint + 1):
        lower = max(largest[c], (root - 1) // c)
        partners[c] = max(0, prime_count[endpoint // c] - prime_count[lower])
    atoms = [mu[n] * partners[n] for n in range(endpoint + 1)]

    present = bytearray([1]) * (endpoint + 1)
    present[0] = 0
    coefficient = bytearray([1]) * (endpoint + 1)
    current = sum(atoms)
    correlation = mertens[root - 1] - mertens[endpoint]
    assert current == correlation
    charges = {}
    first_step = None

    for p in reversed(primes):
        parents = [
            c for c in range(1, endpoint // p + 1)
            if present[c] and present[c * p] and largest[c] < p
        ]
        boundary = sum(
            coefficient[c] * mu[c] * (partners[c] - partners[c * p])
            for c in parents
        )
        threshold = sum(
            coefficient[c] * mu[c]
            * max(0, prime_count[min(p, endpoint // c)]
                  - prime_count[max(largest[c], (root - 1) // c)])
            for c in parents
        )
        mismatch = sum(
            (coefficient[c * p] - coefficient[c]) * atoms[c * p]
            for c in parents
        )
        assert boundary == threshold
        assert mismatch == 0

        parent_mass = sum(coefficient[c] * atoms[c] for c in parents)
        child_mass = sum(coefficient[c * p] * atoms[c * p] for c in parents)
        # Directly evaluate the change from deleting children and multiplying
        # retained parents by 1-1/p in the reciprocal coefficient update.
        euler_next = Fraction(current - child_mass) - Fraction(parent_mass, p)
        raw_next = current - parent_mass - child_mass
        assert current - raw_next == boundary
        assert p * (current - euler_next) == boundary
        assert euler_next - raw_next == Fraction(p - 1, p) * boundary

        if first_step is None:
            first_step = {
                "prime": p, "parent_count": len(parents),
                "raw_before": current, "boundary": boundary,
                "raw_next": raw_next, "reciprocal_next": str(euler_next),
                "reciprocal_energy_change": str(euler_next**2 - current**2),
            }
        charges[p] = boundary
        for c in parents:
            coefficient[c] = 0
            present[c * p] = 0
        current = raw_next

    assert current == 0
    assert sum(coefficient[n] * atoms[n] for n in range(endpoint + 1) if present[n]) == 0
    assert sum(charges.values()) == correlation
    low = [p for p in primes if p != 2 and p * p < root]
    children = {q: mertens[endpoint // (q * q)] for q in low}
    diagonal = sum(b * b for b in charges.values())
    envelope = max(Fraction((mertens[y] - 1)**2, y + 1) for y in range(root))
    return {
        "R": root, "X": endpoint, "correlation": correlation,
        "lower_envelope": str(envelope), "low_q_children": children,
        "low_p_stokes_charges": {p: charges[p] for p in low},
        "low_q_energy": sum(m * m for m in children.values()),
        "full_stokes_diagonal": diagonal,
        "full_stokes_off_diagonal": correlation**2 - diagonal,
        "first_step": first_step,
    }


if __name__ == "__main__":
    roots = [int(x) for x in sys.argv[1:]] or [56, 57, 100, 200, 500]
    for root in roots:
        print(json.dumps(audit(root), sort_keys=True))
