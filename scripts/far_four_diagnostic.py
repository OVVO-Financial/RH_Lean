#!/usr/bin/env python3
"""Exact finite FAR-4 diagnostic; no asymptotic or Gram bound is inferred.

Faces are stored by their squarefree product. This is a bijective encoding of
the actual Boolean face, not an identification of different physical periods.
The carrier predicates and signs follow LowWheelCanonicalPairingFrontier,
LowWheelCanonicalDowncrossParentFibers, LowWheelFrozenFirstFailureBridge,
StableFarWallLowCofactorQ2Descent, and TerminalMertensReduction.
"""

import argparse
from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction
from functools import cache
import json
from pathlib import Path


def sieve(limit):
    mu = [1] * (limit + 1)
    smallest = [0] * (limit + 1)
    largest = [1] * (limit + 1)
    primes = []
    mu[0] = 0
    smallest[1] = 1
    for p in range(2, limit + 1):
        if smallest[p]:
            continue
        primes.append(p)
        for n in range(p, limit + 1, p):
            if not smallest[n]:
                smallest[n] = p
            largest[n] = p
            mu[n] = -mu[n]
        for n in range(p * p, limit + 1, p * p):
            mu[n] = 0
    mertens = [0] * (limit + 1)
    for n in range(1, limit + 1):
        mertens[n] = mertens[n - 1] + mu[n]
    return mu, smallest, largest, primes, mertens


def diagnose(root, data, output_dir=None):
    mu, smallest, largest, primes, mertens = data
    endpoint = root * root - 1
    primes_here = primes[:bisect_right(primes, endpoint)]

    def weight(state):
        face, cofactor, _quotient = state
        return mu[face] * mu[cofactor]

    def mass(states):
        return sum(weight(state) for state in states)

    physical = set()
    downcross = set()
    parent = {}
    for face in range(1, endpoint + 1):
        if not mu[face] or largest[face] > root:
            continue
        for cofactor in range(1, min(root, endpoint // face + 1)):
            if not mu[cofactor]:
                continue
            for quotient in range(root // face + 1,
                                  endpoint // (cofactor * face) + 1):
                state = (face, cofactor, quotient)
                physical.add(state)
                pivot = smallest[cofactor * quotient]
                ancestor = face * (quotient // pivot)
                if cofactor % pivot and ancestor <= root:
                    downcross.add(state)
                    parent[state] = ancestor
    multiplicities = Counter(parent.values())
    unique = {s for s in downcross if multiplicities[parent[s]] == 1}
    frozen = {s for s in downcross if s[2] == smallest[s[1] * s[2]]
              and largest[s[0]] < s[2]}
    repeated_frozen = frozen - unique
    internal = {s for s in repeated_frozen if s[1] == 1 and s[2] <= root}
    frozen_cofactor = {s for s in repeated_frozen if s[1] > 1}
    top = {(f, c // largest[c], largest[c] * k) for f, c, k in frozen_cofactor}
    mates = {(f * p, 1, 1) for f, _c, p in internal}
    near_mates = {s for s in mates if s[0] * s[2] < root + 8}
    far_mates = mates - near_mates
    far_physical = {s for s in physical if s[0] * s[2] >= root + 8}
    assert len(top) == len(frozen_cofactor)
    assert len(mates) == len(internal)
    assert mass(top) == -mass(frozen_cofactor)
    assert mass(mates) == -mass(internal)
    assert not top & far_mates
    assert top | far_mates <= far_physical
    residual = far_physical - (top | far_mates)
    far_primes = primes_here[bisect_left(primes_here, root + 8):]
    far_transport = sum(mertens[endpoint // p] for p in far_primes)
    assert mass(far_physical) == far_transport
    frozen_top_far = mass(residual) - mass(near_mates)
    assert frozen_top_far == mass(internal) - mass(top) + far_transport

    near_transport = sum(mertens[endpoint // p] for p in primes_here
                         if root < p <= root + 7)
    external_unique = {s for s in unique if s[1] == 1
                       and s[2] > root and smallest[s[2]] == s[2]}
    root_boundary = (mertens[root] - mass(unique) - near_transport
                     + mass(external_unique))
    assert root_boundary - frozen_top_far == mertens[endpoint]

    @cache
    def partners(cofactor):
        # Exact membership theorem for squareRootCanonicalRoughPrimePartnerSet.
        if cofactor > endpoint:
            return frozenset()
        lower = max(largest[cofactor], (root - 1) // cofactor)
        return frozenset(primes_here[bisect_right(primes_here, lower):
                                     bisect_right(primes_here, endpoint // cofactor)])

    # The full partner incidence is counted once per parent here.
    rough = sum(mu[c] * len(partners(c)) for c in range(1, endpoint + 1))
    assert rough == mertens[root - 1] - mertens[endpoint]
    rough_root = mu[root] - mass(unique) - near_transport + mass(external_unique)
    assert frozen_top_far == rough + rough_root

    stable_pairs = {(c, p) for c in range(1, root) if mu[c]
                    for p in far_primes if c * p <= endpoint}
    triples = {(largest[c], c // largest[c], p) for c, p in stable_pairs if c > 1}
    assert len(triples) == sum(c > 1 for c, _p in stable_pairs)
    descended = {t for t in triples if t[0] ** 2 * t[1] * t[2] <= endpoint}
    crossings = triples - descended
    descended_mass = sum(mu[d] for _q, d, _p in descended)
    crossing_mass = sum(mu[d] for _q, d, _p in crossings)
    unit_mass = sum(c == 1 for c, _p in stable_pairs)
    assert far_transport == sum(mu[c] for c, _p in stable_pairs)
    assert far_transport == unit_mass - descended_mass - crossing_mass
    assert frozen_top_far == (unit_mass - descended_mass - crossing_mass
                              - mass(mates) - mass(top))

    incidence = []
    for q, d, p in sorted(triples):
        c = q * d
        assert mu[c] == -mu[d]
        old, child = partners(c), partners(c * p)
        assert p in old and not child
        losses, births = old - child, child - old
        assert losses == old and not births
        # This signed boundary is a full parent column, not a new bound.
        assert mu[c] * (len(losses) - len(births)) == mu[c] * len(old)
        q_parent, q_child = partners(d), partners(c)
        q_loss, q_birth = q_parent - q_child, q_child - q_parent
        assert (mu[d] * len(q_parent) + mu[c] * len(q_child)
                == mu[d] * (len(q_loss) - len(q_birth)))
        if output_dir:
            incidence.append(dict(q=q, d=d, p=p, sign=mu[d],
                                  postroot_partners=sorted(old),
                                  q_loss=sorted(q_loss), q_birth=sorted(q_birth),
                                  q2_crossing=(q, d, p) in crossings))

    owners = [q for q in primes_here if 2 < q < root]
    daughters = []
    for q in owners:
        cutoff = endpoint // (q * q)
        far_slice = sum(mu[n] for n in range(1, cutoff + 1)
                        if largest[n] >= root + 8
                        and largest[n // largest[n]] < q)
        owned_descended = sum(mu[d] for r, d, _p in descended if r == q)
        assert far_slice == -owned_descended
        daughters.append(dict(q=q, cutoff=cutoff, mertens=mertens[cutoff],
                              energy=mertens[cutoff] ** 2, far_slice=far_slice))
    q_energy = sum(d['energy'] for d in daughters)
    envelope = max(Fraction((mertens[y] - 1) ** 2, y + 1) for y in range(root))
    excess = max(0, frozen_top_far ** 2 - 4 * q_energy)
    result = dict(R=root, X=endpoint, M=mertens[endpoint], F=frozen_top_far,
                  B=root_boundary, Q=q_energy, K_min=str(envelope),
                  F_sq_over_4Q=str(Fraction(frozen_top_far ** 2, 4 * q_energy))
                    if q_energy else None,
                  required_CF=str(Fraction(excess, root ** 2) / envelope),
                  physical_count=len(physical), downcross_count=len(downcross),
                  residual_count=len(residual), near_mate_mass=mass(near_mates),
                  top_count=len(top), top_mass=mass(top), internal_mate_mass=mass(mates),
                  far_transport=far_transport, far_pair_count=len(stable_pairs),
                  unit_mass=unit_mass, descended_count=len(descended),
                  descended_mass=descended_mass, crossing_count=len(crossings),
                  crossing_mass=crossing_mass, partner_checks=len(incidence)
                    if output_dir else len(triples),
                  two_boundary_gram_verified=False, daughters=daughters)
    if output_dir:
        output_dir.mkdir(parents=True, exist_ok=True)
        # Each row encodes (face product, cofactor, quotient, signed weight).
        ledgers = {name: [list(s) + [weight(s)] for s in sorted(states)]
                   for name, states in [('physical', physical), ('residual', residual),
                                        ('top', top), ('internal_mates', mates),
                                        ('near_mates', near_mates)]}
        ledgers.update(summary=result, incidence=incidence,
                       descended=sorted(descended), crossings=sorted(crossings),
                       caveat='Exact finite identities only. No STOKES-4 Gram identity is assumed.')
        (output_dir / f'R{root}.json').write_text(json.dumps(ledgers, separators=(',', ':')) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--roots', nargs='+', type=int, default=[56, 100])
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    if min(args.roots) < 56:
        parser.error('Frozen/top/far reconstruction requires R >= 56.')
    data = sieve(max(args.roots) ** 2 - 1)
    results = [diagnose(root, data, args.output_dir) for root in args.roots]
    print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
