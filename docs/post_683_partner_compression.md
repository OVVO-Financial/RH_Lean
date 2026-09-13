# Post-#683 partner-column reciprocal compression

This note records the exact composition formalized in
`RHLean/Proof/PostRootPartnerReciprocalCompression.lean`,
`RHLean/Proof/PostRootPartnerEulerMemory.lean`, and
`RHLean/Proof/PostRootPartnerMellinInterpolation.lean`.

The starting point is #683: for a fresh prime `p > R`, the adaptive raw
loss/birth boundary is the intact raw correlation of the parent, equivalently
its full signed partner-incidence column.  The reciprocal Euler coordinate is
the same response divided by the parent cofactor.

The branch proves, before any norm:

1. raw weighted mass equals reciprocal weighted mass after multiplying the
   coefficient by the cofactor;
2. the post-root #683 boundary is exactly a cofactor-weighted reciprocal parent
   mass;
3. reciprocal normalization feeds that partner column directly into the #540
   actual-parent-carrier many-prime compression;
4. `p * Defect = Boundary` for the actual cofactor-weighted physical defect;
5. evolved coefficient mismatch vanishes on a complete descending prefix;
6. complete descending schedules kill the final raw mass exactly;
7. the frozen/top/far residual is therefore chronological raw ledger plus the
   explicit root correction, with no final adaptive remainder;
8. `p * (EulerNext - RawNext) = (p - 1) * Boundary`;
9. raw and reciprocal prime steps are the `z=1` and `z=1/p` endpoints of one
   multiplicative interpolation;
10. the log square-collision correction is q^2-or-deeper: a p-free q^2 block is
    an ordinary q^2 Mertens block plus a p-free q^3 remainder, iterating only
    through p^2,p^3,... scales.

## LOG-MATCH

The reciprocal Mellin kernel on the stable-far physical chronology is

```text
K_Mellin(p) = 1/p.
```

A naive projection that keeps only completed q^2 descendants does **not**
commute with this kernel.  Its entire commutator is the strict-crossing
population.  The physical q^2 operator does not discard those crossings: it
returns them to the stable-far wall.  The compiled depth-one renewal sends each
nonunit crossing to its next descended child while preserving the same far
prime `p`, and unit returns are centered on that same far prime.

`PostRootPartnerMellinInterpolation.lean` states the physical seam as the single
named proposition `LOG_MATCH` and proves the renewal-corrected commutation
against arbitrary test observables.  In operator language:

```text
P_q K_Mellin = K_Mellin P_q.
```

The arbitrary-test formulation is an equality of finite signed pushforward
measures rather than a scalar checksum.  No PNT estimate, Perron inversion,
norm, or RH-scale hypothesis is used.

## p^{-1} diagnostic

`scripts/far_four_diagnostic.py --pinv-only` uses the exact stable-far carrier
census; floating point is used only to evaluate reciprocal-prime sums quickly.

| R | naive commutator | crossing L1 reciprocal mass | |signed|/L1 | renewal-corrected |
|---:|---:|---:|---:|---:|
| 56 | 0.7291603914 | 4.3482900023 | 0.1676889975 | 0 |
| 100 | 0.7147719737 | 7.4973566336 | 0.0953365311 | 0 |
| 500 | 0.9662456647 | 36.5832641167 | 0.0264122322 | 0 |
| 2000 | 1.3308003141 | 132.4888176390 | 0.0100446237 | 0 |

The shrinking signed/L1 ratio is diagnostic only and is not used as a bound.
The exact theorem comes from preservation of the far-prime coordinate through
q^2 descent and strict-crossing renewal.

## Scope of the claim

LOG-MATCH, in the physical Mellin/q^2 commutator sense above, is an exact
finite theorem on this branch.  This note does **not** claim FAR-4 or RH from
that theorem alone.  The remaining work is consumer wiring: substitute the
compiled proper-subwheel/q^2 daughter identities into the signed chronology and
verify that the terminal energy consumer sees only the q^2-or-deeper packet,
without reintroducing a first-power carrier.
