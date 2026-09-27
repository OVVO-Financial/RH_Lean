# Post-789 coefficient sharpening and current research state

Date: 2026-09-27.

## Scope and status

This note records a genuine relaxation of the sufficient coefficient targets,
not a proof of the uniform arithmetic estimate and not a new coordinate system.
The [current contract](../CURRENT_PROOF_CONTRACT.md) is updated accordingly.
All earlier obstruction theorems, identities, and consumers are retained.

The proof scripts are appended to the existing
[correlation comparison module](GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE.lean).
That file is already a path trigger and a checked module in the
[signed-cell Stokes workflow](../.github/workflows/signed-cell-stokes-bridge.yml).
No library module, root import, export manifest, or workflow is changed.
Hosted verification at the exact PR head is the Lean certification gate.

## Same carrier and quantifiers

For natural R >= 56, let

```text
X = R² − 1,
G = M(X) − M(R−1),
E = sum_{q odd prime, q² < R} M(floor(X/q²))²,
Q = sum_{q odd prime, q² < R} M(floor(X/q²))/q,
S = G² + 2QG − D,
F = FinalStokes_R = (G+Q)² − D.
```

The existing quarter frame and diagonal estimates are `4Q² <= E` and
`0 <= D <= 3R²`. The lower envelope is

```text
LowerMertensCriticalEnvelope R K:
  0 <= K and (M(y)−1)² <= K(y+1) for every natural y < R.
```

In particular K >= 1, using y = 0. Every sufficient upper bound below means

```text
exists C >= 0, for all natural R >= 56 and all real K,
  LowerMertensCriticalEnvelope R K -> the stated inequality.
```

C must be independent of R and K. No change to the owner set, daughter cutoff,
root convention, diagonal, or lower-envelope quantifiers is made.

## Exact certificates

The signed-remainder certificate is

```text
S − (3G²/4 − E − 3R²)
  = (G+4Q)²/4 + (E−4Q²) + (3R²−D).
```

Every term on the right is nonnegative, hence

```text
3G²/4 − E − 3R² <= S.
```

If `S <= A E + C R² K`, then

```text
G² <= [4(A+1)/3] E + [4C/3+4] R² K.
```

At A = 2 this is exactly CORR-4. The second certificate is

```text
4F − 3G² + 3E + 4D = (G+4Q)² + 3(E−4Q²).
```

It gives `3G²/4 − 3E/4 − 3R² <= F`. If `F <= B E + C R² K`, then

```text
G² <= [4B/3+1] E + [4C/3+4] R² K.
```

At B = 9/4 this is again CORR-4. The existing
[CORR-4 terminal bridge](CORRELATION_FOUR_TERMINAL_BRIDGE.lean) then supplies
the conditional implication to RH with no additional open bookkeeping premise.

| Signed input | Earlier sufficient endpoint | Relaxed sufficient endpoint |
| --- | --- | --- |
| `S <= A E + C R² K` | A = 3/2 | A = 2 |
| `F <= B E + C R² K` | B = 7/4 | B = 9/4 |

Smaller coefficients also suffice because E >= 0. The earlier transfers remain
valid. The new comparison is not claimed to dominate the earlier comparison
for every value of E/G²; it gives a better sufficient coefficient at the
CORR-4 target. Nor is a universal upper limit on possible proof methods claimed.

## Lean declarations

The appended declarations are:

- `post789_remainder_threeQuarters_certificate` and
  `post789_finalStokes_threeQuarters_certificate`: exact polynomial identities;
- `threeQuarters_correlationSq_sub_le_post789SignedRemainder` and
  `threeQuarters_correlationSq_sub_le_finalStokes`: unconditional lower comparisons
  on the actual repository objects;
- `correlationLowQ2Energy_of_post789SignedRemainderBound_threeQuarters` and
  `correlationLowQ2Energy_of_finalStokesQ2EnergyBound_threeQuarters`: general
  transfers, preserving the explicit uniform upper-bound hypothesis;
- `correlationFour_of_post789SignedRemainderBound_two` and
  `correlationFour_of_finalStokesQ2EnergyBound_nineQuarters`: CORR-4 consumers;
- `riemannHypothesis_of_post789SignedRemainderBound_two` and
  `riemannHypothesis_of_finalStokesQ2EnergyBound_nineQuarters`: conditional RH
  consumers, not unconditional proofs of RH.

No premise supplying the missing arithmetic estimate is introduced under a new
name. The consumers take the existing bound predicates as explicit arguments.

## An exact normalized research target

Define, in this explanatory note,

```text
K_*(R) = max_{0 <= y < R} (M(y)−1)²/(y+1),
H_2(R) = max(S_R−2E_R, 0)/(R² K_*(R)).
```

For R >= 56 this finite maximum exists and K_*(R) >= 1. It is the least
admissible lower-envelope constant. The uniform A = 2 statement is equivalent
to `sup_{R >= 56} H_2(R) < infinity`:

1. A uniform bound applies at K = K_*(R), giving H_2(R) <= C.
2. Conversely, H_2(R) <= C with C >= 0 gives the desired inequality at K_*(R),
   hence at every admissible K >= K_*(R).

This elementary normalization is documented here; this PR does not formalize
K_* or H_2 in Lean, compute new large-root records, or prove their uniform
boundedness. Finite diagnostics should distinguish a record of H_2 from a
proof that all future records are bounded.

## What investigating the other direction can establish

A failed shortcut, an unproved estimate, and an impossibility theorem are
three different conclusions. The earlier pause on repeating tested identities
is a research policy, not a theorem that these reduced bounds cannot be proved.
The new square completion demonstrates that even an existing comparison can
admit a useful coefficient improvement without changing coordinates.

An equality is already reversible. A sufficient implication `P -> RH` does not
by itself give `not P -> not RH`. To turn a disproof of P into a disproof of RH,
one must also prove `RH -> P` for exactly the same P, including its coefficient
and quantifiers. This PR proves no such converse. Similarly, one finite
violation rejects a chosen constant C, not the existence of every finite C.

The earlier finite examples remain useful structural and regression evidence.
A finite certificate combined with a proved induction can establish an
all-scale result; a finite collection of successful evaluations cannot replace
that induction or a uniform estimate. No known impossibility of the remaining
arithmetic estimate is asserted here.

## Validation record

At authoring, independent symbolic expansion of each displayed polynomial
certificate gave residual zero, and both endpoint coefficient transfers gave
exactly 4. This checks algebra, not Lean elaboration or a uniform Mertens bound.

There is no local Lean/Lake installation in the authoring container; a direct
repository clone also failed because the container could not resolve the
GitHub host. Consequently `scripts/local_ci.sh` and the full local repository
audits were not run. The changes were made through the connected GitHub API.
The existing hosted source/export/documentation gates and the warning-fatal
signed-cell Stokes job must pass on the exact PR head before this is described
as kernel-checked. Do not infer green status from the symbolic checks.
