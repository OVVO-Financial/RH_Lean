# VF actual-prime root-to-square contraction attack

Status: focused attack note.  No RH-scale estimate is claimed here.

## Endpoint convention is dead

At the production square endpoint the repository uses

[
X_R = R^2-1.
]

For the actual-prime owner population above the root, this is exactly the same
carrier as the literal interval through (R^2):

[
{q : R<qle R^2-1, q {m prime}}
=
{q : R<qle R^2, q {m prime}},
]

because (R^2) is composite for (Rge2).

The stronger child statement is also exact.  If (q>R) is prime, then
(q
mid R^2), hence

[
leftlfloorrac{R^2-1}{q}ightfloor
=
leftlfloorrac{R^2}{q}ightfloor.
]

These two facts are formalized in
`VF_MID_ACTUAL_PRIME_ROOT_SQUARE_CONTRACTION.lean`.

Therefore no asymptotic or vertical-fit allowance is needed for the
(R^2-1leftrightarrow R^2) switch on the actual-prime operator.  The existing
VF alignment constant (c_0) remains analytically harmless for the separate VF
presentation: `vfMidAlignedMass_succ` proves that an additive alignment changes
no square-block increment, while
`vfMidAlignedSquareEndpointError_eq_direct_sub` changes the endpoint
discrepancy only by the fixed phase.

## Where continuous Li bites

The exact-Li proof contracts the transformed high-owner packet because its
root-to-square reciprocal mass is subunit.  In the continuous/Dickman
coordinate this is the delay-equation contraction; in the discrete Li
coordinate it appears as the (log 2<1) owner-mass bound.

The corresponding actual-prime square geometry is already exact: the complete
high-owner population is (R<qle R^2), with every reciprocal child below
(R).

## The important normalization issue

The raw actual high-prime transport already compiled in
`PRIME_WHEEL_ROUGH_SEAT_SQRT_SPECIALIZATION.lean` is

[
M(X_R)
=
K_R(X_R)
-
sum_{substack{R<qle X_R\q {m prime}}}
M(lfloor X_R/qfloor).
]

The displayed coefficient of each raw child is **one**, not (1/q).
Consequently a reciprocal-prime mass bound cannot simply be pasted onto this
raw transport identity.  Doing so would silently change the operator.

This is the precise place where the direct attack must normalize before taking
a norm.

## The repo already has the correct actual-prime hazard normalization

The chronological Euler machinery has exactly the desired scalar architecture:

[
H(p::ps)
=
(1-1/p)H(ps)+1/p,
]

and proves

[
H(ps)=1-prod_{pin ps}(1-1/p).
]

For every finite list of genuine primes, the new Lean file proves

[
oxed{0le H(ps)<1.}
]

This is a literal subunit actual-prime owner budget, with no PNT replacement.
The existing theorem
`squareRootCanonicalRoughTransportedDefectLedger_norm_le` goes further:
for a signed chronological defect ledger it gives

[
|mathrm{ledger}|
le
(1-P),Delta,
qquad
P=prod(1-1/p),
]

where (Delta) is the maximum scaled signed defect layer.

So the repo already contains the actual-prime analogue of the **coefficient
mechanism** by which Li contracts.

## Direct target now

Do not build another proxy or another endpoint equivalence.

Attack the following exact bridge on the actual VF/prime chronology:

> Rewrite the root-to-square signed actual-prime correction as the existing
> transported Euler-hazard ledger, or prove the corresponding one-step identity
> directly, so that a fresh prime (q) enters with (1/q) and previously
> accumulated memory is multiplied by (1-1/q).

The required shape is

[
A_{p::ps}
=
(1-1/p)A_{ps}
+
rac{B_p}{p},
]

with (B_p) the **actual signed boundary/child defect**, not a Li replacement.
Then the compiled many-prime telescope immediately yields

[
|A|
le
(1-P)max_p|B_p|,
qquad 1-P<1.
]

That is the place to compare directly with the continuous-Li bite.

### What must not be done

- Do not replace the raw coefficient (1) in
  (sum_q M(X_R/q)) by (1/q) without an exact transform.
- Do not spend any more effort on (R^2-1) versus (R^2); it is exact for
  actual primes and their quotient children.
- Do not use (c_0) as though it supplies arithmetic cancellation.  It only
  handles a fixed vertical phase and leaves block dynamics unchanged.
- Do not turn this into a new RH-equivalent proposition.  The next useful
  theorem is the one-step actual-prime Euler normalization itself.

## Immediate proof search

The most likely splice is between these existing exact components:

1. `squareRootFrozenPrimeUniverse_step_and_support`: a fresh (q>R) subtracts
   the completed lower child (M(X_R/q));
2. `squareRootCanonicalRoughTransportedBoundaryChargeLedger_eq_defectLedger`:
   the physical defect ledger is exactly the Euler-hazard boundary ledger;
3. `squareRootCanonicalRoughTransportedDefectLedger_norm_le`: the many-prime
   chronological ledger contracts by (1-P<1);
4. the direct VF theta/native descent identity, which must remain the consumer.

The attack is successful only if the boundary charge in (2) can be identified
with the actual signed VF/prime child correction from (1)/(4) without an
uncontrolled factor of (q), multiplicity inflation, or an absolute value
taken before the chronological telescope.
