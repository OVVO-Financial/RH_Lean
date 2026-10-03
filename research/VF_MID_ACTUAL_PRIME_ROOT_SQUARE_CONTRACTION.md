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


## Attack update: the correct contraction is a high-owner star

The old canonical-rough post-root Euler ledger is **not** the direct closure.
`CanonicalRoughCriticalDefectWindows.lean` proves that for a fresh prime
(p>R), the scaled defect is exactly the parent reciprocal correlation.  Thus
post-root contraction on that carrier simply recycles the quantity being
bounded.  Do not use that route for the VF proof.

The native PNT / protected-block carrier is different and is now the focus.

For a high owner (q>R), set

[
B_q=leftlfloorrac{R^2-1}{q}ightfloor.
]

Then (B_q<R<q).  Hence every (1le mle B_q) is automatically coprime to
(q), and the compiled native reciprocal-Mobius law applies on the whole
completed child:

[
sum_{mle B_q}
left(v(m)+v(mq)ight)
=
left(1-rac1qight)
sum_{mle B_q}v(m)
+
sum_{mle B_q}D(m,q).
]

The new Lean theorem
`vfMidActualHighPrimeChildReciprocalFiber_adjoin_eq_euler` certifies the pure
fibre form, while
`vfMidActualHighPrimeProtectedPairedReciprocalMass_eq_euler_add_defect`
certifies it on the **direct adjacent-square protected correlation** used by the
VF/(psi) consumer.

The next algebraic simplification is more important.  Below the pre-square
endpoint two distinct high primes cannot coexist in one product.  Therefore,
for one fixed low parent (m), its completed post-root descendants form a star.
Writing

[
Q_{R,m}=
{q	ext{ prime}:R<qle R^2-1,;mqle R^2-1},
]

summing the one-prime laws gives

[
oxed{
v(m)+sum_{qin Q_{R,m}}v(mq)
=
left(1-sum_{qin Q_{R,m}}rac1qight)v(m)
+
sum_{qin Q_{R,m}}D(m,q).
}
]

This is the exact location where a uniform root-to-square actual-prime
reciprocal bound plugs in.  It is **a sum coefficient**, not the Euler-product
hazard coefficient.  In particular, if the already-available root-to-square
prime reciprocal estimate gives

[
sum_{R<qle R^2}rac1q<1,
]

then every star has a nonnegative strictly subunit retained-parent coefficient,
since (Q_{R,m}) is a subset of that owner interval.

The remaining mathematical content is then sharply localized:

1. compile the star identity on the direct protected correlation;
2. identify/bound the summed signed physical defects (D(m,q)) before norms;
3. Abel-return the resulting reciprocal-prefix control to
   `nativePNTSignedSquareBlockMobiusCorrelation`;
4. feed that directly into `vfMidSquarePsiProtectedPull` and its exact energy
   update.

The repo already proves the Abel return and even the contrapositive fact that a
large protected block forces a large reciprocal-prefix excursion.  Thus step
(2), not endpoint convention or existence of the Euler factor, is now the
critical arithmetic seam.
