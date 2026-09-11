# Current RH_Lean research handoff

This file records the current mathematical frontier for any research agent continuing the repository. It is intentionally model-agnostic.

## Governing rule

Do not search for a new coordinate system first. The recent formalization has proved that several historically separate descriptions are exact representations of the same signed endpoint/run object. The task is now to exploit the strongest theorem available in each representation on that common carrier.

Keep the proof elementary and Eulerian. The genuine arithmetic operation is adjoining a fresh prime.

## Contact-frame no-go: counting is not cancellation

`ExceptionalContactFrameEnergyNoGo.lean` closes off a recurring proposal: compute
a frame constant `alpha_q` for the six-contact `q^2` pullback on the finite
super-orbit `Z/q^2 x Z/11^2`, prove `alpha_q <= 3`, and feed it to
`ExceptionalOwnerEnergyStep` through `3*(1/9+1/25+1/49)=1891/3675<1`.  Read
compilation status from Hosted Lean at the PR head.  Three exact finite facts
are certified.

1. The contact classes are the active offsets pulled back by `4`, not the offset
   set.  `physicalTransitionActiveOffsets={1,2,3,5,6,7}` are offsets `a` inside
   the site `4*k+a`; the cell classes are their images `2*a mod 9`,
   `6*a mod 25`, `12*a mod 49`, that is the already compiled
   `physicalNineChannelResidues`, `physicalTwentyFiveHitResidues`,
   `physicalFortyNineHitResidues`.  The module proves both the image identities
   and the disequalities, so the two six-element sets cannot be conflated again.

2. The frame constant is exactly two, for EVERY field.  `q` is odd, so `q^2*d`
   and `d` agree mod four and the six offsets split into the mod-four pairs
   `{1,5}`, `{2,6}`, `{3,7}`; a daughter has two tagged preimages off the zero
   class and none on it.  `contact_frame_two` is stated for an arbitrary
   `w : ℕ → ℤ`, and `contact_frame_three` derives the proposed `alpha_q <= 3`
   from it.  So that estimate is a corollary of fibre counting and carries no
   Mobius input.  `contact_frame_two_sharp` shows two is attained on the
   all-ones field, so no field-independent constant is smaller; the gap between
   three and the numerically observed value near one is an assumption about
   Mobius signs, not arithmetic content.  A least-owner restriction only deletes
   preimages, so `<= 2` persists and the route is not helped there.

3. Assembled coefficient norm and recursive Mertens energy are different
   objects.  `contactDaughterCoefficientNorm q Y` is the squared mass of the
   assembled `q^2` children over the daughter range, which is what a frame
   estimate bounds; the induction consumes `E (X / q^2)`.  With the recursive
   Mertens energy the separation is an exact finite witness:
   `mertensSummatoryInt 2 = 0`, while the assembled norm at `Y=2` is `2`, `5`,
   `5` for owners `3`, `5`, `7`.  Hence
   `no_contactDaughterCoefficientNorm_mertensEnergy_constant`: no constant
   compares them, at any scale.  This is a type mismatch, not a bad constant.

What the module does not claim.  The finite mask operator exists and is well
defined; only its norm is trivial.  What does not exist is a fixed finite Mobius
vector on the residue torus whose spectral data could be computed once and
reused at every period: the masks are periodic, the Mobius observable is not,
and the compiled transported field reconstructs its value by pulling back to the
physical source cell (`selectedDegreeOneOffsetDaughterField`) rather than
assigning a value to a residue class.  Nothing here refutes the coefficient-level
compensation of #655, the `q^2` transport, or RH.

Operative rule for continuations.  Never square the coefficient daughters before
their physical signed reassembly.  The `q^2` budget and any frame estimate may
be applied only after the compensated children, with their second-contact and
earlier-owner mates, have been reassembled into a signed packet; the viable
target is that reassembled packet being the lower-scale Mertens-visible packet
up to the already-controlled endpoint carrier, not an ownerwise `L^2` mass.

## Joint-daughter frame clarification after #655

`JointDaughterCrossEnergyAudit.lean` distinguishes the proposed subunit joint
frame from cancellation inside one daughter. For three intact daughters,
write `D=sum norm(Phi_q)^2` and `C=sum_{q<r} inner(Phi_q,Phi_r)`. Exactly,

```text
norm(sum Phi_q)^2 <= c*D+B  <->  2*C <= B-(1-c)*D.
```

The negative term required here is cross-OWNER energy. Internal `F/T`
alignment does not itself prove it. With the compiled scalar predecessor
cubes, every additive incidence image of `F` is actually zero for `X>=1470`;
the within-owner `F/T` inner product is then exactly zero too. If an unsummed
field is intended instead, it needs its own physical operator and coefficient
dictionary; the scalar prefix identity does not establish that field identity.

The same module records that the universal three-vector synthesis factor
already has budget `3*(1/9+1/25+1/49)=1891/3675<1`. Consequently, a unit-normalized
physical daughter comparison and parent reconstruction with a linear error
would imply `E(X)<=3675*C*X/1784` without a subunit frame. Both physical
comparisons remain explicit hypotheses. This exposes the missing energy
normalization rather than proving it. No bound for the proposed arithmetic
boundary `B(X)` or an RH-scale physical Gram is claimed. Consult Hosted Lean
for compilation status at the current PR head.

## Continuation after #654: preserve the physical carrier before q-square closure

PR #655 audits the requested exceptional-owner continuation. Read compilation
status from Hosted Lean at the PR head; none of the new modules proves RH or
the missing physical arithmetic estimate.

`ExceptionalSignedPacketIdentification.lean` supplies a coefficient-level
dictionary on the actual complete least-owner carrier. Its source packet is
defined from the true physical observable, with blocker `P` and recovery `S`
separate. It is exactly the sum of signed predecessor `F-T` increments at
`4*k` and `4*(k+1)`. The existing `physicalD9`, `physicalD25`, and `physicalD49`
LOCAL-BLOCK identities instead use the destination increments at `4*(k+1)`
and `4*(k+2)`. Neither dictionary divides those endpoints by `q^2`.

Two distinctions still prevent the advertised physical q-square identity:

1. The blocker mass `squareBlockOutsidePrimeLeastCompleteT` uses the selected
   observable `selectedDegreeOneProjection P`; the recovered incidence uses
   the true Mobius observable. The selected-to-Mobius parity compensation
   remains necessary, exactly as the #654 finite certificates require.
2. The algebraic two-step identity in `TwoWheelQ2Compensation` does not yet
   identify its parent, current response, and first-power mate with those
   physical occurrences. The uncompensated LOCAL-BLOCK alone cannot supply
   this identification: at `L=39` its owner-three value is `-5`, whereas the
   scalar daughter `M(1440/9)` is zero. The new module certifies this finite
   mismatch. It does not rule out a correctly constructed compensated packet.

`ExceptionalOwnerEnergyClosure.lean` proves the conditional unequal-coefficient
induction with exact budget

```text
beta = alpha3/9 + alpha5/25 + alpha7/49 < 1,
E(0)=0, E(X) <= C*X + sum alphaq*E(X/q^2)
  ==> E(X) <= C/(1-beta)*X.
```

For a common coefficient the threshold is `11025/1891`, not one. Eight times
the selected-11 energy factor fits; twelve times does not. Optimal weighted
Cauchy has amplitude budget `a3/3+a5/5+a7/7`; local factor four combined with
unrestricted owner alignment still fails. An aggregate signed correlation
comparison with coefficient `2/3` would numerically fit, **provided the actual
physical dictionary and selected-11 transfer were proved**. This comparison
is not supplied by the closure theorem.

`ExceptionalTransportCoboundary.lean` makes a further arithmetic obstruction
explicit. The predecessor-cube products for `3,5,7` are `2,6,30`. For
`X >= 1470` all three scalar Go daughters vanish, so `F-T=-T=M(X/q^2)` and
their scalar Gram is purely `TT`. The prime-insertion coboundary therefore
retains the complete Mertens daughter as its terminal potential. There are no
nonzero scalar `FF`, `FT`, or `TF` pieces to cancel in this regime.

At the actual square endpoint `X=41^2-1=1680`, the scalar daughters are
`(-4,-2,-2)`. They violate the universal `2/3` comparison; at this endpoint
the interpolated scalar comparison requires coefficient at least `175/179`.
This is a finite counterexample to that uniform scalar claim, not a proof
against an eventual bound, a compensated physical Gram estimate, or RH.

`SignedTransportAmplificationAudit.lean` retains the exact amplification
numerator `norm(matched-H-1)^2 = (M(R^2-1)-1)^2`. Any fixed amplification
constant in the existing all-root formulation is at least one, already at
`R=2`. The existing closure accepts any finite constant; the uniform bound
itself remains unproved.

The immediate missing theorem is the physical parent/response/mate
compensation and parity transfer on the complete selected carrier, with the
literal signed recovered daughter and all endpoints recorded. After that,
an arithmetic energy estimate must still instantiate the restricted induction
or the amplification theorem. Do not promote the local incidence dictionary,
the scalar telescope, or the conditional constant audit into that estimate.

## Matched-channel recovery audit after #649

`SquareRootMatchedDegreeOneRecovery.lean` makes the terminal-to-three-slot
correction explicit. Read its compilation status from Hosted Lean at the
current head. With `H_R = sum_{p <= R, p prime} M(p-1)`, the exact identities are

```text
matched R - H_R = M(R^2-1),
unifiedReciprocal R = 1 - M(R^2-1),
terminal R K j - H_R = M(R^2-1) - shallowBoundary R K j.
```

The recovered terminal has error at most `R+K` from Mertens and `R+K+3` from
the complete four-cell degree-one sample. The new energy equivalence and RH
implication keep `-H_R` inside the norm. They prove no bound on that quantity.
Do not identify the matched-only bound or its terminal energy telescope with
the three-slot criterion. The older `SquareRootSmoothParityClasses` implication
requires both matched and positive-smooth estimates; neither is discharged by
the exact telescope. This audit does not prove that a matched-only implication
is impossible, or that the matched-only estimate is false.

The born-smooth reciprocal reindexing already existed before this audit.
PR #649 proves the exact Li/floor/PNT decomposition and negligibility of the
seven-coordinate strip; its final code does not prove the wall's proposed
normalized limit `-1`. Neither that asymptotic nor RH is claimed here.

## Continuation after #646: the stable far-prime wall is inhabited

`SquareRootLowPrimeCombinedResidualSourceNormalForm.lean` now constructs the
explicit empty-face, unit-cofactor wall state `(empty, (1,q))`.  For every
`R >= 56`, Bertrand gives `R+7 < q <= 2*(R+7) <= X_R`.  Read compilation status
from Hosted Lean CI at the current head.

The actual wall filter excludes six high-product images, including the
RoughPrefix square-residual integer image.  Every non-near image has composite
high products, while the near image is below `R+8`.  Thus the stronger exact
conclusion is

```text
stableFarWallCarrier R = lowWheelFarTaggedPhysicalStableCarrier R,
stableFarAccountedCarrier R = empty,
R >= 56 ==> stableFarWallCarrier R != empty.
```

Outcome 6c is therefore the surviving branch of Lemma 6.  The membership
characterization uses the real invariant: `lowWheelTaggedHighProduct` is
`P(t)*q`, excluding the cofactor.  On stable states `t=empty`, so this is `q`
itself, not `q/c`.

The final theorem
`oldResidual_add_fullFaceDefect_eq_sourceAssembly_add_rootTerms_add_farWall`
keeps the exact signed source, root/near, and wall blocks.  It preserves every
additive occurrence; identifying a deep defect with a canonical seed does not
erase a same-sign copy from a sum.  The stable wall is not put into the
incomplete boundary or the tagged-11/q^2 daughter schedule.  No frame inequality
or root-scale estimate is supplied for it, and #644 is unchanged.

The subsequent research target is the wall packet alone.  Its stable prime
quotient is `q >= R+8`, so `X_R/q^2=0`; its physical integer is the single
insertion `c*q`.  The existing #622 far transport identity must retain its
original signed weight and endpoint convention in any continuation.

## Continuation after #639: audit the admissible energy before closing it

`PhysicalDaughterEnergyObstructions.lean` extends the corrected six-offset
transport on its exact carrier. Read compilation status from Hosted Lean CI.

The selected `{11}` least-owner `3` deletion mass over `4356*m` source cells is
exactly `2280*m`. The proof preserves the six-offset assembly, the selected
zero-free mask, and the least-owner condition. Consequently no energy envelope
that dominates all these raw selected prefixes can satisfy `ElevenQ2EnergyStep`.
This does not concern the fully reconstructed Mobius field: the selected term
must remain signed-coupled to the rest of that reconstruction. Merely retaining
the affine pullback or restricting to actual deletion carriers is insufficient.

The exact #638 Go-or-root column is also not the existing endpoint object of
one square block. At `R=1000`, the shallow root column is `7041`. Subtracting the
shallow Go daughters leaves `7002`. Each exceeds the single-block endpoint
bound `3*(2R+1)=6003`, so neither quantity can literally equal that endpoint for
any selected prime set. These are finite nonidentification certificates, not
proofs of an asymptotic lower bound or impossibility of signed cancellation with
the root anchor. The all-daughter decomposition now retains the exact signed
correction explicitly.

There is a positive closure refinement in
`SquareRootLowPrimeTSectorQ2Renormalization.lean`: the subcritical induction now
accepts any nonnegative coefficient at most `3/4`, preserving the old theorem.
Young absorption gives

```text
(I+b)^2 <= (13/12)*I^2 + 13*b^2,
(13/12)*(19/23)^2 < 3/4.
```

Thus a genuinely global boundary with `b(X)^2 <= B*X`, together with the desired
interior inequality, yields `E(X) <= 52*B*X`. It is unnecessary to preserve the
exact original coefficient when adding the boundary. The physical signed
interior inequality and a uniform admissible state preserving full Mobius
reconstruction are still open; no RH or Mertens exponent improvement is claimed.

## Current continuation after #608: consume the middle boundary with its base

`research/HALF_ROOT_BOUNDARY_BASE_TELESCOPE.lean` continues the signed
base/boundary coupling left by #608. Read its compilation status from the
dedicated `Proper subwheel depth-two check` at the current head.

The general finite Euler telescope, for `Y <= K <= X` and `X < (Y+1)^3`, is

```text
F_Y(X) - sum_{Y<p<=K} F_p(X/p)
  = F_K(X) + sum_{Y<p<=K} M(floor(X/p^2)).
```

At `Y=R/2`, `K=R`, the entire middle moving boundary is consumed by the
base's advance to the physical root. Its residue is exactly the existing
`halfRootPrimeSquareCorrection R`, already bounded by `R+1` for `R >= 6`.
Thus the middle coupled difference has root-scale error without taking
separate norms of its two large terms.

After the top states complete, the exact coupled core is

```text
halfRootBoundaryCoupledCore(R)
  = F_R(X_R) - sum_{R<p<=X_R} M(floor(X_R/p)) + squareCorrection(R)
  = smooth(R) - highTransport(R) + squareCorrection(R)
  = M(R) - canonicalDefect(R) + squareCorrection(R).
```

The last two identities are explicit complex-cast bridges to
`squareRootSmoothMass (R-1)`, `squareRootTransportCofactorFirst R`, and
`lowWheelCanonicalDefectLedger R`. They preserve the exact root and endpoint
conventions. The square correction is shared with #608 and cancels when the
endpoint is reconstructed; these are not two independent additive errors.

This identifies the remaining target with the existing signed smooth/high
transport coupling, equivalently the canonical root-crossing defect. The
middle moving chronology is not an additional quantitative seam. No bound on
the canonical defect, improved global Mertens exponent, or RH closure is
proved by these identities. In particular, a root-scale correction to an
unbounded core is not itself a global root-scale bound.

## Current finite-wheel continuation: explicit counts and a signed 2310 overlap

PR #604 continues the merged #603 wheel identities on their exact physical
`roughInterval W a b = T_W(b) - T_W(a)` carrier, with `a < n <= b`.
Compilation status must be read from Hosted Lean CI at the current head.

`RoughWheelFiniteCounting.lean` injects each interval into its intersecting
wheel periods and reduced residues.  If `r(W)` is the number of reduced
residue classes, the finite, wheel-uniform bound is

```text
card roughWheelInterval(W,a,b) <= r(W)/W * (b-a) + 2*r(W),  a <= b.
```

`PostRootCovarianceWheelCounting.lean` applies this after the exact signed
wheel identities. It gives the following explicit Mertens majorants and
transfers each to `E(W) <= majorant(W)^2/2` by the existing Bessel theorem:

```text
6:     |M(B)| <= (2/9) B + 9
30:    |M(B)| <= (16/75) B + 66
210:   |M(B)| <= (256/1225) B + 770
2310:  |M(B)| <= (17648/88935) B + 15364
```

The last estimate uses a new exact signed cancellation. Adjoining `11` to the
210-wheel creates a negative band `(B/22,B/11]`, overlapping the positive
15-band `(B/30,B/15]`. Their common interval `(B/22,B/15]` cancels before
absolute values. This reduces the 2310 leading coefficient from `6144/29645`
to `17648/88935`, a gain of `16/1815`. The exact overlap-cancelled identity was
also checked numerically at every integer endpoint from 0 through 100000;
that finite computation is a sanity check, not a substitute for the kernel.

The elementary factor audit reuses `PrimorialReciprocalMobiusFactorization`:
separate-band counting has density factor `1-1/p` but gains child interval
length `1+1/p`. Its leading coefficient is therefore

```text
c(P) = (1/4) * prod_{p in P} (1 - 1/p^2),  P the selected odd primes.
```

An elementary finite telescope proves `c(P) >= 1/6` even when all integers
at least three are allowed as factors. Thus the separate-band estimate alone
cannot force a power saving by enlarging the wheel. This is NOT a lower bound
on Mertens and NOT an obstruction to further signed overlap cancellation.
The new 2310 identity demonstrates exactly where an extra signed gain occurs.
The displayed errors also grow with the wheel and must remain in any proposed
iteration with a wheel depending on the physical endpoint. No exponent
improvement, bounded critical envelope, or RH closure is claimed here.

## Current continuation: the tower is one proposition, and the exchange rate is exact

`PostRootCovarianceGlobalExponentTransfer.lean` supplies the return path that
every reduction from #596 to #602 was missing, and thereby settles what the
record machinery can and cannot do to the unconditional global exponent.

### The return path is one line

In the compiled Bessel identity

```text
2*E(W) = M(W)^2 - complementDiagonalResidual(W) - familyMertensSquareEnergy(W)
```

both subtracted terms are already proved nonnegative.  Hence, unconditionally,
with no cancellation, no record hypothesis and no sieve,

```text
E(W) <= M(W)^2 / 2.
```

### Consequence: every seam in the tower is the same proposition

```text
MertensPowerSavingStatement                          (|M(x)| << x^((1+eps)/2))
  <-> MertensEnergyBoundedStatement
  <-> MertensSquarePowerEnvelopeBoundedStatement
  <-> PostRootCovariancePowerRemainderStatement
  <-> PostRootCovariancePowerEnvelopeBoundedStatement
  <-> PostRootCovariancePowerRecordExcessBoundedStatement
  <-> PostRootFallingEnergyFiniteDifferencePowerStatement
```

All of these are now compiled bi-implications.  Nothing in the post-root,
LCM-wall, envelope, or record layers has cost anything, and nothing in them has
gained anything either.

### The exchange rate, and the no-go it implies

`postRootCovarianceRemainder_le_of_mertensPowerBound` is pointwise and
unconditional:

```text
|M(W)| <= B * W^theta   ==>   E(W) <= (B^2/2) * W^(2*theta).
```

Together with the equivalence above the rate is exact.  **This is a no-go for
the current carrier: no post-root, wall, envelope, or record reduction can
improve the unconditional global exponent without an improvement of the Mertens
exponent itself, and a Mertens power saving `|M(x)| << x^(1-delta)` is a known
open problem (a zero-free strip).**  Record it as such; do not re-derive a
weaker version of it.

### What can move unconditionally: the constant

The exponent cannot move here, but the constant can, and it is moved:
`|M| <= squarefree count`, and one residue in every block of four is a multiple
of four and so not squarefree, giving `|M(K)| <= 3*(K+3)/4` and

```text
E(W) <= 9*(W+4)^2/32,
```

which improves the compiled `E(W) <= W^2` by a factor `32/9` for every
`W >= 5`.  The same sieve extends: excluding `9` as well gives `2/3` and
`E(W) <= (2/9)W^2 + O(W)`; the elementary limit of this route is
`(6/pi^2)^2/2 = 0.1848...`.  A finite check to `W = 4000` finds
`max E(W)/W^2 = 0.0059`, so the sieve bound is far from tight and further
constant work here is cheap but is not exponent progress.

### The record threshold, in closed form

```text
E(W+1) < innovation(W) * (W+1)                               at every record,
E(W+1) < (M(W+2)^2 - M((W+1)/p+1)^2) * (W+1)                 on an active
                                                             post-root divisor.
```

Both are unconditional and carry no `eps` power on either side.

### Where to go next

The remaining work is the Mertens exponent itself, on whatever coordinate.  The
record carrier is a legitimate place to attack it -- it is lossless -- but the
attack has to produce a Mertens power saving, not another reduction.  Consult
Hosted Lean CI for the compilation status of this head.

## Previous continuation: the record step is the carrier

`PostRootCovarianceRecordAbsorption.lean` moves the whole remaining problem
onto the record step of the #600 envelope.  Three things are proved.

### Exact wall split, no triangle inequality

```text
postRootCovariancePowerLocalInnovationBudget eps N
  = postRootRecordOuterRowSeat eps N + postRootRecordDepartureSeat eps N.
```

This is an equality.  The two mechanisms have disjoint support: at a
prime-square endpoint `W+1 = p^2` the physical Moebius row is zero (`p^2` is
not squarefree) and the entire active inherited row total is zero (the only
prime that could divide `W+1` is `p`, which has already left the family set);
away from a prime square the departure is zero.  So no positive part is split
across a cancelling pair, and `mu(W+1) M(W)` never has an absolute value taken.

At a post-root quotient jump the outer row numerator is identified exactly:

```text
mu(W+1) M(W) - activeInheritedRow(W)
  = -mu(c) * (M(W) + M(c-1)),   c = (W+1)/p,  p > sqrt(W+1),  p | W+1.
```

### Record threshold: one full endpoint power

A positive record at `N >= 2` forces the old envelope to beat the *increment*
of the endpoint scale, because the old remainder is already bounded by the old
envelope at the old scale:

```text
env(N) * ((N+1)^(1+eps) - N^(1+eps)) < innovation(N),
env(N)   * N^eps     < innovation(N),
env(N+1) * (N+1)^eps < innovation(N).
```

This is one full power stronger than the naive `innovation / (N+1)^(1+eps)`
localization, and the gain comes from the record hypothesis, not from an
absolute value.  At a fresh prime the innovation is `-M(N)`, so a record there
forces `M(N) < -env(N) * N^eps`.

### The square wall is absorbed by its `p^2` sparsity

The departure is supported exactly on prime squares and equals the complete
lower covariance there:

```text
departure(W) = 0                                   if no prime p has p*p = W+1,
departure(p^2 - 1) = C(p) = realMertensPositiveLagPairSum p.
```

Since `2 C(K) = M(K-1)^2 - diagonal(K)` and the diagonal is nonnegative, the
normalized wall seat is at most `A^M_eps(X) / (2 p^(1+eps))`, and the whole
horizon sum is bounded unconditionally:

```text
sum_{N < X} departureSeat_eps(N)
  <= (A^M_eps(X) / 2) * sum'_{k} k^-(1+eps).
```

`A^M_eps` is the #600 Mertens square envelope, and
`mertensSquarePowerEnvelopeBounded_iff_mertensEnergyBounded` shows it is
*exactly* the terminal Mertens energy criterion.  So the departure costs one
fixed constant relative to the target itself and contributes no growth of its
own.  This is an absorption theorem, not an assumption that the wall is
harmless.

### An unconditional ceiling falls out

Feeding only the trivial one-endpoint bounds

```text
mu(N+1) M(N)            <= N+1,
-activeInheritedRow(N)  <= N+1,
departure(N)            <= N+1,
```

through the record threshold gives, for `0 < eps <= 1` and `X >= 2`,

```text
env_eps(X) <= max(env_eps(2), 3 * X^(1-eps)).
```

That improves #600's coarse `env_eps(X) <= X` by a full `X^eps` with no
arithmetic input at all; the entire gain is the record structure.  It does not
improve the remainder past the already-proved `E(W) <= W^2`.

### What is still open

`postRootRecordAbsorptionEnvelope` is the record-conditioned budget

```text
g_eps(N) = if env(N) < seat(N+1) then outerRowSeat + departureSeat else 0,
r_eps(N) <= g_eps(N),
sup_X sum_{N < X} g_eps(N) < infinity  ==>  MertensEnergyBoundedStatement.
```

**The record indicator is not cosmetic.**  Dropping it leaves the pointwise
positive part of `mu(N+1) M(N)`, of size about `N^(-1/2-eps)` on a positive
density set, whose sum diverges.  Any majorant that re-bounds every step by the
same worst-case threshold therefore cannot close the seam; record sparsity has
to be used.  Numerically, for `eps = 0.1` and `X = 20000` the unconditioned
outer-row seat sum is already `6.36` and growing, while the record-conditioned
sum is `0.119` with a single record in the whole range.

There are two equivalent-strength formulations of what is left, both proved
sufficient for the terminal criterion:

```text
sup_X sum_{N < X} postRootRecordOuterRowRecordSeat eps N < infinity,
```

and, sharper because it is pointwise rather than a sum,

```text
PostRootRecordInnovationPowerBoundedStatement:
  for every eps > 0 there is D with
  innovation(N) <= D * (N+1)^eps  at every N >= 2 with a positive record.
```

The second is the cleanest statement of the gain: the unconditional problem
asks for `W^(1+eps)` at every endpoint, and the record process has absorbed one
full endpoint power, leaving `W^eps` at record steps only.  By the exact wall
split and the departure absorption, the only term in that innovation that is
not already controlled is the record-breaking physical new row after inherited
high transport has been removed.  Nothing in this module bounds it.  Consult Hosted Lean CI for the
compilation status of this head.

## Previous continuation: individual inherited rows and cumulative energy

`PostRootCovarianceRowEnergy.lean` moves the lower-prefix estimate inside the
unit-step covariance row.  It proves, for all `W,p`,

```text
row_p(W)^2 <= M(floor(W/p))^2,
row_p(W) = C(floor((W+1)/p)) - C(floor(W/p)).
```

With the finite envelope `A_eps(W) = max_{d<=W} M(d)^2/(d+1)^(1+eps)`, every
post-root coordinate satisfies

```text
row_p(W)^2 / (W+1)^(1+eps) <= A_eps(W) / (W+1)^((1+eps)/2).
```

At most one active post-root prime divides `W+1`, so the same estimate holds
for the square of the entire active inherited-row sum, with no multiplicity
factor.  The Mertens envelope here is distinct from #600's covariance-remainder
envelope.  No record hypothesis is needed for this finite estimate.

The complete local innovation is also identified exactly:

```text
E(W+1)-E(W) = mu(W+1) M(W) - activeInheritedRow(W) + departure(W).
```

`departure` retains the covariance of families removed at the prime-square
wall.  The full expression feeds #600's existing record budget.  The small
inherited-row estimate alone does not bound the physical new row or the
departures, and does not prove boundedness of either envelope.

**Sign audit:** transporting both the atom and its family prefix preserves the
covariance product: `(-mu(c)) * (-M(c-1)) = mu(c) M(c-1)`.  Reversing only one
factor against an unchanged prefix negates the product.  In the remainder the
inherited row has a minus sign because it is subtracted.  At a new prime the
inherited row is zero, but the full innovation is `-M(W)`, not necessarily zero;
the prime's effect is not limited to its diagonal unit.  Consult Hosted Lean CI
for the compilation status of this head.

## Previous continuation: square energy retains every high-prime transport

`PostRootMertensSquareFiniteDifference.lean` restores the square coordinate on
the existing post-root family set:

```text
Delta_sq(W) = M(W)^2 - postRootFamilyMertensSquareEnergy(W),
Delta_lin(W) = M(W) - sum_p M(floor(W/p)),
Delta_fall(W) = Delta_sq(W) - Delta_lin(W),
abs(Delta_lin(W)) <= 2W.
```

The correction uses the already-proved quotient packing.  The square and
falling positive-power propositions are equivalent, and either feeds #599's
protected Mertens-energy bootstrap.  The new layer reuses the existing Bessel
identity and proves a sharper direct comparison:

```text
Delta_sq(W) = 2 E(W) + postRootComplementDiagonalResidual(W),
0 <= postRootComplementDiagonalResidual(W) <= W.
```

The diagonal residual is identified with the literal squarefree mass outside
the disjoint seat-product union already used for packing.  Therefore a positive
#600 record at `W = N+1` forces

```text
envelope_epsilon(N) < Delta_sq(W) / (2 W^(1+epsilon)).
```

This retains every high square with its favorable sign in the record budget.
The exact reciprocal-band decomposition uses the existing prime-comb bands.
Its top-half band transports one square-energy unit per prime, with total
`pi(W) - pi(floor(W/2))`, including all small-endpoint conventions.

**The positive-power bound remains open.**  A favorable subtraction at each
fixed endpoint is not a monotonicity theorem for the moving family energy.
Also distinguish the LCM falling kernel `M^2-M` from ordinary positive-lag
covariance, whose diagonal correction is `sum mu^2`.  Consult Hosted Lean CI
for compilation status of the current head.

## Previous continuation: the remainder scale sufficient for Mertens

The linear remainder target is stronger than the bootstrap needs. The new
`PostRootCovariancePowerRemainderStatement` asks only for

```text
for every eps > 0, there is D_eps >= 0 such that
E(W) <= D_eps * W^(1+eps) for every W >= 2.
```

This is a one-sided estimate on the signed remainder; its absolute value need
not be small. In `EndpointCubeAnalyticClosure.lean`,
`mertensPositiveLagUpperBounded_of_postRootCovariancePowerRemainder` uses the
remainder estimate at `eps/2`. The existing post-root product packing bounds
the inherited covariance by `A * W^(1+eps/2)`, so both contributions can be
absorbed into `A * W^(1+eps)` after a finite onset. The new theorem
`mertensEnergyBounded_of_postRootCovariancePowerRemainder` then feeds the
protected Mertens energy criterion. The earlier linear theorem names remain
as specializations, via `postRootCovariancePowerRemainder_of_linear`.

**The arithmetic estimate remains open.** This strengthens the conditional
bootstrap by weakening its input; it does not supply a witness of either the
linear or positive-power remainder proposition. The complete-cube sign below
does not control every physical boundary contribution. Consult Hosted Lean CI
for the compilation status of this head.

## Physical LCM cubes after merged #596 and #597

The complete-LCM remainder interior is already bounded between `-W` and `W`.
The boundary identity from #597 is

```text
B_rem(W) = B(W) - sum_{sqrt(W) < p <= W} B(floor(W/p)),
2 B(W) = M(W)^2 - M(W).
```

The continuation in `PostRootCovarianceLcmBoundaryClosure.lean` retains the
physical endpoint in the #596 LCM stencil. For fresh `p` and `a <= b <= W`,
its Boolean four-corner derivative is exactly

```text
1_{W < lcm(a,b), W < p*a}
  - 1_{lcm(a,b) <= W < p*lcm(a,b), p*a <= W}.
```

Both terms matter. At `W=5`, `p=3`, `(a,b)=(2,5)`, the uncut stencil is zero
but the physical stencil is one. First-wall cancellation alone cannot bound
all physical cubes.

There is also an unconditional signed gain on the complete lower parent
carrier. For every post-root prime `p`, put `q = floor(W/p)`. The whole sum
of physical cubes based on `1 <= a < b <= q` equals `-B(q) <= 0`:

- `realMoebiusPhysicalSuperLcmFourCorner_postRoot_eq_neg_lower`;
- `sum_realMoebiusPhysicalSuperLcmFourCorner_postRoot_eq_neg_lower`;
- `sum_realMoebiusPhysicalSuperLcmFourCorner_postRoot_nonpos`.

Nonpositivity uses the integrality of `M(q)`: `M(q)*(M(q)-1) >= 0`.
This is a theorem about the complete parent-cube sum for each fixed prime.
It does not assert a disjoint global decomposition into those cubes.
The physical top escape and cubes outside that complete lower parent carrier
remain to be recombined and bounded. `PostRootCovarianceLinearRemainderStatement`
is still open. Consult Hosted Lean CI for the compilation status of this head.

## Earlier continuation: PR #593 after merged #592

The active branch is `agent/post-root-remainder-owner-carrier` in PR #593.
The older #582 normalization below remains valid background. The new work is
in `GlobalFirstJumpCriticalCorrelationBridge.lean` and
`EndpointCubeAnalyticClosure.lean`; consult the current head's Hosted Lean
result before treating a newly added declaration as compiled.

### A proposed reciprocal bound is refuted on the existing partner coordinate

`criticalReciprocalPrefix_one_eq_partnerCard` and
`criticalReciprocalPrefix_unitPartnerSet` identify the first reciprocal prefix
exactly:

```text
P_R(1) = #{q prime : R <= q <= R^2 - 1}.
```

At every prime root `R`, this is at least one. Since
`C * (log R + 1) / R -> 0`, Euclid's infinitude of primes alone contradicts
`CriticalReciprocalPrefixRootBound`. The declaration
`not_criticalReciprocalPrefixRootBound` records this obstruction.

The old implications from that premise remain logically valid, but cannot
close the endpoint bound. Do not try to prove the premise by changing the
Euler schedule or importing PNT. The exact endpoint/rough-correlation equality
does not identify a partial reciprocal prefix with the endpoint. In particular,
the unit prefix has no opposite Möbius sign with which to cancel.

### The post-root covariance remainder has an exact physical carrier

For the physical endpoint `W`, put `C(W) = sum_{1 <= m < n <= W} mu(m) mu(n)`.
The same-scale remainder is

```text
E(W) = C(W) - sum_{sqrt(W) < p <= W, p prime} C(floor(W/p)).
```

`postRootCovarianceRemainder_eq_physicalPairCarrier` identifies it with the
signed pair sum over pairs with **no common post-root prime**. The removed
families are pairwise disjoint literal finite carriers.

The remaining quantitative proposition is
`PostRootCovarianceLinearRemainderStatement`, namely `E(W) <= D * W` for one
constant `D >= 0`. The compiled conditional route is
`mertensEnergyBounded_of_postRootCovarianceLinearRemainder`. Its hypothesis is
still open; neither the pair partition nor owner promotion discharges it.

### Owner descent must retain child multiplicities

`postRootCovarianceRemainderRecursivePair_owner_descent` proves that every
nonzero recursive pair has an ordered parent on the same remainder carrier,
its owner strictly increases, its separation rank falls by one, and its weight
changes sign. Equal-parent terminal pairs have nonpositive weight.

This parent map is not injective. For any primes `p < q <= W`, the positive
pair `(p,q)` strips at `p` to `(1,q)`. At `W=60`, the sixteen primes below `59`
therefore give sixteen positive children of the one negative pair `(1,59)`.
Owner promotion alone cannot pay for all children with that single parent.

The new aggregate theorem is
`postRootCovarianceRemainder_eq_terminal_sub_parentMultiplicity`:

```text
E(W) = terminalMass(W)
       - sum_parent childMultiplicity(W,parent) * mu(parent.1) * mu(parent.2).
```

Here `terminalMass(W) <= 0`; multiplicity counts precisely the nonzero
recursive children with that ordered parent. No triangle inequality or
support estimate is used. This identity makes the outstanding signed
multiplicity estimate explicit. Replacing those multiplicities by one is not
a valid cancellation argument.

## Earlier main baseline: physical normalization

PR #582 merged into `main` at:

`6b038f934a49b2e86a3c7e305fbffb78c4150ed2`

Its central result is the exact physical normalization of the vertical-line carrier and the elimination of `mask instability` as an independent population.

## One object, several compiled representations

The following are exact compiled bridges.

### Vertical endpoint = oriented Euler endpoint

File: `RHLean/Proof/ComplexVerticalIntervalEulerBridge.lean`

```lean
theorem signedVerticalIntervalEndpointMass_eq_orientedEulerLedger
    (R : ℕ) :
    signedVerticalIntervalEndpointMass R =
      lowWheelCanonicalDowncrossOrientedLedger R
```

### Vertical endpoint = canonical defect endpoint

The same file now proves:

```lean
theorem signedVerticalIntervalEndpointMass_eq_canonicalDefectLedger
    (R : ℕ) :
    signedVerticalIntervalEndpointMass R =
      lowWheelCanonicalDefectLedger R
```

This passes through exact late-parent cancellation and the exact defect/downcross identification.

Therefore the run increment satisfies:

```lean
theorem signedVerticalIntervalMass_eq_canonicalDefectDifference
    (a b : ℕ) :
    signedVerticalIntervalMass a b =
      lowWheelCanonicalDefectLedger (b + 1) -
        lowWheelCanonicalDefectLedger a
```

### Vertical run = oriented run = signed lifetime residual

Also in `ComplexVerticalIntervalEulerBridge.lean`:

```lean
theorem signedVerticalIntervalMass_eq_orientedEulerLedger
    (a b : ℕ) :
    signedVerticalIntervalMass a b =
      canonicalOrientedRunDifference a b
```

and

```lean
theorem signedVerticalIntervalMass_eq_signedPrefixLifetimeResidual
    (a b : ℕ) :
    signedVerticalIntervalMass a b = signedPrefixLifetimeResidual a b
```

The complex/Fermat coordinate, the ordered Euler coordinate, the oriented/downcross coordinate, the lifetime coordinate, and the canonical defect coordinate are therefore not separate analytic problems.

### Largest-prime stable defect = the terminal seam itself

File: `RHLean/Proof/LowWheelLargestDefectSeamEquivalence.lean`

`LowWheelLeastLargestStableTransfer` already proves
`lowWheelCanonicalDowncrossLedger R = lowWheelLargestDefectLedger R`. That is an
identity of the *same* signed object, so the largest-prime stable defect is not
a smaller remaining piece. Compiled explicitly:

```lean
theorem squareRootLargestDefectLinear_iff_canonicalDowncrossLinear :
    SquareRootLargestDefectLinearBound ↔ SquareRootCanonicalDowncrossLinearBound

theorem riemannHypothesis_of_largestDefectLinear
    (h : SquareRootLargestDefectLinearBound) : RiemannHypothesis
```

Anything proving the largest-prime defect bound proves RH; by adversarial check
5 it is the hard theorem, not an auxiliary step. Two practical consequences:

- the *signed* target is RH-strength, so exhibiting the defect's surviving
  pieces inside already-root-bounded endpoint populations does not close it
  unless those pieces carry their signs and their mutual cancellation;
- the *cardinality* target is dead by a full power of `R`. Direct enumeration of
  `lowWheelLargestDefectPart` gives `|defect|/R` rising `18.6, 22.7, ..., 140.1`
  over `R = 8..30` (order `R^2`), while the signed mass over the same range
  stays in `[-7, 9]`. Numerical observation, recorded only to stop the
  cardinality route being re-attempted.

### Downcross ledger after the frozen top/bottom subtraction

File: `RHLean/Proof/LowWheelFrozenCofactorTopBottomCancellation.lean`

`LowWheelFrozenCofactorTopBottomToggle` supplies, pointwise, the sign-reversing
move `(t,(c,p)) -> (t,(c/q, q*p))` with `q = P+(c)` on frozen repeated-parent
states with `c > 1`. That move is injective on the frozen nontrivial-cofactor
sector, with an explicit inverse (the image pivot recovers `p`, the image
quotient over that pivot recovers `q`). Hence the exact identity

```lean
theorem lowWheelFrozenCofactorTopImageLedger_eq_neg
    (R : ℕ) :
    lowWheelFrozenCofactorTopImageLedger R =
      -lowWheelCanonicalFrozenCofactorLedger R
```

and, composed with the compiled late-parent cancellation,

```lean
theorem lowWheelCanonicalDowncrossLedger_eq_unique_add_terminal_sub_topImage
    (R : ℕ) :
    lowWheelCanonicalDowncrossLedger R =
      lowWheelCanonicalDowncrossUniqueParentLedger R +
        lowWheelCanonicalTerminalBoundaryLedger R -
          lowWheelFrozenCofactorTopImageLedger R
```

The relocation is not internal bookkeeping: the image is disjoint from the
whole canonical downcross carrier, because every image state has normalized
root-side parent strictly above `R` while every downcross state has parent at
most `R`, and the image still lies on the physical transport carrier. So the
frozen `c > 1` sector has been moved to the post-root side of the same physical
carrier, leaving on the downcross side only the unique-parent ledger and the
literal terminal `c = 1` monotone first-crossing boundary.

The quantitative seam is restated as `SquareRootFrozenTopBottomLinearBound`,
and `riemannHypothesis_of_frozenTopBottomLinear` discharges RH from it through
the existing square-prefix energy bridge.

This moves signed mass; it does not bound it. No norm, estimate, or density
input is used in that file, and nothing is claimed about the size of any of the
three surviving terms. The power exponent is unchanged.

## Exact active-child normal form

File: `RHLean/Proof/ComplexVerticalLineSquarefreeDiagonal.lean`

For every `R >= 2`:

```lean
theorem orderedEulerCutActiveChildren_eq_squarefreeShell
    (R : ℕ) (hR : 2 ≤ R) :
    orderedEulerCutActiveChildren R = orderedEulerCutSquarefreeShell R
```

where

```lean
def orderedEulerCutSquarefreeShell (R : ℕ) : Finset ℕ :=
  (Finset.Ioo R (R ^ 2)).filter Squarefree
```

Hence the physical endpoint carrier is exactly

`{ n : Squarefree n ∧ R < n ∧ n < R^2 }`.

The converse realization is constructive: recursively strip the canonical largest prime until the remaining high cofactor fits below `R`, preserving the ordered Euler-cut conditions.

## Fresh-prime endpoint transitions are only two physical walls

For fresh prime `p` and squarefree `n`:

```lean
theorem orderedEulerCutPrime_inactive_to_active_iff_birth ...
```

identifies inactive -> active with the lower-root crossing

`n <= R < p*n < R^2`.

```lean
theorem orderedEulerCutPrime_active_to_inactive_iff_topEscape ...
```

identifies active -> inactive with the upper-square crossing

`R < n < R^2 <= p*n`.

The combined theorem is:

```lean
theorem orderedEulerCutPrime_membership_unstable_iff_birth_or_topEscape ...
```

Thus fresh-prime membership instability is exactly

`birth ∨ topEscape`.

The #581 line-event mask therefore has no extra mysterious instability population:

```lean
theorem signedVerticalLineEventMask_prime_unstable_imp_birth_or_topEscape ...
```

Any mask failure is owned by one of those two physical walls at endpoint `a` or endpoint `b+1`.

## Green--Kubo coordinate on the same run

File: `RHLean/Proof/ComplexVerticalLineGreenKubo.lean`

The event process is the endpoint charge difference on one physical child line.

The exact factorization is:

```lean
theorem signedVerticalLineEventStep_eq_moebius_mul_mask ...
```

so

`event(n) = mu(n) * chi(n)`.

The run covariance is exactly a masked Möbius pair sum, not a probabilistic covariance assumption.

The exact energy identity is:

```lean
theorem norm_signedVerticalIntervalMass_sq_eq_lineDiagonal_add_two_mul_covariance ...
```

which is the finite Green--Kubo identity

`||V||^2 = D_line + 2 C_line`.

### Stable fresh-prime families descend exactly

The same module proves that the four-corner fresh-prime cube factors through the mixed mask/order cell, that swapped stable cells leave only the standard top escape, and that a completely stable prime family has exactly the lower-prefix covariance:

```lean
theorem signedVerticalLinePrimeFamilyCovariance_eq_lower ...
```

Hence prime-stable covariance is recursive rather than new. Failure of the descent is now known, by #582, to be only birth/top-escape wall crossing.

## Exact diagonal information

File: `RHLean/Proof/ComplexVerticalLineSquarefreeDiagonal.lean`

Pointwise:

```lean
theorem signedVerticalLineEventStep_sq_le_moebius_sq ...
```

so the event diagonal is bounded by the exact Mertens squarefree diagonal.

The repository also contains an elementary finite zero-density theorem using the prime squares `4,9,25,49,121`:

```lean
theorem realMertensZeroCount_ge_three_eighths_sub_five (x : ℕ) :
    (3 / 8 : ℝ) * (x : ℝ) - 5 ≤
      (realMertensZeroCount x : ℝ)
```

which yields the compiled finite Green--Kubo bound

```lean
theorem norm_signedVerticalIntervalMass_sq_le_five_eighths_endpoint_add_covariance ...
```

schematically

`||V||^2 <= (5/8) X + 5 + 2 max(0,C_line)`.

This is useful diagonal sharpening but does not solve the signed covariance problem.

## Existing reciprocal Euler contraction

File: `RHLean/Proof/CanonicalRoughReciprocalCompression.lean`

The canonical rough covariance coordinate already has the exact fresh-prime contraction:

```lean
theorem squareRootCanonicalRoughResponseCenteredReciprocalSummand_add_mul_freshPrime ...
```

schematically

`v_R(c) + v_R(c*p)`

`= (1 - 1/p) * v_R(c)`

`  + mu(c)/(c*p) * (threshold + topEscape - birth)`.

No norm or independence assumption is used. The file also contains aggregate carrier-level compression and accumulated multi-prime Euler-factor identities.

The underlying complete signed reciprocal cube has the exact factor

`1 - 1/p`

when a fresh prime is inserted; see `RHLean/Arithmetic/PrimorialReciprocalMobiusFactorization.lean`.

## Complete sub-root wheel removes threshold loss

File: `RHLean/Proof/CanonicalRoughCompleteSubrootDefectReduction.lean`

If the complete prime wheel through `p` remains strictly below `R`, then the threshold-loss channel is exactly empty:

```lean
theorem squareRootCanonicalRoughFreshThresholdLossBoundary_eq_empty_of_completeWheel ...
```

Top escapes are forced to partners strictly above the root, while births remain on the lower side.

The intact signed boundary becomes exactly:

`post-root top escape - lower-root birth`.

The scaled reciprocal defect theorem is:

```lean
theorem natCast_mul_squareRootCanonicalRoughFreshPrimeReciprocalPhysicalDefect_eq_topEscape_sub_birth_of_completeWheel ...
```

This is the strongest existing candidate mechanism to combine with the newly normalized vertical/defect carrier.

## Current open terminal energy proposition

File: `RHLean/Proof/ComplexVerticalIntervalEulerBridge.lean`

```lean
def SignedVerticalIntervalEnergyBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a b : ℕ, 3 ≤ a → a ≤ b →
        (b + 1) ^ 2 < 2 * a ^ 2 →
        ‖signedVerticalIntervalMass a b‖ ^ 2 ≤
          C * Real.rpow ((((b + 1) ^ 2 : ℕ) : ℝ)) (1 + ε)
```

The file proves this is equivalent to the pre-existing canonical oriented-run energy statement. It is not a new analytic seam.

A sufficient direct covariance target on strict subdoubling runs is of the form

`max 0 (signedVerticalLineRunCovariance a b)`

`<= C_eps * a^(2+2*eps)`.

The exact exponent/interface should be chosen so the result composes directly with the existing energy theorem rather than introducing another nearly-equivalent proposition.

## Preferred next attack

Do not estimate `mask instability` as a new set. It has already been identified with the physical walls.

The immediate research question is:

**Can the exact reciprocal Euler contraction `1 - 1/p` be transported onto the now-identified vertical/canonical-defect increment while retaining birth/top-escape as a signed physical defect, so that the positive Green--Kubo covariance obeys a genuinely contractive recursion?**

A desirable structural theorem would have the shape

`C_current = contracted lower-prefix covariance + signed boundary defect`,

where:

- every stable prime family is reindexed to a strictly lower prefix;
- the contraction coefficient comes from an exact Euler factor, not an assumed density;
- every failure of descent is explicitly a birth or top-escape wall crossing;
- no triangle inequality is applied until all cross-family signed cancellation has been exposed.

If this exact recursion exists, iterate it before estimating the remaining boundary.

## Required adversarial checks

Any candidate closure must survive all of the following.

1. **Support-only no-go.** The repository records that support-only frontier/capacity control is a full power too weak. A proof that ultimately bounds the critical signed defect only by its cardinality is not the missing argument.

2. **Top-escape no-go.** `RHLean/Analysis/SquareRunTopEscapeClassification.lean` proves that on strict subdoubling runs the natural same-prime nonpositive leaf can be empty and its associated top escape can equal the whole square-run covariance. Therefore `top escape is thin` is not by itself a gain.

3. **No selected-carrier sign balance.** Global asymptotic `40/30/30` Möbius density cannot be transferred to the birth/death/escape carrier without proof. The safe use of squarefree density is the diagonal bound already compiled.

4. **No coordinate-change miracle.** Exact equality among coordinates removes duplicate seams but supplies no quantitative cancellation by itself.

5. **No hidden RH-strength input.** If an intermediate lemma would itself imply the terminal square-run energy estimate by a trivial bridge, recognize it as the hard theorem rather than presenting it as an elementary auxiliary fact.

6. **Frozen-image/high-prime no-go.** `RHLean/Proof/LowWheelFrozenCofactorTopImageHighPrimeObstruction.lean` closes the natural attempt to absorb the post-root image `T_R` into the already-controlled external high-prime population. Every high-prime population here is indexed by a prime strictly above the root (`squareRootHighPrimeCofactorSet R c` filters `Finset.Ioc R (squareRootEndpoint R)`; `lowWheelCanonicalRepeatedExternalTerminalPart` filters on `R < pivot`). The image carries no such prime: writing `y = (t,(c,p))` frozen with `c > 1` and `q = P+(c)`, the image is `(t,(c/q, q*p))` with `p < q <= c < R`, so both its primes lie strictly below the root. Compiled consequences:

   - `lowWheelFrozenCofactorTopImage_quotient_primes_lt_root` — no prime factor of an image quotient reaches `R`;
   - `lowWheelFrozenCofactorTopImage_subset_repeatedExternalTerminal_iff` — the containment holds *only* when the frozen nontrivial-cofactor sector is empty, i.e. exactly when there is nothing to absorb.

   Independently of containment, `norm_lowWheelFrozenCofactorTopImageLedger_eq` gives `‖T_R‖ = ‖F_R^{c>1}‖`. The relocation is a sign-reversing bijection, so it is norm-preserving: bounding `T_R` *is* bounding the frozen `c > 1` sector. No reindexing of that sector can produce its own bound; the bound must come from new information about the sector. This is item 4 above in concrete form.

## Numerical research lane

Before investing heavily in Lean formalization, candidate exact recursions may be tested on finite ranges. This is especially cheap after the squarefree-shell normalization:

`A_R = {n : Squarefree n ∧ R < n ∧ n < R^2}`.

For a proposed identity:

- test exact equality over many roots and fresh primes;
- isolate each discrepancy by lower wall, upper square wall, stable family, and cross-family term;
- search for the smallest counterexample immediately;
- never promote numerical agreement to proof.

For a proposed inequality, search for worst-case ratios and sign configurations before formalization.

## Lean completion standard

A result counts as closed only if:

- the exact intended theorem compiles;
- no `sorry`, `admit`, new `axiom`, or equivalent placeholder is introduced;
- the repository's owned-warning gate passes;
- source/assumption/root-manifest audits pass;
- public export verification remains green where applicable;
- the terminal axiom audit is unchanged.

The terminal forward theorem is guarded in `RHLean/Proof/TerminalAxiomAudit.lean` by `#print axioms`; preserve its existing standard classical axiom footprint.

## Operational workflow

1. Read `AGENTS.md` and this file.
2. Inspect the exact theorem definitions in the cited modules rather than relying on prose summaries.
3. Search the repository before introducing a new abstraction.
4. Derive the strongest exact identity first.
5. Falsify it numerically if useful.
6. Formalize on a branch.
7. Run the relevant Lean build and audits.
8. Only after a structural theorem is kernel-checked should a quantitative estimate be attempted on the reduced signed defect.

The present goal is not another representation. It is a sign-preserving Euler contraction of the one already-identified boundary process.
