# Current RH_Lean research handoff

This file records the current mathematical frontier for any research agent continuing the repository. It is intentionally model-agnostic.

## Governing rule

Do not search for a new coordinate system first. The recent formalization has proved that several historically separate descriptions are exact representations of the same signed endpoint/run object. The task is now to exploit the strongest theorem available in each representation on that common carrier.

Keep the proof elementary and Eulerian. The genuine arithmetic operation is adjoining a fresh prime.

## Current continuation: the record step is the carrier

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
