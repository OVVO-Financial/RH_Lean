# RH_Lean current proof contract

Status date: 2026-10-01. The direct VF-mid route is the canonical proof program.
Compiled Lean source and successful checks of the relevant commit are
authoritative. Historical handoffs, attractive finite plots, and stronger
sufficient criteria do not override this contract.

## Motto and guiding light

> **Close RH through VF.  Preserve the RH-scale target; do not replace it with
> a stronger block-by-block statement merely because that stronger statement
> fits finite data.**

The VF construction can remain an excellent RH-scale approximation to the
prime-counting staircase even though no fixed vertical alignment intersects
that staircase in every square block forever.  Those are different claims.

The canonical arithmetic target is therefore the cumulative square-endpoint
bound

```text
exists C >= 0, for every natural R >= 2,
  |pi(R^2) - VF_mid(R^2)| <= C R log R.
```

In Lean this is

`VFMidSquareEndpointVonKochBoundedStatement`

from
[`VF_MID_VON_KOCH_BRIDGE.lean`](research/VF_MID_VON_KOCH_BRIDGE.lean).

The already-compiled bridge
`vfMidVonKochBounded_of_squareEndpoint` extends that estimate to every real
cutoff `x >= 4`; `primeLiVonKochBounded_of_vfMidSquareEndpoint` combines it
with the unconditional VF/Li quadrature estimate; and
`riemannHypothesis_of_vfMidSquareEndpoint` feeds it into the repository's
explicit classical von-Koch/RH criterion.

The remaining work is therefore arithmetic control of the cumulative signed
VF error itself.  Write

```text
D_R = pi(R^2) - vfMidFinishedMass R
P_R = pi((R+1)^2) - pi(R^2)
m_R = vfMidBandMass R.
```

Then the exact recurrence is

```text
D_(R+1) = D_R + (P_R - m_R).
```

The square-wheel/FTA modules identify `P_R` exactly as the survivors of the
common finite prime wheel for that square block.  Thus the central research
question is signed cumulative control of

```text
sum_{r<R} (P_r - m_r),
```

at the `R log R` scale.  Local prime/composite dispersion, finite wheel
exactness, least-prime ownership, and square-root dependency are useful only
insofar as they help prove this cumulative estimate without introducing a
stronger false premise.


## Canonical closure route: structural admissibility, not realized cancellation

The final direct-VF closure is now stated as an admissible-class theorem rather
than as a request for a separate global cancellation estimate for the realized
prime sequence.

The class is formalized in
[`VF_MID_OWNER_ADMISSIBLE_ESCAPE_CLASS.lean`](research/VF_MID_OWNER_ADMISSIBLE_ESCAPE_CLASS.lean)
as

`VFMidOwnerEscapeAdmissible D`.

Its defining law is deliberately structural:

- finitely many base scales are not channel-threatening;
- every channel-threatening bad scale reproduces on an actual strict recursive
  VF child scale.

It does **not** assume `|D_R| <= K R log R`, a covariance estimate, a
prime-error cancellation rate, or membership in the solved fantasy cone.

The adversarial fuzzer already proves that exact recurrence, perfect midpoint
balance, and the quadratic energy identity are insufficient: an explicit
synthetic defect satisfies them and still escapes every radial channel. The
same file proves that strict-child reproduction kills every escaping trajectory
by strong induction.

The honest-prime obligation is therefore named explicitly:

`VFMidActualPrimeOwnerEscapeAdmissibleStatement`.

Once it is proved, the compiled theorem

`vfMidSquareEndpointVonKochBounded_of_actualPrimeOwnerEscapeAdmissible`

closes `VFMidSquareEndpointVonKochBoundedStatement` immediately.

The intended proof of actual-prime admissibility must use the exact arithmetic
mechanics already present in the repository: the VF-native seat carrier, exact
affine/Mobius decoder, first-separation owner, critical owner trichotomy,
strict continuation to a smaller state, and clipped outgoing contraction.
Those mechanisms may contain exact sign cancellation internally; no separate
long-range statement that the realized prime errors "cancel enough" is an
admissibility hypothesis.

Accordingly, `ActualPrimeContainedInSolvedFantasyConeStatement` is retained
as a valid metric sufficient condition and visualization, but it is **not** the
canonical remaining arithmetic obligation. Proving that cone membership
directly would be essentially the target bound in different coordinates.

## Fixed-alignment step-graph criterion: conditional only

PR #842 formalizes a useful sufficient implication for a fixed additive phase

```text
c0 = 4 - vfMidFinishedMass 3.
```

The corresponding statement is now named

`VFMidInitialAnchorAlignedStepGraphBracketingStatement`.

If that full step graph intersected the prime staircase in every square block,
the compiled theorem

`vfMidSquareEndpointVonKochBounded_of_initialAnchorAlignedStepGraph`

would imply the canonical square-endpoint VF bound.

However, universal fixed-phase block-by-block intersection is **not** the final
target and should not be pursued as such.  The reason is structural: because
the midpoint VF construction lies on the lower side of the corresponding Li
integral up to a fixed normalization, universal one-block crossing would force
a one-sided upper bound of order `sqrt(x)/log(x)` on `pi(x)-Li(x)`.
Classical Littlewood oscillation gives positive excursions larger than every
fixed multiple of that scale by an additional unbounded
`log log log x` factor.  Hence a fixed alignment must eventually miss some
blocks, even if it succeeds over every computationally accessible range.

This does **not** refute VF.  The legitimate RH-scale target allows

```text
|pi(R^2) - VF_mid(R^2)| = O(R log R),
```

which is vastly larger than one local block height
`m_R ~ R/log R`.  A fixed alignment can therefore fail block intersection
while VF still satisfies exactly the estimate needed for RH.

Finite aligned-intersection experiments remain valuable diagnostics of local
geometry.  They are never evidence that the universal fixed-phase statement
should replace the cumulative VF target.

## Research discipline for the VF route

1. **Keep the exact VF object.**  Do not rescale the midpoint construction to
   force a visual crossing phenomenon.
2. **Exploit FTA/square-wheel exactness.**  Prime supply in block `R` is the
   exact survivor count after sieving by the required prefix primes.
3. **Separate spatial dispersion from total supply.**  Left/right
   equidistribution controls placement inside a block; it does not by itself
   control `P_R-m_R`.
4. **Control signed accumulation.**  The target is the partial sum of
   `P_R-m_R`, not an unsigned per-block envelope and not perpetual
   block-by-block capture.
5. **Respect the target scale.**  Stronger-than-RH statements may be useful as
   diagnostics or conditional lemmas, but they are not proof obligations.
6. **Finite computation is diagnostic only.**  Numerical persistence, however
   striking, cannot replace a uniform all-scale theorem.

## Preserved alternative: CORR-4

**The CORR-4 quantitative estimate remains open.** The forward
Mertens-to-RH implication, signed reassembly, and conditional terminal induction
are available. Repeating the existing coordinate changes does not supply the
missing estimate. The pause on repeating tested internal identity searches is
a research policy, not a theorem that the reduced estimates are unprovable.
Coefficient-transfer improvements and new quantitative arguments must be
assessed on their mathematical content.

## Governing rule

**Signed physical reassembly first. Energy second.**

Preserve parent/current-response/first-power-mate compensation, earlier-owner
transfer, second-contact transport, and endpoint terms before squaring. The
energy of a complete signed Mertens packet is different from the sum of squares
of unsummed coefficients.

## Exact target and conventions

Write `M(y) = sum_{1 <= n <= y} mu(n)`, with `M(0) = 0`. For `R >= 56`:

| Symbol | Definition / Lean object |
| --- | --- |
| `X` | `R² − 1`, `squareRootEndpoint R` |
| `G_R` | `M(X) − M(R − 1)`, `lowOwnerPost789EndpointGapReal R` |
| `corr_R` | `−G_R`, `squareRootCanonicalRoughCorrelation R` |
| `E_R` | `sum_{q odd prime, q² < R} M(floor(X/q²))²`, `canonicalRoughLowQ2DaughterEnergy R` |
| `K` | `LowerMertensCriticalEnvelope R K`: `0 <= K` and `(M(y) − 1)² <= K (y + 1)` for every natural `y < R` |
| `Q_R` | `sum_{q odd prime, q² < R} M(floor(X/q²))/q`, `lowOwnerReciprocalMertensColumnReal R` |
| `D_R` | The nonnegative physical Möbius diagonal, `lowOwnerZeroFrequencyMobiusDiagonal R` |
| `S_R` | `G_R² + 2 Q_R G_R − D_R`, `lowOwnerPost789SignedCrossDiagonalRemainder R` |

Here `X` is always an endpoint; `S_R` names the remainder. Some historical
notes use `X_R` for both, so read their Lean definitions to disambiguate.
The envelope implies `K >= 1` by taking `y = 0`.

The sufficient CORR-4 target is

```text
exists C >= 0, for every R >= 56 and every K,
  LowerMertensCriticalEnvelope R K ->
  G_R² <= 4 E_R + C R² K.
```

The constant is independent of `R` and `K`. The estimate is not proved.

[`CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean`](research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean)
defines the low-owner energy and bounds the nonrecursive `q² >= R` tail by
`3 R² K`. Thus existence of the fixed-coefficient low-owner bound is equivalent
to existence of the full odd-owner bound, with only the boundary constant
changed. [`CORRELATION_FOUR_TERMINAL_BRIDGE.lean`](research/CORRELATION_FOUR_TERMINAL_BRIDGE.lean)
proves `correlationFour_iff_exists_lowQ2Energy` and
`riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy`. Its resulting
coefficient `10201/2500` passes the compiled terminal budget. No further
bookkeeping assumption or new induction theorem is needed by that consumer.

## Signed normal forms and sufficient coefficients

The compiled quarter frame and diagonal bounds give

```text
Q_R² <= E_R/4,                    0 <= D_R <= 3 R²,
FinalStokes_R = Q_R² + S_R,
TopTwoClip_R = Q_R² + S_R − Terminal_R.
```

The terminal term stays separate; it does not replace `S_R`. The [completed
branch assembly](research/GLOBAL_RETURNED_CORE_TOP_TWO_COMPLETED_BRANCH_ASSEMBLY.lean)
and [branch-gate composition](research/GLOBAL_RETURNED_CORE_TOP_TWO_BRANCH_GATE_COMPOSITION.lean)
prove these identities. At first owner `2`, the completed top-branch energy
is `(Q_R + G_R)²`, so completing the branch has not removed the endpoint gap.

The [sharpened correlation comparison](research/GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE.lean)
uses a three-quarter square completion. With `C >= 0` and exactly the same
uniform lower-envelope quantifiers, the sufficient endpoint coefficients are:

| Sufficient input | Endpoint coefficient | Sharpened transfer to CORR |
| --- | --- | --- |
| `FinalStokes_R <= B E_R + C R² K` | `B = 9/4` | `4B/3 + 1 = 4` |
| `S_R <= A E_R + C R² K` | `A = 2` | `4(A+1)/3 = 4` |

In either case the low-owner CORR boundary constant becomes `4C/3 + 4`.
Any smaller coefficient also suffices by `E_R >= 0`. These are sufficient
thresholds for the displayed comparisons, not a claim that no other method
could allow larger coefficients. The old `B <= 7/4` and `A <= 3/2` consumers
in the [post-789 control module](research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean)
remain valid and unchanged; they are not the strongest sufficient targets now
available. Historical snapshots that quote them should be read accordingly.

The exact certificates, writing `F = FinalStokes_R`, are

```text
S_R − (3G_R²/4 − E_R − 3R²)
  = (G_R + 4Q_R)²/4 + (E_R − 4Q_R²) + (3R² − D_R),
4F − 3G_R² + 3E_R + 4D_R
  = (G_R + 4Q_R)² + 3(E_R − 4Q_R²).
```

All terms on the right are nonnegative. Consequently

```text
3G_R²/4 − E_R − 3R² <= S_R,
3G_R²/4 − 3E_R/4 − 3R² <= FinalStokes_R.
```

The comparison module contains both polynomial certificates, both lower
comparisons, both general coefficient transfers, and conditional CORR-4/RH
consumers at `A = 2` and `B = 9/4`. The uniform upper bounds are still explicit
hypotheses. Relevant hosted Lean checks at the PR head certify elaboration;
symbolic checks alone are not Lean certification. See the
[research-state note](research/POST789_SHARPENED_COEFFICIENT_CORRIDOR.md)
for the derivation, exact quantifiers, and two-sided research interpretation.

Full quarter cancellation is stronger than required. The original comparison
also proves

```text
G_R²/2 − E_R/2 − 3 R² <= S_R,
S_R <= (1+a) G_R² + b E_R       (a > 0, 4ab = 1).
```

Existence of some remainder bound is equivalent to existence of some CORR-low
bound. This statement does not preserve an arbitrary fixed coefficient and
does not say that every finite coefficient closes RH. The displayed consumer
thresholds must still be met.

## What the latest work does and does not prove

- **Prefix-tail mixed remainder (2026-09-29):** the far-tail/mixed cell
  mass left after the reciprocal prefix is
  [exactly](research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean)
  `2·Mixed_R = S_R + D_P` with `0 <= D_P <= 3 R²`. A mixed bound with
  coefficient `B` is therefore an `S_R` bound with the same `B`. Coefficient
  `2` already closes the consumer, and the remainder is not a narrower seam
  than `S_R`.
- **Owner-two clipped exit (2026-09-29):** at first owner `2` there is a
  single compensated cell, and
  [its exact evaluation](research/GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean)
  gives clipped exit `= M(X_R)` and compensated interior `= Q_R − M(R−1)`.
  The interior satisfies `I² <= 4 E_R + 8 R² K` unconditionally, and
  `SquareEndpointRoundedOddQ2EnergyStep C` is literally a bound on the
  clipped-exit square. A
  [companion module](research/SQUARE_ENDPOINT_STEP_POLYLOG_STRENGTH.lean)
  proves that the step forces `(M(x)−1)² <= B^j (x+1)` for `x < 2^(2^j)`, a
  polylogarithmic Mertens envelope. See the
  [audit note](research/OWNER_TWO_CLIPPED_EXIT_AUDIT.md). Neither module
  proves the step.
- **Coefficient sharpening (2026-09-27):** the same exact signed carrier and
  quarter frame admit `A = 2` or `B = 9/4`, rather than only `3/2` or `7/4`.
  This improves the sufficient coefficient budget. It does not prove the
  required uniform arithmetic upper estimate or a converse from RH.
- **#797:** the top-two clip retains the whole signed cell below the top two
  owners. A top-two estimate forces a bound on the endpoint gap. Discarding
  the branch slack loses the cancellation one needs to estimate.
- **Unconditional finite baseline (2026-09-27):** the same
  [global-bound module](research/GLOBAL_RETURNED_CORE_POST789_UNCONDITIONAL_GLOBAL_BOUND.lean)
  now kernel-proves the elementary all-scale estimate
  `S_R <= E_R/4 + 8 R^4` for every `R >= 56`.  This uses only
  `|M(n)| <= n`, the exact correlation dictionary, and the compiled Young
  comparison.  It is the first explicit polynomial rung in the tightening
  ladder; it is not yet a bound of the target form `A E_R + C R^2 K` because
  the quartic surplus cannot be absorbed by a fixed root-scale constant.
- **#798:** the stronger asymptotic unconditional bound gives
  `S_R <= E_R/4 + 4 B(X)² + 4 B(R−1)²`, with
  `B(x) = C x exp(−c (log x)^(1/10))`. Its leading envelope is of order
  `R⁴ exp(−c' (log R)^(1/10))`, still above the required `R² K` scale.
- **#799:** [Möbius inversion](research/MOBIUS_INVERSION_GLOBAL_CANCELLATION.lean)
  proves `sum_{d<=X} M(floor(X/d)) = 1` for `X >= 1`, and
  `bornSmooth + farSurvivor = M(X) + E_root` with an explicit root strip.
  The root strip uses lower arguments; that fact alone is not a bound on its
  aggregate size. The top Mertens value remains.
- **#800:** the [K₂ closeout](research/K2_COHERENT_MODE_KILL_GATE.md) separates
  the compiled summatory/PNT comparison from a classical Dirichlet-series
  calculation and a finite regression. Its corrected signed series is
  `2 (zeta'/zeta)² − zeta''/zeta`, retaining double poles at zeta zeros.

Finite examples can falsify a proposed identity or reproduce these exact
relations. A negative remainder on all tested roots, or strong cancellation
between large terms, cannot certify a constant uniform over all roots.
A finite certificate plus a proved all-scale induction can certify such a
bound; a finite list of successful evaluations alone cannot.

Failure of one sufficient bound is not a disproof of RH. A reverse implication
must first be proved for that same statement and its exact quantifiers.
Neither the source audits nor the research pause establish impossibility of
proving the remaining estimates.

## Existing forward analytic bridge

[`MertensEnergyRHForward.lean`](RHLean/Analysis/MertensEnergyRHForward.lean)
proves `riemannHypothesis_of_mertensEnergy` from
`MertensEnergyBoundedStatement`. The latter is the all-epsilon bound
`|M(x)|² <= C_epsilon (x+1)^(1+epsilon)`.
[`TerminalMertensForward.lean`](RHLean/Proof/TerminalMertensForward.lean)
constructs `mertensForwardCriterion` and the square-prefix-to-RH implication.
These forward consumers do not take `ClassicalMertensRHCriterion` as an
external argument. Historical equivalences still do; the reverse implication
is not needed for the present proof route. An implication from an unproved
energy estimate is not a proof of RH.

## Regression constraints retained from earlier contracts

1. A periodic contact mask is not a periodic physical Möbius field.
2. [Coefficient energy is not recursive Mertens energy](RHLean/Proof/ExceptionalContactFrameEnergyNoGo.lean):
   at daughter cutoff two, Mertens energy vanishes while coefficient mass is
   positive. Sum with signs first.
3. [Selected prime-11 tensors are not the true Möbius tensor](RHLean/Analysis/PhysicalRecoveredPrimeTensorCompatibility.lean).
   The abstract `19/23` factor cannot be substituted without the physical
   compatibility theorem that the executable counterexamples rule out.
4. [Go daughters require high transport](RHLean/Proof/TwoWheelQ2GoCompatibility.lean):
   `M(X/q²) = Go_q(X) − highTransport_q(X)`.
5. [Whole physical daughters are already reassembled](RHLean/Proof/PhysicalQ2BookkeepingSynthesis.lean):
   `physicalReassembledQ2Daughter K q = M(4K/q²)` for odd prime owners.
   Prime `2` belongs to the base mod-four geometry, not the odd contact schedule.
6. A bounded endpoint may be used only after an exact theorem attaches it to
   the same parent decomposition. No replacement by a similarly named object.
7. Support counts, coefficient norms, positive ownerwise energy, the prime-11
   budget, and a coordinate change do not supply the open signed estimate.
8. [The compensated interior is not the seam](research/GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean):
   at owner `2` the clipped exit is exactly `M(X_R)`. A bound on the
   reassembled interior is already unconditional and cannot close CORR-4.

## Preservation and success conditions

Preserve all obstruction modules, exact reassembly theorems, root/export
manifests, declaration-graph checks, owned-warning gates, and terminal axiom
checks. Do not add unfinished proofs, new analytic axioms, independence
assumptions, or a renamed RH-strength hypothesis.

A new route must identify the quantitative ingredient, its exact carrier and
quantifiers, and the compiled consumer it meets. Success means proving a
sufficient uniform estimate and composing it with that consumer without a new
open premise. The present coefficient sharpening makes no such closure claim.
