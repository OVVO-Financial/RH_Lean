# RH_Lean current proof contract

Status date: 2026-09-26. This contract incorporates the #796–#800 closeout.
Compiled Lean source and successful checks of the relevant commit are
authoritative. Historical handoffs and plans do not override this contract.

**RH is not proved. One quantitative top-scale estimate remains.** The forward
Mertens-to-RH implication, signed reassembly, and conditional terminal induction
are available. Repeating the existing coordinate changes does not supply the
missing estimate. Searches among the tested internal identity families are
frozen pending a new quantitative ingredient.

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

The [post-789 consumer](research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean)
accepts either uniform estimate below, with `C >= 0` and the same envelope
quantifiers:

| Sufficient input | Allowed coefficient | Compiled transfer |
| --- | --- | --- |
| `FinalStokes_R <= B E_R + C R² K` | `−1/4 <= B <= 7/4` | CORR coefficient `1/2 + 2B <= 4` |
| `S_R <= A E_R + C R² K` | `−1/4 <= A <= 3/2` | CORR coefficient `2A + 1 <= 4` |

Full quarter cancellation is stronger than required. Conversely, the
[correlation comparison](research/GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE.lean)
proves

```text
G_R²/2 − E_R/2 − 3 R² <= S_R,
S_R <= (1+a) G_R² + b E_R       (a > 0, 4ab = 1).
```

Existence of some remainder bound is equivalent to existence of some CORR-low
bound. This statement does not preserve an arbitrary fixed coefficient and
does not say that every finite coefficient closes RH. The displayed consumer
thresholds must still be met.

## What the latest work does and does not prove

- **#797:** the top-two clip retains the whole signed cell below the top two
  owners. A top-two estimate forces a bound on the endpoint gap. Discarding
  the branch slack loses the cancellation one needs to estimate.
- **#798:** the remainder is the top CORR square in another coordinate. The
  [unconditional global bound](research/GLOBAL_RETURNED_CORE_POST789_UNCONDITIONAL_GLOBAL_BOUND.lean)
  gives `S_R <= E_R/4 + 4 B(X)² + 4 B(R−1)²`, with
  `B(x) = C x exp(−c (log x)^(1/10))`. Its leading envelope is of order
  `R⁴ exp(−c' (log R)^(1/10))`, not the required `R² K` scale.
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

## Preservation and success conditions

Preserve all obstruction modules, exact reassembly theorems, root/export
manifests, declaration-graph checks, owned-warning gates, and terminal axiom
checks. Do not add unfinished proofs, new analytic axioms, independence
assumptions, or a renamed RH-strength hypothesis.

A new route must identify the quantitative ingredient, its exact carrier and
quantifiers, and the compiled consumer it meets. Success means proving a
sufficient uniform estimate and composing it with that consumer without a new
open premise. The present closeout makes no such claim.
