# Multi-route RH criterion formalization plan

This document records the dependency-bounded program for developing multiple rigorous routes into the repository's existing square-prefix/Mertens criterion.

It does not introduce a second definition of the RH target. Every route must terminate in one of the already compiled propositions

```text
SquarePrefixCurrentPointwiseBoundedStatement
SquarePrefixUniformLocalBoundedStatement
MertensEnergyBoundedStatement
```

and may reach `RiemannHypothesisStatement` only through an ordinary argument of type

```text
ClassicalMertensRHCriterion
```

whose field is exactly

```text
MertensEnergyBoundedStatement ↔ RiemannHypothesisStatement.
```

## 1. Governing classification

Every new theorem or definition must be identified as exactly one of the following.

1. **Exact identity** — proved from existing definitions with no analytic estimate.
2. **Exact reparameterization** — an invertible or one-way coordinate description that creates no new arithmetic information.
3. **Realization theorem** — identifies an abstract or geometric object with a concrete arithmetic object.
4. **Sufficient criterion** — proves a one-way implication into the compiled pointwise or uniform-local criterion.
5. **Open analytic premise** — a typed proposition not asserted to be proved.
6. **Finite certificate statement** — an executable finite-range claim whose asymptotic extension is not inferred.

No candidate baseline, numerical experiment, partial-moment ratio, covariance identity, or transport decomposition may be described as equivalent to RH unless the equivalence is actually proved through the existing criterion spine.

## 2. Protected criterion spine

The immutable repository endpoint is

```text
SquarePrefixUniformLocalBoundedStatement
  ↔ SquarePrefixCurrentPointwiseBoundedStatement
  ↔ SquarePrefixEnergyBoundedStatement
  ↔ MertensEnergyBoundedStatement
  ↔ RiemannHypothesisStatement.
```

The project proves the first three equivalences. The final equivalence remains the ordinary typed external input `ClassicalMertensRHCriterion`.

New routes should normally prove one of

```text
NewPremise → SquarePrefixCurrentPointwiseBoundedStatement
NewPremise → SquarePrefixUniformLocalBoundedStatement
NewPremise → SquareBlockIncrementEnergyBoundedStatement
```

and then reuse the compiled chain.

## 3. Completed foundation

### 3.1 Generic baseline transport split

Module:

```text
RHLean.Proof.SquareBlockTransportBaseline
```

For arbitrary `F : ℝ → ℂ`, the module defines

```text
squareBlockBaselineTransportApprox
squareBlockBaselineTransportError
squareBlockBaselineMainIncrement
squareBlockBaselineMainPrefix
squareBlockBaselineTransportErrorPrefix
```

and proves exact blockwise and cumulative identities

```text
transport = baseline approximation + baseline error
canonical increment = baseline main increment - baseline error
squarePrefixMertens = baseline main prefix - baseline error prefix.
```

This is only a coordinate split of the existing largest-prime-factor transport object. It does not yet provide prime-count interval semantics.

## 4. Phase XI — finite signed-moment infrastructure

### 4.1 Generic finite partial moments

Planned module:

```text
RHLean.Proof.FinitePartialMoments
```

Define for a finite real sequence and `d > 0`

```text
upperPartialMoment
lowerPartialMoment
absolutePowerMass
signedPowerMoment
```

Prove

```text
upperPartialMoment - lowerPartialMoment = signedPowerMoment
upperPartialMoment + lowerPartialMoment = absolutePowerMass.
```

At degree one prove

```text
signedPowerMoment 1 = finite signed sum
absolutePowerMass 1 = finite absolute sum.
```

For nonzero absolute mass define the ratio and prove

```text
signed sum = absolute mass * (2 * ratio - 1).
```

The ratio theorem must explicitly handle the zero-denominator case. No theorem may claim that a general degree `d ≠ 1` recovers the ordinary signed sum.

### 4.2 Sign-valued degree collapse

Planned module:

```text
RHLean.Analysis.SignValuedPowerMoments
```

For values in `{-1,0,1}`, prove for every `d > 0`

```text
sign x * |x|^d = x.
```

This special theorem must remain separate from the general real-sequence identity.

## 5. Phase XII — square-block partial-moment criteria

### 5.1 Real canonical block increments

Planned module:

```text
RHLean.Proof.RealSquareBlockIncrements
```

Define the real canonical increment

```text
realCanonicalTotalIncrement k = ∑ m ∈ canonicalSquareBlock k, (μ m : ℝ)
```

and prove its complex cast equals `canonicalTotalIncrement k`. Prove the cumulative real sum casts to `squarePrefixMertens`.

### 5.2 Elementary total-variation bound

Prove

```text
|realCanonicalTotalIncrement k| ≤ 2 * k + 1
```

and hence

```text
∑ k ∈ range (N + 1), |realCanonicalTotalIncrement k| ≤ (N + 1)^2.
```

### 5.3 Degree-one balance criterion

Planned module:

```text
RHLean.Proof.SquareBlockPartialMomentBalance
```

Use a denominator-free primary statement. A model form is

```text
∀ ε > 0, ∃ C ≥ 0, ∀ N ≥ 1,
  N * |∑ k ≤ N, d_k| ≤ C * N^ε * ∑ k ≤ N, |d_k|.
```

Combine it with the elementary total-variation bound to prove

```text
SquarePrefixCurrentPointwiseBoundedStatement
```

and then reuse the existing local and RH bridges. The ratio formulation is secondary and requires a nonzero-mass hypothesis.

## 6. Phase XIII — common-normalized signed empirical discrepancy

Planned modules:

```text
RHLean.Analysis.SignedEmpiricalDiscrepancy
RHLean.Proof.SquarePrefixSignedDiscrepancy
```

Define positive and negative prefix masses with one common normalization. Prove that the terminal signed discrepancy equals the signed sum divided by the common total mass.

Do not normalize the positive and negative empirical distributions separately, because separate normalization erases total sign imbalance.

A decay premise for the supremum discrepancy, combined with an elementary mass bound, may be proved sufficient for the current pointwise square-prefix criterion.

## 7. Phase XIV — baseline joint-energy hierarchy

Planned modules:

```text
RHLean.Proof.SquareBlockBaselineJointEnergy
RHLean.Proof.SquareBlockBaselineEnergyCriterion
```

For the exact split

```text
Δ_k = baselineMain_k - baselineError_k
```

prove the complete signed identity

```text
|Δ_k|^2 = |baselineMain_k|^2 + |baselineError_k|^2
          + complete signed interaction.
```

Retain the interaction exactly.

Also prove the stronger diagonal sufficient theorem

```text
baseline-main L2 bound
and baseline-error L2 bound
→ SquareBlockIncrementEnergyBoundedStatement.
```

This is a one-way sufficient route, not an equivalence unless both directions are separately proved.

## 8. Phase XV — atomic block bridges

Planned module:

```text
RHLean.Analysis.FiniteAtomicBlockBridge
```

For an arbitrary finite atomic measure on `[a,b)`, prove the exact decomposition into

```text
left endpoint value
+ affine total-mass path
+ centered atomic bridge.
```

Prove that the centered bridge vanishes at the block endpoints and records the atom locations.

A prime-counting specialization is descriptive and takes the true prime atoms as input. It is not a prime estimator and must be documented as non-predictive.

## 9. Phase XVI — implied logarithmic bases and Viole candidates

### 9.1 Generic implied base

Planned module:

```text
RHLean.Analysis.ImpliedLogBase
```

For a positive estimator `F`, define

```text
b_F(x) = exp (F(x) * log x / x)
```

under explicit domain conditions and prove

```text
x / log_{b_F(x)} x = F(x).
```

This is an exact reparameterization. Specializing to `F = π` is exact but circular as a predictive formula.

### 9.2 Deterministic Viole function

Planned modules:

```text
RHLean.Analysis.VioleFunction
RHLean.Analysis.VioleMidpointInterpolation
RHLean.Analysis.VioleAsymptotics
```

Define the dynamic-base candidate from `x`, `log 10`, and the fixed tuning constant. Define local midpoint affine interpolation and prove endpoint agreement and gluing.

Any asymptotic expansion must be proved with explicit domains and remainder hypotheses. The known nonzero third-order bias relative to `Li` must be retained; this candidate receives no RH implication merely from being non-circular.

## 10. Phase XVII — canonical transport prime-pair realization

Planned modules:

```text
RHLean.Proof.CanonicalTransportPrimePairs
RHLean.Proof.CanonicalTransportPrimeIntervals
```

Starting from the existing definition of `squareBlockTransportIncrement`, prove the exact largest-prime-factor reindexing `m = c*q` with

```text
q prime
q > k
c ≤ k
q ∤ c
k^2 ≤ c*q < (k+1)^2.
```

Prove the boundary conditions rather than hiding them in a naive prime-count difference. Only after this realization may transport be rewritten as a Möbius-weighted restricted prime-interval count.

## 11. Phase XVIII — two-index interval discrepancy

Planned module:

```text
RHLean.Proof.TransportIntervalDiscrepancy
```

For a baseline `F`, define a two-index discrepancy `r_F(k,c)` on the correctly restricted pulled-back intervals. Prove

```text
squareBlockBaselineTransportError F k
  = ∑ c ≤ k, μ(c) * r_F(k,c)
```

for the baseline approximation matched to the prime-interval realization.

Whole square-block prime totals do not determine these partial interval discrepancies and must not replace the two-index object.

## 12. Phase XIX — triangular transport operator and large-sieve routes

Planned modules:

```text
RHLean.Analysis.TriangularTransportOperator
RHLean.Proof.TransportLargeSieveCriterion
```

Define

```text
(M r)_k = ∑ c ≤ k, μ(c) * r(k,c).
```

Prove finite Cauchy–Schwarz and Hilbert–Schmidt estimates. State stronger cancellation-aware operator estimates as open premises.

A transport-error L2 premise plus a baseline-main L2 premise may then imply the compiled increment-energy criterion.

## 13. Phase XX — increment coherent mean and centered covariance

Planned module:

```text
RHLean.Analysis.IncrementMeanCovariance
```

For finite increments prove

```text
increment energy = coherent mean energy + centered increment energy.
```

Keep this distinct from the already compiled covariance decomposition for cumulative prefix values. Prove the exact conjunction equivalence for the strong increment-energy statement.

## 14. Phase XXI — weighted signed Möbius power moments

Planned module:

```text
RHLean.Analysis.WeightedSignedPowerMoments
```

For nonnegative weights prove

```text
UPM_d - LPM_d = ∑ μ(m) * w(m)^d
UPM_d + LPM_d = ∑ μ(m)^2 * w(m)^d.
```

For indicator weights prove degree collapse. For general weights preserve the distinction between degree one and higher degree.

## 15. Phase XXII — executable finite certificates

Planned modules may include

```text
RHLean.Verification.PartialMomentCertificates
RHLean.Verification.BaselineTransportCertificates
RHLean.Verification.PrimeBlockCertificates
RHLean.Verification.TransportOperatorCertificates
```

Each checker must prove only a finite statement from supplied data. No finite certificate implies an asymptotic premise without a separate theorem.

## 16. Required PR order

The repository requires one dependency-bounded layer per PR. The intended order is:

```text
#65 generic baseline split
then finite partial moments
then real square-block increments
then degree-one partial-moment sufficient route
then common-normalized signed discrepancy
then baseline joint energy
then atomic block bridge
then implied log bases
then deterministic Viole definitions/interpolation
then Viole asymptotics
then canonical transport prime-pair realization
then prime-interval realization
then two-index discrepancy identity
then triangular operator estimates
then increment mean/covariance
then weighted signed moments
then finite certificate layers.
```

A later phase may be reordered only when its imports and theorem statements do not depend on unfinished earlier realizations.

## 17. Merge discipline

For every phase:

- branch from current green `main`;
- inspect the pinned mathlib `v4.24.0` APIs before implementation;
- update `FORMALIZATION_SEQUENCE.md`, `FORMALIZATION_CHECKLIST.md`, and the PR body before merge-gating CI;
- run `bash scripts/audit_assumptions.sh`;
- run `lake build RHLean --wfail`;
- merge only after green CI and explicit authorization;
- begin the next PR only after confirming the previous merge on current `main`.

This sequencing is not administrative overhead. It prevents a descriptive identity, conjectural estimate, or candidate baseline from being silently promoted into the repository's established RH equivalence chain.
