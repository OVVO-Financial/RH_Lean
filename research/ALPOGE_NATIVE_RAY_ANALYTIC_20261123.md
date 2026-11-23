# Native ray analytic bridge using Alpöge's original costs

descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1
tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1

## Scope

This reconstruction continues the actual ray-ideal arithmetic family merged in
PR #1197. It uses the original sufficient costs and retains the real exceptional
zero. It does not import the original finished RH theorem, create a new analytic
family as a hypothesis, or require the optional B^-6 improvement.

Acceptance is the warning-fatal hosted build and exact terminal-axiom audit of
the PR head. No local Lean or Lake is used.

## Constructed chain

The same `NativeRay.LFam.ofRayData` fixes K, d, M, the root, actual ray datum,
and the literal ideal coefficients. The new analytic definitions are finite
character sums of those coefficients, their Mellin remainder, the regularized
F, the prime-power summatory function and the explicit exceptional-zero predicate.

| Native module | Supplied result and retained original cost |
| --- | --- |
| NativeRayLFunctionDefinitions | Literal aChi, lamChi, res, mel, F, psi, ell and ExcZ |
| NativeRayLFunctionContinuation | Analyticity for Re(s)>1/2, exact Dirichlet-series identity, and 300 B (norm(s)+1)^2 growth for Re(s)>=11/20 |
| NativeRayLFunctionLogDeriv | Full von Mangoldt convolution, exponential identity, nonvanishing for Re(s)>1, lower norm ((Re(s)-1)/Re(s))^2, and the exact principal pole correction |
| NativeRayLFunctionPositivity | The complete 3-4-1, principal, two-real and four-real positive combinations |
| NativeRayExpSumBounds | B^11 min(t,1/t) theta remainder and the exact nonprincipal theta integral at one |
| NativeRayRealCharacterLowerBound | Original quantitative real-character lower bound; the source proof chooses exponent 45 |
| NativeRayRealZeroGap | Cauchy derivative bound 18000 B; the original conversion (A,c) to (A+1,c/18000) |
| NativeRayLocalZeros | General analytic factorization, zero count and local logarithmic derivative, preserving multiplicities |
| NativeRayLFunctionLocalFormula | Native ray specialization at center 5/4+it and the original radii 3/5 and 1/2 |
| NativeRayZeroFreeRegion | Zero-free region with the precise possible real-character, real-zero exception |
| NativeRayExceptionalZero | Family-wide uniqueness and simplicity of that possible exception |
| NativeRayAnalyticFamily | Actual-ray-data continuation, exact logarithmic derivative and real-character nonvanishing at one |

B remains 4 d M^2. The principal regularization is F_1(s)=(s-1)L(a_1,s);
nonprincipal F_chi(s)=L(a_chi,s) on Re(s)>1. The logarithmic derivative includes
+1/(s-1) only for the principal character. All prime powers are retained.

The possible exceptional character is not asserted to be nonprincipal. That
case is preserved in the original positive-combination argument and in ExcZ.

## Source and reconstruction

Pinned guide: CocoSgt/riemann-hypothesis-lean at
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.

Definition source:
`src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean`.

Proof sources are under
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`:

- RayClassLFunctionFamilyContinuationGrowth.lean
- RayClassFamilyLogDerivReGtOne.lean, with the required two elementary lemmas from TsumOneDivRpowLe.lean
- RayClassLFunctionFamilyLogDerivPositivity.lean
- ExpSumBounds.lean
- NormRayClassFamilyFOneGeOfRealCharacter.lean
- ExistsRayClassLFunctionRealZeroFarFromOne.lean
- ExistsFactorOrder.lean and NormOneSubConjMul.lean
- RayClassLFunctionLogDerivLocalFormula.lean
- RayClassLFunctionZeroFreeRegion.lean
- RayClassLFunctionUniqueSimpleExceptionalZero.lean

Native calls replace the original statement-wrapper aliases directly. Proof
bodies retain the original normalizations and constants, with syntax/API repairs
for the native Mathlib pin. No proof budget is increased.

## Review and verification contract

Independent source and mathematical reviews check the principal normalization,
literal coefficients, signed regrouping after absolute convergence, all positive
character combinations, zero multiplicities, the exceptional cases and constants.
`research/ALPOGE_NATIVE_RAY_ANALYTIC_AUDIT_20261123.lean` guards thirteen
quantitative or actual-family endpoints and accepts only propext,
Classical.choice and Quot.sound. The root import manifest includes every new
native module. Hosted CI is the compiler acceptance gate.

## Remaining application

The next analytic application is the exceptional-zero prime-power summatory
estimate, identity-ray short-interval mass, and actual norm-one level-prime
selection. The native actual theta/cusp-section construction and quantitative
Gram/divisor/lattice conditions still have to be attached to one compatible
geometric family before the complete signed-slope consumer becomes unconditional.

The final square-clock universal Gz bound and RH are not concluded here.
