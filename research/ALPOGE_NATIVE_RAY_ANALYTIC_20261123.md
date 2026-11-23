# Native ray analytic and level-prime bridge using Alpöge's original costs

descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1
tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1

## Scope

This reconstruction continues the actual ray-ideal arithmetic family merged in
PR #1197 through analytic continuation, the possible exceptional zero, short
prime windows, and an integral norm element in the actual native dyadic host.
It uses the original sufficient costs, including the real-character exponent 45
and the complete prime-power correction. The optional B^-6 improvement is not
a prerequisite. No original finished RH theorem or source compiled artifact is
imported, and no new analytic family is supplied as a hypothesis.

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
| NativeRayContourResidues | Rectangle residue theorem with local simple and double principal parts |
| NativeRayContourLocalExpansion | Local logarithmic-derivative pole and the precise analytic expansion used in the contour integral |
| NativeRayContourChebyshev | The original bound sum(vonMangoldt(n), n<=x)<=2x, with a kernel-checked finite base case |
| NativeRayPerronKernel | The original truncated Perron kernel and its constant 3 |
| NativeRayPerronSums | Absolutely convergent interchange and near/far tail estimates, retaining both neighboring floor terms |
| NativeRayPerron | Truncated Perron for coefficients bounded by 2 vonMangoldt, with error C(u log(u)^2/T + log(u)) |
| NativeRayLogDerivHalf | Logarithmic derivative after subtracting the actual exceptional zero, with C ell(t)^2 bound |
| NativeRayPsiExceptional | Explicit prime-power summatory estimate with exceptional term retained and error C u exp(-c sqrt(log u)) |
| NativeRayShortInterval | Identity-ray short-interval mass c' h X / B^A, with universal constants before the family |
| NativeRayNormPrimeWindow | Literal native norm-one primes, lower count c' h X / ((4 d M^2)^A log X), and the complete 2(psi-theta) prime-power subtraction |
| NativeRayPrimeParameters | The original discriminant/modulus size regime ModAt, containing no prime-existence premise |
| NativeRayNormPrimeCount | Uniform dyadic lower count Y^(9/10), constructing the ray datum internally |
| NativeRayLevelPrime | A prime in the specified window (Ts, (1+1/V)Ts] with modulus N(g1 g2)^2 and the original logarithmic costs |
| NativeRayHostLevelPrime | That level prime and its integral norm element in the literal quadratic subfield of nativeDyadicHostRaw |

B remains 4 d M^2. The principal regularization is F_1(s)=(s-1)L(a_1,s);
nonprincipal F_chi(s)=L(a_chi,s) on Re(s)>1. The logarithmic derivative includes
+1/(s-1) only for the principal character. All prime powers are retained.

The possible exceptional character is not asserted to be nonprincipal. That
case is preserved in the original positive-combination argument and in ExcZ.

## Same-host endpoint and quantifiers

`nativeDyadicHostRaw_levelPrime_rayNormElement` first fixes eps in (0,1/52)
and positive constants cs and CY, then produces a threshold x0 **before**
the host, modulus, generators, and short window are chosen. The actual quadratic
field is H.K inside H.E for H = nativeDyadicHostRaw e q d he hH. Its root
`NativeQuadraticSplitting.bK H.sqd` and its rational degree two are existing
native constructions; neither is an extra field-existence hypothesis.

Under the original ModAt and window-size conditions, the theorem constructs
one prime T and one element pi in the ring of integers of that same H.E, with:

- Ts < T <= (1 + 1/V) Ts;
- IsNormOne d (N (g1 g2)^2) T;
- pi in H.K and pi * H.conj(pi) = T;
- pi - 1 in the principal ideal generated by N (g1 g2)^2;
- T congruent to 1 modulo N (g1 g2)^2.

The proof first invokes the native level-prime theorem in H.K and then the
existing `nativeDyadicHostRaw_exists_rayNormElement` construction. N may be
the actual host conductor. Its size regime and the other geometric window
conditions remain explicit; this theorem does not assert they hold without
the corresponding parameter construction.

The modulus cost is exactly
log 4 + log d + 2 log N + 4 log g1 + 4 log g2.
The norm-prime count and level-prime proofs discharge the original ShortNorm
analytic supplier using the constructed ray family. They do not take that
supplier as an additional premise.

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
- LogDerivSubExceptionalLe.lean
- AnalyticAtDslope.lean (the needed local analytic helper only)
- TruncatedPerronOfLeTwoVonMangoldt.lean and its Perron kernel/sum dependencies
- RayClassFamilyPsiWithExceptionalZero.lean
- TrivialClassShortInterval.lean
- NormPrimesImagQuadShortIntervalLowerBound.lean

The elementary Chebyshev proof is reconstructed from
`src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SumVonMangoldtLeTwoMul.lean`.
The final parameter and prime-window proofs follow `ShortNorm.lean`,
`normPrimesN.lean`, and `levelPrimeN.lean` in
`src/Development/AutomorphicArithmetic/ShortNorms/`.
The same-host application follows the level-prime-to-norm-element passage in
`ExistsLevChOfLevelPrime.lean`, using the already native algebraic supplier.

Native calls replace the original statement-wrapper aliases directly. Proof
bodies retain the original normalizations and constants, with syntax/API repairs
for the native Mathlib pin. No proof budget is increased.

## Review and verification contract

Independent source and mathematical reviews check the principal normalization,
literal coefficients, signed regrouping after absolute convergence, all positive
character combinations, zero multiplicities, the exceptional cases and constants.
`research/ALPOGE_NATIVE_RAY_ANALYTIC_AUDIT_20261123.lean` guards twenty-four
quantitative or actual-family endpoints and accepts only propext,
Classical.choice and Quot.sound. The root import manifest includes all 26 new
native modules. Hosted CI is the compiler acceptance gate; the draft's source
review is not a claim that compilation has already succeeded.

## Remaining application

This branch supplies the ray analytic and level-prime chain, including its
attachment to the actual native host. The next geometric work is to construct
the actual theta/cusp-section carrier and prove its short-span and integral
norm properties, then attach the quantitative Gram, divisor, and lattice
conditions to one compatible physical family. The complete signed-slope
consumer still needs those geometric inputs, the strong error-window bounds,
and their common size regime.

The final square-clock universal Gz bound and RH are not concluded here.
