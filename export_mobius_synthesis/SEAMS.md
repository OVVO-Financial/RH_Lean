# Möbius Synthesis seams

This note records the exact interfaces that currently join the square-block, prime-wheel, native PNT, and physical-scale layers. It is synchronized to development commit `1535b80a8bac8a800d9368814fe2567e79808312`, the merge of PR #354.

The important post-#354 distinction is that the project now has both:

- a historical direct square-wheel target `H_{k,n}` whose RH-scale exponent remains open; and
- a proved generalized affine PNT contraction whose missing input is an RH-compatible physical cutoff law.

These are related quantitative fronts, not competing definitions of the same theorem.

## 1. Elementary prime-sieve to square-root transport seam

The elementary bridge is carried by

```text
RHLean.Proof.PrimeSievePostSqrtGap
RHLean.Proof.PrimeSieveSquareRootTransport.
```

Under `sqrt x < y`, the first proves

```text
M_y^+(x) - M(x)
  = 2 * sum_{y < q <= x, q prime} M(floor(x/q)).
```

The second specializes to `x = R^2 - 1`, `y = R`, and identifies the pre-large-prime state with the square-block smooth and transport variables. This is exact finite algebra; no prime-distribution estimate is consumed.

## 2. PNT centering to reciprocal intervals

```text
RHLean.Analysis.PrimeSievePNTCentering
RHLean.Analysis.PrimeSieveQuotientPNTError
```

use the singleton logarithmic-integral density

```text
density(q) = Li(q) - Li(q-1)
```

and reindex by

```text
d = floor(x/q).
```

For positive `d`, the exact quotient fibre is

```text
max(y, floor(x/(d+1))) < q <= floor(x/d).
```

The Li masses telescope on that interval, so the exact prime error becomes a finite Mertens-weighted family of prime-count-minus-Li discrepancies.

After the actual square-wheel zero-mode centering, the canonical nonzero response is

```math
H_{k,n}=C_{k,n}^{PNT}-2E_{k,n}^{rec}.
```

The identity is exact. It does not prove separate bounds on either term and does not justify destroying their relative sign with a triangle inequality.

## 3. Square-wheel zero-mode seam

```text
RHLean.Analysis.SquareWheelQuadraticSampling
RHLean.Analysis.SquareWheelZeroModeElimination
RHLean.Analysis.SquareWheelQuantitativeBridge
```

prove the complete-square identity

```math
R_k(X_n)=H_{k,n}+\rho_{k,n}R_k(U_k)
```

and, on synchronized blocks,

```math
0\le\rho_{k,n}<\frac16.
```

Thus the self-referential zero mode is already uniformly contractive. The unresolved direct quantitative target is the size of `H_{k,n}`, not the zero-mode denominator.

## 4. Native PNT to Möbius endpoint seam

The native square-prefix Selberg--Erdős chain proves the ordinary prime number theorem unconditionally:

```text
RHLean.Analysis.nativePNTSquarePrefixPrimeNumberTheorem.
```

`RHLean.Analysis.NativePNTAxer` connects the same arithmetic architecture to the Mertens summatory function. This seam historically established the `o(x)` scale, not the RH power scale.

The post-#354 update is that the native PNT layer now also carries a **quantitative affine-envelope state**, so the seam is no longer purely qualitative.

## 5. Affine PNT envelope seam

`RHLean.Analysis.NativePNTTailAffineEnvelope` proves that a true tail estimate beginning at physical cutoff `M`,

```math
|\psi(N)-N|\le\alpha N
\qquad (N\ge M),
```

globalizes to an affine envelope with finite-prefix intercept

```math
D=(\log 4+3)M.
```

`RHLean.Analysis.NativePNTOptimalInterceptCore` and `NativePNTTailOptimalIntercept` then connect this explicit envelope to the least admissible intercept.

This is the seam between physical cutoff control and global affine PNT control.

## 6. Reciprocal intercept to square-root error seam

`RHLean.Analysis.NativePNTReciprocalInterceptPowerBound` defines

```text
NativePNTReciprocalInterceptLaw K
NativePNTReciprocalTailCutoffLaw K.
```

The first requires an affine envelope of slope `alpha` with intercept `K / alpha`. From it the theorem

```text
nativePNTError_abs_le_two_sqrt_of_reciprocalInterceptLaw
```

proves

```math
|\psi(N)-N|\le2\sqrt{KN}.
```

The second gives a sufficient physical-cutoff formulation and is converted to the same reciprocal intercept law.

This seam is fully formalized. The reciprocal law itself remains open.

## 7. State-dependent cubic contraction to quadratic cutoff seam

`RHLean.Analysis.PrimeSieveStateDependentSelbergScalePersistence` records the physical cutoff at every contraction step.

Its target law is

```text
NativePNTQuadraticTailScaleLaw K,
```

which requires, for every small target slope `eta`, a cutoff `M` satisfying

```math
M\eta^2\le K
```

and a genuine tail estimate of slope `eta` beyond `M`.

The theorem

```text
nativePNTError_abs_le_sqrt_of_quadraticTailScaleLaw
```

then proves

```math
|\psi(N)-N|\le\sqrt{KN}
```

for the stated range.

The wrapper

```text
nativePNTError_abs_le_sqrt_of_stateDependentCubicGain
```

shows that an explicit cubic scale chain with the same terminal scale property is enough.

This is the current **bound-changing seam**: the target power changes as soon as the physical cutoff law is supplied.

## 8. Formal obstruction seam: why the state must remain signed

`RHLean.Analysis.NativePNTEvolvingTailObstruction` applies to the canonical absolute evolving-tail state.

It proves:

- the first absolute remainder contains a linear factorial floor;
- the second absolute remainder contains an `N log N`-scale floor;
- the full evolving cost retains that floor up to the explicitly bounded negative tail compensation.

At fixed polynomial physical scale in the reciprocal slope, this is incompatible with the desired cubic gain as the slope tends to zero.

This theorem is the formal seam between the failed sign-blind state and the signed second-Selberg replacement. The conclusion is not that cubic contraction is impossible; the repository already proves cubic contraction. The conclusion is that this particular absolute remainder state cannot deliver the required scale law.

## 9. Log-square cells to signed second Selberg seam

The square-stage log-square modules are

```text
RHLean.Analysis.NativePNTSignedLogSquarePrimeCells
RHLean.Analysis.NativePNTSignedLogSquarePositiveDyadicKernel
RHLean.Analysis.NativePNTSignedLogSquareDyadicCell
RHLean.Analysis.NativePNTSignedLogSquareSquareStage.
```

They reindex `Lambda_2 = mu * log^2` into finite Möbius log-square fibres, expose fresh-prime endpoint atoms, and place the surviving odd-kernel mass on exact complete-square activity bands.

`RHLean.Analysis.NativePNTSignedSecondSelberg` then proves

```math
K_2(n)
=(\Lambda*\Lambda)(n)-\Lambda(n)\log n
=\Lambda_2(n)-2\Lambda(n)\log n
```

and the exact recurrence

```text
E(N) log(N)^2
  = signed Selberg remainder * log(N)
    - Lambda signed remainder mass
    + dyadic Lambda_2 cell mass
    + top boundary mass
    - 2 * Lambda-log signed error mass
    - floor-log signed defect mass.
```

This seam is designed to preserve cancellation until the last possible stage.

## 10. Partial prime wheel to signed second-kernel frontier seam

`RHLean.Arithmetic.PrimeWheelPartialErrorThreshold` already localizes the actual unresolved partial-wheel error below twice the square of the wheel cutoff.

`RHLean.Analysis.NativePNTSignedSecondSelbergWheelFrontier` evaluates the signed second-Selberg kernel on that support. Under

```math
N<2y^2,
```

every frontier site is exactly one of:

```text
q^2, q prime, y < q:
  K_2(q^2) = -(log q)^2

q r, q and r distinct primes, y < q, y < r:
  K_2(qr) = 2 log q log r.
```

No third face occurs.

## 11. Frontier charge to PNT error seam

`RHLean.Analysis.NativePNTSignedSecondSelbergFrontierCharge` defines the actual unresolved frontier finset and its signed raw charge.

The same square-root geometry proves, for every frontier site,

```text
N / n = 1.
```

Since `nativePNTError 1 = -1`, the theorem

```text
nativePNTSignedSecondSelbergWheelFrontierErrorMass_eq_neg_charge
```

gives the exact identity

```text
frontier error mass = - frontier charge.
```

No termwise absolute value and no auxiliary remainder enters this seam.

## 12. Good-mass density to strengthened affine contraction seam

The same post-#354 module returns to the fully rederived square-prefix good-mass theorem. The existing density coefficient is

```text
beta^2 / 6600000.
```

In the low-slope regime `0 < alpha <= 3/2`, choosing

```math
\beta=\frac{2\alpha}{3}
```

gives

```text
nativePNTSquarePrefixLowSlopeCubicConstant = 1 / 178200000.
```

Thus

```text
nativePNTSquarePrefixHasAffineEnvelope_lowSlope_cubic_step
```

proves

```math
\alpha\mapsto\alpha-\frac{\alpha^3}{178200000}.
```

`nativePNTSquarePrefixLowSlope_affineEnvelope_strictly_tighter` certifies that this is strictly stronger than the previous square-prefix step.

This seam is quantitative, not merely structural.

## 13. What is still missing between the seams

The following implications are formalized:

```text
quadratic physical cutoff law
  -> sqrt(N) Chebyshev bound

reciprocal intercept law
  -> 2 sqrt(N) Chebyshev bound.
```

The missing implication is

```text
signed square-block and wheel-frontier arithmetic
  -> RH-compatible physical cutoff law.
```

That is the present central research problem.

The historical direct route remains

```text
signed square-wheel H_{k,n}
  -> RH-scale H bound
  -> RH-scale Mertens transfer,
```

with the first quantitative arrow still open.

## 14. Build completeness

`RHLean.lean` imports 366 modules and is the authoritative exhaustive manifest. The exported `RHLean/` tree is synchronized byte-for-byte to development commit `1535b80a8bac8a800d9368814fe2567e79808312`.

The standalone baseline audit builds the full manifest and checks the axiom dependencies of the historical synthesis theorem, the native PNT endpoint, the strengthened post-#354 affine contraction, and the conditional square-root scale bridge.
