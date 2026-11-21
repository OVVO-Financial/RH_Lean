# Alpoge Gz -> exact native signed Erdos historical rate and explicit cost

Date: 2026-11-21. Status: finite source identity unconditional;
new Lean source committed, exact-head CI pending; terminal uniform estimate open.
External quantitative cost theorem is a SOURCE inspected proof chain, not
a declaration that its total RH claims are independently certified.

## 1. Exact original arithmetic (not an imported theorem)

From nativePNTWeightedErrorMass_eq and the prime-power successor formulas:
~~~
Gz(N) = N * C(N), N>=1
C(N) = nativePNTWeightedErrorMass(N-1)+harmonic(N)-log(N)+EulerGamma
     = sum_(1<=n<N) (psi(n)-n)/(n*(n+1))
        +harmonic(N)-log(N)+EulerGamma.
~~~
This is the literal original Alpoge Gz, expressed on the full signed
Erdos Chebyshev-error prefix. No term is discarded. The right endpoint
von Mangoldt term cancels between N*LambdaRecip(N) and psi(N).

Original square endpoints X_R=R^2-1 therefore obey Gz(X_R)=X_R*C(X_R).
The external one-sided positive-sign objective
Gz(N)<=constant_eps*N^(1/2+eps) is IDENTICAL to the native objective
C(N)<=constant_eps*N^(-1/2+eps). It is NOT a demand for an absolute
pointwise Chebyshev-error estimate.

Lean source: RHLean/Analysis/AlpogeGzErdosReciprocalHistory.lean.
Earlier research: research/ALPOGE_LITERAL_GZ_SELBERG_TRANSLATION_20261120.lean
and RHLean/Analysis/NativePNTErrorMass.lean.

## 2. Actual Alpoge cost theorem, with no hidden parameters

Source: CocoSgt/riemann-hypothesis-lean:
src/Development/AutomorphicArithmetic/ConductorsKronecker/CostPropositionBasicBound.lean
theorem cost_proposition_basic_bound.

Set T=TT.card, m=number of genuine lifts, f=fPl(H),
delta=delta2(T2)=(T2.card)/(Fintype.card H), b>0.
With the EXACT external HostFactsS and GrowthInequalityHypotheses it proves
~~~
T*m*b*(delta/2) * (Gz(x)-3*x^(1/2+eps)-moveCost)
  <= Err + T*m*(2*f*(x+1)*b*theta)
         + T*m*(6*f*(x+1)*(eta+1)).
~~~
For integer x=N>=1, T,m,b,delta strictly positive, substitute
Gz(N)=N*C(N), divide by N*T*m*b*delta/2, and obtain EXACTLY:
~~~
C(N) <= 3*N^(-1/2+eps) + moveCost/N
       + 2*Err/(N*T*m*b*delta)
       + 4*f*(N+1)*theta/(N*delta)
       + 12*f*(N+1)*(eta+1)/(N*b*delta).
~~~
The external SmallCosts package states
~~~
moveCost <= N^(1/2+eps),
2*f*(N+1)*theta <= 1/N,
6*f*(N+1)*(eta+1) <= b/N,
~~~
hence the native exact implication reduces to
~~~
C(N) <= 4*N^(-1/2+eps) + 2*Err/(N*T*m*b*delta)
        + 4/(N^2*delta).
~~~
Every cost is visible. Neither an unquantified NNS covariance
nor the isolated negative rank-one 2I-J prime-band matrix
supplies the genuine Err/multiplicity/thick fraction bounds.

The external theorem cost_proposition_at_scale adds SizeWindows and proves
~~~
Gz(x) <= x^(1/2+(C+3)*eps),
~~~
therefore C(N)<=N^(-1/2+(C+3)*eps). To reconstruct the result independently
inside RH_Lean, establish actual source-identical Ask-MAIN/topExcess,
width/ramified return/height, true family multiplicity and SizeWindows
witnesses. Do NOT import that final inequality as an axiom.

## 3. Finite full-prime-power check, not a uniform theorem

Separate sieve over every actual prime power up to X_R gave:
~~~
R      X_R      direct Gz(X_R)    Gz/sqrt(X_R)    identity residual
56       3135       2.83318        0.05060           3.7e-11
317    100488       3.79008        0.01196           1.2e-08
549    301400      -0.18379       -0.00033           1.6e-09
1027  1054728       7.13886        0.00695           7.7e-07
~~~
Residuals are floating-point rounding; the symbolic statement is exact.
No finite set of observed signs or cancellation percentages proves a
uniform asymptotic exponent.

## 4. Source-faithful attack

Original Mobius and Lambda -> signed Erdos reciprocal prefix (exact)
-> genuine Alpoge Gz (exact new Lean lemma)
-> joint Frobenius/inertia four-colour occupancy (exact algebra)
-> source-preserving ASK-MAIN with ALL prime-power, collar, partner returns
-> SAME family's geometric height/covolume/divisibility and multiplicity
-> paid genuine topExcess/SizeWindows
-> one-sided native C(N) upper power rate
-> one-sided Landau.

This is a detailed reconstruction path, not a substitute statement for
the missing normalized top-excess estimate. The next necessary output is
a genuine bound on Err/(T*m*b*delta) on the SAME arithmetic family,
not an independent bound on selected K2 products. The full K2-lambda
principal-mode cancellation is audited in
research/ALPOGE_MATCHED_K2_NNS_GLOBAL_COHERENCE_20261121.md.
