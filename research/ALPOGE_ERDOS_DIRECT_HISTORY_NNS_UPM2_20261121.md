# Bounding the complete signed Erdos history DIRECTLY (NNS, 2026-11-21)

**Scope and verification:** First-Mertens-based direct one-sided discrete
slope proof and actual dyadic UPM2 **increment** bound are derived without RH.
They are committed to PR #1169 and included in RHLean.lean.
Exact-head Lean CI has NOT completed; these are formalization candidates,
not yet kernel-certified claims. The **global** one-sided
Gz(N)=O_epsilon(N^(1/2+epsilon)) remains an open arithmetic estimate IN THIS REPO.
It is not obtained by summing the local bound. External Alpoge geometric
theorems are not imported as a final premise.

## 1. The source

Let gamma=EulerGamma, psi(N)=sum_{n<=N} Lambda(n),
P(N)=sum_{n<=N} Lambda(n)/n and
W(N)=sum_{n<N} (psi(n)-n)/(n(n+1)).

The exact finite Abel identity from RHLean/Analysis/NativePNTErrorMass.lean is
~~~
Gz(N) = N * H(N),
H(N)=W(N)+harmonic(N)-log(N)+gamma.
~~~
This is **the complete original Alpoge Gz**, not a K2 subband.
Reference Lean: RHLean/Analysis/AlpogeGzErdosReciprocalHistory.lean.

## 2. Exact discrete derivative, original signs intact

At every n >= 1, the prime-power at n+1 cancels from
(n+1)P(n+1)-psi(n+1). Hence
~~~
Gz(n+1)-Gz(n)
 = [P(n)-log(n)+gamma]
   - [(n+1)*(log(n+1)-log n)-1].
~~~
The second bracket is nonnegative: the already-certified theorem
nativeOne_le_succ_mul_log_succ_sub_log proves
(n+1)*(log(n+1)-log n)>=1.

The FIRST Mertens theorem, already certified in RHLean.Analysis,
gives P(n)-log(n)<=log 4+2. Therefore uniformly for all n>=1,
~~~
Gz(n+1)-Gz(n) <= L := log 4+2+gamma.
Gz(M) <= Gz(N) + L*(M-N)  (1<=N<=M).
M*H(M) <= N*H(N)+L*(M-N).
~~~
No extra signed hypothesis, zero-free input, randomness, or external
Alpoge theorem is inserted. Lean source:
RHLean/Analysis/AlpogeErdosHistoryDirectBound.lean.

For X_R=R^2-1, X_(R+1)-X_R=2R+1; thus
~~~
D_R := Gz(X_(R+1)) - Gz(X_R)
     <= L*(2R+1).
~~~

## 3. The ORIGINAL signed history has a critical NNS UPM2 on INCREMENTS

Define positivePart(x)=max(x,0), and set
Lsafe=log 4+2+|gamma| >=0. For every dyadic H>=2,
~~~
sum_(H<=R<2H) positivePart(D_R)^2
 <= H*[Lsafe*(4H+1)]^2
 = O(H^3).
~~~
This is an *UNCONDITIONAL critical-scale degree-two NNS energy
estimate* for the exact signed historical square increments, with
every original prime-power and earlier prefix retained before taking
the positive part. Not an assumption about random signs.

Lean module:
RHLean/Analysis/AlpogeErdosHistoryIncrementNNS2.lean
  alpogeErdosHistorySquareIncrement_eq_Gz_diff
  alpogeErdosHistorySquareIncrement_le
  alpogeErdosHistorySquareIncrementUPM2_le.

Do not conflate this with the larger, RH-strength square-ENDPOINT
energy:
~~~
sum_(H<=R<2H) positivePart(Gz(X_R))^2 <= C_eps*H^(3+eps),
~~~
or the pointwise Gz(X_R)<=C_eps*R^(1+eps).
The former has an inherited initial condition and all inter-block
covariance of D_R.

## 4. Where NNS Co/Div has to land (exact, not modeled)

For a completed root segment [A,B), the telescoping increment sum is
S=sum_(A<=R<B)D_R = Gz(X_B)-Gz(X_A). Its actual zero-target
degree-two polarization is
~~~
S^2 = sum_R D_R^2 + 2*sum_(A<=R<S<B)D_R*D_S
    = Diagonal + 2*(Co_0-Div_0).
~~~
Here Co_0 and Div_0 are genuine off-diagonal positive and negative
pair populations. They must retain their sign when they are *recombined*,
and the inherited Gz(X_A) must be included in any full endpoint claim.

A naive proof that Co_0<=Div_0 always is FALSE on actual primes.
For A=750, B=1500, complete actual prime-power census gave
  sum(D_R^2) = 126.180
  Co_0-Div_0 = +48.441 > 0,
while at [549,1098) the same signed cross term is approximately -48.744.
These are numerical diagnostics, NOT formal counterexample certificates
until a rational interval census is checked. The sign alternates, so
any genuine uniform theorem must be a **quantitative upper covariance
budget**, not an asserted universal nonpositivity law.

The small pointwise bounds on D_R do not directly show either
   (sum_R D_R)_+ = O(B^(1+epsilon))
or
   Gz(X_B)_+ = O(B^(1+epsilon)).
A triangle bound gives O(B^2), losing one full root power.
The missing work must pay the COMPLETE across-root signed covariance
with actual Alpoge partner, host, ramification, width, and height
witnesses, or another NNS arithmetic theorem restricting the same
complete source.

## 5. Actual-prime sanity checks

Original Gz, actual Lambda through every prime power:
~~~
R       Gz(X_R)       Gz(X_(R+1))-Gz(X_R)
56       2.8331809     -0.5577882
317      3.7900760     +0.0759892
549     -0.1837885     -1.0146461
1027     7.1388582     -0.6181555
~~~
All four satisfy the unconditional slope bound L*(2R+1).
These unusually small finite responses are valuable for locating
the source-preserving NNS interaction but not a proof of any
uniform decay rate.

## 6. Direct Alpoge map onto this carrier

External source
src/Development/AutomorphicArithmetic/ConductorsKronecker/CostPropositionBasicBound.lean
proves the true topExcess/height cost inequality conditional on
HostFacts and GrowthInequalityHypotheses. At integer N with
T=TT.card,m>0,b>0,delta=delta2(T2)>0:
~~~
H(N) <= 3*N^(-1/2+eps) + moveCost/N
      + 2*Err/(N*T*m*b*delta)
      + 4*f*(N+1)*theta/(N*delta)
      + 12*f*(N+1)*(eta+1)/(N*b*delta).
~~~
This is a DIRECT one-sided upper-bound formula for the complete signed
historical source and its genuine error terms. An independent RHLean
proof must construct and pay the actual topExcess/size-window
multiplicity witnesses. Neither the local unconditional O(H^3)
increment moment nor Schur PSD alone pays Err or the inter-block Gram.
