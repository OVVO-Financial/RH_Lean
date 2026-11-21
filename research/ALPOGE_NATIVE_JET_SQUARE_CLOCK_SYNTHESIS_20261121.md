# Alpöge × RH_Lean: final native proof synthesis and exact square-clock sampling

**21 November 2026.** Evidence and proof ledger, not a claim to have proved RH.
The direct all-integer upper bound on the complete `G_z` source is still
conditional on a genuinely new arithmetic/geometric quantitative estimate.
This note identifies what is exact, what is unconditionally bounded, what
can be reduced, and why the simpler `C -> R` and Boolean-derivative shortcuts
do not by themselves pay Stepanov multiplicity.

## A. Source identity, with no compensation discarded

The native integer-point Alpöge source is exactly
```
G(N) = N*sum_{d<=N} Lambda(d)/d - psi(N)
       -N*log(N)+(1+EulerGamma)*N
     = N*(W(N-1)+harmonic(N)-log(N)+EulerGamma),
W(K) = sum_{1<=n<=K} (psi(n)-n)/(n*(n+1)).
```
The first equality is its definition, the second is a finite Abel
identity. For integer N, the Lambda(N) endpoint cancels exactly when
comparing N*LambdaRecip(N)-psi(N) with the preceding prefix.
The new independent root module
`RHLean/Analysis/AlpogeSquareClockSignedHistorySampling.lean`
recovers this result directly from MAIN's
`nativePNTWeightedErrorMass_eq` plus the prime-power successor theorems.
No `G_z` estimate is imported, and no separate signed channel is bounded.

Earlier #1169 also identified the same whole source as the complete
signed Erdos historical observable; that earlier draft is NOT a
prerequisite for this file or this new focused branch.

## B. Exact one-sided discrete derivative and ALL-INTEGER interpolation

On MAIN, `nativeLambdaRecip_sub_log_bounds` gives:
```
-1 <= LambdaRecip(n)-log n <= log 4 + 2    (n>=1).
```
On MAIN, `nativeOne_le_succ_mul_log_succ_sub_log` gives:
```
(n+1)*(log(n+1)-log n) >= 1              (n>=1).
```
Their exact recombination after prime-power cancellation is:
```
G(n+1)-G(n)
 = LambdaRecip(n)-log n + EulerGamma
   +1 - (n+1)*(log(n+1)-log n)
 <= Lsafe := log 4+2+|EulerGamma|.
```
Thus for all integers 1<=A<=B:
```
G(B) <= G(A)+Lsafe*(B-A).
```
At N>=4, choose R=floor(sqrt(N+1)).
The primitive integer inequalities are
```
2 <= R; 1 <= X_R=R^2-1 <= N;
0 <= N-X_R <= 2R+1.
```
Consequently, UNCONDITIONALLY:
```
G(N) <= G(X_R)+Lsafe*(2R+1).
```
This is an O(sqrt N) full-source INTERPOLATION ERROR, not a
bound on the unknown square-clock value G(X_R).

The root theorem `nativeAlpogeGz_of_squareClock_bound` is intentionally
parametric in an honest square-endpoint supplier U(R):
```
(forall R>=2, G(R^2-1)<=U(R))
    => G(N)<=U(floor(sqrt(N+1)))
             +Lsafe*(2floor(sqrt(N+1))+1).
```
Since R<=sqrt(N+1), choosing U(R)=C_eps R^(1+2eps)
transfers the required root-clock growth
to G(N)=O_eps(N^(1/2+eps)) at ALL integer N.
**Therefore the difficult bound only needs to be proved on the
original RH_Lean square endpoints**, not at every integer.

No square-endpoint U(R)=O_eps(R^(1+eps)) theorem is asserted or supplied.

## C. Arithmetic derivative, Boolean jet, and C-to-R map

Three genuinely pre-existing exact algebraic tools:

1. `RHLean/Analysis/LogWeightedPrimeExtensionEndpoint.lean`:
   the derivation Df(n)=f(n)log n obeys the Dirichlet product rule
   D(f*g)=Df*g+f*Dg; its next iterate gives the authentic
   Selberg LambdaTwo = D Lambda + Lambda*Lambda.
2. `RHLean/Arithmetic/PrimeCombFiniteDifference.lean` and
   `MobiusFiniteDifferenceIdentification.lean`:
   the complete Boolean prime differentiation operator
   `D_S f(X)=sum_{d|P_S} mu(d) f(floor(X/d))`.
   It is an exact order-|S| finite difference and preserves full
   original integer Möbius signs.
3. `research/STABLE_FAR_PERRON_REALIFICATION.lean`:
   the invertible real map Phi(a+ib)=(a-b,a+b), its inverse, and its
   normalized Hermitian Gram/energy equivalence. The corresponding
   real directional derivatives for a holomorphic F are
   `(partial_u+partial_v)Phi(F)=Phi(F')` and
   `(partial_v-partial_u)Phi(F)=Phi(iF')`.
   These are chain-rule identities (not new kernel-certified
   declarations in this branch).

These interfaces unify polynomial/complex differentiability with
original signed arithmetic and exact NNS covariance. However,
**an isometric coordinate change cannot independently improve a
nonnegative Gram bound**, nor does order-|S| of a Boolean derivative
automatically produce order-|S| vanishing or p-adic divisibility.

## D. Exact counter-test: high finite-difference order is not high
## Stepanov multiplicity

Take the original Boolean Mobius finite-difference operator applied
to the entirely legitimate linear arithmetic source f(X)=X.
For a prime set S and its primorial P:
```
D_S f(P) = sum_{d|P} mu(d)*floor(P/d)
         = P*sum_{d|P}mu(d)/d
         = P*prod_{p in S}(1-1/p)
         = prod_{p in S}(p-1)
         = phi(P).
```
For S={2,3}, this is 6-3-2+1=2, NOT divisible by 3.
For S={2,3,5,7}, it is 48, NOT zero and NOT divisible by 7.
For the first k primes ending at p, every q-1 is in [1,p),
so p divides none of the factors q-1: in fact p does NOT
divide phi(P) for ANY such k.

The exact independent integer test
`scripts/alpoge_difference_multiplicity_exact_audit.py`
passes for the first 10 primorials and asserts the missing
p-adic divisibility fails for every tested wheel.

This is a counterexample only to the *automatic jet=Stepanov
multiplicity* argument, not an impossibility theorem for a
source-specific construction with extra geometric constraints.
It shows that a theta-lift substitute must include an actual
high-divisibility certificate and a controlled height/determinant,
not merely many commuting difference directions.

The realification linear map has determinant 2, hence on m
integer complex coordinates the unnormalized lattice index
is 2^m; this height/covolume cost is also not free.

## E. NNS cross-source cancellation and the correct global target

The complete signed Selberg source has a formerly missed
quadratic principal-mode cancellation:
```
K2(n)-(Lambda*Lambda)(n) = -Lambda(n)*log n.
```
Thus the selected negative `-S^2` 2I-J prime band is canceled
by its matched ordered Lambda convolution, leaving a positive
diagonal.  `research/SELBERG_MATCHED_PRODUCT_FACE.lean` already
certifies the selected physical source and its critical dyadic bound.

NNS finite partial moments give exact Co-Div decompositions.
The earlier #1169 investigation paid the positive local degree-two
UPM of signed G(R^2-1) INCREMENTS at O(H^3), using the one-sided
Mertens bound. A bound on increments alone **does not** bound their
historical cumulative sum: the across-block zero-target covariance
and inherited initial condition can add coherently.

The true global signed inequality remains
```
for all eps>0 exists C_eps:
  G(R^2-1) <= C_eps * R^(1+2eps) for all R>=2,
```
equivalently as a rate for the actual centered Erdos history
```
W(R^2-2)+harmonic(R^2-1)-log(R^2-1)+EulerGamma
    <= C_eps R^(-1+2eps).
```
Combined with Section B and a properly reconstructed one-sided
Landau theorem this supplies RH. **That global square-clock estimate
has NOT been proved here.**

## F. External Alpöge mechanism / exact missing cost certificate

Alpöge's own remark (https://alpo.ge/remark.pdf, pp. 3-4) says
the sqrt(X)-length chain of theta lifts is not just analytic
differentiation; it produces increased multiplicity combined with
divisibility, height, integral structures, covolume and a
source-specific trace formula.

His formal cost proposition (as independently inspected in
CocoSgt/riemann-hypothesis-lean) has the schematic genuine-term
form, at integer x=N with T,m,b,delta>0:
```
CenteredHistory(N)
 <= 3*N^(-1/2+eps)
  + moveCost/N
  + 2*Err/(N*T*m*b*delta)
  + 4*f*(N+1)*theta/(N*delta)
  + 12*f*(N+1)*(eta+1)/(N*b*delta).
```
The terms T, m, b and delta are actual physical witnesses.
No symbol among them may be replaced by merely counting first-order
Boolean prime directions.  The positive topExcess Err and
same-family height/covolume movement are not paid by
an abstract realification or PSD covariance identity.

**A self-contained proof of RH would require a new unconditional
upper estimate on the complete source or native constructions
discharging ALL the genuine Alpöge cost hypotheses with the
same arithmetic family and no imported terminal RH theorem.**
This PR does not contain that estimate.

## G. Source-aware closure acceptance gate

Treat a future proof as closed ONLY if:
- exact source: original Gz integer/square history, including primes powers,
  both signs, floor defects, and matched ordered convolution;
- either an all-R one-sided bound `G(R^2-1)=O_eps(R^(1+2eps))`,
  or original theta/character/height witnesses paying the exact
  normalized topExcess at that scale;
- nonzero determinant, p-adic multiplicity and finite lattice cost
  are proved, not inferred from the number of formal derivatives;
- no circular use of RH or its equivalent target as an assumption;
- a warning-fatal Lean build and axiom audit at the exact merged HEAD.

This is a real simplification of the required endpoint coverage and
a quantified obstruction to the "automatic high-jet" shortcut,
not an announcement that the last RH-strength inequality is solved.
