# Direct Alpöge hard-supplier attack in RH_Lean coordinates (2026-11-20)

**Status**: Original finite algebraic consequences of the existing source (proved on paper, finite regression PASS); an unconditional *asymptotic* arithmetic rank bound derived from Stadlmann's established prime-gap theorem (NOT Lean-imported); exact published Alpöge analytic consumption mechanism (SOURCE REVIEWED, external code); the missing complete **signed, cost-controlled** inequality is **OPEN**. This note does not prove RH, GRH, a new Mertens exponent, or a new theorem about zero locations.

## 1. Verified exact target: only one sign at the square root

External published formal source (Alpöge/Claude Lean, read on 2026-11-20):

- `src/Formalism/StatementOC.lean` defines
  `Sz(x) := Sum_{n<=x} Lambda(n) (x/n - 1)` and
  `Gz(x) := Sz(x) - x log x + (1+EulerGamma) x`.
- `src/Formalism/ZetaNonvanishing/GzLipschitz.lean` proves `zetaPrimeSumErrorLipschitz`: there exists an absolute constant `L` such that `|Gz(x)-Gz(y)| <= L|x-y|` for `x,y>=1/2`.
- `src/Formalism/StatementU.lean` defines `ZetaLandauEps`, and `src/Formalism/ZetaNonvanishing/ZetaLandau.lean` proves `zetaLandauEps`: for `s0=1` OR `s0=-1`, upper bounds `s0*Gz(x)=O_epsilon(x^(theta+epsilon))` exclude zeros in `Re(s)>theta`.
- `src/Formalism/SizeWindowBrackets/ChainSlopeWindows/RiemannHypothesisOfPowerBound.lean` specializes the one-sided bound for `theta=1/2` to RH using the half-plane argument.
- `src/Development/AutomorphicArithmetic/PrimitiveCosets/GzEq.lean` proves the zero-target `Gz` is identified with the family principal `An.G` and `Deduction.G`; typed source bridge must not be replaced by an analogy.

Thus, **conditional** on one fixed choice `s0 in {1,-1}` and for every epsilon>0 one scale-independent C_epsilon,

```
s0*Gz(R^2-1) <= C_epsilon*R^(1+epsilon),  all R>=2,
```

then `s0*Gz(x) <= C'_eta*x^(1/2+eta)` for all large real x. Proof: choose `R=floor(sqrt(x+1))`, so `X_R<=x<X_(R+1)`, gap `2R+1`; Lipschitz costs at most `L(2R+1)`, absorbed by `R^(1+epsilon)`, and `R~sqrt(x)`. Alpöge's **one-sided Landau theorem** (not an absolute-value argument) then excludes zeros to the right of `1/2`, and functional equation symmetry gives RH. A bounded choice of sign depending on R does NOT suffice; the sign must be a fixed `s0` for all R.

This is a new *research coordinate*, not a new zero theorem on RH_Lean main. Its hard arithmetic supplier remains OPEN.

## 2. Actual external multiplicity/cost balance

`src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean` defines `GrowthInequalityExplicit` with a principal term

```
 nT * m * b * (delta2/2) * (Gz(x)-3*x^(1/2+epsilon)-moveCost)
 <= Err + nT*m*(2*f*(x+1)*b*theta + 6*f*(x+1)*(eta+1)).
```

All variables are actual external family parameters, not RH_Lean variables. Algebraic division by the positive principal coefficient gives

```
Gz(x) <= 3*x^(1/2+epsilon) + moveCost
       + 2*Err/(nT*m*b*delta2)
       + 4*f*(x+1)*theta/delta2
       + 12*f*(x+1)*(eta+1)/(b*delta2).
```

The hard theorem is simultaneous construction of true host/window/family data for which **all** terms fall at `x^(1/2+O(epsilon))`, particularly the source-faithful top-excess `Err`, the thick fraction `delta2`, thin size `theta`, and width `b`. Having `m` independent elementary Möbius rows alone does not prove `AskMainBalance`, or the host/automorphic `GrowthInequalityHypotheses`, and does not pay these costs.

## 3. New exact finite native source: high-prime prefix incidence

For every integer R>=2, let X=R^2-1. Rows are actual primes p>R, columns are actual cofactors 1<=c<R, and

```
B_R[p,c] = mu(p*c) if p*c<=X, else 0.
```

`RHLean/Analysis/LargePrimeTTransport.lean` ALREADY proves `LargePrimeTransportData.moebius_mul_eq_neg`:
`mu(p*c)=-mu(c)` because `p>R>c`. Hence

```
B_R[p,c] = -mu(c) * 1_{c<=floor(X/p)}.
```

This exact signed matrix is **not** a model with random signs. It uses actual primes, actual physical endpoint masks, and the actual integer Möbius function. (It is the one-large-prime sector, not the entire frozen-root source or the Lambda convolution; keep the complementary sectors.)

For any increasing squarefree cofactors `q_1<...<q_m<R` such that each quotient interval

```
I_q = (X/(q+1), X/q]
```

contains a prime `p_q>R`, take the `m x m` submatrix with row `p_qi` and column `q_j`. It satisfies **exactly**

```
B[i,j] = -mu(q_j) if j<=i, else 0.
```

Thus `B=L*D`, where `L[i,j]=1_{j<=i}` and `D[j,j]=-mu(q_j)` are diagonal +/-1 signs.

### Complete algebraic consequences (no independence assumptions)

1. `det(B) = product_j(-mu(q_j)) in {+1,-1}`: unimodular integral minor, so no determinant/index loss in this *selected integer lattice*. Analytic normalizations and geometric weights may create additional costs.
2. `B^{-1}=D^{-1}(I-S)`, where `S` is the strict subdiagonal shift. `||I-S||_op <= 2`, `||D^{-1}||_op=1`; hence

   `||Bv||_2^2 >= (1/4)*||v||_2^2`, all real/complex `v` (uniform coercivity).

   Equivalently, if `z_i=sum_{j<=i}(-mu(q_j))*v_j`, then `(-mu(q_i))*v_i = z_i-z_{i-1}` (z_0=0), and `sum_i |v_i|^2 <=4 sum_i |z_i|^2` by `|a-b|²<=2|a|²+2|b|²`.
3. The complete (possibly singular) cofactor Gram is

   `Gram_R[c,d] = mu(c)*mu(d)*[pi(floor(X/max(c,d)))-pi(R)]`.

   This preserves all *signed* off-diagonal terms and every high-prime physical mask. For any sorted squarefree c_i, its determinant is

   `prod_i mu(c_i)^2 * H(c_m) * prod_(i<m)(H(c_i)-H(c_(i+1)))`,

   where `H(c)=pi(floor(X/c))-pi(R)`. In particular a missing prime in any necessary quotient band makes the chosen Gram determinant zero. No generic Gram positivity gives strict positivity.
4. Rank of the full high-prime matrix equals the number of distinct physical quotient rows `floor(X/p)` that introduce at least one new cofactor `c` with `mu(c)!=0`. It is <=`R-1`, even though there are `asymp R²/log R` rows. The repeated rows are genuine redundancy. Do not infer the lift count from the number of high primes.
5. A fixed positive fraction of squarefree cofactors always exists in intervals `[Q,2Q]` as `Q->infinity`, since `sum_{n<=Q}mu(n)^2=(6/pi²+o(1))*Q`. If we can guarantee prime-occupied quotient intervals for most of them, we obtain a large unimodular minor.

### Independent unconditional rank exponent from established prime-gap mathematics

Julia Stadlmann, *On the mean square gap between primes* (arXiv:2212.10867; also Oxford PhD thesis, Thm. 2.1): for every `kappa>0`,

```
sum_{p_n<=Y} (p_(n+1)-p_n)^2 <= C_kappa*Y^(1.23+kappa)
```

for Y large. This result is external literature, not in RH_Lean's Lean kernel.

Fix `alpha<154/177=0.870056497...`, take `Q=floor(R^alpha)` and `Q<=q<2Q`. The intervals `I_q` above are disjoint, contained in a prime height range `Y~R²/Q=R^(2-alpha)`, and have lengths at least `W~R²/Q²=R^(2-2alpha)`. Every empty `I_q` lies entirely inside a consecutive-prime gap of length at least W. Because the empty I_q are disjoint, the total number of empty intervals is bounded by

```
#empty <= (1/W) * sum_{gaps length>=W} gap
       <= (1/W²) * sum_{gaps below O(Y)} gap²
       <<_kappa Y^(1.23+kappa)/W².
```

Comparing with `Q~R^alpha`, we find

```
#empty / Q << R^(-1.54 + 1.77*alpha + kappa*(2-alpha)),
```

which tends to zero for sufficiently small fixed kappa whenever `alpha<1.54/1.77=154/177`. Since a positive fraction of `[Q,2Q)` are squarefree, at least `c_alpha R^alpha` squarefree q have a matching prime p_q; for large R these primes satisfy `p_q>R`. Taking precisely those q gives an actual integer unimodular minor, and hence

```
rank_R(B_R) >= c_alpha R^alpha, for every alpha<154/177, all sufficiently large R.
```

**Status:** Mathematical consequence of cited established Stadlmann theorem, the density of squarefree integers, and exact finite triangular algebra; NOT currently formalized/imported in Lean. The proof does not assert that `rank(B_R)` is `R^(1-o(1))` or that `Gz` is bounded. The exponent is a **physical source multiplicity exponent**, not a new Mertens/zero exponent.

At physical source scale `x=R²`, this is an unconditional rank `m>>x^(0.4350-o(1))`. If a valid RH_Lean-to-Alpoge *operator error bridge* produced a main term proportional to m and remaining cost of type `x/m`, the rank alone would permit a **conditional** exponent `x^(0.5650+o(1))`; this is a dimensional benchmark, **not** a proved `Gz` bound. The actual structural `SizeWindows` requirement `m>=x^(1/2-epsilon)` still fails for arbitrarily small epsilon. Need near-critical (`m>=R^(1-o(1))`) slots plus all independent analytic costs to reach 1/2.

## 4. Verified finite census (separate from infinite theorem)

`python3 scripts/alpoge_high_prime_unimodular_regression.py` passes exact finite tests:

| R | actual primes above root | distinct floor quotients | rank full B | unimodular minor on q in [R^.8, 2 R^.8] |
|---:|---:|---:|---:|---:|
| 31 | 151 | 21 | 15 | 3 |
| 100 | 1204 | 62 | 44 | 14 |
| 317 | 9565 | 180 | 131 | 35 |
| 549 | 26011 | 317 | 222 | 65 |
| 1027 | 82290 | 565 | 395 | 103 |
| 3000 | 602059 | 1569 | 1122 | 292 |

For each of these, the script verifies all selected row/column physical masks, prime/cofactor conditions, the direct integer Mobius product on a 12x12 submatrix, exact fraction-free determinants +/-1, the signed Gram identity, and sample vector coercivity. It does not extrapolate observed ratios to an asymptotic theorem.

The separate direct square-source census (C program, not part of the proof) computes Alpoge's `Gz(R²-1)` for every `2<=R<=3000` and finds both signs (1864 positive, 1135 negative; first negative R=147). Therefore `Gz>=0` and `Gz<=0` are both FALSE as proposed unconditional signs. The one-sided target is a growth bound, not a pointwise sign assertion.

## 5. EXACT UNPAID BRIDGE TO THE HARD THEOREM

1. **Supplier A — signed source**. Retain the complete `Lambda=mu DirichletConvolution log` source, the principal `Gz`, the surviving high-prime prefix sector, the missing/dilated high-prime compensators, the LOW/LOW and HIGH/HIGH masks, all mixed orientations, and the virtual finite-Euler divisors. A `B_R` Gram is a proper sector, **not** the full arithmetic trace.
2. **Supplier B — near-critical multiplicity**. Improve `m>=R^alpha (alpha<154/177)` toward `R^(1-o(1))`, either with a stronger quotient-interval prime occupancy theorem or through additional arithmetic lifting beyond one-high-prime masks. Establish actual independent selected directions, not merely high-prime rows.
3. **Supplier C — response upper estimate**. Prove a source-faithful inequality that upper-controls the *complete response energy* of these directions by `Err` with all geometrical and signed returns. **Coercivity is a LOWER bound and cannot by itself upper-bound `Gz`**. The `m` gain is only real after `Err`, `b`, `delta2`, `theta`, and all costs are paid. No reliance on Masullo's unproved global nuclearity or cutoff interchange.
4. **Consumer**. Apply the existing external one-sided Landau result to a globally uniform square-block `Gz` bound, or supply an independent Lean bridge into `EnvelopeBound (2-delta) 0` on the original strict historical `K_R`; do not conflate `Gz` and Mertens's growth exponents without an analytic transfer.

**This improves the concrete unconditional physical-source multiplicity theorem but DOES NOT yet improve RH_Lean's global Mertens exponent or prove RH.** Add as independently sourced rank/coercivity branch to the existing proof DAG only after exact-head Lean audit; preserve the November 20 seven-agent task and all source guards.

## 6. **The essential signed-source correction: Lambda_2, not Lambda**

The ordinary von Mangoldt function vanishes at every distinct semiprime `p*q`:
`Lambda(p*q)=0`. Thus the highly independent `mu(p*q)` channel **does not survive** first-order `Lambda=mu*log` convolution. Treating the integer minor above as independent contributions to Alpöge's `Gz` would be a source violation; the ghost mass must be returned with its exact negative omitted-divisor compensator, giving zero.

There is, however, an existing, certified *second-order* RH_Lean source in which precisely these semiprimes survive:

- `RHLean/Analysis/LogWeightedPrimeExtensionEndpoint.lean`:
  `nativeLambdaTwo_eq_logWeight_vonMangoldt_add_convolution` proves `Lambda_2 = Lambda*log + Lambda*Lambda`, with `Lambda_2=mu*log^2`.
- `RHLean/Analysis/NativePNTSignedSecondSelbergWheelFrontier.lean`:
  `nativeLambdaTwo_mul_distinct_primes` and
  `nativePNTSignedSecondSelbergKernel_mul_distinct_primes` prove, for different primes,
  `Lambda_2(p*q) = K_2(p*q) = 2 log p log q`, where
  `K_2=Lambda*Lambda-Lambda*log`.
  The same file certifies the **negative** prime-square diagonal
  `K_2(p^2)=-(log p)^2`. The full signed source must keep both faces.

Select now **prime** cofactors `q_i` rather than merely squarefree cofactors.
The prime-gap-moment empty-band estimate is polynomially smaller than
`Q/log Q` when `alpha<154/177`, while the PNT gives `>>Q/log Q` prime
cofactors in `[Q,2Q]`. Thus for all large R, the actual physical source
admits **m >>_alpha R^alpha/log R** matched *prime/prime* channels, with no
additional conjecture and without assuming that every quotient band contains a prime.

On the same selected rows and columns, define the **signed second Selberg
source** matrix, retaining the literal endpoint mask:

```
C_ij = K_2(p_i*q_j) 1_(p_i*q_j <= X_R)
     = 2*log(p_i)*log(q_j) * 1_(j<=i)
     = diag(2*log(p_i)) * L * diag(log(q_j)).
```

This is a full coefficient of the actual Selberg source, not an invented
positive weight. Because the row/column logarithms are positive, the
normalised matrix is the *same integral unit-prefix matrix*. In particular,

```
||C v||_2 >= (min_i log p_i)*(min_j log q_j)*||v||_2
         >= log(R)*log(Q)*||v||_2
```

for every real or complex selected vector, using `||L^(-1)||<=2`.
The constant is **independent of m and the physical prime spacing**.

This is a genuine second-order signed-source coercivity theorem on
`m>>R^(154/177-o(1))/log R` channels, modulo the established external
prime-gap-moment theorem for the count. It is not a new theorem about the
complete first-order `Gz` error.

**First unpaid estimate is now precise:** build a source-faithful quantitative
upper response-energy estimate for the **complete signed second Selberg
source** (including square diagonal, all other prime factors, LOW/HIGH and
mixed masks, cutoff and geometric costs) that, together with this lower
coercivity, forces Alpöge's **one-sided** `Gz(X_R)=O_epsilon(R^(1+epsilon))`
or RH_Lean's verified historical `EnvelopeBound` consumer. Merely
dividing by `m` in a separately bounded positive semiprime term is invalid:
the diagonal and compensating pieces may cancel the gain.

The new Lean module contains a selected-matrix prefix theorem directly
for `nativePNTSignedSecondSelbergKernel`, reusing the existing
`nativePNTSignedSecondSelbergKernel_mul_distinct_primes` declaration.
Compile status is governed only by exact-head CI; do not claim this new
declaration Lean-certified until it passes.
