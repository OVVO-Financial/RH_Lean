# Original Euler fractional cancellation: audited historical one-sided carrier

2026-10-27. Status: exact source code **draft** until dedicated warning-fatal CI is green. The independent rational checks are finite certificates; this document does not assert finite C or RH.

## 1. Original signed decomposition (no asymptotic replacement)

Fix R >= 2, N=R-1, X=N(R+1)=R^2-1, and original Mobius mu. Write S_N=sum_(a<=N) mu(a)/a and

- Q_R = sum_(a,b<=N) mu(a)mu(b) floor(X/(ab)),
- F_diag = sum_(b<=N) mu(b)^2 {X/b^2},
- F_off = sum_(1<=a<b<=N) mu(a)mu(b){X/(ab)}.

Then exactly

    Q_R = X*S_N^2 - F_diag - 2*F_off,

and 0<=F_diag<=N. The fractional part is the Euclidean rational remainder (X mod d)/d for positive d. This means the diagonal is already inside the finite-C budget with NO K_R loss.

These are the native genuine-Mobius source weights, not independent generic variables.

## 2. The nonzero continuous Abel corner

If D_cont and B_cont denote the ORIGINAL #1034 triangular Mertens forms with each floor replaced by its continuous value, then

    D_cont + 2*B_cont = X*S_N^2 - (X/R^2)*M(N)^2.

The terminal corner is nonzero for the continuous kernel, despite being zero in the discrete kernel. The raw fractional square identity automatically restores this corner; do not discard or separately estimate it.

## 3. Exact rank-one historical subtraction

The already-compiled Mobius inversion theorem states

    sum_(a<=N) mu(a)floor(N/a) = 1.

For positive a,b define the non-symmetric kernel

    T_R(a,b) = floor(X/(ab)) - (R+1)/b * floor(N/a).

For the original Q_R,

    Q_R = (R+1)*S_N + sum_(a,b<=N) mu(a)mu(b)T_R(a,b).

The *pointwise* identity is

    T_R(a,b) = (R+1)/b * {N/a} - {X/(ab)}.

This is exact, not a mean-zero or norm statement. The previously obtained independent historical estimate

    |S_N| <= 20 (K_R/N)^(1/3)

would pay the linear term at <=60 R^(2/3) K_R^(1/3) <=60 R sqrt(K_R). This rational reciprocal estimate is a PAPER argument and should not be called Lean-certified until its own proof compiles.

## 4. A source-specific subpower sector already paid

If a divides N, then {N/a}=0, so

    T_R(a,b) = -{X/(ab)},   0<= -T_R(a,b)<1.

Thus for the entire genuine signed divisor-row part,

    |sum_(a|N)mu(a) sum_(1<=b<=N)mu(b)T_R(a,b)|
       <= N * #{a|N:mu(a)!=0} <= N*tau(N).

The classical all-epsilon divisor bound tau(N)=O_epsilon(N^epsilon) gives

    divisor-row source = O_epsilon(R^(1+epsilon))

UNCONDITIONALLY, independent of K_R. Because K_R>=1, this sector fits a subcritical R^(1+epsilon)K_R^(1-eta/2) budget for every fixed 0<eta<=2. The full kernel is not bounded: NON-DIVISOR a is the unresolved complementary sector. This is an honest arithmetic saving on a strict subfamily, not RH.

## 5. Exact high-product geometry

On the band X/2<ab<=N^2, floor(X/(ab))=1. Thus the continuous and fractional parts cancel to **+1**, NOT -1. The surviving signed contribution is sum mu(a)mu(b) over the band, which is NOT controlled by support geometry.

Do not apply first-owner local diagonal contraction to this additive band without the original mask/corner and occurrence-correct owner map; the prime q^2 daughter index, integer minFac, and Gram first-separating owner are three distinct indices.

## 6. Quantitative status and next proof obligations

Already available as paper finite arguments (not yet compiled into this branch):

    X*S_N^2 <= 640 R^(4/3)K_R^(2/3)
    |D-D_cont| <=64 R^(6/5)K_R^(4/5).

These are independent improvements for separate components, but by themselves are too large in R to prove a finite-C or fixed-eta whole-amplitude estimate.

A source-faithful successor has to control the mixed NON-DIVISOR rows of T_R and retain their signed interactions with the divisor rows, or directly prove

    |X*S_N^2 - 2*F_off| <= C R sqrt(K_R)

(uniform finite-C), or the weaker historical nonlinear budget with a fixed eta>0. Bounding the continuous square and F_off separately is not admissible unless both bounds already meet the target independently.

Finite independent checks were performed with exact rational arithmetic at R=2,3,7,15,21,56,100,317,500. All proposed exact identities and the divisor-row formula passed.

The b={1,3,5} signed-cross negativity bound discussed in prior analysis is strictly negative starting at R=21 (not R=15 or only R>=25), by direct integer-floor computation; a formal all-R proof still needs the coarse tail and finite endpoint cases.

## 7. Lean dependency provenance

- #1034: research/EULER_HYBRID_TRIANGULAR_GRAM_20261027.lean (merged, certified exact Q=D+2B)
- research/EULER_FRACTIONAL_COUPLED_20261027.lean (new original fractional Gram, Euclidean fraction, diagonal bound)
- research/EULER_RANK_ONE_FRACTIONAL_ROWS_20261027.lean (new Mobius inversion rank-one, exact divisor rows)
- RHLean/Analysis/NativePNTMertens.lean::nativeSumMoebiusMulFloor (existing certified Möbius inversion)
- #1035 original pointwise terminal bridge remains a separate draft PR and is not used to invent any new quantitative estimate.

No `sorry`, `admit` or new `axiom` permitted; exact-head Lean4.34.1 CI will report kernel certification separately.
