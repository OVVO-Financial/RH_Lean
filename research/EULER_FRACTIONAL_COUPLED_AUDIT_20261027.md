# Original Euler fractional cancellation: audited historical one-sided carrier

2026-10-27. Status: exact fractional and rank-one Lean source compiled under warning-fatal CI and standard-axioms audit at PR #1036 head `fe34e12`. This mathematical note adds separately proved paper-level arithmetic consequences not yet all formalized. It does not assert finite C or RH.

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

## 8. Euclidean carry-phase coordinate (original kernel, no estimates)

Let L=R+1, q_a=floor(N/a), t_a=N mod a, and
rho_(a,b)=(L*q_a) mod b. Then N=a*q_a+t_a and
L*q_a=b*floor(L*q_a/b)+rho_(a,b). Thus exactly

    T_R(a,b) = floor((a*rho_(a,b)+L*t_a)/(a*b)) - rho_(a,b)/b.

This separates the **integer carry** and the **congruence phase** while keeping
their signed correlation. Neither summand is automatically small after summing
over the genuine coefficients. In particular the carry can exceed 1 for small b.

- If a|N, then t_a=0 and the carry vanishes.
- If b|(L*q_a), then rho_(a,b)=0 and T_R(a,b)=floor(L*t_a/(a*b))>=0.
- If both conditions hold, T_R(a,b)=0 exactly.
- At a=1, T_R(1,b)=-{X/b}; the signed first row is minus the
  original PNT-first lattice sum Phi_R of
  research/PNT_FIRST_LAMBDA_HYPERBOLA_ANCHOR_20261018.lean.
- At b=1, T_R(a,1)=floor(L*(N mod a)/a), an integer carry.

These are occurrence-preserving arithmetic subcases, not an operator-norm
contraction or a fixed eta.

## 9. NEW UNCONDITIONAL ROOT-SCALE PAYMENT: TOP SQRT(R) FULL ROWS

For 1<=b<=N, let Y_b=floor(X/b) and define the **entire** signed row

    G_R(b)=sum_(a=1)^N mu(a)*T_R(a,b).

Use the exact nested-floor identity floor(X/(a*b))=floor(Y_b/a),
and complete finite Möbius inversion at Y_b:

    sum_(a<=Y_b) mu(a)floor(Y_b/a)=1.

Here Y_b>=N for every b<=N. The row is therefore

    G_R(b)=1-L/b
           -sum_(n=N+1)^Y_b mu(n)*floor(Y_b/n).          (ROW)

When b>=ceil(R/2), Y_b<2R, and every floor in the omitted tail
equals 1. Hence the signed row is EXACTLY

    G_R(b)=1-L/b-[M(Y_b)-M(N)].                          (TOP)

Now write b=N-j, 0<=j<=N/2. Since L-b=j+2,

    Y_b-N <= N*(L-b)/b = N*(j+2)/(N-j) <= 2*(j+2),

and

    |1-L/b|=(j+2)/(N-j) <= j+2.

With |mu(n)|<=1 we obtain the uniform bound

    |G_R(N-j)| <= 3*(j+2).                               (LOCAL)

Let H=floor(sqrt R). For all R>=5, H<=N/2+1 and the
H distinct values b=N-H+1,...,N satisfy 0<=j<=H-1<=N/2.
Therefore, using |mu(b)|<=1,

    |sum_(b=N-H+1)^N mu(b)G_R(b)|
       <= 3*sum_(j=0)^(H-1)(j+2)
       = (3/2)*H*(H+3)
       = O(R).                                            (PAID)

This is a **quantitative** source-specific root-scale estimate for a
complete upper boundary strip, with NO dependence on K_R, PNT, zero
regions, or assumptions on M(Y_b). The bounded strip arises by
performing the full genuine inner Mobius inversion BEFORE taking any
absolute value.

Independent exact-floor verification (reported as rounded decimals):

    R    H    signed upper-row sum    proven abs bound
    56   7       -0.0785                  105
    100  10      +12.7077                 195
    317  17       -9.1433                 510
    500  22       -5.0544                 825
    1000 31      -13.9310                1581
    2000 44      +13.9109                3102

The finite checks were carried out on the ORIGINAL Mobius coefficients
and actual floor quotients. They are not substituted for proof.

### What is left after the two independent payments

Define R_div as the signed contribution from all rows a|N,
and R_top as the contribution of all b>N-H, including those a|N.
The intersection of these sets is counted in both, so avoid
double counting by using the disjoint partition:

    A = {(a,b): 1<=a,b<=N, a|N}
    B = {(a,b): 1<=a,b<=N, a does NOT divide N, b>N-H}
    C = {(a,b): 1<=a,b<=N, a does NOT divide N, b<=N-H}.

The full rank-one residual equals the three signed restrictions.
The A contribution is O_epsilon(R^(1+epsilon)) by the divisor-row bound
and tau(N)=N^o(1). The B contribution is O(R)+O(H*tau(N)),
since B is the full paid top strip minus its divisor-row intersection.
Thus both A and B fit O_epsilon(R^(1+epsilon)) WITHOUT K_R.

The remaining independent target is the complete original signed
C-contribution. Any fixed-eta historical estimate for C,

    |sum_((a,b) in C) mu(a)mu(b) T_R(a,b)|
      <= C_(eta,epsilon) R^(1+epsilon) K_R^(1-eta/2),

for some eta>0 (and every epsilon>0), would activate the nonlinear
square-root amplification route **provided** the independently controlled
linear mode (R+1)*S_N is included with the correct budget.
The target is OPEN. The local payments are genuine but do not by
themselves infer a uniform fixed eta for the full source.

The q^2 daughter index, integer least-prime divisor, and Gram first-separating
owner are distinct; this source must be paired with their actual occurrence
weights before applying the reciprocal-operator contraction.
