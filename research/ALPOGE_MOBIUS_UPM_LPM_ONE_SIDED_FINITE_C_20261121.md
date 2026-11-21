# Alpöge four-colour ASK + Möbius UPM/LPM: a one-sided terminal criterion

**2026-11-21.** Mathematical status: unconditional finite algebra, classical published one-sided Landau lemma, and **NEW CONDITIONAL RH IMPLICATION**. The original one-sided arithmetic bound remains **OPEN**. Do not label RH proved, or infer an estimate from finite samples. The Lean reconstruction of the algebra is `RHLean/Analysis/AlpogeMobiusPartialMoments.lean` (PR #1169; exact-head CI required). The analytic one-sided Landau lemma is NOT imported into Lean.

## 1. Actual sign-split carriers and two physical walls

For R>=2, X=R^2-1, strict historical `K_R=max_(0<=y<R) (M(y)-1)^2/(y+1)`, define `w_R(n)=1` below R and `-1` on [R,X]. Then

    Q_R = 2*M(R-1)-M(X) = sum_(1<=n<=X) w_R(n)*mu(n).

Let `mu_+(n)=(mu(n)^2+mu(n))/2`, `mu_-(n)=(mu(n)^2-mu(n))/2`. These are nonnegative, supported on squarefree integers and sum to `mu(n)^2`.

For any *nonnegative* original Alpöge colour projector `P(n)`, set

    U_P(R) = sum_(1<=n<R) P(n) mu_+(n)
           + sum_(R<=n<=X) P(n) mu_-(n),
    L_P(R) = sum_(1<=n<R) P(n) mu_-(n)
           + sum_(R<=n<=X) P(n) mu_+(n).

Then EXACTLY (without norm, geometry or probabilistic independence)

    Q_P(R)=sum_(n<=X) w_R(n) mu(n)P(n)=U_P(R)-L_P(R),
    T_P(R)=U_P(R)+L_P(R)=sum_(n<=X) P(n)mu(n)^2,
    Q_P(R)^2=T_P(R)^2-4*U_P(R)*L_P(R).

The historical wall swaps positive and negative Möbius contributions. Ordinary separate UPM and LPM upper bounds discard the decisive cross product `U_P L_P`.

The Lean file defines the full UPM1, LPM1, their signed difference, complete total mass and exact cross-square equality using existing `FinitePartialMoments.lean`. Its n=1 seed is handled separately because `log 1=0` in `mu*Lambda=-mu log`.

## 2. Eight nonnegative channels, keeping ramified 2,q,d

Let `a(n),b(n)` be the two real quadratic character/inertia response coefficients of Alpöge's `primVal` (assume values in [-1,1], including zero at a locally nontrivial inertia restriction). For signs `s,t in {+1,-1}`, define

    P_st(n)=(1+s*a(n))*(1+t*b(n)) >= 0.

There is a **pointwise partition of unity** even when `a` or `b` is zero:

    P_++ + P_+- + P_-+ + P_-- = 4.

Therefore every n contributes to the eight nonnegative populations

    P_st(n)*mu_+(n), P_st(n)*mu_-(n)

and the complete original principal channel is EXACTLY recovered:

    4*Q_R = sum_(s,t) (U_st(R)-L_st(R)).

This is a formal algebraic partition, **not** an assertion that one selected colour suffices or that the abstract `a,b` have been identified with all concrete Frobenius/inertia choices in #1166. There is no dropped bad-prime coefficient: at `a=0`, the two a-sign weights both equal 1, and similarly at `b=0`. Such terms are counted with their actual soft weights, not declared absent.

The third parity bit is `lambda(n)=(-1)^Omega(n)` on squarefree n, with `mu(n)=mu(n)^2*lambda(n)`. Unlike the first two quadratic characters, `lambda` has no fixed finite conductor. Thus finite-coset orthogonality on the original Frobenius group does not automatically average away this parity bit.

## 3. Exact arithmetic of the new **one-sided finite-C criterion**

**Claim (paper theorem, conditional arithmetic supplier).** Fix `0 <= kappa < 1` and ONE fixed `sigma in {-1,+1}`. Suppose for every eps>0 there is a finite constant `C_eps` independent of R such that

    sigma * Q_R <= C_eps * R^(1+eps) * K_R^kappa   (all R>=2).

Then RH holds.

The special `kappa=1/2`, eps=0 and a single absolute C is **one-sided finite C**. In the UPM/LPM coordinates this demands ONLY one of the two inequalities `U_1(R)-L_1(R) <= C R sqrt(K_R)` or `L_1(R)-U_1(R) <= C R sqrt(K_R)`. The sign may not depend on R.

### Proof (using classical Landau, no circular new estimate)

Let `Theta` be the supremum of real parts of nontrivial zeros of the Riemann zeta function. Use the known RH_Lean growth/zero dictionary `M(x)=O_eta(x^(Theta+eta))`, and `1/2<=Theta<1`. For every positive eta, this implies

    K_R <<_eta R^(2*Theta-1+eta), 
    M(R-1) <<_eta R^(Theta+eta).

The assumed fixed-sign Q bound, together with `Q_R=2M(R-1)-M(R^2-1)`, gives

    -sigma*M(R^2-1)
       <= C_eps R^(1+eps) K_R^kappa + 2 |M(R-1)|
       <<_eta R^(1+kappa*(2Theta-1)+eta).

The exponent of the historical `M(R-1)` term is smaller, since `Theta<1` and `kappa>=0`. Since the square endpoints differ by O(R) and `|mu(n)|<=1`, this extends to all real x:

    -sigma*M(x) <<_eta x^(1/2+kappa*(Theta-1/2)+eta).

For the ordinary Riemann zeta function there are NO real zeros in (0,1). The classical Landau positivity theorem therefore implies that **either fixed-sign** one-sided estimate `M(x)<=C x^beta` or `-M(x)<=C x^beta` forces `Theta<=beta`: otherwise an off-real-zero pole of `1/zeta(s)` would contradict positivity of the Mellin integral `int_1^inf (C x^beta +/- M(x))*x^(-s-1) dx` and Landau's rightmost-real singularity principle. This is the ordinary-zeta specialization of Proposition 2.6 in the 2024 paper `On a Mertens-type conjecture for number fields` (DOI: 10.1017/S0305004124000306).

Thus

    Theta <= 1/2 + kappa*(Theta-1/2).

Because `kappa<1`, `Theta<=1/2`. Functional-equation symmetry gives RH.

**For finite C kappa=1/2:**

    Theta <= 1/4 + Theta/2,

so one-sided historical amplification closes directly. The one-sided condition is weaker than the original two-sided finite C and need not imply the original stronger finite-A statement; it is independently sufficient for RH via Landau.

### Scope and missing Lean bridge

The finite UPM/LPM algebra and original `Q_R` source bridge are in RH_Lean. The **one-sided Landau Mellin positivity theorem** is classical, but not presently established as a Lean declaration in RH_Lean. It must be imported or reconstructed to mark the new full conditional consumer kernel-certified. The quantitative one-sided `Q_R` estimate is still **not proved**.

## 4. Exact finite census (not an all-R estimate)

The four-colour example uses quadratic `a=chi_5,b=chi_3`, `P=(1-a)(1+b)`, and the genuine integer Möbius sieve:

| R | four-colour UPM1 | four-colour LPM1 | Q_P | principal UPM1 | principal LPM1 | original Q_R |
|---:|---:|---:|---:|---:|---:|---:|
| 56 | 932 | 988 | -56 | 950 | 960 | -10 |
| 317 | 30572 | 30549 | +23 | 30558 | 30536 | +22 |

Both populations are genuinely positive and O(R^2); their difference is small in these **finite samples only**. No proof that this persists at all R has been obtained.

## 5. New specific proof task

Instead of the previous *two-sided* finite C, seek ONE fixed orientation:

    (UPM1 - LPM1)(R) <= C_eps R^(1+eps) K_R^kappa
    OR
    (LPM1 - UPM1)(R) <= C_eps R^(1+eps) K_R^kappa,

for any `kappa<1`, after complete four-colour reconstruction of the principal source including all exceptional 2,q,d coefficients and both walls.

Alpöge's finite character positivity can now be used in the *individual nonnegative parity populations*, and only a single large deviation direction must be forbidden. The nonperiodic Liouville parity and its full cross-owner transport remain the essential arithmetic work: the finite-coset projector does not alone supply the estimate.
