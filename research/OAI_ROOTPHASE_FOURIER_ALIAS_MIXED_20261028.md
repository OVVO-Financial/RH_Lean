# Original Möbius root-phase harmonics: exact aliasing, fourth-moment opportunity, and the cross-mode obstruction

2026-10-28. Independent direct source research supplement to PR #1048. This note addresses the three proposed extensions of the sharp square-block / NNS bridge without silently discarding harmonic covariance.

Original pinned OpenAI reference: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Primary RH_Lean source bridge: merged PR #1047.
The ongoing PR #1048 already proves the NNS LPM4+UPM4 exact moment identity, finite Cauchy, the *conditional* 1/8 fourth-grid budget, and original Mobius perfect-square zero. Do not duplicate or present them as a new analytic moment saving.

## 1. Three-line exact first-derivative root-grid trace

Let H>=2, u_R=2 log R and h_R=u_(R+1)-u_R. Then

    1/H <= h_R <= 2/H, H<=R<2H.

For a locally absolutely continuous F and any v in I_R=[u_R,u_(R+1)], the fundamental theorem for |F|^2 implies

    |F(u_R)|^2 <= |F(v)|^2 + 2*integral_(I_R)|F||F'|.

Average in v and use 1/h_R<=H. The intervals I_R are DISJOINT, so summing gives

    sum_R |F(u_R)|^2
      <= H*integral_I |F|^2+2*integral_I |F||F'|
      <= H*||F||_(L2(I))^2+2*||F||_(L2(I))*||F'||_(L2(I)).

The same proof with |F|^4 instead gives

    sum_R |F(u_R)|^4
      <= H*||F||_(L4(I))^4+4*||F||_(L4(I))^3*||F'||_(L4(I)).

For a globally T-bandlimited F with a global L4 Bernstein estimate
||F'||_4 <= const*T*||F||_4, this yields

    sum_R |F(u_R)|^4 <= (H+C*T)*||F||_(L4(R))^4.

(For the L2 statement, use global Plancherel. Localized smooth source moments require buffer/tail control.)

Then Cauchy gives

    (sum_R |F(u_R)|^2)^2 <= H*sum_R |F(u_R)|^4.

Under an INDEPENDENT, properly normalized continuous fourth-root-moment
H*||F||_4^4 << H^(4-2delta0), the second-moment grid tax would be
(T/H)^(1/2)=H^(1/8+delta/4+kappa/2), and the power budget would be

    delta0 >= 1/8+5delta/4+kappa/2
                  + beta4/2*(1/4+delta/2+kappa).

THIS DOES NOT FOLLOW from a smooth L2 source estimate. The required
continuous L4 source estimate is much stronger in concentrated/spiky
situations. Also the pinned theorem
source_batch_plain_marked_fine
controls actual products of marked Hecke polynomials SUMMED OVER ROWS,
not the physical sample moment
    H*||F(root shift)||_4^4.
A new original-source and normalization bridge is necessary.

## 2. Exact ROOT-index Parseval: no smoothing, no independent signs

For the original Möbius sequence and H>=2 set

    A_H(theta)=sum_(n=H²)^(4H²-1)
          mu(n)*exp(2*pi*i*theta*floor(sqrt n)).

Since floor(sqrt n)=R exactly on [R²,(R+1)²),

    integral_(theta=-1/2)^(1/2)|A_H(theta)|²dtheta
       =sum_(R=H)^(2H-1) |Delta_R|².

This is also H*(NNS-LPM2(0)+NNS-UPM2(0)), with the empirical distribution
formed from the ORIGINAL deterministic R-sampled Möbius block totals.

## 3. Fourier expansion of the fractional-root step phase

Let u>=0 and theta in [-1/2,1/2]. The exact identity is

    exp(2*pi*i*theta*floor u)
       = exp(2*pi*i*theta*u)*f_theta(u),

where f_theta(u)=exp(-2*pi*i*theta*{u}) is 1-periodic.
The Fourier coefficients for mode k in Z are

    c_k(theta)
       = integral_(v=0)^1 exp(-2*pi*i*(theta+k)*v)dv
       = (1-exp(-2*pi*i*theta))/(2*pi*i*(theta+k)),

with the removable value c_0(0)=1 and c_k(0)=0 for k!=0.

At noninteger u, the BV Fourier series converges to

    exp(2*pi*i*theta*floor u)
       =sum_(k in Z) c_k(theta)
                      exp(2*pi*i*(theta+k)*u).

For |k|>=1 and |theta|<=1/2, |c_k(theta)|<=2/(pi*|k|).
Consequently the INDIVIDUAL DIAGONAL coefficient-squares decay
like 1/k². THIS ALONE DOES NOT diagonalize the square of the mode sum.

At integer u=m the Fourier series generally converges to the
left/right midpoint (rather than the right-continuous step value).
But in the genuine Möbius sum the integer-root sites are exactly
n=m²>=4, and mu(m²)=0. Thus NO perfect-square jump correction is
needed after full integer norm-fiber reassembly. This is an exact
Möbius-specific advantage over a generic coefficient sequence, and
is certified independently in ongoing PR #1048.

Therefore for every fixed H>=2 and almost every theta, the ORIGINAL
sharp root-phase sum is exactly the coherent limit of the smooth modes

    A_H(theta)=lim_(K->infty) sum_(|k|<=K)
                    c_k(theta) V_H(theta+k),

    V_H(xi)=sum_(n=H²)^(4H²-1)
               mu(n)*exp(2*pi*i*xi*sqrt n).

The fixed finite sum over n allows Fourier inversion to pass through
the n-sum; control for theta integration is available by standard
bounded-variation Fourier convergence for the finitely many
noninteger roots. No new random process is involved.

## 4. Critical warning: the k-modes are NOT orthogonal

The exact squared moment is

    integral |sum_k c_k(theta)V_H(theta+k)|²dtheta
      =sum_(k,l) integral c_k(theta)*conj(c_l(theta))
           V_H(theta+k)*conj(V_H(theta+l))dtheta,

under an appropriate convergent truncation/limit.

The terms k!=l are not zero by any available orthogonality law.
Their signs and correlations are precisely part of the ORIGINAL
Euler compensation mechanism. One CANNOT replace the expression by
sum_k |c_k|²*integral |V_H(theta+k)|² dtheta without proving
a new diagonalization theorem (which is false in general).

A genuine-Möbius finite witness shows how bad diagonalization can be.
Both n=5 and n=6 lie in the shell [4,9), with mu(5)=-1,mu(6)=+1.
Their TWO-SITE exact root-phase is

    -exp(2*pi*i*theta*2)+exp(2*pi*i*theta*2)=0
    for ALL theta.

But at smooth frequency xi,

    V_pair(xi) = -exp(2*pi*i*xi*sqrt 5)
                   +exp(2*pi*i*xi*sqrt 6),

which is generally nonzero. Thus
    integral sum_k |c_k(theta)V_pair(theta+k)|² dtheta > 0,
although the fully recombined physical energy is EXACTLY ZERO.
The missing NEGATIVE cross-mode terms pay ALL the diagonal energy.

The new Lean module proves μ(5)+μ(6)=0, their common physical square
shell, the vanishing physical two-site source for any common phase,
the nonzero smooth-mode source for distinct phase values, and the
general no-diagonal-orthogonality lemma.

The companion numerical script checks using genuine μ(5),μ(6):
with K=200 and θ-integration, diagonal harmonic energy is about
0.4258 while the full coherent truncated sum is about 2.5e-6.
As K grows, the coherent physical answer converges to zero, NOT
to the positive harmonic diagonal energy. This is a TEST of the
claimed mode-diagonal step, not evidence of RH exponent improvement.

## 5. Actual Mellin phase of each smooth root harmonic

For the smooth mode exp(2*pi*i*xi*sqrt x) on
x in [H²,4H²), define its Mellin frequency kernel

    M_(xi,H)(t)=integral_(H²)^(4H²)
       exp(2*pi*i*xi*sqrt x)*x^(-it)dx/x.

The exact substitution y=sqrt x gives

    M_(xi,H)(t)=2*integral_H^(2H)
       exp(2*pi*i*xi*y)*y^(-2it)dy/y.

Its phase is 2*pi*xi*y-2*t*log y, with derivative

    d/dy phase = 2*pi*xi-2*t/y.

Thus stationary phase requires

    t=pi*xi*y, y in [H,2H].

The natural frequency scale is |t|~|xi|*H:
- principal k=0, |theta|<=1/2: |t|<=pi*H;
- modes |k|>=1: |t|~|k|*H.

This is NOT compact Mellin support: the sharp outer global endpoints
also yield off-stationary tails, which require explicit estimates or
outer-endpoint smoothing. It DOES avoid introducing H interior
square-block collar transitions.

The original pinned OpenAI inverse/raw moment theorem has
C*(1+height)^J for its specified row data and smooth profile family.
The marked fourth theorem bounds a different Hecke-row product;
neither as currently stated pays for arbitrary V_H(theta+k),
uniformly in k, with the full mixed k!=l covariance.

## 6. Source-level next theorem; do not claim mere re-expression is payment

The exact Fourier / Mellin identity suggests an honest new target:
derive an independent, uniform compensated mixed-root-phase moment
on the ORIGINAL quadratic norm-fiber coefficients,

    integral_(-1/2)^(1/2)
      |lim_K sum_(|k|<=K)c_k(theta)
           sum_(H²<=md<4H²) a_F(m)*chi_-3(d)
               exp(2*pi*i*(theta+k)*sqrt(md))|² dtheta
           << H^(5/2-delta), delta>0,

with all k!=l interactions intact. This expression is E_sharp(H)
by exact algebra; the display is the THEOREM TO BE PROVED, not
an independent estimate already obtained from OAI.

More useful as an intermediate lemma: provide a uniform bilinear
large-sieve estimate for k,l mode pairs in the ACTUAL marked,
rescaled-compensated source; or directly prove a sharp-root-index
quartic moment by transporting OAI's marked fourth source with all
normalizations. Every step must retain all ideal labels, phases,
selected-prime masks, conductor guards and the actual cosine/kernel
frequency supports.

**Verdict:** first-derivative trace is correct and fourth-moment
half-cost is conditional. Perfect-square Fourier jump payment is ZERO
for actual Möbius. The naive k^-2 mode diagonalization is FALSE even
on genuine two-site Möbius subpopulations. Preserving the signed
harmonic cross-mode covariance is essential; root-phase Fourier
representation does not supply a new power saving on its own.


## 7. NEW: the outer-support smoothing cost is O(W²), not O(H W²)

This is a real improvement in the root-phase Fourier coordinate that does
not require a new OAI moment theorem. The exact phase
exp(2*pi*i*theta*floor(sqrt n)) has already encoded ALL internal H square
walls, so there is NO reason to smooth each square shell separately.

Instead, smooth only the global endpoints of the full dyadic support
[H²,4H²). Let W>=1, and let a smooth physical outer mask agree with
1 on [H²+W,4H²-W], taper in two collars of width W, and vanish outside
the original support. The discrepancy from the ORIGINAL sharp phase
is supported on at most

    |[H²,H²+W) union [4H²-W,4H²)| <= 2W

actual integers. For any theta, after reassembling the original Mobius
norm fibers and using |mu(n)|<=1, |phase(n,theta)|=1 and a taper in [0,1],

    |A_H(theta)-A_H,outerSmoothed(theta)| <= 2W.

Taking the theta integral over an interval of length one gives

    integral |A_H-A_H,outerSmoothed|² <= 4W².

Consequently (triangle inequality in L²(theta)):

    E_sharp(H) <= 2*integral |A_H,outerSmoothed|²+8W².

Choosing W~H pays an OUTER rounding cost O(H²), which is below the
H^(5/2-delta) power-saving budget for any delta<1/2. In contrast,
smoothing H distinct blocks independently at width W~H would pay
O(H^3) and destroy the saving.

This removes the GLOBAL support-collar part of the earlier Tax 1.
At physical x~H², W~H costs log width ~W/H²~H^-1, so the Mellin
frequency needed for these TWO OUTER SUPPORT CUTS is only O(H),
NOT H^(5/4+...). Crucially the INTERNAL sharp boundaries remain
encoded in the k!=0 fractional-root harmonic modes, whose effective
frequency remains |t|~|k|H. One cannot conclude the entire source
only needs t=O(H).

The Lean module OAI_ROOTPHASE_TWO_OUTER_COLLARS_20261028.lean proves:
- exact two-collar site cardinality <=2W for ALL H,W;
- any complex coefficient error of per-site norm <=1 has total
  absolute amplitude <=2W;
- its squared amplitude is <=4W².

The final theta-integrated estimate is a direct consequence of the
pointwise inequality and the unit length of the theta interval; that
measure-theoretic step is documented but not claimed to be part of
this finite-arithmetic Lean module.

**New acceptance gate:** prove an OAI compensated bound on the
outer-smoothed, INTERNALLY sharp root-phase source, retaining the
entire mixed harmonic k,l matrix, with saving H^(5/2-delta).
It is false to demand H separate small physical collars once the
root-phase sampling operator has been used.

## 8. Harmonic coefficient norm and the missing original mixing theorem

Since f_theta(v)=exp(-2*pi*i*theta*{v}) has |f_theta(v)|=1
on v in [0,1), Parseval in its PERIODIC variable gives

    sum_(k in Z) |c_k(theta)|² = 1.

This is true even though the off-diagonal k!=l terms in the
MOBIUS source energy are nonzero and often strongly negative.
Coefficientwise l² normalization is NOT orthogonality of the
arithmetic smooth modes V_H(theta+k).

In fact, the bare unweighted sum
    sum_k |V_H(theta+k)|²
generally diverges for a finite original n-sum of complex
exponentials. Therefore using Cauchy--Schwarz on the infinite
k-series with only ||c(theta)||_l2=1 does NOT give a finite
moment estimate. One needs actual decay or a mixed-k/l large
sieve at the original signed source level.

PR #1049 deliberately preserves all mode pairs. Its direct
cofactor/Hecke next step is a source-normalized, harmonic-mixed
moment inequality that survives k,l recombination without
spending the original signed cancellation on an invalid
diagonalization.
