# The sharper ray theta payment gives an auxiliary B^-6 bound at s=1

Status: **PAPER_PROOF, NOT COMPILED**. This is an independent derivation from
the actual ray-family coefficients and explicitly listed LFam inputs.
The companion native arithmetic modules now contain proof drafts for all
these inputs and their same-datum assembly; hosted verification is pending.
The analytic integral argument below is not yet formalized. It proves no
G_z estimate, new RH exponent, or RH. No local Lean execution was used.

## Precise conditional statement and constants

Fix an admissible imaginary quadratic ray datum D with d>=100, M>=3, and
the SAME coefficients a_c(n)=aRay(D,c,n). Let H=card(D.G), and set

    B=4 d M^2,
    kappa=2*pi/(sqrt(d)*M^2),
    C0=(3*pi/8)*d*sqrt(d)*M^2.

The native count/theta candidates provide nonnegativity, a_c(0)=0,
a_c(1)=1 if c is the identity and 0 otherwise, and

    |sum_{1<=n<=floor(x)} a_c(n)-kappa*x| <=10*sqrt(x)   (x>=1),
    |sum_n a_c(n)e^(-tn)-kappa/t| <=C0*t               (t>0).

The first bound follows from the sharper native 4sqrt(x)/M+1 bound; the
second is the new all-time theorem. Retain these *literal* coefficients.
Assume the remaining actual arithmetic LFam inputs:

1. H<=B and 1/B<=kappa<=4. The latter numerical bounds follow from the
   displayed kappa and the admissible d,M; H<=B requires the actual ray
   class-number bound, now supplied in the companion `NativeRayClassBound` draft.
2. For every real character chi of D.G, put
   A_n=sum_c a_c(n) and b_n=sum_c chi(c)a_c(n), with chi(c) in {1,-1}.
   For every integer k>=1, retain the actual convolution positivity

       c_k=sum_{mn=k} A_m*b_n >=0.

   This is exactly the first half of the source `LFam.sq` field, supplied
   there by `ConvRealChar.conv_real_char`. The companion native
   `NativeRayRealCharacter.conv_real_addChar` draft proves both halves;
   it remains subject to hosted verification. The second half of sq, the log convolution and
   von Mangoldt mass are not needed for the lemma proved below, although
   they remain obligations in assembling the full original LFam.
3. Define the SAME F_chi by the source LFam Mellin formula. Equivalently,
   for nontrivial chi, the exact identity established below is

       F_chi(1)=integral_0^infty sum_n b_n e^(-tn) dt;

   for the trivial character, F_1(1)=rho=kappa*H. This is the source's
   regularized F, not an arbitrarily rescaled L-function.

Then there is an absolute c>0, independent of d,M,D,chi, such that

    |F_chi(1)| >= c/B^6                     for every real chi.   (T)

An explicit choice in the proof is

    S=14*sum_{n>=0} n*exp(-n/2),
    C=max(1, pi/64, 2S+4),
    c=exp(-4)/(64*(1+C^2)).

All constants are absolute and positive; the geometric series defining S
converges. There are no X,h,zero-free-region, or short-window hypotheses in
(T). Those enter later upstream consumers and are not claimed here.

## 1. Exact character theta bound, including large time

Let Theta_chi(t)=sum_n (sum_c chi(c)a_c(n))*exp(-tn), and let
rho_chi=kappa*sum_c chi(c). Finite character aggregation, absolute
convergence and |chi(c)|=1 give

    |Theta_chi(t)-rho_chi/t| <=H*C0*t.

Since B=4dM^2 and M>=3,

    C0/B^(3/2)=3*pi/(64M)<=pi/64,
    H*C0<=(pi/64)*B^(5/2).                              (1)

The count bound and positivity give, for n>=1,

    0<=a_c(n)<=kappa*n+10sqrt(n)<=14n.

Hence all theta series are absolutely summable at every positive t, and
the source's large-time argument gives for t>=1

    |Theta_chi(t)|<=S*B*exp(-t/2),
    |rho_chi|<=4B.

Indeed exp(-tn)<=exp(-t/2)*exp(-n/2) when n,t>=1. Also
exp(-t/2)<=2/t. Together with (1), this proves for every t>0

    |Theta_chi(t)-rho_chi/t|
       <=E*min(t,1/t),        E=C*B^(5/2).             (2)

The two time regimes are both covered; the improved small-time estimate is
not incorrectly reused as a decreasing bound at large time. All factors of
H and B in the character aggregation have been retained.

For a nontrivial real character chi, character orthogonality gives
rho_chi=0. Set

    P(t)=sum_n A_n exp(-tn),
    Q(t)=sum_n b_n exp(-tn),
    rho=kappa*H,
    L=integral_0^infty Q(t) dt.

Then P,Q are real, 0<rho<=4B, and

    |P(t)-rho/t|<=E*min(t,1/t),
    |Q(t)|<=E*min(t,1/t).

The separate exponential bound at infinity makes Q integrable; the bound
at zero is O(t).

### Verify the normalization F_chi(1)=L

For nontrivial chi let N(x)=sum_{1<=n<=floor(x)} b_n. Character cancellation
in the count main term gives |N(x)|<=10H sqrt(x) for x>=1. Abel summation
gives Q(t)=t*integral_1^infty N(x)e^(-tx) dx. Absolute integrability permits
the subsequent swap, since integral_1^infty |N(x)|/x^2 dx<=20H. Therefore

    L=integral_1^infty N(x)/x^2 dx.

The source defines LFam.mel at 1 by precisely the last integral (the
nontrivial residue is zero), and LFam.F(chi,1)=LFam.mel(chi,1). Thus there
is no gamma, degree, class-group, or factor-of-two normalization missing.
For chi=1 the source formula gives F_1(1)=rho directly.

## 2. Positive-convolution lower bound on the same sequences

Define, for v>0,

    W(v)=integral_0^infty exp(-v/w-w) dw/w,
    I(v)=integral_0^infty P(v/w)*Q(w) dw/w.

The exact product-series identity is

    I(v)=sum_{m,n>=1} A_m*b_n*W(vmn)
        =sum_{k>=1} c_k*W(vk).

This is valid despite signed b_n: |A_n|,|b_n|<=14Hn, and the source proves
W(y)<=G/y^3 with an absolute G. Thus the absolute pair sum is at most a
finite constant times sum_{m,n>=1} 1/(m^2 n^2). These absolute-convergence
constants are needed only to justify the equality; they never enter the
quantitative lower bound.

The genuine unit-ideal normalization gives A_1=b_1=1, hence c_1=1.
The assumed actual convolution positivity gives c_k>=0, and W>=0. Therefore

    I(v)>=W(v).                                         (3)

For 0<v<=1 and v<=w<=1, both v/w and w are at most one, so

    W(v)>=exp(-2)*integral_v^1 dw/w
         =exp(-2)*log(1/v).                            (4)

No positivity of Q itself is assumed or needed.

## 3. Exact error-kernel integral saves the extra square

Write m(t)=min(t,1/t). Using (2) and the identity
P(v/w)=rho*w/v+[P(v/w)-rho*w/v] yields

    I(v)<=rho*L/v + E^2*J(v),
    J(v)=integral_0^infty m(v/w)*m(w) dw/w.

For 0<v<=1 the integral is exact. Split at w=v and w=1:

| Interval | Integrand | Integral |
| --- | --- | --- |
| (0,v) | w/v | v/2 |
| (v,1) | v/w | v log(1/v) |
| (1,infinity) | v/w^3 | v/2 |

Consequently

    J(v)=v*(1+log(1/v)),
    I(v)<=rho*L/v+E^2*v*(1+log(1/v)).                   (5)

All three integrals converge. In particular the residual product is
absolutely integrable. The source uses the weaker bound J(v)<=K*sqrt(v),
where K=8/3. Retaining J(v) and the logarithmic lower bound (4) is the new
analytical saving.

## 4. A uniform admissible parameter and the complete power accounting

Put

    epsilon=exp(-2)/8,
    v=epsilon/(1+E^2),
    ell=log(1/v).

Then 0<v<=epsilon<exp(-1)<1 and ell>=1. Also E^2*v<=epsilon. Hence

    E^2*v*(1+ell)<=2epsilon*ell=exp(-2)*ell/4.

Combining (3), (4), and (5),

    rho*L/v >= (3/4)*exp(-2)*ell >= exp(-2)/2.

In particular L is positive. Now substitute every original normalization:

    L >= exp(-2)*v/(2rho)
      = exp(-4)/(16rho*(1+E^2))
      >= exp(-4)/(64*(1+C^2)*B^6),

because rho<=4B, E^2=C^2 B^5, and B>=1 implies
1+C^2 B^5<=(1+C^2)B^5. Since F_chi(1)=L, this proves (T) for nontrivial
real chi. For the trivial character,

    F_1(1)=rho>=kappa>=1/B>=c/B^6,

as H>=1, B>=1 and the displayed c is less than one.

## 5. Conservative B^-11 check using the unchanged source kernel bound

The claim B^-45 -> B^-11 is also valid if one changes only the theta
allowance in the source proof and leaves its coarse scalar bound unchanged.
Let w0=W(1)>0, K=8/3, and

    delta=min(1, w0/(2*(C^2*K+1))),
    s=delta/B^5,    v=s^2.

Then 0<v<=1, W(v)>=w0, and

    E^2*sqrt(v)*K=C^2*B^5*(delta/B^5)*K<=w0/2.

The original integral comparison therefore yields

    L>=w0*v/(2rho)>=w0*delta^2/(8B^11).

The source's B^-45 arises in exactly the same way from its original
E=C B^11 and s=delta/B^22. All constants in both substitutions are
absolute. The B^-6 argument above is a further independent simplification,
not an attribution of a sharper exponent to the existing source theorem.

## Source dependencies checked

Inspected Alpöge source mirror pin:
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`; paths below are relative to `src/`.

* `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LamIdealOfNotPrimePow.lean`:
  exact LFam fields, aChi, res, mel, F.
* `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsLFamRay.lean`:
  exact same-ray-coefficient assembly with B=4dM^2 and kappa above.
* `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean`:
  a_le_mul, norm_theta_large, norm_theta_small, integral_theta.
* `Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/NormRayClassFamilyFOneGeOfRealCharacter.lean`:
  besW, hasSum_pairs, besW_le_integral, integral_le, norm_F_one_ge.

Native suppliers used as candidates, pending hosted verification:
`RHLean/Analysis/AlpogeThin/NativeRayIdealCounts.lean`,
`NativeRayQuadraticForm.lean`, `NativeRayCountTheta.lean`,
`NativeRayRealCharacter.lean`, `NativeIdealClassBound.lean`, and
`NativeRayClassBound.lean`. `NativeRayLFam.ofRayData` assembles every
original arithmetic LFam field on the same given K,d,M,root,D, with the
sharper theta estimate retained separately. The analytic integral consumer
above still requires formalization before (T) is a native verified result.
