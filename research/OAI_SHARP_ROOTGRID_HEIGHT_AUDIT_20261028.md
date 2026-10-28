# Pinned OpenAI moment vs sharp root-indexed Euler sampling: quantitative audit

28 October 2026. Continues the successful PR #1047 exact source-to-Euler identity. This note audits the ACTUAL pinned OAI moment quantifiers and BOTH smoothing-to-sharp and continuous-to-root-sample costs. Nothing in this note assumes a new analytic moment saving.

Pinned OAI commit: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.

## UPDATE: 2026-10-28 NNS sampling and first-derivative trace correction

The original squared-derivative Sobolev trace and its H^(1/2+delta)
loss below remain VALID as a conservative proof, but are NOT optimal.
A first-derivative Plancherel--Polya-type argument reduces the
generic high-frequency penalty to H^(1/4+delta/2+kappa).
Read the corrected source and exponent budgets in Section 7 below.
No lossless arbitrary-profile-to-OAI theorem is asserted.

## The proved physical source and what is still missing

For H<=R<2H, PR #1047 proves the complete ORIGINAL, sharp quadratic norm-fiber source identity, before squaring:

    S_R=sum_(md in [R^2,(R+1)^2)) a_F(m)*chi_{-3}(d)
       =M((R+1)^2-1)-M(R^2-1)
       =Delta E_R+Delta C_R-Delta P_R.

Its true dyadic moment is E_sharp(H)=sum_(R=H)^(2H-1)|S_R|^2.
The proposed exponent improvement requires an independent bound

    E_sharp(H) <= C_epsilon H^(5/2-delta+epsilon), delta>0.

There is no penalty from regrouping the same compensated source into a
fixed three-part Euler population. Separate component estimates, if
available with the same uniform constant, give an optional factor 9;
they are not required and can lose the large signed cross terms.

Do not equate these variables without proving a source map:
1. Physical root scale R and integer site scale x~R^2;
2. OAI source height/scale Z, ideal-polynomial scale Z^d and family scales;
3. Mellin/Fourier frequency v of a new profile;
4. Original detector spectral/row-height t and shift parameters.

## Smooth collar: exact deterministic cost

For a smooth block mask with transition collars of physical width
Delta>=1 around [R^2,(R+1)^2), and assuming full reassembly to the
original integer Mobius coefficients with |mu(n)|<=1, the discrepancy
is bounded by 4Delta+2 (coarse count, both endpoints). Hence

    sum_(R~H)|S_R-S_R,smooth|^2<=H*(4Delta+2)^2.

Choose Delta=H^(3/4-delta/2-kappa), with kappa>0. Then

    rounding energy exponent =1+2*(3/4-delta/2-kappa)
                            =5/2-delta-2*kappa.

The user's stronger choice Delta=H^(3/4-delta) also suffices but
requires a sharper and more expensive Fourier profile.

At x~H^2, the logarithmic transition width and effective frequency are

    eta_log~Delta/H^2=H^(-5/4-delta/2-kappa)
    T_eff~H^2/Delta=H^(5/4+delta/2+kappa).

Effective frequency is NOT compact support. A compactly supported
nonzero smooth physical window has no compact Fourier/Mellin support,
so the high-frequency tail must receive its own signed estimate.

A smooth window can even interpolate the exact integer indicator by
placing sub-unit transitions between integer sites; this removes the
integer rounding error but requires logarithmic transitions of size
O(H^-2), and therefore even more demanding Fourier control.

## What the original pinned OAI theorem ACTUALLY bounds

1. Original inverse profiles, fixed_raw_profiles:
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/DetectorInverseRawField.lean

Its quantifier structure is

    exists J, forall data:RowData, exists C(data)>0,
      forall reverse n<=2 U>0 tstar r s in [0,1],
      forall height>=0 t in [-height,height],
        RawMoment data W c kappa (C(data)*(1+height)^J),

and also the scaleProfile form, where W is precisely the
oriented/inverse/log-derivative/twisted existing profile.
The same C is UNIFORM over the moving U,tstar,r parameters for FIXED
row data, but the theorem does not quantify over arbitrary new sharp
root-dependent W and does not say C is independent of rowData.

2. Reference Fourier transfer, rawMoment_reference:
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Dictionary/InverseRawEnergy.lean

For any newly supported C-infinity profile W, the moment constant
produced by THIS specific Fourier argument contains

    C * (integral_v (1+|v|)^J
        * |Fourier(logSchwartz W)(v)| dv)^2.

An estimate on the UNWEIGHTED Fourier L1 norm of O(log(H/Delta))
is not enough; the original theorem requires a POLYNOMIALLY WEIGHTED
Fourier norm, squared. The proof of uniformity for the original
inverseSourceSchwartz profiles separately establishes bounded
weighted Fourier moments over that family. No such bound for the
shrinking physical square-root collars has been established.

In fact, for a smooth taper changing by 1 over log width h,
the Fourier derivative identity gives
1/h<=const*integral |v|*|Fourier W(v)|dv
when the derivative exists and the integral is finite. For J>=1,
the weighted L1_J cannot remain uniformly bounded as h tends to 0.
This rules out a LOSSLESS application of that particular Fourier
argument, NOT all alternative compensated signed localization proofs.

3. Marked fourth moment, source_batch_plain_marked_fine:
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/DetectorPlainMarkedFineField.lean

It bounds the actual marked character-source row-energy by

   (C*(1+height)^J)*(Z^d)^(1+D.t)

under an explicit PositiveFineSourceInput for the ORIGINAL source
and smooth positive-annular test profiles. The terminal certificate
discharges the positive input in that original family, not for a
new square-shell-sharp mask.

4. Actual RawMoment is an IDEAL/CHARACTER ROW sum, not a
sum over square-root indices R. Its unscaled shape is

    sum_(v in ideal rows)|polynomial(char_v,W,D)|^2
       <= C * X*(X*max(1,D))^kappa.

Source: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationRaw.lean

5. Final chosen detector height:
https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyMomentInput.lean

The raw_input_chosen_height theorem selects

   height=Z^(2*tau), 0<tau<1/400,

with polynomial-height absorption 2*tau*(1+J)<=D.t.
The raw moment quantifies all heights with cost (1+height)^J,
but the TERMINAL certificate does not preserve its power budget
for arbitrary large heights.

Only IF a separate transfer identified the physical scale Z~H^2
AND identified the required Mellin v frequency with that row-height
parameter would the chosen height convert to H^(4*tau)<H^(1/100),
far below the sharp collar T_eff=H^(5/4+delta/2+kappa).
Those identifications are NOT currently proved and should not be
silently assumed. The weighted Fourier norm issue is independent
of such a matching.

## Exact sparse-root Sobolev trace

Let u_R=2 log R and h_R=u_(R+1)-u_R=2 log(1+1/R).
For H<=R<2H, elementary log bounds give

    1/H<=h_R<=2/H.

For any locally absolutely continuous complex F on
[u_H,u_(2H)], the fundamental theorem and Cauchy give

    sum_(H<=R<2H) |F(u_R)|^2
     <= 2H*integral |F(u)|^2 du
        +(4/H)*integral |F'(u)|^2 du.                (TRACE)

Proof on I_R=[u_R,u_(R+1)]:
F(u_R)=F(v)-integral_(u_R)^v F'(t)dt.
Square with |a+b|^2<=2|a|^2+2|b|^2, use Cauchy
on the derivative integral, average over v in I_R:

    |F(u_R)|^2 <= (2/h_R)*int_(I_R)|F|^2
                       +2*h_R*int_(I_R)|F'|^2.

Sum and use the mesh bounds.

If an ACTUAL frequency support |v|<=T or a controlled tail supplies
||F'||_2<=T||F||_2 in the relevant global/buffered norm, TRACE
costs at most 1+(T/H)^2. Local Bernstein control does NOT
follow from global bandlimiting and a local window without boundary
or tail terms, so this is a conditional trace budget, not an
automatically obtained bound from the OAI character rows.

For T=T_eff, generic sampling costs

    (T/H)^2 = H^(1/2+delta+2*kappa).

This is a real power loss even when the profile-constant penalty is zero.

## Exact exponent-closure formulas (Lean-checked algebra)

Assume as ADDITIONAL input a continuous smooth root-source moment
H^(5/2-delta0), not provided by the original final 7/8 prefix theorem.

If the generic root trace is paid, and the profile price is
the hypothetical RELATIVE factor (T/H)^beta, the final power exponent is

    5/2-delta0 + 1/2+delta+2*kappa
                +beta*(1/4+delta/2+kappa).

To reach target 5/2-delta, the EXACT requirement inside this
specific generic scheme is

    delta0 >= 1/2+2*delta+2*kappa
                  +beta*(1/4+delta/2+kappa).       (REL)

Even beta=0, kappa=0 requires delta0>=1/2+2*delta.
At target delta=0.01, this means delta0>=0.52.

If the OAI ABSOLUTE height factor T^J must be paid in the SAME
generic scaling, the corresponding condition is

    delta0 >= 1/2+2*delta+2*kappa
                  +J*(5/4+delta/2+kappa).          (ABS)

At delta=0.01, kappa=0, the right-hand side is 0.52+1.255 J.
This is an illustrative POWER ACCOUNTING comparison, NOT a
claim that the original OAI source moment has exponent 5/2-delta0
or that Fourier v equals its row height.

The Lean file OAI_SHARP_ROOTGRID_HEIGHT_BUDGET_20261028.lean
formally proves both exponent equivalences, plus the collar,
effective-frequency, and conditional terminal-height comparisons.

## What actually needs to be proved

Three coherent alternatives, each preserving the original compensated
source and true mixed phases:

A. Prove a sharp/BV-profile physical source moment DIRECTLY on the
square-root grid. This bypasses generic trace and collar penalties,
but requires a new analytic estimate (not only exact source identities).

B. Prove a specialized root-grid Bessel/large-sieve inequality for
the fully compensated OAI ideal source with strong enough saving
to beat the generic (T/H)^2 trace factor at T>>H.

C. Use the native RH_Lean cofactor-prime cancellation to prove
a SIGNED sharp-minus-smooth collar estimate, permitting a wider
collar and a much lower necessary Mellin bandwidth.

These routes also require an independently proved strict smooth
moment saving if they are to IMPROVE rather than merely recover 7/8.
The terminal OAI global prefix bound itself does not provide one.

**Audit verdict:** fixed partition count is NOT a uniformity problem.
The pinned theorem is uniform over its OWN specified profile family.
For arbitrary shrinking square-root physical masks, its proof carries
a polynomial weighted Fourier-norm cost; for the root grid, a generic
trace carries H^(1/2+delta) inflation. No currently identified pinned
theorem simultaneously (i) covers the sharp physical masks, (ii)
controls their root-indexed moment, and (iii) delivers strict saving.
This is a quantitative theorem-applicability gap, not an impossibility
result against more arithmetic signed localization.


## 7. Corrected: a first-derivative trace beats the squared-Sobolev tax

The original Section on the squared-derivative Sobolev trace is a
correct inequality but NOT an unavoidable +1/2 exponent tax.
There is a strictly better bound from the fundamental theorem applied
to |F|^2 (sometimes formulated as Plancherel--Polya or a sampling
Bessel inequality).

For u_R=2 log R, h_R=u_(R+1)-u_R, H<=R<2H, we have

    1/H <= h_R <= 2/H.

For any locally absolutely continuous complex F and interval
I_R=[u_R,u_(R+1)], the fundamental theorem gives for v in I_R

    |F(u_R)|^2 <= |F(v)|^2 + 2*int_(I_R)|F||F'|.

Average over v and sum DISJOINT intervals:

    sum_R |F(u_R)|^2
       <= H*int_I |F|^2 + 2*int_I|F||F'|
       <= H*int_I |F|^2
          + 2*||F||_(L2(I))*||F'||_(L2(I)).        (TRACE-1)

If F is globally L2 and Fourier bandlimited to |v|<=T, then
global Plancherel gives ||F'||_2<=2*pi*T*||F||_2
under the exp(2*pi*i*u*v) transform convention. Therefore

    sum_R |F(u_R)|^2
       <= (H+4*pi*T)*||F||_(L2(R))^2.           (PP)

The frequency inflation RELATIVE to the natural H*integral is now
1+T/H, not 1+(T/H)^2. Global bandlimitedness does not automatically
give a Bernstein inequality on the smaller interval I alone, which is
why PP is stated using the GLOBAL continuous L2 norm. To insert it
into a LOCAL smooth source moment, one needs a global/buffered norm or
explicit tail control. This qualification is essential.

At collar width Delta=H^(3/4-delta/2-kappa), we need
T_eff=H^(5/4+delta/2+kappa), hence the refined grid price is

    (T_eff/H)=H^(1/4+delta/2+kappa).

Assuming INDEPENDENT continuous smoothed root-source moment saving
delta0 and hypothetical RELATIVE profile penalty (T/H)^beta, the
revised exact closure budget is

    delta0>=1/4+3*delta/2+kappa+
                      beta*(1/4+delta/2+kappa).    (REL-1)

For beta=0,kappa=0,delta=0.01 this is 0.265 instead of 0.52.
If paying the original polynomial ABSOLUTE height price T^J,
the corresponding (conditional) budget is

    delta0>=1/4+3*delta/2+kappa+
                         J*(5/4+delta/2+kappa).    (ABS-1)

The Lean file adds oaiLinearTracePower_eq,
oaiLinearGridRelativeBudget_iff, and
oaiLinearGridAbsoluteBudget_iff, all proved with standard axioms.
The earlier +1/2 budget remains a valid NONOPTIMAL inequality for
the squared-derivative route and MUST NOT be called a fundamental
uncertainty-principle obstruction.

This does NOT establish the OAI smooth moment saving delta0 in the
PHYSICAL root variable. It also does not supply a uniform OAI theorem
for the actual shrinking sharp-window profiles.

## 8. NNS sampling is an exact discrete-to-continuous DISTRIBUTION bridge

Canonical source:
https://github.com/OVVO-Financial/NNS/blob/NNS-Beta-Version/vignettes/NNSvignette_05_Sampling.Rmd

In NNS, the degree-zero lower-partial-moment ratio recovers the
empirical CDF; positive degrees create continuous threshold
descriptions, and the vignette's multivariate examples explicitly
preserve/compare dependence rather than assume IID.

Let s_R be the original sharp Mobius square-block signed increment
(no synthetic, randomized or independence surrogate) and choose R
UNIFORMLY from the H integer roots [H,2H).
Define the exact empirical law

    nu_H=(1/H)*sum_(R=H)^(2H-1) delta_(s_R).

It is a probability measure on R, not a claim of independence.
For target t and q>0 define actual NNS partial moments

    LPM_(q,H)(t)=(1/H)*sum_R max(t-s_R,0)^q,
    UPM_(q,H)(t)=(1/H)*sum_R max(s_R-t,0)^q.

At q=2, t=0, the exact identity is

    sum_R s_R^2 = H*(LPM_(2,H)(0)+UPM_(2,H)(0)).

The general target identity is

    H*(LPM_(2,H)(t)+UPM_(2,H)(t))=sum_R(s_R-t)^2.

The degree-two LPM is continuously differentiable as a function of
the TARGET t. Its first derivative is 2 LPM_(1,H)(t), and its
second derivative is 2 F_H(t) almost everywhere, with F_H the
degree-zero empirical CDF. This gives an exact continuous
partial-moment REPRESENTATION of the same discrete data.
The positive-degree LPM.ratio itself reweights the empirical
distribution and therefore is not a lossless substitute for the
original moments unless additional identities are proved.

Alternatively, introduce an EXACT continuous uniform-quantile
variable z in [0,1), with root index R(z)=H+floor(H*z).
Then, for any original deterministic samples s_R,

    int_(z in [0,1)) |s_(R(z))|^2 dz
       =(1/H)*sum_R |s_R|^2.

There is zero sampling or interpolation error here. However the
resulting source is a STEP FUNCTION of z; it is NOT automatically
one of the original smooth OAI inverse/marked Hecke profiles.
Thus NNS sampling removes the representation/trace obstacle, but
DOES NOT by itself prove that an OAI moment bound applies to the
resulting empirical measure.

The full joint law should be used for the user's moving Euler
three-prime-population streams, not independent marginals:

    nu_H^joint=(1/H)*sum_R delta_(
       DeltaE_R, DeltaC_R, -DeltaP_R).

Then the true variance has the signed cross-terms:

    (1/H)*sum_R |s_R|^2
       =int_(a,b,c) (a+b+c)^2 d nu_H^joint(a,b,c).

NNS multivariate dependence/copula methods can diagnose that
correlation on finite genuine arithmetic samples, but resampling
or bootstrap simulations cannot prove a bound uniform in H.

The degree-zero empirical CDF of |s_R| also gives the exact
tail-moment representation

    (1/H)*sum_R |s_R|^2
      =2*int_(t>0) t*P_H(|s_R|>t) dt.

A new arithmetic theorem such as

    P_H(|s_R|>z*H^(3/4-delta/2))<=A*exp(-c*z^2)
    for ALL H and z>=0 (with uniform A,c>0),

would yield the desired H^(5/2-delta) energy (integrate tails).
This sufficient tail theorem is genuinely NEW arithmetic input,
not a consequence of the NNS empirical CDF identity or finite
sampling observations.

The exact unnormalized NNS degree-two identities are certified by
oaiNNSTwoSidedSecond_eq_energy and
oaiNNSDyadicTwoSided_eq_energy in the Lean budget module.

## 9. Revised conclusion / next source task

The user's NNS insight provides a lossless continuous *empirical
measure* of the deterministic sharp data and preserves the joint
prime/cofactor covariance. Also the naive +1/2 grid exponent tax is
not fundamental: a first-derivative Bessel trace reduces it to +1/4
at the collar bandwidth, still not negligible.

The OPEN source-level task is now precise:

- Either prove the original OAI compensated moment directly under the
  empirical root-index law / root-phase Parseval formulation;
- Or build a weighted, buffered Plancherel--Polya estimate that
  transfers the actual OAI smooth family into this source with the
  stated first-derivative cost and controlled sharp boundary tails;
- Or prove a uniform joint NNS partial-moment / tail dominance
  estimate for the actual arithmetic three-population residual.

No route may replace the actual signed Möbius coefficients with
resampled/independent signs, and no lossless moment inequality follows
from the mere existence of the continuous empirical distribution.
