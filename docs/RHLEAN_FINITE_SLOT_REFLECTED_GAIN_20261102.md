# Finite-slot reflected gain and fixed-source uniformity

Date: 2026-11-02. Complete strict-endpoint source, reviewed and submitted to pinned warning-fatal Lean verification. The exact-head verification status is recorded in [proof PR #1073](https://github.com/OVVO-Financial/RH_Lean/pull/1073) and its Actions runs; source text alone is not a verification certificate.

Base RH_Lean main: **8e5d64ae689b39dabd2a4f6eb33efe4d5d192015**.
Original OpenAI analytic source: **1581d4cbdd69a0faf34b2089614fe2a814316a6a**.

## The new source restriction

The old scalar relaxation admits arbitrarily small positive selected mass. The actual HighData source has a fixed finite slot list with
\[
0 < (7/8)r_{\min}\le \ell_i.
\]
Every nonempty selected set therefore has total mass at least
\(\ell_{\min}=(7/8)r_{\min}>0\).

The empty selected set has actual slot product one. On every nonempty tuple dyad,
\[
1\le \operatorname{divisorDyadicScale}(j)\le N(P)=1
\]
forces its scale to one. The source caller sets \(Q_P=2\operatorname{divisorDyadicScale}(j)\), so its actual reflected width is
\[
z=\log_Z(Q_P/2)=0.
\]
Nominal padding does not change this identity: LowNominalEnergy uses
\(\ell_0=s+\eta/2\), and LowInactiveEnergy passes that same \(\ell_0\) into all inner active subsets.

Pinned original sources:

- ParametersHighData.lean: positive fixed slot lengths.
- Detector/LowNominalGeometry.lean: \(d+s=L\).
- Detector/LowNominalEnergy.lean: nominal padding.
- Reflection/LowInactiveEnergy.lean: preservation through inner subsets.
- Reflection/TupleDyads.lean: dyadic norm bounds.
- Reflection/LowDyads.lean: actual \(Q_P\).
- Reflection/LowFixedMember.lean: logarithmic width.

All original paths here have prefix **lean/OAI/NumberTheory/DirichletL/** in openai/math at the pin above.

## Proved scalar extension

Let \(M=S-2d\), \(a=1+4L-2S\), and
\[
T=2H+2A+2z-1-\ell_0-\theta-N-3B.
\]
Retain the exact original hybrid saving and reflected exponent:
\[
h=\min(v,z,(v+z)/3),
\]
\[
E=O/2+\max(H,v+\lambda)-S_0-B+z-h-\lambda-2e/3
-\tfrac12\max(0,T-v-3\lambda-e).
\]

Assume
\[
S+L\le1,\quad L\le1/3,\quad d,\eta,O,N,S_0,B,v,\lambda\ge0,
\]
\[
H\le M-O+\eta,\quad 2A\le O+3\eta,\quad N\le A,
\]
\[
\ell_0\le L-d+\eta,\quad z\le\ell_0+\eta,\quad e\ge-\eta,\quad |\theta|\le\eta,
\]
\[
v+3\lambda+e\le T+2\eta.
\]
Then the sufficient gate
\[
h=z\quad\hbox{or}\quad a\le\ell_0
\]
implies
\[
\boxed{E\le M+\frac{38}{3}\eta.}
\]

This retains the original reflected terms. It does not assume that a principal coefficient vanishes.

### Proof

The gates give
\[
T\le H-3d+8\eta,\qquad v+\lambda\le H+11\eta.
\]
If \(h=z\), its two occurrences cancel and
\[
E\le O/2+H+11\eta+2\eta/3
\le M-O/2+38\eta/3.
\]

Otherwise \(h\ge v/2\). The retained kernel inequality is
\[
T/4\le(v+3\lambda+e)/4+
\tfrac12\max(0,T-v-3\lambda-e).
\]
It gives total hybrid/retained charge at least \(T/4-5\eta/12\).

If the row maximum \(H\) is active, substitution and expansion give
\[
E\le M/2+(1+3\ell_0)/4+5\eta/3
\le M+(a-\ell_0)/4+8\eta/3.
\]
The last comparison is exactly \(\ell_0\le L-d+\eta\).

If the column maximum is active, the retained gate instead gives
\[
E\le M-\tfrac12+\tfrac32L-\tfrac32d+\tfrac{26}{3}\eta
\le M+\tfrac{26}{3}\eta.
\]
This proves the claim in every branch.

### Source-facing proof

The new surviving_low_exponent_finite_slot_gap generalizes the original
original_surviving_low_exponent with physical power \(S-2d\), slot cap \(L\), and the sufficient gate above. It retains actual ideal labels, optional prime pools, frozen branches, row masks, dyads, raw scales, terminal widths and logarithmic budgets.

The original source gates supply \(v,\lambda\ge0\), ramified width \(e\ge-\eta\), retained slack at most \(\delta_{\rm retained}+\eta\le2\eta\), and
\[
H\le S-2d-O+\eta,\qquad 2A\le O+3\eta.
\]
The extracted widths are nonnegative and satisfy \(N\le A\).

The retained padding is distinct from the physical perturbation below.
Its original choice is \(\delta_{\rm retained}=\eta_{\rm low}/2\);
it decreases with the arbitrary low error while the physical gain stays fixed.

The new surviving_low_energy_sum_finite_slot_gap and
low_sector_literal_energy_finite_slot_gap carry this estimate through
branch counting to the actual signed dyadic row energy:
\[
\sum_K|\operatorname{literalDyadicRow}(K)|^2
\le C(1+|\theta|)^J
N\!\left(\prod_bG_b\right)^\rho
Z^{S-2d+38\eta/3+\pi-O_0/2}.
\]
The original cusp column, sector completion, weights, masks, prime pools
and surviving branches remain in the statement. This is still one retained
dyad and unit; the full physical low reconstruction remains below.

The new file also proves the literal empty-tuple dyad identity. The downstream LOW composition is implemented in VF919TiltedLowReflection.lean and VF919TiltedLowPhysical.lean. Its Lean verification is tracked separately from this previously verified local source theorem.

## Candidate leading exponent movement

Keep the same slots, \(L=1/6\), and choose
\[
x=17/48-6\delta,\qquad y=23/48-6\delta.
\]
The exact accounting is
\[
S=x+y=5/6-12\delta,\qquad a=24\delta,
\]
\[
g=(5x+y)/12=3/16-3\delta,
\]
\[
c=-5/6+x/3+L/6=-11/16-2\delta,
\]
\[
g-c=7/8-\delta.
\]
Thus \(0<24\delta<\ell_{\min}\) pays the new scalar gate for every nonempty selected set. Empty selections use \(z=0\).

This is feasible local exponent movement, not a proved complete contraction.

### Improved choice of physical direction

A stronger audited direction keeps the same total \(S\) and finite-slot charge:
\[
x=17/48-24\delta,\qquad y=23/48+12\delta.
\]
Then
\[
g=3/16-9\delta,\qquad c=-11/16-8\delta,\qquad
g-c=7/8-\delta,\qquad a=24\delta.
\]
The high physical prefactor changes by
\[
-(96/25+12a_{\mathrm{det}}+72e)\delta
\le-(249/25)\delta
\]
for \(a_{\mathrm{det}}\ge51/100\), \(e,\delta\ge0\).
Even after paying the \(9\delta\) movement of the lowest target signal,
this leaves at least \(24\delta/25\) in the favorable direction.

Its additional geometric requirements are
\[
2x-y-L=1/16-60\delta>0,\qquad
\zeta>24\delta.
\]
For example, \(\delta=\ell_{\min}/48\), \(\zeta=t\), and
\(\ell_{\min}\le t/200\) satisfy them. This direction is preferable for the
remaining full-source reconstruction. The equal perturbation above remains
a valid comparison and explains the dependence of the crossing on total
physical length.

The Lean file proves the tilted scale identities and its central prefactor
inequality as well. Neither statement asserts the missing full high estimate.

## Stronger native uniformity

The native source assembly now establishes
\[
\exists J\ge0\ \forall\chi\ \exists C_\chi>0\ \exists Z_0\
\forall Z\ge Z_0\ \forall\tau\in\mathbb R\ \forall h\ge0:
\operatorname{NativeSourceMomentBound}
(F,\mathrm{counts},\chi,Z,\tau,C_\chi(1+h)^J,h).
\]
The threshold precedes both \(\tau\) and \(h\), as well as all moving rows, bins, selected subsets and batches inside the source conclusion. The existing \(h=Z^{2\tau}\) interface specializes this theorem, so the original complete \(7/8\) replay consumes it.

For the three suppliers, one may take
\[
J=\max(J_i,J_m,J_u),\qquad C_\chi=\max(C_i,C_m,C_u).
\]
The four moment conclusions are separate fields, so their degrees and constants need not be added. Downstream consumers retain their own height constraints.

The generic native certified band theorem requires the actual analytic range
\[
51/100\le\beta\le7/8+\Delta_0.
\]
These bounds supply the analytic floor condition and
\(2\beta-1\le3/4+2\Delta_0\).
The old proof's arithmetic tactics use these dependencies implicitly; the new interface states them explicitly. At \(\beta=7/8\), a positive auxiliary \(\Delta_0\) can therefore be fixed independently of \(\beta-7/8\).

## Analytic region margin

The same local Euler correction estimate extends to \(\Re x\ge21/25\):
\[
|\operatorname{unramifiedClosed}-1|\le240Q^{-17/10}.
\]
At the enlarged boundary,
\[
|R|\le Q^{-2},\quad |V|\le Q^{-24/25},\quad
|W|\le Q^{-9/10},\quad |D|\le Q^{-21/25},\quad
|K|\le Q^{-37/50}.
\]
The limiting product is \(KV\), whose exponent is exactly \(-17/10\). All other products in the proof have stronger decay. The constant and summable majorant remain unchanged.

The implementation below propagates this estimate through the actual normal product and source correction; the remaining physical contour comparison is tracked separately.

## Explicit chosen data and continuation

The additional source budget is now constructed directly. Every HighData record already implies
\[
\epsilon,e\le t/2000,\qquad e\le\ell_{\min}/4.
\]
Only the auxiliary values \(\mathrm{eps}\) and \(\sigma\) are decreased:
\[
\mathrm{eps}'=\min(\mathrm{eps},t/(N+8)),\qquad
\sigma'=\min(\sigma,\ell_{\min}/4).
\]
Every original budget and height-choice property is preserved. The source
slot list, \(t\), \(r_{\min}\), \(\epsilon\), and \(e\) remain identical.
This preserves any prescribed fine mesh.

The implemented bounds give central cost \(B\le18t\), hence
\[
B+49/881280\le49/440640.
\]
The fixed auxiliary parameter \(\Delta_0=10^{-6}\) also satisfies
\[
\Delta_0+\sigma+t/8+t/8\le49/881280.
\]
Thus the old continuous-gap parameter need not be sent to zero.

A convenient physical choice is now
\[
\boxed{\delta=e/48>0.}
\]
It gives
\[
24\delta=e/2\le\ell_{\min}/8,\qquad
\delta\le t/96000.
\]
If \(\beta\ge7/8-\delta\), then \(\beta+e>7/8\) and
\(\beta+8e>7/8\). The existing principal and small-row contour domains can
therefore be retained. The low-side error remains a separate arbitrary
positive parameter; it is not forced to equal \(e\), \(t\), or \(\delta\).

The local Euler estimate has also been propagated through the actual
normal product. The new sourceCorrection_analytic_wide and
sourceCorrection_bound_wide prove, with the same original character,
exclusion set and CorrectionTail,
\[
H\text{ is analytic on }\Re s>21/25,\qquad |H(s)-1|\le1/2.
\]

The implemented nonzero_of_probe_bounds_variable_boundary uses the
original signal and regularized Mellin identity. If
\[
J=O(Z^{\theta+c+\omega}),\qquad
J-\operatorname{signal}=O(Z^{\beta+c-\sigma}),
\]
with \(0<\omega<\beta-\theta\), \(\sigma>0\), \(\beta\le1\), and
\(21/25\le\theta\), it gives nonvanishing, subject to
\(s\ne1\) or \(\chi.\mathrm{residue}\ne1\), for
\[
\Re s>\max(\theta+\omega,\beta-\sigma).
\]
No contour is moved through possible zeros: the regularized product
identity is analytically continued from \(\Re s>1\).

The variable physical normalization has an exact source theorem as well:
normalized_source_double_residue_variable_x retains the original
principal residue, source multiplier, slot weights and normalizer, and
computes its signal shift as
\[
c=x/3-5/6+1/36.
\]
This is the source of \(c=-11/16-8\delta\) for the tilted choice.

### Actual principal remainder, uniform in the physical tilt

The arbitrary-\(X,Y,Z\) theorem ordered_remainders_scale_bound can be
specialized to the tilted scales without changing its constant or contours.
The new source_scale_identity_variable_xy proves the exact exponent
\[
a+c(x)+(7/6-x)(\xi-1/6)+y(\upsilon-1).
\]
For the two original remainder contours, relative to \(a+c\), this becomes
\[
\frac{13}{16}e-\frac{23}{960}+\delta(24e-3/5),
\qquad
-\frac{13}{9600}-\frac{\delta}{25}.
\]
For \(0<e\le1/1000\) and \(\delta\ge0\), both retain the original strict
saving. The two actual integral bounds have one constant \(C\) before
every nonnegative physical tilt, slot exponent list, bounded supported
window family and excluded prime pool.

The exact physical decomposition then gives
physical_principal_residue_remainder_tilted:
\[
\|\text{weighted principal-row sum}-\text{source residue integral}\|
\le \frac{C}{e}\,
Z^{\beta-11/16-8\delta-17/48000}.
\]
This uses \(7/8<\beta+e\le2\), the original tuple injectivity and exclusions,
and the same source multiplier. The constant can depend on the character,
slot count, fixed Schwartz profiles, support bounds and \(e\).
Division by the outer normalizer has not occurred in this theorem;
its existing inverse bound costs an arbitrary additional exponent \(\nu>0\).

The large-tail integrand's row exponent moves by \(24\delta\), while
its constant term \(1+x/2+y=53/32\) stays fixed. Keeping the original
row cutoff \(U=Z^{13/16+t}\) leaves the positive contour buffer
\(t-24\delta=t-e/2>0\). Thus this part of the source audit does not require
enlarging the central row set or its moment-conductor range.

The previously verified local declarations are now consumed by the complete LOW and HIGH drafts described below. Every new declaration is submitted to the same warning-fatal Lean check.

## Complete consumers drafted

The entire source-to-endpoint chain is now written. Compilation, the exact endpoint type check, the standard-axiom whitelist and live proof dependency audit remain the acceptance gates.

| File | Actual conclusion or role |
|---|---|
| VF919TiltedLowReflection.lean | Complete reflected row energy with physical exponent S−2d, including the empty selection and every inactive subset |
| VF919TiltedLowPhysical.lean | Gram reconstruction, physical scale, inverse normalization and arbitrary LOW loss |
| VF919TiltedProbe.lean | One definition of the actual normalized compensated probe and its fixed-tilt LOW estimate |
| VF919TiltedHighTails.lean | Small and large physical tails, cube errors, and canonical decomposition |
| VF919TiltedHighCentral.lean | Floor and nonfloor central integrals from unchanged arithmetic moments |
| VF919TiltedHighPrincipal.lean | Exact residue and signal scaling; actual normalized weighted principal estimate |
| VF919TiltedHighTransport.lean | Complete normalized error transport with all four original errors |
| VF919TiltedHighAssembly.lean | Complete HIGH estimate with independent arithmetic parameter Delta=10^−6 |
| VF919NativeStrictSevenEighths.lean | Internally supplied native moments, identical-probe estimates, and strict supremum contradiction |
| VF919NativeStrictMertens.lean | Exact transfer to native Mertens growth and the complete signed-pair bound |

All files have prefix `research/oai_434/` in the proof PR. They retain the original signed rows, masks, excluded primes, weights, normalizer, character dependencies, bin populations, and height restrictions.

### Full LOW accounting

The reflected estimate is carried through retained and discarded rows, global completion, tuple dyads, inactive subsets, and the actual source punctures. The source slot charge is fixed:

\[
24\delta<\ell_{\min},\qquad\delta=D.e/48>0.
\]

For each nonempty outer selection, a whole source slot pays that charge. Empty active selections have actual dyadic width zero. Restricting to an inner inactive subset preserves the outer nominal length and its already paid gate.

The physical row energy has exponent

\[
S-2d+507\varepsilon.
\]

The inverse normalization cancels the same S; the Gram scale contributes

\[
(5x+y)/12=3/16-9\delta.
\]

The final LOW theorem allows every independent positive loss omega:

\[
J_{\eta,\delta}(Z)
=O_{\eta,\omega}\!\left(Z^{3/16-9\delta+\omega}\right).
\]

The physical tilt does not shrink when omega shrinks.

### Full HIGH accounting

The exact norm ratio of the physical Mellin weights is

\[
Z^{\delta(24r+12u-24)}.
\]

On the small contour it is `Z^(−246 delta/25)`. On the central contour the additional exponent is at most `−249 delta/25`. Both dominate the `−8 delta` required by the shifted principal signal. The large contour pays the positive `24 delta r` charge using `zeta−24 delta>0`; its arbitrary-saving parameter is increased explicitly. Cube truncation and finite aggregation retain their original payments.

Every normalized transport error consequently carries the same `−8 delta` shift. The original geometric, principal, window and large-tail budget inequalities remain applicable. The unchanged central arithmetic moments use the fixed positive parameter Delta0=10^−6; the explicit reserve pays

\[
\Delta_0+\sigma+\nu+\operatorname{dyadCost}
\le49/881280.
\]

The source moment degree is selected before the character. The original height-choice theorem selects one height exponent after that degree and before the character. It absorbs the polynomial height factor into the existing `Z^t` moment allowance. No unproved moment or probe certificate is passed into the final endpoint theorem.

The resulting HIGH statement is

\[
J_{\eta,\delta}(Z)
-\operatorname{signal}_{\eta,H_\eta,-11/16-8\delta}(Z)
=O_\eta\!\left(Z^{\beta-11/16-8\delta-\sigma}\right).
\]

It is the same `SourceData.tiltedProbe` used in LOW.

### Strict endpoint argument

First use the already verified native replay to obtain beta≤7/8. If strictness failed, beta would equal 7/8. Choose the fixed auxiliary data and tilt before any character. Set

\[
\theta=7/8-\delta,\quad
c=-11/16-8\delta,\quad
\omega=\delta/2,\quad
m=\min(\delta/2,\sigma)>0.
\]

The LOW exponent is exactly theta+c+omega; the HIGH exponent is exactly beta+c−sigma. The wider correction remains analytic and within 1/2 of one on Re s>21/25, and delta<1/960 implies 21/25≤theta.

The proved variable-boundary continuation theorem therefore excludes a zero above

\[
\max(\theta+\omega,\beta-\sigma)
=\beta-m<\beta.
\]

The primitive-supremum theorem supplies a primitive zero with real part greater than beta−m. The original finite-deletion mask transfers that zero to the exact character used by the probe, including the nonpole condition. This contradicts continuation.

The drafted terminal theorem has no hypotheses:

```lean
native_beta_lt_seven_eighths : HeckeZeroSupremum.beta < 7/8
```

Its drafted corollaries assert one positive global gap and a common improved zero-free half-plane for every character. The equality-exclusion argument does not identify that global gap with the physical tilt; no numerical gap or Riemann Hypothesis conclusion is asserted.

### Return to actual rational Moebius sums

The additional native consequence uses the exact Dirichlet-to-Hecke product at the principal character modulo one. An actual nontrivial zeta zero is therefore an actual zero of that Hecke L-function. The already proved native converse then gives

\[
\lambda_M=\Theta_\zeta\le\beta_{\mathrm{Hecke}}<7/8.
\]

No equality of rational Moebius signs and ideal-character phases is asserted. The actual transfer is through the L-function product and the independently proved Mertens growth/zero-boundary identification.

The drafted Mertens corollary has the full order

\[
\exists g>0\quad\forall\varepsilon>0\quad\exists C_\varepsilon\ge0
\quad\forall x\in\mathbb N,\ x\ge1:
\quad |M(x)|\le C_\varepsilon x^{7/8-g+\varepsilon}.
\]

Applying the exact native Green--Kubo identity preserves every pair and the squarefree diagonal:

\[
K_x+2C_x=|M(x)|^2,
\qquad
2C_x\le\bigl(C_\varepsilon x^{7/8-g+\varepsilon}\bigr)^2-K_x.
\]

The proof also spends half the positive gap to obtain a fixed power bound with exponent strictly below 7/8. This is an all-prefix statement; it does not substitute a sum of shell squares for the square of the complete signed sum.

## Review and verification

Root wrote the proof chain. Same-model agents separately reviewed the finite-slot geometry, physical HIGH transport, fixed-data reserve, native height quantifiers and terminal contradiction. Their source reviews found no remaining mathematical defect. This is not a claim of statistical independence and does not replace Lean checking.

Verification runs only in the pinned GitHub Actions environment. Every target uses `-DwarningAsError=true`. The workflow collects independent component diagnostics but fails if any target fails. The final audit checks the entire unconditional endpoint type, allows only `propext`, `Classical.choice`, and `Quot.sound`, and requires actual proof-value dependencies on the native source moments, tilted LOW, tilted HIGH, actual principal comparison, and variable-boundary continuation.

Acceptance requires all these checks to pass at the identified head. The proof PR records the checked head and run. No main-branch or merged proof claim is made.
