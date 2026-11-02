# Finite-slot reflected gain and fixed-source uniformity

Date: 2026-11-02. Status: independently reviewed mathematical derivation; Lean source prepared for warning-fatal GitHub Actions. A new endpoint below \(7/8\) is **not** claimed.

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

The new file also proves the literal empty-tuple dyad identity. Composition through every downstream low-side caller remains unfinished; this local source theorem is not yet the final low probe bound.

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

All these declarations are submitted to the same warning-fatal Lean check.
They do not supply the two complete physical probe estimates.

## Remaining complete-consumer work

The remaining substantive task is to propagate the changed physical scales
through both estimates of one identical normalized compensated probe:

1. Carry the finite-slot gate and \(S=5/6-12\delta\) through the complete
   reflected low reconstruction. At LowDyads, empty active types use the
   exact zero-width theorem; nonempty outer selections retain their nominal
   mass through every inner inactive subset.
2. Generalize inverse normalization and the Gram scale with the same \(S\).
   The inverse identity cancels \(S\) exactly, and the Gram exponent becomes
   \(3/16-9\delta\). The final low error must remain arbitrary.
3. Propagate the tilted physical prefactors through the complete high cube,
   dyadic and tail reconstruction, and combine the now-proved raw principal
   remainder with the normalized window comparison, using the explicit
   fixed-data budgets above. The arithmetic moment suppliers are unchanged.
4. Apply the completed low and high bounds to the variable-boundary
   continuation theorem, then carry out the supremum contradiction and
   native signed-energy consequence.

The source-level audit found no numerical obstruction in this list.
It does not replace the missing composed proofs.

## Review and verification

Root derived and implemented the source estimates. The critical-family agent checked the exact slot geometry and downstream exponent costs. The signed-compensation agent separately checked the scalar branches, source argument mapping and finite-slot restriction. These are distinct same-model review sessions, not a claim of statistical independence.

Lean validation uses only pinned GitHub Actions. The existing workflow adds the new file to its warning-fatal proof compilation and axiom scan. The live dependency audit additionally requires the all-height source theorem and fixed-data certified band theorem in the original complete \(7/8\) replay.

No endpoint statement, source coefficient, central policy, axiom whitelist or existing validation gate is weakened.

