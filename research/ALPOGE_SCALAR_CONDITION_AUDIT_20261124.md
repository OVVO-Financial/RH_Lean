# Return #1201 to the scalar-bound cut

**Status:** proposed native scalar cost proofs; exact-head hosted verification
required. The critical geometric top-excess estimate and RH remain open.

Pinned original scalar definitions:
- [HostFactsS](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean).
- [GrowthInequalityHypotheses, SmallCosts, SizeWindows](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean).
- [cost_proposition_at_scale](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ConductorsKronecker/CostPropositionBasicBound.lean).

Native baseline main@9f84aae95729d566d4aa7189584620fbd0e1099a, prior #1201 head eee6c7af97e8ddef4a00108004fbd6c95cf44738.
The two-parent integration preserves every previous #1201 source and
imports the exact later main declarations. The only overlapping differing
file was RHLean.lean; both sides only added imports, so its resolution is
their sorted union. No completed external RH theorem is imported.

## 1. Complete 43-condition audit

The four bundles contain 43 immediate fields/conjuncts, not 43 independent
geometric problems. The following is a **consumer-level replacement audit**:
"Replaced" means the original literal premise is not needed in the chosen
native theorem, not a proof of the corresponding upstream structure for an
unconstructed instance. "Paid" means the listed native lemma proves it under
its actual retained parameter hypotheses. "Realize" means an actual compatible
family must still supply the stated relation. "Open" means a quantitative
supplier is not established. All statuses are source inspections unless an
exact-head hosted result is explicitly given.

Use
[nativeConstructedDyadicGzPayment](../RHLean/Analysis/AlpogeThin/NativeConstructedDyadicGzPayment.lean)
and
[nativeConstructedDyadicSignedSlopePayment](../RHLean/Analysis/AlpogeThin/NativeConstructedDyadicSignedSlopePayment.lean)
on their actual selected PageN exponent and PairGood prime pair. Their
conclusion is initially a **mean** of Gz at the physical heights. The
new scalar recovery below accounts for that difference.

### HostFactsS (8)

| ID | Original requirement | Native status and source |
|---|---|---|
| H01 | D.d prime | Replaced: PairGood.pair.d_prime in the actual selected pair. |
| H02 | 2 in S | Replaced: dyadic arithmetic host, no separate S input to native payment. |
| H03 | q1 in S | Replaced: selected q in the actual conductor/reciprocity host. |
| H04 | d not in S | Replaced: distinct selected prime data; the native d-inertia term is kept separately. |
| H05 | unramified outside S and d | Paid in the native host: nativeDyadicHostData_inertia_unramified. |
| H06 | split inertia at S | Replaced by native type-I and actual prime-power weight lemmas, not a freely selected inertia table. |
| H07 | split Frobenius at S | Replaced by the same native type-I/prime-power decomposition. |
| H08 | inertia at d equals two stated elements | Paid by nativeDyadicHostData_mem_inertia_d and nativeDyadicHostData_inertia_d_card. |

Source: [native host prime-power weights](../RHLean/Analysis/AlpogeThin/NativeDyadicHostPrimePowerWeights.lean),
[native host windows](../RHLean/Analysis/AlpogeThin/NativeDyadicHostWindows.lean).
The actual Gz payment does not assume HostFactsS as a record.

### GrowthInequalityHypotheses (16)

| ID | Original requirement | Native status and remaining input |
|---|---|---|
| G01 | 3 <= x | Paid by eventual threshold or actual square-clock scale. |
| G02 | 0 < b | Paid by b >= exp(x^eps); realize that width scale. |
| G03 | 0 <= eta | Realize native h >= 0 and its upper bound. |
| G04 | 0 < X' | Paid at X'=exp(x^(eps/3)). |
| G05 | 0 < b' | Replaced by actual beta > 0 and partner-ratio condition; realize widths. |
| G06 | b' X' <= x b | Replaced by actual nonthick ratio >= exp(x^(eps/3))/3; realize on the same profile. |
| G07 | 0 <= theta | Paid by selected exponential thin error. |
| G08 | 0 <= Cd | Paid by alpogeNativeMoveConstant_nonneg and native character movement estimates. |
| G09 | all top heights within 1 of x | Realize near-height family. New proof permits mean displacement cost <= 3*x^(1/2+eps) instead of pointwise unit distance; also require the actual heights in the selected analytic window. |
| G10 | NodeSizes T2 b b' eta w | Realize actual positive widths, thick interval, nonthick ratios, and selected beta. No replacement arbitrary profile is allowed. |
| G11 | sharp cutoff a/w <= N | Paid for the actual N=ceil(Amax/beta), given a<=Amax and w>=beta. |
| G12 | topExcess <= Err | OPEN: complete same-family signed top excess. This is the decisive supplier, not a definitional field. |
| G13 | ThinScales D ell X' theta | Paid in the native selected dyadic comparison at its actual conductor regime; realize its nonthick ratio condition. |
| G14 | LipW D ell | Replaced by native actual prime-power width/freezing comparison, with the original width conditions. |
| G15 | DerivInt D ell Cd | Paid by native Gz/character movement estimates. |
| G16 | ValuesAtX D ell x eps CL | Replaced by the selected PairGood window for the at-most-three nonprincipal characters. Their bound is not assumed for a fixed arbitrary character. |

Sources: [native dyadic cost windows](../RHLean/Analysis/AlpogeThin/NativeDyadicCostWindows.lean),
[native dyadic thick characters](../RHLean/Analysis/AlpogeThin/NativeDyadicThickCharacters.lean),
[native zeta balance](../RHLean/Analysis/AlpogeNativeZetaBalance.lean),
[native complete projection](../RHLean/Analysis/AlpogeNativeCompleteSourcePayment.lean).
Use the actual selected q,d throughout each window, not new pairs at every height.

### SmallCosts (3)

| ID | Original requirement | Native status |
|---|---|---|
| C01 | moveCost <= x^(1/2+eps) | Replaced by paid native mean-height movement, using available scalar headroom; displacement condition retained. |
| C02 | 2 f (x+1) theta <= 1/x | Paid by nativeDyadicCostWindows_eventually under actual host polynomial size and original thin scale. |
| C03 | 6 f (x+1) (eta+1) <= b/x | Paid by the same theorem on the native width deviation h, subject to its actual upper bound and b lower bound. |

### SizeWindows (16)

| ID | Original requirement | Native status |
|---|---|---|
| W01 | 3 <= x | Eventual threshold. |
| W02 | 0 < eps | Choose fixed positive eps < 1/52 before scale. |
| W03 | 0 <= C | Actual fixed cost exponent; verify its nonnegativity and uniformity. |
| W04 | 0 < n | Paid by actual finite group nonemptiness. |
| W05 | 0 < b | Paid by exponential lower bound. |
| W06 | 0 <= aE | Realize the actual nonnegative error scale. |
| W07 | aE <= 2 x b | Realize actual geometric scale, not an assigned value. |
| W08 | x^(-eps/8) n/2 <= nT | Realize actual top-set cardinality. |
| W09 | x^(-eps) <= nT2/n | Realize actual thick-set cardinality. |
| W10 | nT2 <= n | Paid by Finset.card_le_univ. |
| W11 | x^(1/2-eps) <= m | Paid on square clock m=R by alpogeNativeSquareMultiplicity_pageN_of_largeX. |
| W12 | m <= x^(1/2+eps/2) | Paid by the same theorem. |
| W13 | x m <= k | Paid numerically at k=x R; prove this is the physical parameter. |
| W14 | k <= n^2 x^(1/2-eps) | Paid numerically at k=x R on the same PageN host. |
| W15 | Err <= original explicit geometric bracket | Scalar accounting paid by normalizedCosts_add_remainder_le using the actual cost bracket. The signed excess bound G12 must still be earned. |
| W16 | 26 <= x^(3 eps/8) | Paid by alpogeNativeLargeX_of_threshold_le. |

Sources: [size absorption](../RHLean/Analysis/AlpogeThin/NativeGeometricCostWindows.lean),
[square multiplicity](../RHLean/Analysis/AlpogeNativeSquareMultiplicity.lean),
[large scale threshold](../RHLean/Analysis/AlpogeNativeZetaWindowWitness.lean),
[same-ideal lattice and theta realization](../RHLean/Geometry/NativeSquareHostRealization.lean).
The latter realizes base lattices and sections, not the measured rank, height,
thick-set, and loss witnesses of the final family.

## 2. New direct arithmetic payment

The original normalized local shift price is at most

    12*(log(4)+2)*c*ceil(Amax/beta)/(b*Delta).

Let E=exp(x^(eps/3)). On the original width regime b>=exp(x^eps),
beta>=b/(n E), c<=4 exp(x^(eps/4)), Amax/b<=x+1, n<=x^3,
Delta>=x^(-eps), and nonnegative shift/height data, we have

    ceil(Amax/beta) <= 4*x^4*E,
    12*(log(4)+2)*c*ceil(Amax/beta) <= 768*x^4*E^2.

For large x, 768*x^(5+eps)<=E and E^3<=b.
Consequently the complete normalized shift price is <=1/x, uniformly in
all physical parameters after eps is fixed. The native prime-power theorem
uses the actual cutoff and divisor to transfer this bound to the original
TT/lift/prime sum. This is one concrete part of the loss budget, not the
whole loss inequality: the low-central exclusions, local recovery gain,
the other local deductions, and their mean compatibility remain open.

The new global Gz movement follows by subdividing any interval [z,y] with
1<=z<=y into unit cells and applying the existing arithmetic move theorem.
It implies

    Gz(x) <= mean_TT Gz(v_t) + M*mean_TT |x-v_t|,
    M=log(4)+4.

The existing scalar proof has headroom 4*x^(1/2+eps). Its generalization
pays the entire remainder of that size; it preserves the original theorem
as a specialization. Thus the constructed signed-slope mean with analytic
price <=x^(1/2+eps) gives the original scalar exponent as soon as the
actual mean displacement costs <=3*x^(1/2+eps). No pointwise |v_t-x|<=1
is needed for this last recovery. The mean still has to come from the
actual geometric/analytic family. The square-size constructor specializes
the existing PageN multiplicity proof to this same scalar cost consumer.

Implementation:
[NativeScalarSupplierPayment](../RHLean/Analysis/AlpogeThin/NativeScalarSupplierPayment.lean)
and [terminal audit](ALPOGE_SCALAR_SUPPLIER_PAYMENT_AUDIT_20261124.lean).
These proofs require hosted checking; the audit does not certify unproved
premises.

## 3. Exact next mathematical suppliers

The already constructed dyadic signed-slope theorem retains the eleven
physical slope conditions (HidaSetting, DIV, EComp5, HComp, Count5, Slopes,
QuotientSlopeBoundsWith, LossBounds, SlopeIneq, HHBound, FParams) and strong
error windows and B0/Nc bounds. The native mean-loss comparison on main
can replace LossBounds by the two actual averaged inequalities. The
one-sided period comparison on #1201 can replace exact period equality,
using the existing period-DIV theorem; actual measured degree and
reverse derivative integrality are still required. The two substitutions
must be applied on the same physicalData, not independent witnesses.

Priority of the remaining work:
1. Construct the actual height/width/top/thick/recovery family on the same
   PageN and PairGood host at the square-clock parameters.
2. Pay the **complete** signed local recovery loss after the newly paid
   shift term, keeping low-central, ramified, dl/tauP and other costs;
   compare the actual gain and averaged losses.
3. Prove the measured quotient/degree/slopes and rank/mass budgets on
   that same family. Reuse actual native determinant descent, rank-growth
   jet budget and one-sided period direction, constructing geometry only
   where a specific remaining premise requires it.
4. Supply uniform constants and a simultaneous family on arbitrarily late
   complete multiplicative windows; use existing #1205 and #1206.
   The weaker cofinal square-window route must still cover every square
   in such a window and transfer to the complete real window; isolated
   favorable R do not suffice.

No independent proof of the missing complete Gz bound is claimed. Do not
restart downstream Landau, import a terminal RH theorem, or complete
unconnected geometric machinery merely because it occurs upstream.

## 4. Prior hosted failure and correction

The exact R20 head eee6c7a failed the mandatory preflight
[run 45320118677](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45320118677),
job 138196596172. The bounded diagnostic compiled NativeCMIsogenyPeriodMean
(including the one-sided class mean), NativeOneSidedIsogenyNorm,
NativeCMWeierstrassGroupTorsion and NativeCMWeierstrassMultiplicationUnramified.
It did not certify the full closure. The empty-product goal in
NativeCMLineBundleGenerators remained a reflexive-looking unit equality;
the attempted eq_self simp argument was unused. The correction now
explicitly closes the remaining goal after product simplification, using
reflexivity or unit extensionality. The original theorem is unchanged.
Full hosted preflight and axiom audit remain mandatory.
