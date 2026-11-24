# Square-clock scalar and lattice realization, with the remaining family boundary

Date: 2026-11-23; actual lattice constructor and terminal-source audit added
2026-11-24. Baseline: `8e5f9b59ebacc022757e13ec6737c272633c13bc`.

## Result

At the native endpoint `x = R² - 1`, the integer choice **m = R** and real
parameter **k = xR** satisfy all four multiplicity/lattice-size fields of
`AlpogeNativeRestSize` on the **same previously selected dyadic host**.
The consumer's existing largeness threshold already suffices. No new
asymptotic threshold, host chooser, or prime-pair selection is required.

This result removes scalar parameter selection from P3. The added actual
lattice/theta corollary below also instantiates the existing geometric
constructor on the same host and prime pair, with measured lattice ranks.
It does not yet identify those objects with the required recovery/cost data.
P3's simultaneous physical realization, including the retained count and
height conditions, remains open. In particular, this is not a constructed
`AlpogeNativeZetaWindowWitness` and does not supply its `top` field.

The new module is
[`AlpogeNativeSquareMultiplicity.lean`](../RHLean/Analysis/AlpogeNativeSquareMultiplicity.lean).
Its proof text is complete; hosted Lean validation and axiom audit are handled
by the containing PR. No local Lean execution was performed.

## Exact parameter calculation

Let `R ≥ 2`, `x = R² - 1`, and `0 < ε < 1/52`. Then

\[
\sqrt{x}\le R\le2\sqrt{x}.
\]

If `2 ≤ x^(ε/2)`, this gives

\[
x^{1/2-\varepsilon}\le R\le x^{1/2+\varepsilon/2}.
\]

The existing `alpogeNativeLargeX ε C x` includes `x ≥ 3` and
`26 ≤ x^(3ε/8)`. Since `3ε/8 ≤ ε/2`, it already implies the needed
`2 ≤ x^(ε/2)`.

For any host cardinality `n ≥ x`, choose `k = xR`. The lower lattice
inequality is equality. The upper follows from

\[
\begin{aligned}
k=xR
&\le x^{3/2+\varepsilon/2}\\
&\le x^{5/2-\varepsilon}\\
&\le n^2x^{1/2-\varepsilon}.
\end{aligned}
\]

The middle inequality only needs `ε ≤ 2/3`, so the original range
`ε < 1/52` has ample room.

The constructed host's exact cardinality is `n = 2^e`. The original
`PageN ε x e` has lower bound `x^(2+8ε) ≤ 2^e`. Hence `n ≥ x` for
`x ≥ 1`. This argument applies to **every** exponent satisfying `PageN`;
it preserves the exponent selected by `nativeDyadicHost_windows` and the
prime pair used by `nativeConstructedDyadicGzPayment`.

## A necessary restriction on any alternative host

The new theorem `AlpogeNativeRestSize.source_scale_le_host_sq` proves

\[
\boxed{x\le n^2}
\]

from the existing size regime and `x > 0`, without extra density or
positivity assumptions. Indeed,

\[
x\,x^{1/2-\varepsilon}\le xm\le k
\le n^2x^{1/2-\varepsilon},
\]

and the common real power is positive. A fixed small host cannot satisfy
this size regime on arbitrarily large windows. The constructed dyadic host
has sufficient size; a replacement square-block module must retain enough
host capacity or prove a genuinely different normalization and budget.

## Exact remaining inputs of the size supplier

`alpogeNativeSquareMultiplicity_pageN_of_largeX` retains:

* `0 < b`;
* the actual height/cost inequality `aE ≤ 2xb`;
* the actual top count `x^(-ε/8) n / 2 ≤ |TT|`;
* the actual thick density `x^(-ε) ≤ |T2|/n`.

It supplies the other four fields with `m=R`, `k=xR`. The eventual theorem
`alpogeNativeSquareMultiplicity_pageN_eventually` uses exactly
`alpogeNativeLargeXThreshold ε`.

There is no replacement of measured `aE` by a chosen formula, no replacement
of geometric rank by a cardinality, and no assignment of the desired source
bound to a field. The result is intentionally universal in the actual counts
and actual `aE` condition. Selecting the full host as both top and thick set,
or assigning constant heights, would be only a scalar consistency example
until those choices were proved compatible with the recovery maps and global
cost object; that example is not used as a physical supplier here.

## Window and source audit

The attachment's final analytic implication matches the existing source
types, with these requirements retained:

1. `alpogeNativeGz_windows_of_witnesses` first fixes the exponent constant
   `C` and positive admissible `ε₁`; for each desired `η>0` it chooses a
   sufficiently small `ε`. Its source bound is conditional on actual
   witnesses on complete windows.
2. `riemannHypothesis_of_Gz_windows` requires a fixed `δ>0`, then for each
   `η>0` a constant uniform in every point of arbitrarily late windows
   `[Y,Y^(1+δ)]`. Isolated good scales do not satisfy that type.
3. `riemannHypothesis_of_squareClock_Gz_windows` requires every integer
   radius in the corresponding root window. Its interpolation preserves
   the one-sided sign and charges the complete between-square correction.
4. `nativeConstructedDyadicGzPayment` constructs the arithmetic host and
   selected pair, and pays its analytic remainder. The output still
   contains the **literal complete physical top excess divided by Q**.
   It does not estimate that surviving quantity.
5. The constructed payment theorem controls the mean of
   `Gz(a_t/b)`. It requires every selected height to lie in the same
   selected pair's window. Comparing this mean with a prescribed `Gz(x)`
   still requires the actual height localization and its movement charge.
6. The local recovery, IO loss, global capacity, counts, heights, and widths
   must coexist on one family. Separate existence of a good local profile
   and a good global profile does not prove this. A combined average can
   select one profile only after the combined native cost is bounded with
   all necessary signs and nonnegativity conditions.

The finite weighted candidate identity and the complete NNS history retain
proper prime powers and the initial-site correction. No bare prime-count
bound was substituted for this completed arithmetic source.

## Acceptance capsule

```text
descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1
tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1
SOURCE=native x=R²−1, existing PageN host, unchanged RestSize predicates
SUPPLIERS=alpogeNativeDyadicH_card; PageN lower bound; existing LargeX threshold
CONSTRUCTION=m=R; k=xR, on every existing admissible dyadic host
PROVED_CONTENT=integer multiplicity bounds; lattice parameter bounds; x≤n² necessity
RETAINED_INPUTS=actual top/thick counts, b>0, actual aE bound
FIRST_UNPAID=physical recovery and capacity object realizing those same parameters
FORMAL_STATUS=proof text supplied; containing PR owns hosted Lean/axiom verification
T_C_P=smaller scalar witness burden / elementary reusable restriction / RH open
```

## 2026-11-24 addition: actual lattice and theta sections on the same ideal

The new module
[`NativeSquareHostRealization.lean`](../RHLean/Geometry/NativeSquareHostRealization.lean)
imports only `RHLean.Geometry.NativeThetaNonzeroSection` and adds four
theorems. The principal corollary, `nativeSquareHost_exists_lattice_theta`,
takes exactly `R,e,q,d : Nat`, `2 <= R`, `epsilon,Y : Real`,
`0 < epsilon`, `PageN epsilon ((R^2-1 : Nat) : Real) e`, and
`WinPair epsilon Y q d`.

It uses these already selected `e,q,d`. Primality follows from the supplied
pair, `2 <= e` follows from `nativeDyadicPageN_two_le` and `R²-1 >= 3`,
and the original host hypotheses follow from
`nativeDyadicHostHyp_of_winPair`. No second host or prime pair is chosen.

The elementary results `nativeSquareHost_scale_ge_three`,
`nativeSquareHost_chain_size`, and `nativeSquareHost_chain_dimension`
establish, for every `R >= 2`,

\[
3\le R^2-1,\qquad R+3\le (R^2-1)R,\qquad
(R^2-1)R+R-1=R^3-1.
\]

The corollary invokes the existing
[`nativeDyadicHost_exists_nonzeroThetaSections`](../RHLean/Geometry/NativeThetaNonzeroSection.lean)
**once**, retaining its one ideal `B`, its half-different factorization,
coprimality with the conjugate ideal, and Galois invariance. For this same
ideal, `twistedLattice_rank` and `twistedLattice_rank_int` prove

\[
\begin{aligned}
\operatorname{rk}_{\mathcal O_E}
 (\operatorname{prescribedLattice}(H,B,(R^2-1)R,R))&=R^3-1,\\
\operatorname{rk}_{\mathbb Z}
 (\operatorname{prescribedLattice}(H,B,(R^2-1)R,R))&=(R^3-1)(4\,2^e).
\end{aligned}
\]

The second equality uses the actual field-degree theorem
`nativeDyadicHostRaw_finrank_E` and `nativeDyadicFrame_ord`. These are ranks
of the literal inverse-ideal lattice, derived by the existing localization
proofs; they are not assigned fields in a newly invented bundle. The rank
is much larger than the chain multiplicity `R` and must remain in any
subsequent norm or cost calculation.

For every `1 <= j <= R`, the conclusion preserves the original prescribed
geometric datum and period map, a positive definite Hermitian form whose
imaginary part is the prescribed alternating form, and a nonzero
holomorphic theta section. It retains the exact automorphy factor and the
invariant fiber norm identity. The ranks and every theta section use the
same `B`; two separately selected existential ideals are not combined.

This is a genuine nonempty geometric construction from the displayed
host/pair premises, which are already supplied by the constructed arithmetic
family. It is not a constructor of top/thick sets, localized measured
heights, integral recovery maps, Petersson masses, or the required signed
gain/cost estimates. In particular, `WinPair` alone does not place the
as-yet-unconstructed ratios `a_t/b` in the pair's arithmetic window, and
the geometric period is not yet identified with `Data.logOm`.

The global-cost task independently reviewed this corollary against its
theta and lattice-rank suppliers and found no mathematical or visible Lean
defect. The proof text and `git diff --check` are complete. Hosted Lean and
axiom verification remain the containing PR's responsibility; no local Lean
execution was performed.

## 2026-11-24 addition: actual terminal theorem and complete-source audit

The audited direct terminal declaration in
[`AlpogeNativeSquareClockCriterion.lean`](../RHLean/Analysis/AlpogeNativeSquareClockCriterion.lean)
has precisely the following arithmetic input:

\[
\forall\eta>0\ \exists C\ge0\ \exists R_0\
\ \forall R\ge\max(2,R_0),\qquad
\operatorname{nativeAlpogeGz}(R^2-1)\le C R^{1+\eta}.
\]

`riemannHypothesis_of_eventual_squareClock_Gz_rpow` has no additional
geometric premise, no two-sided estimate, and no hidden second source-bound
hypothesis. Its conclusion is Mathlib's original `RiemannHypothesis`.
The proof applies the displayed hypothesis at `2*eta`, uses
`R² <= 2*(R²-1)`, and invokes the square-clock window theorem with
`delta=1`. This establishes sufficiency, not the missing input estimate.

The definition in
[`AlpogeSquareClockSignedHistorySampling.lean`](../RHLean/Analysis/AlpogeSquareClockSignedHistorySampling.lean)
is the exact completed source

\[
G_z(N)=N\sum_{n=1}^{N}\frac{\Lambda(n)}n
       -\sum_{n=1}^{N}\Lambda(n)-N\log N+(1+\gamma)N.
\]

Both `nativeLambdaRecip` and `nativePsi` retain the true von Mangoldt
function on all prime powers. The NNS/history bridge retains its initial
site and harmonic/logarithmic correction. The theorem
`alpogeNativeGzArithmetic_natCast` in
[`AlpogeNativeWindowLandau.lean`](../RHLean/Analysis/AlpogeNativeWindowLandau.lean)
identifies the real arithmetic source at natural inputs with this source.
Neither a prime-only sum nor an uncentered counting function is substituted.

The square-clock and real-floor interpolation proofs keep the one-sided
upper-bound direction. Their safe slope is `log 4 + 2 + |gamma|`, supplied
unconditionally by the elementary first-Mertens bound. The conversion to
real windows charges at most `6*nativeAlpogeSafeSlope*y^(1/2+eta)`.

The weaker window consumer fixes `delta>0` and requires

\[
\forall\eta>0\ \exists C\ \forall A_0\ \exists A\ge A_0\
\ \forall R\in\mathbb N\cap[A,A^{1+\delta}],\qquad
G_z(R^2-1)\le C(R^2-1)^{1/2+\eta}.
\]

The constant is chosen before the arbitrarily late window. Every integer
radius in the window is required. Isolated good scales do not meet the
type, and this weaker premise has not been promoted to all-scale control.
The real-window version has the analogous complete interval
`[Y,Y^(1+delta)]` and preserves the same quantifier order.

The source audit also followed the actual analytic suppliers in
[`AlpogeNativeWindowMellin.lean`](../RHLean/Analysis/AlpogeNativeWindowMellin.lean),
`AlpogeNativeWindowLandau.lean`, and
[`AlpogeWindowLandauCriterion.lean`](../RHLean/Analysis/AlpogeWindowLandauCriterion.lean).
`alpogeNativeGzArithmetic_poleData` constructs measurability, crude
exponential growth, the actual Laplace transform, isolated poles and local
pole expansions without a Gz upper-bound hypothesis. The transform is

\[
\frac{1+\gamma-
 \operatorname{dslope}(\operatorname{logDeriv}\zeta_1)(1,s)}s.
\]

At a zero `rho` of multiplicity `m>0`, its residue is
`-m/(rho*(rho-1))`, nonzero and positive when `rho` is real and
`0<rho<1`. The one-sided `WindowLandau.landau_window` consumes these pole
facts and the displayed complete-window bound to exclude zeros to the
right of the target line. The native RH theorem then applies the actual
completed-zeta functional equation to the left side. The source audit
found no hidden copy of the desired bound inside the pole-data constructor.
Source inspection remains distinct from a new hosted kernel verification.

## 2026-11-24 addition: first unmatched same-family substitution

The exact current stopping point is exposed by
[`nativeConstructedDyadicSignedSlopePayment`](../RHLean/Analysis/AlpogeThin/NativeConstructedDyadicSignedSlopePayment.lean).
After selecting the exponent and prime pair once, it universally quantifies
over `TT`, `T2`, `a`, `b`, `w` and an arbitrary geometric
`WeightedMeanData.Data` value `D0`. Its `Ds` sets only `x`, `epsilon`,
and `b`; `physicalData` attaches native arithmetic entries while preserving
the other geometric data. It still requires on that same data:

```text
HidaSetting, DIV, EComp5, HComp, Count5, Slopes,
QuotientSlopeBoundsWith, LossBounds, SlopeIneq, HHBound, FParams,
ErrWindows, LargeX, and the original B0 and Nc budget inequalities.
```

The same-host theta constructor has no `TT`, `T2`, `a`, `aE`, `Ga`, or
`IO` output. No constructor in the inspected native source turns that
theta output into a measured `D0` satisfying these hypotheses. The first
missing compatibility premise is the joint attachment of actual section
recovery, mass/rank data, top/thick sets, localized heights and widths to
the same family used for the global cost. Choosing full subsets or constant
scalar heights does not prove that attachment.

The existing short-section and descent infrastructure was also checked.
[`exists_short_integral_HHa_spanning_family`](../RHLean/Geometry/NativeThetaSpanningFamily.lean)
constructs an actual bounded polynomial family.
[`exists_short_integral_HHa_evaluation_family`](../RHLean/Geometry/NativeThetaEvaluatedFamily.lean)
still takes formal germs as inputs; its image-span statement does not
construct the desired physical cusp-space span.
[`NativeTheta.SectionRealization.existsUnique_value`](../RHLean/Geometry/NativeThetaSectionRealization.lean)
descends supplied jets using faithfully flat algebra and a `PhaseTransport`
premise. The native analytic theta output does not yet supply those inputs
on the required arithmetic family. These theorems remain reusable; they
are not counted as completed recovery/mass estimates.

Thus P3 now has both valid scalar sizes and an actual prescribed lattice
with a nonzero analytic theta chain at those sizes on the same selected
host. Simultaneous physical recovery, capacity, counts and localization
remain open. No new interface carrying the desired source bound as a
field was introduced, and no further construction targets were added.

```text
semantic_acceptance_ack=NATIVE_BOUND_SEMANTIC_ACCEPTANCE_V1
ADDED_SUPPLIER=nativeSquareHost_exists_lattice_theta
SAME_WITNESS=one selected e,q,d and one half-different B for ranks and all theta sections
MEASURED_RANKS=R^3-1 over O_E; (R^3-1)*(4*2^e) over Z
TERMINAL_AUDIT=direct square-clock theorem requires only the displayed complete one-sided Gz estimate
FIRST_UNPAID=measured recovery/cost data on that same section family, with actual TT,T2 and localized heights/widths
FORMAL_STATUS=source complete and independently reviewed; hosted checks pending containing PR
T_C_P=smaller scalar and base-lattice witness burden / genuine same-host corollary / critical source bound and RH open
```
