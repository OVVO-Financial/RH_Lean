# VerifyTask integration: use existing proof suppliers, not a new proof program

**2026-11-24.** Applied to final proof PR #1201, starting at `73a4979c7a1c42e28798fb3fd47063f0d656c2f6`.
Status: exact statements and upstream source inspected; new native audit
submitted for hosted Lean verification. No claim of new RH-strength
estimate or full Comparator replay.

## 1. Pinned evidence and selection

[VerifyTask](https://riemann.verifytask.cn/?lang=en) reports 39 numbered
benchmark components covering a 92.23% deduplicated subset of the archive
on November 23. This is scope, not percentage of whole-proof compression.
Its staged submissions are standalone benchmark proofs, not merged native
suppliers. The [collaboration fork](https://github.com/Osgood001/riemann-hypothesis)
explicitly reserves integration for author confirmation, licensing and
toolchain/interface checks. Do not copy contestant proof code or treat a
leaderboard score as a dependency certificate. No change of toolchain,
manifest or external compiled-artifact dependency is authorized here.

| Pinned benchmark | Exact useful result | Native consumer / disposition |
|---|---|---|
| [Core 6 #99242](https://github.com/Osgood001/riemann-hypothesis/pull/7) at `d9942073f3ef3314068344b6ce67f0a49a4a4e11` (64.29% token reduction) | `JInvariantIntegrality ∧ CM3` | Direct: existing `NativeCMIdealClassModels.latticeCurve_j_integral_of_order_stable` (namespace `NativeCM.Weierstrass`), actual `fractionalIdealPeriod_j_integral` in `NativeCMInverseIdealClassModels`. Freeze and independently prove the first conjunct from native results, below. CM3 concerns the inert-prime formal logarithm at a good model, not general DVR extension or the period mean; only use if a surviving local prerequisite requires it. |
| [Core 7 #99236](https://github.com/Osgood001/riemann-hypothesis/pull/8) at `3f9bde59bad2dd779407afd0ef420c17fd71857f` (98.41%) | Prime ideal and nonvanishing polynomial imply preconnected complex basic open | Reserve for a real connectedness gap. `NativeCMWeierstrassIntegralExtension` already follows the finite graph and Mathlib relative normalization/smooth base-change route. Do not replace it with a general irreducibility construction. |
| [Core 8 #99219](https://github.com/Osgood001/riemann-hypothesis/pull/9) at `2e19007ee54544988e68a6fd243bf3ad52e876a8` (43.48%) | `SeriesEqDens ∧ UnrFormula`: convergence of the local Siegel series to the density and the actual unimodular Hermitian density product | High priority if the local matching step in actual `ChainTied` requires this. Identify the same local form, uniformizer, characters, residual q, epsilon sign, ranks and measure; the result is not itself the signed arithmetic recovery or a global Petersson measure. |
| [Core 9 #99253](https://github.com/Osgood001/riemann-hypothesis/pull/10) at `752a74314eb2eb7f4a2625e166e68dd1b37a021f` (94.55%) | `GelfandGraevMultOne`: Whittaker functionals on an irreducible GL representation over a finite field are scalar multiples | High priority only at the actual local theta/Whittaker matching gap. It does not prove nonzero global cusp sections, their normalization or their measured rank/mass. |
| [Core 10 #99249](https://github.com/Osgood001/riemann-hypothesis/pull/11) at `8bb8025387dbb6e81ab4493d791487c4ff572701` (40.92%) | `UpperTheory.Esk.TF` (torus trace formula) | Inspect actual trace-formula hypotheses against the original theta/Petersson realization in `NativeMeasuredComponentNorm` and signed slope. No GRH specialization or scalar mass assignment. The staged README's informal GRH summary is not its theorem. |
| [Core 11 #99154](https://github.com/Osgood001/riemann-hypothesis/pull/12) at `fa380fd319907cc7fc9c6cafb450fc4013b3debb` (72.37%) | Injective holomorphic map on open complex domain has nonzero derivative determinant | Reserve for necessary geometric jet injection on an actual injective chart. The elliptic uniformization has a lattice kernel; do not claim global injectivity. |
| [Core 12 #99275](https://github.com/Osgood001/riemann-hypothesis/pull/13) at `b35625028c5dc22844761411db7cdc7574f11cb7` (68.91%) | Eight cyclotomic power-series rigidity, divisibility and Frobenius-splitting statements | Use only if needed to supply original local level-letter recovery. `NativeCyclotomicHost/Residue` already prove actual fixed-field, residue inertia and Frobenius, which are not the entire power-series claim. |
| [Core 13 #99274](https://github.com/Osgood001/riemann-hypothesis/pull/14) at `7a1531bf5cf905cb4ebe26f8152516516fbda282` (70.81%) | `BoxSumOne ∧ RecursionSharp ∧ LeadingMinorsCount` | Compare only against a surviving exact Hermitian curvature premise. `NativeJetRankBudget` pays the separate binomial jet cost; do not equate those statements by name. |

The core 1--4 classical analytic results are lower priority because the
native Landau consumer and ray inputs already exist; neither classical
zero-free-region bounds nor Siegel--Walfisz alone supply the critical exponent.
The new phase-3 benchmark coverage is not evidence that the new core
pillars have replacement proofs. Prioritize exact supplier matches, not
token rankings. The [disjoint pure-lattice simplification PR #25](https://github.com/Osgood001/riemann-hypothesis/pull/25)
is relevant to measured component decomposition only if it matches the
actual lattice orthogonality; native `NativeMeasuredComponentDegree.OrthogonalSum.rkK_deg_iSup`
already derives additivity from genuine norm-square orthogonality.

## 2. The exact Core 6 saving

Read the original
[CMGoodModels/Statement.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LocalToGlobal/TorsionIntegrality/CMGoodModels/Statement.lean).
The first conjunct states integrality of the literal invariant
(1728 g_2^3/(g_2^3-27g_3^2)) for a squarefree d congruent to 3 mod 4,
where multiplication by (1+i sqrt(d))/2 preserves the actual lattice.
Its second conjunct instead asserts an integral power-series coordinate
at inert good primes; it does not prove integral reverse isogeny extension.

The native route already normalizes the original lattice as
(a(\mathbb Z\tau+\mathbb Z)), cancels the nonzero a from the
multiplication-stability relation, and applies
`isIntegral_modularJ_of_mul_mem`. The literal Weierstrass j formula is
obtained from the actual c4 and discriminant formulas, rather than a
chosen height. The new `cmJ_native` proof checks the frozen first
conjunct on arbitrary original `PeriodPair` data using that existing
route. It retains the noninteger multiplier, derived from its nonzero
imaginary part. Existing actual ideal-class and inverse-ideal-class
constructors already call the order-stable version; keep them. This
eliminates a redundant Core 6 reconstruction obligation. It does not
construct the cross-model morphism or the local derivative integrality.

## 3. Adopt independent statement checking at the string's attachment

[Challenge](ALPOGE_VERIFYTASK_CHALLENGE_20261124.lean) imports only Mathlib.
It states the original CM invariant and the independently specified
complete principal prime-power sum, including Euler centering. The
window has fixed K and eps1, C outside the requested window, and
every y in [Y,Y^(3/2)]. The [native audit](ALPOGE_VERIFYTASK_NATIVE_STATEMENT_AUDIT_20261124.lean)
proves the CM statement, checks the actual cyclic source against the
literal sum, and checks the exact conditional type of the existing
#1205 handoff to root Mathlib RH. Six named roots are audited for the
three standard axioms. Existing changed-research hosted preflight
compiles these two files; no separate full CI workflow or rebuild
of upstream proof is added. The challenge is independent in its imports,
not an independent kernel replay. No new production RH endpoint.

For final acceptance use the [community Comparator method](https://github.com/leanprover-community/riemann-hypothesis):
freeze a Mathlib-only challenge, compare exact root types and imported
definitions, check transitive axioms and replay the actual proof closure
with independent kernels. Use a supported exporter/Comparator for the
pinned 4.34.1 (or separately verified export compatibility); avoid
changing the project pin just for this. A cached olean is not independent
replay. Do not require a full upstream rebuild on every repair. Run the
final independent check on the exact closed native theorem when it exists,
in addition to #1209's semantic audit. Do not claim Comparator passed
from the source-level check or from VerifyTask's unrelated benchmark.

## 4. Remain on the actual proof path

The existing principal cyclic source and window handoff already compile
on the earlier diagnostic. The quantitative theorem
`level_gm_le_on_family_scales` is an existing proved implication, not
an unconditional native witness. Its exact inputs are EFamC, actual
ChainTied at all sufficiently large points of Win, complete HasWindows
at 3/2, and fixed eD,eL,eps1. Do not restart the all-character GRH proof.
For each real missing premise use the original supplier and any matched
VerifyTask simplification; retain the same host, original periods,
all-place integral derivative, signed source, actual measures and the
entire cost budget. Close principal-window application first; stone
bridge compression second. All other candidate entries above are
SOURCE_INSPECTED only, not proof credit.

## 5. The community covolume supplier

Use `leanprover-community/riemann-hypothesis` at
`27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59` as the reference for this reduction.
Community PR #466 removed the vacuous geometry field and arguments. At this revision
`OAt` retains `LamAre`, which constrains the actual isotropy spaces and logarithmic
scalings. The community source uses Lean 4.37.0-rc1. The native declarations below
use RH_Lean's 4.34.1 definitions. The import counts recorded for #1211 describe
its frozen original revision. [Cleanup](https://github.com/leanprover-community/riemann-hypothesis/pull/466)
· [retained field](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean#L58-L74)
· [reference toolchain](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/lean-toolchain).

A whole-word source scan of all 59,582 `.lean` files under `src/` at this
revision found zero occurrences of `GeoP`, `anyGeometry`, `GeoCl` and
`geoCl`. The native audit separately traverses the types and proof terms of
its declared roots. The external replay template now imports the community
module containing `core_gm`. Running that template still requires a closed
same-host window supplier. [Pointwise theorem](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean#L1337-L1341).

The four original supplier declarations map to a different import graph at this
revision. The row declaration `galoisLocalGlobalStrong_recParameter` now lives
in `MainConclusion`. That module directly imports both `VwinOfRow` and
`EveryCharacterOfLiteratureOfVWin`. Its row proof applies
`galoisRepresentations_of_thetaLift` to `tLift_holds_k`. Only the final
member's recorded import header names the two large suppliers.
[Module imports](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L30-L35)
· [row proof and final consumer](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L923-L960).

| Community source import graph | Project modules |
|---|---:|
| Reachable from all four supplier modules | 59,543 |
| Saved by deleting the two explicit imports while retaining `MainConclusion` | 0 |
| Reachable from the other direct imports of `MainConclusion`, retaining `RecTExists` explicitly | 22,963 |
| Reachable exclusively through the two edges in that split, excluding `MainConclusion` itself | 36,579 |

These counts follow the actual module imports under `src/`, including public
imports, with each module counted once. The last two rows model an extraction.
To realize that saving while retaining the row proof, isolate it with its
geometric-realization and theta-lift inputs and verify the extracted proof.
The direct signed-cost route can instead establish the principal estimate
inside RH_Lean. The quantitative estimates on the chosen native host remain open.

| Step | What the community proof uses |
|---|---|
| Core 15 supplies `CovolumeBoundOfX` | The literature assembly passes `topCovolSlim2_use_alt_alt` as the covolume argument. [Call site](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L1472-L1478) |
| Core 21 consumes it | `nonempty_hyps_definite_side_of_closed_bound` passes `hX` once to `linked_bundles_l3_of_open_alt`. The final call consumes `hL3` at `GridA (max CF0 CF1)` together with the grid evaluation, row and Fourier inputs. The intervening selection uses actual row summands and `RecTied` on those points. [Assembly](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L1933-L1957) · [selection](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L1156-L1172) |
| The finite inequality | On the false branch of the selected summand's data, `L3` asks for every `j` that `lcv (S.XW j) (S.M j) / S.D ≤ N.l3 j`. In `IndefScale.num` this budget is `Z.l3m j + C * Z.l3u`. [Summand](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SummandFunctionalBound.lean#L85) · [budget](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean#L228-L235) · [inequality](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/LocalToGlobal/IndefiniteForms/IndefSide.lean#L319-L320) |

For a totally complex field, the native `normalized_lcv_le_of_gram_bounds`
uses a linearly independent frame in the actual integral lattice of the same
rank. If its Gram determinant at place $v$ is at most $B_v$, the height
formula gives

$$
\frac{\operatorname{lcv}(X,M)}{D}
\;\le\; \frac{2}{[K:\mathbb Q] D}
\log\!\left(\frac{\prod_v B_v}{[M:\langle e\rangle_{\mathcal O_K}]}\right),
\qquad D>0 .
$$

The index belongs to that frame in that lattice. To supply the Core 21
estimate, identify the selected `XW j` and `M j`, prove the place bounds,
and show that this expression fits the displayed budget with one admissible
`C` across the required points and summands. The ambient `S.D` and the
summand rank are separate inputs. [Native frame estimate](../RHLean/Geometry/NativeSummandCovolume.lean).

On the signed-cost route, independently measured count and degree periods
can be used as soon as `Pcount ≤ Pdegree` on each fiber. The degree/count
estimates, the order itself and the remaining signed estimates still need
proof on the actual dyadic host at each anchor. The target
remains one bound for all points of arbitrarily distant complete windows,
with the constant fixed before the window. [Native period comparison](ALPOGE_NATIVE_PAIRED_PERIOD_CAPACITY_20261124.md).

## 6. Recommended route on the native square clock

Use Cores 19 and 20 to locate what makes the evaluated rows recover the
source. Use Core 15 at its input to Core 21 to locate what pays for those
rows. Core 19 returns an evaluation grid, Core 20 gives a Fourier coefficient
fit, and Core 21 combines those results with the covolume estimate. None of
their statements identifies a row of the native square-block operator or
supplies its physical gain. Cores 16–18 build the upstream Galois and
automorphy route into Core 14's all-character conclusion. RH_Lean has a
principal-character host and its own window-to-RH theorem. The DAG observation
is from board revision `a3b23dd031e9861f`; the pinned community declarations
above determine the actual hypotheses. [VerifyTask map](https://riemann.verifytask.cn/?lang=en).

1. **Use one pair throughout a square-clock window.** Put $X_R=R^2-1$, $m=R$,
   $k=X_R R$. For $A\ge2$ and $A\le R\le A^{3/2}$, choose the pair from
   `nativeConstructedDyadicGzPayment` with external window exponent two
   and $Y=A^2-1$. Every evaluation in $[X_R,X_R+1]$ lies in $[Y,Y^2]$
   because $R^2\le A^3$ and $(A^2-1)^2-A^3=A^2(A-2)(A+1)+1$.
   `nativePrincipalEAtH_squareClock_of_pair` accepts that very pair and
   the actual dyadic exponent at $X_R$. The local size, physical height
   interval and density still belong to the constructed family.
   [Square-window inclusion and principal host](../RHLean/Analysis/AlpogeThin/NativePrincipalEAtH.lean)
   · [physical height interval](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean).
2. **Prove the finite-place gain on those rows first.** For one retained prime
   orbit, use the original Frobenius, inertia and partner map. Construct
   integral combinations of its evaluations that recover $p^D$ times each
   of $n$ independent coordinates, with $n\ge(1-\kappa)\dim V$. Bound
   evaluations on the other edges from the same source. This is the content
   of the community's `GoodRankK` and `LPprimeAt`.
   [Integral recovery and off-edge conditions](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L208-L223).

   A smaller first theorem is available. Fix the independent row functionals
   $\phi_i$ on the actual local target lattice $L$ and the exponent $D$
   allowed by the local budget before choosing coefficients. For each coefficient
   vector $c$ with a unit entry, exhibit $G\in L$ for which the integral
   value $\sum_i c_i\phi_i(G)$ divides $p^D$. The community theorem
   `goodRank_of_prim` converts this and integral linearity into the
   recovery map by Smith normal form. Its caller separately supplies the
   row count and off-edge divisibility. Test the coupled orbit rows here.
   On the plain native wheel, every difference iterate retains coefficient
   one at the first site of each prime-power fibre. Repetition alone cannot
   supply a positive valuation on that coefficient.
   [Primitive-combination theorem](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/GoodRankOfPrim.lean#L34-L65)
   · [use with edge and rank data](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/GoodRankOfPrim.lean#L109-L132)
   · [native wheel coefficient theorem](NATIVE_PRIME_POWER_RECOVERY_TEST_20261123.lean).

   The community's `admG1` makes two different measurements. Every retained
   vector satisfies a lower valuation bound involving the sum of the local
   gains. The quotient of the ramified lattice by the retained submodule
   has a length **upper** bound involving `tauP + ioP`. Identify the actual
   native partner widths, gain and errors as in `ParametersFill`. Prove
   their local inequality with the orbit deduction `dl`, the deduction
   `tauP`, and the allowances `lo` and `m*fl`. The native
   `nativeDyadicDe_re_le_localRetainedSource` supplies the prior signed
   upper bound including exclusions, shifts and ramification.
   `lengthFromAllBut_of_sandwich` handles the quotient once the lattice
   inclusions, exceptional layers and stopping exponent are supplied.
   The positive gain still requires the valuation estimate.
   [Local valuation and quotient length](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/SmallOrderPrimes.lean#L212-L223)
   · [identification of parameters](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L427-L437)
   · [primewise budget and orbit deduction](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean#L125-L156)
   · [native local source](../RHLean/Analysis/AlpogeNativeLocalGainSource.lean)
   · [lattice length](../RHLean/Geometry/NativeServedPrimeApplication.lean)
   · [exact deductions and existing bounds](ALPOGE_NATIVE_PHYSICAL_SUPPLIER_REDUCTION_20261123.md).
3. **Pay the global cost on the same family.** Attach the actual widths,
   quotient slopes, count and relative degree. Use the ordered period
   comparison and, where a summand covolume is needed, the frame estimate
   in §5. The community's `MeanKappaBound` averages over amplitude and
   height boxes. A native proof must either establish the corresponding
   defect budget directly for the subgroup average or prove the change of
   measure. Use that average to prove both
   $\operatorname{umean}(\mathrm{ASK}-\mathrm{Ga})\le\mathrm{LoP}$ and
   $\operatorname{umean}(\mathrm{IO})\le\mathrm{LoP}$. The physical numerator
   is the full signed top excess and its divisor is
   $Q=|TT|\,m b\,(|T_2|/|H|)/2$. Core 33 can supply a matching local
   stabilizer obligation. Core 36 applies when the actual period sublattices
   are pure and span. Both have narrower conclusions than this signed estimate.
   [Community defect average](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean#L350-L360)
   · [signed mean comparison](../RHLean/Analysis/AlpogeNativeSignedSlopeComparison.lean)
   · [Core 33 premises](../RHLean/Geometry/NativeCore33HostDegree.lean).
4. **Use the existing one-sided window theorem.** Apply
   `nativeGz_le_of_mean_normalizedCosts` with the actual average height
   displacement. The square-clock theorem requires that for each $\eta>0$ there be
   one $C_\eta$ such that for arbitrarily large $A$, every integer
   $A\le R\le A^{3/2}$ satisfies
   $G_z(X_R)\le C_\eta X_R^{1/2+\eta}$. This is the hypothesis of
   `riemannHypothesis_of_squareClock_Gz_windows` at $\delta=1/2$.
   Its proof transports the one-sided estimate across each whole real window.
   [Mean-to-point theorem](../RHLean/Analysis/AlpogeThin/NativeScalarSupplierPayment.lean)
   · [square-clock window theorem](../RHLean/Analysis/AlpogeNativeWindowLandau.lean).
