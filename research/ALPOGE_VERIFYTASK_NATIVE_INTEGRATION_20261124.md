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

The November 25 source check used community revision `251c7b05`, RH_Lean `c94fc79`, and VerifyTask board revision `4c156e9a205084bb`. The board identifies 19 → 20, 19/20 → 21, 15 → 21 and 21 → 14. Its 39 pillars include Cores 40 and 41. Core 41 treats nongeneric orbital terms in a Siegel-lattice trace formula. Its application here would require identifying a term of the native sum with that orbital integral. The community uses Lean 4.37.0-rc1 and the native project uses 4.34.1. [Pillar descriptions and revision](https://riemann.verifytask.cn/api/board) · [community toolchain](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/lean-toolchain) · [native toolchain](../lean-toolchain).

### What the upstream consumer reads

`PrimAt` tests every combination of the actual source products with a unit coefficient modulo the edge lattice. `TestAt` chooses one dual vector with bounded depth, integral on the selected edge and divisible on all competing incoming edges. `SrcTests` separately requires source sections divisible on competing outgoing edges and the quota $\sum_e n_e\ge(1-\kappa)\dim V$. `goodRank_of_prim` converts primitive tests into an integral decoder by Smith normal form. A unit coefficient in polynomial coordinates detects edge primitivity only after proving that those coefficient functionals are integral on the edge lattice. For example $1\in\varpi(\varpi^{-1}\mathcal O)$. [Primitive and dual tests](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/SourcePrimitiveIntegrality.lean#L292-L322) · [source sections and quota](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/ManyEdges.lean#L23-L35) · [decoder](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/GoodRankOfPrim.lean#L34-L77).

`admG1` is a predicate with three clauses. In `linkG_at_core`, the middle clause gives an upper bound for the length of the discarded quotient. The signed primewise inequality instead comes from `Conclusion1` and the gain identification in `ParametersFill`. The auxiliary `zeroCh` retains the levels and replaces the operator by zero. Its valuation clause holds for any lower bound and is discarded in this call. If a later slope estimate uses valuations of actual operator columns, `kernel_valuation_served` requires the separate comparison on those columns. [Definition](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/SmallOrderPrimes.lean#L177-L187) · [actual length and gain calls](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/PlaneCountTheoremWithConstants.lean#L598-L646) · [auxiliary construction](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/LocalToGlobal/GroupLattices/LinkGConcreteNoKer.lean#L1374-L1418) · [operator comparison](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/WeilJacquetShalikaLaw.lean#L317-L332).

### Native local recovery

At $x=R^2-1$, $m=R$, $k=xR$, `nativeSquareHost_exists_lattice_theta` constructs an actual period lattice of rank $R^3-1$ over the host's ring of integers and a nonzero complex theta section. The local quota counts sections in $V$. The first physical construction needed here is an integral pairing of those sections and dual evaluations on the same Frobenius edges, including the lattices on which each functional is integral. [Square host](../RHLean/Geometry/NativeSquareHostRealization.lean) · [formal evaluations and their input germs](../RHLean/Geometry/NativeThetaEvaluatedFamily.lean).

For integral maps $E,C$ on one lattice $L$, and submodules $P,K$ in their respective targets, the inclusion $P\subset E(C^{-1}K)$ is equivalent to $P\oplus0\subseteq\operatorname{im}(E,C)+(0\oplus K)$. On a chosen square frame write $A=E(v)$, $B=C(v)$, $\delta=\det A\ne0$, $a=p^D$, $b=\varpi^c$. There is an integral matrix $T$ with $AT=aI$ and $BT\equiv0\bmod b$ exactly when
\[
  \delta\mid a\,\operatorname{adj}(A)_{ik},\qquad
  \delta b\mid a(B\operatorname{adj}(A))_{jk}
\]
entrywise. This tests one and the same lift. Over a DVR the example $E(x,y)=x$, $C_1(x,y)=y$, $C_2(x,y)=x-y$ admits unit lifts separately and has joint image $\varpi^c\mathcal O$ under both congruences. Source-side and dual-side competitors require their respective integral presentations. [Block and adjugate criteria](../RHLean/Geometry/NativeJointEvaluationRecovery.lean).

For a polynomial on $0\le j_i\le d_i$, put $D_g=\prod_i d_i!$. Scaled interpolation places $D_g\,\mathrm{coeff}_m(P)$ in the ideal of its grid values. A unit coefficient yields a grid evaluation of valuation at most $v_\varpi(D_g)$. The monic polynomial $\prod_i(X_i)_{d_i}$ in falling-factorial notation attains exactly this cost at the upper corner and vanishes elsewhere on the box. Compare $v_\varpi(D_g)$ with $D\,v_\varpi(p)$. For the constructed leading-minor products, zero-one matrices distinguish column flags at depth zero whenever a positive-weight minor contains a missing column for every competing flag. Both tests still require mapping their grid evaluations to the admissible physical dual. [Integral interpolation, determinant polynomials and column tests](../RHLean/Geometry/NativeThetaIntegralGrid.lean).

The actual integer colour row for $p^i$ is the indicator of $i\,\mathrm{Frob}_p+I_p$. The original kernel is this indicator times $2/|I_p|$. The first $K$ powers have an identity minor of size $\min(K,\operatorname{ord}(\mathrm{Frob}_p\bmod I_p))$ on their representatives. Disjoint competitors vanish there. At odd $p$, both $2$ and $|I_p|$ are units locally because $|I_p|$ divides the power-of-two host order. A repeated coset gives identical colour rows. For the first-return exclusion from $t$, let $g=\mathrm{Frob}_p$. The exact conditions are odd $i$, central bit $g_{1,2}=1$, $i<\operatorname{ord}(g_H)$ and $t+i g_H\in TT$. They apply at every cutoff, including the cutoff $\lceil A_{\max}/\beta\rceil$. Recovery on the unrestricted site module still requires a lift to the physical section lattice with the required source and dual divisibilities. [Native prime powers and masks](../RHLean/Analysis/AlpogeThin/NativeDyadicPrimePowerIncidence.lean).

The normalized tail estimate removes the high unramified odd powers of exponent at least three from the critical-scale loss. Write $X=x+1$. For $p^i>X$, $i\ge3$, a positive-width ASK atom is at most $a_t/p^i\le a_t X^{\sigma-1}p^{-\sigma i}$. At $\sigma=3/8$, summing even over all integers $p\ge2$ and all $i\ge3$ costs at most
\[
 K=\frac{256}{1-2^{-3/8}}.
\]
Indeed, summing the geometric series costs $(1-2^{-3/8})^{-1}$ and $\log n\le16n^{1/16}$ gives $\sum_{n\ge2}\log n/n^{9/8}\le16\sum_{n\ge2}n^{-17/16}\le256$. Restore the native $2\log p$ weight, sum over $t,j$, take the subgroup mean and divide by $Q$. With $a_t/b\le x+1$ and $\Delta\ge x^{-\varepsilon}$ the normalized tail is at most $4K(x+1)^{3/8}x^\varepsilon$. The Lean estimate uses a fixed convergent-series majorant in place of this explicit paper constant. It is uniform in $\beta$, the cutoff $N$, the subgroup translate and any mask on these nonnegative atoms. At $X=R^2$ and $0<\varepsilon<1/52$ the exponent of $R$ is at most $41/52$. The exact finite partition keeps the complementary masked summand in the original ASK. The unramified first powers above $x+1$ still enter the signed estimate. [Masked tail and normalized comparison](../RHLean/Analysis/AlpogeThin/NativeDyadicHigherOddTail.lean) · [normalizing divisor](../RHLean/Analysis/AlpogeNativeCostNormalization.lean).

The selected pair also excludes all inert primes $p\le Y^{\varepsilon/5}$ on the literal native prime support. For $p^i\le Y^2$, this yields $i<10/\varepsilon$ independently of the window. [Actual inert-prime support](../RHLean/Analysis/AlpogeThin/NativeDyadicInertPrimeRange.lean).

For the same selected pair and $\exp(16)\le Y$, its lower bound on $\log d$ gives $d\ge Y^8\ge x^4$ throughout $1\le x\le Y^2$. The existing estimate for the **entire** ramified-$d$ contribution then gives
\[
\frac{\left\|\sum_{j,t}\operatorname{ASK}_d\right\|}{Q}
\le \frac{2(x+1)\log d}{\Delta(d-1)}
\le \frac{16}{\Delta x}\le16 x^{\varepsilon-1}.
\]
This keeps every $d$-power and the original divisor, uniformly in the cutoff and width data satisfying the native bounds. [Complete ramified estimate](../RHLean/Analysis/AlpogeThin/NativeDyadicRamifiedWindow.lean).

### Full exponent recovery on one integral edge

For $P=p^g$ the map from degree-$d$ monomials to $(\rho,\beta)$ is a bijection onto $\sum_i\rho_i+P\sum_i\beta_i=d$, $0\le\rho_i<P$. Both indices remain in the coefficient functional. With $n$ variables the full count is $\binom{n+d-1}{d}$. A fixed residue with $d=|\rho|+Pk$ retains exactly $\binom{n+k-1}{k}$ coarse monomials. At $n=4,d=8,P=3$, the 27 residue classes carry 165 distinct monomials. The native square-clock floor operation already gives this coordinatewise division on each full integer fibre. Applying it to exponent indices requires the choice of actual symbol and section. [Digit bijection, exact counts and factorial unit](../RHLean/Geometry/NativeThetaExponentDigits.lean) · [native floor fibres](../RHLean/Analysis/AlpogeSquareRootArithmeticMultiplicity.lean).

Write $v(n!)=v_p(n!)$. The recursion $v(n!)=\lfloor n/p\rfloor+v(\lfloor n/p\rfloor!)$ gives
\[
v((\rho+P\beta)!)=v(\rho!)+\beta v(P!)+v(\beta!).
\]
The ratio of these factorials has $p$-valuation zero. The remaining local approximation is quantitative: for every precision $c\ge1$, both this multivariate unit and its inverse require integral binomial expressions of total degree at most $4c$ valid on *all* coarse coordinates. Divided-derivative congruences carry their own coarse-order bound. [Exact upstream statements](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/Lemma5aAt.lean#L114-L137).

For a full exponent $\alpha$, use $H_{\alpha,z}(F)=[U^\alpha]F(z+U)$. For degree at most $|\alpha|$ this is $[X^\alpha]F$ at every center. On any finite family of distinct monomials the mixed-order matrix has determinant one. For the native product of leading minors with antitone row weights ending at zero and injective selected columns, the coefficient at the diagonal exponent, **with every row repeated to its prescribed weight**, is exactly one. Row homogeneity shows why evaluating at the unit mask sees this one coefficient. The other full-exponent jets now distinguish polynomials with identical mask values. These assertions concern the indicated symbol families. The integral span of a Cartan orbit can be smaller: every mixed coefficient of $(aX+bY)^p$ vanishes modulo $p$. [Integral jets](../RHLean/Geometry/NativeThetaIntegralJets.lean) · [leading coefficient and jet](../RHLean/Geometry/NativeThetaIntegralGrid.lean).

At a native Frobenius orbit of order $o$ modulo inertia, all the exponents $a+oj$ return to a single colour. Before forgetting the exponent, their Hasse rows form $\binom{a+oj}{k}$ with determinant $o^{m(m-1)/2}$ for $0\le j,k<m$. This determinant is a unit at odd places since $o$ is a power of two. Within the cyclic quotient the relation $(1+u)^o=1$ forces every nilpotent deformation $u$ to vanish when $o$ is a unit. A physical recovery proof must therefore carry the lifted section labels through the projection. [Native Frobenius progression and quotient](../RHLean/Geometry/NativeFrobeniusHasse.lean).

The source proof of `PrimStep` lifts a split family with its remaining Weyl basis, reduces the transported tensor identity modulo the uniformizer, and obtains independence for primitive combinations. The independent `TestStep` supplies a *single* dual satisfying the selected test, the height constraint and all incoming competitor conditions. The per-edge quota includes the flat count, the remaining Weyl count and the factor $1/p^{fr(n-r)}$. The number of available edges alone cannot certify the sum of independent local ranks. [Primitive step](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/DualFockLinear/Closed.lean#L532-L658) · [dual test](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/DualFockLinear/TestSideExplicitIdentification.lean#L153-L197) · [rank factors](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/ManyEdges.lean#L82-L112).

For a native DVR let $e_0=v_\pi(p)$. On integral candidate lifts $B$, it suffices to prove $E_{\rm actual}B-p^D I\in\pi^{e_0D+1}\operatorname{Mat}(\mathcal O)$ and $C_{\rm actual}B\in\pi^c\operatorname{Mat}(\mathcal O)$. Then $E_{\rm actual}B=p^D U$, $U\equiv I\bmod\pi$, and $BU^{-1}$ gives the exact joint decoder with the same competitor divisibility. Upstream uses $w^2=p$ and the stronger competing modulus $p^{D+1}$. On each incoming edge its adapted target basis $u_i$ and offsets $o_i\ge0$ require an integral row $G$ to satisfy $G(u_i)\in w^{\max(c_\star-o_i,0)}\mathcal O$ for competing-edge suppression. The native jet frame uses iterated invariant derivatives and the physical normalizer $1/(\beta\,[L:F]\,|Q|\,N^{\deg F})$. Even an integral formal group can mix derivative orders. For $F(X,Y)=X+Y+XY$, $D=(1+X)\partial_X$ gives $(D^2X)(0)=1$ and $[U^2](0+U)=0$. The physical row comparison may instead be a measured high-precision congruence on the proposed lifts, with the normalization, neighboring edges, and height costs included. [Upstream actual-versus-symbolic condition](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/ScaleZpowMono.lean#L24-L48) · [adapted basis](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/EdgeLatticeAdaptedBasis.lean#L166-L180) · [native physical jet](../RHLean/Geometry/NativeThetaJetEvaluation.lean).

On the prescribed host itself, an integral coordinate row on $(B^{-1})^{k+m-1}$ is exactly a vector in $B^{k+m-1}$. The finite native theta family also supplies an integral polynomial algebra. Substituting integral polynomial combinations of *actual Hermitian lattice directions* in a polynomial of this algebra gives a polynomial with integral coefficients. This proves integrality of its translated coefficient rows under the family's own Hermitian-integrality condition. The integral formal-group identity $F(X,0)=X$ recovers the original germ coefficients under pullback to the identity. Matching these functionals to all competing normalized edge tests still requires the adapted basis and loss bounds above. [Prescribed host dual and Hermitian coefficient rows](../RHLean/Geometry/NativeHostIntegralJetRows.lean) · [formal-group and polynomial coefficient recovery](../RHLean/Geometry/NativeThetaIntegralJets.lean) · [common congruent-frame decoder](../RHLean/Geometry/NativeJointEvaluationRecovery.lean).

### From recovery to the measured frame index

For the actual frame $F=\langle e_i\rangle\subset M$, choose a residue map on $M$ that kills each $e_i$. If its image contains a finite subgroup $T$, then $|T|\mid[M:F]$ by factoring through $M/F$. At comaximal moduli, the Chinese remainder theorem combines lifts in the same global module. Within a single prime power they must be simultaneous. The layer $(\mathfrak p^a/\mathfrak p^{a+b})^n$ has size $N(\mathfrak p)^{bn}$. The extra depth $b$ is the difference between the selected-coordinate frame-vanishing and recovery depths. Using the actual place bounds $B_v$ now gives
\[
 \frac{\operatorname{lcv}(X,M)}{D_{\rm amb}}\leq
 \frac{2}{[K:\mathbb Q]D_{\rm amb}}\log\!\frac{\prod_v B_v}{|T|}.
\]
Each $B_v$ measures that same frame. For $M=\mathbb Z[i]$, frame $e=n$ and unit archimedean metric, the Gram determinant and index both equal $n^2$. Scaling the vectors leaves their ratio equal to one. The geometric obligation is a measured upper bound on the Gram cost together with the actual residue map, degree comparison and ordered count and degree periods. [Relative index and normalized covolume](../RHLean/Geometry/NativeSummandCovolume.lean) · [ordered-period comparison](../RHLean/Geometry/NativeSquareCapacityPeriod.lean).

### Signed gain and window

The upstream prime inequality keeps the orbit deductions $d_l,\tau_p$, exceptional layers and both allowances $\mathrm{lo},m\,\mathrm{fl}$. The native physical ASK contains the retained term, low-central exclusions, shifts and ramified correction. Its finite slope consumer preserves the original $D_0.\mathrm{Ga}$. Prove both $\mathrm{umean}(\mathrm{ASK}-\mathrm{Ga})\le\mathrm{LoP}$ and $\mathrm{umean}(\mathrm{IO})\le\mathrm{LoP}$ for one choice of heights and weights on the actual subgroup. Upstream selection averages over full coordinate boxes and sums the defects over the primes before choosing a single profile. The square-clock size $m=R$, PageN and $|TT|\le|H|$ pay the scalar `NumMean.tot` budget $x^{-9}/4$ uniformly for $x\ge96^4$, $0<\varepsilon<1/52$. The per-orbit defect estimate and the identification with the common physical profile still require proof. [Square-clock scalar estimate](../RHLean/Analysis/AlpogeThin/NativeSquareDefectSelection.lean) [Prime and orbit estimates](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean#L90-L121) · [box selection](https://github.com/leanprover-community/riemann-hypothesis/blob/251c7b05dd869ceba1aa42c6001c00b4010f23f9/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/MeanNum.lean#L447-L517) · [native arithmetic](../RHLean/Analysis/AlpogeNativeLocalGainSource.lean) · [signed comparison](../RHLean/Analysis/AlpogeNativeSignedSlopeComparison.lean).

Fix one prime pair for the outer window beginning at $Y=A^2-1$ and ending at $Y^2$. For $A\le R\le A^{3/2}$ the interval $[R^2-1,R^2]$ lies inside it. The actual height box must also place $a_t/b$ near $x$ to pass from the signed mean to the anchor. Divide by the original $Q=|TT|\,m b\,|T_2|/(2|H|)$. The final target is one $C_\eta$ for every $\eta>0$ valid on arbitrarily late complete windows, with $\mathcal C_R-\mathcal D_R\le C_\eta R^{1+\eta}$ throughout each window. At an endpoint exponent $1/2+\varepsilon$, use the root exponent $1+2\varepsilon$ and $R^2\le2X_R$ for $R\ge2$. Existing interpolation and #1205 then give the RH implication. The physical recovery, relative capacity and both uniform signed losses remain open. [Window inclusion](../RHLean/Analysis/AlpogeThin/NativePrincipalEAtH.lean) · [mean-to-anchor comparison](../RHLean/Analysis/AlpogeThin/NativeScalarSupplierPayment.lean) · [complete-window implication](../RHLean/Analysis/AlpogeNativeWindowLandau.lean).
