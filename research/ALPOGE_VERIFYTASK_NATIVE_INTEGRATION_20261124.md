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
