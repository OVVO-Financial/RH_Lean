# Actual geometric suppliers — secure the geometric end of the string

**Scope:** stacked work branch of #1201, pinned starting head
`92f46c80a678df7f05f4741437068b51607b643c`. #1201 remains the intended
final proof PR; #1205 is the merged native consumer. This PR is not a
second RH claim, new conditional endpoint, or alternate research route.

## Verified baseline and first source changes

[Previous hosted preflight](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45393478344/job/138443224895)
compiled `NativeExistingRecoveryPayment` and failed later geometry.
The full build was skipped. Do not equate diagnostic compilation with
mandatory preflight success. At branch creation the newer exact-head
checks had not certified all geometry.

The initial source patch keeps all theorem statements unchanged. In
`NativeCMWeierstrassSectionJet`, replace the three deprecated dependent-if
rewrites with their existing replacement used in that same proof.
In `NativeCMWeierstrassMorphismTangent`, explicitly transport section
evaluation equality through the dual-number second coordinate instead
of rewriting under the dependent section evaluator; normalize the
chain-rule derivative's `beta * 1` in both same-model and cross-model
proofs. The two native source hashes are refreshed. These are submitted
proof repairs, not yet compiled, and not a discharge of reverse
integrality or any signed-slope premise.

## Critical path — apply existing supplying proofs

| Gate | Existing source/consumer | Required actual discharge |
| --- | --- | --- |
| G1 | `exists_inverseIdeal_reverse_scheme_isogeny` in NativeCMInverseIdealClassModels; `shortModelSchemeIso` in NativeCMWeierstrassTranslationGroup | Construct the same reverse ideal-class hom on the original equations, conjugating the actual rational short-model map. Preserve the field, period inclusion, nonzero multiplier and complex-point action; no witness chosen to match a target formula. |
| G2 | `existsUnique_elliptic_hom_extension_dvr` and `exists_elliptic_extension_integral_coordinate` in NativeCMWeierstrassIntegralExtension | Apply to G1 at every relevant finite localization, identifying the generic fibre. Use the existing relative normalization / finite graph argument. Obtain genuine integral derivative coordinates and global integrality by the existing arithmetic descent; prove compatibility under every embedding, not only the distinguished embedding. |
| G3 | `exists_tangent_scalar_between` in NativeCMWeierstrassMorphismTangent; `mean_log_covolume_sub_log_pi_ge_class_period` in NativeCMIntegralClassPeriodMean | Identify the coordinate of the actual dual-number map with the original analytic multiplier times the source/target change-of-coordinate ratio. Supply the actual two lattice inclusions, common field, class permutation and unit discriminants. One-sided period mean suffices: do not require forward derivative integrality merely to obtain equality. |
| G4 | `nativeDIV_of_period_lower` in NativeExistingRecoveryPayment | Apply G3 and the independently earned degree inequality to the physical `Data` on the same selected family. Obtain DIV with zero extra period debt. The period lower bound alone does not prove DIV. |
| G5 | NativeCMSerreSchemeMetric, NativeCMSerreBundlePairing, NativeCMAllPlaceEigenlineDegree, NativeThetaCuspSchemeTorsion, NativeThetaCuspComponentSections, NativeMeasuredComponentDegree, NativeMeasuredComponentNorm | Use the existing pinned construction to realize the actual signed polarized Serre family, cusp sections/span, Petersson component Gram/mass and rank/degree lower shares. Retain original projective trace-polarized module, index, signed metric, finite-level coefficient geometry and all embeddings. A finite Haar norm is not the required measured Petersson mass. |
| G6 | `nativeConstructedDyadicSignedSlopePayment_of_meanLoss` and its `physicalData` consumer | Pay every surviving measured, slope and recovery input on ONE actual family: HidaSetting, DIV, EComp5, HComp, Count5, Slopes, QuotientSlopeBoundsWith, Losses, SlopeIneq, HHBound, FParams, ErrWindows, LargeX, B0/Nc and size windows. Use original gain_bound_all_of_star / AuxBlock8.Pf.stmtF and exact native Phi transport where relevant. No new cancellation or reduced-rank experiment. |
| G7 | pinned `level_gm_le_on_family_scales` / `core_gm`; `nativeSmallEpsilonWindowBound_of_principalCyclic` | Supply genuine principal FamilyClassConnected/ChainTied, EFamC and complete HasWindows with fixed eD,eL,eps1 and correct quantifier order. Return the already proved growth estimate on the actual principal cyclic family to #1201, where the native identity and #1205 handoff finish the implication. |

G1–G4 are the immediate serial period priority. G5 and local recovery
work can proceed in parallel on the same original family. G6–G7 are
integration gates, not additional independent estimates. If the original
pinned principal-window supplier is shorter, apply it directly with
proved object identifications; do not make all seven rows independent
mandatory reconstructions. The 43 conditions are coverage, not a count.

## Exact source references

- [Pinned reverse-isogeny period construction](https://github.com/CocoSgt/riemann-hypothesis-lean/tree/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory).
  Follow the actual proofs in `ExistsCmCurvesOfWeierstrassCurves.lean`,
  `MulLeftCompOfPullbackPointEquivMul.lean`,
  `ExistsUniqueHomExtensionSemiAbelianDvr.lean` and
  `IdealValDifferentEqOne.lean`; inspect their prerequisites.
- [Pinned tied-family quantitative application](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean).
- [Pinned core supplying proof](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean).
- [Existing 43-condition and principal cyclic audit](ALPOGE_SCALAR_CONDITION_AUDIT_20261124.md), sections 12–14.
- [Existing native bound handoff #1205](https://github.com/OVVO-Financial/RH_Lean/pull/1205).

## Hosted preflight order

Repair the actual reached graph-kernel overlapping-instance warning,
section-jet warnings, CMOpen/rational map, tangent and translation group
sites. Then resolve theta atlas, shifted vacua, Serre polarization and
dependent downstream failures on the same exact head. The old log
identifies these as failures, not necessarily the exhaustive latest list.
Do not weaken statements or disable warnings; do not rerun unrelated
cold builds to hide the first failure. Retain existing mandatory fail-fast
preflight, full native build, exact source/declaration graph, source
hashes and guarded terminal-axiom audit. Run Lean only in hosted CI.

## Acceptance and ownership

All seven roles use the existing ownership and reporting rules, with
G1–G4 as the priority; coordinate a single source-compatible family.
Each submission records the precise unpaid typed premise, upstream
proved declaration and native application, the changed declarations,
and exact-head hosted status. A passing intermediate file is not
unconditional closure. Reject True geometry, copied analytic lattices
as geometric witnesses, assigned height identities, circular premises,
extra axioms, sorry, terminal RH imports and any dropped signed source,
prime power or embedding.

Merge this stacked supplier branch into #1201 only by human review after
actual supplier verification. No direct merge into main. No claim of RH
until #1201 independently supplies the complete uniform critical estimate
and the closed Mathlib RiemannHypothesis theorem. No agent launch or
schedule changes are implied by this repository update.
