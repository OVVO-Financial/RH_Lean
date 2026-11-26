# Actual geometric suppliers — secure the geometric end of the string

## Consolidated into #1201; #1208 closed as superseded (2026-11-24)

By user direction (one PR, one proof frontier, one verification cycle),
this document now governs #1201 directly. Its G1–G7 gate table below is
the single critical-path map; there is no separate supplier branch.
The text after this section is #1208's original record, kept unchanged
for provenance, including its hosted-attempt history.

Consolidation audit of #1208 head `86f351997392b8d1832923b7272bb403a6eb56c9`
against #1201 head `496398bb29800810b32556a97f440eb76b8db508`:

- **Adopted:** the `KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one`
  helper without the unused `IsDiscreteValuationRing` binder and without
  the local `linter.overlappingInstances` exception. Its proof only uses
  the domain/fraction-field injection `fractionField_map_injective`;
  dropping a hypothesis strengthens the statement, and the DVR wrapper
  `graph_kernel_no_torsion` is unchanged.
- **Adopted:** this G1–G7 gate map and its hosted-attempt record.
- **Discarded:** #1208's `.github/workflows/lean.yml` at `86f3519`. The
  conflict resolution pasted a second copy of the workflow inside a grep
  pattern; the file is invalid YAML, so the Lean workflow never ran on
  #1208's final head. #1201 does not need the intended target-selection
  change: its research audit roots differ from main, so the changed
  research closure is always selected.
- **Discarded:** #1208's AGENTS.md section requiring a PR stacked on
  #1201 (superseded by SINGLE_PR_SINGLE_FRONTIER_V1).
- **Decided by #1201's exact-head evidence** ([run 45418252140](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45418252140)
  on `496398b`): #1208's alternative proof bodies prove the same
  statements as #1201's. #1201's `mixedSerreExponential_coefficient` /
  `exists_prescribedMixedSerreExponential` bodies compiled
  (NativeCMSerreMixedPeriods built), so they are kept. #1201's
  `rigidified_originLinComb` body failed (unsolved diagonal-unit goal,
  coercion mismatch and two unused simp arguments), so #1208's body —
  `LB.isLB_linComb`/`LB.isLB_pull`, `LB.res_g_self` and `resG_self` on the
  same chart — is adopted. It still awaits its own hosted compile.

The status is unchanged: these are Lean repairs and bookkeeping, not
discharge of any G1–G7 premise. The native critical estimate and RH
remain OPEN.

---

**Scope (original #1208 text):** stacked work branch of #1201, pinned starting head
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

## First #1208 hosted failure — graph-kernel linter

At `b8e18c7`, [Lean source audit run 45398505544](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45398505544) passed the static audit but [Hosted Lean build](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45398505544/job/138460873597) stopped on the overlapping-instance warning in `KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one` (line 75); the changed research closure was skipped and cancellation succeeded. The helper already receives etaleness explicitly. Its only base-ring-specific step is `fractionField_map_injective`, which uses a domain and its fraction field. Remove the redundant DVR instance from the helper, retaining its original proof and all torsion, flatness/etaleness and generic-isomorphism premises. The actual DVR wrapper `graph_kernel_no_torsion` is unchanged, as are all warning-fatal checks and guarded roots. Refresh the exact source hash. This is a proposed repair of the first reached blocker, not certification of downstream geometry.

## Reconcile #1208 with the five later #1201 commits

The #1208 head `94d90467b4395177223873c685a4003b0c90b7e3` was two commits ahead of the common ancestor `92f46c80a678df7f05f4741437068b51607b643c`; #1201 advanced five commits to `6937f9a6cbde4f3345bde720e8aa4c51b997a50e`. [Hosted failure 138475431298](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45402689873/job/138475431298) explicitly built NativeCMWeierstrassGraphKernelTorsion, then stopped on two type mismatches in NativeCMSerrePolarization (old lines 178, 180). Static audit passed; research closure was skipped. No full Lean success is claimed.

Resolve using the complete later #1201 tree and both parents. Keep both AGENTS directives, the #1208 supplier report, and the actually compiled #1208 graph helper (no local linter suppression). The two branches' SectionJet blobs are identical; the later #1201 MorphismTangent proof includes the same explicit evaluation transport and chain-rule normalization plus more precise composition, chart and preimage proofs, so retain it byte for byte. Keep the later #1201 SerrePolarization repair (explicit integral unit-multiplier goals rather than broad simplification), theta atlas, translation, open-point, tensor vacua, VerifyTask integrations and other base changes unchanged. Use the later source manifest and replace only the graph-helper entry with the already verified #1208 source hash. The proof statements, actual mathematical witnesses, audit roots and fail-fast workflow remain intact. The Serre and downstream repairs still require exact-head hosted validation.

## Mixed Serre period elaboration — 2026-11-24

[Hosted build 138497887906](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45409054729/job/138497887906) on reconciled head `1c066c4` passed the static audit and advanced past the preceding Serre polarization errors. The reached frontier is NativeCMSerreMixedPeriods: tensor scalar action (111), unused simp argument (112), unnecessary simpa (217), product second-projection scalar action (412), and dependent rewriting of the mixed dimension (431). Repair the tensor action by explicit linear-map tensor evaluation, use the explicit second-coordinate action, remove both lint causes, and transport the existing mixed exponential through a dimension-parametrized proposition so that the original period lattice, type function and coordinate module move together. The theorem statements, both orientations, kernel, surjectivity and full coefficient action are unchanged. Refresh the exact manifest entry: the original Git blob 6202b87 already had SHA-256 ee5638a8527388cc3d217254ea6c4326f91984c00d2944fe8223a10035311e58, differing from the previous manifest. These are source repairs awaiting hosted validation, not certification of the full geometry.

## Origin rigidification of the represented Serre scheme — 2026-11-24

[Hosted build 138505007360](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45411063916/job/138505007360) on `afddcd8` advanced past the previous mixed-period errors; the reached errors are all in NativeCMSerreSchemeBundle, lines 67, 74 and 97. The existing germ argument proves that any pair of charts meeting at the identity has the same literal all-origin index. Instead of unfolding and expanding both dependent signed products in their stalks, apply the already proved `LB.isLB_linComb` and `LB.isLB_pull` and then the diagonal transition identity `g_self` on that common chart. Qualify `_root_.one_mul` to distinguish it from the monoid-object law. Keep the group morphisms, signed exponents, chart-membership argument, and rigidification statement exactly as before. Refresh the verified source hash. No assertion of a full successful hosted build or geometric closure.

## Reflexive chart restriction — 2026-11-24

[Hosted build 138511693284](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45412938230/job/138511693284) on `ee8794a` reduced the previous three errors to one type mismatch at line 100: `IsLB.g_self` gives the restriction of the diagonal transition, not its unrestricted value on the self-intersection. Use the existing `LB.res_g_self` with the reflexive restriction on that self-intersection, pass to underlying sections via `Units.val`, and cancel the identity restriction with the already proved `resG_self` from NativeCMLineBundleAtlas. The chart membership proof and rigidification statement are unchanged. Refresh the exact manifest entry. Full hosted verification remains required.

## Bundle Gram frontier and synchronized parent — 2026-11-24

[Hosted build 138518651367](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45414912711/job/138518651367) on `8550997` advanced beyond Serre scheme rigidification. Its only reached diagnostics are NativeCMSerreBundleGram lines 137 and 163: pointwise evaluation of the coefficient module action, and matching the four-term Gram sum under a let-bound frame. The parent #1201 has since advanced two commits from `6937f9a6cbde4f3345bde720e8aa4c51b997a50e` to `714f5b0ffe3ec43296409cab7202a48783aaa7cd`. Its new Gram proof explicitly resolves the integral tensor, specializes the evaluation at each root automorphism, and instantiates the Hermitian matrix and four-pullback identity before expanding sums. Both reported errors have targeted repairs there, awaiting hosted validation. Use that complete parent tree, retaining the already advanced child versions of MixedPeriods, SchemeBundle and GraphKernelTorsion (same theorem statements and actual source objects, alternative proof bodies only), both agent directives and the complete supplier report. Reconcile the exact source manifest entries for those three retained child blobs against the newer parent manifest; retain all other parent changes and its hosted-attempt history. No changes to #1201 itself, no theorem weakening, no linter bypass and no claim of unconditional closure.

## Repeated mixed-period diagnostic and one-pass guarded preflight — 2026-11-24

[Hosted build 138529811810](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45418030156/job/138529811810) at `e8fd39e` reports an outstanding pure-tensor coercion equality at line 111 of NativeCMSerreMixedPeriods. A later error in a parallel build did not certify all previous modules; correct the prior status accordingly. Adopt the parent's explicit three-step scalar transport: the tensor scalar lemma, reflexivity for the actual tensor-map application, and the tensor scalar lemma on the conjugate factor. Keep the existing other mixed-period proof bodies, original statements, and all signed data. Preserve the prior scheme rigidification and graph-kernel fixes. The new parent `496398bb29800810b32556a97f440eb76b8db508` incorporates the full semantic proof-risk audit; retain its complete tree and merge its AGENTS directives with the child-specific prefix. Since geometry-only changes previously skipped the changed-research preflight, select the existing CM seed/Serre/mass audit root for changed NativeCM/NativeTheta geometry sources when that root exists. This reuses the existing warning-fatal preflight and bounded diagnostic-only pass without weakening any check or introducing a new theorem or new workflow. The mandatory full native build remains gated on successful preflight. Do not infer any compiled supplier status from which parallel error appears first. The parent and child both remain subject to exact hosted verification; no RH closure asserted.
