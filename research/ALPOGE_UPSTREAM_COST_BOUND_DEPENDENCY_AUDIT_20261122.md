# Alpöge upstream audit: is the topExcess / Gz cost bound actually proved?

Date: 2026-11-22. **Status: source-text dependency audit (no upstream build). Not an RH proof, not a new equivalence.**

Upstream source audited: mirror `CocoSgt/riemann-hypothesis-lean` at commit
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4` (byte copy of the alpo.ge archive; Lean `v4.33.1`;
175,187 `.lean` files, about 17.4M lines). The mirror README said that, as of mirroring
(2026-11-20), no independent build or review had been published.

**Update (2026-11-22): RH is now independently verified.**

- The [Lean/Mathlib communities' joint statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
  (2026-11-21), endorsed by the Lean FRO and the Mathlib Initiative, certifies
  that both the statement (Mathlib's `RiemannHypothesis`) and the proof are
  correct.
- [A. Sutherland's verification files](https://math.mit.edu/~drew/grh/) report:
  - compilation of all modules;
  - only the three standard axioms;
  - kernel replay of every module;
  - acceptance by independent kernels;
  - statement matching.

  At the page's 2026-11-22 04:35 UTC update, the end-to-end `lake comparator`
  run and the Lean-kernel replay of the export were still in progress.

This settles that RH is proved. It does not change the dependency findings
below: they concern *which route* the proof takes. The Gz / `topExcess` route
named for translation leaves its cost bound as a hypothesis; the exported
theorem goes through `everyCharacter`.

Method: every claim below was read from declaration text. Whether a theorem is *proved*
means a `theorem`/`lemma` with that conclusion exists in the tree. Whether the
tree compiles, and what `#print axioms` reports, was **not** checked: a module-level import
closure is useless here (the terminal file's closure is 175,179 of 175,187 modules), and a
build of this size is impractical on GitHub-hosted runners.

## 1. PR #1182 (native ASK−MAIN → NNS map)

- The hosted build of PR head `649905a` compiled `RHLean.Analysis.AlpogeActualASKMainNNSMap`.
  CI failed only at the exact-graph cross-check: `source=9182, elaborated=9183` named proofs.
- Cause: `instance alpogeLiteralHostModulus_neZero : NeZero …` is Prop-valued, so Lean
  elaborates it as a theorem while the source inventory counted an instance.
- Fix (`452f024`, branch `claude/zen-ptolemy-a0ddsf`): the same declaration as `@[instance] theorem`.
  The statement, proof and instance registration are unchanged.
  `workflow_dispatch` run 44976272289: **audit ✓, Hosted Lean build ✓** (build, exact
  elaborated-graph validation, RHLean warnings gate).
- Follow-up commit adds `#print axioms` for the five exported map theorems, so their kernel
  axioms appear in the hosted build log.

## 2. Mapping of the requested seven steps to upstream declarations

| Step | Upstream object | Upstream status | RH_Lean status |
|---|---|---|---|
| 1 ASK−MAIN = De | `StronglyIrreducible.colour_balance : AskMainBalance` (`ChainSlopeWindows/StronglyIrreducible.lean:695`) | proved | native identity merged; NNS form in PR #1182 (CI green with fix) |
| 2 host identification | `LHost.hostData e q d := cftData q d (recMap e q d)` (`GaloisToProductIsIso.lean:69`); the five host specs are proved in `ChainSlopeWindows/GaloisMapComplexConjugation.lean:64–203` | proved (finite modular-unit facts) | the same host, transcribed component for component (§3); native counterparts of all five specs are already on main |
| 3 topExcess | `ThickSetMeanBounds.topExcess` (`GrowthBoundGivesRiemannHypothesis.lean:50`) | definition | `alpogeActualCanonicalTopExcess_eq_NNS`, `_le_iff_NNS` (PR #1182) |
| 4 cost bound | `GrowthInequalityDataExists`, `ChainCore`, `Chain2Core`, `Chain6Core`, `CoreAt` | **never proved: hypothesis only** (§4) | nothing to translate |
| 5 Gz bound | `proposition_at_point : GrowthBoundAtPoint`, `chain_at_alt : ChainAt`, `MergeGL2.chain6At` | proved, **conditional on the step-4 witness** | not ported |
| 6 power bound ⇒ RH | `ConditionalMainTheorem.riemann_hypothesis_of_power_bound` (`ChainSlopeWindows/RiemannHypothesisOfPowerBound.lean`) via `zetaLandauEps`, `riemannHypothesis_of_zero_free_halfPlane` | proved (classical Landau direction) | not ported |
| 7 audit | — | upstream never built | PR #1182 map verified as above |

## 3. Step 2: the literal host is already native

Upstream's analytic-route host is itself modular-unit data, with no number field involved:

- `hostN e q d = 2^(e+2) * q * d`
- `HA e = Additive ((ZMod (2^(e+2)))ˣ ⧸ zpowers (-1))` (`FrobeniusOrbits/Statement.lean:24`)
- `recMap` is `(sgn2 ∘ legU d, sgn2 ∘ legU q, hcl e ∘ unitsMap)`, with `hcl = QuotientGroup.mk`
- `cftData` is built from `localUnits` and `frobUnit`

`alpogeNativeHostN`, `AlpogeNativeDyadicH`, `alpogeNativeRecMap`, `alpogeNativeCftData` and
`alpogeNativeHostData` (`AlpogeNativeSharpASKBalance.lean:1428–1533`) match these component for
component: the same bit order (d, then q), the same dyadic quotient and the same CFT inertia and
Frobenius.

The upstream specs have native counterparts on main:

| Upstream spec | Native counterpart |
|---|---|
| `frobenius_unit_spec` | `alpogeNativeFrobUnit_spec` |
| `unramified_spec` | `alpogeNativeLocalUnits_unramified` and `alpogeNativeFrobUnit_modEq` |
| `dirichlet_character_spec` | `alpogeNativeDirChar_unit`, `_nonunit` |
| `inertia_conductor` | `alpogeNativeInertiaConductor_iff` |
| `primitive_value_ramified` | `alpogeNativePrimePower_conductor_split` |
| `PrimValPrimitive` | `alpogeNativePrimVal_eq_primitive` |

Cross-project definitional agreement is a transcription audit, not a kernel theorem.

The number-field Galois identification (the actual field, `tE : GG ≃ MM`, `frob_unram`) lives on
the separate `Br`/`D7` route (`SharpRestriction/GlobalSchurBounds/RamificationTwoAndConjugationAtQAndD.lean`)
and is not used by the topExcess route.

## 4. Step 4: the cost bound is never proved upstream

1. The five files named for this step contain **zero** `theorem`/`lemma` declarations.
   They hold 212 `def`s of statements and data:

   | File | `def`s |
   |---|---:|
   | `GrowthBoundGivesRiemannHypothesis.lean` | 29 |
   | `SChain.lean` | 33 |
   | `Chain2aCoreNoAnalytic.lean` | 81 |
   | `GrowthBracketBoundOfSizeWindows.lean` | 45 |
   | `FixedEpsilonConcreteGrowthBound.lean` | 24 |

2. Every proved theorem about these statements is a reduction, a general lemma, an identity or
   a sizes-only model. The proofs are in `PChain.lean`, `LipschitzWeightAndMinimum.lean` and
   `StronglyIrreducible.lean`:
   - `chain_top_bound : ChainTop`: `ChainInputs → ReducedGrowthInequalityDataExists`.
   - `chain_at_alt : ChainAt`: `ChainInputs → Gz` bound.
   - `chain_reduction_of_top : ChainCoreOfTop`: the top inequality is a hypothesis.
   - `exists_data_completion`.
   - `chain_sizes_model_eventually`, `chain_sizes_eventually`: size windows only, with no
     `ThinScales`, no `ValuesAtX` and no top inequality.
   - `proposition_size_bound`, `proposition_at_point`, `proposition_final`, `proposition_joint`,
     `proposition_final_minimum`: conditional.
   - `lipschitz_weight_all`, `derivative_integral_all`: general analytic lemmas.
   - `colour_balance`: the identity.
3. No declaration anywhere in the tree concludes a `ChainCore` / `Chain2Core` / `Chain6Core` /
   `CoreAt` / `GrowthInequalityDataExists` witness unconditionally. Every occurrence is a
   hypothesis or a core-to-core conversion (`Chain3Core→Chain2Core`, `Chain2aCore→ChainCore`, …).
4. The most-closed statement is
   `MergeGL2b.prime_gap_chain_mean_square` (`LocalToGlobal/GlobalTheory/AnalyticConclusionCompatibleMeanSquare.lean:131`):

   ```
   MeanSquareHypW ε 36 x₄ →
     ∀ large x, CoreAt (q1At ε x) (dAt ε x) … → Gz x ≤ x^(1/2 + (eD+eL+6)ε)
   ```

   `ZeroDensityBox` is proved there, and `PNTAPRelW` is proved (`JacobiCharacterSums/PNTFinal.lean:22`).
   **`CoreAt` remains a hypothesis.** `prime_gap_chain_mean_square`, `chain6AtPNT`,
   `analytic_conclusion_mean_square` and `analyticEndPNT` are referenced nowhere else in the tree.

**Exact unpaid hypothesis on this route.** It is the `CoreAt` witness at the selected primes
`(q1At ε x, dAt ε x)` for every large `x`, which `core_of_coreAt` maps to `LChain6.Chain6Core`
(`LossHyp` and `Inputs6d`). In the simpler `ChainCore` presentation, `chain_reduction_of_top`
reduces it to three inputs on the same host:

- the top inequality

  ```
  ∀ u0, ASK u0 ≤ Main u0 + cDiv·nT·a·La + cDiv·m·(B0+Nc)·x^(eDiv·ε) + LoP C
  ```

- `ThinScales D ell (exp x^(ε/3)) θ`
- `ValuesAtX D ell x ε CL`, i.e. `‖GPsi ψ x‖ ≤ x^(1/2+ε)` for `ψ ∈ {psC, chC, chpsC}`

`ErrWindows`, `BNBounds` and the size windows must hold as well. This repeats the frontier
recorded in `ALPOGE_BACKWARDS_DEEPEST_EQUIVALENCE_20261121.md` §6, now with the stronger finding
that **no upstream proof of it exists to translate**.

## 5. Where the exported theorem gets its cost content

The terminal chain:

```
Main.riemannHypothesis := rhOfAll
rhOfAll := Formalism.VW.rh_of_every allChi
allChi := UpperTheory.FinalTheorems.everyCharacter
everyCharacter := everyCharacter_of_row galoisLocalGlobalStrong_recParameter
                                          -- CharacterBoxes/MainConclusion.lean:10
everyCharacter_of_row h := every_character_of_literature_of_vWin ⟨h, recTExists, h⟩ (vwin_of_row h)
```

- `OpenLiteratureStatements` is a three-field `Prop` structure: `caraianiLocalGlobalDual`,
  `localLanglandsExists`, `galoisRepOfPolarizedPairLit`. It is filled in-repo, and dozens of
  "published" results (Bhatt–Scholze, base change, Bloch–Kato, …) are derived from it.
- `galoisLocalGlobalStrong_recParameter := galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK`
  (`Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean:6`).
- A generalized top-bound route over all primitive characters exists in `Development/`:
  - `UpperTheory.Top.zeroFreeAll_of_topG (h : TopG) …` (`CharacterBoxes/ZeroFreeAllOfTopG.lean:26`)
    has two consumers: `zero_free_all_of_green_v_win` (`ThirdPlaceSeries/TopPlug.lean`) and
    `plugWin` (`CharacterBoxes/EveryCharacter.lean`).
  - `TopG` is produced by `shape_closed_link_n_of_green : GLq.Green → TopShapeAlt … TopG`
    from a bundle of about 60 hypotheses (`HypsAlt`). Per-character hosts come from `VWin`.
  - Not traced: whether `every_character_of_literature_of_vWin`'s body (via
    `every_character_of_theta_integrals_local_matching`) reaches these consumers.
- `topExcess` occurs in exactly eight upstream files. In every one, a bound on it enters only as
  a hypothesis:
  - via `GrowthInequalityHypotheses`;
  - via `adm7` in `Br.proposition_eleven_two_at_scale`;
  - via `FamilyTopBoundAbsolute` in `Br.rh_of`.

  The only use in `Development/` is `ConductorsKronecker/CostPropositionBasicBound.lean`, and its
  `cost_proposition_at_scale` is conditional, consumed only by the `Br` route.
  `GrowthInequalityDataExists` occurs only in three statement files.
- Whatever cost content the exported theorem has therefore sits in the automorphic/geometric
  development:

  | Subtree | Files | Lines |
  |---|---:|---:|
  | `AbelianVarietyTheory` | 99,187 | 8,142,960 |
  | `WeilBound` | 7,051 | 848,547 |
  | `AutomorphicArithmetic/Foundations` | 4,413 | 419,572 |
  | `ThetaCorrespondence` | 3,201 | 178,983 |

## 6. Consequences

1. Steps 4–5 of the requested translation cannot be carried out as *translation*: on the named
   route the upstream code assumes the cost bound (the `CoreAt` / `ChainCore` witness) and never
   proves it.
2. Porting steps 5–6 alone would yield another theorem of the form "bound ⇒ RH", which the
   completion definition explicitly excludes.
3. Any RH-strength content that upstream supplies lies in the `everyCharacter` route (theta
   lifts, Galois representations, local Langlands, abelian varieties). Moving it into NNS
   coordinates would mean porting that development, not changing coordinates.
4. *(Superseded 2026-11-22; see the update at the top.)* This item originally said upstream
   was unverified. The headline theorems have since compiled, shown only the standard axioms,
   passed kernel replay with independent kernels, and been statement-matched to Mathlib's
   definitions, as reported by the community joint statement and Sutherland's verification
   files. Since the final statement is Mathlib's own, intermediate definitions such as
   `GalStar.Row0b` or `VWin` cannot make it vacuous. What remains open for RH_Lean is porting,
   not trust: either a toolchain-compatible import of the verified theorem (Lean v4.33.1
   versus RH_Lean's 4.34.1 pin), or a native re-derivation.
