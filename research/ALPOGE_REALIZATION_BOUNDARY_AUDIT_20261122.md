# Geometric realization and signed-observable boundary audit

**Date:** 2026-11-22. **Native base:** `291e21aa788aaa2af9238b835dbd24a76d1b3717`.
**Pinned upstream:** `CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

This is a read-only audit of the named geometry marker, analytic seed, and nearby hypotheses. It does not validate the whole upstream dependency graph or establish that the upstream theorem is invalid. No Lean/Lake command was run. The [source/hash ledger](data/alpoge_realization_boundary_audit_20261122.json) records exact source/native paths, SHA-256 hashes, declaration locations, and the scope of each finding.

## Finding

The user's local observations are correct: `anyGeometry` is the constant proposition `True`; the seed copies analytic row data; `MjAre` and `LamAre` for that copy use definitional equalities; and the subsequent weak geometric graft can use zero maps into a degenerate model. These facts mean that **the seed/graft path alone does not construct a faithful geometric realization with an independently identified metric**. They do not show that the rest of the proof is reflexive. The seed already requires substantive analytic and lattice data, and other source contracts separately require genuine evaluation, norm, and height comparisons.

The source explicitly distinguishes the weak interface from a stronger realization interface. `LargeFor.lean` defines `FamOver.Reads` with joint injectivity, full span, integral-lattice comparison, an exact norm identity, and equality to actual cusp-form comparison maps. `IsGeoOf` requires that interface for the same core and resulting record; `geoOf` additionally asks for actual surface data. **Those properties are not supplied by `anyGeometry`, `GeoCl`, `MjAre`, `LamAre`, or the flat graft.** Whether every stronger property needed by the terminal proof is independently supplied requires following its actual consumers and cannot be decided from the seed alone. [S01–S09]

## 1. What the marker and parameter constructors say

In `OverIx.lean`, `GeoP` is a predicate on a `D7`, a core, and a divisor record. `anyGeometry` ignores all three inputs and returns `True`. By contrast, `geoOf Q` requires a positive integer `c`, `IsGeoOf (Q D) J c X`, and `HasTrueSurf X`. These are distinct predicates. [S01]

`NotGeoClFalse.lean` defines `GeoCl` inductively. Its base constructor accepts the original predicate; its step transports to `setDiv D N h` for arbitrary `N` and `h`, along with the copied core and transformed divisor record. Thus `geoCl anyGeometry` imposes no additional realization condition on already existing data. It does not itself construct a `D7`, core, analytic row family, or measured-height inequality. [S02]

`ThetaChr.prmR N S Γ` merely packages `RX`, `N`, `S`, and `Γ` into `Prm`. The underlying `hL : Published.LocalLanglandsGL`, `N : NExt hL`, and `S : SExt` remain parameters. `SExt.none` is a trivial extra slot; it does not trivialize all slots. `BuiltE`, `GoodE`, `MemberE`, and `RecPinE` retain their distinct construction, compatibility, kernel, and row-data conditions. [S03]

## 2. Exact seed and graft behavior

`TupPinsOfMuIsW.x0` is parameterized by the existing `D7`, finite group and family, number field and embedding, `RealDat3`, `Face3`, base row side, and an existing `Read`. Its explicit inputs are `Z : ReadL R F X0 Y`, `Pins R F cG`, and `Holds R F`. It installs the empty geometric example, empty levels/components/surfaces, `MjH := mjH Z`, `jM := jM Z`, and `logLam := logLamOf Z hH`. [S04]

The final two identity proofs have the claimed form:

- `mjAre_x0` uses `exists_mjHTie` with equality of `MjH` and heterogeneous equality of `jM`, both reflexive for the copy.
- `lamAre_x0` applies `lamAre_of_eq` to the reflexive equality of `logLam` with `logLamOf`.

These are bookkeeping identities for copied data. However, `x0`'s other row fields are not all proved by reflexivity: `MjH_good`, `jM_basis`, `jM_lat`, `MjLat_sub`, and `jM_metric` call existing lemmas with `Holds` and/or `Pins`. In particular, `MapSeqIndAll.jM_metric` identifies the copied Hermitian-coordinate norm with the analytic norm of `jM`, using `jW_norm`. This is a real norm assertion about the analytic data already assumed; it is not a proof that geometric section maps `iMj` faithfully realize that norm. [S04, S05]

`exists_divT` takes an actual `ColPin w` and `Lv4 𝒮 K w Z`. It first makes `x0`, installs actual local character data by `ReQ.reQ`, and then uses `geoOver_stages`. The latter takes an existing `Stages` and divisor record and supplies the weak `GeoOver (fun _ => True)` interface through `divXFl`. `divXFl` uses `geoDegenerate`, unit levels, zero geometric degrees, and `iMj = 0`, while retaining the copied analytic entries. `GeoGraft.graft` likewise preserves `MjH`, `jM`, `jM_metric`, `logLam`, and character data; its new `iM` need only land in the declared section subspace. [S04, S06, S07]

The predicate actually satisfied here, `GeoTiedP`, asks for a compatible family, ties of its fields, complex embeddings, cusp-boundary membership, isometry invariance, and level compatibility. Its definition contains no joint-injectivity or norm-identification clause for `iMj`. Consequently, its flat witness cannot be used as evidence for those stronger properties. `divEx_prov` fills the optional `anyGeometry` field by `trivial`. The three literature propositions appearing as arguments of `divEx_of_ox` are unused by that particular proof, which delegates to `divEx_prov`. [S04, S08]

## 3. The stronger independent realization contract

The source's stronger contract is explicit. For every relevant row, `FamOver.Reads X0 iM` requires all of the following on the same family and maps: [S09]

1. If every component of `iM x` vanishes, then `x = 0`.
2. A cusp-form submodule and a semilinear map `φ` with the prescribed weight, full complex span, and containment of the actual integral row lattice in its image.
3. An equivalence between membership in the source cusp lattice and membership in the actual row lattice.
4. An exact norm formula `‖φ x‖ = sqrt (vol * dimKap D j) * l2NormAlt (...) x` for each row, one `vol` independent of `x`.
5. Equality of each `iM` component with the actual cusp-form comparison map whenever `jM x = φ f`.

`IsGeoOf Q J c X` also requires an actual `Top`, its `LawsP`, a `FamOver` with its kit/form/provisional-family ties, the identity of that top's core with `J`, equality of `X` with the resulting geometric record, and the specified different exponent. These are considerably stronger than the flat interface. This identifies the exact independent attachment **not furnished by the named seed/graft constructors**. This audit does not infer that `IsGeoOf` itself is a mandatory premise of every later route, nor that no other theorem supplies the required attachment.

## 4. Existing analytic and global obligations survive the seed

`RowsT` still contains `r : RowsAre`, `exAt`, `inGeo`, group/character identifications, exact local-place support, two exact inner-product identities, row integrality, and index identities. `RowsAre` supplies the `Holds` used above. Its `inGeo` field is `RealGeo.InGeo`, whose seven fields are evaluation existence at good embeddings, conjugate evaluation existence, evaluation injectivity, independent/full-span uniformization, compatible geometric action, fullness of the cusp lattice, and a dimension comparison. The actual definitions of `EvInj`, `JUnif`, `GeoAct`, and `LatFull` are substantive. [S10–S13]

`Read` and `ReadL` also retain their actual linear equivalences, operator identities, lattice ties, and metric comparisons. For example, `ReadL.met` and `met0` identify the Hermitian forms at nondistinguished places; `jW_read` identifies the row map with the existing analytic form map. These premises do not follow from `anyGeometry`. [S14]

Nor is `Hyps` a trivial predicate. It is a large record of selected-family existence, row, divisor, period, count, mass, and compatibility assertions. The particular constructor `nonempty_hyps_of_classicalTheoremsUE` requires **all** of these top-level inputs: [S15, S16]

- `S0.HypothesesUE` and `S0.RowRat`;
- `hL : Published.LocalLanglandsGL`, `cDep : ℝ`, `A : GroupRetwisting.AtP`, and `EvLgG A`;
- the stated `RL.At (prm1 hL cDep)` bound-at-two-and-three condition;
- the stated `RL.At (prmR (...) SExt.none (geoCl anyGeometry)) S0.FunctorialityCondition`;
- the stated `RL.At` on that same parameter package for `S0.CovolumeBound'`.

The proof invokes constructions and comparison theorems using those inputs. Inspecting their transitive suppliers is separate work. No conclusion that genuine analytic RH follows from the displayed `rfl` proofs is justified by this bounded audit.

## 5. Native check and exact remaining boundary

A literal scan of the native Alpoge additions and geometry modules of 242 files found no `anyGeometry`, `GeoCl`, `MjAre`, `LamAre`, `prmR`, `setDiv`, or `hExpl6`. Absence of those names is only a scan result, not a proof of complete native realization.

The relevant native scalar attachment, `AlpogeNativeSignedSlope.physicalData`, copies only the visible arithmetic entries from the actual source: Euler's constant, the principal logarithmic derivative, heights, widths through the actual finite CM-type equivalence, and the full prime-power kernel sum. It deliberately leaves the finite-place gain `Ga` and geometric slope data unchanged. `physicalData_Ga` is reflexive because it certifies that preservation; the MAIN identity is proved by finite reindexing and the literal source formula. [N01]

Its inequality theorem still requires the eleven original finite inputs on that same data: `HidaSetting`, `DIV`, `EComp5`, `HComp`, `Count5`, `Slopes`, `QuotientSlopeBoundsWith`, `LossBounds`, `SlopeIneq`, `HHBound`, and `FParams`. The strong-window and normalized versions additionally retain their explicit size/window and auxiliary-budget assumptions. In particular, `LossBounds` is not made true by selecting a replacement `Ga`, and no assumed `physicalTopExcess` conclusion is introduced. The constructed Gz consumer preserves these inputs and the same selected host. [N01, N02]

The native field, inverse-different lattice, full polarization Datum, and frozen period construction establish concrete prerequisites; none is being counted as a completed construction of the actual moduli/section/metric suppliers for those eleven inputs. The remaining audit obligation is to trace the independent measured-map bounds and their same-data transports into the finite consumer. The separate `setDiv`/`WordFacts`/`DivClausesR` audit must be kept with this one: a freely assigned height label is neither the measured height nor, by itself, proof of the measured-height bound.

That distinction also needs a nonvacuity check. `HLatTie` can be reflexive for `HLat.ofCoord L X`. `DivClausesR` permits the zero map, and `divClausesR_of` explicitly handles that case with a positive upper-bound family having the prescribed logarithmic mean. Their mere existence is not evidence of a nonzero or injective geometric realization. Conversely, `RecBridge.WordFacts` explicitly requires the actual measured-height bound when `Bk ≠ 0`; `wordFacts_of_clauses` separately takes the actual-map identity `hBk`, the measured-height equality `tHt`, and the budget-label equality `tH`. The relevant force lies in these same-data transports together with the actual consumer's nondegeneracy, rank, and size requirements, not in the record names alone. [S17–S19]


## 6. The declared height and the measured map height are distinct

The third local observation is also confirmed. `GlobalTheory.EX.OB.setDiv`
updates the integral submodule in each `Nu u`, assigns the scalar field
`div.h := h`, and updates `HH` using the resulting `sFrame`. In
`LedPart`, `ht := DV.hExpl6 D p.L Y.X C.Csz`; `pt` calls `setDiv` with
that function, and its `nprimeDef` and `h_eq` fields are reflexive. This is
a declared height budget on the changed record. [S20–S22]

`DivData.h` is a freely specified real-valued field of the divisor record.
It is not the definition of the measured height `Formalism.HN.htMap` of
its pairing map and Hermitian structures. The later `WordFacts` predicate
separately requires

\[
 B_k\ne0\quad\Longrightarrow\quad
 \operatorname{htMap}(B_k;\mathrm{Nu},\mathrm{RR}^{\vee})
 \le \mathrm{div.h}(u),
\]

together with actual integral-image containment and the scalar comparison
to `MAIN` plus the full error. Assigning `div.h := hExpl6` proves neither
that measured-height inequality nor the scalar comparison. [S19, S21]

The source makes the distinction explicit in `wordFacts_of_clauses`:
`hBk` identifies the actual bilinear maps; `tHt` identifies their measured
heights; `tH` identifies the declared budget with the recurrence expression.
`htMap_le_of_bound` uses a positive bound `cu v` for the square of the actual
operator norm at **each** infinite place, its specified average logarithm,
and positivity of the actual norm. It applies monotonicity of the logarithm
to derive the measured-height inequality. That is a substantive estimate
when attached to the intended nonzero map. [S19]

The wrapper `wordFacts_of_face` does not leave `tHt` as an unexplained
identification: it derives good coordinate frames from `HLatTie.metric`,
uses `RBTie.htMap_tie` with the same pairings and metrics, and derives the
dual-slope transport with `RBTie.muDual_tie`. Its hypotheses still include
the actual lattice/metric ties, pairing identity, `DivClausesR`, shifted
lattice identity, and scalar budget comparisons. The remaining work in a
native application is to construct those inputs on the selected data.
The fact that an identity copy or zero-map example can satisfy some of
these interfaces is why the actual consumer's nondegeneracy and rank
conditions must be checked as well. [S17–S19]

## 7. What can be concluded about the terminal statement

The pinned source contains `riemannHypothesis : RiemannHypothesis := rhOfAll`.
It also exposes `riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := rhOfAll`,
where `Statements.lean` explicitly defines the latter proposition using
zeros of `riemannZeta`, exclusion of the negative even integers and the
pole, and the conclusion `s.re = 1/2`. `UpperTheory.EveryCharacter` is
explicit nonvanishing of the actual Dirichlet L-functions in the right
half-plane. These displayed statements are not propositions of the form
`P = P`. [S23–S26]

`MainTheorems.rhOfAll` applies `Formalism.VW.rh_of_every` to `allChi`;
the latter comes from `UpperTheory.FinalTheorems.everyCharacter`.
`rh_of_every` specializes to the modulus-one character and uses the
L-function/zeta identity. The supplying final theorem uses the separate
row and local-to-global machinery. This bounded inspection does not
verify that machinery's full transitive axiom closure or every supplied
analytic hypothesis. [S26–S28]

Accordingly, the three definitional identifications establish a serious
**realization-audit requirement**. They do not establish the stronger
claim that Lean has certified only “RH = RH” in place of the displayed
analytic proposition. Reflexivity proves a definitional equality; it
does not prove an unrelated nonvanishing or zero-location statement.
Determining whether the complete upstream argument supplies every
necessary hypothesis requires the full exact-source dependency and
semantic audit. No verdict of global invalidity or global validity is
made here, and no upstream terminal theorem is imported into RH_Lean.

## 8. Consequences for the current native construction

The native construction preserves the source's complete `Datum` and
`IsPeriod` contracts. Its period map acts on the already-constructed
inverse-half-different lattice. Injectivity, discrete image, full real
span, exact coefficient-type multiplicities, and a positive Hermitian
form with the prescribed imaginary part are proved from that lattice
and its real-coordinate equivalence. They are not filled by `True` or
by a weak geometric graft. These are finite geometric prerequisites;
they do not yet supply the abelian-scheme moduli, section maps, or the
metric/observable comparison. Hosted verification of these new modules
remains pending at this audit checkpoint. [N03–N06]

The companion arithmetic construction defines its ray group from actual
nonzero ideals prime to the same nonzero modulus. It proves the class/residue
injection and the bound `#G ≤ classNumber(K) * M^[K:Q]`. `aRay` is the
finite cardinality of the actual ideal-norm fibers; `lamRay` sums the
ideal prime-power logarithms. The convolution is proved by an actual
divisor/product bijection. No target analytic coefficient, count
estimate, or theta estimate is assigned to these definitions. [N07–N08]

For the final attachment, the original signed observable is fixed first.
A proposed change `T` to the section maps must retain integral image,
joint injectivity, the actual ranks and short generators, and all-place
forward bounds. It must also preserve or independently reprove the
comparison with that original observable. For the lower unilateral shift
on `N` coordinates, `J = I-S` has determinant one; nevertheless, for
`N ≥ 1`, `1 ≤ j ≤ N` and `k ≥ 1`,

\[
 ((J^{-k})^{\mathsf T}\mathbf1)_j
 =\binom{N-j+k}{k}.
\]

This follows by summing the entries
`binom(k+r-1,r)` of the finite nilpotent inverse power. The displayed
formula also holds at `k=0`, where the inverse power is the identity.
At `k=1`, the
weight is `(N,N-1,...,1)` and `J` sends the all-ones vector to the first
basis vector. Thus a paid forward height and unchanged determinant do
not pay the recovery weight. The native reserve theorem is not being
used to claim otherwise.

The practical acceptance boundary is therefore the complete same-data
proof: actual maps and nondegeneracy, actual integral lattices and
all-place metrics, their measured-height bounds, and the eleven original
signed-comparison inputs including `LossBounds`, strong `ErrWindows` and
the auxiliary size bounds. A reflexive equality is legitimate for a
proved coordinate identification or preservation statement. It is not
evidence that an independent geometric bound has been constructed.
The current conditional comparison leaves this distinction explicit.
Its remaining compatible suppliers, uniform quantifiers, and final
native analytic consumer are not declared complete. [N01–N08]

## Source locator key

All source paths below are relative to the [pinned upstream root](https://github.com/CocoSgt/riemann-hypothesis-lean/tree/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4). Full SHA-256 hashes and declaration locations are in the accompanying source/hash ledger.

| ID | Source path |
|---|---|
| S01 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/OverIx.lean` |
| S02 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NotGeoClFalse.lean` |
| S03 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/ThetaChr.lean` |
| S04 | `src/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TupPinsOfMuIsW.lean` |
| S05 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/MapSeqIndAll.lean` |
| S06 | `src/Formalism/LocalToGlobal/LatticeGeometry/Inhabited.lean` |
| S07 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/GeoTiedPGraft.lean` |
| S08 | `src/Formalism/LocalToGlobal/LatticeGeometry/GeoTiedP.lean` |
| S09 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/LargeFor.lean` |
| S10 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/NonzeroPlacesOverPrimes.lean` |
| S11 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/FieldValuesMemFixedField.lean` |
| S12 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/JEvExists.lean` |
| S13 | `src/Formalism/LocalToGlobal/IndefiniteReal/FWExist.lean` |
| S14 | `src/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/StableIffCarrierEq.lean` |
| S15 | `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/APerTw.lean` |
| S16 | `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NonemptyHypsOfPublishedUE.lean` |
| S17 | `src/Formalism/LocalToGlobal/Divisibility/RowSideTie.lean` |
| S18 | `src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean` |
| S19 | `src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean` |
| N01 | Native `RHLean/Analysis/AlpogeNativeSignedSlopeComparison.lean` |
| N02 | Native `RHLean/Analysis/AlpogeThin/NativeConstructedDyadicSignedSlopePayment.lean` |

Source attribution: Levent Alpöge (with Claude), the pinned repository above. Its source archive/mirror states no license; this report assigns none. The report paraphrases and locates definitions, rather than claiming new proof of their transitive dependencies.

- S20: `src/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/SetUnipotentTranslate.lean` — `setDiv`, `ht`, `pt`.

- S21: `src/Formalism/LocalRingCardinality/DataArith.lean` — `sFrame`, `DivData`.

- S22: `src/Formalism/LocalRingCardinality/KernelPlaceMeanBound.lean` — `hExpl6`.

- S23: `src/Main.lean` — `riemannHypothesis`, `riemannZeta_eq_zero_re`.

- S24: `src/Statements.lean` — `RiemannZetaZerosOnLine`, `DirichletLNonvanishingRightOfHalf`.

- S25: `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean` — `UpperTheory.EveryCharacter`, `UpperTheory.Top.plugAll`.

- S26: `src/Supplements/Kernels/MainTheorems.lean` — `allChi`, `rhOfAll`.

- S27: `src/Formalism/GammaFactorNonvanishing/CritLine.lean` — `Formalism.VW.rh_of_every`.

- S28: `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean` — `UpperTheory.FinalTheorems.everyCharacter_of_row`, `UpperTheory.FinalTheorems.everyCharacter`.

- N03: native `RHLean/Geometry/NativeGeometricDatum.lean` — `NativeGeometricDatum`.

- N04: native `RHLean/Geometry/NativePrescribedGeometricDatum.lean` — `nativeDyadicHost_exists_prescribedGeometricData`.

- N05: native `RHLean/Geometry/NativeGeometricPeriods.lean` — `periodOfRealEquiv_isPeriod`.

- N06: native `RHLean/Geometry/NativePrescribedGeometricPeriod.lean` — `nativeDyadicHost_exists_prescribedPeriods`.

- N07: native `RHLean/Analysis/AlpogeThin/NativeRayClassData.lean` — `rayData`, `card_le_classNumber_mul_sq`.

- N08: native `RHLean/Analysis/AlpogeThin/NativeRayIdealCounts.lean` — `idealsIn`, `lamIdeal`, `aRay_mul_log`.
