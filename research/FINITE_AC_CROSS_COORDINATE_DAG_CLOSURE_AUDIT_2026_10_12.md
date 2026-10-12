# Exhaustive cross-coordinate audit: finite A/C and actual-prime VF source

Date: 2026-10-12. Repository: OVVO-Financial/RH_Lean. Base: updated main after merged research-DAG PR #930. This is a source-and-import reconciliation with one elementary new cross-carrier non-overlap lemma. **Finite A, finite C, original-VF actual-prime payment, and RH remain unproved.**

## Scope, provenance, and method

The GitHub tree endpoint returns **2,934 entries**, not truncated, including 835 primary RHLean source paths, 545 research paths, 871 synthesis-export paths, 136 square-block export paths, 62 prime-wheel export paths, 198 script paths and the rest of the repository. The new full-source search tool at [scripts/finite_ac_coordinate_dag_audit.py](../scripts/finite_ac_coordinate_dag_audit.py) uses the existing [repo_index](../scripts/repo_index.py) to index every worktree source occurrence, compare named declaration locations, search both primary library and research proof bodies, and traverse the actual module import DAG. The [workflow](../.github/workflows/finite-ac-cross-coordinate.yml) runs this audit and attempts warning-fatal Lean compilation. GitHub's code-search snippets alone may lag recent merges; fetch actual current source when testing conclusions.

The full declaration audit distinguishes primary declarations from independent exported copies. Graph adjacency is navigation, **not** a theorem of matching physical carriers. A named conditional consumer proves an implication, not its premise.

## A. Finite A/C representation map (one actual endpoint; no independent estimate)

For R>=2 let X=R²−1, M(x)=sum_{n<=x}mu(n) and K_R=max_{0<=y<R}(M(y)−1)²/(y+1)>=1. The original historic floor-kernel has the exact identity

\[
Q_R=\sum_{1\le a,b<R}\mu(a)\mu(b)\lfloor X/(ab)\rfloor
=2M(R-1)-M(X).
\]

Finite-C means |Q_R|<=C R sqrt(K_R), finite-A means (M(X)−1)²<=A R²K_R, with constants uniform in R. Their **existence** is equivalent and sufficient for the existing Mertens-energy/RH consumer. No converse RH=>these particular finite constants is claimed.

| Coordinate pair | Already-proved source | Quantitative status |
| --- | --- | --- |
| scalar endpoint A vs legal ancestry Gram | [SquareRootMertensEndpointAmplification.lean](../RHLean/Proof/SquareRootMertensEndpointAmplification.lean): squareRootMertensEndpointAmplification_iff_legalAncestryGram | Exact equivalence; OPEN bound |
| root minus legal successor | [SquareRootLegalAncestryGramReduction.lean](../RHLean/Proof/SquareRootLegalAncestryGramReduction.lean): sourceRootPrefix_sub_sourceSuccessorPrefix_eq_mertensInt_sub_one | Exactly M(X)−1 |
| parent-fibre and wheel-ordered edge | [SquareRootAncestryParentFibres.lean](../RHLean/Proof/SquareRootAncestryParentFibres.lean) and [WheelToLedgerPushforward.lean](../RHLean/Proof/WheelToLedgerPushforward.lean) | Exact weight- and owner-preserving reindex, not cancellation estimate |
| sequential low-prime wheel shell | [LowWheelAncestryCrossLedgerBridge.lean](../RHLean/Proof/LowWheelAncestryCrossLedgerBridge.lean): squareRootSequentialCrossLedgerCoercivity_iff_mertensEndpointAmplification | Coercivity exactly original OPEN A |
| smooth high-prime owner-two Gram | [OWNER_TWO_UPPER_HALF_POLARIZATION.lean](OWNER_TWO_UPPER_HALF_POLARIZATION.lean) and [DYADIC_SMOOTH_HIGH_JOINT_PACKET.lean](DYADIC_SMOOTH_HIGH_JOINT_PACKET.lean) | Exact M(X) smooth minus transport; signed polarization essential |
| prime-two Othello escape wall | [DYADIC_BUCHSTAB_OTHELLO_GLIDER_WALL.lean](DYADIC_BUCHSTAB_OTHELLO_GLIDER_WALL.lean) | The live annulus is already an escaped boundary, not an unspent cancellable interior |
| historical A closure | [SquareRootAmplificationClosure.lean](../RHLean/Proof/SquareRootAmplificationClosure.lean) | Compiled conditional endpoint-amplification -> critical Mertens energy |
| true primary RH implication | [MertensEnergyRHForward.lean](../RHLean/Analysis/MertensEnergyRHForward.lean) | Compiled conditional energy -> RH |

The exact cross-ledger coercivity margin, on the complete source, is

\[
\boxed{A R^2 K_R-(M(R^2-1)-1)^2.}
\]

The repo explicitly proves that equality. The *upper* cross-ledger inequality obtained from square nonnegativity is automatic, but the needed **lower** cross-ledger inequality is precisely the open finite-A bound. Merely switching from a scalar Mertens amplitude to the prime-shell, smooth/high, ancestry parent, Othello, or Gram vocabulary cannot change this fact.

### The full same-endpoint historical/live Gram weld

Write H_R=M(R−1), L_R=# nonzero odd live integers in (X/2,X], and Gamma_R=sum_{m<n live}mu(m)mu(n). Then

\[
M(X)^2=L_R+2\Gamma_R,\qquad L_R\le R^2/2
\]
and, by the exact floor-kernel identity,

\[
\boxed{Q_R^2=L_R+2\Gamma_R+4H_R^2-4H_R M(X).}
\]

This is the **complete signed historical coupling** in the same scalar coordinate. It preserves the negative or positive signed off-diagonal interaction and the historical/current cross term; no stochastic independence or stationarity is used. Its upper bound is still open: Gamma_R<=B R²K_R would be EQUIVALENT to finite A, up to constants.

The actual live packet gcd pair decomposition, genuine parent/child sign reversals, clipped Euler cubes, and fixed-gcd-cutoff rational sign results already classify the summands. The missing estimate must be uniform for a cutoff growing with R. Fixed-depth errors O_T(sqrt(X)) cannot automatically be summed to T~sqrt(X). Actual Gamma_R can be positive (e.g., R=5561), ruling out termwise Gamma<=0.

## B. Original VF first-bad path: the source and its own physical boundary are ALREADY connected

This is a major finding of the whole-repo search: **we should no longer describe original VF active source -> its own six physical boundaries as a missing theorem.** That operation has already been established.

| Original carrier and operation | Exact source | What remains |
| --- | --- | --- |
| genuine VF active physical site, with actual prime/processed-squarefree weights | [VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean](VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean): vfMidOneBlockActivePhysicalSite | original literal source exists |
| original source, root, squareful restoring and signed square/absolute Gram | [VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER.lean](VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER.lean) | correct original denominator retained |
| original VF active cell pure clipped-base, admitted-base mass zero | [VF_MID_FIRST_BAD_ACTIVE_CLIPPED_BOUNDARY.lean](VF_MID_FIRST_BAD_ACTIVE_CLIPPED_BOUNDARY.lean): vfMidActiveMobiusScale_eq_zero_of_admittedBase | exact, not a bound |
| original site-dependent VF source -> six oriented *raw-parent* boundaries | [VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE.lean](VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE.lean): vfMidActiveCellGram_eq_sixOrientedBoundary | exact physical weight-preserving Fubini |
| only three of six physically nonzero Co/Div orientations | [VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean](VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean): vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess | exact residual plus 3 boundaries |
| boundary + formal negative returned parent heat | [VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean](VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean): vfMidActiveResidual_sharpTransport_iff_sourceInlet | OPEN estimate exactly equivalent to original first-bad payment |
| canonical dyadic multi-block run split | [VF_MID_DYADIC_PREFIX_OWNER.lean](VF_MID_DYADIC_PREFIX_OWNER.lean), [VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR.lean](VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR.lean) | fixed-prefix is endpoint-bounded, signed late-owner correction still OPEN |
| generic no-independent-persistence Dirichlet pair splitting | [VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE.lean](VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE.lean): lowOwnerFirstOwnerSignedCellTelescope_eq_noPersistenceSafe_add_sectorSix | already proved on *different carrier* |
| local sector-six overflow -> rank-lowering child PAIR | [VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR.lean](VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR.lean): vfMidNoPersistenceCapacitor_forces_sectorSixDescent | requires local safe capacity and excess; one PAIR does not bound a lower RUN |
| actual first-bad original-payment proposition and conditional terminal consumer | [VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean](VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean): VFMid915FirstBadSourcePaymentStatement, vfMid915FirstBad_closed_of_sourcePayment | payment OPEN; contradiction CONDITIONAL |

The sharp transport/negative heat equation has *already been proved equivalent to the open source inlet*. Thus plugging it into linarith without an independent arithmetic restriction cannot close the first-bad contradiction.

## C. Precise NEW cross-coordinate no-go: the two candidate sector-six carriers are DISJOINT

The search reveals a simple but decisive geometry that explains why naive re-use of the #903 Dirichlet sector-six theorem has not paid the original #915 weighted source.

Fix one actual first owner p, lower signature sig, and common square endpoint W=squareRootEndpoint(R+1). Define

\[
A_p=\{a\text{ in the p-free base fibre}:pa\le W\},
\qquad
C_p=\{a\text{ in that fibre}:pa>W\}.
\]

The **original VF active returned pair** is zero-extended from

\[
\boxed{\mathcal V_p=C_p\times A_p}
\]

as explicitly defined by vfMidActiveReturnedPairCarrier. Its actual signed atom is **site-dependent VF scales times** the Dirichlet polarization atom, with the VF scale equal to zero off the clipped/admitted physical support.

In contrast, the generic greatest-owner **recursive sector six** starts with positive-lag admitted/admitted pairs contained in

\[
\boxed{\mathcal D_p=A_p\times A_p.}
\]

Therefore

\[
\boxed{\mathcal V_p\cap\mathcal D_p=\varnothing,}
\]

because no a satisfies both pa>W and pa<=W. The new [VF_MID_932_ORIGINAL_VF_CARRIER_DISJOINT.lean](VF_MID_932_ORIGINAL_VF_CARRIER_DISJOINT.lean) records this explicit cross-coordinate disjointness, plus zero extension of the literal VF returned atom on the entire admitted-positive carrier. These statements are elementary **carrier guardrails**, not a signed-payment theorem; kernel compilation is required before claiming formal verification.

This is **not** the discovery of a missing elementary VF source classifier. The existing active-clipped-boundary module already proves original VF admitted-base mass vanishes! The genuinely useful new observation is the direct proof of incompatibility with the separately formalized admitted/admitted recursive sector-six currency. It rules out a shortcut based on equating cells or spending the nonpositive Dirichlet sector-six terms in place. To transfer cancellation, the proof must use **an actual nonlocal historical-return correspondence across the square cutoff** (or a different independently proved signed estimate). A parent that exists as a symbolic sign reversal is not necessarily a compensating historical occurrence on the same weighted source.

## D. Existing rigorous restrictions exposed by the search (not new analytic cancellation)

1. [VF_MID_DYADIC_OWNER_EXACT.lean](VF_MID_DYADIC_OWNER_EXACT.lean) proves each late least-prime owner above the frozen root contributes at most FOUR sites in one subdoubling square block, and all unresolved squarefree composite survivors are products of exactly TWO fresh primes with Möbius sign +1. The number of fresh owners and square blocks grows, so per-owner four-site capacity does not bound the cumulative signed run.
2. [VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR.lean](VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR.lean) proves the literal lower-scale prime interval transport is NONNEGATIVE and children lie below the starting square. That is the lower-wall/composite-vacuum direction only; the upper-wall prime-jump direction has its own true wheel capacity bill.
3. [VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET.lean](VF_MID_ONE_BLOCK_SOURCE_TO_RANK_INLET.lean) proves a one-block native-descent linear remainder smaller than a radial-square increment. Its own comments warn that this does NOT pay the quadratic historical/current cross term. The exact one-block energy weld is already present; it must not be squared and separated blindly.
4. [SquareRunFreshPrimeCubeBoundary.lean](../RHLean/Analysis/SquareRunFreshPrimeCubeBoundary.lean) proves fresh-prime cancellation cubes straddle BOTH boundaries of any subdoubling physical run; no complete interior four-corner payment is available.
5. [SquareRunTopEscapeClassification.lean](../RHLean/Analysis/SquareRunTopEscapeClassification.lean) proves the natural same-prime leaf is empty in a subdoubling run and that bounding its top escape is EQUIVALENT to Mertens energy. This is a formal NO-GO to naive one-prime matching.
6. [PrimeAveragedCubeEnergy.lean](../RHLean/Analysis/PrimeAveragedCubeEnergy.lean) proves prime-averaging total first-failure-frontier energies gives the Mertens square itself, not a new independent saving.
7. [DYADIC_LONG_RANGE_TETHER_AUDIT.lean](DYADIC_LONG_RANGE_TETHER_AUDIT.lean) proves the complete prime-labelled long-range tether is injective but the cofactor-only root projection is not; at R=56, 198 large prime source occurrences can share cofactor 1. A one-unit charge per historical cofactor is unsound.
8. [GLOBAL_RETURNED_CORE_ZERO_TARGET_CLIPPED_HISTORY_CONTRACTION.lean](GLOBAL_RETURNED_CORE_ZERO_TARGET_CLIPPED_HISTORY_CONTRACTION.lean) proves 79/162, 1/2, 1/4, and 3/4 reciprocal outgoing energy contractions. They apply to their explicit restricted owners and *reciprocal physical amplitudes*, not automatically to the original VF first-bad Co/Div budget.
9. [JointDaughterCrossEnergyAudit.lean](../RHLean/Proof/JointDaughterCrossEnergyAudit.lean) explicitly exhibits the missing physical daughter-to-Mertens energy normalization as a hypothesis. Negative cross-owner estimates in a different coefficient metric are not an original-source payment.
10. [VF_QUOTIENT_VARIATION_FIRSTBAD_ATTACK.lean](VF_QUOTIENT_VARIATION_FIRSTBAD_ATTACK.lean) proves a strict square-hyperbola quotient gap and sharp short-coefficient reduction, but long low-quotient variation remains open.
11. [VF_SHARP_OAI_SIGNED_MOMENT_ATTACK.lean](VF_SHARP_OAI_SIGNED_MOMENT_ATTACK.lean) preserves genuine physical weights and gives a conditional sharp centered-moment ceiling; no unconditional uniform physical moment or one-to-one ideal/source identification is proved.
12. [VF_MID_915_SECTOR_SIX_CONE_AUDIT.md](VF_MID_915_SECTOR_SIX_CONE_AUDIT.md) records negative raw recursive sector-six cone slack at R=8 and R=18. The raw recursive sector itself is NOT automatically cone-balanced, even though sampled original weighted global balances were positive.

## E. Narrowest non-circular closure program after the search

**Canonical VF:** Existing results already map the actual weighted source to its own three clipped Co/Div boundaries; the generic safe/sector-six classifier lives on DISJOINT admitted/admitted Dirichlet pairs. Next prove (a) an original-occurrence and original-weight HISTORICAL-RETURN transfer (rather than identity/inclusion between those carriers), with correct least/greatest ownership, masks, two cutoffs, and historical denominator; and (b) a quantitative signed lower-child **RUN** descent/payment from a hypothetical actual-prime first-bad endpoint. This must be an independent arithmetic theorem using the exact prime-factor structure, not a new assumption equivalent to first-bad payment. It cannot conclude from the existing statement that *one pair* descends.

**Alternative finite A/C:** Work on the exact original Q_R floor-kernel; use the fully reassembled live gcd sign Gram together with the historical coupling 4H_R*M(X), preserving real Möbius zero density and prime-dependent clocks. The missing input is a uniform **positive off-diagonal upper** estimate at moving cutoff. The existing one-sided negative cross-owner lower bound, fixed-T rational signs, average Euler/CRT/prime-wave estimates, and very large exact numerical scan do not supply it. This route is not a newly mandatory prerequisite for the canonical VF proof.

**No-go:** Do not create yet another scalar RH-equivalent signed Gram, square-root coercivity margin, generic no-persistence theorem, random partition model, or unweighted/unsigned support bound. The repo has exact representations already.

## F. Acceptance criteria

- Exact declaration locations and import reachability emitted by the full-index script, sourced from the updated main worktree; duplicate exports are not treated as new independent proof input.
- Lean warning-fatal compilation and three standard-axiom audits of the new cross-carrier disjointness module via the dedicated workflow. If CI is incomplete or fails, the new Lean statements are UNVERIFIED.
- A source-preserving quantitative signed estimate, *independently derived*, or a genuine weighted cross-cutoff return + mass-carrying lower-run descent is still required for any claimed RH closure.
- PR remains draft, no merge without review/approval; no probabilistic, density extrapolation or hidden RH-strength premise.

See also [CURRENT_PROOF_CONTRACT.md](../CURRENT_PROOF_CONTRACT.md), [docs/research-frontier.json](../docs/research-frontier.json), [docs/REPOSITORY_SEARCH.md](../docs/REPOSITORY_SEARCH.md), [research/FINITE_A_C_VF_ALIGNMENT_2026_10_11.md](FINITE_A_C_VF_ALIGNMENT_2026_10_11.md), and [research/VF_MID_915_SOURCE_PAYMENT_STATUS.md](VF_MID_915_SOURCE_PAYMENT_STATUS.md).


## G. Further high-value source discoveries: apparent closures that are already conditional or on the wrong side of the wall

The exhaustive source-index output contains 70 first-bad/source-budget declaration-body matches, 114 amplification/Gram matches, 123 coercivity/contractive matches, 1,020 signed Fubini matches, and 35 run-descent matches in the primary library plus research tree. These counts are source SEARCH HITS, not independently proved arithmetic statements. The full-index CI on a PR source snapshot scanned **2,783 eligible files, 2,164 Lean modules, 32,640 declarations and zero import cycles**, with **all 28 specified exact anchors located**. A follow-up exact final-head check is still required. The import graph CONFIRMS that the original VF raw-parent module transitively imports the generic Dirichlet sector-six continuation module. Thus the obstacle is NOT an absent import path: it is the proven disjointness of their literal pair supports and incompatible signed physical weights.

**Already proved conditional-rule equivalence.** [VF_MID_FIRST_BAD_ACTUAL_ADMISSIBILITY_CERTIFICATE.lean](VF_MID_FIRST_BAD_ACTUAL_ADMISSIBILITY_CERTIFICATE.lean) proves vfV2ActualPrime_verifiedStructuralRules and has the precisely named

\[
\text{vfV2ActualPrime\_signedOwnerRule\_iff\_noFirstBad}.
\]

The supposed global owner-escape rule is equivalent to there being no later first-bad endpoint. The theorem vfV2ActualOccurrencePreservingReturn_closes_firstBad explicitly takes the unchanged **original signed six-sector budget as an hypothesis**. This cannot be imported as independent admissibility or numerical compensation. It confirms the exact logical cost of the desired final sign estimate.

**Owner-two interior is ALREADY quantitatively controlled.** [GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean](GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean) proves

- lowOwnerFirstOwnerClippedAmplitude_two_eq_topMertens: the owner-2 clipped exit is EXACTLY M(X_R);
- squareEndpointMertensEnergyReal_eq_ownerTwoClipped_sq: the required endpoint square is that exit square;
- ownerTwoCompensatedInterior_fourEnergyBound_unconditional: the interior ALREADY obeys the target-shaped four-energy upper estimate without any new hypothesis.

Therefore using the proven interior 1/4-frame or four-energy bound **cannot** close finite A. The entire hard M(X_R) quantity remains on the *clipped boundary*. This is a stronger no-go than the mere absence of an identical carrier: the alleged helpful bound is already available and explicitly leaves the full top-scale Mertens discrepancy unpaid.

**Directional Perron-frame restriction.** [STABLE_FAR_PERRON_QUARTER_FRAME_BOUND.lean](STABLE_FAR_PERRON_QUARTER_FRAME_BOUND.lean) proves an unconditional 1/4 upper synthesis frame for the critical q² owner multiplier but also constructs a zero-frequency two-owner nonzero-input / zero-output witness. Its inequality cannot be reversed to bound owner input energies or the original physical source. The unproved amplitude-to-daughter identification remains necessary.

**Dyadic dissipation is an open quantitative package.** [PrimeSieveDyadicPacketDissipation.lean](../RHLean/Analysis/PrimeSieveDyadicPacketDissipation.lean) records the exact deep-energy identity D_J=L_J+D_(J+1), and conditional level-fraction or reverse-Carleson RH consumers. No unconditional lower bound on the released signed-sibling energy at the active moving frontier is proved there.

**Revised priority:** the narrow signed arithmetic breakthrough cannot come from an existing compensated *interior* contraction or an import edge alone. It must control the actual top clipped exit using literal nonlocal historical returns and an occurrence-preserving, bounded-multiplicity aggregate signed payment, or independently control the fully signed Mertens cross-owner boundary. The repository is unusually complete in equivalent representations; that very completeness rules out several tempting shortcuts.


## H. Proved declaration-graph overlap audit: 19 RH leaves, 70 cross-module duplicate signatures

The separate, fully successful **primary Lean knowledge graph / proof-inventory** workflow on updated-main SHA fac70bba86fc, run [38202495853](https://github.com/OVVO-Financial/RH_Lean/actions/runs/38202495853), was retrieved and examined IN ADDITION to the full-source repo-index audit. Its exact provenance counts:

- 12,611 primary Lean declarations, including 8,842 named proofs; research additionally has 4,558 named proofs over 405 indexed research Lean files.
- Of primary declarations, 8,029 classified proved, 624 reduced/conditional, 133 open and 197 explicit no-go propositions. These categories are the graph's mechanical source taxonomy; an axiom audit and actual source are authoritative.
- The conditional implication DAG contains **19 RH-relevant open leaf proposition components**, and the terminal square-prefix-energy theorem's own import/dependency cone contains **42/12,611 declarations and 31/8,842 named proofs**. Most useful arithmetic machinery is OUTSIDE that terminal cone, so genuine missing semantic transfers remain plausible; mere graph ancestry is no such transfer.
- The normalized statement-signature scanner found **111 duplicate groups**, **70 spanning different primary Lean modules**. Such collisions are candidates for exact redundancy, not an unconditional proof when the statements are conditional.
- Four separate statements in [RootSmoothCrossRegionGram.lean](../RHLean/Proof/RootSmoothCrossRegionGram.lean) and [SquareRootLegalAncestryGramReduction.lean](../RHLean/Proof/SquareRootLegalAncestryGramReduction.lean) normalize to the **same shifted square-prefix Mertens state**. Another pair identifies the same positive-smooth-plus-matched decomposition in [RootSmoothCrossRegionGram.lean](../RHLean/Proof/RootSmoothCrossRegionGram.lean) and [SquareRootTransportRealization.lean](../RHLean/Analysis/SquareRootTransportRealization.lean). These are concrete proven overlaps; none adds the missing positive signed mixed-term estimate.
- The actual open obligation SquareRootMertensEndpointAmplificationStatement appears in the graph, with 16 dependent declarations and no unconditional proof. The explicitly equivalent RootSmoothGlobalSignedAntiAlignmentStatement and RootSmoothCrossRegionEnergyBound collapse into one RH-relevant leaf component. This independently confirms that moving between those representations does NOT remove the same obstruction.
- The primary graph's research-overlap detector already flags research modules wholly or mostly repeated in the compiled library (for example STABLE_FAR_COORDINATE_OVERLAP and SquareRootLowPrimeQuantitativeEnergyReduction). Search these compiled twins before writing another duplicate theorem.

Two decisive source-level findings align with this knowledge-graph diagnosis: the **owner-two clipped exit equals the complete top M(X_R)** despite an unconditional correct-scale bound on the compensated interior; and the actual VF weighted clipped/admitted physical pair carrier is **disjoint** from generic admitted/admitted sector-six pairs, despite a transitive import path already existing between their modules. Hence the missing result is *not another import or coordinate equality* but independent quantitative arithmetic on the true source, potentially carried across nonlocal historical-return boundaries.

This knowledge-graph evidence is stronger than a keyword search: it groups provably equivalent proposition components, separates open/conditional/negative results, and identifies where overlapping representations have already been formally reduced to the same Mertens state. It **does not prove finite A, finite C or RH**.


## I. NEW cross-coordinate equality: the chronological prime comb is the dyadic owner-two survivor

The full-source search uncovered a stronger **already-proved pair of theorem families** in *different* primary Lean modules:

- [PrimeCombVisualizationDynamics.lean](../RHLean/Proof/PrimeCombVisualizationDynamics.lean): primeCombTailSignedDelta_eq, the **actual one-prime chronological update** at arbitrary integer W.
- [PrimeCombReciprocalBandCancellation.lean](../RHLean/Proof/PrimeCombReciprocalBandCancellation.lean): primeCombLargePrimeFamilyMass_eq_neg_mertens and reciprocal-quotient bands.
- [DyadicSurvivorMertensInvariant.lean](../RHLean/Proof/DyadicSurvivorMertensInvariant.lean): dyadicLargePrimeSurvivorMass_eq_neg_mertens and dyadicLargePrimeSurvivorMass_eq_primeCombLargePrimeFamilyMass. Thus prime-comb FAMILY and dyadic SURVIVOR were **already** kernel-identified: no independent cancellation is created by rewriting between them.

For every actual prime p>floor(sqrt(W)) with p<=W, put k=floor(W/p). The two primary independently proved identifications are

\[
H_W(p):=\sum_{\substack{W/(2p)<c\le W/p\\c\ {\rm odd}}}\mu(cp)=-M(k)
\qquad\text{and}\qquad
\Delta_W(p):=2(1-M(k)).
\]

This yields a **new explicit cross-coordinate composition**

\[
\boxed{\Delta_W(p)=2\big(1+H_W(p)\big).}
\]

The new Lean module [FINITE_A_C_PRIME_COMB_DYADIC_OCCURRENCE_WELD.lean](FINITE_A_C_PRIME_COMB_DYADIC_OCCURRENCE_WELD.lean) expresses it on the original single prime p and sums it over **every prime occurrence once**, producing

\[
\boxed{\sum_{\sqrt W<p\le W\atop p\text{ prime}}\Delta_W(p)
=2\Bigg(\pi(W)-\pi(\lfloor\sqrt W\rfloor)
+\sum_{\sqrt W<p\le W\atop p\text{ prime}}H_W(p)\Bigg).}\tag{I.1}
\]

**For W>=4** (so every prime greater than sqrt(W) is odd), the full signed **smooth** dyadic live component S_W is defined as the sum over live odd squarefree integers with **no** prime factor greater than floor(sqrt W). Unique factorization on the actual squarefree odd live annulus then gives

\[
\boxed{M(W)=S_W+\sum_{\sqrt W<p\le W}H_W(p)
=S_W+\frac12\sum_{\sqrt W<p\le W}\Delta_W(p)
-\big(\pi(W)-\pi(\lfloor\sqrt W\rfloor)\big).}\tag{I.2}
\]

**Small-clock exception:** At W=2 or 3, the generic high-prime sum includes p=2. Its formal dyadic fibre is valid but does not consist of ODD physical live numbers, so the smooth-plus-high decomposition (I.2) must not be applied there. Every square endpoint used in the numerical scan has R>=3, so W=R²-1>=8. The per-prime chronological/dyadic fibre theorem holds separately without this physical odd-live restriction.

These identities preserve every actual cofactor, prime interval and Möbius sign. However, the *remaining bound* on the right of (I.2) is precisely the Mertens discrepancy again, not an independently paid inequality.

### Boundary convention discovered: there is an EXACT one-prime correction

For every integer R>=2 and X_R=R²−1,

\[
\boxed{\lfloor\sqrt{X_R}\rfloor=R-1.}
\]

Consequently the **generic** post-root fibre sum in DyadicSurvivorMertensInvariant.lean ranges over p>R−1, whereas the **canonical** square-root transport squareRootDyadicSurvivorMass R ranges over p>R. These two adjacent definitions do NOT have the same prime population when R itself is prime. They differ by exactly ONE physical owner:

\[
\boxed{
\operatorname{DyadicPostRoot}(R^2-1)
=\operatorname{SquareRootDyadicTransport}(R)
-\mathbf 1_{\mathbb P}(R)\,M(R-1).}\tag{I.3}
\]

The new Lean module encodes this as squareRootEndpoint_natSqrt_eq_pred and dyadicPostRootSurvivorMass_squareEndpoint_eq_transport_add_rootPacket. This root equality correction is *not* a sign saving; failing to include it causes spurious numerical mismatches and can misalign Fubini endpoint conventions. A similar actual chronological correction is

\[
\boxed{\Delta_{\rm generic}-\Delta_{\rm canonical}
=2\mathbf1_{\mathbb P}(R)(1-M(R-1)).}\tag{I.4}
\]

**The correction is quantitatively harmless at the finite-A scale.** By definition of the historical lower envelope K_R>=1,
\[
(M(R-1)-1)^2\le R K_R,
\]
whence
\[
\boxed{\big|\mathbf1_{\mathbb P}(R)M(R-1)\big|^2
\le 2R K_R+2\le 4R K_R,\qquad R\ge2.}\tag{I.5}
\]
Thus switching endpoint conventions incurs only a smaller-scale O(sqrt(R K_R)) term, while the real large cross-sector compensation is still unproved.

### Exact genuine-prime and Möbius numerics, not random models

An independently rebuilt Möbius linear sieve through 35,999,999 tests *all* the equalities above, including odd-dyadic M(W), on each root. Here H_can excludes p=R and H_generic includes it if prime.

| R | X=R²-1 | M(R-1) | M(X) | H_can | H_generic | root correction | S_generic | total chronological Δ |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 17 | 288 | -1 | -7 | -4 | -3 | +1 | -4 | 104 |
| 56 | 3,135 | -2 | +6 | +47 | +47 | 0 | -41 | 952 |
| 317 | 100,488 | -3 | -28 | +887 | +890 | +3 | -918 | 20,912 |
| 1000 | 999,999 | +2 | +212 | +6,567 | +6,567 | 0 | -6,355 | 169,794 |
| 2000 | 3,999,999 | +5 | +192 | +21,607 | +21,607 | 0 | -21,415 | 608,900 |
| 5561 | 30,924,720 | +5 | -2,544 | +124,373 | +124,373 | 0 | -126,917 | 4,070,622 |
| 6000 | 35,999,999 | 0 | +2,256 | +145,554 | +145,554 | 0 | -143,298 | 4,698,066 |

**This is an important empirical cancellation witness in a shared coordinate:** at R=5561 the high-prime live Möbius source is **+124,373**, the root-smooth live source is **-126,917**, and the genuine signed endpoint is **-2,544**. Any proof that individually estimates only high fibres, only the smooth field or only the prime-comb updates loses the dominant \(\approx 125,000\)-unit cross-sector cancellation.

The exact finite-A equation in these same coordinates is

\[
\boxed{
\big(S_R+\tfrac12\Delta_R-N_R-1\big)^2\le A R^2K_R,
\quad
N_R=\#\{p\ge R:\ p\le R^2-1,\ p\ \mathrm{prime}\}.}\tag{I.6}
\]

It is **the original finite-A claim**, not a completed bound. The search shows where the arithmetic dependence has to survive: through the entire smooth/high signed cross term and the true prime counts, after the safe small root-equality correction has been removed. The successful new result is an exact *reconciliation of coordinate systems*, not a proof of RH.

The hosted strict source audit and warning-fatal Lean checks are the acceptance tests for the new statements; until those checks finish, only the independently checked integer calculations and paper identities are established.


## J. Four-way full-source commutative diagram and measured signed quadratic cancellation

The repository also already proves the canonical **born-smooth + positive-smooth + physical dyadic high-prime = true Mertens endpoint** in [DyadicSurvivorMatchedSplice.lean](../RHLean/Proof/DyadicSurvivorMatchedSplice.lean):

\[
\boxed{P_R+B_R+H_R^{\rm can}=M(R^2-1).}
\]

Combining that finished theorem with (I.3) gives a NEW formal coordinate, with exactly the right root-prime adjustment,

\[
S_R^{\rm gen}:=P_R+B_R-\mathbf1_{\mathbb P}(R)H_{R^2-1}(R).
\]

This is a *definition* of the corrected smooth component on the formal Mobius source. For R>=3 it coincides with the actual greatest-prime-below-root odd-live squarefree census, and the complete global identity is

\[
\boxed{S_R^{\rm gen}+H_R^{\rm gen}=M(R^2-1),}
\]
\[
\boxed{
S_R^{\rm gen}+\frac12\Delta_R^{\rm gen}-N_R^{\rm gen}
=M(R^2-1).
}
\]

The new Lean file now states and proves, from exact existing primary sources,

- squareRootOddGenericSmooth_add_postRoot_eq_squarePrefixMertens;
- squareRootOddGenericSmooth_add_half_primeComb_sub_primeCount_eq_mertens.

These are full original-source **four-coordinate welding identities** (prime-comb chronology, dyadic high-prime survivor, born/positive smooth, complete Mertens), not yet checked by the new CI compile. No randomness, no independence and no discarded prime label occurs. The corrections are exactly zero except for the one genuine p=R face when R is prime.

### The exact signed Co/Div cancellation this exposes

Set S=S_R^{gen}, H=H_R^{gen}, M=S+H. At R=5561 the independently verified true Möbius census gives:

\[
S=-126,917,\quad H=124,373,\quad M=-2,544.
\]

Then the **quadratic signed cross-term** is

\[
\begin{aligned}
S^2 &=16,107,924,889,\\
H^2 &=15,468,643,129,\\
2SH &=-31,570,096,082,\\
(S+H)^2 &= 6,471,936.
\end{aligned}
\]

Thus the actual negative historical/survivor interaction cancels

\[
\boxed{99.9795\%}
\]

of the positive diagonal \(S^2+H^2=31,576,568,018\) at this tested endpoint. At R=6000 the cancellation is **99.9878%**; at R=317 it is **99.9520%**. These are genuine signed product identities, not an unsubstantiated average-sign assumption.

Crucially, **the arithmetic question is now fully explicit in matched populations**: does the genuine prime-factor/ownership structure prohibit positive excess \(S^2+H^2+2SH\) from exceeding \(A R^2K_R\) uniformly? The empirical cross-sector anti-alignment is powerful evidence that absolute-value bounds on separate populations are wasteful, but these exact equalities do NOT prove that the observed 99.9% negative cross-term persists at all R. Indeed at R=17 the two components are both negative and the cross-term is POSITIVE. A uniform theorem must handle every sign regime.

The candidate analytic work is no longer to *identify* the missing pair population: both true smooth and high populations and their relative sign are fully explicit. It is to establish a **uniform quantitative anti-persistence of the signed smooth/high sum under genuine prime-dependent chronological updates**. The correct measure must remain in the original \(K_R\) normalization and not be replaced by an RH-equivalent conditional hypothesis.

No new universal bound and no completed RH proof is asserted.


## K. Exhaustive all-root signed anticorrelation: the positive mixed sector disappears after R=21 on the tested range

The original empirical census only selected seven roots. The new
[dyadic_all_roots_signed_cross_scan.cpp](../experiments/PrimePopulationCutoff/dyadic_all_roots_signed_cross_scan.cpp)
runs a **complete independent physical-site census at every root** \(2\le R\le6000\), all integers through 35,999,999.

It builds the exact Möbius function with a linear prime sieve. Each odd squarefree site \(m\) is active precisely for roots

\[
\lfloor\sqrt m\rfloor+1\le R\le\lfloor\sqrt{2m}\rfloor.
\]

Among these, it belongs to the true GENERIC high-prime sector exactly when
\(R\le P^+(m)\), where \(P^+(m)\) is the actual largest prime factor;
otherwise it belongs to the genuine smooth odd sector. Two difference arrays
sum each physical occurrence once over its ENTIRE root lifetime, so every
root is verified without an \(O(R^2)\) independent rescan.
The scan *separately* computes the raw prefix \(M(R^2-1)\) directly from \(\mu\),
and asserts its exact equality to the sum of the two cumulative sector ledgers
for **all 5,999 roots**. The sample direct prime-by-prime quotient census in
the other program is an independent second crosscheck.

Define the signed quadratic interaction

\[
\mathcal I_R:=2S_R^{\rm gen} H_R^{\rm gen}.
\]

The exhaustive deterministic scan returns:

- **Only four strictly positive \(\mathcal I_R\)** among all \(2\le R\le6000\): \(R=11,14,17,21\).
- For **every tested \(R\ge22\)**, \(S_R^{\rm gen}<0\) and \(H_R^{\rm gen}\ge0\).
- The only \(R\ge22\) with \(H_R^{\rm gen}=0\) is \(R=26\); all \(27\le R\le6000\) have \(S_R^{\rm gen}<0<H_R^{\rm gen}\) and hence \(\mathcal I_R<0\).
- Among \(R\ge100\), the worst normalized unsquared-sector energy ratio
\[
\frac{(S_R^{\rm gen}+H_R^{\rm gen})^2}
     {(S_R^{\rm gen})^2+(H_R^{\rm gen})^2}
\]
is \(\approx0.03463136832\), at \(R=102\). This is a **finite-range** extremum, not a uniform all-R proof.

The original physical-sign conjecture suggested by the data is

\[
\boxed{S_R^{\rm gen}<0<H_R^{\rm gen}\quad\forall R\ge27.}
\]

**Status: conjecture, not a theorem.** Even proving the two sector signs for all sufficiently large roots would NOT establish finite \(A\): the negative cross term must quantitatively cancel the diagonals to within the much smaller \(A R^2K_R\) wall. This experiment isolates a deterministic real-arithmetic tendency that avoids making false conjectures such as \(\Gamma_R\le0\) or universally negative cross term for all roots.

The two all-root scan/selected-root prime-fibre audit programs are registered
in the PR #931 CI and will reject any failed true-Mobius endpoint reassembly.
