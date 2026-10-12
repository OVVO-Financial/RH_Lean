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
