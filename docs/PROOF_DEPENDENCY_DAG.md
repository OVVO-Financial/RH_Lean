# RH_Lean mathematical proof-dependency DAG

**Status (registry `2026-11-08.2`, base main `8b5a6921002da0742ecfab9ee7d40728ed5fe348`, Lean 4.34.1): merged evidence through PR #1109 is unchanged; repaired PRs #1111 and #1113 are GREEN / REVIEW_READY / UNMERGED at their recorded heads. RH remains OPEN. Uniform finite A, zero-log amplification and complete signed HIGH closure remain OPEN.** This page is generated from, and validated against, the machine-readable registry [proof-obligations.json](proof-obligations.json) by [`scripts/proof_obligation_dag.py`](../scripts/proof_obligation_dag.py). It is a proof map, not a proof: a compiled implication does not prove its premise, an explicit theorem interface is not a Lean construction, and paper or numerical findings are not Lean certificates.

**Exact-head evidence:** [#1111](https://github.com/OVVO-Financial/RH_Lean/pull/1111) at `20875a55dd9780993c4cdc06624c88be6060e2ee` has 13/13 checks green, including warning-fatal source, fixed public types and all three new standard-axiom closures. It proves `b_active=b_pack=7/8-1/(32*N_pack)`, with `N_pack=nearUniformSlotCount` fixed independently of cutoff and every positive Mertens exponent loss. Main still has `b_main=7/8-1/(48*explicitSlotCount)`. The elementary ceiling comparison `N_pack<=explicitSlotCount` and resulting positive gap are labeled paper corollaries, not additional named Lean declarations. The next-improvement node follows `b_active`; its previous numerical target is retained in the registry history. This does not change the canonical VF/RH contract or assert the separate VERIFIED_ETA program gate.

[#1113](https://github.com/OVVO-Financial/RH_Lean/pull/1113) at `43c9ac1235ceed8f40762ad5357486fea27e31bb` has 14/14 checks green. It proves the original signed prime/prefix/removed-site decomposition, a genuine smaller factor root and a finite failure of perfect one-block balance inheritance. It does not prove a same-normalized-bad-event descent or asymptotic anti-clustering bound. Square-block regrouping in #1111 is likewise a separate identity, not a quantitative smooth-to-sharp bridge. Both PRs await human review/merge; earlier failures and the axiom-parser repair remain in the evidence records.

Read first the [November 8 all-route proof status and seven-role handoff](RHLEAN_REPO_WIDE_PROOF_ATTACKS_20261108.md), which supersedes dated route and agent priorities but not theorem signatures, then the [coordinate atlas](COORDINATE_ATLAS.md) (which repository objects are the same quantity in other coordinates), [FORMALIZATION_MILESTONES.md](FORMALIZATION_MILESTONES.md) (what is finished), the [ten-route portfolio](RH_PROOF_ATTACK_PORTFOLIO_20261024.md) (task routing) and the [overlap / imported 7/8 audit](RH_PROOF_OVERLAP_AND_SEVEN_EIGHTHS_AUDIT_20261024.md) (why shared coordinates are not equivalences).

## 1. Three graph layers

| Layer | Question | Source of truth | Producer / check |
| --- | --- | --- | --- |
| **A. Mathematical proof obligations** | Which proposition implies, equals, projects to or refutes which; what each RH route still needs | [proof-obligations.json](proof-obligations.json) | `python3 scripts/proof_obligation_dag.py --check` |
| **B. Lean source and declarations** | Which file and declaration states or proves a node; which modules import which | Lean source on `main`, [repository index](REPOSITORY_SEARCH.md), [knowledge graph](KNOWLEDGE_GRAPH.md), [historical import DAG](RESEARCH_FRONTIER_DAG.md) | `--repo-index` cross-check, `scripts/repo_index.py`, `scripts/proofq.py`, `scripts/research_frontier_dag.py` |
| **C. Evidence and implementation** | Which PR, head, CI run, report, script or reference supports a status, and when it was observed | `evidence` records in the registry (dated snapshot) | validator; refresh from GitHub before relying on open-PR rows |

An import edge (Layer B) proves dependency on code, never a proposition. Evidence grade (Layer C) is recorded separately from logical status (Layer A).

**Node status fields.** `logical_status` ∈ PROVED, ESTABLISHED_LITERATURE, OPEN, CLAIMED (paper, review pending), FINITE_EVIDENCE, REFUTED, DEFINITION (carriers). `formal_status` records the Lean side (on main, green unmerged PR, red PR head, explicit interface, statement only, not formalized). `evidence_class` uses the repository's nine categories (`PROVED_IN_LEAN_ON_MAIN` … `UNKNOWN`). `provenance` separates *proved internally*, *imported certified external Lean*, and *literature passed as an explicit interface / not formalized*. `open_obligation` with `obligation_kind` ∈ ARITHMETIC, REVIEW, FORMALIZATION_COMPLETENESS keeps formalization chores apart from open mathematics.

**Edge types.** `EXACT_IDENTITY`, `PROVED_EQUIVALENCE` (both collapse into one class only when certified by a proved node), `PROVED_IMPLICATION`, `CONDITIONAL_IMPLICATION` (explicit `conditions`; an unreviewed certifier must itself be a condition), `WEIGHTED_PROJECTION` (non-invertible; states what it loses), `REQUIRES` (a proved node may only require proved nodes), `REFUTED_BY`, `INDEPENDENT_ARITHMETIC_GAIN` (a mechanism that would pay an open target; never a proof). The validator collapses proved equivalence classes, rejects any remaining directed cycle as an unlabelled equivalence, enforces the recorded non-equivalences, recomputes every route's unpaid inputs from its edges, and fails if any path to RH has nothing left to pay.

## 2. Major formalization milestone: von Koch (1901) and canonical VF

**Classical theorem `HISTORICAL-VONKOCH-1901`.** von Koch, *Sur la distribution des nombres premiers*, Acta Math. **24** (1901) 159–182, doi:10.1007/BF02403071, proved RH ⇒ π(x) = Li(x) + O(√x log x); the converse is the classical Mellin argument, so RH ⇔ π(x) − Li(x) = O(√x log x). Li₂(x) = ∫₂ˣ dt/log t differs from li by li(2) ≈ 1.04516, which the scale absorbs.

**Formalized in Lean on main (PR [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932), merged 2026-10-12 at head `2713d8ef`, 13 workflow runs / 17 jobs green):**

- `MILESTONE-VF-CANONICAL` — [`vfCanonical`](../research/VF_CANONICAL_SQRT_TWO.lean): VF_can(x) = √2 + Σ_{r=2}^{R−1} (2r+1)/log(r²+r+1/2) + (x−R²)/log((R²+x)/2), R = ⌊√x⌋, with the exact actual-prime block recurrence `vfCanonicalSquareDefect_succ`.
- `MILESTONE-VF-LI-O1` — [`abs_vfCanonicalLiError_le_uniform_allReal`](../research/VF_CANONICAL_SQRT_TWO.lean), [`abs_vfMidLiError_le_uniform_allReal`](../research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean): **VF_can(x) − Li₂(x) = O(1) for every real x ≥ 4**, unconditionally.
- `MILESTONE-VONKOCH-VF-LEAN` (classification `FORMALIZED_CANONICAL_VONKOCH_REDUCTION`) — [`vfCanonicalSquareVonKoch_iff_primeLiVonKoch`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) and companions: (∃C ∀R≥2, |π(R²) − VF_can(R²)| ≤ C R log R) ⇔ (∃C′ ∀x≥4, |π(x) − Li₂(x)| ≤ C′ √x log x), with the all-real and legacy forms in the same class.

**What is not proved.** The classical analytic equivalence enters only as the explicit argument [`ClassicalVonKochRHCriterion`](../research/VF_MID_VON_KOCH_BRIDGE.lean) (`IFACE-CLASSICAL-VONKOCH`); constructing it is the formalization-completeness task `CLASSICAL_VONKOCH_CRITERION_FORMAL_IMPORT_OR_PROOF`. The actual-prime bound `OPEN-VF-ACTUAL-PRIME` (`VFCanonicalSquareVonKochStatement`) is open. `#print axioms` lists logical axioms only; it does not discharge these theorem arguments.

Milestone narrative (not the typed graph; the generated graphs in §6 are authoritative):

```text
HISTORICAL-VONKOCH-1901  (literature; Lean: explicit interface IFACE-CLASSICAL-VONKOCH)

MILESTONE-VF-CANONICAL ──REQUIRES── MILESTONE-VONKOCH-VF-LEAN ──REQUIRES── MILESTONE-VF-LI-ROOT
MILESTONE-VF-LI-O1  ──PROVED_IMPLICATION──▶ MILESTONE-VF-LI-ROOT        (O(1) is the stronger result)

OPEN-VF-ACTUAL-PRIME ≡ PROP-VF-CAN-REAL-VONKOCH ≡ PROP-VF-MID-SQUARE-VONKOCH
                     ≡ PROP-VF-MID-REAL-VONKOCH ≡ PROP-PRIME-LI-VONKOCH   (PROVED_EQUIVALENCE, #932)
        │
        └─CONDITIONAL_IMPLICATION [condition: IFACE-CLASSICAL-VONKOCH]
          certified by RH-CONDITIONAL-CONSUMER (riemannHypothesis_of_vfCanonicalSquare)
                     ▼
                    RH   (OPEN)
```

## 3. Answers an agent should not have to reconstruct

**2026-11-08 correction to the dated October 26 narrative (§3 and historical discussion below).** The intermediate goal "some strict Mertens exponent below 7/8" is now PROVED on main by #1107/#1108: b_base=7/8-1/(48*N_*). The original OAI import #987 remains the foundation, but not the strongest current bound. The newly open targets are *a further complete-source improvement*, *zero-log original amplification*, and *uniform fractional owner contraction*; CORR4 #1109 supplies only an image-multiplicity theorem. See the generated scoreboard and current [all-route handoff](RHLEAN_REPO_WIDE_PROOF_ATTACKS_20261108.md), not historical item 6/10 below.


**Merged #1021 power milestone:** for each beta >= 1/2, `corr4PowerFirstOwnerGram_iff_mertensPowerBound` proves `(exists A>=0, Corr4PowerFirstOwnerGram A beta) <=> MertensPowerBound beta`. This is a *proved equivalence*, not a proof of either arithmetic statement below the imported 7/8 exponent. The distinct OPEN node `OPEN-CORR4-MIXED-TAIL-POWER` asks for the full signed first-owner inequality `2 Gamma_mixed <= 2 E_R + A R^(7/2-eta)` with some eta>0. The merged *conditional* consumer converts this into beta `7/8 - eta/4`. The old RH-strength relaxed remainder `OPEN-CORR4-RELAXED-REMAINDER` remains OPEN; no RH or strict 7/8 improvement is claimed.


1. **von Koch (1901):** RH ⇒ π(x) − Li(x) = O(√x log x); with the classical converse, an equivalence (§2).
2. **Proved in Lean:** canonical VF, all-real VF_can − Li₂ = O(1), and the equivalence of the canonical square-endpoint, all-real, legacy and prime−Li₂ von Koch bounds; the conditional RH consumer.
3. **External:** the classical prime−Li ⇔ RH theorem, as `ClassicalVonKochRHCriterion`.
4. **Significance of O(1):** π − Li₂ and π − VF_can differ by a bounded deterministic term at every real x, so the von Koch question is exactly the actual-prime VF question; it bounds nothing about primes.
5. **Open actual-prime inequality:** ∃C ∀R ≥ 2, |π(R²) − VF_can(R²)| ≤ C R log R.
6. **Imported 7/8 (#987):** ζ(s) ≠ 0 for Re s > 7/8 and M(x) = O_ε(x^{7/8+ε}) on original carriers via pinned OAI; #1107/#1108 subsequently prove the strict explicit boundary 7/8-1/(48N_*), leaving only an ADDITIONAL gain (`OPEN-MERTENS-FURTHER-GAIN`) unproved.
7. **Routes:** VF-LOW, SAT, CODIV, BLOCK, OAI-NNS, JOH, FINITE-AC, CORR4, MU-LIFT, NYMAN; BLOCK's universal form is refuted at R = 549.
8. **Independent mechanisms:** (I) prime/composite incidence (VF-LOW, SAT, JOH); (II) genuine Mertens signed pair and historical envelope (CODIV, FINITE-AC) with CORR4's q² recursion as a distinct mechanism; (III) original OAI Hecke/character (OAI-NNS); (IV) higher-order Newton lift (MU-LIFT); (V) Nyman Hilbert (NYMAN).
9. **Exact missing estimate per route:** §4 scoreboard.
10. **Breakthrough theorems:** any unpaid OPEN input in §5 (each closes RH with its listed conditions); short of RH, `OPEN-MERTENS-FURTHER-GAIN` beyond the current strict explicit baseline, with separate zero-log and finite-A terminal targets.
11. **Numerical shortcut-killers:** `CE-BLOCK-R549`, `CE-CORR4-R57`, `CE-CORR4-R56`, `CE-CORR4-R5561`, `CE-JOH-R4-R7`; literature `LIT-BURNOL-2002` kills the q < 1/2 Nyman contraction; `NOGO-FINITE-A-HURST` (paper) bounds finite-A constants below.
12. **Kernel-verified vs conditional vs paper vs numerical:** the `formal_status` and `evidence_class` columns of §7.
13. **Where:** Lean links and PR columns in §7; dated PR heads and checks in §8.
14. **Who:** §5 agents table.
15. **Does any route prove RH?** No. §5 lists every path's unpaid inputs, each typed as arithmetic open, classical theorem not proved in Lean, review pending, finite outside Lean, or refuted premise.

## 4. Route scoreboard

<!-- BEGIN GENERATED: scoreboard -->
| Route | Disposition | Exact missing mathematics | Quantitative target | Best source | Largest unpaid term | Falsifiers | Next proof action |
| --- | --- | --- | --- | --- | --- | --- | --- |
| **VF-LOW** | OPEN | A legitimate original-source lower-wall restriction or first-bad contradiction retaining all original prime occurrences, VF weights, historical anchors, returning cells, restored terms and signed NNS interactions. | pi(R^2) - VF_can(R^2) >= -K R log R for all R >= R0. | #932 canonical VF/von Koch; #915 source accounting; merged #1106 actual Euler log; floor-Li signed transport; canonical HIGH/LOW on square blocks. | First-bad original weighted actual-prime source; O(1) VF-Li quadrature and zeroth-moment event cancellation do not imply the physical lower wall. | `CE-BLOCK-R549`, `CE-JOH-R4-R7` | Start from paid floor-Li mismatch cancellation and true first-bad #915 source, then derive the first weighted, location-preserving unpaid inequality (including anchors and returning cells). |
| **SAT** | OPEN | A new uniform signed owner-removal or cofactor/prime-innovation inequality with complete original source coefficients and nonlocal historical contributions; arithmetic restrictions on genuine prime locations and their least-prime-owned composite complements. | T(R^2) > A(R^2) - L(R^2) eventually (JOH form) or the VF-LOW wall. | #1019 exact births/moving transport; original least-prime owner census; #1106 prime-admission log; floor-Li Buchstab actual cofactor weights. | Nonlocal historical composite-removal mass; PNT-sized density carries no RH-scale sign. | `CE-JOH-R4-R7` | Compare the three distinct S=A-T carriers; use the already-cancelled floor-Li event stream at the original cofactor weights, keeping exact square-block first moments and boundary corrections. |
| **CODIV** | GLOBAL SIGNED STRICT GAP PAID; CRITICAL COVARIANCE OPEN | Actual full signed covariance already satisfies the merged strict sub-7/8 consequence. Prove an additional complete signed power saving beyond the explicit boundary, or RH-level M^2=O(X^(1+eps)) with the squarefree diagonal. | Main certifies M^2=O_eps(X^(7/4-1/(24N_*)+eps)); green unmerged #1111 certifies MertensGrowthAtMost(b_pack), b_pack=7/8-1/(32*N_pack). Squaring with half the positive loss gives the elementary energy consequence O_eps(X^(2*b_pack+eps)); no new separately named signed-pair theorem is claimed. Further gain and the critical X^(1+eps) remain open. | #1107 complete signed-pair return; #1108 merged explicit bound; #1111 exact-head green unmerged improved native Mertens bound; MertensCovarianceDescent and real Phi / NNS packets. | Joint genuine pair interactions not controlled at the RH-scale; no factorwise transfer from Hecke atom labels to rational Moebius signs. | none recorded | Compare actual complete covariances with already-paid signed-energy bound; identify a smaller weighted source-loss with a full consumer, or prove a new genuine arithmetic restriction. |
| **BLOCK** | Original universal version REFUTED; weaker replacements not automatically accepted | None for the universal statement: it is false. A weaker multi-block, averaged or one-sided theorem must be new, precise, not refuted, with a verified consumer and explicit arithmetic input. | N/A (refuted). | research/VF_MID_LITERAL_BLOCK_CROSSING.lean (valid conditional consumer); scripts/vf_block_capture_counterexample_549.py. | N/A | `CE-BLOCK-R549` | Keep the R = 549 regression permanent; do not assign the universal statement. |
| **OAI-NNS** | STRICT GAP ON MAIN; IMPROVED #1111 GREEN UNMERGED; FURTHER GAIN / RH OPEN | Further complete-source saving beyond the strongest verified b_active=7/8-1/(32*N_pack), available at green unmerged #1111, or a repeatable licensed contraction. Main still has 7/8-1/(48N_*). Retain the existing original cancellation, total-slot-mass LOW and full same-probe HIGH/principal return. | Main: beta<=7/8-1/(48N_*). Green unmerged #1111: beta<=b_active=7/8-1/(32*N_pack). NEXT: beta<=b_active-eta for fixed eta>0, or uniform renewal toward 1/2; every-positive-loss versus fixed-power quantifiers remain distinct. | Merged #1107 VF919TotalMassEndpoint and #1108 finite-slot/amp; exact-head green unmerged #1111 original near-uniform slot witness; retained-slot-feedback marked 1+t/2 and generalized kappa; original complete ledger. | Complete downstream combined counts, crossing/height budgets and every resonant/principal/outer branch when using retained marked 1+t/2 and generalized kappa. | none recorded | Feed proved 1+t/2 marked and kappa>1/2 source moments through the actual combined counts, LOW/HIGH/principal comparison and native return; record first failed exponent, not a new generic cancellation premise. |
| **JOH** | OPEN | A genuine nonlocal least-prime ancestry restriction controlling signed chronological displacement, together with weighted block defects and historical anchors. | G(R^2) < 0 for all R >= R0 (Johnston scale -N^(3/2)/log N). | Actual floor-Li backlog and signed transport; Johnston-weighted composite removal contract; #915 zeroth-moment boundary, distinguished from first moment. | sum_r J_r, trivially O(N^(3/2)/log N) with no sign. | `CE-JOH-R4-R7` | Estimate the true first-moment displacement J_r and cumulative G(R^2), including anchored terms; retain r=4 and r=7 equal-count/opposite-moment falsifiers. |
| **FINITE-AC** | EXPLICIT FINITE-POWER AMP PROVED; UNIFORM FINITE A AND ZERO-LOG OPEN | Show A(X)=X^(o(1)) or a constant uniform bound on the true historical ratio, not merely pointwise finite roots or the fixed positive-power bound of #1108. | Proved A(X)<=C X^(3/4-1/(48N_*)); limsup q(X)<=3/4-1/(24N_*). OPEN: forall eta>0 A(X)<=C_eta X^eta; stronger sup_X A(X)<infty. | #1106 exact Euler logarithmic admission; #1108 exact historical amp; finite A/C alignment; squarePrefixMertens and Q_R=2M(R-1)-M(R^2-1). | Complete signed return relative to actual K_R; using K_R>=1 loses historical feedback strength and cannot prove subpower. | `CE-CORR4-R5561` | Compare prime-admission signed log return, canonical HIGH, legal live-packet Gram, Q_R and cofactor-weighted floor-Li on the ORIGINAL K_R; prove a strictly stronger uniform source estimate; do not reset to the trivial bound. |
| **CORR4** | Q2 COLLISION MULTIPLICITY PROVED (#1109); FULL SIGNED MIXED TAIL OPEN | #1109 controls the multiplicity of original off-ray daughter-cutoff images (at most two), NOT their image energy/signs. Need the complete signed prefix-tail/mixed bill with rays, parent, q>Q, historical prefix and negative daughters kept. | RH-sufficient: \|B_R\|^2 <= (9/4) E_R + C R^2 K_R. Strict-power consumer: 2 Gamma_mixed <= 2 E_R + A R^(7/2-eta). Elementary threshold comparison: beating main requires eta>1/(12N_*); beating green unmerged #1111 requires eta>1/(8*N_pack). The full signed input remains unproved. | Merged #1021 general-power Gram, #1027/#1040 signed reductions, #1109 CORR4_CUTOFF_COLLISIONS; full original q^2 daughter carrier. | Signed mixed-tail return and distinct-image energy; an upper energy bound cannot replace a negative daughter credit with the wrong sign. | `CE-CORR4-R57`, `CE-CORR4-R5561`, `CE-CORR4-R56` | Combine #1109 multiplicity-two off-ray theorem with a new source-specific estimate on IMAGE energy and complete signed mixed terms; retain rays and tail, test the actual R=5561 excursion. |
| **MU-LIFT** | OPEN | A genuinely new full-prefix signed estimate yielding a subcritical exponent r < k. | E(B^k) <= B^(o(1)) E(B)^r, fixed r < k. | #954 actual signed Newton/Heath-Brown convolution, MU-LIFT full-prefix budget, #1109 CORR4 q^2 cutoff multiplicity as optional distinct input. | Remaining K3 ranges and K1/K2 at full prefix scale. | none recorded | Attack a fixed k>=2 with genuine all-prefix r<k and subpower loss; explicitly pay K1/K2/K3 corners, factor-power support and all cutoffs. |
| **NYMAN** | OPEN | Full-scale norm decay or density, not finite-dimensional approximation. | d_N -> 0 at a = 1/2 for the full basis. | Nyman-Beurling positive residue attack and finite rational Gram certificates; external Baez-Duarte equivalence; Burnol lower bound. | All-scale tail of the basis approximation. | none recorded | Show full N->infinity residue-basis density or new weighted a>1/2 consequence; keep a=1/2 external criterion and Burnol q<1/2 obstruction honest. |
<!-- END GENERATED: scoreboard -->

## 5. RH paths, frontier and agents

Each path is a chain of implication edges ending at `RH`. Unpaid inputs are recomputed by the validator from the first premise and every edge condition, minus proved nodes.

<!-- BEGIN GENERATED: paths -->
| Route path | Edges to RH | Unpaid inputs (kind) | Meaning |
| --- | --- | --- | --- |
| `VF-LOW/one-sided` | `E-VF-LOW-RH` | `OPEN-VF-LOW` (arithmetic open); `LIT-MV-OMEGA-PM` (classical theorem, not proved in Lean); `PAPER-VF-LOW-ONE-SIDED` (review pending) | Lower wall + external Omega+- theorem. |
| `VF-LOW/canonical-two-sided` | `E-VF-CAN-RH` | `OPEN-VF-ACTUAL-PRIME` (arithmetic open); `IFACE-CLASSICAL-VONKOCH` (classical theorem, not proved in Lean) | Public canonical target through the formalized von Koch reduction. |
| `VF-LOW/915-first-bad` | `E-915-VF` → `E-VF-CAN-RH` | `OPEN-915-SOURCE-PAYMENT` (arithmetic open); `FINITE-915-BASE-WINDOW` (finite, outside Lean); `IFACE-CLASSICAL-VONKOCH` (classical theorem, not proved in Lean) | Original #915 source payment (fixed K = 2 envelope) into the canonical target. |
| `SAT/via-JOH` | `E-JOH-RH` | `OPEN-JOH-SIGN` (arithmetic open); `LIT-JOHNSTON-2022` (classical theorem, not proved in Lean); `PAPER-JOH-SQUARE-TRANSFER` (review pending) | SAT pays the JOH weighted composite-removal inequality. |
| `SAT/via-VF-LOW` | `E-VF-LOW-RH` | `OPEN-VF-LOW` (arithmetic open); `LIT-MV-OMEGA-PM` (classical theorem, not proved in Lean); `PAPER-VF-LOW-ONE-SIDED` (review pending) | SAT pays the one-sided canonical wall. |
| `CODIV/mertens-energy` | `E-MERTENS-RH` | `PROP-MERTENS-ENERGY` (arithmetic open) | RH-strength CODIV input is literally the Mertens-energy statement (target-equivalent). |
| `BLOCK/literal` | `E-BLOCK-RH` | `REFUTED-BLOCK-UNIVERSAL` (refuted premise); `IFACE-CLASSICAL-VONKOCH` (classical theorem, not proved in Lean) | Valid consumer with a false premise. |
| `OAI-NNS/mertens-energy` | `E-MERTENS-RH` | `PROP-MERTENS-ENERGY` (arithmetic open) | RH strength needs exponent 1/2 + eps; any delta < 3/8 only improves the zero-free region. |
| `JOH/johnston` | `E-JOH-RH` | `OPEN-JOH-SIGN` (arithmetic open); `LIT-JOHNSTON-2022` (classical theorem, not proved in Lean); `PAPER-JOH-SQUARE-TRANSFER` (review pending) | Johnston's external criterion and the square-endpoint transfer. |
| `FINITE-AC/mertens` | `E-FINITE-A-MERTENS` → `E-MERTENS-RH` | `OPEN-FINITE-AC` (arithmetic open) | Fully Lean-certified consumer chain; only the arithmetic premise is open. |
| `CORR4/coefficient-4` | `E-CORR4-FINITE-A` → `E-FINITE-A-MERTENS` → `E-MERTENS-RH` | `OPEN-CORR4` (arithmetic open) | Merged terminal chain riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy. |
| `CORR4/relaxed-remainder` | `E-CORR4-RELAXED` → `E-CORR4-FINITE-A` → `E-FINITE-A-MERTENS` → `E-MERTENS-RH` | `OPEN-CORR4-RELAXED-REMAINDER` (arithmetic open) | Merged #1021 conditional relaxed-remainder consumer into certified CORR-4; only the original arithmetic source bound is unpaid. |
| `MU-LIFT/contraction` | `E-MULIFT-MERTENS` → `E-MERTENS-RH` | `OPEN-MU-LIFT` (arithmetic open); `PAPER-MU-LIFT-CONTRACTION` (review pending) | Paper contraction argument into the Lean Mertens-energy consumer. |
| `NYMAN/baez-duarte` | `E-NYMAN-RH` | `OPEN-NYMAN-DENSITY` (arithmetic open); `LIT-BAEZ-DUARTE` (classical theorem, not proved in Lean) | External Baez-Duarte criterion. |
<!-- END GENERATED: paths -->

Ranked frontier (no viable alternative is retired by ranking):

<!-- BEGIN GENERATED: frontier -->
| Rank | Frontier | Routes | Target nodes | Falsification lens | Task |
| --- | --- | --- | --- | --- | --- |
| A | Complete native square-block HIGH and historical amplification | FINITE-AC, CODIV, VF-LOW | `OPEN-AMPLIFICATION-SUBPOWER`, `MECH-FINITE-AC-HISTORICAL-ENVELOPE`, `MECH-CODIV-SIGNED-COVARIANCE` | `NOGO-FINITE-A-HURST` | Reuse proved canonical LOW O(R), existing strict signed Mertens/covariance and full six-term HIGH; identify the first real loss relative to K_R on the complete signed return. Subpower amp or further exponent improvement, no target-equivalent identity relabeled as saving. |
| B | Reuse complete OAI LOW/HIGH/principal source and feedback | OAI-NNS, CODIV | `OPEN-MERTENS-FURTHER-GAIN`, `MECH-OAI-NNS-COMPLETE-LEDGER` | `CLAIM-1022-POISSON-SAVING` | Reuse merged #1107/#1108 and the stronger exact-head green unmerged #1111 endpoint. Carry proved marked 1+t/2 and generalized kappa through combined count, crossing/height, full HIGH and principal. Compare a new complete improvement with b_active=7/8-1/(32*N_pack), while keeping main's older bound distinct. |
| C | CORR4 signed q2 mixed-tail after multiplicity-two theorem | CORR4, FINITE-AC | `OPEN-CORR4-MIXED-TAIL-POWER`, `OPEN-CORR4-RELAXED-REMAINDER`, `MECH-CORR4-SIGNED-FIRST-OWNER-GRAM` | `NOGO-CORR4-FRAME-ONLY` | Use #1109 cutoff collisions only as multiplicity bookkeeping. Keep negative daughter credit, parent square, ray, q>Q, full physical diagonal and mixed signed terms; prove eta>1/(12N_*) for a further strict gain or RH-sufficient O(R^2 K). |
| D | Euler/floor-Li actual prime ancestry and one-sided walls | VF-LOW, SAT, JOH | `MECH-JOH-ANCESTRY-DISPLACEMENT`, `MECH-VF-LOW-FIRST-LOWER-ESCAPE`, `MECH-SAT-OWNER-REMOVAL` | `CE-JOH-R4-R7` | Use exact floor-Li population cancellation and #1106 genuine Euler admission as supplied. Prove a new rate on original cofactor-weighted event displacement, JOH first moments, or #915 first-bad source, retaining all prime occurrences and boundary corrections. |
| E | Full-prefix higher-order MU lift and independent Hilbert reserve | MU-LIFT, NYMAN | `MECH-MU-LIFT-SUBCRITICAL`, `MECH-NYMAN-FULL-BASIS-DECAY` | `REFUTED-NYMAN-SQUARE-CONTRACTION` | MU-LIFT: prove fixed-degree r<k with subpower loss and full prefix. NYMAN: certify all-scale full-basis density, not finite samples or an impossible q<1/2 square contraction. |
| F | Formalization completeness and falsifier protections | VF-LOW, BLOCK | `CLASSICAL_VONKOCH_CRITERION_FORMAL_IMPORT_OR_PROOF` | `IFACE-CLASSICAL-VONKOCH` | Keep the classical von Koch interface explicit; never use a false universal BLOCK crossing (R=549). Update registry, DAG and milestone render together; verify unconditional vs conditional nodes and known counterexamples. |
<!-- END GENERATED: frontier -->

Seven permanent specialists, one distinct next deliverable each (repository templates only; saved Studio configurations and schedules are unchanged):

<!-- BEGIN GENERATED: agents -->
| Agent | Owns | Next distinct deliverable | Target nodes |
| --- | --- | --- | --- |
| 1. RH | Research Coordinator | All nine viable routes; proof-obligations.json, generated DAG and current certified endpoint | Refresh all ten route states and seven roles with #1106-#1109; select one prime-side and one independent recursive/analytic consumer with exact baseline, full signed source and falsifier. Keep weekly route rotation, not single-route compulsion. | `OPEN-MERTENS-FURTHER-GAIN`, `OPEN-AMPLIFICATION-SUBPOWER`, `OPEN-CORR4-MIXED-TAIL-POWER` |
| 2. RH | Owner Payment | VF-LOW, SAT, JOH; actual prime/cofactor chronology, #915 and floor-Li | One source-faithful weighted prime-event displacement or first-bad boundary inequality starting from the already-proved floor-Li matched cancellation; preserve JOH first moment, #915 masks, historical anchors and all returning cells. | `MECH-JOH-ANCESTRY-DISPLACEMENT`, `MECH-VF-LOW-FIRST-LOWER-ESCAPE`, `MECH-SAT-OWNER-REMOVAL` |
| 3. RH | Adversarial Referee | Quantifier and source-integrity audits, strict baseline comparisons and falsifiers across all nine routes | Independent ACCEPT/REVISE/REJECT on the proposed new signed source estimate: inspect the complete consumer, current b_base, omitted cross terms and K_R, R=549 BLOCK, R=4/7 JOH, R=5561 CORR4 and #1109 negative-credit direction. | `NOGO-CORR4-FRAME-ONLY`, `NOGO-FINITE-A-HURST`, `CLAIM-20261024-OWNER-1` |
| 4. RH | Prime Census Laboratory | Reproducible finite diagnostics and held-out arithmetic falsification | Supply exact held-out R diagnostics for A(X), K_R, CORR4 image/mixed packets and floor-Li FIRST-moment displacement; isolate first counterexample and never promote finite census to a uniform asymptotic. | `FINITE-CORR4-CENSUS`, `CE-JOH-R4-R7`, `CE-CORR4-R5561` |
| 5. RH | Analytic Type II | OAI-NNS and CODIV signed analytic source; independent NYMAN alternatives | Consume existing weighted marked 1+t/2 and generalized kappa estimates through the complete LOW/HIGH/principal comparison; give a same-source full exponent budget versus b_base, or pinpoint the exact consumer inequality still lost. | `MECH-OAI-NNS-COMPLETE-LEDGER`, `OPEN-MERTENS-FURTHER-GAIN`, `MECH-NYMAN-FULL-BASIS-DECAY` |
| 6. RH | Finite Wheel & Incidence | FINITE-AC, CORR4 q2 daughters, MU-LIFT; independent wheel/parity and physical first-owner work | Use #1109 multiplicity-two only on its actual off-ray image carrier; preserve signed parent and daughter credits, and propose either complete mixed-tail eta, subpower K_R amplification or full-prefix r<k signed-lift inequality with a real consumer. | `OPEN-CORR4-MIXED-TAIL-POWER`, `OPEN-AMPLIFICATION-SUBPOWER`, `MECH-MU-LIFT-SUBCRITICAL` |
| 7. RH | Lean Verification | Formalize independently accepted new arithmetic input and maintain truthful, generated proof DAG | Keep proofs on source-pinned Lean 4.34.1 CI with warning-fatal checks, exact types and axiom audits. Render and validate registry/DAG/milestones on every status change; only formalize genuinely accepted remaining consumer, otherwise NO_NEW_THEOREM_TO_FORMALIZE. | `OPEN-MERTENS-FURTHER-GAIN`, `OPEN-AMPLIFICATION-SUBPOWER`, `CLASSICAL_VONKOCH_CRITERION_FORMAL_IMPORT_OR_PROOF` |
<!-- END GENERATED: agents -->

## 6. Graphs (quotient by proved equivalence)

Solid arrows: proved implications and requirements. Dotted: conditional implications, conditions, arithmetic-gain targets and unreviewed projections. Boxes list every member of a proved equivalence class.

<!-- BEGIN GENERATED: mermaid-routes -->
```mermaid
%% RH routes (quotient by proved equivalence)
flowchart LR
  c0["RH"]
  c2["IFACE-CLASSICAL-VONKOCH"]
  c4["MILESTONE-VF-CANONICAL"]
  c5["MILESTONE-VF-LI-ROOT"]
  c6["MILESTONE-VF-LI-O1"]
  c7["MILESTONE-VONKOCH-VF-LEAN"]
  c8["OPEN-VF-ACTUAL-PRIME<br/>PROP-VF-CAN-REAL-VONKOCH<br/>PROP-VF-MID-SQUARE-VONKOCH<br/>PROP-VF-MID-REAL-VONKOCH<br/>PROP-PRIME-LI-VONKOCH"]
  c10["OPEN-VF-LOW"]
  c11["PAPER-VF-LOW-ONE-SIDED"]
  c12["LIT-MV-OMEGA-PM"]
  c13["OPEN-915-SOURCE-PAYMENT"]
  c14["FINITE-915-BASE-WINDOW"]
  c17["MECH-VF-LOW-FIRST-LOWER-ESCAPE"]
  c18["MECH-SAT-OWNER-REMOVAL"]
  c20["OPEN-JOH-SIGN"]
  c21["LIT-JOHNSTON-2022"]
  c22["PAPER-JOH-SQUARE-TRANSFER"]
  c24["MECH-JOH-ANCESTRY-DISPLACEMENT"]
  c27["PROP-MERTENS-ENERGY"]
  c35["MILESTONE-MERTENS-STRICT-EXPLICIT"]
  c36["MECH-CODIV-SIGNED-COVARIANCE"]
  c37["MECH-SIGNED-QUOTIENT-VARIATION"]
  c38["MECH-OAI-NNS-COMPLETE-LEDGER"]
  c42["OPEN-FINITE-AC<br/>PROP-LEGAL-ANCESTRY-GRAM"]
  c45["MECH-FINITE-AC-HISTORICAL-ENVELOPE"]
  c47["OPEN-CORR4"]
  c49["OPEN-CORR4-RELAXED-REMAINDER"]
  c50["PR1021-RELAXED-CONSUMER"]
  c51["PR1023-FRAME-B7"]
  c53["MECH-CORR4-SIGNED-FIRST-OWNER-GRAM"]
  c61["OPEN-MU-LIFT"]
  c62["PAPER-MU-LIFT-CONTRACTION"]
  c63["MECH-MU-LIFT-SUBCRITICAL"]
  c64["OPEN-NYMAN-DENSITY"]
  c65["LIT-BAEZ-DUARTE"]
  c68["MECH-NYMAN-FULL-BASIS-DECAY"]
  c69["REFUTED-BLOCK-UNIVERSAL"]
  c81["OPEN-CORR4-MIXED-TAIL-POWER"]
  c84["MILESTONE-OAI-TOTAL-MASS"]
  c85["MILESTONE-EXPLICIT-AMPLIFICATION"]
  c87["MILESTONE-NEAR-UNIFORM-SLOT-BOUNDARY"]
  c89["OPEN-MERTENS-FURTHER-GAIN"]
  c90["OPEN-AMPLIFICATION-SUBPOWER"]
  c5 -->|required by| c7
  c4 -->|required by| c7
  c6 -->|PROVED_IMPLICATION| c5
  c8 -.->|CONDITIONAL_IMPLICATION| c0
  c2 -.->|condition| c0
  c8 -->|PROVED_IMPLICATION| c10
  c10 -.->|CONDITIONAL_IMPLICATION| c0
  c12 -.->|condition| c0
  c11 -.->|condition| c0
  c13 -.->|CONDITIONAL_IMPLICATION| c8
  c14 -.->|condition| c8
  c17 -.->|INDEPENDENT_ARITHMETIC_GAIN| c10
  c18 -.->|INDEPENDENT_ARITHMETIC_GAIN| c10
  c18 -.->|INDEPENDENT_ARITHMETIC_GAIN| c20
  c24 -.->|INDEPENDENT_ARITHMETIC_GAIN| c20
  c20 -.->|CONDITIONAL_IMPLICATION| c0
  c21 -.->|condition| c0
  c22 -.->|condition| c0
  c27 -->|PROVED_IMPLICATION| c0
  c27 -->|PROVED_IMPLICATION| c35
  c84 -->|required by| c87
  c36 -.->|INDEPENDENT_ARITHMETIC_GAIN| c89
  c37 -.->|INDEPENDENT_ARITHMETIC_GAIN| c89
  c38 -.->|INDEPENDENT_ARITHMETIC_GAIN| c89
  c42 -->|PROVED_IMPLICATION| c27
  c45 -.->|INDEPENDENT_ARITHMETIC_GAIN| c42
  c47 -->|PROVED_IMPLICATION| c42
  c49 -->|PROVED_IMPLICATION| c47
  c51 -->|required by| c50
  c53 -.->|INDEPENDENT_ARITHMETIC_GAIN| c49
  c61 -.->|CONDITIONAL_IMPLICATION| c27
  c62 -.->|condition| c27
  c63 -.->|INDEPENDENT_ARITHMETIC_GAIN| c61
  c64 -.->|CONDITIONAL_IMPLICATION| c0
  c65 -.->|condition| c0
  c68 -.->|INDEPENDENT_ARITHMETIC_GAIN| c64
  c69 -.->|CONDITIONAL_IMPLICATION| c0
  c2 -.->|condition| c0
  c81 -->|PROVED_IMPLICATION| c35
  c35 -->|PROVED_IMPLICATION| c85
  c42 -->|PROVED_IMPLICATION| c90
```
<!-- END GENERATED: mermaid-routes -->

<!-- BEGIN GENERATED: mermaid-carriers -->
```mermaid
%% carriers, projections and refutations
flowchart LR
  c25["REFUTED-JOH-COUNT-ONLY"]
  c26["CE-JOH-R4-R7"]
  c55["REFUTED-CORR4-C-012"]
  c56["CE-CORR4-R5561"]
  c57["REFUTED-CORR4-LOCAL-SIGN"]
  c58["CE-CORR4-R57"]
  c59["REFUTED-CORR4-DAUGHTER-ONLY"]
  c60["CE-CORR4-R56"]
  c66["LIT-BURNOL-2002"]
  c67["REFUTED-NYMAN-SQUARE-CONTRACTION"]
  c69["REFUTED-BLOCK-UNIVERSAL"]
  c70["CE-BLOCK-R549"]
  c72["CARRIER-PRIME-MODEL-EVENTS"]
  c73["CARRIER-915-ZEROTH-MOMENT"]
  c74["CARRIER-JOH-FIRST-MOMENT"]
  c75["CARRIER-915-WEIGHTED-SOURCE"]
  c72 -->|WEIGHTED_PROJECTION| c73
  c72 -.->|WEIGHTED_PROJECTION| c74
  c75 -->|WEIGHTED_PROJECTION| c73
  c26 -.->|refutes| c25
  c56 -.->|refutes| c55
  c58 -.->|refutes| c57
  c60 -.->|refutes| c59
  c66 -.->|refutes| c67
  c70 -.->|refutes| c69
```
<!-- END GENERATED: mermaid-carriers -->

Proved equivalence classes:

<!-- BEGIN GENERATED: classes -->
| Class | Members (proved equivalent) | Status |
| --- | --- | --- |
| `OPEN-VF-ACTUAL-PRIME` | `OPEN-VF-ACTUAL-PRIME`, `PROP-VF-CAN-REAL-VONKOCH`, `PROP-VF-MID-SQUARE-VONKOCH`, `PROP-VF-MID-REAL-VONKOCH`, `PROP-PRIME-LI-VONKOCH` | OPEN |
| `OPEN-FINITE-AC` | `OPEN-FINITE-AC`, `PROP-LEGAL-ANCESTRY-GRAM` | OPEN |
<!-- END GENERATED: classes -->

Recorded non-equivalences (the validator fails if any pair collapses):

<!-- BEGIN GENERATED: non-equivalences -->
| Not equivalent | Reason |
| --- | --- |
| `CARRIER-915-WEIGHTED-SOURCE` ≠ `CARRIER-SAT-MERTENS` | The original #915 weighted, masked, clipped, anchored NNS source is not the unweighted signed Mertens smooth-minus-transport kernel; only an aggregate zeroth-moment identity is proved. |
| `CARRIER-JOH-FIRST-MOMENT` ≠ `CARRIER-915-ZEROTH-MOMENT` | Blocks r = 4, 7 have zero count defect and opposite first-moment displacement (CE-JOH-R4-R7). |
| `OPEN-JOH-SIGN` ≠ `OPEN-VF-ACTUAL-PRIME` | JOH is a Cesaro/weighted projection of the pointwise discrepancy; it is not pointwise-equivalent to the square-endpoint VF error. |
| `OPEN-CORR4` ≠ `OPEN-FINITE-AC` | Only CORR-4 => finite A is proved; shared K_R and a consumer do not give the reverse. |
| `OPEN-FINITE-AC` ≠ `PROP-MERTENS-ENERGY` | Finite A implies the Mertens energy statement; the converse is not proved and finite A can be stronger than RH. |
| `PROP-LEGAL-ANCESTRY-GRAM` ≠ `PROP-MERTENS-ENERGY` | Co/Div and finite A/C are existentially equivalent only on the correctly normalized live-packet carrier, not as global unnormalized covariance statements. |
| `CARRIER-OAI-IDEAL-SOURCE` ≠ `CARRIER-915-WEIGHTED-SOURCE` | Original OAI ideal coefficients are not automatically RH_Lean physical prime-owner coefficients; #987 is an output-level bound. |
| `IMPORTED-OAI-7-8` ≠ `OPEN-MERTENS-FURTHER-GAIN` | The imported OAI 7/8 bound and the strongest already certified strict baseline do not themselves supply an ADDITIONAL saving beyond b_active=7/8-1/(32*N_pack); that further complete consumer remains OPEN. |
| `OPEN-VF-LOW` ≠ `OPEN-VF-ACTUAL-PRIME` | One-sided sufficiency uses an external Omega+- theorem; no Lean equivalence. |
| `OPEN-915-SOURCE-PAYMENT` ≠ `OPEN-VF-ACTUAL-PRIME` | The #915 payment is a fixed-constant K = 2 envelope; the public target is existential in C. |
| `CLASSICAL_VONKOCH_CRITERION_FORMAL_IMPORT_OR_PROOF` ≠ `OPEN-VF-ACTUAL-PRIME` | Formalizing the classical criterion does not touch the open actual-prime estimate. |
<!-- END GENERATED: non-equivalences -->

## 7. Node registry

<!-- BEGIN GENERATED: nodes -->
| ID | Type | Logical | Formal | Evidence | Lean / source | PR | Statement |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `RH` | rh_target | OPEN | LEAN_STATEMENT_ONLY | UNKNOWN | [`VFMidRiemannHypothesisStatement`](../research/VF_MID_VON_KOCH_BRIDGE.lean) |  | Every nontrivial zero of the Riemann zeta function has real part 1/2 (Mathlib `RiemannHypothesis`; repository alias `VFMidRiemannHypothesisStatement`). |
| `HISTORICAL-VONKOCH-1901` | historical_theorem | ESTABLISHED_LITERATURE | EXPLICIT_LEAN_INTERFACE | INDEPENDENTLY_REVIEWED_PAPER_PROOF | [`ClassicalVonKochRHCriterion`](../research/VF_MID_VON_KOCH_BRIDGE.lean) |  | RH <=> pi(x) - Li(x) = O(sqrt(x) log x). von Koch (1901) proved RH => pi(x) = Li(x) + O(sqrt(x) log x); the converse is the classical Mellin/partial-summation argument (an O(x^(1/2+eps)) error continues the relevant Dirichlet series to Re s > 1/2). Li_2(x) = int_2^x dt/log t differs from li(x) by the constant li(2) = 1.04516..., so the criterion is normalization-independent. |
| `IFACE-CLASSICAL-VONKOCH` | explicit_interface | ESTABLISHED_LITERATURE | EXPLICIT_LEAN_INTERFACE | INDEPENDENTLY_REVIEWED_PAPER_PROOF | [`ClassicalVonKochRHCriterion`](../research/VF_MID_VON_KOCH_BRIDGE.lean)<br/>[`PrimeLiVonKochBoundedStatement`](../research/VF_MID_VON_KOCH_BRIDGE.lean) |  | structure ClassicalVonKochRHCriterion where iff_riemannHypothesis : PrimeLiVonKochBoundedStatement <-> VFMidRiemannHypothesisStatement. Supplied as an explicit theorem argument; the repository does not construct it. |
| `CLASSICAL_VONKOCH_CRITERION_FORMAL_IMPORT_OR_PROOF` | formalization_task | ESTABLISHED_LITERATURE | NOT_FORMALIZED | INDEPENDENTLY_REVIEWED_PAPER_PROOF | [`ClassicalVonKochRHCriterion`](../research/VF_MID_VON_KOCH_BRIDGE.lean) |  | Construct a term of ClassicalVonKochRHCriterion, either from an existing certified Lean proof of the classical equivalence or by a new proof in the pinned Lean 4.34.1 / Mathlib toolchain. |
| `MILESTONE-VF-CANONICAL` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`vfCanonical`](../research/VF_CANONICAL_SQRT_TWO.lean)<br/>[`vfCanonical_eq_legacy_plus_sqrt_two`](../research/VF_CANONICAL_SQRT_TWO.lean)<br/>[`vfCanonicalSquareDefect_succ`](../research/VF_CANONICAL_SQRT_TWO.lean)<br/>[`vfCanonicalPrimeLiError_eq_primeError_add_quadrature`](../research/VF_CANONICAL_SQRT_TWO.lean) | [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | vfCanonical x = vfMid x + sqrt 2; for x >= 4, R = floor(sqrt x): VF_can(x) = sqrt2 + sum_{r=2}^{R-1} (2r+1)/log(r^2+r+1/2) + (x-R^2)/log((R^2+x)/2). The square-endpoint defect obeys the exact actual-prime recurrence D_{R+1} = D_R + (P_R - V_R). |
| `MILESTONE-VF-LI-ROOT` | proved_lemma | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`VFMidLiRootBoundedStatement`](../research/VF_MID_VON_KOCH_BRIDGE.lean)<br/>[`vfMidLiRootBounded`](../research/VF_MID_VON_KOCH_BRIDGE.lean) |  | VFMidLiRootBoundedStatement: exists B >= 0, forall x >= 4, \|vfMid(x) - Li_2(x)\| <= B sqrt(x). This is the quadrature input actually used by the von Koch equivalence proofs. |
| `MILESTONE-VF-LI-O1` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`abs_vfMidLiError_le_uniform_allReal`](../research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean)<br/>[`vfMidLiAllRealUniformBounded`](../research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean)<br/>[`abs_vfCanonicalLiError_le_uniform_allReal`](../research/VF_CANONICAL_SQRT_TWO.lean) | [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | exists C, forall real x >= 4: \|VF_can(x) - Li_2(x)\| <= C (and \|vfMid(x) - Li_2(x)\| <= C_square + C_live). Unconditional; elementary uniform midpoint quadrature, no prime-distribution hypothesis. |
| `MILESTONE-VONKOCH-VF-LEAN` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`vfCanonicalSquareVonKoch_iff_primeLiVonKoch`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfCanonicalRealVonKoch_iff_primeLiVonKoch`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfCanonicalSquareVonKoch_iff_realVonKoch`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfCanonicalRealVonKoch_iff_legacy`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfCanonicalSquareVonKoch_iff_legacy`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`vfMidVonKochBounded_iff_primeLiVonKochBounded`](../research/VF_MID_VON_KOCH_BRIDGE.lean)<br/>[`vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded`](../research/VF_MID_VON_KOCH_BRIDGE.lean)<br/>[`vfMidVonKochBounded_of_squareEndpoint`](../research/VF_MID_VON_KOCH_BRIDGE.lean) | [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | (exists C >= 0, forall R >= 2, \|pi(R^2) - VF_can(R^2)\| <= C R log R) <=> (exists C' >= 0, forall real x >= 4, \|pi(x) - Li_2(x)\| <= C' sqrt(x) log x), and both are equivalent to the all-real canonical and legacy vfMid forms, with renormalized nonnegative constants. |
| `OPEN-VF-ACTUAL-PRIME` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | TARGET_EQUIVALENT | [`VFCanonicalSquareVonKochStatement`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | VFCanonicalSquareVonKochStatement: exists C >= 0, forall R >= 2, \|pi(R^2) - VF_can(R^2)\| <= C R log R. |
| `PROP-VF-CAN-REAL-VONKOCH` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | TARGET_EQUIVALENT | [`VFCanonicalRealVonKochStatement`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | VFCanonicalRealVonKochStatement: exists C >= 0, forall real x >= 4, \|pi(x) - VF_can(x)\| <= C sqrt(x) log x. |
| `PROP-VF-MID-SQUARE-VONKOCH` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | TARGET_EQUIVALENT | [`VFMidSquareEndpointVonKochBoundedStatement`](../research/VF_MID_VON_KOCH_BRIDGE.lean) |  | VFMidSquareEndpointVonKochBoundedStatement: exists C >= 0, forall R >= 2, \|pi(R^2) - vfMid(R^2)\| <= C R log R (historical statement, not redefined). |
| `PROP-VF-MID-REAL-VONKOCH` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | TARGET_EQUIVALENT | [`VFMidVonKochBoundedStatement`](../research/VF_MID_VON_KOCH_BRIDGE.lean) |  | VFMidVonKochBoundedStatement: exists C >= 0, forall real x >= 4, \|pi(x) - vfMid(x)\| <= C sqrt(x) log x. |
| `PROP-PRIME-LI-VONKOCH` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | TARGET_EQUIVALENT | [`PrimeLiVonKochBoundedStatement`](../research/VF_MID_VON_KOCH_BRIDGE.lean) |  | PrimeLiVonKochBoundedStatement: exists C >= 0, forall real x >= 4, \|pi(x) - Li_2(x)\| <= C sqrt(x) log x, Li_2(x) = int_2^x dt/log t. |
| `RH-CONDITIONAL-CONSUMER` | conditional_consumer | PROVED | PROVED_IN_LEAN_ON_MAIN | CONDITIONAL | [`riemannHypothesis_of_vfCanonicalSquare`](../research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean)<br/>[`riemannHypothesis_of_vfMidSquareEndpoint`](../research/VF_MID_VON_KOCH_BRIDGE.lean) | [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | riemannHypothesis_of_vfCanonicalSquare (criterion : ClassicalVonKochRHCriterion) (h : VFCanonicalSquareVonKochStatement) : RiemannHypothesis; legacy form riemannHypothesis_of_vfMidSquareEndpoint. |
| `OPEN-VF-LOW` | open_obligation | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | exists K >= 0, R0, forall R >= R0: pi(R^2) - VF_can(R^2) >= -K R log R. |
| `PAPER-VF-LOW-ONE-SIDED` | paper_claim | CLAIMED | NOT_FORMALIZED | PAPER_PROOF_NEEDS_REVIEW | [VF_MID_LOWER_CHANNEL_ALONE_RH_AND_FIRST_BAD_GATE.md](../research/VF_MID_LOWER_CHANNEL_ALONE_RH_AND_FIRST_BAD_GATE.md) | [#925](https://github.com/OVVO-Financial/RH_Lean/pull/925) | Lower wall + square-endpoint O(1) quadrature + monotonicity of pi give pi(x) - li(x) >= -O(sqrt(x) log x) for all real x; with LIT-MV-OMEGA-PM this forces RH. |
| `LIT-MV-OMEGA-PM` | literature_theorem | ESTABLISHED_LITERATURE | NOT_FORMALIZED | INDEPENDENTLY_REVIEWED_PAPER_PROOF |  |  | With Theta = sup Re(rho), for every eps > 0: pi(x) - li(x) = Omega_+-(x^(Theta - eps)). |
| `OPEN-915-SOURCE-PAYMENT` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | UNKNOWN | [`VFMid915FirstBadSourcePaymentStatement`](../research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean)<br/>[`vfMid915FirstBadSourcePayment_iff_radialTwoEnvelope_of_base`](../research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean) | [#915](https://github.com/OVVO-Financial/RH_Lean/pull/915) | VFMid915FirstBadSourcePaymentStatement: forall R >= 8 with first bad successor R+1 at K=2, 2 * Source(R)^2 <= TotalMass(R). Content audit (#939): equivalent to the absence of first-bad successors; with the finite base window, equivalent to \|D_R\| <= 2 R log R for every R >= 2. |
| `FINITE-915-BASE-WINDOW` | finite_evidence | FINITE_EVIDENCE | NOT_FORMALIZED | FINITE_COMPUTATION |  | [#939](https://github.com/OVVO-Financial/RH_Lean/pull/939) | For 2 <= B <= 8, the actual-prime endpoint defect is not bad at K = 2 (hypothesis hbase of the #939 consumers). |
| `CONSUMER-915-CANONICAL` | conditional_consumer | PROVED | PROVED_IN_LEAN_ON_MAIN | CONDITIONAL | [`vfCanonicalSquareVonKoch_of_915SourcePayment_and_base`](../research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean)<br/>[`vfMid915FirstBadSourcePayment_iff_noFirstBad`](../research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean)<br/>[`vfMid915FirstBad_closed_of_sourcePayment`](../research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean) | [#939](https://github.com/OVVO-Financial/RH_Lean/pull/939) | vfCanonicalSquareVonKoch_of_915SourcePayment_and_base (hbase) (hpay) : VFCanonicalSquareVonKochStatement; also vfMid915FirstBad_closed_of_sourcePayment (payment forbids every first-bad successor). |
| `MILESTONE-915-MOVING-OWNER` | proved_lemma | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`vfMid915HistoricalMovingOwner_eq_signedMismatch`](../research/VF_MID_915_FLOOR_LI_TRANSPORT_BOUNDARY.lean) |  | For 2 <= A <= B: vfMid915HistoricalMovingOwnerCorrection A B = -(signed floor-Li population balance on [A^2, B^2)). Aggregate (zeroth-moment) identity only. |
| `MECH-VF-LOW-FIRST-LOWER-ESCAPE` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | A legitimate original-source lower-wall restriction or first-bad contradiction retaining all original prime occurrences, VF weights, historical anchors, returning cells, restored terms and signed NNS interactions. |
| `MECH-SAT-OWNER-REMOVAL` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | A new uniform signed least-prime owner-removal or cofactor/prime-innovation inequality on the genuine prime/composite incidence S = A - T, with complete original source coefficients and nonlocal historical contributions; must use arithmetic restrictions on genuine prime locations, not population counts. |
| `MILESTONE-1019-BIRTH-TRANSPORT` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`closedSquareShell_birthTime_floor_eq_two_mu_sub_mu_sq`](../research/VF_MID_CLOSED_SQUARE_BIRTH_TIME_20261024.lean)<br/>[`closedSquareShellFloor_eq_open_add_rootDivisor`](../research/VF_MID_CLOSED_SQUARE_BIRTH_TIME_20261024.lean)<br/>[`closedSquareShell_actual_moving_transport_telescope`](../research/VF_MID_CLOSED_SQUARE_MOVING_TRANSPORT_20261024.lean) | [#1019](https://github.com/OVVO-Financial/RH_Lean/pull/1019) | Exact closed-square prefix drift, birth bill 2 mu(k) - mu(k)^2, and the physical moving-complement transport telescope. |
| `OPEN-JOH-SIGN` | open_obligation | OPEN | NOT_FORMALIZED | UNKNOWN | [LI_FAN_ONE_SIDED_WEIGHTED_COMPOSITE_RH_CONTRACT_20261022.md](../research/LI_FAN_ONE_SIDED_WEIGHTED_COMPOSITE_RH_CONTRACT_20261022.md) | [#1012](https://github.com/OVVO-Financial/RH_Lean/pull/1012) | exists R0, forall R >= R0: G(R^2) < 0, where Q(n) = floor(Li_2(n)), G(N) = sum_{2<=n<N} (pi(n) - Q(n) - 1) = A(N) - T(N) - L(N); equivalently T(R^2) > A(R^2) - L(R^2). |
| `LIT-JOHNSTON-2022` | literature_theorem | ESTABLISHED_LITERATURE | NOT_FORMALIZED | INDEPENDENTLY_REVIEWED_PAPER_PROOF |  |  | RH <=> int_2^X (pi(t) - li(t)) dt < 0 for all real X > 2, with quantitative forms (Section 3 eqs (3.4)-(3.6); Theorem 1.4, Lemma 2.8). |
| `PAPER-JOH-SQUARE-TRANSFER` | paper_claim | CLAIMED | NOT_FORMALIZED | PAPER_PROOF_NEEDS_REVIEW | [LI_FAN_ONE_SIDED_WEIGHTED_COMPOSITE_RH_CONTRACT_20261022.md](../research/LI_FAN_ONE_SIDED_WEIGHTED_COMPOSITE_RH_CONTRACT_20261022.md) | [#1012](https://github.com/OVVO-Financial/RH_Lean/pull/1012) | Using Johnston's quantitative estimates: RH <=> exists R0 forall R >= R0, G(R^2) < 0. |
| `CLAIM-20261024-OWNER-1` | paper_claim | CLAIMED | NOT_FORMALIZED | PAPER_PROOF_NEEDS_REVIEW |  |  | With eta(k) = 1_prime(k) - (Q(k) - Q(k-1)) and J_r = sum_{r^2<k<(r+1)^2} ((r+1)^2 - k) eta(k): sum_{r^2<=n<(r+1)^2} E(n) = (2r+1)(P_r - 1) + J_r and G(B^2) - G(A^2) = (B^2 - A^2)(P_A - 1) - sum_{j=A}^{B-1} (B^2 - (j+1)^2) D_j + sum_{r=A}^{B-1} J_r. The #915 boundary carries the zeroth moment; JOH needs the first moment. |
| `MECH-JOH-ANCESTRY-DISPLACEMENT` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | A genuine least-prime-ancestry restriction on the boundary-padded displacement pairs J_r, stronger than the trivial total-distance bound, surviving the opposite-sign blocks r = 4, 7, and combining with the anchor and weighted block defects without assuming eventual G < 0. |
| `REFUTED-JOH-COUNT-ONLY` | refuted_claim | REFUTED | NOT_FORMALIZED | REFUTED |  |  | Conjecture (refuted): the JOH first-moment contribution of a square block is determined by its zero-th moment count defect D_r, or J_r has a universal sign. |
| `CE-JOH-R4-R7` | counterexample | PROVED | NOT_FORMALIZED | FINITE_COMPUTATION |  |  | r=4: primes {17,19,23}, floor-Li arrivals {18,21,24}, D_4 = 0, J_4 = +4. r=7: primes {53,59,61}, floor-Li arrivals {53,57,61}, D_7 = 0, J_7 = -2. Every Li_2 value used is >= 0.06 from an integer. |
| `PROP-MERTENS-ENERGY` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | TARGET_EQUIVALENT | [`MertensEnergyBoundedStatement`](../RHLean/Analysis/SquarePrefixMertensBridge.lean) |  | MertensEnergyBoundedStatement: forall eps > 0, exists C >= 0, forall x: \|M(x)\|^2 <= C (x+1)^(1+eps). Via M(N)^2 = D(N) + 2C(N) this is literally the RH-strength CODIV target D + 2C = O(N^(1+eps)). |
| `CONSUMER-MERTENS-ENERGY-RH` | conditional_consumer | PROVED | PROVED_IN_LEAN_ON_MAIN | CONDITIONAL | [`riemannHypothesis_of_mertensEnergy`](../RHLean/Analysis/MertensEnergyRHForward.lean)<br/>[`riemannZeta_ne_zero_of_half_lt_re`](../RHLean/Analysis/MertensEnergyRHForward.lean) |  | riemannHypothesis_of_mertensEnergy (hM : MertensEnergyBoundedStatement) : RiemannHypothesis. No classical interface argument: the zeta/Mertens Mellin continuation is proved in the RHLean library. |
| `MILESTONE-MERTENS-CONVERSE` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`growthAtMost_iff_strip`](../research/MERTENS_CONVERSE_IDENTIFICATION.lean)<br/>[`growthExponent_eq_rightmost`](../research/MERTENS_CONVERSE_IDENTIFICATION.lean)<br/>[`logLimsup_eq_rightmost`](../research/MERTENS_CONVERSE_IDENTIFICATION.lean) | [#949](https://github.com/OVVO-Financial/RH_Lean/pull/949) | growthAtMost_iff_strip, growthExponent_eq_rightmost, logLimsup_eq_rightmost: the Mertens growth exponent equals the rightmost real part of nontrivial zeta zeros. |
| `MILESTONE-MERTENS-SIGNED-LIFT` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`heathBrownLift_agrees_below_power`](../research/MERTENS_HEATH_BROWN_SIGNED.lean) | [#954](https://github.com/OVVO-Financial/RH_Lean/pull/954) | heathBrownLift_agrees_below_power: a genuine Mobius prefix below B reconstructs coefficients below B^k (every integral k), with exact signed geometric/defect formulas. |
| `MILESTONE-COVARIANCE-IDENTITY` | proved_lemma | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal`](../RHLean/Analysis/MertensCovarianceDescent.lean) |  | realMertensPositiveLagPairSum_eq_norm_sq_sub_diagonal: the genuine positive-lag pair sum equals (\|M\|^2 - sum mu^2)/2, i.e. M(X)^2 = sum mu(n)^2 + 2 sum_{a<b} mu(a) mu(b). |
| `MILESTONE-958-ODD-RESIDUAL` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`nine_mul_canonicalLargestPrimeFactor_lt_sq`](../RHLean/Proof/OddResidualCofactorSupport.lean) | [#958](https://github.com/OVVO-Financial/RH_Lean/pull/958) | 1 < m, Odd(canonicalCofactor m), IsOddFactorDepthResidual m, m < R^2 ==> 9 * canonicalLargestPrimeFactor m < R^2. |
| `MILESTONE-961-COMPLETE-FIBRE` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`completeFibre_of_root_le`](../RHLean/Proof/RootWallCompleteFibre.lean)<br/>[`largestPrimeFactor_eq_iff_exists_mul_of_root_le`](../RHLean/Proof/RootWallCompleteFibre.lean) | [#961](https://github.com/OVVO-Financial/RH_Lean/pull/961) | For prime q >= R: the greatest-prime fibre below R^2 is complete, with multiplier a < q, non-square property and explicit odd-residual characterization. |
| `IMPORTED-OAI-7-8` | imported_theorem | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`openai434_actual_zeta_nonzero`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean)<br/>[`openai434_actual_global_signed_covariance`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean)<br/>[`openai434_actual_global_signed_pairs`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean)<br/>[`openai434_actual_all_square_blocks_seven_eighths`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean)<br/>[`openai434_actual_all_square_block_covariance`](../research/VF_919_OPENAI_434_UNCONDITIONAL_SQUARE_BLOCK_COVARIANCE_20261019.lean) | [#987](https://github.com/OVVO-Financial/RH_Lean/pull/987) | zeta(s) != 0 for Re s > 7/8, hence M(x) = O_eps(x^(7/8+eps)), the global signed covariance bound and the all-square-block 7/8 bound on the original RH_Lean carriers. |
| `MILESTONE-MERTENS-STRICT-EXPLICIT` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`native_beta_le_explicit_slot_count_total_mass`](../research/oai_434/VF919ExplicitSlotTotalMass.lean)<br/>[`native_mertens_explicit_slot_count_total_mass`](../research/oai_434/VF919ExplicitSlotTotalMass.lean) | [#1108](https://github.com/OVVO-Financial/RH_Lean/pull/1108) | Let N_* = explicitSlotCount > 0, fixed independently of x. The original Hecke zero boundary is <= 7/8-1/(48N_*); for every eps>0 there exists C_eps for all n>=1: \|M(n)\| <= C_eps*n^(7/8-1/(48N_*)+eps). This discharges the earlier intermediate open target below 7/8, not RH. |
| `MECH-CODIV-SIGNED-COVARIANCE` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | A nontrivial uniform source estimate for the full signed covariance C(N) = sum_{a<b<=N} mu(a) mu(b), with diagonal and off-diagonal terms retained, giving C(N) <= -D(N)/2 + O(N^(7/4 - 2 delta + eps)). |
| `MECH-SIGNED-QUOTIENT-VARIATION` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN | [`vfVarSquareMertens_norm_le_four_lowVariation_add_two_shortMass`](../research/VF_QUOTIENT_VARIATION_FIRSTBAD_ATTACK.lean) | [#923](https://github.com/OVVO-Financial/RH_Lean/pull/923) | A uniform bound V_low(X) = sum_{t<=sqrt X} \|D_X(t)\| = O(X^(7/8 - delta + eps)); with the compiled signed Abel theorem \|M(X)\| <= 4(V_low + V_high) and V_high <= 2 sqrt X (paper), this pays an exponent gain. |
| `MECH-OAI-NNS-COMPLETE-LEDGER` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | Gates: (1) source admission of every compensated component; (2) conductor and physical normalization; (3) low-J, resonant and unit-trivial rows; (4) principal and Gaussian-tail costs; (5) true multiplicity and incomplete sextic moments; (6) compensation subsets, collisions and outer sums; (7) full signed cross-energy and NNS Co/Div restoration; (8) a complete exponent budget with strictly positive net saving delta. |
| `MILESTONE-OAI-HEAVY-SLOT` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`Fiber.exists_heavy_slot`](../research/oai_434/VF919OriginalFiberHeavySlotSplit.lean)<br/>[`Fiber.exists_heavy_slot_with_two_channel_sum`](../research/oai_434/VF919OriginalFiberHeavySlotSplit.lean) | [#1017](https://github.com/OVVO-Financial/RH_Lean/pull/1017) | Fiber.exists_heavy_slot_with_two_channel_sum: every original fiber has a heavy slot and an exact two-channel powerset decomposition. |
| `PR1022-ZERO-MODE` | proved_lemma | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`bareCongruenceCoefficient_zero_mode_of_nontrivial`](../research/oai_434/VF919OriginalLowNonresonantZeroMode.lean)<br/>[`actualCongruenceCoefficient_zero_mode_of_nontrivial`](../research/oai_434/VF919OriginalLowNonresonantZeroMode.lean) | [#1022](https://github.com/OVVO-Financial/RH_Lean/pull/1022) | actualCongruenceCoefficient_zero_mode_of_nontrivial: every source component admitting a coprime multiplier with nontrivial residual sextic phase has an exact zero Fourier mode on the original calibrated numerator. |
| `CLAIM-1022-POISSON-SAVING` | paper_claim | CLAIMED | NOT_FORMALIZED | PAPER_PROOF_NEEDS_REVIEW |  | [#1022](https://github.com/OVVO-Financial/RH_Lean/pull/1022) | In the nonprincipal short-radical band Z^(21/64) <= N(J) <= Z^(1/3), N(I) N(J)^3 <= Z^(1+1/384), X = Z^(17/48), Y = Z^(23/48): F/Q_s <= Z^(-1/128) and, after exact zero-mode elimination, radial Poisson gives a source-local Z^(-1/64) factor before outer costs. |
| `OPEN-FINITE-AC` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | UNKNOWN | [`SquareRootMertensEndpointAmplificationStatement`](../RHLean/Proof/SquareRootMertensEndpointAmplification.lean) | [#929](https://github.com/OVVO-Financial/RH_Lean/pull/929) | SquareRootMertensEndpointAmplificationStatement: exists A >= 0, forall R >= 2, forall K with LowerMertensCriticalEnvelope R K: (M(R^2-1) - 1)^2 <= A R^2 K. Equivalent as an existence claim to finite C: exists C, forall R >= 2, \|Q_R\| <= C R sqrt(K_R), Q_R = 2M(R-1) - M(R^2-1), K_R = max_{0<=y<R} (M(y)-1)^2/(y+1) (elementary: K >= 1 and \|M(R-1) - 1\| <= sqrt(K R)). |
| `PROP-LEGAL-ANCESTRY-GRAM` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | UNKNOWN | [`SquareRootLegalAncestryGramAmplificationStatement`](../RHLean/Proof/SquareRootLegalAncestryGramReduction.lean) |  | SquareRootLegalAncestryGramAmplificationStatement: the genuine legal live-packet Gram Gamma_R satisfies the historical-envelope bound Gamma_R <= B R^2 K_R (with changed constants); existential equivalence with finite A on this normalized carrier only. |
| `THM-FINITE-A-IFF-LEGAL-GRAM` | proved_lemma | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`squareRootMertensEndpointAmplification_iff_legalAncestryGram`](../RHLean/Proof/SquareRootMertensEndpointAmplification.lean) |  | squareRootMertensEndpointAmplification_iff_legalAncestryGram. |
| `CONSUMER-FINITE-A-MERTENS` | conditional_consumer | PROVED | PROVED_IN_LEAN_ON_MAIN | CONDITIONAL | [`mertensEnergyBounded_of_squareRootEndpointAmplification`](../RHLean/Proof/SquareRootAmplificationClosure.lean) |  | mertensEnergyBounded_of_squareRootEndpointAmplification (hamp) : MertensEnergyBoundedStatement. |
| `MECH-FINITE-AC-HISTORICAL-ENVELOPE` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | A genuine all-root signed upper estimate for Q_R (or Gamma_R) with the historical denominator R^2 K_R intact. |
| `NOGO-FINITE-A-HURST` | no_go | CLAIMED | NOT_FORMALIZED | PAPER_PROOF_NEEDS_REVIEW | [ABSOLUTE_A_ALL_SCALE_SIGNED_ESTIMATE_AUDIT.md](../research/ABSOLUTE_A_ALL_SCALE_SIGNED_ESTIMATE_AUDIT.md) | [#926](https://github.com/OVVO-Financial/RH_Lean/pull/926) | Using Hurst's unconditional theorem and the actual Mertens state: any uniform A in the finite-A statement satisfies A > 0.4357. |
| `OPEN-CORR4` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | UNKNOWN | [`CanonicalRoughCorrelationFourQ2EnergyStatement`](../research/CORRELATION_FOUR_TERMINAL_BRIDGE.lean)<br/>[`CanonicalRoughCorrelationQ2EnergyStatementWith`](../research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean) |  | CanonicalRoughCorrelationFourQ2EnergyStatement: exists C >= 0 such that for every R >= 56 and every LowerMertensCriticalEnvelope R K: \|\|squareRootCanonicalRoughCorrelation R\|\|^2 <= 4 * farFourOddQ2DaughterEnergy R + C R^2 K. |
| `CONSUMER-CORR4-FINITE-A` | conditional_consumer | PROVED | PROVED_IN_LEAN_ON_MAIN | CONDITIONAL | [`correlationFour_implies_rawQ2_10201_over_2500`](../research/CORRELATION_FOUR_TERMINAL_BRIDGE.lean)<br/>[`riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy`](../research/CORRELATION_FOUR_TERMINAL_BRIDGE.lean)<br/>[`corrFour_10201_over_2500_is_subcritical`](../research/CORRELATION_FOUR_TERMINAL_BRIDGE.lean)<br/>[`squareEndpointRawOddQ2EnergyStepWith_implies_endpointAmplification`](../RHLean/Proof/PhysicalQ2ExceptionalTerminalSynthesis.lean) |  | correlationFour_implies_rawQ2_10201_over_2500 then squareEndpointRawOddQ2EnergyStepWith_implies_endpointAmplification (subcritical 10201/2500 * 37/36 * 17/72 < 1); composite terminal theorem riemannHypothesis_of_canonicalRoughCorrelationFourQ2Energy. |
| `OPEN-CORR4-RELAXED-REMAINDER` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | UNKNOWN | [`LowOwnerPhysicalRelaxedRemainderBound`](../research/CORR4_OAI_RELAXED_REMAINDER_20261024.lean) | [#1021](https://github.com/OVVO-Financial/RH_Lean/pull/1021) | LowOwnerPhysicalRelaxedRemainderBound: exists C >= 0, forall R >= 56 and every LowerMertensCriticalEnvelope R K: \|B_R\|^2 <= (9/4) E_R + C R^2 K, where X_R = R^2 - 1, C_R = M(R-1) - M(X_R), U_R = sum_{q odd prime, q^2<R} M(floor(X_R/q^2))/q, E_R = sum_{q odd prime, q^2<R} M(floor(X_R/q^2))^2, B_R = C_R - U_R. Equivalently 2 Gamma_R <= (9/4) E_R + C R^2 K - D_R on the first-owner Gram \|B_R\|^2 = D_R + 2 Gamma_R. |
| `PR1021-RELAXED-CONSUMER` | conditional_consumer | PROVED | PROVED_IN_LEAN_ON_MAIN | CONDITIONAL | [`correlationFour_of_relaxedPhysicalRemainder`](../research/CORR4_OAI_RELAXED_REMAINDER_20261024.lean)<br/>[`riemannHypothesis_of_relaxedPhysicalRemainder`](../research/CORR4_OAI_RELAXED_REMAINDER_20261024.lean) | [#1021](https://github.com/OVVO-Financial/RH_Lean/pull/1021) | correlationFour_of_relaxedPhysicalRemainder (hC : 0 <= C) (h : LowOwnerPhysicalRelaxedRemainderBound C) proves the coefficient-4 CORR-4 input; riemannHypothesis_of_relaxedPhysicalRemainder composes it with the established terminal consumer. The 886/225 coefficient uses the proven 211/900 low daughter frame; #1023 separately sharpens the odd-prime reciprocal frame. The h premise remains OPEN. |
| `PR1023-FRAME-B7` | proved_lemma | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`oddPrimeOwnerReciprocalSquareBudget_le_compositeGap`](../research/ODD_PRIME_COMPOSITE_GAP_BASEL_20261025.lean)<br/>[`stableFarCriticalQ2OddPrimeSynthesis_energy_le_compositeGap`](../research/ODD_PRIME_COMPOSITE_GAP_BASEL_20261025.lean)<br/>[`compositeGapBudget_lt_twoTermBasel`](../research/ODD_PRIME_COMPOSITE_GAP_BASEL_20261025.lean) | [#1023](https://github.com/OVVO-Financial/RH_Lean/pull/1023) | forall N: sum_{q <= N, q odd prime} 1/q^2 <= 1565172113/7214407200 (= 0.21695...), hence \|U_R\|^2 <= b_7 E_R on the CORR-4 carrier; strictly below 211/900. |
| `NOGO-CORR4-FRAME-ONLY` | no_go | CLAIMED | NOT_FORMALIZED | PAPER_PROOF_NEEDS_REVIEW |  |  | With a = 9/4: \|B_R\|^2 - a E_R <= lambda_7 \|C_R\|^2, lambda_7 = a/(a - b_7) = 16232416200/14667244087 = 1.10671...; sharp for the unsigned frame alone. If H_R = (\|B_R\|^2 - a E_R)/(R^2 K) > 0 then sqrt(A_R) >= sqrt(kappa_7 H_R) - 1/sqrt(R), A_R = (M(X_R) - 1)^2/(R^2 K), kappa_7 = 14667244087/16232416200. |
| `MECH-CORR4-SIGNED-FIRST-OWNER-GRAM` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | An all-root sign-preserving restriction on the complete first-owner Gram Gamma_R showing that genuine incidence excludes near-saturation of the antiparallel parent/daughter frame extremizer on large finite-A endpoint excursions. |
| `FINITE-CORR4-CENSUS` | finite_evidence | FINITE_EVIDENCE | NOT_FORMALIZED | FINITE_COMPUTATION |  | [#1021](https://github.com/OVVO-Financial/RH_Lean/pull/1021) | Exact census 56 <= R <= 6000 (Census 20261025-census-1) and Numba sweep R <= 10000 (#1021): max observed c_R = (\|B_R\|^2 - (9/4)E_R)/(R^2 K_R) is 0.14418310472084428 at R = 5561 (M(X) = -2544, K = 3/2); all 58 roots with c_R > 1/10 (R <= 6000) are square-endpoint excursions with C_R U_R < 0. |
| `REFUTED-CORR4-C-012` | refuted_claim | REFUTED | NOT_FORMALIZED | REFUTED |  |  | Conjecture (refuted): the relaxed remainder bound holds with C <= 0.12 for all R >= 56. |
| `CE-CORR4-R5561` | counterexample | PROVED | NOT_FORMALIZED | FINITE_COMPUTATION |  |  | R = 5561: X = 30924720, M(X) = -2544, C_R = 2549, E_R = 196306, K = 3/2, c_R = 0.14418310472084428 (exact rational certificate in the Census report). |
| `REFUTED-CORR4-LOCAL-SIGN` | refuted_claim | REFUTED | NOT_FORMALIZED | REFUTED |  |  | Conjecture (refuted): every root with positive boundary payment c_R > 0 has anti-aligned parent and daughter synthesis, C_R U_R < 0. |
| `CE-CORR4-R57` | counterexample | PROVED | NOT_FORMALIZED | FINITE_COMPUTATION |  |  | R = 57: X = 3248, C_R = -19, U_R = -71/105, E_R = 3, K = 3/2, c_57 = 14509429/214921350 > 0 and C_R U_R > 0. |
| `REFUTED-CORR4-DAUGHTER-ONLY` | refuted_claim | REFUTED | NOT_FORMALIZED | REFUTED |  |  | Conjecture (refuted): \|B_R\|^2 <= (9/4) E_R for all R >= 56 (the historical R^2 K term can be dropped). |
| `CE-CORR4-R56` | counterexample | PROVED | NOT_FORMALIZED | FINITE_COMPUTATION |  |  | R = 56: \|B_56\|^2 > (9/4) E_56 (c_56 > 0), the first root of the domain; 3,577 of the 5,945 roots 56..6000 have c_R > 0. |
| `OPEN-MU-LIFT` | open_obligation | OPEN | NOT_FORMALIZED | UNKNOWN | [MERTENS_AMPLIFICATION_BUDGET.md](../docs/MERTENS_AMPLIFICATION_BUDGET.md) |  | For a fixed k >= 2 and fixed r < k: E(B^k) <= G(B) E(B)^r with E(B) = max_{1<=n<B} \|M(n)\|/sqrt(n), log G(B)/log B -> 0, on a chain with complete interval coverage. |
| `PAPER-MU-LIFT-CONTRACTION` | paper_claim | CLAIMED | NOT_FORMALIZED | PAPER_PROOF_NEEDS_REVIEW | [MERTENS_AMPLIFICATION_BUDGET.md](../docs/MERTENS_AMPLIFICATION_BUDGET.md) |  | u_{j+1} <= (r/k) u_j + g_j/k with u_j = log E(B_j)/log B_j and g_j -> 0 forces u_j -> 0; full-prefix interpolation gives \|M(n)\| <= n^(1/2+o(1)). |
| `MECH-MU-LIFT-SUBCRITICAL` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | A genuinely new signed estimate on the exact K1/K2/K3 floor kernel (Type II corner plus every complementary range, square/floor boundaries and full-prefix coverage) yielding a fixed subcritical r < k. |
| `OPEN-NYMAN-DENSITY` | open_obligation | OPEN | NOT_FORMALIZED | UNKNOWN | [NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md](../research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md) | [#957](https://github.com/OVVO-Financial/RH_Lean/pull/957) | d_N -> 0 for the full integer-dilation (Baez-Duarte) basis distance at the critical a = 1/2, or an independently justified weighted a > 1/2 zero-free consequence. |
| `LIT-BAEZ-DUARTE` | literature_theorem | ESTABLISHED_LITERATURE | NOT_FORMALIZED | INDEPENDENTLY_REVIEWED_PAPER_PROOF |  |  | RH <=> the integer-dilation Nyman-Beurling distance d_N tends to 0. |
| `LIT-BURNOL-2002` | literature_theorem | ESTABLISHED_LITERATURE | NOT_FORMALIZED | INDEPENDENTLY_REVIEWED_PAPER_PROOF |  |  | Unconditionally, the Nyman-Beurling distance satisfies a positive lower bound of order 1/log N, which applies to the centered integer-modulus span. |
| `REFUTED-NYMAN-SQUARE-CONTRACTION` | refuted_claim | REFUTED | NOT_FORMALIZED | REFUTED |  |  | Conjecture (refuted): for some fixed q < 1/2, eventually d_{B^2}^2 <= q d_B^2. |
| `MECH-NYMAN-FULL-BASIS-DECAY` | arithmetic_mechanism | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | A proved (possibly slow) all-scale decay of d_(N,a) for the full basis, not monotonicity, finite Gram fits or finite rational certificates. |
| `REFUTED-BLOCK-UNIVERSAL` | refuted_claim | REFUTED | LEAN_STATEMENT_ONLY | REFUTED | [`VFMidIntegerBlockCrossingStatement`](../research/VF_MID_LITERAL_BLOCK_CROSSING.lean) |  | VFMidIntegerBlockCrossingStatement / capture: forall R >= 2, pi(R^2) <= floor(F_R) <= pi((R+1)^2). FALSE. |
| `CE-BLOCK-R549` | counterexample | PROVED | NOT_FORMALIZED | FINITE_COMPUTATION |  |  | pi(549^2) = 26112, floor(F_549) = 26194, pi(550^2) = 26193; canonical floor(F_549 + sqrt2) = 26196 also fails. |
| `CONSUMER-BLOCK-RH` | conditional_consumer | PROVED | PROVED_IN_LEAN_ON_MAIN | CONDITIONAL | [`riemannHypothesis_of_vfMidIntegerBlockCrossing`](../research/VF_MID_LITERAL_BLOCK_CROSSING.lean)<br/>[`vfMidIntegerBlockCrossingStatement_iff_captureStatement`](../research/VF_MID_LITERAL_BLOCK_CROSSING.lean) |  | riemannHypothesis_of_vfMidIntegerBlockCrossing (criterion : ClassicalVonKochRHCriterion) (hcross : VFMidIntegerBlockCrossingStatement) : RiemannHypothesis. |
| `CARRIER-PRIME-MODEL-EVENTS` | carrier | DEFINITION | LEAN_DEFINITION_ON_MAIN | — | [`vfMidFloorLiPrimitiveMismatch`](../research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean) |  | eta(k) = 1_prime(k) - (Q(k) - Q(k-1)), Q = floor(Li_2), in {-1, 0, 1}. |
| `CARRIER-915-ZEROTH-MOMENT` | carrier | DEFINITION | LEAN_DEFINITION_ON_MAIN | — | [`vfMidFloorLiBlockPrimeDefect`](../research/VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean) |  | D_r = Q((r+1)^2) - Q(r^2) - (pi((r+1)^2) - pi(r^2)); aggregate history telescopes to endpoints. |
| `CARRIER-JOH-FIRST-MOMENT` | carrier | DEFINITION | NOT_FORMALIZED | — |  |  | G(N) = sum_{2<=n<N} (pi(n) - Q(n) - 1) = sum_k (N - k) eta(k) + boundary; = A(N) - T(N) - L(N). |
| `CARRIER-915-WEIGHTED-SOURCE` | carrier | DEFINITION | LEAN_DEFINITION_ON_MAIN | — | [`VFMid915FirstBadSourcePaymentStatement`](../research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean) |  | Source(R) = D_raw(R+1), TotalMass(R) = (\|D_raw(R)\| + beta_R)^2 with native VF weights m_R, w_R, active/returned masks, clipping, historical anchors, restoration and zero-target NNS denominators. |
| `CARRIER-SAT-MERTENS` | carrier | DEFINITION | NOT_FORMALIZED | — |  |  | M(R^2 - 1) = A_mu(R) - T_mu(R): smooth Mobius mass minus high-prime cofactor transport. |
| `CARRIER-SAT-PRIME` | carrier | DEFINITION | NOT_FORMALIZED | — |  |  | Square-block least-prime candidate count minus least-prime-owned composite removals (P_R = R - C_R). |
| `CARRIER-OAI-IDEAL-SOURCE` | carrier | DEFINITION | NOT_FORMALIZED | — |  |  | Ideal-labelled Gaussian/Hecke source with marked-minus-rescaled compensation and split/inert labels (research/oai_434). |
| `CARRIER-CORR4-PHYSICAL-REMAINDER` | carrier | DEFINITION | NOT_FORMALIZED | — |  |  | B_R = C_R - U_R on X_R = R^2 - 1 with the actual weight omega_R(n) = 1_{R<=n<=X_R} + sum_{q in S_R} (1/q) 1_{n<=Y_q}. |
| `MILESTONE-CORR4-POWER-IFF` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`corr4PowerFirstOwnerGram_iff_mertensPowerBound`](../research/CORR4_OAI_POWER_DETERMINISTIC_FRAME_20261025.lean)<br/>[`corr4_low_daughter_energy_of_prefix_power`](../research/CORR4_OAI_POWER_DETERMINISTIC_FRAME_20261025.lean)<br/>[`corr4_power_buffer_for_H`](../research/CORR4_OAI_POWER_DETERMINISTIC_FRAME_20261025.lean) | [#1021](https://github.com/OVVO-Financial/RH_Lean/pull/1021) | forall real beta >= 1/2: (exists A >= 0, Corr4PowerFirstOwnerGram A beta) <=> MertensPowerBound beta. The merged Lean reverse and forward proof uses the original q^2 daughter frame (211/900), all-integer square-shell buffer, and the constant 1000(A+1). This is an unconditional proof OF AN EQUIVALENCE BETWEEN ARITHMETIC ASSERTIONS; neither side is independently established at beta < 7/8. |
| `OPEN-CORR4-MIXED-TAIL-POWER` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | UNKNOWN | [`Corr4PowerMixedTailBill`](../research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean) | [#1021](https://github.com/OVVO-Financial/RH_Lean/pull/1021) | exists real eta,A with 0 < eta <= 3/2 and 0 <= A such that for every integer R >= 56: 2 * lowOwnerPrefixTailMixedRawCellMass R <= 2 * canonicalRoughLowQ2DaughterEnergy R + A * R^(7/2 - eta), on the FULL signed original first-owner carrier. Here beta = 7/8 - eta/4 and this is Corr4PowerMixedTailBill A beta. No proof of this estimate exists in #1021. |
| `CONSUMER-CORR4-MIXED-TAIL-POWER-IMPROVEMENT` | conditional_consumer | PROVED | PROVED_IN_LEAN_ON_MAIN | CONDITIONAL | [`mertensSevenEighthsImprovement_of_corr4MixedTailPowerSaving`](../research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean)<br/>[`mertensPowerBound_of_corr4MixedTailBill`](../research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean)<br/>[`corr4PowerFirstOwnerGram_of_mixedTailBill`](../research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean) | [#1021](https://github.com/OVVO-Financial/RH_Lean/pull/1021) | For 0 < eta <= 3/2 and A >= 0, a full signed mixed-tail bill 2 Gamma_mixed <= 2 E_R + A R^(7/2-eta) yields MertensPowerBound (7/8 - eta/4) by mertensSevenEighthsImprovement_of_corr4MixedTailPowerSaving, using the merged Gram/Mertens biconditional. This is a PROVED CONDITIONAL implication, not an unconditional improvement. |
| `MILESTONE-PRIME-ADMISSION-LOG` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`eulerAdmissibleLogReturn_eq_endpoint`](../research/PRIME_ADMISSION_LOG_AMPLIFICATION_20261107.lean)<br/>[`squareRootAmplificationLogRatio_le_iff_primeAdmissionLogReturn`](../research/PRIME_ADMISSION_LOG_AMPLIFICATION_20261107.lean) | [#1106](https://github.com/OVVO-Financial/RH_Lean/pull/1106) | Exact Euler prime-admission telescope with original M(R^2-1)-1, denominator R^2 K_R, inclusive p=R, initial smooth population and all signed mixed terms. The finite-cutoff q(X) upper bound is equivalent to a uniform inequality for these actual logarithmic returns; q(X)->0 is not proved. |
| `MILESTONE-OAI-TOTAL-MASS` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`native_beta_le_true_physical_slot_minimum_total_mass`](../research/oai_434/VF919TotalMassEndpoint.lean)<br/>[`native_mertens_true_physical_slot_minimum_total_mass`](../research/oai_434/VF919TotalMassEndpoint.lean) | [#1107](https://github.com/OVVO-Financial/RH_Lean/pull/1107) | On the same actual finite source, the complete LOW/HIGH/principal comparison retains complementary tuple mass and proves beta <= 7/8-actualSlotMinimum(D)/4; all source masks, signed pairs and fixed source uniformity survive. |
| `MILESTONE-EXPLICIT-AMPLIFICATION` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`native_amplification_fixed_explicit_slot_count_total_mass`](../research/oai_434/VF919ExplicitAmplificationBound.lean)<br/>[`native_amplification_limsup_explicit_slot_count_total_mass`](../research/oai_434/VF919ExplicitAmplificationBound.lean)<br/>[`native_amplification_eventually_lt_cutoff`](../research/oai_434/VF919ExplicitAmplificationBound.lean) | [#1108](https://github.com/OVVO-Financial/RH_Lean/pull/1108) | With N_*=explicitSlotCount fixed, exists C>0 for all integer X>=1: A(X)<=C*X^(3/4-1/(48N_*)); limsup_{X->infinity} log(1+A(X))/log X <= 3/4-1/(24N_*) and A(X)<X eventually. The exact historical K_R is retained (with K_R>=1 used for this coarse transfer). |
| `MILESTONE-CORR4-CUTOFF-COLLISIONS` | formalization_milestone | PROVED | PROVED_IN_LEAN_ON_MAIN | PROVED_IN_LEAN_ON_MAIN | [`corr4_offRay_sum_le_twice_image`](../research/CORR4_CUTOFF_COLLISIONS_20261108.lean)<br/>[`corr4_offRay_mertens_energy_le_twice_image`](../research/CORR4_CUTOFF_COLLISIONS_20261108.lean) | [#1109](https://github.com/OVVO-Financial/RH_Lean/pull/1109) | For actual off-ray events with q,r<=Q and roots >=H, Q^3<=2H gives equal-cutoff injectivity; Q^3<=4H permits at most two occurrences after parity splitting. The actual nonnegative Mertens occurrence energy is <= twice its distinct-image energy. Does not bound that image energy or the complete signed mixed tail. |
| `MILESTONE-NEAR-UNIFORM-SLOT-BOUNDARY` | formalization_milestone | PROVED | PROVED_IN_LEAN_PR_GREEN_UNMERGED | PROVED_IN_LEAN_PR_GREEN_UNMERGED | [`native_beta_le_near_uniform_slots`](https://github.com/OVVO-Financial/RH_Lean/blob/20875a55dd9780993c4cdc06624c88be6060e2ee/research/oai_434/VF919ExplicitSquareBlockPacking.lean)<br/>[`native_mertens_near_uniform_slots`](https://github.com/OVVO-Financial/RH_Lean/blob/20875a55dd9780993c4cdc06624c88be6060e2ee/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | [#1111](https://github.com/OVVO-Financial/RH_Lean/pull/1111) | For the fixed N_pack=nearUniformSlotCount=ceil(max(1,1/(6*explicitFineLength)))+2, beta <= 7/8-1/(32*N_pack), and for every eps>0 there is C_eps>=0 for all integers n>=1: \|M(n)\|<=C_eps*n^(7/8-1/(32*N_pack)+eps). The positive distinct slots have sum 1/6 and satisfy the original complete detector/source budgets. No no-loss bound at the endpoint is asserted. |
| `MILESTONE-PRIME-LOCATION-ANCESTRY` | formalization_milestone | PROVED | PROVED_IN_LEAN_PR_GREEN_UNMERGED | PROVED_IN_LEAN_PR_GREEN_UNMERGED | [`squareWheelPrimeHalfMass_eq_prefix_sub_late`](https://github.com/OVVO-Financial/RH_Lean/blob/43c9ac1235ceed8f40762ad5357486fea27e31bb/research/VF_MID_PRIME_LOCATION_ANCESTRY_DICHOTOMY_20261108.lean)<br/>[`squareWheelLateRemoved_has_new_prime_factor`](https://github.com/OVVO-Financial/RH_Lean/blob/43c9ac1235ceed8f40762ad5357486fea27e31bb/research/VF_MID_PRIME_LOCATION_ANCESTRY_DICHOTOMY_20261108.lean)<br/>[`squareWheelLateRemoved_has_smaller_prime_root`](https://github.com/OVVO-Financial/RH_Lean/blob/43c9ac1235ceed8f40762ad5357486fea27e31bb/research/VF_MID_PRIME_LOCATION_ANCESTRY_DICHOTOMY_20261108.lean)<br/>[`squareWheelEarlierBalanced_nextUnbalanced`](https://github.com/OVVO-Financial/RH_Lean/blob/43c9ac1235ceed8f40762ad5357486fea27e31bb/research/VF_MID_PRIME_LOCATION_ANCESTRY_DICHOTOMY_20261108.lean) | [#1113](https://github.com/OVVO-Financial/RH_Lean/pull/1113) | For every R>=2 and S<=R, the genuine prime left-minus-right mass on R^2<n<(R+1)^2 equals prefix-wheel mass minus the signed mass of later-removed composite sites. Every removed site has a genuine prime divisor S<q<=R, hence sqrt(q)<R. The exact masses at R=2,3,4 are 0,0,1, refuting only inheritance of perfect one-block balance. |
| `OPEN-MERTENS-FURTHER-GAIN` | open_obligation | OPEN | NOT_FORMALIZED | UNKNOWN |  |  | Prove a fixed eta>0 so for every eps>0 there exists C_eps independent of x with \|M(x)\|<=C_eps*x^(b_active-eta+eps), where the strongest verified b_active is 7/8-1/(32*N_pack) at green unmerged #1111. Preserve the actual source and every complementary term. A further gain beyond that boundary remains open; main's merged comparator is separately 7/8-1/(48N_*). |
| `OPEN-AMPLIFICATION-SUBPOWER` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | UNKNOWN | [`SquareRootAmplificationZeroLogGrowthStatement`](../RHLean/Proof/SquareRootAmplificationLogGrowth.lean) |  | SquareRootAmplificationZeroLogGrowthStatement: q(X)=log(1+A(X))/log X tends to zero for integer X->infinity, with A(X)=max_{R^2-1<=X}(M(R^2-1)-1)^2/(R^2 K_R) and strict history K_R. Equivalent to eventual bounds by every positive power, not to the proved fixed positive-power bound. |
| `OPEN-NATIVE-OWNER-FRACTIONAL` | open_obligation | OPEN | LEAN_STATEMENT_ONLY | UNKNOWN | [`NativeUniformFractionalOwnerContraction`](../research/oai_434/VF919FractionalOwnerContraction.lean) |  | Exist c with 0<c<=1 such that for every theta in [1/2,7/8], MertensGrowthAtMost(theta) implies NativeOwnerBound((1-c)*(2*theta-1)); the existing consumer then contracts theta-1/2 geometrically. The quantifier over UPDATED theta is essential and unproved. |
<!-- END GENERATED: nodes -->

### Typed edges

<!-- BEGIN GENERATED: edges -->
| Edge | From | Type | To | Conditions | Certified by | Note |
| --- | --- | --- | --- | --- | --- | --- |
| `E-VK-CAN-SQ-REAL` | `OPEN-VF-ACTUAL-PRIME` | PROVED_EQUIVALENCE | `PROP-VF-CAN-REAL-VONKOCH` |  | `MILESTONE-VONKOCH-VF-LEAN` | vfCanonicalSquareVonKoch_iff_realVonKoch (renormalized constants) |
| `E-VK-CAN-SQ-LEGACY` | `OPEN-VF-ACTUAL-PRIME` | PROVED_EQUIVALENCE | `PROP-VF-MID-SQUARE-VONKOCH` |  | `MILESTONE-VONKOCH-VF-LEAN` | vfCanonicalSquareVonKoch_iff_legacy (fixed sqrt2 phase absorbed) |
| `E-VK-CAN-REAL-LEGACY` | `PROP-VF-CAN-REAL-VONKOCH` | PROVED_EQUIVALENCE | `PROP-VF-MID-REAL-VONKOCH` |  | `MILESTONE-VONKOCH-VF-LEAN` | vfCanonicalRealVonKoch_iff_legacy |
| `E-VK-MID-REAL-PRIMELI` | `PROP-VF-MID-REAL-VONKOCH` | PROVED_EQUIVALENCE | `PROP-PRIME-LI-VONKOCH` |  | `MILESTONE-VONKOCH-VF-LEAN` | vfMidVonKochBounded_iff_primeLiVonKochBounded (uses vfMidLiRootBounded) |
| `E-VK-MID-SQ-PRIMELI` | `PROP-VF-MID-SQUARE-VONKOCH` | PROVED_EQUIVALENCE | `PROP-PRIME-LI-VONKOCH` |  | `MILESTONE-VONKOCH-VF-LEAN` | vfMidSquareEndpointVonKochBounded_iff_primeLiVonKochBounded |
| `E-VK-REQ-QUAD` | `MILESTONE-VONKOCH-VF-LEAN` | REQUIRES | `MILESTONE-VF-LI-ROOT` |  |  | the equivalence consumes the root-scale quadrature |
| `E-VK-REQ-CANON` | `MILESTONE-VONKOCH-VF-LEAN` | REQUIRES | `MILESTONE-VF-CANONICAL` |  |  | canonical definition and sqrt2 phase transport |
| `E-O1-IMPLIES-ROOT` | `MILESTONE-VF-LI-O1` | PROVED_IMPLICATION | `MILESTONE-VF-LI-ROOT` |  |  | elementary: O(1) <= B sqrt(x) for x >= 4 |
| `E-VF-CAN-RH` | `OPEN-VF-ACTUAL-PRIME` | CONDITIONAL_IMPLICATION | `RH` | `IFACE-CLASSICAL-VONKOCH` | `RH-CONDITIONAL-CONSUMER` | riemannHypothesis_of_vfCanonicalSquare |
| `E-VF-TWO-TO-ONE` | `OPEN-VF-ACTUAL-PRIME` | PROVED_IMPLICATION | `OPEN-VF-LOW` |  |  | elementary: \|D\| <= C R log R implies D >= -C R log R |
| `E-VF-LOW-RH` | `OPEN-VF-LOW` | CONDITIONAL_IMPLICATION | `RH` | `LIT-MV-OMEGA-PM`, `PAPER-VF-LOW-ONE-SIDED` | `PAPER-VF-LOW-ONE-SIDED` | uses the Lean square-endpoint quadrature abs_vfMidLiError_sq_le_uniform plus an external Omega+- theorem |
| `E-915-VF` | `OPEN-915-SOURCE-PAYMENT` | CONDITIONAL_IMPLICATION | `OPEN-VF-ACTUAL-PRIME` | `FINITE-915-BASE-WINDOW` | `CONSUMER-915-CANONICAL` |  |
| `E-VFLOW-MECH` | `MECH-VF-LOW-FIRST-LOWER-ESCAPE` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-VF-LOW` |  |  | would supply the one-sided wall K R log R directly on the original source |
| `E-SAT-MECH-VFLOW` | `MECH-SAT-OWNER-REMOVAL` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-VF-LOW` |  |  | signed owner-removal bound on genuine prime/composite incidence feeding the lower wall |
| `E-SAT-MECH-JOH` | `MECH-SAT-OWNER-REMOVAL` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-JOH-SIGN` |  |  | weighted composite-removal inequality T(R^2) > A(R^2) - L(R^2) |
| `E-JOH-MECH` | `MECH-JOH-ANCESTRY-DISPLACEMENT` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-JOH-SIGN` |  |  | controls the first-moment displacement term sum J_r in the conservation law |
| `E-JOH-RH` | `OPEN-JOH-SIGN` | CONDITIONAL_IMPLICATION | `RH` | `LIT-JOHNSTON-2022`, `PAPER-JOH-SQUARE-TRANSFER` | `PAPER-JOH-SQUARE-TRANSFER` |  |
| `E-ETA-ZEROTH` | `CARRIER-PRIME-MODEL-EVENTS` | WEIGHTED_PROJECTION | `CARRIER-915-ZEROTH-MOMENT` |  | `MILESTONE-915-MOVING-OWNER` | within-block arrival locations (block sums only) |
| `E-ETA-FIRST` | `CARRIER-PRIME-MODEL-EVENTS` | WEIGHTED_PROJECTION | `CARRIER-JOH-FIRST-MOMENT` |  | `CLAIM-20261024-OWNER-1` | pointwise discrepancies (triangular weight N - k) |
| `E-915-SOURCE-ZEROTH` | `CARRIER-915-WEIGHTED-SOURCE` | WEIGHTED_PROJECTION | `CARRIER-915-ZEROTH-MOMENT` |  | `MILESTONE-915-MOVING-OWNER` | native VF weights, masks, clipping, historical anchors, restoration, quadratic NNS terms |
| `E-REF-JOH` | `REFUTED-JOH-COUNT-ONLY` | REFUTED_BY | `CE-JOH-R4-R7` |  |  |  |
| `E-MERTENS-RH` | `PROP-MERTENS-ENERGY` | PROVED_IMPLICATION | `RH` |  | `CONSUMER-MERTENS-ENERGY-RH` |  |
| `E-MERTENS-BELOW-78` | `PROP-MERTENS-ENERGY` | PROVED_IMPLICATION | `MILESTONE-MERTENS-STRICT-EXPLICIT` |  |  | elementary: exponent 1/2 + eps is below 7/8 - delta for delta < 3/8 |
| `E-NEAR-UNIFORM-REQUIRES-TOTAL-MASS` | `MILESTONE-NEAR-UNIFORM-SLOT-BOUNDARY` | REQUIRES | `MILESTONE-OAI-TOTAL-MASS` |  |  |  |
| `E-CODIV-MECH` | `MECH-CODIV-SIGNED-COVARIANCE` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-MERTENS-FURTHER-GAIN` |  |  | A strictly positive NEW global saving beyond b_active=7/8-1/(32*N_pack), retaining the complete original-source consumer and exact-head unmerged status of the current baseline. |
| `E-QUOT-MECH` | `MECH-SIGNED-QUOTIENT-VARIATION` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-MERTENS-FURTHER-GAIN` |  |  | A strictly positive NEW global saving beyond b_active=7/8-1/(32*N_pack), retaining the complete original-source consumer and exact-head unmerged status of the current baseline. |
| `E-OAI-MECH` | `MECH-OAI-NNS-COMPLETE-LEDGER` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-MERTENS-FURTHER-GAIN` |  |  | A strictly positive NEW global saving beyond b_active=7/8-1/(32*N_pack), retaining the complete original-source consumer and exact-head unmerged status of the current baseline. |
| `E-FINITE-A-GRAM` | `OPEN-FINITE-AC` | PROVED_EQUIVALENCE | `PROP-LEGAL-ANCESTRY-GRAM` |  | `THM-FINITE-A-IFF-LEGAL-GRAM` |  |
| `E-FINITE-A-MERTENS` | `OPEN-FINITE-AC` | PROVED_IMPLICATION | `PROP-MERTENS-ENERGY` |  | `CONSUMER-FINITE-A-MERTENS` |  |
| `E-FINITE-AC-MECH` | `MECH-FINITE-AC-HISTORICAL-ENVELOPE` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-FINITE-AC` |  |  | the uniform constant A itself |
| `E-CORR4-FINITE-A` | `OPEN-CORR4` | PROVED_IMPLICATION | `OPEN-FINITE-AC` |  | `CONSUMER-CORR4-FINITE-A` |  |
| `E-CORR4-RELAXED` | `OPEN-CORR4-RELAXED-REMAINDER` | PROVED_IMPLICATION | `OPEN-CORR4` |  | `PR1021-RELAXED-CONSUMER` | Merged Lean consumer; physical remainder estimate stays unproved. |
| `E-CORR4-REQ-FRAME` | `PR1021-RELAXED-CONSUMER` | REQUIRES | `PR1023-FRAME-B7` |  |  | the sharper coefficient 3 + 4 b_7 uses #1023; the 886/225 version uses the merged 211/900 frame |
| `E-CORR4-MECH` | `MECH-CORR4-SIGNED-FIRST-OWNER-GRAM` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-CORR4-RELAXED-REMAINDER` |  |  | pays \|B_R\|^2 - (9/4) E_R by O(R^2 K) without a prior finite-A bound |
| `E-REF-CORR4-012` | `REFUTED-CORR4-C-012` | REFUTED_BY | `CE-CORR4-R5561` |  |  |  |
| `E-REF-CORR4-SIGN` | `REFUTED-CORR4-LOCAL-SIGN` | REFUTED_BY | `CE-CORR4-R57` |  |  |  |
| `E-REF-CORR4-C0` | `REFUTED-CORR4-DAUGHTER-ONLY` | REFUTED_BY | `CE-CORR4-R56` |  |  |  |
| `E-MULIFT-MERTENS` | `OPEN-MU-LIFT` | CONDITIONAL_IMPLICATION | `PROP-MERTENS-ENERGY` | `PAPER-MU-LIFT-CONTRACTION` | `PAPER-MU-LIFT-CONTRACTION` |  |
| `E-MULIFT-MECH` | `MECH-MU-LIFT-SUBCRITICAL` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-MU-LIFT` |  |  | fixed r < k |
| `E-NYMAN-RH` | `OPEN-NYMAN-DENSITY` | CONDITIONAL_IMPLICATION | `RH` | `LIT-BAEZ-DUARTE` | `LIT-BAEZ-DUARTE` |  |
| `E-NYMAN-MECH` | `MECH-NYMAN-FULL-BASIS-DECAY` | INDEPENDENT_ARITHMETIC_GAIN | `OPEN-NYMAN-DENSITY` |  |  | all-scale decay of the full-basis distance |
| `E-REF-NYMAN` | `REFUTED-NYMAN-SQUARE-CONTRACTION` | REFUTED_BY | `LIT-BURNOL-2002` |  |  |  |
| `E-BLOCK-RH` | `REFUTED-BLOCK-UNIVERSAL` | CONDITIONAL_IMPLICATION | `RH` | `IFACE-CLASSICAL-VONKOCH` | `CONSUMER-BLOCK-RH` |  |
| `E-REF-BLOCK` | `REFUTED-BLOCK-UNIVERSAL` | REFUTED_BY | `CE-BLOCK-R549` |  |  |  |
| `E-CORR4-MIXED-TAIL-IMPROVES-78` | `OPEN-CORR4-MIXED-TAIL-POWER` | PROVED_IMPLICATION | `MILESTONE-MERTENS-STRICT-EXPLICIT` |  | `CONSUMER-CORR4-MIXED-TAIL-POWER-IMPROVEMENT` | If the full signed mixed-tail estimate holds for eta>0, the merged Lean theorem yields beta = 7/8 - eta/4. This edge does not assert its open premise. |
| `E-EXPLICIT-MERTENS-AMPLIFICATION` | `MILESTONE-MERTENS-STRICT-EXPLICIT` | PROVED_IMPLICATION | `MILESTONE-EXPLICIT-AMPLIFICATION` |  | `MILESTONE-EXPLICIT-AMPLIFICATION` | Merged #1108 consumes the explicit Mertens bound using exact endpoint amplification with K_R>=1; supplies a fixed positive-power bound, not zero-log growth. |
| `E-FINITE-A-IMPLIES-ZERO-LOG` | `OPEN-FINITE-AC` | PROVED_IMPLICATION | `OPEN-AMPLIFICATION-SUBPOWER` |  |  | elementary: A constant uniform bound on the original A(X) implies log(1+A(X))/log(X)->0; converse need not hold. |
<!-- END GENERATED: edges -->

## 8. Dated PR evidence snapshot

<!-- BEGIN GENERATED: evidence -->
Snapshot `2026-11-08T19:18:49Z`, main `8b5a6921002da0742ecfab9ee7d40728ed5fe348`, `leanprover/lean4:v4.34.1`. Refresh from GitHub before relying on any open-PR row.

| PR | State | Head | Observed checks | Grade |
| --- | --- | --- | --- | --- |
| [#915](https://github.com/OVVO-Financial/RH_Lean/pull/915) | merged 2026-10-12 |  | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#923](https://github.com/OVVO-Financial/RH_Lean/pull/923) | merged 2026-10-12 |  | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#929](https://github.com/OVVO-Financial/RH_Lean/pull/929) | merged 2026-10-12 |  | not re-audited | REPOSITORY_NOTE |
| [#932](https://github.com/OVVO-Financial/RH_Lean/pull/932) | merged 2026-10-12 | `2713d8ef495e` | 17/17 jobs green | KERNEL_CHECKED_ON_MAIN |
| [#939](https://github.com/OVVO-Financial/RH_Lean/pull/939) | merged 2026-10-14 |  | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#949](https://github.com/OVVO-Financial/RH_Lean/pull/949) | merged 2026-10-15 |  | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#954](https://github.com/OVVO-Financial/RH_Lean/pull/954) | merged 2026-10-15 |  | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#957](https://github.com/OVVO-Financial/RH_Lean/pull/957) | merged 2026-10-16 |  | not re-audited | REPOSITORY_NOTE |
| [#958](https://github.com/OVVO-Financial/RH_Lean/pull/958) | merged 2026-10-16 |  | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#961](https://github.com/OVVO-Financial/RH_Lean/pull/961) | merged 2026-10-16 |  | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#983](https://github.com/OVVO-Financial/RH_Lean/pull/983) | merged 2026-10-20 | `ed9bb56e29ea` | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#987](https://github.com/OVVO-Financial/RH_Lean/pull/987) | merged 2026-10-21 | `a5271548202e` | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#1012](https://github.com/OVVO-Financial/RH_Lean/pull/1012) | merged 2026-10-24 |  | not re-audited | REPOSITORY_NOTE |
| [#1017](https://github.com/OVVO-Financial/RH_Lean/pull/1017) | merged 2026-10-24 | `b96ac58b656a` | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#1019](https://github.com/OVVO-Financial/RH_Lean/pull/1019) | merged 2026-10-24 | `0d39cfe586b8` | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#1020](https://github.com/OVVO-Financial/RH_Lean/pull/1020) | merged 2026-10-24 | `effff7a0462a` | not re-audited | REPOSITORY_NOTE |
| [#1021](https://github.com/OVVO-Financial/RH_Lean/pull/1021) | merged 2026-10-26 | `72d7e508ed13` | 14/14 jobs green | KERNEL_CHECKED_ON_MAIN |
| [#1022](https://github.com/OVVO-Financial/RH_Lean/pull/1022) | merged 2026-10-26 | `03f756a4e495` | 13/13 jobs green | KERNEL_CHECKED_ON_MAIN |
| [#1023](https://github.com/OVVO-Financial/RH_Lean/pull/1023) | merged 2026-10-26 | `44fbcf3f2dca` | 12/12 jobs green | KERNEL_CHECKED_ON_MAIN |
| [#1024](https://github.com/OVVO-Financial/RH_Lean/pull/1024) | merged 2026-10-26 | `b74d47009362` | 8/8 jobs green | REPOSITORY_NOTE |
| [#1106](https://github.com/OVVO-Financial/RH_Lean/pull/1106) | merged 2026-11-08 | `aafb28e85bbc` | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#1107](https://github.com/OVVO-Financial/RH_Lean/pull/1107) | merged 2026-11-08 | `cd8f98fd6ed2` | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#1108](https://github.com/OVVO-Financial/RH_Lean/pull/1108) | merged 2026-11-08 | `a0c986c0343a` | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#1109](https://github.com/OVVO-Financial/RH_Lean/pull/1109) | merged 2026-11-08 | `fedd203158af` | not re-audited | KERNEL_CHECKED_ON_MAIN |
| [#1111](https://github.com/OVVO-Financial/RH_Lean/pull/1111) | open | `20875a55dd97` | 13/13 jobs green | KERNEL_CHECKED_GREEN_PR_HEAD |
| [#1113](https://github.com/OVVO-Financial/RH_Lean/pull/1113) | open | `43c9ac1235ce` | 14/14 jobs green | KERNEL_CHECKED_GREEN_PR_HEAD |
<!-- END GENERATED: evidence -->

## 9. Maintenance

Edit [proof-obligations.json](proof-obligations.json), then:

```bash
python3 scripts/proof_obligation_dag.py --write          # regenerate the marked blocks
python3 scripts/proof_obligation_dag.py --check --repo-index
python3 -m unittest discover -s scripts -p test_proof_obligation_dag.py -v
python3 scripts/proof_dag_falsifier_regressions.py
python3 scripts/vf_block_capture_counterexample_549.py
```

Before upgrading any status, verify the original carrier, quantifiers, normalization, complete source terms, independence from the conclusion, all-scale validity, the exact passing Lean head, the standard axiom footprint, an actual exponent/coefficient gain, and independent review of any paper argument. Never infer an open PR's state from this page; query GitHub and update the dated snapshot.

