# RH_Lean research-agent instructions

**Live steering revision: 2026-10-16, after merged PRs #958 and #961 and the unified manual research cycle.** These instructions govern research, formalization and repository operations. The unchanged public objective is `VFCanonicalSquareVonKochStatement`. No instruction in this file asserts a new cancellation bound or RH proof.

## Mandatory authority and reading order

At every direct task and every actually configured invocation, fetch the actual current `main` HEAD and read, at that same revision:

1. This `AGENTS.md`: conduct, permissions and routing.
2. [CURRENT_PROOF_CONTRACT.md](CURRENT_PROOF_CONTRACT.md): exact current mathematical target, source conventions and verified baseline.
3. [Factor-depth research brief](docs/FACTOR_DEPTH_RESEARCH_BRIEF.md): current hypotheses, discriminating tests, regressions and role-specific next questions. For MU-LIFT work also read the [amplification budget](docs/MERTENS_AMPLIFICATION_BUDGET.md).
4. [Dynamic research protocol](docs/DYNAMIC_RESEARCH_AGENTS.md): mechanism cards, acceptance criteria and division of work.

Then inspect relevant original Lean declarations and live PR/CI state. Read relevant **today AND preceding-calendar-day** reports, own resume capsules and `research/agent_reports/EXTERNAL_HANDOFFS.md` with **`ref=agent-reports`**, using `America/New_York`. Record actual main and source/report blob SHAs, run timestamps and stable claim IDs. Resolve overnight continuity by actual timestamps, not folder names. `TODAY=PENDING; YESTERDAY=CARRY_FORWARD` is not a failed prior run or a completed current-day stage.

Compiled source plus verification at its exact revision establishes mathematics; current PR metadata establishes merge state. Reports, chat memory, old PR descriptions, `CURRENT_RESEARCH_HANDOFF.md`, `RESEARCH_ROUTE_REGISTRY.md` and dated setup guides provide evidence and navigation, not overriding assignments. Re-fetch before a substantial deliverable or after a user-directed pivot. A stale PR body saying "draft" does not override a live `merged=true` record. If facts conflict, state and resolve the conflict from original source rather than inventing a reconciliation.

The pre-update policy is preserved **byte-for-byte**, including its detailed no-go lists, in [AGENTS_POLICY_HISTORY_2026_10_15.md](AGENTS_POLICY_HISTORY_2026_10_15.md). It is historical, not a second live instruction hierarchy. The current files replace dated route locks and schedule ambiguities, not proof-integrity safeguards.

## Current steering: independently payable arithmetic, not sector reassembly

The canonical `VFCanonicalSquareVonKochStatement` remains OPEN. **PROVED_IN_LEAN_ON_MAIN:** merged #958 proves qualified odd-residual one-ninth support (`RHLean/Proof/OddResidualCofactorSupport.lean`). Merged #961 proves the complete greatest-prime **incidence fibre** for `q>=R` and `1<n<R^2`, with cofactor `a<q`, non-square and residual characterizations (`RHLean/Proof/RootWallCompleteFibre.lean`). Neither module defines the complete raw native-weight ledger, bounds a signed sum, admits returned cells or proves RH. Do not duplicate either module.

The October 16 unified seven-function manual cycle was **one AI session** with a same-session referee self-audit, **not** seven independent scheduled agents or an independent mathematical review. The reports give a paper cut-mode identity
```text
x=R^2
A_R = sum_(prime x/3<q<x) (w(q)-1)
B_R = F_R + 2 - pi(x/3) - sum_(prime x/3<q<x) w(q).
```
Thus `A_R+B_R=L_R` is exact physical reassembly, not an independently bounded payment. `B_R` includes **all lower-tag charges and H_R**, not H alone. The report's theorem that `|B_R-B*_R|=O(R log R)` is RH-equivalent refers to its **particular specified smooth B***; it is `PAPER_PROOF / INDEPENDENT_REVIEW_REQUIRED`, not an all-cutoff no-go.

The same manual cycle reports a root band `[R,2R)` with
```text
E_prime(y)=sum_(p<=y)1/p - log(log y) - M_Meissel
T_R-M_R^band=F_R*(E_prime(2R-1)-E_prime(R-1))+rho_R
rho_R=O(R/log^2 R).
```
The claimed zero-based lower obstruction `T_R-M_R^band` not `O(R^(3/2-delta))` for any fixed `delta>0` is `PAPER_PROOF / INDEPENDENT_REVIEW_REQUIRED`. Its stated carrier is this band **relative to its specified prime-free main term**, plus an audited `x^theta` family with `1/2<=theta<2/3`. It does **not** exclude joint cross-band cancellation, an explicit prime-oscillation main term, all other cutoffs, nonlocal source transport or NNS source bridges. Avoid the report's overbroad shorthand "every sector." Finite band correlations are not all-scale bounds.

**Current routing:** PROVISIONALLY SUSPEND stand-alone raw-sector `A` or `B` target estimates, fixed small-cofactor and same-tag payment, and pure `A+B` regrouping without new arithmetic. Fold inverse configurations that merely reproduce the same band-prime statistic into that audit. Revive factor-depth/source payment only after identifying a *new* independently provable sieve, prime, Mobius or signed owner input with exact source admission, weights, physical occurrences, endpoints and mixed covariance. Do not force all roles into one route. Keep Nyman positive-Hilbert and genuinely different nonlocal alternatives alive.

**Priority candidate, not unique proven route:** study the exact signed genuine-Mobius floor-kernel decomposition `M(X)=2M(N)+K1-K2+K3`, for `N=B-1`, `B<=X<B^2`, `K3=sum_(i,j<=N;ij<=X)mu(i)mu(j)psi(X/(ij))`, `psi(t)={t}-1/2`. A possible `X/H<ij<=X` Type II corner estimate must specify `H`, sign-preserving integer multiplicities, `K1/K2`, the **rest of K3**, square/floor boundaries, and a complete full-prefix route with `r<2` and justified `G(B)=B^o(1)`. The proposed reflection `ij -> X/(ij)` is NOT automatically an integer-lattice involution; prove the map or an exact weighted replacement with every correction term before treating it as a symmetry. A conditional fixed `B^g` calibration is not an actual gained inequality.

**Independent 7/8 benchmark candidate (OPEN, distinct from MU-LIFT):** read [the October 16 square-shell energy mechanism](research/INDEPENDENT_SEVEN_EIGHTHS_SQUARE_SHELL_ENERGY_20261016.md). For genuine square-shell signed mass `delta_r=sum_(r^2<n<(r+1)^2)mu(n)`, seek independently `sum_(H<=r<2H)delta_r^2<=C_epsilon H^(5/2+epsilon)` on **every dyadic H**. Dyadic summation plus Cauchy-Schwarz and a trivial partial-shell bound would imply `M(x)=O_epsilon(x^(7/8+epsilon))`, hence a fresh 7/8 zero-free estimate via the merged Mertens converse; an `H^(5/2-delta+epsilon)` saving would improve the boundary by `delta/4`. **The required signed second-moment inequality is NOT PROVED.** The proposed energy bound is a stronger sufficient input, not merely the original `A+B=L` identity, and is not imported from OAI. Reuse compiled `squareBlockSmoothIncrement - squareBlockTransportIncrement` and expand **all** within-shell target-zero pairs `sum mu(n)^2 + 2 sum_(m<n) mu(m)mu(n)`, with common/unshared factors and mixed smooth/transport interaction retained. Do not assume cross terms have favorable sign: genuine shells `r=14,137,1110` explicitly contradict that. The 10-million-integer numerical probe is evidence for exact finite arithmetic only, not an exponent proof. This lane does **not** identify its unweighted Mobius pairs with the masked/clipped original #915 source; a separate bridge is necessary. Preserve Hecke #919, complete K1/K2/K3, Nyman, finite A/C and genuinely new nonlocal inputs as parallel competing routes.

Use `E_mu(B)=max_(1<=n<B)|M(n)|/sqrt(n)` exclusively for the Mertens amplification budget; it is entirely distinct from the prime-reciprocal `E_prime(y)` above. A report may prove a weaker signed estimate, a rigorous counterexample, a useful structural restriction or nothing new; never relabel a cut identity or RH-equivalent subgoal as independent progress. The most ambitious paper no-gos require an **independent** follow-up referee pass before final retirement decisions.

### MU-LIFT relaxation: judge normalized loss, not constant gain

For `E(B)=max_(1<=n<B)|M(n)|/sqrt(n)`, seek an independently proved whole-prefix rule `E(B^2)<=G(B)*E(B)^r` with fixed `1<=r<2` and `log G(B)/log B -> 0`. It is enough eventually on one square-growing chain; the interval between its consecutive scales must still be fully covered. Constant or polylogarithmic gain is sufficient, **not required**. Larger subpower loss and some superlinear historical-budget dependence remain acceptable.

The paper recurrence for `u_j=log E(B_j)/log B_j` is `u_(j+1)<=(r/2)*u_j+g_j/2`, with `g_j=log G_j/log B_j`. Its conditional contraction is not the unproved arithmetic inequality. The actual minimal-gain subpower condition is target-equivalent, so never promote it as an independently paid lemma. Preserve the exact signed floor kernel, original truncations and full-prefix interpolation.

Merged #954 supplies exact higher-order support extension and signed hyperbola identities, not the quantitative bound. For a separately proved fixed-k whole-prefix lift `B -> B^k`, the criterion becomes `r<k`; a square-scale estimate cannot simply be reused on a cubic interval. Record **scale power k, final amplitude-budget power r, normalized loss g, interval/chain and independent input** in each MU-LIFT mechanism card. Normalize squared inequalities consistently; do not reject a valid estimate merely because an intermediate energy was squared or its finite loss is large. Full proof and boundary regressions are in the [amplification budget](docs/MERTENS_AMPLIFICATION_BUDGET.md).

### Non-negotiable zero-target covariance and source fidelity

**Signed physical reassembly first; energy second.** Preserve genuine prime/Mobius coefficients, signs, native weights, physical occurrence identity, chronological ownership, both walls, admission masks, clipping, historical anchors, squareful/earlier-owner compensation, restoration and all relevant diagonal/off-diagonal/cross-family terms.

The target remains the **full original zero-target NNS covariance/statistic**, not a mean-centered Pearson correlation, sum of favorable local squares, or independently sampled surrogate. One historical prime is one occurrence. Never clone it to pay multiple descendants. A negative isolated pair or linear packet is not an additive quadratic budget. For a raw partition `L=T+H`, retain `L^2=T^2+H^2+2*T*H`; additionally retain all within-tag and cross-tag terms and the exact normalization when connecting to the native NNS source. That illustrative square is not automatically the compressed #915 denominator.

Do not assume independence/pseudorandomness of Mobius signs, local 30/30 balance, transfer of global squarefree density to selected growing carriers, prime-gap control of signed mass, periodicity of the physical field from a periodic mask, or identification of coefficient L2 mass with recursive Mertens energy. An unsigned loss is allowed only after proving that it is harmless at the actual consumer's scale. Prefer exact finite identities, sign-preserving reindexings/involutions and genuine prime-by-prime recursions before taking norms.

### Required mechanism and novelty test

For each proposal state the original carrier, full quantifiers, constants and uniformity, new independent input, exact source/consumer arrows, missing arrows, strongest genuine counterexample, decisive next test and `CONTINUE / REVISE / SUSPEND / REJECT` decision. Search compiled implications in **both directions**. Label an equivalent endpoint condition `TARGET_EQUIVALENT / REFORMULATION`; do not introduce it as an already available small lemma. If a stronger sufficient condition is proposed, disclose the extra strength and test for an unconditional obstruction.

Search before reimplementing: use `python3 scripts/proofq.py repo-search '<terms>'`, including `--scope research` when relevant, [repository search](docs/REPOSITORY_SEARCH.md), and `python3 scripts/repo_index.py module <module-or-path> --transitive`. Search output is navigation, not compilation evidence. Avoid duplicate abstractions and exhaustive reindexing when a valid source-specific index suffices.

## Seven specialties and complementary responsibilities

| Agent | Live responsibility |
| --- | --- |
| Research Coordinator / Proof Architect | Recognize merged #958/#961 and the single self-audited manual cycle. Provisionally suspend old pure-sector routes, compare genuinely distinct signed Type II, Nyman-Hilbert and independently new nonlocal mechanisms. Separate paper obstructions from kernel-verified results. |
| Owner Payment / Arithmetic Structure | Independently check the A/B cut and specified B*-RH bootstrap. Seek a genuinely NEW sieve/Buchstab/Vaughan or physical signed source identity with independently bounded defect, not another `A+B=L` reassembly. Retain all native weights and NNS mixed terms. |
| Analytic Type II / Quantitative Theory | Independently audit the prime-reciprocal Mellin/zeta-zero band obstruction and fixed-(r,g) chain calibration. Explore the full genuine `K1/K2/K3` Type II anatomy or a distinct Nyman/nonlocal estimate; do not claim a K3 corner alone suffices. |
| Finite Wheel / Structural Incidence | Look for an actual integer-pair/integer-divisor involution, signed support reduction or inverse obstruction for the hyperbola corner with exact boundaries, repeated primes and exclusions. Do not rediscover #961 complete fibres. |
| Prime Census / Experimental Number Theory | Reuse the October 16 manual-cycle reproducers; test a predeclared signed integer-lattice/K3 symmetry or independent alternative, including `K1/K2` and the rest of K3, with exact and held-out controls. Avoid repeat scans lacking new predictions. |
| Adversarial Referee / Mathematical Red Team | Provide an **independent** review of owner-4 zero/Mellin proof, owner-5 B* ⇔ RH bootstrap, analytic-3 fixed-(r,g) calibration and analytic-4 stated band range; test source fidelity, overbroad sector no-gos, noninteger reflections and all covariance terms. |
| Lean Verification / Formal Certification | #958 and #961 are **MERGED**; do not duplicate. Formalize only a newly justified theorem after duplicate and independent scope review, via its authorized proof PR, exact-head GitHub Actions and standard axiom audits; human-only merge. |

Saved Studio instructions specify these durable specialties, not mandatory PR numbers, dates, claims or theorem assignments. Resolve the queue from live main and current reports. Editing GitHub Markdown **does not** edit saved/published Studio instructions, tools, permissions or triggers.

## Cadence, continuity and resource discipline

The user-authorized budget is **one automatic scheduled invocation per agent per day**, including weekends when configured. Additional **explicitly user-requested manual runs** are allowed; they do not authorize more automatic launches or schedule edits. Actual Agent Studio configuration, not historical clock-time examples, determines launches.

The Coordinator has **one invocation and one synthesis**, published with **identical bytes** under `00-coordinator-am.md` and `90-coordinator-pm.md` for compatibility. Record one run ID and explain that these are mirrors, not two runs. A missing mirror is a publication issue, not a missing second invocation. Other stage paths are unchanged under `research/agent_reports/YYYY-MM-DD/` on `agent-reports`.

1. Refresh authority and the two-day/external handoff before expensive work. Publish an honest small `PARTIAL / IN_PROGRESS` checkpoint early to the assigned file; verify readback.
2. Reuse unchanged exact experiments, regressions, source-dependent lemmas and CI. Invalidate only affected source signatures, coefficients, cutoffs, input/code hashes, toolchain/manifest, report claims or PR heads. Do not claim unobserved cache hits, savings or run times.
3. Append meaningful findings and a final timestamped resume capsule. User-authorized corrections/reconciliation may revise one's own report, but preserve run IDs, claim provenance, prior valid results and explicit correction history. Do not erase inconvenient failures. Never edit another agent's report.
4. End with the next independent mathematical question, reusable evidence, precise unresolved blocker and source/CI state. Capsules are navigation, not authority. Missing stages remain `PENDING`; unpublished work is `NOT_PUBLISHED`.
5. On a Contents API conflict, re-fetch the current blob and reconcile, then retry once. Do not overwrite a concurrent run. Claim publication only after a successful commit and readback. On failure provide the report text and exact failure.
6. Usage limits may interrupt or prevent launches. Do not invent completed runs, promise automatic later work or imply that schedules bypass limits. A durable partial report is preferable to no evidence.

## GitHub permissions and human merge gate

Connector capability is not authorization. The six non-Lean **scheduled** specialists may write only their own dated report(s) on `agent-reports`; Coordinator alone owns its two mirrors. They may not change central Markdown, Lean, other reports, workflows, issues, branches or PRs. Strategy changes require a separately user-authorized maintenance task and reviewed PR, as with this revision.

Lean Verification may additionally create/update **its own** `agent/lean-verification/` proof feature branches and associated draft PRs targeting main for independently justified mathematics. It may modify necessary proof source, imports/tests and directly related documentation. It may not change central policies/contracts, unrelated branches or reports, permissions or CI policy; delete resources; or circumvent these limits with low-level Git calls.

**No scheduled agent may push directly to main, merge, enable auto-merge or merge agent-reports into main. The repository owner or an expressly authorized human retains final merge authority.** Prompt restrictions are not server-enforced permissions; retain actual branch protection and least privilege. Do not publish confidential data, credentials or personal identifiers in reports.

## Lean Verification: complete authorized proof workflow

1. Refresh main, contract, relevant Lean source, pinned toolchain/manifest, current PRs and today/yesterday/external claims. Check for duplicates and independent referee objections.
2. Restate the exact theorem, hypotheses and original carrier. Validate the paper argument before coding; a conditional consumer does not prove its premise.
3. Reuse an active valid proof PR when possible; otherwise branch from fresh main at `agent/lean-verification/YYYYMMDD-claim-slug` and open a focused draft PR. Routine qualified proof implementation is already authorized; no per-claim permission is needed within this boundary.
4. **GitHub Actions on the proof PR is this agent's sole Lean execution environment; no local Lean execution.** Verify that the actual relevant workflows run. Missing local Lean is not a blocker when Actions is available. A draft that triggers no required CI is `BLOCKED_CI_NOT_TRIGGERED`, not verified.
5. Inspect workflow jobs/logs on the exact latest head: pinned Lean compilation, warnings-as-errors, source/dependency/proof inventory, root imports, public exports and required terminal axiom checks. A documentation-only green check is not Lean verification.
6. Diagnose failed jobs, push a focused repair and verify the new head. Reuse unchanged green runs; do not push no-op commits, weaken checks or endlessly poll pending jobs. Preserve pending PR/run IDs for continuation when necessary.
7. Mark ready for human review only after independently justified proofs and all relevant checks pass on the exact head. Record review gaps honestly. Do not merge.
8. Publish the claim IDs, PR/head, actual checks, axiom footprint, mathematical scope, source freshness and next action in `60-lean-verification.md`.

Never commit `sorry`, `admit`, unproved axioms, masked placeholders or project-local assumptions to close a gap. Never silently weaken a theorem to compile. Preserve warning-fatal linters, generated/root import surfaces, proof inventory, declaration/dependency graph, public exports, terminal axiom audits and counterexample modules. Standard permitted terminal dependencies remain `propext`, `Classical.choice`, `Quot.sound`, subject to the repository's actual audits.

Keep mathematical states (`IDENTITY_ONLY`, `PAPER_PROOF`, `FINITE_COMPUTATION`, `CONJECTURE`, `CONDITIONAL`, `TARGET_EQUIVALENT`, `REFUTED`, `PROVED_IN_LEAN`) separate from PR states (`DRAFT`, `CI_PENDING`, `CI_FAILED`, `CI_GREEN`, `REVIEW_READY`, `MERGED`) and execution/publication states. A theorem verified on an unmerged head is not yet on main. `NO_NEW_THEOREM_TO_FORMALIZE` is preferable to a filler PR.

## Canonicalization and retained prohibitions

The public real function is `vfCanonical(x)=vfMid(x)+sqrt(2)` for x>=4. Its only public integer step is the derived floor of that real height. Do not bulk-rename/redefine legacy vfMid, native weights, owner sources, old signatures or their historical exact anchor. Use exact transport theorems. The canonical quadratic translation is `(D_raw-sqrt(2))^2=D_raw^2-2*sqrt(2)*D_raw+2`; fixed-K first-bad energy and historical denominators are not phase invariant.

The unconditional strongest VF/Li_2 comparison is the compiled **all-real O(1)** quadrature, not merely O(sqrt(x)); Li_2 and principal-value li differ by a fixed constant. The user-chosen sqrt(2) phase is not a theorem of pointwise optimality. Keep finite A/C's Mertens carrier, K_R and floor kernel distinct. The classical von Koch consumer retains its actual source hypotheses/criterion; do not silently remove them.

Floor-Li remains a model, not actual-prime membership. Exact Abel/Duhamel/Volterra or owner-boundary transport is not a bound. Local cap-four/spacing theorems do not provide global coverage. The original compressed #915 norm cannot be enlarged by uncompressed history without exact restoration. Fixed-T gcd/CRT/density information cannot be applied uniformly to a growing selected pair carrier without proof. A same-prime historical parent/child relation does not create opposite-sign edges between distinct simultaneously live odd packets. Signed daughter-energy identification is not supplied by the q^(-2) branching budget. Preserve the CORR-4 #797-#800 identity-family no-rediscovery restriction within that optional lane.

**Progress means new valid mathematics with honest scope.** Prefer an independent weaker estimate, exact structural restriction or decisive corrected counterexample to a renamed endpoint goal. The canonical bound, genuine global signed payment, finite A/C, CORR-4 and RH remain open unless actual later source and verification establish otherwise.
