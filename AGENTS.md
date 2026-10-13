# RH_Lean research-agent instructions

These instructions govern mathematical research, Lean formalization, and repository changes in this repository.

## Authority and source of truth

1. Compiled Lean source is authoritative.
2. `CURRENT_PROOF_CONTRACT.md` states the compact current proof architecture and must be read before beginning a new proof attack.
3. `CURRENT_RESEARCH_HANDOFF.md` records the broader research history and detailed prior frontiers. Use it for context, but do not let older sections override the current proof contract or compiled source.
4. Architecture notes, route registries, research notes, exports, old PRs, and historical handoffs are evidence and context, not authority when they conflict with compiled source or the current proof contract.
5. Never infer that two quantities are equal because their prose descriptions sound similar. Use or prove an exact bridge theorem.

## Dynamic research direction and specialist-agent refresh

**Central routing rule:** `AGENTS.md` governs standing agent conduct and how to find current instructions; `CURRENT_PROOF_CONTRACT.md` identifies the **current active mathematical proof target**, with compiled Lean source authoritative for what is actually proved. The user may change research strategy at any time; dated campaign notes, old PRs, custom agent names, and previously supplied prompts do NOT freeze a mathematical target.

For every new research assignment, and again before making a significant recommendation or writing code:

1. Fetch fresh `AGENTS.md` and `CURRENT_PROOF_CONTRACT.md` from the current `main` HEAD using the connected GitHub repository; record the actual branch/commit and indicate whether retrieval succeeded. Do not substitute chat memory, a cached snapshot, or a draft PR for fresh authoritative instructions.
2. Read relevant Lean declarations, then consult `CURRENT_RESEARCH_HANDOFF.md`, `RESEARCH_ROUTE_REGISTRY.md`, and research PRs only for scoped context. A draft PR can propose a future priority but does not supersede `main` until merged or the user expressly changes the assignment.
3. Derive the current research objective from these fresh sources. Treat named specialist agents (owner payment, analytic number theory, sieve/combinatorics, numerical referee, Lean verification, coordination) as **persistent expertise**, not permanent commitments to #915, finite A/C, Type II, or any particular conjecture. Redirect that expertise to the active target; explicitly flag a mismatch or ask for direction if the specialty cannot help.
4. If the sources conflict, distinguish operating rules, formal mathematics and current objectives; identify the conflict and ask rather than invent a reconciliation. Existing safety, proof-integrity, no-hidden-assumptions, warning-fatal and authorization constraints are never silently weakened.
5. Treat a long-lived session as potentially stale: re-fetch on a new user request, an announced pivot, or before a substantive deliverable. Do not claim that Workspace Agents automatically synchronize their memory or launch other agents. State any GitHub access limitation.

Initial ChatGPT Agent Studio campaign: [setup guide](docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md) and [research snapshot](research/CHATGPT_AGENT_STUDIO_FIRST_BAD_CAMPAIGN_2026_10_12.md). These are **dated starting assignments**, not higher-priority instructions than `AGENTS.md` and the current proof contract.

### Daily seven-specialist research loop (when scheduled)

The user directs a **complete daily research cycle, including weekends**. The daily inter-agent handoff is a **dated Markdown report per stage on the dedicated `agent-reports` branch**, under `research/agent_reports/YYYY-MM-DD/`; see [report branch README](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/README.md), [report template](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/REPORT_TEMPLATE.md), and [eight schedule prompts](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/SCHEDULE_PROMPTS.md). Scheduling details are in [Studio setup guide](docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md).

**Every scheduled invocation must re-read these central files from `main`**, then fetch actual earlier reports explicitly using `ref=agent-reports`. Source-of-truth mathematics NEVER comes from the reports branch. The seven agents post eight uniquely named files per day: `00-coordinator-am.md`, `10-owner-payment.md`, `20-analytic-type-ii.md`, `30-finite-wheel.md`, `40-prime-census.md`, `50-adversarial-referee.md`, `60-lean-verification.md`, `90-coordinator-pm.md`. By default, every scheduled agent may write only its assigned daily Markdown report to `agent-reports`, with explicitly authorized GitHub write access. **Exception:** `RH | Lean Verification` may additionally create/update its own `agent/lean-verification/` proof feature branches and associated draft pull requests targeting `main` under the proof-promotion policy below. This does not authorize direct writes to `main` or merges. Broad read/write connector privileges (even without delete ability) do not technically enforce branch/path restrictions.

The evening Coordinator fetches the seven upstream report paths, reconciles exact claim IDs and evidence, records `PENDING`/not-published stages instead of inventing handoffs, and publishes a dated verified synthesis. The 17:00 Lean Verification stage independently formalizes qualified results, performs authorized proof-branch and PR work, and uses **GitHub Actions on the proof PR as its only Lean execution environment** (no local Lean compilation); it reports observed CI/compiler results and PR status to the 19:00 Coordinator. A plan to post files is NOT a complete automated cycle until schedules, write credentials, actual report commits and readbacks have been verified. No scheduled agent may write directly to `main`, merge, or enable auto-merge; the repository owner retains final merge authority.

### Seven-agent write authorization and proof promotion

**Connector capability is not authorization.** Even if all seven agents have repository-wide GitHub read/write rights except deletion, their permitted actions are restricted here. Prompt instructions do not create technical branch/path restrictions; maintain `main` protection and enforce least privilege where available. The `agent-reports` README governs the default reporting lane; this section is the explicit additional proof-branch exception for Agent #7 only, once merged into `main`.

| Scheduled agent | Permitted routine GitHub writes |
| --- | --- |
| Research Coordinator | Its own `00-coordinator-am.md` and `90-coordinator-pm.md` on `agent-reports` |
| Owner Payment | Its own `10-owner-payment.md` on `agent-reports` |
| Analytic Type II | Its own `20-analytic-type-ii.md` on `agent-reports` |
| Finite Wheel & Incidence | Its own `30-finite-wheel.md` on `agent-reports` |
| Prime Census Laboratory | Its own `40-prime-census.md` on `agent-reports` |
| Adversarial Referee | Its own `50-adversarial-referee.md` on `agent-reports` |
| Lean Verification | Its own `60-lean-verification.md` on `agent-reports`; plus scoped proof-branch/PR operations below |

Each daily report is filed under `research/agent_reports/YYYY-MM-DD/` using `America/New_York`. Read real predecessor files at `ref=agent-reports`; absent files are `PENDING`, not evidence of a completed stage. To update an existing report, fetch its blob SHA, preserve old content, append dated findings, commit explicitly to `agent-reports`, and re-fetch to verify the commit. On failure state `NOT_PUBLISHED` and provide full report text. No agent may overwrite another's report or merge the reporting branch into `main`.

### Lean Verification proof-promotion exception (effective only after merger of this policy)

`RH | Lean Verification` owns the end-to-end **formalization → draft PR → GitHub Actions Lean CI → CI repair → human-review handoff** for independently justified new mathematical results. **GitHub Actions triggered by its proof PR is the sole Lean build/test environment for this agent.** Agent #7 does not execute Lean locally, does not need local Lean/Mathlib installation, and must not make missing local command execution a blocker when PR CI is available. Once this authorization is on `main` and actual feature-branch/PR write tools are available, routine implementation and draft PR creation need no additional per-claim human permission. **Only the repository owner or an expressly authorized human may merge; the agent must not merge or enable auto-merge.**

At the 17:00 ET daily run (including weekends), and for directly authorized implementation requests:

1. **Refresh authority and queue.** Fetch current `main:AGENTS.md`, `main:CURRENT_PROOF_CONTRACT.md`, actual `main` commit SHA, relevant original Lean declarations, pinned Lean/Mathlib revisions, and existing open proof PRs. Search for duplicates before proposing an implementation.
2. **Read all six earlier daily reports**, if present: `00-coordinator-am.md`, `10-owner-payment.md`, `20-analytic-type-ii.md`, `30-finite-wheel.md`, `40-prime-census.md`, `50-adversarial-referee.md`. Keep their original claim IDs and adversarial objections. Mark absent or unpublished handoffs `PENDING`. Independently assess available findings even if some reports are absent.
3. **Verify the mathematics.** Restate exact quantifiers, original carriers, weights and hypotheses. Audit proof dependencies, circularity, RH-equivalent assumptions and source bridges. A legitimate supporting lemma can qualify even if it does not prove RH; a conditional consumer does not prove its open premise.
4. **Implement on an isolated feature branch.** Reuse a suitable already-open proof PR if possible. Otherwise create a branch from fresh `main` named `agent/lean-verification/YYYYMMDD-claim-slug`. Commit a complete, focused Lean proof attempt, necessary supporting imports/tests, and directly related proof documentation. Keep unrelated source, central proof contracts and `AGENTS.md` unchanged. No local Lean execution is expected or required.
5. **Open a draft PR targeting `main` to obtain real Lean execution.** Include claim IDs, exact theorem declarations, dependencies, report links, intended CI checks and known gaps. Opening the PR and pushing subsequent commits should trigger the repository's GitHub Actions verification; confirm that a workflow actually starts on the exact PR head SHA. If draft PRs do not trigger the required workflow, do not bypass branch protection or misrepresent the proof: mark `BLOCKED_CI_NOT_TRIGGERED` and report the obstruction. Do not commit `sorry`, `admit`, unproved axioms, unproved source-payment assumptions or masked placeholders.
6. **Verify exclusively through PR GitHub Actions CI.** Poll or fetch actual PR workflow runs and job logs, including Lean compilation on the pinned toolchain, warning-fatal checks, proof-inventory/dependency audits, root/import and public-export checks, terminal-axiom audits and every required workflow. Record workflow/run/job URLs, exact tested head commit SHA, commands reported in logs, pass/fail conclusions, warnings, theorem declaration and axiom evidence. `CI_PENDING`, a missing job, or a green unrelated documentation job is **not** verified Lean compilation. Never fabricate compiler or CI evidence.
7. **Repair and continue from CI logs.** Read failed GitHub Actions job diagnostics, identify the error, update only the proof feature branch, push a focused fix, and verify that CI runs again on the new head commit. Repeat until all required checks pass or an exact mathematical/technical blocker is identified. Asynchronous CI may outlast the daily run; retain the existing draft PR and carry its state to the next run. Avoid duplicate PRs and weakening CI to manufacture success.
8. **Mark ready for human review only after verified PR CI.** Require a complete independently justified theorem, actual green relevant Lean and axiom checks on the **latest proof PR head commit**, no hidden proof gaps, and a candid account of missing external referee review. Never directly modify `main` or merge.
9. **Publish `60-lean-verification.md`** to `agent-reports` with claim IDs, PR numbers/URLs and head SHAs, executed checks, mathematical status, CI state, pending objections and remaining obligations. The 19:00 Coordinator must check actual PR status and separate research reports from merged theorems.

Allowed code writes are confined to `agent/lean-verification/` feature branches and their associated PRs; the report write remains confined to Agent #7's assigned dated Markdown file. Other six agents remain report-only. Forbidden actions include pushes to `main`, merge/auto-merge, deletions, edits on unrelated branches, modifications to other agents' reports, changes to central instructions/contracts, permissions or CI policies, and circumvention through low-level Git operations.

Track **mathematical** states (`PROVED_IN_LEAN`, `PAPER_PROOF`, `FINITE_COMPUTATION`, `CONDITIONAL`, `REFUTED`, `NO_NEW_RESULT`, `BLOCKED`) separately from **PR** states (`DRAFT_PR`, `CI_PENDING`, `CI_FAILED`, `CI_GREEN`, `REVIEW_READY`, `MERGED`). An unverified proof in a draft PR is not `PROVED_IN_LEAN`; `PROVED_IN_LEAN` requires relevant real GitHub Actions Lean CI evidence at the exact source SHA and an acceptable axiom audit. A green conditional theorem does not establish its unproved antecedent. If no valid theorem is ready, audit/repair existing PRs or report `NO_NEW_THEOREM_TO_FORMALIZE` rather than creating filler PRs.

**First candidate, not a frozen assignment:** inspect `20261012-wheel-1`, the proposed subdoubling late-owner fibre bound of two, with its block/run corollaries and any newer counterevidence. If independently justified and not already implemented, it is eligible for a focused formalization PR; the improved unit-weight census is not an RH proof or the original signed VF source-payment bound.

## Mandatory public VF canonicalization — 2026-10-12

**NEW SINGLE PUBLIC DEFINITION:** On x>=4,
\[
VF(x)=vfCanonical(x)=vfMid(x)+\sqrt2.
\]
Square endpoint \(VF(R^2)=vfMidFinishedMass R+\sqrt2\).
The only public integer step is the DERIVED floor of that REAL height.
The actual-prime endpoint defect is
\(D_R^{can}=\pi(R^2)-VF(R^2)=D_R^{raw}-\sqrt2\).
Lean canonical modules: VF_CANONICAL_ALL_REAL_LI_O_ONE,
VF_CANONICAL_SQRT_TWO, VF_CANONICAL_SQRT_TWO_VON_KOCH;
full [mandatory coordinate autopsy](research/VF_CANONICAL_SQRT_TWO_AUTOPSY_2026_10_12.md).

- **Supersession concerns all NEW public names/plots and the canonical proof goal.** Do not bulk-rename, redefine, or mutate OLD vfMid, original physical weights, owner-cell source, formal theorem signatures or their historical exact x=9 anchor: they remain LEGACY implementation. Always transport with explicit exact Lean theorems.
- **O(1) on ALL REAL x>=4 is unconditional** from the pre-existing square O(1), live-band O(1), and the exact decomposition; DO NOT revert to the obsolete all-real O(sqrt x) description as the strongest theorem. CI is required to certify the newly assembled Lean theorem.
- Li baseline is Li_2=int_2^x dt/log t. Standard principal-value li differs by fixed li(2). Never conflate these height normalizations.
- The canonical statement VFCanonicalSquareVonKochStatement is equivalent as an existence assertion to the old raw VFMidSquareEndpointVonKochBoundedStatement. Actual-prime inclusion is OPEN. Classical von Koch/RH remains an explicit ClassicalVonKochRHCriterion parameter.
- sqrt2 is a user-chosen FIXED vertical phase, NOT the historical exact anchor 4-5/log(13/2), and NOT a theorem of universal pointwise approximation advantage.
- The correct translated **quadratic** energy is (D_raw-sqrt2)^2=D_raw^2-2sqrt2*D_raw+2. Never silently use a raw historical energy/first-bad denominator for a canonical first-bad source.
- Keep finite A/C's actual Mertens K_R and original floor kernel entirely distinct; phase alignment contributes nothing to their uniform signed upper estimate.

## Governing mathematical philosophy

Keep the proof as elementary as possible and faithful to the repository's Eulerian geometry. The fundamental arithmetic operation is adjoining a fresh prime coordinate.

The current non-negotiable ordering rule is:

**signed physical reassembly first; energy second.**

Prefer, in order:

1. exact finite identities;
2. sign-preserving reindexings, mate transfers, and involutions;
3. prime-by-prime parent/child or cube recursions;
4. signed global inequalities only after the exact cancellation structure is exposed;
5. recursive energy only after the signed child packet has been identified with the genuine lower-scale Mertens-visible object.

Do not replace a signed problem by an unsigned support count unless the loss is proved harmless for the stated target. Do not take absolute values, coefficient `L2` norms, or triangle inequalities before the final energy stage when doing so destroys a cancellation mechanism.

## Prohibited hidden assumptions

Do not assume or smuggle in any of the following:

- independence or pseudorandomness of Möbius signs;
- local `30/30` sign balance on an arithmetically selected carrier;
- transfer of global Möbius densities to a selected birth/death/escape population without proof;
- an RH-strength prime-gap, Mertens, covariance, or cancellation estimate under a weaker name;
- that a geometrically thin support has small signed mass;
- that a coordinate change itself supplies a quantitative estimate;
- that a periodic contact mask makes the physical Möbius observable periodic;
- that coefficient square mass is a recursive Mertens endpoint energy;
- that a scalar frozen-prefix identity automatically defines an unsummed physical field.

Global squarefree density may be used only where the carrier and theorem justify it. Preserve the distinction between exact zero-density/diagonal information and signed off-diagonal cancellation.

## Current common object

Several historically separate coordinate systems are compiled descriptions of the same signed endpoint/run arithmetic and should not be treated as independent analytic seams. These include the endpoint/interval, ordered Euler-cut, oriented Euler ledger, downcross, defect, prefix-lifetime, transport, and square-root prime-wheel descriptions documented throughout the repository.

For the preserved exceptional-owner `q^2` descent, the critical distinction is between:

- the true physical coefficient daughter produced by parent/current-response/first-power-mate compensation;
- the signed packet obtained only after earlier-owner and second-contact reassembly;
- the lower-scale Mertens-visible recursive packet;
- unsigned coefficient square mass, which is a different object.

Consult `CURRENT_PROOF_CONTRACT.md` for the exact active theorem target and the modules that already certify failed identifications.

## Required research discipline

Before proposing a new route:

1. Search the repository for an existing theorem on the same carrier.
   Use `python3 scripts/proofq.py repo-search '<terms>'` for full-source,
   statement, documentation, and script search; use `--scope research` for
   staging modules. The default library `proofq search` is not exhaustive over
   the repository. Follow [repository search](docs/REPOSITORY_SEARCH.md) when
   including fetched PR refs, and inspect import dependencies with
   `python3 scripts/repo_index.py module <module-or-path> --transitive`.
   Search hits are source navigation; confirm compilation and hypotheses
   against the relevant source and successful workflow at its exact commit.
2. Identify the exact carrier, weight, endpoint convention, root parameter, owner convention, and whether the object is scalar, coefficient-level, or already reassembled.
3. State which compiled equality transports the proposed idea into the current common object.
4. Check the route against `CURRENT_PROOF_CONTRACT.md` and the recorded no-go modules.
5. If useful, falsify candidate identities or inequalities numerically on finite ranges before formalizing them. Numerical evidence is a filter only, never proof.
6. Prefer strengthening an existing theorem on the correct carrier over creating a parallel abstraction.
7. Before applying any norm or square, list every compensation, mate, earlier-owner, second-contact, and endpoint term that must already have been reassembled.

When a proposed quantitative argument uses a fresh prime `p`, keep the full signed parent/child structure intact long enough to determine whether the interior cancels, transfers owner, or descends. Track every boundary term explicitly.

## Known no-go patterns

Treat rediscovery of these as a failed branch unless a genuinely new signed ingredient is supplied:

- support-only frontier/capacity estimates that are a full power too large;
- naive same-prime leaf arguments on strict subdoubling square runs where top escape is the whole covariance;
- prime-gap spacing alone as a bound on the signed Mertens/frontier residual;
- diagonal density improvements presented as a substitute for signed covariance or cross-owner cancellation;
- converting birth/top-escape sets to cardinality bounds before exploiting their signed coupling;
- fixed finite-torus Möbius vectors that reuse one residue-class field value across different physical periods;
- inequalities identifying a positive coefficient `L2` mass with `M(Y)^2` at cutoffs where `M(Y)=0`;
- ownerwise squaring before transferring omitted higher-owner contacts to their signed earlier-owner mates;
- using the `q^{-2}` branching budget as though it supplied the missing signed daughter-energy dictionary.

## Current quantitative objective (legacy raw source, equivalent to canonical sqrt2, updated 2026-10-12)

**Canonical:** The active direct VF-mid program remains the cumulative real-prime discrepancy
\[
|\pi(R^2)-VF_{\rm mid}(R^2)|=O(R\log R),
\]
with actual owner-admissible escape proved from a chronological **multi-block run**, not from a one-bad-child selector. The no-independent-persistence owner-cell cancellation and sector-six rank descent are already established infrastructure. Consume them; do NOT introduce a new general "no persistent correlation" or ergodicity hypothesis. The unresolved actual-prime seam is the original first-bad weighted source-to-compensated-boundary occurrence map and run-level signed late-owner correction. Check CURRENT_PROOF_CONTRACT.md before attempting new code.

**Sufficient alternative (#929):** Finite-C (the original Mertens bilinear \(Q_R=2M(R-1)-M(R^2-1)\)) and finite-A endpoint amplification are equivalent as existence claims and would imply RH through the existing conditional Lean consumer. They remain UNPROVED and are not a separate required gate for the VF proof. Read [the aligned finite A/C scope and assumptions audit](research/FINITE_A_C_VF_ALIGNMENT_2026_10_11.md) before changing this route.

- Never re-label the equivalent \(\Gamma_R\le BR^2 K_R\) live signed-pair inequality as a new known bound; the diagonal is controlled, the POSITIVE reassembled cross-family Gram is not.
- Never apply global \(6/\pi^2\) squarefree density, fixed-prime multiplicative sign purity, or fixed-T gcd-sector asymptotics to a selected growing first-owner/run carrier without a uniform transfer theorem. The live interaction is a PAIR sum, not an integer population.
- No same-prime parent/child edge occurs between *distinct simultaneously live* odd packets of \((x/2,x]\). Such exact opposite signs are historical/future generation transport, not already-paid endpoint covariance.
- Root-relative period/CRT phase independence and near-zero fixed-lag Pearson/Spearman/Kendall are diagnostics, NOT worst-case control of multiplicative signed ancestry at physical square endpoints.
- Opposite terminal-owner / seed contributions may be individually much bigger than the target \(R\sqrt{K_R}\). Reassemble the original source, its weights, cross terms, clips and both walls **before** norming or comparing it to the target.

**Preserved older alternative:** CORR-4 remains an open sufficient route with its own compiled conditional Stokes/remainder consumer; the #797–#800 identity-family search freeze still applies. Do not describe CORR-4 as the current required canonical theorem.

The acceptance test for any new step is a genuinely INDEPENDENT quantified arithmetic inequality on the exact original physical carrier or an actual-source-to-recursive-run matching theorem. A density computation, algebraic reformulation, one-owner sign, finite graph, or a conditional theorem with its input left open is NOT RH closure.

## Lean and repository rules

- The general instruction to work on branches and submit PRs applies only to actors authorized for source changes. The six non-Lean scheduled specialists remain report-only; only Agent #7 has the additional proof-branch exception above, which takes effect on `main` after the reviewed policy merge.
- Keep daily agent reports separate from implementation PRs. Neither a report nor an unmerged draft PR establishes a new kernel-verified theorem in `main`.

- Never use `sorry`, `admit`, `axiom`, or a project-local assumption to close a mathematical gap.
- Do not weaken a theorem merely to make it compile without explicitly documenting that the mathematical target changed.
- Keep changes localized and reuse existing definitions and theorem names where possible.
- Work on a branch and submit changes through a PR unless explicitly instructed otherwise.
- If a new `.lean` module is added, update the generated/root import surface as required by repository CI.
- Run the relevant Lean build and repository audits. **For Agent #7, execute these exclusively in GitHub Actions CI on the proof PR, never locally; inspect the actual workflow jobs/logs and match every result to the tested commit SHA.** Treat owned warnings as failures.
- Preserve the proof inventory, exact elaborated declaration graph, root import audit, public export audit, and terminal axiom audit.
- Preserve obstruction and finite-counterexample modules as regression tests even when a route is abandoned.
- When a false identification is discovered, prefer an executable Lean counterexample or impossibility theorem over prose alone.
- The terminal forward theorem must retain only the existing standard classical axioms reported by `RHLean/Proof/TerminalAxiomAudit.lean`.

## Definition of progress

Structural progress means a new exact identification, compensation, mate transfer, signed reindexing, cancellation, or reduction that strictly narrows the remaining quantitative seam on the physical carrier.

Quantitative progress means a proved inequality for the correctly reassembled signed object that improves the required scale and composes with the recursive energy/terminal bridge.

Do not label a restatement, coordinate rename, support bound, mask norm, torus spectral calculation, unsigned coefficient estimate, or heuristic cancellation as closure.

**Implementation progress:** A new independently justified result is implemented in a focused feature-branch PR, verified by **GitHub Actions Lean CI on that PR** and required axiom audits, and submitted for human review. A review-ready PR is not `MERGED`: only an approved human merge adds it to `main`.
