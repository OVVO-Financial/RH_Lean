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

### Centralized live assignment and PR discovery — no pinned Studio tasks

The seven Workspace Agents' **saved, durable Agent Studio Instructions are role specifications, not a priority queue**. They must contain permanent mathematical specialties, operating safeguards, GitHub permission boundaries, source-refresh rules, reporting filenames, and allowed proof-PR workflow—but **must NOT hard-code a particular PR number, research claim ID, dated campaign, first theorem, numerical test case, or named implementation target as a mandatory scheduled assignment**. Update the shared GitHub instructions and proof contract instead of repeatedly editing seven agents.

Every new direct research task and **every scheduled invocation** must resolve the assignment afresh:

1. Read the actual **current `main` HEAD** and fetch both `main:AGENTS.md` and `main:CURRENT_PROOF_CONTRACT.md`. Determine the live mathematical objective, including any express user-directed pivot. Read current original Lean source to distinguish what has actually been proved from what remains open.
2. Read relevant **latest actually committed** upstream agent reports and the agent's own previous `Next-run resume capsule` on `agent-reports`, with report/commit SHAs and original stable claim IDs. Missing stages remain `PENDING`; prior snapshots are historical continuity, not active commands.
3. Discover current relevant **open/draft PRs directly from GitHub**, checking each exact PR state, base/head SHA, diff/theorem declarations, CI status and last update. `AGENTS.md` may centrally nominate a current PR or research frontier, but **validate it against live GitHub and current proof contract** before acting. No PR number in an old instruction or report automatically determines current work.
4. Select the highest-value **still-open, independently justified** task matching the agent's permanent specialty: first unresolved mathematical lemma, new specific census/referee test, existing implementation PR repair, or a new formalization of a genuine supporting theorem. Avoid work already merged, refuted, superseded or delegated to another active PR. A clear direct user assignment takes priority when consistent with mathematical and repository safeguards.
5. Record the chosen objective and **dynamically discovered** claim IDs, PR numbers, source SHAs, and evidence links **in that run's report**, not in saved Studio Instructions. On the next run, independently recheck whether those facts remain current rather than treating a warm-start capsule as authority.

**Separate historical citations from operational assignments.** Dates, PR references and archived research examples in this repository's mathematical documentation are evidence of prior work; they are **not automatic instructions to reopen or implement that PR**. The active mathematical target is specified by the live proof contract, with this file governing the selection process. The authoritative status of an implementation comes from actual GitHub PR and CI records.

This applies to **all seven agents**, including the Research Coordinator and Lean Verification, on every actually configured invocation. Repository documentation does not create, double, or reschedule Agent Studio launches. If an existing saved Agent Studio instruction still contains a compulsory named PR or claim, remove that local clause; GitHub cannot remotely edit the saved Agent Studio text.

Initial ChatGPT Agent Studio campaign: [setup guide](docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md) and [research snapshot](research/CHATGPT_AGENT_STUDIO_FIRST_BAD_CAMPAIGN_2026_10_12.md). These are **dated starting assignments**, not higher-priority instructions than `AGENTS.md` and the current proof contract.

### Cross-session handoff inbox and logical no-narrowing screen (2026-10-14)

**Mandatory independent intake:** after the live `main` authority fetch and the **today-and-previous-day** dated agent reports, read `research/agent_reports/EXTERNAL_HANDOFFS.md` with `ref=agent-reports` and inspect relevant newest linked external handoffs. They contain user-directed research from outside scheduled agent runs. Check original claim IDs, theorem/PR state, exact sources and input SHAs, experiment reproducers, and independent referee objections. Report whether each relevant new claim was consumed, accepted provisionally, rejected, revised, or deferred; do not impersonate an absent scheduled stage, overwrite someone else's report, or treat the external index as proof authority. A newly merged proof PR is authoritative in `main` after checking its imported theorem; a merely CI-green open PR is **not yet a theorem on `main`**.

**No-narrowing test before assigning a supposed last lemma:** write the proposed claim with full quantifiers, fixed/existential constants, assumptions, and its original arithmetic carrier. Search exact compiled arrows in **both** directions between the proposed claim and `VFCanonicalSquareVonKochStatement`. If both directions are proved, label the candidate **TARGET-EQUIVALENT / REFORMULATION**, not a narrower independently paid theorem. If it is a stronger sufficient condition, identify the extra strength and check for unconditional impossibility before treating it as a required gate. A conditional consumer from an unproved premise is not an independently proved bound. A separately provable exact signed occurrence/source-to-ledger **identity** can still be useful; it must be distinguished from the RH-scale inequality one hopes to derive from it. This audit is methodological: it does not preclude new genuine arithmetic estimates or imply owner-based proofs are impossible.

**Current review queue, NOT standing implementation targets:** the 2026-10-14 direct research handoffs flag [PR #938](https://github.com/OVVO-Financial/RH_Lean/pull/938) (dyadic signed-late correction, tracking, and actual-prime owner-escape admissibility equivalent to the canonical endpoint bound) and [PR #939](https://github.com/OVVO-Financial/RH_Lean/pull/939) (the #915 payment's two-number reduction, first-bad content and fixed-constant envelope). Both had green PR CI on their submitted heads when reported, but must be rechecked against **live GitHub** before citing as merged, independently peer-refereed, or usable as `main` proof dependencies. Do **not** automatically reopen, merge, or reimplement either. The historical #915 source-payment proposition has the first-bad(2,R+1) hypothesis; on that hypothesis the compiled existing victory machinery forces the **strict opposite** of the requested payment inequality. Avoid presenting the payment as an independently available positive NNS budget.

**Exact denominator and sign discipline:** under the original raw implementation, `D_R=pi(R^2)-F_R`, `P_R` is the genuine block prime supply, `m_R` the midpoint block mass, `w_R=m_R/R`, and `beta_R=m_R+(1-2w_R)P_R` is the actual current odd-seat **absolute** charge. The compressed #915 objects are `Source(R)=D_(R+1)=D_R+P_R-m_R` and `TotalMass(R)=(|D_R|+beta_R)^2`, so payment reads `2*D_(R+1)^2 <= (|D_R|+beta_R)^2`. This algebra is not global independent owner-pair covariance and does not grant a second uncompressed historical denominator; any re-expansion must restore all historical cross terms and the exact original norm. Distinguish the additive public `sqrt(2)` phase from these frozen raw charges.

**Provisional no-go review:** external paper claim `EXT-20261014-5` argues `limsup (D_(R+1)^2/TotalMass(R)) = 1` using Littlewood oscillation and Brun-Titchmarsh, hence no **unconditional all-R** fixed strict-fraction payment for this unchanged denominator. **Status: PAPER_PROOF until independently checked; not a Lean theorem.** Do not confuse failure of a hypothesis-free bound with failure of the conditional first-bad strategy or with disproof of RH. Inspect the exact square-endpoint transfer and original norm before adopting any stronger assertion.

## Per-invocation warm-start and verification cache

**Every actually configured invocation must advance the next unresolved question rather than blindly rerun completed work.** The latest user-stated usage preference is **one scheduled run per agent per day**; the repository cannot inspect or change Agent Studio schedules. Check actual configured launches rather than inferring a second daily invocation. Use the live reporting-branch `README.md`, `REPORT_TEMPLATE.md`, and external research inbox to resume verified work.

1. **Refresh authority on every run.** Fetch current `main:AGENTS.md` and `main:CURRENT_PROOF_CONTRACT.md`, recording actual `main` HEAD SHA; old checkpoints cannot replace these mandatory reads. Check relevant source-file blob SHAs and exact theorem declarations before treating prior findings as still applicable.
2. **Resume the most recent verified work.** Read **both today and the preceding calendar day's** available own-stage and relevant upstream-stage reports using `ref=agent-reports` and `America/New_York`, compare actual publication timestamps and the latest `## Next-run resume capsule`, then check `EXTERNAL_HANDOFFS.md` and applicable recent outside-session files. Record consumed report/inbox blob SHAs, claim IDs and run timestamps. A missing current-day report remains `PENDING` even when yesterday is `CARRY_FORWARD`; it is not a completed stage.
3. **Invalidate precisely.** A changed proof contract, theorem signature, source dependency, coefficient system, experiment code/input hash, upstream claim, proof PR head SHA, or relevant toolchain/manifest may invalidate a prior result. Unchanged relevant inputs allow reuse of previously verified finite scans, citations, theorem inventories, and accepted/rejected claim IDs without rerunning them. Do not confuse the scope of a finite test with an all-scale theorem.
4. **Prioritize deltas.** Skip broad repository reindexing and identical prime/Möbius experiments when an unchanged, reproducible result already exists. Resume the first missing lemma, evaluate newly arrived upstream findings, expand a useful test range, diagnose a specific objection, or repair a real CI failure. Revalidate only what the change affects.
5. **Publish early, then append.** After refreshing current authority and available handoffs, publish an honest, minimally useful `PARTIAL` / `IN_PROGRESS` checkpoint to the assigned dated report **before** lengthy research, computation or proof-PR CI waiting. Record actual current objective, SHA, prior inputs, precise next task and run timestamp. Re-fetch its commit. This is an execution checkpoint, not proof evidence. As real progress emerges, append results; never wait until the end to publish all findings. The next invocation can continue from the last committed checkpoint even if the preceding run stopped unexpectedly. A usage or spending limit may also block future scheduled launches, so do not guarantee a report from an agent that never started or published.
6. **Maintain the same dated report.** Each invocation appends a timestamped run section to the same logical-stage file, preserving all previous evidence and appending an updated, concise `Next-run resume capsule`. Record source SHA and relevant blob/contract versions, upstream report and claim IDs, completed proof/experiment with reproducer or checksum, exact next blocker, top continuation action, and CI/PR head SHA and run IDs for Agent #7. Fetch current blob SHA; on conflict re-fetch/reconcile/retry once.
7. **Reuse actual PR CI results on unchanged sources.** Agent #7 executes Lean **only via GitHub Actions on its draft proof PR**. Check latest PR head SHA and workflow/job state first. Reuse required green Lean and axiom checks **only for that exact SHA** without pushing no-op commits or rerunning them. If CI is pending, record the run and do other useful work. If red, read the failing job logs and push a diagnosed repair; the next SHA must get new CI. Never claim a cache hit, verification, or saved time without actual evidence.
8. **Preserve existing GitHub Actions artifact caches.** Mathlib/`.lake/packages`, patched StrongPNT, native `.lake/build` and research `.olean` import closures are already cached with toolchain/manifest/source-sensitive invalidation. Reuse completed dependency artifacts after a failing leaf build; do not mix incompatible toolchain or source hashes or create redundant competing caches. Use observed cache-hit and actual duration data in the report if available.
9. **Treat checkpoints as navigation, not authority.** Revalidate source provenance, actual compiled Lean theorem statements, assumptions and CI evidence. The final capsule should make it possible for the next run to resume a concrete proof/experiment/CI job immediately, without changing any claim's epistemic status.

The earlier two-runs-per-agent schedule is **historical**; the later user-stated compute budget is **one run per agent per day** unless the user explicitly changes it. The existing eight filenames are **logical report stages**, not proof of eight launches or any number of coordinator invocations. Only Agent Studio establishes actual schedules; do not create, repeat, or infer extra launches. Preserve mathematical/PR status labels and the human-only merge gate.

### Daily seven-specialist research loop (when scheduled)

The **current user-stated budget is one scheduled invocation per specialist per calendar day**, including weekends if actually configured; all date grouping uses `America/New_York`. The Coordinator's historical AM/PM filenames are two **possible logical phases**, not mandatory twice-daily launches. Any unscheduled phase stays `PENDING` and should not be fabricated or auto-triggered. Exact launch times, enabled schedules and retries are Agent Studio state, not repository state. The daily inter-agent handoff is a dated Markdown report per logical stage on the dedicated `agent-reports` branch, under `research/agent_reports/YYYY-MM-DD/`; repeated runs, if explicitly configured later, append timestamped sections. See [report branch README](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/README.md), [report template](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/REPORT_TEMPLATE.md), [external handoff inbox](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/EXTERNAL_HANDOFFS.md), and [historical schedule prompts](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/SCHEDULE_PROMPTS.md). The [Studio setup guide](docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md) records original anchors but must not override the actual configured cadence.

**Every scheduled invocation must re-read these central files from `main`**, then fetch actual earlier reports explicitly using `ref=agent-reports`. Source-of-truth mathematics NEVER comes from the reports branch. The seven agents have eight uniquely named logical report files per day (not a limit on total runs): `00-coordinator-am.md`, `10-owner-payment.md`, `20-analytic-type-ii.md`, `30-finite-wheel.md`, `40-prime-census.md`, `50-adversarial-referee.md`, `60-lean-verification.md`, `90-coordinator-pm.md`. By default, every scheduled agent may write only its assigned daily Markdown report to `agent-reports`, with explicitly authorized GitHub write access. **Exception:** `RH | Lean Verification` may additionally create/update its own `agent/lean-verification/` proof feature branches and associated draft pull requests targeting `main` under the proof-promotion policy below. This does not authorize direct writes to `main` or merges. Broad read/write connector privileges (even without delete ability) do not technically enforce branch/path restrictions.

When an evening Coordinator run is **actually configured**, it fetches the seven available upstream report paths, reconciles exact claim IDs and evidence, records `PENDING`/not-published stages instead of inventing handoffs, and publishes a dated verified synthesis. The **historical** 17:00 Lean Verification and 19:00 Coordinator anchor times do not authorize an additional scheduled run. Every real Lean Verification invocation independently formalizes qualified results, performs authorized proof-branch/PR work, and uses **GitHub Actions on the proof PR as its only Lean execution environment** (no local Lean compilation). Its report records actual CI/compiler findings for whichever Coordinator run later consumes them. A plan to post files is NOT a complete automated cycle until schedules, write credentials, actual report commits and readbacks have been verified. No scheduled agent may write directly to `main`, merge, or enable auto-merge; the repository owner retains final merge authority.

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

### Lean Verification proof-promotion exception (authorized on current `main`)

`RH | Lean Verification` owns the end-to-end **formalization → draft PR → GitHub Actions Lean CI → CI repair → human-review handoff** for independently justified new mathematical results. **GitHub Actions triggered by its proof PR is the sole Lean build/test environment for this agent.** Agent #7 does not execute Lean locally, does not need local Lean/Mathlib installation, and must not make missing local command execution a blocker when PR CI is available. Once this authorization is on `main` and actual feature-branch/PR write tools are available, routine implementation and draft PR creation need no additional per-claim human permission. **Only the repository owner or an expressly authorized human may merge; the agent must not merge or enable auto-merge.**

At each actually configured Lean Verification invocation (the historical anchor was 17:00 ET), or for directly authorized implementation requests:

1. **Refresh authority and queue.** Fetch current `main:AGENTS.md`, `main:CURRENT_PROOF_CONTRACT.md`, actual `main` commit SHA, relevant original Lean declarations, pinned Lean/Mathlib revisions, and existing open proof PRs. Search for duplicates before proposing an implementation.
2. **Read the available real handoffs**, checking **both today and yesterday** for `00-coordinator-am.md`, `10-owner-payment.md`, `20-analytic-type-ii.md`, `30-finite-wheel.md`, `40-prime-census.md`, and `50-adversarial-referee.md`. Read `EXTERNAL_HANDOFFS.md` and relevant outside-session research files as a separate evidence lane. Preserve original IDs and adversarial objections; missing/unpublished stages remain `PENDING`, not completed by an external handoff. Independently assess findings even when some reports are absent.
3. **Verify the mathematics.** Restate exact quantifiers, original carriers, weights and hypotheses. Audit proof dependencies, circularity, RH-equivalent assumptions and source bridges. A legitimate supporting lemma can qualify even if it does not prove RH; a conditional consumer does not prove its open premise.
4. **Implement on an isolated feature branch.** Reuse a suitable already-open proof PR if possible. Otherwise create a branch from fresh `main` named `agent/lean-verification/YYYYMMDD-claim-slug`. Commit a complete, focused Lean proof attempt, necessary supporting imports/tests, and directly related proof documentation. Keep unrelated source, central proof contracts and `AGENTS.md` unchanged. No local Lean execution is expected or required.
5. **Open a draft PR targeting `main` to obtain real Lean execution.** Include claim IDs, exact theorem declarations, dependencies, report links, intended CI checks and known gaps. Opening the PR and pushing subsequent commits should trigger the repository's GitHub Actions verification; confirm that a workflow actually starts on the exact PR head SHA. If draft PRs do not trigger the required workflow, do not bypass branch protection or misrepresent the proof: mark `BLOCKED_CI_NOT_TRIGGERED` and report the obstruction. Do not commit `sorry`, `admit`, unproved axioms, unproved source-payment assumptions or masked placeholders.
6. **Verify exclusively through PR GitHub Actions CI.** Poll or fetch actual PR workflow runs and job logs, including Lean compilation on the pinned toolchain, warning-fatal checks, proof-inventory/dependency audits, root/import and public-export checks, terminal-axiom audits and every required workflow. Record workflow/run/job URLs, exact tested head commit SHA, commands reported in logs, pass/fail conclusions, warnings, theorem declaration and axiom evidence. `CI_PENDING`, a missing job, or a green unrelated documentation job is **not** verified Lean compilation. Never fabricate compiler or CI evidence.
7. **Repair and continue from CI logs.** Read failed GitHub Actions job diagnostics, identify the error, update only the proof feature branch, push a focused fix, and verify that CI runs again on the new head commit. Repeat until all required checks pass or an exact mathematical/technical blocker is identified. Asynchronous CI may outlast the daily run; retain the existing draft PR and carry its state to the next run. Avoid duplicate PRs and weakening CI to manufacture success.
8. **Mark ready for human review only after verified PR CI.** Require a complete independently justified theorem, actual green relevant Lean and axiom checks on the **latest proof PR head commit**, no hidden proof gaps, and a candid account of missing external referee review. Never directly modify `main` or merge.
9. **Append a timestamped invocation to `60-lean-verification.md`** on `agent-reports` with claim IDs, PR numbers/URLs and head SHAs, executed checks, reused versus invalidated findings, mathematical status, CI state, pending objections and remaining obligations. End with a new `Next-run resume capsule` for the next scheduled invocation. The 19:00 Coordinator must check actual PR status and separate research reports from merged theorems.

Allowed code writes are confined to `agent/lean-verification/` feature branches and their associated PRs; the report write remains confined to Agent #7's assigned dated Markdown file. Other six agents remain report-only. Forbidden actions include pushes to `main`, merge/auto-merge, deletions, edits on unrelated branches, modifications to other agents' reports, changes to central instructions/contracts, permissions or CI policies, and circumvention through low-level Git operations.

Track **mathematical** states (`PROVED_IN_LEAN`, `PAPER_PROOF`, `FINITE_COMPUTATION`, `CONDITIONAL`, `REFUTED`, `NO_NEW_RESULT`, `BLOCKED`) separately from **PR** states (`DRAFT_PR`, `CI_PENDING`, `CI_FAILED`, `CI_GREEN`, `REVIEW_READY`, `MERGED`). An unverified proof in a draft PR is not `PROVED_IN_LEAN`; `PROVED_IN_LEAN` requires relevant real GitHub Actions Lean CI evidence at the exact source SHA and an acceptable axiom audit. A green conditional theorem does not establish its unproved antecedent. If no valid theorem is ready, audit/repair existing PRs or report `NO_NEW_THEOREM_TO_FORMALIZE` rather than creating filler PRs.

**Dynamic initial and recurring candidate selection:** retrieve the live proof contract, the latest independently evaluated agent report claims, and all relevant open/draft Lean proof PRs. Prefer repairing a valid existing PR over creating a duplicate; otherwise formalize the highest-value independently justified supporting theorem. No particular historical candidate, PR, claim ID, or date is an implicit standing assignment. An improved positive census does not by itself pay the original signed VF source.

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
- using the `q^{-2}` branching budget as though it supplied the missing signed daughter-energy dictionary;
- presenting the conditional #915 fixed-2 first-bad inequality or a target-equivalent dyadic/owner-escape predicate as an already independent signed estimate;
- treating an isolated two-seat NNS/LPM-UPM calculation as the global original #915 zero-target covariance without the compressed `|D_R|` historical term and full cross-term restoration.

## Current quantitative objective (legacy raw source, equivalent to canonical sqrt2, updated 2026-10-12)

**Canonical:** The open public target is the genuine-prime square-endpoint estimate
\[
|\pi(R^2)-(vfMidFinishedMass(R)+\sqrt2)|=O(R\log R).
\]
The legacy raw-coordinate existence criterion is exactly equivalent, but its **fixed-K first-bad energy is not invariant** under the public additive phase shift. Historical owner-cell no-independent-persistence and Sector Six cancellations are infrastructure, not the missing quantitative theorem. The signed-late correction and structural owner-admissibility statements are **claimed to be target-equivalent by CI-green, still-unmerged PR #938**; #915's fixed-2 first-bad payment is likewise audited in **still-unmerged PR #939**. Recheck PR states and the precise Lean reverse implications before routing another open-ended owner-payment attack. An occurrence-preserving source-to-boundary identity may still be meaningful independent work; a sufficient **uniform signed bound** for the actual source remains open and is not paid by identity rewriting or unsigned wheel capacity. Check `CURRENT_PROOF_CONTRACT.md` and the external inbox before proposing code.

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

Structural progress includes a new exact identification, compensation, mate transfer, signed reindexing, cancellation, or reduction on the original physical carrier, with provenance and an **independent new mathematical ingredient**. An identity need not by itself imply RH to be valid research progress; do not report its intended RH-hard quantitative consequence as already proved.

Quantitative progress means a proved inequality for the correctly reassembled signed object that improves the required scale and composes with the recursive energy/terminal bridge.

Do not label a restatement, coordinate rename, support bound, mask norm, torus spectral calculation, unsigned coefficient estimate, or heuristic cancellation as closure.

**Implementation progress:** A new independently justified result is implemented in a focused feature-branch PR, verified by **GitHub Actions Lean CI on that PR** and required axiom audits, and submitted for human review. A review-ready PR is not `MERGED`: only an approved human merge adds it to `main`.
