# RH_Lean daily multi-agent research ledger

**Branch:** `agent-reports` (**not** `main`).
**Reports root:** `research/agent_reports/`.
**Timezone/date for filenames:** `America/New_York`, ISO `YYYY-MM-DD` (including weekends).
**Schedule:** the user reports two scheduled runs per agent per day, including weekends. Coordinator's AM/PM files cover its two logical phases; other specialists may append a second run to their existing named report. The eight names below are **logical report files, not a limit of eight invocations**. Actual additional start times are configured in Agent Studio and must be verified there.
**Authorization:** this branch/folder is a proposed workflow; creating it does NOT grant Workspace Agents GitHub write access or set schedules. Configure and authorize those separately.

## Source of truth (never reverse this precedence)

1. Live `main:AGENTS.md` governs agent conduct and where to find current directions.
2. Live `main:CURRENT_PROOF_CONTRACT.md` defines the current research objective.
3. Actual compiled Lean source and verified CI establish what is proved.
4. This ledger records dated, independently reproducible work, *not* proof authority.
5. Draft PRs, historical papers/notes, and agent memory provide context. They do not override the two live central files.

On **every** scheduled run, use GitHub to read both central files at current `main`, report the observed main HEAD SHA, and redirect your stable mathematical specialty to the *latest* objective. Read relevant reports from **both today and the preceding calendar day (America/New_York)** on this branch, even when today's files exist; never assume another agent finished. Resolve cross-midnight handoffs by verified run timestamps, not filenames alone.

## External/direct research inbox — required live handoff check

**Read [EXTERNAL_HANDOFFS.md](EXTERNAL_HANDOFFS.md) on `ref=agent-reports` during every scheduled run**, after the mandatory fresh `main` authority reads and today's/yesterday's stage-report handoffs. It indexes user-authorized **outside-session research** not automatically present in the eight named Workspace Agent reports. Inspect any applicable new claim's linked dated source, mathematical status, exact input SHA, and reproducer before allocating computation or opening another proof PR. Cite the external claim ID and whether you accepted, revised, rejected, or deferred it in your **own** next report. This prevents merged PR work or independently discovered paper research from being silently missed.

External handoffs do **not** replace scheduled agent reports, bypass Adversarial Referee review, authorize edits to another agent's file, imply automatic synchrony, or change the active `main` proof contract. Only independently verified Lean/CI work is `PROVED_IN_LEAN`; finite tests and paper estimates retain their own status. Publication by a user-directed external session is confined to a distinct `external/YYYY-MM-DD/` subfolder plus the inbox index, not the eight reserved daily stage files.

## Required daily folder and reporting order

```text
research/agent_reports/YYYY-MM-DD/
  00-coordinator-am.md         07:00 ET  goals, base SHA, previous-day handoff
  10-owner-payment.md          08:00 ET  original arithmetic specialist
  20-analytic-type-ii.md       09:00 ET  analytic methods specialist
  30-finite-wheel.md           10:00 ET  finite sieve/incidence specialist
  40-prime-census.md           13:00 ET  independent computation & falsification
  50-adversarial-referee.md    15:00 ET  adversarial review
  60-lean-verification.md      17:00 ET  formal proof/CI audit or explicit blocker
  90-coordinator-pm.md         19:00 ET  verified synthesis, next priorities
```

These are the original **handoff anchor times**, not a dependency-controlled schedule or an exhaustive list of the additional configured launches. Scheduling alone does not create files; every invocation must commit its own report to `agent-reports` and verify the readback. Twice-daily invocations of the same specialist use the **same dated filename**, appending a timestamped new run and a refreshed resume capsule rather than creating conflicting alternate names or deleting earlier findings.

## Twice-daily warm-start and cache-validity protocol

Each invocation must do **new work or a verified continuation**, rather than repeat the same exploratory search automatically. Before expensive searches, scans, experiments or Lean CI:

1. **Check live authority first:** fetch current `main:AGENTS.md`, `main:CURRENT_PROOF_CONTRACT.md` and actual `main` HEAD SHA on EVERY run, even on a cache hit. A cached summary never replaces these files or actual compiled Lean/CI.
2. **Mandatory two-day rolling handoff:** for your own logical stage AND each relevant upstream stage, check **both today's and yesterday's dated report paths**, using the actual `America/New_York` calendar date and `ref=agent-reports`. Read the latest verified run section and `## Next-run resume capsule` in both available files, even if today's stage has already published. Prefer the newest applicable handoff by **actual execution/publication timestamp**, not by filename alone; keep earlier verified claims for context. Record each consumed path, blob SHA, timestamp, and claim IDs.
   - If today's upstream file is absent, report **`TODAY=PENDING; YESTERDAY=CARRY_FORWARD`** with the verified prior-day reference, rather than treating the stage as having no research. Yesterday's findings remain yesterday's findings: do not mark today's stage `COMPLETED` or invent a current-day run.
   - After a longer interruption, consult the latest older verified report as an explicitly dated fallback. Always revalidate its Lean dependencies, claims, contract, PR state, and exact source before reusing it.
   - An overnight run may consume yesterday's late Owner/Analytic/Coordinator results together with today's early Wheel/Census/Referee results. Do not require chronological handoffs to fall in the same folder or assume a 07:00 Coordinator report already exists shortly after midnight.
3. **Invalidate selectively:** compare recorded `main` SHA, relevant source blob SHAs, theorem statements, upstream report SHA/claim IDs, experiment code/input hashes, and (for Agent #7) proof PR head SHA and CI run status. A changed proof contract or relevant dependency requires revalidation. An unchanged unrelated file does not justify rebuilding unaffected mathematical or software work.
4. **Reuse verifiable completed work:** preserve exact results, counterexamples, reproducible commands, finite tested ranges, literature references, and prior accepted/rejected claim IDs **without re-running them** if all their dependencies still match. Revisit only on a changed premise, reproducibility issue, new candidate, or useful wider range. A prior negative result remains a negative result with its original precise scope.
5. **Spend time on the next gap:** prioritize the first unresolved theorem/experiment, new upstream claim, referee objection, or failed CI job. Avoid full-repository reindexing and repeated large prime/Möbius scans when an unchanged source-specific index or independently verified computation already exists.
6. **End each run with a concise checkpoint:** append a timestamped run section and a new `## Next-run resume capsule` (target approximately 250–500 words). Include run ID/date, observed main SHA, crucial source/contract blob SHAs, latest consumed upstream report SHAs and claim IDs, completed proof/experiment evidence, exact outstanding blocker, highest-value next action, and Agent #7 PR/head SHA/CI job URLs when applicable. State which cached claims remain verified versus require revalidation. Do not save secrets or misleading proof conclusions.
7. **Report efficiency:** identify reused versus invalidated work, relevant CI cache hit/miss evidence if observed, and whether expensive computation or a full build was skipped safely. Do not invent saved minutes, cache hits or cost estimates.

**Agent #7 uses GitHub Actions CI on proof PRs, not local Lean execution.** Reuse the existing pinned Mathlib/StrongPNT/RHLean/research-closure Actions caches. Read the exact PR head SHA and CI workflow/job states before doing anything expensive. Do not push a no-op change or rerun green CI on unchanged code; reuse checks tied to the exact unchanged head SHA. For a failed CI run, fix only the diagnosed failure and rely on the next PR commit's CI; for pending CI, carry forward the run URL rather than spinning or claiming completion. A draft PR that does not trigger required Lean CI is `BLOCKED`, not verified.

**The latest capsule is navigation and continuity, not proof authority.** It cannot replace current source, theorem assumptions or kernel evidence. Maintain full historical report sections and claim provenance. Concurrent runs must re-fetch blob SHA and reconcile/retry one GitHub conflict without deleting prior content.

## Best-effort partial reports and usage-limit resilience

The user's preference is **research continuity over all-or-nothing runs**. When an agent invocation starts and has working GitHub write access, it must **publish a small useful checkpoint early** (after refreshing authoritative `main` files and reading its available predecessor reports, but **before** expensive computation, lengthy browsing, large repository audits or Lean PR CI waiting). Publish to its **one assigned date-and-stage file** with the exact observed `main` commit SHA, actual timestamp/run ID, current objective, report/claim IDs consumed, first concrete pending task, and honest status `IN_PROGRESS` / completeness `PARTIAL`. These are execution states, not mathematical proof claims. Never populate unsupported research results. Fetch blob SHA and preserve previous run content.

Then **append substantive findings as soon as they are established**, rather than deferring all writing until the very end. A final best-effort update should include completed evidence, failures, and a short next-run resume capsule. Avoid excessive GitHub writes; aim for an initial checkpoint, meaningful-result update when available, and a final completion or handoff update.

If a five-hour allowance or other usage/spending limit interrupts a run, **do not claim a completed task or an automatically generated later report**. The already-committed checkpoint is the durable partial output. The next eligible agent invocation (if permitted to start by its account/workspace usage limits and available credits) reads that checkpoint and continues. Scheduling does **not** bypass shared usage limits; if launch is blocked before any report is written, no report can be guaranteed. Mark missing handoffs `PENDING` until an actual GitHub commit exists. Do not invent a future run, backdate reports, or assume credits are available. Check Scheduled/Agent run history for skipped, blocked, or incomplete invocations.

## Exact read/write protocol

- At the start: read `AGENTS.md` and `CURRENT_PROOF_CONTRACT.md` with `ref=main`, and read relevant Lean files on `main`. Record the observed main commit SHA, not a guessed SHA.
- Read relevant **today AND yesterday** stage files at `ref=agent-reports`, using the eight deterministic names above; compare latest verified run timestamps across midnight. The morning Coordinator must read yesterday's `90-coordinator-pm.md` if available. Explicitly distinguish `TODAY=PENDING` from a verified prior-day carry-forward; do not treat a missing file as a zero finding.
- Compose an original report following [REPORT_TEMPLATE.md](REPORT_TEMPLATE.md). Every named run posts a report, **including negative/no-change/blocked runs**. Include evidence links and exact theorem statements; no unsupported proof claims.
- Create ONLY your assigned file via GitHub's contents API with `branch=agent-reports`. Do NOT create/modify `main`, Lean source, central instructions, other agents' reports, or any unrelated path. If rerunning the same stage/date, fetch its existing blob SHA first and update **only that same file**, appending a new timestamped section and preserving prior reports.
- On a GitHub write conflict (409/422), re-fetch that day's file and branch, reconcile without deleting another run's entries, and retry once. On permission denied or write failure, clearly declare `NOT_PUBLISHED`, return the exact report text to the user, and tell the coordinator the handoff was unavailable. Do not claim a report was committed until GitHub returns a successful commit SHA and the file can be fetched back.
- **Do not publish confidential data or user identifiers** in reports. Be aware that repo-scoped GitHub permission is **not** automatically limited to this directory just because these instructions say so; least-privilege authorization or a separately enforced posting intermediary is needed for truly restricted unattended writes.
- The Coordinator must validate which files are actually present. Missing or incomplete upstream research is `PENDING`, not completed. The Lean step may legitimately report `NO_NEW_THEOREM_TO_FORMALIZE`, but must not fabricate a Lean compile.
- The final 19:00 report includes a stage-completion matrix, accepted findings with evidence, refutations, open obligations, carry-forward items, and proposed `AGENTS.md`/contract updates for **human review**, not automatic edits.

## Naming, status, and handoff discipline

Statuses are `PROVED_IN_LEAN` (verified SHA/CI), `PAPER_PROOF` (unverified formalization), `FINITE_COMPUTATION`, `CONDITIONAL`, `CONJECTURE`, `REFUTED`, `NO_NEW_RESULT`, `BLOCKED`, `PENDING`, and `NOT_PUBLISHED`.

For a claim, give a stable local claim ID (e.g., `20261013-owner-1`), its full quantified statement and exact original arithmetic carrier, input hypotheses, independent new ingredient (if any), reproducer or proof, counterexamples sought, and first unresolved lemma. The referee/Lean verifier uses those IDs and must never infer proof from a narrative.

No branch report should be merged into `main` merely for archival convenience. A genuinely proved theorem follows the ordinary reviewed proof PR path. Reports remain on `agent-reports`; a coordinator may propose a separate reviewed update to the living proof contract.

[Use the template](REPORT_TEMPLATE.md) and [eight stage-specific schedule prompts](SCHEDULE_PROMPTS.md).

## Status as of initial setup

The reporting branch and templates are available. **No daily scheduled Workspace Agent runs, report-posting permission, shared report writes, or agent-to-agent handoff execution have been verified by this branch setup.** They must be enabled and tested in Agent Studio.
