# RH_Lean daily multi-agent research ledger

**Branch:** `agent-reports` (**not** `main`).
**Reports root:** `research/agent_reports/`.
**Timezone/date for filenames:** `America/New_York`, ISO `YYYY-MM-DD` (including weekends).
**Schedule:** one complete seven-agent cycle every day, with eight scheduled runs because Coordinator starts and ends the cycle.
**Authorization:** this branch/folder is a proposed workflow; creating it does NOT grant Workspace Agents GitHub write access or set schedules. Configure and authorize those separately.

## Source of truth (never reverse this precedence)

1. Live `main:AGENTS.md` governs agent conduct and where to find current directions.
2. Live `main:CURRENT_PROOF_CONTRACT.md` defines the current research objective.
3. Actual compiled Lean source and verified CI establish what is proved.
4. This ledger records dated, independently reproducible work, *not* proof authority.
5. Draft PRs, historical papers/notes, and agent memory provide context. They do not override the two live central files.

On **every** scheduled run, use GitHub to read both central files at current `main`, report the observed main HEAD SHA, and redirect your stable mathematical specialty to the *latest* objective. Read the appropriate previous reports from this branch; do not assume they exist or that another agent finished.

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

These are eight **independent launch times**, not a guaranteed dependency-controlled workflow. Scheduling alone will not create the files. Each agent must successfully use a GitHub create/update-file action targeted at branch `agent-reports`; read-only GitHub cannot publish reports.

## Exact read/write protocol

- At the start: read `AGENTS.md` and `CURRENT_PROOF_CONTRACT.md` with `ref=main`, and read relevant Lean files on `main`. Record the observed main commit SHA, not a guessed SHA.
- Read **today's** prior files at `ref=agent-reports`, using the eight deterministic names above. The morning Coordinator additionally reads **yesterday's** `90-coordinator-pm.md`; do not falsely treat a missing file as a zero finding.
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
