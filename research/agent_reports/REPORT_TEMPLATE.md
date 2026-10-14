# RH_Lean agent daily report — [DATE / AGENT]

> This is a TEMPLATE, not a generated research result. Copy into your assigned dated filename; do not alter this template.

## Provenance

- **Report date (America/New_York):** YYYY-MM-DD
- **Agent / stage:** RH | [NAME] / [FILENAME]
- **Scheduled start:** HH:MM ET (actual configured slot; do not infer)
- **Run ID / sequence:** [ISO 8601 start timestamp with timezone and first/second/other run of this date]
- **Actual execution / completed time:** [ISO 8601 with offset]
- **Previous own checkpoint:** [report path, blob SHA and run ID, or NONE]
- **Warm-start cache status:** [reused/invalidated items, with exact source and proof dependency checks]
- **Observed `main` HEAD SHA:** [verified exact SHA]
- **Central contract fetched:** [main:AGENTS.md and main:CURRENT_PROOF_CONTRACT.md, success/failure]
- **Report target:** `agent-reports:research/agent_reports/YYYY-MM-DD/FILENAME.md`
- **Previous upstream reports actually read (today):** [paths, latest verified run timestamps, blob SHA, claim IDs or TODAY=PENDING]
- **Previous-day upstream continuity actually read:** [yesterday's relevant stage paths, latest verified run timestamps, blob SHAs, claim IDs; label YESTERDAY=CARRY_FORWARD when today's stage is PENDING; otherwise NONE]
- **Execution environment/tools used:** [GitHub read, GitHub write, web, code, Lean CI; verify each]
- **Publication status:** [INITIAL_CHECKPOINT / PARTIAL / COMPLETED / NOT_PUBLISHED, with actual verified GitHub commit SHA when published]
- **Early durable checkpoint:** [time and verified GitHub commit SHA, or NOT_PUBLISHED; state only work actually started]

## Current central research objective

[Literal concise restatement from current main. If it changed since yesterday, record the pivot and its source.]

## Work performed today

[New mathematics/reproduction, not repeated background. If blocked, specify the blocker.]

## Claims and evidence

### Claim YYYYMMDD-shortagent-1

- **Exact quantified statement and original carrier:** ...
- **Status:** PROVED_IN_LEAN / PAPER_PROOF / FINITE_COMPUTATION / CONDITIONAL / CONJECTURE / REFUTED / NO_NEW_RESULT / BLOCKED
- **Lean declaration or theorem reference, if any:** ...
- **Independent mathematical ingredient (not an equivalent reformulation):** ...
- **Proof, script, data or source reference:** ...
- **Attempted falsification / counterexamples:** ...
- **Precise first unproved lemma or limit:** ...
- **What changed relative to current known baseline:** ...

## Downstream handoff

- **Claims ready for census:** ...
- **Claims ready for independent referee:** ...
- **Claims ready for Lean (ONLY independently proved):** ...
- **Missing inputs or upstream stages:** PENDING or explicit refs.
- **Next action / priority:** ...

## Final report summary

**Net-new mathematical progress:** [specific theorem/estimate, or NONE]
**Completeness:** [DONE / DONE_NO_NEW_RESULT / PARTIAL / BLOCKED]
**No RH-proof claim:** [yes; unless independently verified complete proof with all checks]

## Next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** [ISO 8601 with offset, date-specific file]
- **Source freshness:** [main HEAD and crucial contract/relevant source blob SHAs; changed or unchanged]
- **Upstream consumed (two-day window):** [today AND yesterday: precise report paths, latest run timestamps, blob SHAs and claim IDs; distinguish TODAY=PENDING from YESTERDAY=CARRY_FORWARD]
- **Completed evidence worth reusing:** [theorems, experiments, finite ranges, result/code hashes, citations, exact statuses; no unsupported claims]
- **Invalidations / uncertain results:** [precise changed source/hypothesis/dependency or NONE]
- **First unresolved mathematical/CI blocker:** [one exact claim or job ID]
- **Next highest-value step:** [specific reproducible proof/experiment/review action]
- **For Agent #7:** [PR URL, head SHA, relevant Actions run/job URLs, latest CI/axiom state and required repair; no local Lean execution]
- **Avoid next run:** [unchanged scans, previously validated computations or green CI tied to the same source SHA]

For the second daily invocation, append its timestamped findings to this existing dated report and end with a **new final capsule**, preserving all earlier run sections. The latest capsule is a work checkpoint, not current mathematical authority.
