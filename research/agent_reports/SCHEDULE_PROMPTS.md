# ChatGPT Agent Studio: daily schedule instructions for the GitHub report branch

**Use one schedule for each role and two for Coordinator.** Set timezone to `America/New_York`, repeat `DAILY` (every calendar day). These prompts are meant for each agent's **ChatGPT-channel schedule**. This file does not create schedules or give tools/permissions.

## Mandatory shared preamble — prepend to EACH schedule instruction

> Execute today's designated RH_Lean daily-cycle stage. Fetch CURRENT `AGENTS.md` and `CURRENT_PROOF_CONTRACT.md` at latest `main`, record the exact current `main` commit SHA, and follow the CURRENT research objective over dated prompts/memory. Fetch real predecessor Markdown reports, if they exist, at `ref=agent-reports` in `research/agent_reports/YYYY-MM-DD/` where the date uses America/New_York. Use `research/agent_reports/REPORT_TEMPLATE.md` from `agent-reports`. On completion, CREATE your exact assigned report path using GitHub **branch=agent-reports**; if it already exists, fetch its blob SHA and update only that file without deleting prior data. Include exact claims, execution provenance, proof status, falsification and downstream handoffs; post a NO_NEW_RESULT/BLOCKED report if necessary. Verify GitHub returned a commit SHA and re-fetch the report. If access is read-only or posting fails, report NOT_PUBLISHED and present full report in the chat; never pretend downstream agents can see it. Never change `main` or merge. Do not fabricate missing stages, arithmetic proofs, test executions, Lean builds, or report commits.

## Eight scheduled actions

| ET time | Agent and filename | Append this stage-specific sentence |
| --- | --- | --- |
| 07:00 | #1 Coordinator / `00-coordinator-am.md` | Read yesterday's actual `90-coordinator-pm.md` if available; extract active objective from current main; give today a scoped falsifiable workplan. Publish `00-coordinator-am.md`. |
| 08:00 | #2 Owner Payment / `10-owner-payment.md` | Read `00-coordinator-am.md`, if present. Work independently on the current genuine-prime signed arithmetic/ancestry restriction, not on yesterday's permanently pinned theorem. Publish exact candidate claims and blockers. |
| 09:00 | #5 Analytic Type II / `20-analytic-type-ii.md` | Read morning goals, if present. Derive an independently proved arithmetic/analytic quantitative estimate relevant to the current objective, or identify the exact unresolved analytic hurdle. |
| 10:00 | #6 Finite Wheel / `30-finite-wheel.md` | Read morning goals, if present. Seek a new exact finite combinatorial/sieve restriction using original arithmetic incidence and signs, or a counterexample; do not double-count historical charges. |
| 13:00 | #4 Prime Census / `40-prime-census.md` | Read the three research stage files actually posted so far; reproduce and falsify explicit claims using actual primes/Möbius data. Include code/results and clearly distinguish executed tests from suggested ones. |
| 15:00 | #3 Adversarial Referee / `50-adversarial-referee.md` | Read morning goals, available three proposals and census results. Challenge precise claimed theorems, source bridges and proof strength; issue verdicts linked to claim IDs. |
| 17:00 | #7 Lean Verification / `60-lean-verification.md` | Read the referee and approved surviving candidates. If any new independent proof exists and an authorized executor is available, compile/audit Lean. Otherwise post NO_NEW_THEOREM_TO_FORMALIZE or BLOCKED, never simulated CI. |
| 19:00 | #1 Coordinator / `90-coordinator-pm.md` | Fetch all SEVEN earlier named files. Produce a stage-status matrix with links and claim IDs; synthesize verified discoveries, refutations, first open lemma, and next day's assignments. Missing outputs remain PENDING. Include whether the daily cycle was actually completed. |

## Practical caveats

1. GitHub access is read-only in the original agent configurations; actual shared reporting requires **expressly enabling authorized GitHub report-file writes**. Instructions alone cannot elevate connector permissions.
2. GitHub repository write credentials are not necessarily restricted by a prompt to a folder/branch. Prefer server-enforced least privilege when available. Otherwise ask for explicit approval of the operational risk or use a posting intermediary that enforces allowed paths.
3. Multiple simultaneous writers to one branch can create Contents API conflicts. The staggered times reduce but do not eliminate them; re-fetch, reconcile, retry once.
4. Scheduling is asynchronous, not a dependency engine. Do not assume an upstream file exists until successfully fetched.
5. New findings that matter to the formal RH proof move through ordinary reviewed code PRs. A research report is not equivalent to a proved Lean theorem.
