# RH_Lean multiple-daily agent invocation policy — 2026-10-31

**User-directed operational policy; effective only after human merge into `main`.** This changes cadence authorization, not theorem status, source mathematics, roles, report ownership, Agent Studio settings, permissions, or the human-only merge gate.

## 1. Authorized daily cadence and precedence

All seven existing RH_Lean specialists **may have multiple automatic scheduled invocations on the same America/New_York calendar day**, including weekends if configured. The prior repository-wide *one automatic/scheduled run per agent per day* restriction is **withdrawn**. There is **no fixed numeric per-day limit in repository policy**: the owner chooses how many actual Studio triggers to configure and at what local times, subject to real platform and usage limits. One, two, three, or more actual invocations on a date are valid if genuinely configured or separately authorized; **none is presumed merely because this policy was published**.

Owner-requested manual continuations are also permitted; they do not masquerade as independent scheduled invocations and do not themselves create a Studio trigger. An existing automatic trigger remains an actual scheduled run even if it is the second or third for that role that day.

This policy supersedes every older once-daily/one-run-per-agent budget instruction for **cadence only**, whether in `AGENTS.md`, `CURRENT_PROOF_CONTRACT.md`, `docs/DYNAMIC_RESEARCH_AGENTS.md`, dated Studio setup/prompt examples, reporting-branch README/schedule prompts/templates, or historic report descriptions. Those earlier passages remain historical evidence of a former preference, not an operative daily cap. For research *task selection*, the current broad-search-until-eta directive still takes precedence.

## 2. Mandatory independent execution record on EVERY actual invocation

1. **Refresh before research.** Fetch current `main` SHA and authoritative instructions, original sources and PR/CI status; fetch all applicable **today and yesterday** own/upstream reports on `agent-reports`, including all committed same-day invocation sections, and the external handoff inbox. Do not infer that a timed upstream stage completed without its published evidence.
2. **Distinct provenance.** Record role, `America/New_York` local timestamp and offset, trigger kind (`SCHEDULED` or `USER_REQUESTED_MANUAL`), real run ID when exposed (otherwise `RUN_ID_UNAVAILABLE`), main SHA, policy/source SHAs, actual consumed report IDs, route/eta-gate, and independent theorem/falsifier/evidence class. Multiple runs on one date have distinguishable timestamped sections.
3. **Append, never erase.** Continue the same authorized `research/agent_reports/YYYY-MM-DD/<role-file>.md` with an early checked `PARTIAL / IN_PROGRESS` section and a timestamped final/resume capsule, preserving prior scheduled/manual work, claims, failures and corrections. Before writing, re-fetch blob; on conflict, reconcile and retry once. Verify successful readback. Never rewrite a completed earlier run as if it were the current one.
4. **No duplicate work.** Start from the newest verified theorem/counterexample and precise open inequality. Reuse exact-head CI and unchanged computations. A second same-day run should attempt the next nonduplicative step or a different protected route; never run the same scan just to fill a schedule.
5. **Real research rotation.** Count the broad-search anti-starvation cycle over **actual substantive invocations**, not calendar days or compatibility filenames. The three portfolio leads rotate over their distinct routes within a rolling three *actual* attempts. Preserve all nine viable routes until `VERIFIED_ETA` through a complete source-to-endpoint argument; a local tau, eta or green partial PR does not close the gate.
6. **Referee and Lean independence.** Separate author and referee execution provenance. Agent #7 formalizes only referee-qualified claims on its scoped proof PR with GitHub Actions and exact-head axiom audits. No number of repeated runs upgrades a local estimate to a complete bound.

## 3. Coordinator mirrors and time-dependent handoffs

The Coordinator may have **multiple genuine invocations per day**. **Each actual Coordinator invocation** creates one synthesis, uniquely timestamped and identified by its real run ID, and appends it to both `00-coordinator-am.md` and `90-coordinator-pm.md`. Keep the **entire two files byte-identical** after publication, preserving every earlier synthesis; the two filenames alone never imply two invocations. A missing mirror is a publication defect, not evidence of an unrun stage.

The other six roles retain their existing filenames and ownership. Multiple runs share each role's same dated file, with separate sections. Handoff order is based on what was **actually published before a given invocation**, not a hard-coded morning/evening sequence. Mark missing items `PENDING` and write `NOT_PUBLISHED` if publication fails. Do not count a same-session self-review as independent referee acceptance.

## 4. Deployment boundary and unchanged safeguards

A GitHub policy PR **does not create, enable, duplicate or reschedule** any Workspace Agent Studio triggers and cannot verify the user's saved schedule. After human merge, the owner should inspect the seven actual saved Studio schedules and add/change any desired additional daily triggers **in Studio**, using `America/New_York`; a second Coordinator schedule is now **permitted**, never mandated. Existing dynamically refreshing agents must load this policy from `main`; verify consumption in their next real timestamped report. If a saved Studio prompt hard-codes one/day, it must be synchronized separately.

The six non-Lean specialists remain **own-report-only** on `agent-reports`; the Coordinator alone owns its two mirror reports. Lean Verification alone retains the scoped `agent/lean-verification/` draft-PR/Actions exception. No scheduled specialist may change Studio schedules, permission grants, shared policy, another role's report, main directly, merge or enable auto-merge. Human review remains required for policy and proof merges. Preserve strict source fidelity, independent falsification and the canonical proof-status ledger.

**Acceptance check for deployment:** current `main` contains this policy; old one/day statements are explicitly superseded; at least the next actual run for each role records the main/policy SHA and run identity; a Studio schedule change is never claimed without separately verified Studio state.
