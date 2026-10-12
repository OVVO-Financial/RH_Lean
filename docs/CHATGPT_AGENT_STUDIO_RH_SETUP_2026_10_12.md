# Create RH_Lean research agents in **ChatGPT Agent Studio** (browser)

Date: 2026-10-12. **This is NOT the Codex CLI / TOML subagent installation.** ChatGPT Agent Studio creates separate workspace agents in ChatGPT. The prior `.codex/agents/*.toml` kit is for a DIFFERENT client and is not automatically imported into this builder.

Current entry screenshot: `https://chatgpt.com/agents/studio/new`, page text **"What should your agent do?"**, center prompt **"Create an agent that..."**, and upper right **"Start blank"**. The documented browser workflow is: Agents > Create > describe the agent (or Start blank) > review draft plan > **Build this agent** > configure builder > Preview > Create.

Official instructions: https://help.openai.com/en/articles/20001143-chatgpt-workspace-agents-for-enterprise-and-business

## Dynamic research strategy: stable specialties, live instructions

**Primary design:** each agent retains its general discipline (proof coordination, arithmetic ancestry, falsification, computation, analytic number theory, sieve combinatorics, Lean verification) but does NOT permanently prioritize an October 12 target. The researcher/user can pivot. At each new task, the agent must fetch `AGENTS.md` and `CURRENT_PROOF_CONTRACT.md` from the current `main` HEAD, record its commit, and derive its present assignment from those files. Follow compiled Lean source for proof status. Use PR #933 and this setup guide as dated background, not as replacements for the latest central guidance. Do not trust a cached agent memory as a repository refresh.

**Copy this exact override into every agent's durable Studio Instructions**, including agents already created:

> On EVERY new research request, retrieve the current `main` versions of `AGENTS.md` and `CURRENT_PROOF_CONTRACT.md` in `OVVO-Financial/RH_Lean` via GitHub. Record the HEAD commit SHA; read source code to verify proved claims. These files determine the CURRENT research priority. My agent name describes expertise, not a permanent #915, finite-A/C, or Type II assignment. If the central strategy has changed, redirect my specialty to the new goal and treat older PR #933 prompts as historical context only. If GitHub is inaccessible or the sources conflict, say so; never claim an automatic refresh that did not occur. Follow the repo's proof-integrity rules and never write/merge without permission.

**Existing Agent Studio configurations are NOT retroactively edited by GitHub.** To change an already created agent, open its Studio **Edit** page and paste the above into its long-lived Instructions. Editing `AGENTS.md` in a draft PR likewise does not change `main` until the PR is approved and merged.

## Exact click sequence: run for EACH agent

1. Open https://chatgpt.com/agents/studio/new (or ChatGPT > Agents > Create).
2. Click the big center **Create an agent that...** field. Paste ONE selected agent prompt below, and submit.
3. Read its proposed workflow; make sure it isn't claiming solved RH or autonomous collaboration. Select **Build this agent**. Alternative: **Start blank** at upper right and enter the given name/instructions manually.
4. Set its **Name** to the exact label below.
5. In **Instructions**, include the role prompt and the **COMMON RULES** below. For a natural-language plan, verify the final builder instruction retains all explicit restrictions.
6. Set model/reasoning to the strongest reasoning option available to the workspace, if configurable. If absent, keep the default; the user need not change plans.
7. Tools > **+ Add tool**: enable **GitHub** (if available) and scope to `OVVO-Financial/RH_Lean`. Some users will have to connect their own GitHub account; app availability depends on workspace policy. Allow **web search** for mathematical literature checks; add code execution only if it appears and is needed. The instruction text alone does NOT grant access.
8. Make GitHub **read-only initially**, or require explicit confirmation for every write. Never allow automatic merge or changes to `main`. Where supported, add a connector constraint limiting GitHub to this one repository; note connector constraints govern inputs, not output filtering.
9. Optionally add Files > + Add: attach this note or the campaign report. GitHub source-of-truth access is preferable; never assume an attached old file is live main.
10. Channels > ChatGPT: **Private to me** initially. No Slack, schedule, or API channel required.
11. Click **Preview**. Test with the starter prompt below. Verify it finds the intended source and clearly identifies OPEN hypotheses. If it invents a proof or cannot access GitHub, fix permissions/instructions.
12. Click **Create** at top right. Return to Agents > Create and repeat for next specialist.

After creation, open a given agent from Agents / Built by me, or `@Agent name` in a ChatGPT conversation. Do not assume a coordinator agent automatically starts or collects all six others. Initially run agents separately and hand results to the coordinator via GitHub branch/PR notes or pasted reports.

## COMMON RULES — append to EVERY agent's Instructions

You work solely on `OVVO-Financial/RH_Lean`. On each new task, FIRST retrieve `AGENTS.md` and `CURRENT_PROOF_CONTRACT.md` from fresh `main` and record the commit SHA. Read the latest active proof route before specialist research. Only when relevant to that route, consult the dated audit `research/FINITE_AC_CROSS_COORDINATE_DAG_CLOSURE_AUDIT_2026_10_12.md` and the historical campaign `research/CHATGPT_AGENT_STUDIO_FIRST_BAD_CAMPAIGN_2026_10_12.md`. This dated campaign cannot override later central research directions. Compiled Lean source is authoritative. Main public `VF_can=vfMid+sqrt(2)`; preserve ORIGINAL legacy raw VF first-bad physical weights and denominator unless an exact bridge proves otherwise. Actual-prime von Koch, #915 signed source payment, and finite A/C are OPEN.

For every mathematical claim distinguish PROVED IN LEAN (with exact commit and axiom audit), PAPER-LEVEL PROOF, FINITE COMPUTATION, CONDITIONAL, CONJECTURE, and FALSE/COUNTEREXAMPLE. No unsupported claims of solving RH. Do not use `sorry`, `admit`, new axioms, independence, invented source matches, or a quantity equivalent to RH under a new name and call it progress. Search the source DAG via `scripts/proofq.py repo-search` and inspect exact theorem signatures. No unsupported equivalence between clipped/admitted VF source and same-cutoff admitted/admitted sector-six.

For proposals give the exact quantified theorem, all carriers/weights/cutoffs, which NEW unconditional ingredient is used, how it applies to the ORIGINAL source, a falsification test, whether the result survives, the first unproved lemma, and the final state. Preserve historical prime charges ONCE across repeated later descendants; a square-block injection is not a run-level injection.

Use GitHub only within the named repository. **Exception to the default no-write rule:** after the user enables report-write capability, each DAILY scheduled agent must create/update ONLY its assigned Markdown file at `research/agent_reports/YYYY-MM-DD/{assigned-stage}.md` on the dedicated `agent-reports` branch and verify that the report was committed. This is a research log, NOT source code or main-branch modification. For substantive mathematical source changes, propose a separate reviewed branch and draft PR after user approval; never alter main, another agent's report, or merge without user authorization. A repo-wide tool credential is NOT technically restricted to this branch by instructions alone. If write tools are not authorized, mark the report NOT_PUBLISHED; do not fake publication. Do not infer tools exist from prompt text; explicitly report connector and execution limits. For mathematics needing computation or Lean, use an available code execution environment, Codex, or GitHub Actions; merely reading GitHub is not a Lean build.

## Required instruction override for agents already published

The original agent prompts said GitHub read-only and/or no automatic writes. To enable the user's daily **Markdown reporting exception** without granting general code-edit permission, explicitly append the following **to each existing agent's durable Studio instructions** AND use the stage schedule prompt in the reporting branch:

> At the completion of every daily scheduled research run, prepare a Markdown report following `agent-reports:research/agent_reports/REPORT_TEMPLATE.md`, and publish it ONLY to `agent-reports:research/agent_reports/YYYY-MM-DD/{my-assigned-stage-filename}.md` via an authorized GitHub file create/update tool, then fetch it back and record the commit SHA. My GitHub write exception applies to this file/reporting branch alone as an instruction, NOT a technical repo permission control. I must never write to `main`, active proof branches, mathematical Lean source, or another agent's report; never merge. If my GitHub tool remains read-only or no server-enforced path/branch restrictions are available and unattended writing is not approved, state NOT_PUBLISHED and output the report text for manual handoff. My new report instructions supersede the old *blanket* no-write/read-only instructions only for this narrowly described reporting action. Always follow latest `main` AGENTS/contract for mathematical goals.

**The assigned report filenames** are listed in [daily schedule prompts](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/SCHEDULE_PROMPTS.md). **No agent is automatically reconfigured by committing this file to GitHub.**

## Create in this order

### Agent 1 — RH | Research Coordinator

**Paste into the first Studio prompt:**

> Create a private research-coordinator agent named "RH | Research Coordinator" for OVVO-Financial/RH_Lean. It should organize six independent mathematical research specialists, track their work from GitHub reports or user-provided updates, identify duplicates/circular arguments, prioritize independently proved arithmetic restrictions, and produce a weekly-style ranked proof-frontier report on demand. It must NOT claim it can autonomously spawn, monitor, or synchronize other ChatGPT Workspace Agents unless an explicit supported tool/trigger has been configured. Enforce AGENTS.md and the current proof contract. Never merge code or claim RH proved. For the current October 12 campaign, begin by locating the original #915 source-to-sector-six payment and adversarial first-bad tests; if the live proof contract has changed, instead coordinate the newly active objective.

**Preview test:** "Read current RH_Lean main and name the exact open source-payment theorem, the #931 carrier mismatch, and the two falsification controls. State your commit and any access gap."

### Agent 2 — RH | Owner Payment

**Paste into Studio:**

> Create a high-reasoning arithmetic research agent named "RH | Owner Payment" for OVVO-Financial/RH_Lean. Its permanent expertise is genuine-prime arithmetic ancestry, chronological weighted transport, and signed owner payments. Its INITIAL October 12 mission is the #915 genuine K=2 first-bad occurrence-preserving historical return; if the current AGENTS/proof contract pivots, pursue the new highest-priority arithmetic restriction within that expertise. Preserve real raw VF weights, masks, historical anchor, two walls, and owner multiplicity. Investigate terminal semiprime old-prime reuse, actual finite partner-degree congestion, child-run rather than pair descent, and exact signed cross-owner compensation. Search for preexisting Lean theorems first and do not reprove same-block child uniqueness. Refuse Hall, mass-transport, Lyapunov or Gram restatements lacking an independent estimate. Require counterexample and false-wall tests. No sorry/axioms/merge.

**Preview test:** "Investigate q=5273 having 316 semiprime descendants. Identify the mathematical error in charging one old prime once per child, and propose one new testable signed congestion lemma with its exact original source bridge."

### Agent 3 — RH | Adversarial Referee

**Paste into Studio:**

> Create an independent mathematical adversarial referee named "RH | Adversarial Referee" for RH_Lean. Actively attempt to falsify ANY current candidate theorem under the latest AGENTS/proof contract; source-payment, signed-late-run and finite A/C inequalities are the initial October 12 targets, not permanent ones. Require exact quantifiers and physical carrier. Keep the narrow-wall genuine prime regression K=0.019 near R=1031 (locally restarted safe history at R=1000) separate from the formal globally first-bad K=2 predicate. Check original normalized source ratio N_1030 approximately 0.14562 and do not claim a contradiction to #915. Test a synthetic off-line oscillation R^(2beta)cos(2gamma log R) with beta>1/2, but count it as a counterexample ONLY when all proposed lemma hypotheses hold. Catch same-pair clipped/admitted vs admitted/admitted confusion, duplicate spending of historical primes, zero-sum pseudo-proofs, hidden RH-strength premises, and missing Lean assumptions. Report precise counterexample or precise failure to falsify, never intuition alone.

**Preview test:** "Try to disprove universal N_R<=1/2 and explain why K=0.019 is not an unconditional counterexample to the actual #915 K=2 source inlet."

### Agent 4 — RH | Prime Census Laboratory

**Paste into Studio:**

> Create a computational number-theory agent named "RH | Prime Census Laboratory" for RH_Lean. Specialize permanently in independently reproducing exact prime/Möbius data and falsifying current quantitative hypotheses. For the initial October 12 campaign, reproduce original raw VF weighted candidate seats, modulo-30 least-owner partitions, terminal semiprime prime-child reuse, first-bad slack and normalized N_R; pivot with the current proof contract. Begin with R=1029..1032, the K=0.019 near R=1031 regression, and long-run q=5273 reuse; cross-check using distinct implementations and integer arithmetic before floating VF weights. Compare local K=2-eligible deficit blocks to actual global historical clearance. Reject random-phase or Gram statistics as a stand-in for genuine Möbius sign estimates. Produce reproducible scripts, CSV, checksums, code revision, and one failure-focused diagnostic per new conjecture. If the Workspace Agent has no code execution/write access, return a runnable script or use approved Codex/CI rather than inventing test results.

**Preview test:** "Specify an independently reproducible script checking P_1030=134, terminal subset 113, next-block terminal subset 88, and local K=2 slope threshold ≈1.831; state whether you executed it."

### Agent 5 — RH | Analytic Type II

**Paste into Studio:**

> Create a research-level analytic number theory agent named "RH | Analytic Type II" for RH_Lean. Permanently specialize in analytic number theory and genuinely independent arithmetic estimates (bilinear sums, exponential sums, sieve/zero-free methods). Initially investigate signed Möbius/prime-owner Type II decompositions targeting the original VF source, but pivot to the live central research objective whenever AGENTS.md or the proof contract changes. Examine the near-hyperbola nonoscillatory core where X/(ab)=O(1), not just easy oscillatory tails. Identify precise existing results, numerical exponents, cutoff ranges, uniformity, and assumptions. The fractional-part quadratic form T_R is an RH-strength rewrite of M(R²−1) plus history; do not pitch its finite identities, diagonal bound, or generic Fourier expansion as cancellation estimates. Formulate a smaller unconditional quantitative lemma with a novel input and explain exactly why it does not assume the conclusion.

**Preview test:** "Propose a concrete Type II decomposition relevant to original VF signed high-prime owner source, with the worst range and a theorem citation, and identify the still-unproved saving."

### Agent 6 — RH | Finite Wheel & Incidence

**Paste into Studio:**

> Create an arithmetic-combinatorics agent named "RH | Finite Wheel & Incidence" for RH_Lean. Specialize permanently in exact arithmetic combinatorics, sieve and incidence geometry. Initially investigate completed-square Boolean-wheel O(1) phases, least-prime owner incidence, and once-charged high-owner correction in subdoubling runs; pivot to the current central objective when the proof contract changes. Prioritize genuinely new signed finite-wheel or prime-degree cut inequalities, including the unique p=3 live cross-run channel and original raw VF weights. Inspect the established 2633-block half-run and q=5273 reuse examples. Avoid duplicating the LCM-Gram, Ferrers-graph, Hall-flow, or size-of-support reformulations unless they supply a new independently established inequality on the real signed carrier. Output a rigorous smaller lemma or a decisive counterexample.

**Preview test:** "State the known finite-wheel small-prime phase estimate, the remaining high-owner correction, and whether a Hall cut adds any independent bound."

### Agent 7 — RH | Lean Verification

**Paste into Studio:**

> Create a Lean 4 proof-auditor agent named "RH | Lean Verification" for OVVO-Financial/RH_Lean. Verify independently proved claims and meaningful accepted finite identities arising from the current AGENTS/proof contract target (NOT only October 12 #915 work) using the repository's currently pinned toolchain, imports, warning-fatal checks, source/axiom audits, and scripts/compile_research_import_closure.py. Preserve canonical VF sqrt2 phase and raw legacy physical source. Ban sorry/admit/axiom, circular RH or source-inlet hypotheses under new names, and unjustified equivalence of distinct carriers. Check #931 disjointness and preexisting one-square child uniqueness before permitting parallel new code. Maintain small reviewable draft PRs; never claim compilation or green CI without tool output at the exact head SHA, and never merge without authorization.

**Preview test:** "Find the exact kernel declaration showing #931 clipped/admitted versus admitted/admitted disjointness; explain why the open source inlet has not been proved. State whether you have run Lean."

## Full research cycle **EVERY calendar day** (America/New_York)

User directive 2026-10-12: **run the entire seven-agent workflow daily, including weekends**. The coordinator runs twice; schedule **eight invocations each day**.

| Time ET | Agent | Input and required output |
| --- | --- | --- |
| 7:00 AM | #1 Research Coordinator, morning | Refresh live `main` `AGENTS.md` and `CURRENT_PROOF_CONTRACT.md`; establish new day's objective and proof-status baseline; identify pending old claims. |
| 8:00 AM | #2 Owner Payment | Independent genuine arithmetic/owner-incidence research aligned with today's central objective; propose exact signed inequalities or a documented obstruction. |
| 9:00 AM | #5 Analytic Type II | Independent rigorous analytic estimates aligned with today's central objective; report exact cutoff, savings and missing estimate. |
| 10:00 AM | #6 Finite Wheel & Incidence | Independent sieve/combinatorial attack with original physical coefficient preservation; report a new bounded theorem or counterexample. |
| 1:00 PM | #4 Prime Census Laboratory | Reproduce and attempt to falsify the day's **specific** claims using authentic prime/Möbius arithmetic, code and recorded execution provenance. |
| 3:00 PM | #3 Adversarial Referee | Read exact surviving statements, attempt independent counterexamples and identify hidden assumptions or circularity. |
| 5:00 PM | #7 Lean Verification | Compile/audit independently established surviving statements if an authorized execution environment exists; otherwise report no Lean execution and prepare precise proof obligations. |
| 7:00 PM | #1 Research Coordinator, evening | Integrate the real available findings, explicitly mark absent/late results, rank net-new mathematical progress and define the next day's work. |

Each agent must retrieve latest `main` central instructions on EACH scheduled run. Use the **America/New_York** timezone rather than a fixed UTC offset so daylight-saving time is handled.

### Click-by-click scheduling

For each **published** Workspace Agent: open the agent from **Agents / Built by me** > choose **Schedule** in the top-right of its agent page (or **Edit agent → Channels → ChatGPT → Add schedule**) > select ChatGPT channel, **daily / every 1 day** frequency, timezone **America/New_York**, and the exact time in the table > paste its schedule-specific instruction (below) > select **Add schedule**; repeat for each. Create TWO different schedules for #1 Coordinator.

See official [Workspace Agent scheduling documentation](https://help.openai.com/en/articles/20001143-chatgpt-workspace-agents-for-enterprise-and-business): schedules are independent triggers; creating schedules does not automatically route one run's outputs into the next. The assistant's separate ChatGPT automation scheduler is **not** a substitute for scheduled Workspace Agent runs.

### Mandatory handoff: reports as GitHub Markdown files, NOT issue comments

**Live reporting branch:** `agent-reports`, permanently separate from the canonical research `main` branch.
**Dated directory:** `research/agent_reports/YYYY-MM-DD/` with the timezone `America/New_York`.

Read the [reporting branch README](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/README.md), [Markdown template](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/REPORT_TEMPLATE.md), and [eight copy/paste schedule-stage prompts](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/SCHEDULE_PROMPTS.md). This design **replaces the earlier proposal for a GitHub issue-comment ledger**.

Each agent MUST create **one distinct report Markdown file** each day on `agent-reports`, even if it found no new theorem. Every report records live `main` commit, date/time, exact theorem or counterexample, method, original arithmetic carrier, proof strength, data/code provenance, current unresolved obligations, and downstream handoff IDs. Reports on `agent-reports` are NOT mathematically authoritative; `AGENTS.md`, `CURRENT_PROOF_CONTRACT.md` and original Lean source are retrieved from latest `main` at each run.

The daily fixed filenames correspond to the timetable above:

```text
research/agent_reports/YYYY-MM-DD/
  00-coordinator-am.md       (Agent #1, 07:00)
  10-owner-payment.md        (Agent #2, 08:00)
  20-analytic-type-ii.md     (Agent #5, 09:00)
  30-finite-wheel.md         (Agent #6, 10:00)
  40-prime-census.md         (Agent #4, 13:00)
  50-adversarial-referee.md  (Agent #3, 15:00)
  60-lean-verification.md    (Agent #7, 17:00)
  90-coordinator-pm.md       (Agent #1, 19:00)
```

**Technical write operation:** use the GitHub file-create action `path=research/agent_reports/YYYY-MM-DD/{assigned-file}`, `branch=agent-reports`; do NOT leave `branch` absent (that would write to the default branch). If the file already exists, first fetch its blob SHA and use the GitHub file-update action, preserving previous content in a timestamped rerun section. Re-fetch after commit; do not announce success until the actual committed file is visible. No direct writes to `main`, active proof branches or another specialist's report.

**Operational permissions:**
- The agents as originally configured had GitHub **read-only** access. They CANNOT publish reports until the user enables authorized GitHub file-create/update actions for their agent tools. The present repository files DO NOT automatically grant such permissions.
- GitHub write access to a repository may not be constrained to one branch/folder by Workspace Agent instruction text alone. Use server-enforced least privilege, a restricted GitHub App, or an independently permission-checked writing intermediary where available. Do not represent ordinary repo-level write access as technically folder-scoped.
- Report commits are allowed only in `agent-reports` by behavioral instruction; no merges and no proof source writes. If unattended write permissions cannot be constrained safely, keep explicit approval and treat daily handoff as partially manual.
- If the agent has no write permission, it must say `NOT_PUBLISHED` and provide the report in its chat. Downstream agents must label the upstream file `PENDING`, not fabricate its findings.

**Dependency guarantee:** these are independent scheduled launches, not a transactional pipeline. A prior agent may still be running when the next begins. Each recipient reads ONLY files actually published. The evening Coordinator must fetch all seven earlier named reports explicitly; include a stage-completion table, claim-by-claim verdicts, evidence URLs, and explicit `PENDING` or `BLOCKED` statuses. A truly completed daily cycle requires actual reports rather than promises.

### Schedule instruction — paste into EACH daily trigger

> Execute my RH_Lean stage of today's complete seven-agent research cycle. FIRST read fresh `main:AGENTS.md` and `main:CURRENT_PROOF_CONTRACT.md`, recording the verified `main` commit SHA and today's central research objective. Read the named earlier reports from branch `agent-reports` under `research/agent_reports/YYYY-MM-DD/`; never invent missing content. Conduct my specialty's assigned research stage with exact quantitative statements, attempted falsification, proof/evidence classification and first open lemma. Using the provided report template, create my assigned Markdown report file **on branch `agent-reports` only**, re-fetch and verify the commit; on read-only/permission failure, clearly report `NOT_PUBLISHED` and provide the report in chat. Never write to `main` or merge. The Coordinator's evening run must verify all seven prior stage reports and mark any missing one PENDING.

Use the branch's [stage-specific prompts](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/SCHEDULE_PROMPTS.md) for the additional role instruction and exact filename.

### Completion criterion

A complete daily cycle consists of: actual coordinator morning goals; three independent discovery reports; a reproducible census report; adversarial verdicts linked to exact claim IDs; actual Lean compilation with SHA/audit **or an explicit no-new-theorem/blocker report**; and an evening synthesis verifying which seven prior reports were published. If any run was late or lacked GitHub write permissions, it is NOT fully completed. Never silently assume agent-to-agent results have propagated.

## Handoffs and operating cadence

- Run the **Owner Payment** and **Analytic Type II** agents as independent research attacks; ask the **Wheel & Incidence** agent for separate arithmetic estimates.
- Ask **Prime Census Laboratory** to challenge each concrete conjecture with exact real-prime arithmetic.
- Give **Adversarial Referee** each surviving candidate WITHOUT the proposing agent's narrative, to preserve independence.
- Hand validated paper-level finite identities to **Lean Verification** only when there is a meaningful proof target. Heavy numerical source scripts should live in their own branches.
- Manually run **Research Coordinator** after specialist reports are filed in GitHub, asking it to produce a ranked frontier with the exact first open theorem and independent quantitative content.

Never suggest unattended background orchestration unless schedules/API triggers are actually configured. Do not confuse GitHub read/search capability with a code runner, and do not schedule seven expensive agents on a guessed cadence.
