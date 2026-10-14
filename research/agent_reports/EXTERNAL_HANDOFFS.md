# Independent research inbox (cross-session handoffs)

**Branch:** `agent-reports`. **Purpose:** durable, discoverable handoffs produced by user-directed research outside the seven separately scheduled Workspace Agents. This index is not a ninth agent, not a substitute for any assigned report, and not proof authority.

## Mandatory consumer protocol

After refreshing live `main:AGENTS.md`, `main:CURRENT_PROOF_CONTRACT.md`, actual `main` SHA and relevant today's **and yesterday's** named stage reports, read this inbox. Check the newest handoff that has not yet been addressed in your own reporting lane. Verify relevant theorem names, commit SHA, source carriers, hypotheses, numerical scripts and actual GitHub PR status. Reuse accepted material, record which external claim IDs were consumed, and continue with the first genuinely missing lemma; do **not** reclassify `PAPER_PROOF` as `PROVED_IN_LEAN`, retroactively mark missing upstream stages completed, or write to another agent's assigned report.

If a handoff is stale, superseded, refuted, formalized, or irrelevant to your specialty, record the reason in **your own** scheduled report with live references. Do not erase research history. Future direct sessions explicitly authorized to publish may add new dated files under `external/YYYY-MM-DD/` and append an index entry here, without modifying existing specialist reports or `main`. Existing specialist agents keep their normal write restrictions.

## Open handoffs

### 2026-10-14 — Direct seven-function RH_Lean cycle

**[Read the complete handoff and proofs](external/2026-10-14/seven-function-handoff.md)**

Main baseline: `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`. Latest verified merge at publication: `fcccdb32559d762dc5296dc519929f053f0fdf95`.

- **EXT-20261014-1 / PAPER_PROOF:** genuine-prime late least-factor quotient, strict-endpoint sharp gcd-2310 wheel capacity; exact run totals and counterexamples. Separately check and, if useful, formalize; unsigned only.
- **EXT-20261014-2 / PAPER_PROOF:** strict negative original-weight owner-3 current-versus-historical signed pair `w_R+w_r-1<-451/640` for genuine `3q` at `R>=2048`; distinct historical prime occurrence and actual block weights.
- **EXT-20261014-3 / PAPER_PROOF:** strict *isolated* NNS pair slack `6xy-x^2-y^2<-541/409600` for the same subcarrier. **NOT** a global zero-target covariance conclusion: exact cross terms and historical norm restoration remain.
- **EXT-20261014-4 / PROVED_IN_LEAN:** wheel-30 owner-fibre and dyadic run capacity theorems merged through [PR #937](https://github.com/OVVO-Financial/RH_Lean/pull/937), merge SHA `fcccdb32559d762dc5296dc519929f053f0fdf95`, verified proof head `59221ae46b2fa9b61cce2330ba965ea99bbce715`.
- **First unproved direct-VF lemma:** `SOURCE-SPLICE-1` — literal original occurrence/weight/sign/mask/anchor/clip/multiplicity/chronology and cross-term preserving history/current source -> compensated safe/Sector-Six reassembly. The NNS target is **global zero-target covariance**, not individual pair payment.

Exact reproducers in the same folder: [prime wheel](external/2026-10-14/sharp_wheel_2310.py) and [NNS pair](external/2026-10-14/nns_pair_slack.py). They are finite checks, not universal proofs.

**Specialist routing:** Owner Payment and Analytic Type II: EXT-2/3 and SOURCE-SPLICE-1; Finite Wheel: EXT-1; Prime Census: independent exact tests only where a new claim needs them; Adversarial Referee: independent ACCEPT/REVISE/REJECT of EXT-1/2/3; Lean Verification: avoid duplicating merged #937 and consider new scoped proof PRs only for referee-qualified theorems; Coordinator: log current uptake and unresolved obligations without changing the canonical proof target.

### 2026-10-14 (second) — Direct Claude seven-function cycle

**[Read the complete handoff and proofs](external/2026-10-14/claude-cycle/claude-seven-function-handoff.md)** — consumes the ChatGPT handoff above.

Main: `fcccdb32559d762dc5296dc519929f053f0fdf95`. Proof PRs (REVIEW_READY, not merged): [#938](https://github.com/OVVO-Financial/RH_Lean/pull/938) head `e2a2f39`, [#939](https://github.com/OVVO-Financial/RH_Lean/pull/939) head `7b93850`; all workflows green with compile-time `#guard_msgs` axiom audits (`[propext, Classical.choice, Quot.sound]`).

- **CL-20261014-1/2 / PROVED_IN_LEAN (#938):** `VFMidDyadicSignedLateCorrectionStatement`, `VFMidDyadicVFTrackingBoundedStatement` and `VFMidActualPrimeOwnerEscapeAdmissibleStatement` are each **equivalent** to the square-endpoint and canonical von-Koch targets. They are not narrower seams.
- **CL-20261014-3/3'/4/6/7 / PROVED_IN_LEAN (#939):** the #915 source payment is FALSE at every first-bad instance; it is equivalent to "no first-bad successor at K=2", i.e. (base bad) ∨ the explicit envelope |D_R| ≤ 2R log R. For each R it depends only on (D_R, P_R), and it is sandwiched by explicit block-scale thresholds.
- **CL-20261014-8..11 / PAPER_PROOF:** explicit offset 2.96758 ≤ li(R²)−F_R ≤ 3.15727; payment ⇔ RH (Schoenfeld); unconditional K=2 envelope for R ≤ 1.049·10¹³ (Johnston 2022); hypothesis-free payment fails infinitely often (Littlewood + Brun–Titchmarsh).
- **FINITE_COMPUTATION:** exact census to x = 10¹² (π(10¹²) verified). Payment holds at all 999,993 R ∈ [8,10⁶] (min normalized slack 0.588). EXT-1 table reproduced by independent code.
- **Referee:** EXT-1 ACCEPT, EXT-2 ACCEPT (scope note), EXT-3 REVISE, designation of SOURCE-SPLICE-1 as a "first missing lemma" REJECT (it is RH-equivalent).
- **First unproved statement:** the canonical target itself; there is no strictly weaker named lemma on `main` whose proof completes the route.


### 2026-10-14 (third) — Independent review: physical normalized source-payment limsup

**[Read the complete paper proof and audit](external/2026-10-14/normalized-payment-limsup-no-go.md)**. Consumes and checks the two earlier external sessions and PR #938/#939 as they existed at the review.

- **EXT-20261014-5 / PAPER_PROOF:** for the exact #915 original-physical denominator `T_R=(|D_R|+beta_R)^2`, source `S_R=D_{R+1}` and `N_R=S_R^2/T_R`, one has `0<=N_R<=1` for all `R>=8` and **`limsup_(R->infinity) N_R=1` unconditionally** (classical Littlewood + Brun–Titchmarsh + compiled VF–li O(1) bridge). This strengthens the second handoff's CL-11: **no uniform unconditional `N_R<=c<1` is possible** with the existing denominator. Not a Lean proof; independent referee review required.
- **Critical scope correction:** #939 audits the original payment inequality, not every possible occurrence-preserving `SOURCE-SPLICE-1` *equality*. A new exact identity may be unconditional; deriving a bound strong enough to pay the source would be RH-hard. The previous isolated EXT-3 paired NNS statistic is not itself the original global #915 norm. The suggested de la Vallée Poussin baseline is weaker than the established Vinogradov–Korobov unconditional prime-counting error.
- **Agent routing:** Coordinator include the result in next handoff; Referee independently test its full proof and denominator; Owner/Analytic reject proposed all-R strict-fraction NNS payment without altering the carrier; Lean agent may prove the deterministic sandwich on a separate scoped PR, but Littlewood is **not** formalized in this submission.

## Index integrity

This file lists *external* research only. The eight named reports under `research/agent_reports/YYYY-MM-DD/` remain the seven agents' actual scheduled output. External submissions do not supersede authoritative live Lean source or `main` proof instructions. New entries should include original claim IDs, status, source/commit SHA, direct GitHub handoff link, reproducer path, and first missing mathematical lemma.
