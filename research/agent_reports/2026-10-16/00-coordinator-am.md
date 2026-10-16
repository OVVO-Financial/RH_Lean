# RH_Lean Coordinator synthesis — 2026-10-16

**Status:** PARTIAL / IN_PROGRESS (early durable checkpoint of a user-directed manual cycle)
**Agent:** RH | Research Coordinator / Proof Architect — performed inside **one unified manual AI research cycle** (Claude, single session) with sequential role passes 1→7, explicitly requested by the repository owner. This is **not** seven independent scheduled invocations, and no other agent was launched, scheduled or simulated.
**Run ID:** `RH-UNIFIED-MANUAL-20261016T0806-0400` (session start 2026-10-16T08:06:37-04:00)
**Checkpoint time:** 2026-10-16T08:27-04:00
**Reporting rule:** one synthesis, mirrored byte-for-byte at `00-coordinator-am.md` and `90-coordinator-pm.md`. These are compatibility mirrors of one run, not two runs.

## A. Authority at intake

- Live `main`: `69e44d7cc8a63ebc1160639c264cbda4210339e1` (merge of #959, 2026-10-16T11:54:29Z). #958 merged at `b0446d45037b10637522791e398a9c8ffd99f123`; #960 merged into `agent-reports` at `79fbcd1d8707189f0eb4cb7cbdaedaedb660dcf4`. No open pull requests at intake (REST query).
- Authority blobs at that main: `AGENTS.md` `c40e9bc1fd57f8cdb295385f5cfdd7d9d0630f80`; `CURRENT_PROOF_CONTRACT.md` `b945dec4c55b8a91b85e2647210fb6c99b402d5c`; factor-depth brief `80b865bfaa99ebe6883dbac7803a12d1e63a4a93`; dynamic protocol `03d07880eaf8a018c6d52c6a2b99535eea79ff22`; amplification budget `3beff1f789646d59237744379ff8e578bb1042a0`.
- Source blobs: #958 module `RHLean/Proof/OddResidualCofactorSupport.lean` `356eefadaa7d798177da54017873021c4b8e0eae`; canonical definition `b504704070b193cea835713d697ba0d980704c7a`; canonical theorem `43e160ac7ad51f7646771297f43a9b95395ce709`; signed-seat source `13dda0d2c6cc59580959a2d59fad60126b1c6b0b`.
- Today's reports consumed: Wheel `9af028f5ce10cf9a06280d47ae6b0795c5974b8b`, Census `7e7033b2f5c7c780efb6e9ff4ce347b8a879296f`, Referee `068986b83d7ebc1421fe72c8e63c17dd1f68052e`, Lean `958330fdfeeda191b5b95de6468aaa6798f2c444` (its "draft / CI pending" text predates the live merge of #958). Coordinator, Owner, Analytic: `TODAY=PENDING` before this cycle.
- Yesterday (`YESTERDAY=CARRY_FORWARD`): Coordinator `0f9e254738e1bc3d01cfd0a3b114d99b7478b08a`, Owner `01fb928be14c1004b3124fb25101f369ad7e8611`, Analytic `fda92df0cd94cb997f213eddf4e6a5427b6dd03f`, Wheel `6d451c35eef4021fcff78253bed609d193c249c1`, Census `2e3c1cf95cd11669d57d2ce1f7216916736ff095`, Referee `cf0db85f6b04c56527bc9a26a1b6741ae196435a`, Lean `a11eddb6f78c927b8ec838426f94d72e63cda123`.
- External inbox `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c`: no entry newer than 2026-10-14; EXT-20261014-1..5 and CL-20261014-1..11 keep their recorded scopes.

## B. Pass 1 — architecture assessment and objectives (published before passes 2–7)

Objective unchanged: `VFCanonicalSquareVonKochStatement`, equivalently (paper coordinate bridge) `|L_R| = O(R log R)` with `L_R = F_R - pi(R^2) + 2`.

**Coordinator diagnosis.** The raw ledger `L_R = sum_seats (w(n) - 1_Prime(n))` is a regrouping of the prime indicator over physical seats. Any partition (T/H, A/B, cofactor bands) recombines by exact seat-count complementarity, so "coupling" between sectors is automatic at the level of totals. The live question is therefore sharper than "find a transport": **what arithmetic quantity does each sector's deviation encode, and is any sector-local restriction possible below RH strength?** Working hypothesis to test (H-CUT): at a greatest-prime cut `y`, the two sectors exchange a prime-distribution mode at scale `y`, weighted by the tag-charge density at `y`; near `y = R = sqrt(x)` that density is about `F_R/y`, which would make band-local deviations supertarget.

Independent obstacles retained (distinct inputs, not one bound in three notations):

1. **FD-TRANSPORT (raw ledger):** exact fluctuation content of `A_R`, complete `B_R` and its sub-sectors; whether a coefficient-preserving relation exists whose defect is not the endpoint.
2. **MU-LIFT (genuine Mobius):** exact anatomy of the floor kernel `Q_N(X)`, the power `r` forced by each signed piece, and calibration of what any fixed `(r, g)` would imply.
3. **INV-CONFIGURATION / incidence:** structural fibre geometry beyond #958 and an inverse statement whose configuration is independently restricted.

**Objectives assigned to passes 2–7:**

- **Owner (pass 2):** derive closed forms for `A_R` and complete `B_R` (lower tags + `H_R`) and for tag bands `[y, 2y)`, retaining every weight and boundary; identify the transported quantity across the `R^2/3` cut and the `sqrt(x)` wall. Reject any formulation whose defect is `L_R` itself.
- **Analytic (pass 3):** split `M(X) = 2M(N) - Q_N(X)` into signed components; determine which terms are critical (`r = 2`), test the sparse control's exact failure condition, and prove a strength-calibration lemma for fixed `(r, g)`. Report k, r, G, g, coverage.
- **Wheel (pass 4):** complete-fibre structure of tags above `sqrt(x)`; an inverse theorem tying band imbalance to an independently restricted statistic.
- **Census (pass 5):** pre-registered, falsifiable test of H-CUT on the raw carrier for all `R <= 5000` with complete signed `A/B` stratification; extend the predicted mode to large `R` only through proved identities.
- **Referee (pass 6):** self-audit every claim (this is a self-audit, not independent review).
- **Lean (pass 7):** only referee-surviving exact theorems, after duplicate search; candidates: Oct 16 staircase (accepted by today's scheduled Referee) or a new exact fibre lemma. GitHub Actions only; no merge.

Final synthesis will replace this checkpoint in both mirrors with identical bytes.
