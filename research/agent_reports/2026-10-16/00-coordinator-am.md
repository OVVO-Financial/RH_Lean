# RH_Lean Coordinator synthesis — 2026-10-16

**Status:** COMPLETED
**Agent:** RH | Research Coordinator / Proof Architect — performed inside **one unified manual AI research cycle** (Claude, single session, explicitly requested by the repository owner) with sequential role passes 1→7 and a final Coordinator pass. This is **not** seven independent scheduled invocations; no other agent was launched, scheduled or simulated, and no schedule was modified.
**Run ID:** `RH-UNIFIED-MANUAL-20261016T0806-0400` (start 2026-10-16T08:06:37-04:00; synthesis written 2026-10-16T09:07-04:00)
**Reporting rule:** one synthesis, mirrored byte-for-byte at `00-coordinator-am.md` and `90-coordinator-pm.md` — compatibility mirrors of one run, not two runs.
**Early checkpoint:** published at `agent-reports@06321eb48342fb97a83bb312044f0c80be7a03ef` (both mirrors, blob `5e6dffa5aa10a0b5c6fff65c1c32281d5d111073`, read back identical); replaced by this synthesis.

## A. Bottom line

The cycle produced exact structural theorems and decisive obstructions, **no quantitative progress on the canonical bound**. Its main finding is negative and sharp: on the raw odd-seat carrier, every way of localising the problem by greatest-prime sector is either **RH-equivalent** (fixed-ratio cuts, including the complete complement `B_R`) or carries a **provably supertarget** prime-distribution mode (cuts and bands near the square-root wall). The requested "signed coupling of `A_R` with complete `B_R`" exists exactly — it is the cut identity through `pi(R^2/3)` — and after it the only remainder is the endpoint itself.

## B. Authority and continuity

- `main` `69e44d7cc8a63ebc1160639c264cbda4210339e1` (#959); #958 merged `b0446d45…`; #960 merged into `agent-reports` `79fbcd1d…`. No open PRs at intake.
- Authority blobs: `AGENTS.md` `c40e9bc1…`, contract `b945dec4…`, brief `80b865bf…`, protocol `03d07880…`, amplification budget `3beff1f7…`. Objective unchanged: `VFCanonicalSquareVonKochStatement`.
- Today's scheduled reports consumed: Wheel `9af028f5…`, Census `7e7033b2…`, Referee `068986b8…`, Lean `958330fd…`. Yesterday carried forward (all seven, Coordinator `0f9e2547…`, Owner `01fb928b…`, Analytic `fda92df0…`, Wheel `6d451c35…`, Census `2e3c1cf9…`, Referee `cf0db85f…`, Lean `a11eddb6…`). External inbox `c1d1aad9…`: no new entries.

## C. Completion matrix (2026-10-16)

| Role | File | State |
| --- | --- | --- |
| Coordinator | `00`/`90` | this synthesis (mirrors) |
| Owner Payment | `10-owner-payment.md` | COMPLETED (manual pass 2; new file) |
| Analytic Type II | `20-analytic-type-ii.md` | COMPLETED (manual pass 3; new file) |
| Finite Wheel | `30-finite-wheel.md` | scheduled run COMPLETED + manual pass 4 appended |
| Prime Census | `40-prime-census.md` | scheduled run COMPLETED + manual pass 5 appended |
| Adversarial Referee | `50-adversarial-referee.md` | scheduled run COMPLETED + manual pass 6 (**self-audit**) appended |
| Lean Verification | `60-lean-verification.md` | scheduled run + manual pass 7 appended; PR #961 |

## D. Findings by evidence class

**Exact identities (`IDENTITY_ONLY`, exact on the carrier):**
- owner-3 band identity: `T_R - M_R = F_R (E(2R-1) - E(R-1)) + rho_R`, `rho_R` in an explicit `O(R/log^2 R)` bracket.
- owner-5 cut identity: `B_R = F_R + 2 - pi(R^2/3) - sum_{R^2/3<q<R^2} w(q) = Psi_w(R^2; R^2/3) - pi(R^2/3) + 2`, with its Stieltjes form.
- owner-6 wall decomposition `L_R = Lambda^<_R + sum_{R<=q<R^2} phi_x(q)`.
- analytic-1 floor-kernel anatomy `M(X) = 2M(N) + K1 - K2 + K3` (and the four-term form).

**Paper proofs (`PAPER_PROOF`):**
- owner-1 complete fibres above the wall; owner-2 sampling bracket; wheel-4 fibre staircase and the square-root wall.
- **owner-4 (Lemma M + band):** `E(2y) - E(y)` is not `O(y^(-1/2-delta))` (uses only the zero `rho_0 = 1/2 + 14.13…i`); hence the band `[R, 2R)` deviates from its prime-free main term by a quantity that is **not `O(R^(3/2-delta))`** — unconditionally supertarget.
- **owner-5:** `|B_R - B*_R| = O(R log R)` for all `R` **⇔ RH**.
- analytic-2: finitely supported prefix controls amplify iff `sum a(n)/n = 0`.
- analytic-4: cut-mode spectrum — target scale only at fixed-ratio cuts (RH-equivalent there); provably supertarget for bands at `x^theta`, `1/2 <= theta < 2/3`.
- wheel-5: inverse theorem (band imbalance ⇔ Mertens increment at scale `R`) with an independent restriction of classical strength, `|T_R - M_R| = O(R^2 exp(-c sqrt(log R)))`.

**Conditional implications:** analytic-3 strength calibration — a fixed whole-interval `(r, g)` inequality on a square chain forces a zero-free half-plane `Re s > 1/2 + 2g/(2-r)`; every fixed `g < (2-r)/4` is a quasi-RH statement.

**Finite computations (pre-registered, held out):** band law confirmed for every `R in [1000, 5000]` (`corr = 0.99997`, `0` bracket violations); cut mode `corr(B - B*, -epsilon(R^2/3)) = 0.991`; independent re-implementation to `5e-12`; band deviation exceeds the whole signed total `|L_R|` for 74.8% of roots (max ×9.27); by the proved identity the band mode first exceeds `R log R` near `R ≈ 1.1×10^8` (primes sieved to `2×10^9`).

**Lean-certified (on PR head, not on main):** owner-1 / wheel-4 incidence core in `RHLean/Proof/RootWallCompleteFibre.lean`, draft PR #961 head `dd066a06…`, primary build/warnings/graph/audit green, axiom footprint build-enforced as `[propext, Classical.choice, Quot.sound]`; four legacy suites pending at synthesis time.

**Unresolved:** the canonical endpoint; complete-source payment; finite A/C; CORR-4; any MU-LIFT gain; RH.

## E. Mechanisms: advanced, falsified, retired

| Mechanism | Before | Now | Reason |
| --- | --- | --- | --- |
| Same-tag `A -> H`; fixed cofactor backbone | REJECT | REJECT | unchanged (#958 support, census-2) |
| Band-local / sector-local estimates at intermediate cuts | implicitly open (brief's "dyadic cofactor bands") | **REJECT** | owner-4, analytic-4: unconditional supertarget oscillation |
| Independent estimate of complete `B_R` | candidate sub-goal | **REJECT as sub-goal** | owner-5: RH-equivalent |
| FD-TRANSPORT (raw ledger, complete A/B) | CONTINUE/REVISE | **SUSPEND** | coupling is the exact cut identity; regroupings cannot change cut modes; revival needs a sieve identity with explicit bilinear remainder |
| INV-CONFIGURATION | CONTINUE (low) | **MERGE** into cut-mode picture | wheel-5 realises it, restriction only classical-strength |
| MU-LIFT | CONTINUE | **REVISE** to structural study of the `K3` corner | analytic-3: no fixed nontrivial `(r,g)` short of quasi-RH |
| Nyman positive-Hilbert | CONTINUE (distinct) | unchanged | no new input this cycle |

These decisions are recommendations of one manual cycle for human review; no central policy file was edited.

## F. Quantitative progress

**None.** No unconditional bound on `L_R`, `D_can` or `M` improved. The only new quantitative statements are lower bounds (owner-4, analytic-4), an equivalence (owner-5), a classical-strength band estimate (wheel-5) and finite values.

## G. Remaining obstruction — smallest unpaid statement

On the raw carrier there is no named lemma strictly weaker than RH whose proof would complete the route: the natural intermediate objects are RH-equivalent (`B_R`, any fixed-ratio sector) or provably supertarget (bands near the wall). The smallest genuinely *new* input common to the surviving formulations is a **Type II bilinear estimate at the square-root scale**, concretely square-root cancellation in the hyperbola corner of the Mobius sawtooth form

```text
| sum_{i,j <= N, X/H < ij <= X} mu(i) mu(j) psi(X/(ij)) |  <=  G E(B)^r sqrt(X),   r < 2,  G = B^o(1),  B <= X < B^2,
```

together with the matching smooth pieces `K1, K2` (analytic-1, G). Any sieve-identity revival of FD-TRANSPORT reduces to a sum of this type. By analytic-3 even a fixed power saving here would be quasi-RH.

## H. Next research direction (single recommendation)

**Look for an exact signed symmetry of the `K3` corner** — a hyperbola reflection `ij <-> X/(ij)`, a Mobius involution, or a Buchstab-type recursion that rewrites the corner as a shorter signed sum with explicit remainder. Why: this cycle proved that every sector or band localisation on the raw carrier is RH-equivalent or supertarget, and analytic-3 shows that no fixed quantitative saving is attainable short of quasi-RH; an exact structural reduction inside the bilinear corner is the one remaining place where a non-tautological, independently checkable advance can occur. Decisive test: a reflection identity verified exactly against `analytic-1` data (`N = 10^3, 3162, 10^4`) and checked for a strictly shorter support.

## I. GitHub deliverables

- Reports (this commit set): `research/agent_reports/2026-10-16/{00,90,10,20}` (new or replaced), `{30,40,50,60}` (appended), reproducers in `research/agent_reports/2026-10-16/manual-cycle/`.
- Lean: draft PR [#961](https://github.com/OVVO-Financial/RH_Lean/pull/961), branch `agent/lean-verification/20261016-root-wall-complete-fibre`, heads `cc8bc766…` → `dd066a06…`; Lean source audits run `38904295596` success; six further suites success; four legacy VF suites pending (`38904295454`, `38904295487`, `38904295391`, `38904295486`). Not merged; human-only merge.

## J. Resume capsule

- Reuse owner-1..6, analytic-1..4, wheel-4/5, census N-C/N-D, the reproducer folder, PR #961.
- Do not pursue band-local or sector-local estimates, separate `A_R`/`B_R` estimates, or fixed `(r,g)` MU-LIFT claims from finite ratios.
- Next: the `K3` corner symmetry test (section H); optionally the staircase formalization; check PR #961's pending suites before any review-state change.
- No RH proof claim.
