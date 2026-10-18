# RH_Lean Coordinator synthesis - 2026-10-18

**Status:** COMPLETED
**Run ID:** 2026-10-18T11:55:28-04:00, scheduled invocation
**Completed:** 2026-10-18T12:00:33-04:00
**Agent:** RH | Research Coordinator / Proof Architect
**Reporting rule:** `00-coordinator-am.md` and `90-coordinator-pm.md` are byte-identical compatibility mirrors of this one run, not two executions.

## A. What changed mathematically?

The new result is a PNT-scale obstruction to a direct local use of the only cofactor windows visible inside the original #915 half-run.

### Claim `20261018-coordinator-1` - anchor-visible prime-density residue

For `r>=2` and fixed `1<=c<=r`, put
[
P_r(c)=pi(lfloor((r+1)^2-1)/cfloor)-pi(lfloor r^2/cfloor).
]
For each fixed `c in {1,2,3}` and `H` beyond the finite boundary cases,
[
sum_{Hle r<2H}P_r(c)
=#{p {m prime}:H^2<cp<4H^2}
=pi(4H^2/c)-pi(H^2/c)+O(1).
]
The strict shell intervals are disjoint and exhaustive. A missing boundary would require `cp` to be a square. For `c=1` this is impossible for prime `p`; for `c=2,3` it forces the finite cases `p=c`.

Merged #978 proves that, for `R>=13`, the cofactor-window top lies in the original half-run exactly for `c<=3`. Since `mu(1)=1` and `mu(2)=mu(3)=-1`, the literal anchor-visible high-prime part of
[
delta_r=a_r^{smooth}-sum_{cle r}mu(c)P_r(c)
]
is
[
A_r^{anchor}=-P_r(1)+P_r(2)+P_r(3).
]
Ordinary PNT now gives
[
sum_{Hle r<2H}A_r^{anchor}
sim {3H^2over2log H}(-1+1/2+1/3)
=-{H^2over4log H}.                                      	ag{AR}
]

**Consequence.** The `c=1,2,3` high-prime modes do not cancel even at their first dyadic moment. A direct #915 payment cannot be obtained by balancing only the prime-only mode with the other two anchor-visible cofactor modes. It must transport compensating mass from `c>=4` through the compressed historical anchor, or use an occurrence-legal smooth/cross-owner term with the original weights and restoration.

**Status:** `PAPER_PROOF / PNT-SCALE LOCAL-MECHANISM NO-GO / INDEPENDENT_REFEREE_PENDING`. This is not a shell-energy bound, a Mertens estimate, a bridge from Mobius signs to native VF charges, or an RH result.

Exact finite checks support the sign and scale:

| H | sum P(1) | sum P(2) | sum P(3) | sum A_anchor | A_anchor log(H)/H^2 |
|---:|---:|---:|---:|---:|---:|
| 64 | 1,336 | 719 | 503 | -114 | -0.115750 |
| 128 | 4,642 | 2,484 | 1,729 | -429 | -0.127046 |
| 256 | 16,458 | 8,739 | 6,032 | -1,687 | -0.142742 |
| 512 | 59,025 | 31,139 | 21,457 | -6,429 | -0.152993 |
| 1,024 | 213,922 | 112,221 | 77,035 | -24,666 | -0.163051 |
| 2,048 | 781,924 | 408,552 | 279,728 | -93,644 | -0.170231 |

The slow drift is compatible with the PNT limit `-1/4`; the table is evidence, not the proof.

## B. Current proof objective

Fresh final authority:

- `main@5ae5a524ca447d1936e351bbbe4b134c068a1a13`, merge of PR #979.
- `AGENTS.md` blob `4c66a1d462df98c84deebf0069ad11f904039858`.
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- Primary PNT-first contract blob `e8acbeff24942d1f8ee0079f715afff2ddda2c33`.
- Two-scale attack plan blob `0606d764ffebb4639cc0abb52ccbef30546b7764`.

The canonical open theorem is still
[
{	t VFCanonicalSquareVonKochStatement}:
exists Cge0, orall Rge2, |D_{can}(R)|le CRlog R.
]
The public carrier remains actual `pi-VF_can`. The proved `VF_can-Li_2=O(1)` does not bound it.

PR #977 makes the PNT-first signed cofactor/historical-return seam primary. PR #979 makes the `S=A-T` two-scale plan the next experiment. Text inside the contract saying "pending merge" and text inside the plan calling #978 draft are stale status labels: live GitHub records show #978 and #979 merged. Their mathematical warnings remain correct; neither merge proves a signed estimate.

## C. Competing mechanism portfolio

### 1. Compensated q/p Type II shell tile - primary

**Concept.** Use the exact `delta_r=C_r-Q_r` carrier and outer-prime interchange for `sum Q_r C_r`, then center the q-prime/p-prime/cofactor tile by the genuine smooth divisor compensator before taking norms.

**Independent input.** A uniform power-saving estimate on a complete centered low-divisor tile, including `c=1` and every complement, together with the paper `TAIL(Y)` estimate for `Y=r^(1/2+kappa)`.

**Target implication.** Reassemble
[
mathcal E(H)=sum_{Hle r<2H}delta_r^2
ll_epsilon H^{5/2-eta+epsilon};
]
then the existing square-clock argument yields Mertens exponent `7/8-eta/4`.

**First missing theorem.** A coefficient-level low/middle-divisor dispersion bound with exact shell walls, both prime variables, Mobius cofactor signs, smooth companion, and the `d=1` mode. `TAIL(Y)` alone only moves the boundary of the unpaid range.

**Obstructions.** #976 proves same-base two-prime covariance is positive. Wheel claim `20261018-wheel-1` rules out two-prime within-orbit cancellation. Census and Referee refute control by the first cancelling depth `t=3`. The external 7/8 prefix estimate gives no short-window saving.

**Decisive experiment.** Predeclare dyadic `c` scales and measure the complete centered tile plus its exact complement, not a Li-only model. Disposition: **CONTINUE / HIGHEST PRIORITY**.

### 2. Cross-shell signed renewal - second quantitative gate

**Concept.** After any single-shell gain, use actual lagged smooth/high prime-cofactor sources across distinct square shells, preserving shared-prime and distinct-prime ownership.

**Independent input.** A restricted positive-lag bilinear theorem with an arithmetic phase and a separately bounded complement; no blanket negative covariance premise.

**Target implication.** Control the off-diagonal part of
[
(sum_{rin J}delta_r)^2
=sum_rdelta_r^2+2sum_{r<s}delta_rdelta_s
]
at the square-root Mertens scale, then use the compiled classical consumer.

**First missing theorem.** A real cross-shell correlation estimate. The sign `mu(c)mu(c+1)` varies, and the minus sign in `S=A-T` supplies no restorative drift by itself.

**Decisive experiment.** Exact lag matrix separated by shared outer prime, distinct outer prime, cofactor shift, and birth/death boundary on held-out dyadic blocks. Disposition: **REVISE / DISCOVERY**, not yet ready for Lean.

### 3. Original #915 cross-anchor payment - distinct direct-VF route

**Concept.** Map the PNT-first cofactor source into the original weighted, masked, clipped first-bad carrier while keeping the positive historical residual from #975.

**Independent input.** An occurrence-preserving cross-anchor transport theorem and a norm-compatible upper bound carrying the `c>=4` compensation into a strictly lower contiguous child-run exactly once.

**Target implication.** A legal first-bad contradiction for the original canonical VF theorem, bypassing a full Mertens bound.

**First missing theorem.** The cross-anchor bridge and quantitative payment. Claim (AR) proves that `c<=3` alone has the wrong macroscopic balance; #975 proves that the historical residual cannot be dropped.

**Decisive experiment.** Reconstruct the full native charge for the `c<=3` visible part and the `c>=4` compressed part at `R=317,1027` and adverse held-out roots, including masks, anchors, squareful restoration and mixed terms. Disposition: **CONTINUE, STRICTLY SEPARATE FROM THE UNWEIGHTED SHELL CLAIM**.

HECKE-low, full K1/K2/K3, Nyman and finite A/C remain comparators. They are not promoted over the merged PNT-first selector in this run.

## D. Conceptual research and no-circularity audit

Claim (AR) works backward from a hypothetical local payment. If only the windows visible in the original half-run were used, their prime-density contribution would have to be negligible or restorative. Instead it has a forced negative main term of order `H^2/log H`. Therefore a successful proof must reveal where an opposite main term enters across the anchor or from the complete smooth source.

The proof uses only strict-shell geometry, #978's compiled anchor localization, the exact signs of `mu(1),mu(2),mu(3)`, and ordinary PNT. It assumes no bound on `M`, `delta`, `E_R`, shell energy, or the canonical defect. It is therefore independent, but negative. It does not show the full source is large, because the omitted `c>=4` and smooth contributions may compensate it. It also cannot be transferred to #915 merely by reading Mobius sign as native VF charge.

The outer-prime reindex and smooth compensator remain `IDENTITY_ONLY`. The proposed `TAIL(Y)` bound is an elementary `PAPER_PROOF` candidate, but the `d=1` row contains the full shell mode. Any "low-range theorem" that assumes its recombined alternating sum is small is `TARGET_EQUIVALENT`.

Merged #978 adds exact Lambda-hyperbola identities, not a saving. Its total error contains
(-sum_{nle X}mu(n)log n-1), hence a term (-M(X)log X+int_1^X M(t)dt/t) after summation by parts. Bounding the complete high-plus-dual Lambda error at target strength would rehouse the target. A usable Lambda mechanism must bound one independently structured sector and its complement without assuming this total.

## E. Specialist findings and continuity

Today's available reports preceded the 14:00-15:55 EDT PNT-first and two-scale merges, so they are accepted at their stated shell scope but superseded as mechanism selection:

- Wheel blob `62da494755501409879e894779d026aed70835f8`: exact shell divisor antichain; two-prime orbits are sign-coherent. `PAPER_PROOF`, later formally specialized by #976.
- Census blob `08d80d6fe5f8114e210d6e50f5939603a511994e`: complete alternating-depth finite data; the `t=3` mechanism changes sign after restoring higher depths. `FINITE_COMPUTATION / REFUTED`.
- Referee blob `096513f9a32d79bc6699719fcac3c997572b31f0`: accepts the antichain scope and gives the minimal `r=9` fixed-depth falsifier.
- Lean blob `0ed62011c7a02051b634928b10ef670380033e34`: #976 exact two-prime positive-pair theorem, then review-ready; it is now merged.
- Today's Owner and Analytic reports are absent: **TODAY=PENDING**. No execution or result is inferred.

The complete 2026-10-17 report set was read as `YESTERDAY=CARRY_FORWARD`, including Coordinator blob `9a797b07dcd7c74147b6b0cdbc8f6a69024c3961`, Owner `6980422de5f7cc55b9dec32a2f0fe21f98ed7ff1`, and Analytic `08e96ac308fc08f59f2e4f5c82a70ba7d901c97e`. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` was consumed. `EXT-20261018-PNT-1..3` are incorporated at exact identity, finite falsifier and source-no-go scopes.

## F. Mathematical bottlenecks and decisions

1. **Stage A shell gain:** no independent low/middle-divisor estimate pays `d=1`, the q-prime square and every compensator complement. Continue.
2. **Stage B renewal:** no cross-shell arithmetic covariance theorem exists. Revise; do not assign sign by analogy.
3. **Direct VF:** no source-legal cross-anchor bridge or child-run contraction exists. Continue only with original weights and #975 residual restored.
4. **Lambda interface:** exact and compiled, but quantitatively target-rehousing unless a sector-specific estimate is proved. Keep as a diagnostic, not a fourth active mechanism.
5. **Retire:** local one-prime toggles, two-prime within-orbit cancellation, first-cancelling-depth control, and any anchor-visible `c<=3` density cancellation.

No Mertens exponent, zero-free line, finite A/C bound, canonical VF estimate, or RH theorem improved in this run.

## G. Next specialist assignments

- **Owner Payment:** give an occurrence-level decomposition of the original #915 source into the `c<=3` anchor-visible part and the `c>=4` compressed part. Reuse #975/#978, keep native weights, masks, squareful restoration and global residual. A valid output is an exact once-only bridge plus the first unsigned/unpaid mixed term. Falsifier: any reused parent, Mobius-sign/VF-charge substitution, or omitted anchor term.
- **Analytic Type II:** independently prove or sharply refute Claim (AR), then formulate one complete dyadic q/p/cofactor tile with `P*C roughly H^2`, exact walls, `mu(c)`, smooth compensator and every remainder. Quantify the conditional `eta` after optimizing `Y=r^(1/2+kappa)`. Falsifier: pointwise short-interval PNT, an assumed `c^(-1/8)` gain, or a premise equal to full shell energy.
- **Finite Wheel & Incidence:** derive the exact cross-anchor incidence kernel for `c>=4`: which source occurrence can legally couple to `c=1,2,3`, which block owns it, and which matches are forbidden. Include `p=r` endpoint distinctions. Falsifier: approximate q/p windows or guaranteed negative cofactor signs.
- **Prime Census Laboratory:** independently reproduce the dyadic anchor residue at predeclared held-out `H>2048`; then measure the complete centered tile and its complement by cofactor scale. Record integer identities before Li approximations. Falsifier: fitted exponents, only in-sample roots, or a residual normalized by the target.
- **Adversarial Referee:** audit Claim (AR), including strict endpoints, the `cp` square exceptions, PNT constants, and the precise transfer from #978's prefix anchor to shell increments. Separately audit `TAIL(Y)` and try to expose any hidden `d=1` target equivalence.
- **Lean Verification:** do not formalize Claim (AR) before Referee acceptance. Search first for an existing outer-prime reindex and parameterized divisor-tail theorem. If absent and accepted, formalize only those exact/elementary statements on a proof branch with warning-fatal compile and axiom audit; attach no quantitative consumer until the analytic input exists.

These are assignments for the agents' next actual authorized executions. No additional run or schedule is implied.

## H. Lean and PR status

- **#975:** merged at `860d78ee2f22e687c585c803e2213a3074c82296`; original first-bad historical residual obstruction is on main. It proves no signed gain.
- **#976:** merged at `345b435770be66288b56f2e01f31e44e237a1ea0`; exact two-prime positive-pair no-go is on main.
- **#977:** merged at `fd0a1dfaa2911da936aa815af61819387577f76b`; research-direction documents only.
- **#978:** merged at `742b0584fdd580ca37f2d3b9a2a6aedf1c12daaf`; proof head `ba89ca4e5fc6a341ca0422698ec40b4646480000`; all ten returned exact-head workflows succeeded. Its Lambda/anchor interfaces are `PROVED_IN_LEAN_ON_MAIN`, with no estimate.
- **#979:** merged at current main; attack plan and finite falsifier, no new Lean cancellation theorem.
- **#969:** still merged only into its stacked non-main base; its three OAI files are absent from current main. Status remains `PROVED_IN_LEAN_ON_NONMAIN_BRANCH / INTEGRATION_REQUIRED`.
- Final open-PR search returned none. No proof branch, PR, merge, rerun or review-state mutation was performed by this Coordinator.

## I. Next-run resume capsule

- Authority: `main@5ae5a524ca447d1936e351bbbe4b134c068a1a13`.
- New claim: `20261018-coordinator-1`, anchor-visible prime-density residue (AR), `PAPER_PROOF / LOCAL-MECHANISM NO-GO / REFEREE_PENDING`.
- Primary route: compensated q/p Type II shell tile; first missing theorem is a genuine low/middle-divisor dispersion estimate including `d=1` and all complements.
- Direct VF route: must cross the #978 anchor and preserve #975's positive historical residual; `c<=3` alone leaves (-H^2/(4log H)).
- Retired local ideas: one-prime toggle, two-prime within-orbit cancellation, fixed first cancelling depth, and anchor-visible density cancellation.
- Missing today: Owner and Analytic remain `PENDING`.
- Highest-value next reasoning task: construct or refute an exact occurrence-preserving coupling between the macroscopic anchor-visible residue and the `c>=4` compressed/smooth response, then test whether a dyadic Type II estimate controls that coupling without assuming shell energy.
- No RH proof claim.


---

## Continuation checkpoint - 2026-10-18T19:32-04:00

**Status:** IN_PROGRESS  
**Authority refreshed:** `main@c2b075fca8a02079ebab7464a16e1fb58c2b5c7a` (merge of PR #980).  
**New investigation:** moving-window cubic stability for genuine square-shell Mobius increments.  
**Provisional classification:** `PAPER_PROOF / NEW DETERMINISTIC REDUCTION / NO_NEW_QUANTITATIVE_BOUND`.

The exact claim, literature-scope audit, updated three-mechanism portfolio, specialist assignments, and final PR/CI/readback verification are being completed below in this same scheduled continuation. The prior synthesis above remains preserved as historical evidence; its older `main@5ae5...` snapshot is superseded for this continuation.
