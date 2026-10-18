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

## Continuation checkpoint - 2026-10-18T19:12-04:00

**Status:** IN_PROGRESS  
**Authority refreshed:** `main@c2b075fca8a02079ebab7464a16e1fb58c2b5c7a` (merge of PR #980).  
**New investigation:** moving-window cubic stability for genuine square-shell Mobius increments.  
**Provisional classification:** `PAPER_PROOF / NEW DETERMINISTIC REDUCTION / NO_NEW_QUANTITATIVE_BOUND`.

The exact claim, literature-scope audit, updated three-mechanism portfolio, specialist assignments, and final PR/CI/readback verification are being completed below in this same scheduled continuation. The prior synthesis above remains preserved as historical evidence; its older `main@5ae5...` snapshot is superseded for this continuation.


## Final continuation - 2026-10-18T19:14-04:00

**Status:** COMPLETED  
**Continuation authority:** `main@c2b075fca8a02079ebab7464a16e1fb58c2b5c7a`; `agent-reports` evidence read through branch head `bea3f271a1ac6ab27ece41dae2f57f6be2db9df4` before this continuation.  
**New result class:** `PAPER_PROOF / NEW DETERMINISTIC REDUCTION / LITERATURE-SCOPE NO-GO / NO_NEW_QUANTITATIVE_BOUND`.

### A. What changed mathematically?

The within-shell outer-prime Type II proposal is now retired: Analytic proved that its genuine outer-prime operator is rank one, so mean-zero dispersion deletes the actual constant mode rather than bounding it. I therefore tested a genuinely different additive mechanism. It produces an exact bridge from sparse square-shell energy to an all-start moving-window mean square, together with the precise power saving that the latter must supply.

#### Claim `20261018-coordinator-2` - moving-window cubic stability

For `H>=2`, define the genuine shell increment and its rigid translates

```text
delta_r = sum_(1<=j<=2r) mu(r^2+j),
S_r(t)  = sum_(1<=j<=2r) mu(r^2+t+j),
W(H)    = sum_(H<=r<2H) sum_(|t|<=floor(r/2)) |S_r(t)|^2.
```

Then

```text
sum_(H<=r<2H) |delta_r|^3 <= 16 W(H),                         (MW1)
E(H)=sum_(H<=r<2H) delta_r^2
     <= 16^(2/3) H^(1/3) W(H)^(2/3).                         (MW2)
```

Consequently, for any fixed `eta>=0`, an independently proved all-start estimate

```text
W(H) <<_epsilon H^(13/4 - 3*eta/2 + epsilon)                 (MW3)
```

implies

```text
E(H) <<_epsilon H^(5/2 - eta + 2*epsilon/3).
```

After reparameterizing epsilon, `eta>0` beats the 7/8 Mertens benchmark through the already accepted shell-energy consumer. The random-scale heuristic `W(H) about H^3` would give `E(H) << H^(7/3+epsilon)`, corresponding to `eta=1/6`; this is a heuristic calibration, not evidence for (MW3).

**Proof.** Shifting a length-`2r` interval by `t` changes at most `2|t|` terms, each of modulus at most one. Hence

```text
|S_r(t)-delta_r| <= 2|t|.
```

For `|t|<=floor(|delta_r|/4)`, `|S_r(t)|>=|delta_r|/2`. If `|delta_r|>=4`, there are at least `|delta_r|/4` such integer shifts; if `|delta_r|<4`, the single term `t=0` gives the same claimed lower bound. Since `|delta_r|<=2r`, every selected shift lies in `|t|<=floor(r/2)`. Thus the `r`-summand of `W(H)` is at least `|delta_r|^3/16`, proving (MW1). Holder gives

```text
sum delta_r^2 <= H^(1/3) (sum |delta_r|^3)^(2/3),
```

which proves (MW2). The exponent in (MW3) follows by substitution.

This is not a target reformulation. `W(H)` is defined over every prescribed rigid translation in a fixed radius, without selecting translations from `delta_r`; its desired bound is a stronger sufficient short-interval mean-square theorem. The proof uses no PNT error estimate, Mertens bound, prime independence, favorable covariance sign, cofactor norm, or #915 carrier transfer.

#### Literature applicability audit

The Matomaki-Radziwill almost-all short-interval theorem proves cancellation for Mobius in almost all intervals whose length tends to infinity. At `X about H^2` its exceptional set and quantitative logarithmic losses are far too large to exclude all `H` square starts; boundedness upgrades its available first-moment form only to `W(H)=o(H^4)`, not the polynomial threshold `H^(13/4+epsilon)`. The later higher-uniformity theorem is likewise averaged over starting points and qualitative at the needed power scale. The 2016 paper's all-interval bilinear theorem concerns a product-variable, divisor-multiplicity average rather than the literal translated sums `S_r(t)`, and its stated logarithmic error does not supply (MW3). Sources checked: Matomaki-Radziwill, *Multiplicative functions in short intervals*, Annals 183 (2016), https://doi.org/10.4007/annals.2016.183.3.6; Matomaki-Radziwill-Tao, *An averaged form of Chowla's conjecture*, https://arxiv.org/abs/1503.05121; Matomaki-Radziwill-Tao-Teravainen-Ziegler, *Higher uniformity of bounded multiplicative functions in short intervals on average*, Annals 197 (2023), https://doi.org/10.4007/annals.2023.197.2.3.

The literature is relevant infrastructure, but no imported theorem currently proves (MW3). Classification remains `PAPER_PROOF` for (MW1)-(MW2), `CONDITIONAL` for the implication from (MW3), and `OPEN` for (MW3).

### B. Current proof objective

- Live `main`: `c2b075fca8a02079ebab7464a16e1fb58c2b5c7a`, merge of PR #980.
- Authority blobs remain `AGENTS.md` `4c66a1d462df98c84deebf0069ad11f904039858` and `CURRENT_PROOF_CONTRACT.md` `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- Canonical theorem remains `VFCanonicalSquareVonKochStatement`:

```text
exists C>=0, forall R>=2,
  |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C*R*log R.
```

The exact PNT-first `M=S-L-E`, signed shell renewal, triangular cofactor kernel, and raw transfer cone are established only at their stated identity/structural scopes. The canonical theorem, independent signed compensation, finite A/C, square-root Mertens estimate, original #915 payment, and RH remain OPEN.

### C. Competing mechanism portfolio

1. **SHIFT-L2 moving-window stability - promoted primary quantitative experiment.** Concept: replace sparse square starts by all rigid translations and use (MW1)-(MW2). Independent input: (MW3), an all-start polynomial mean-square saving on the genuine Mobius carrier. Target implication: (MW3) -> Target A shell energy -> improved Mertens exponent. First missing statement: (MW3), with literal interval endpoints and uniform dyadic `H`. Support: exact deterministic bridge and mature short-interval/averaged-Chowla machinery. Obstruction: existing theorems are averaged or logarithmic and miss the required `3/4` saving over the trivial `H^4`. Decisive experiment: exact held-out `W(H)`, cubic lower ratio, and worst translated windows. Disposition: **CONTINUE / HIGHEST DISCOVERY PRIORITY**.

2. **COFACTOR-PROFILE low-divisor kernel - continue, revised.** Wheel claims `20261018-wheel-2/-3` give exact `K_H(c)`, `E_H(c)` and every divisor profile; `d=1` is exactly the dyadic Mertens increment. `TAIL(Y)` pays only the high-divisor budget. Independent input: a signed low-divisor estimate before recombination, including `c=1`. Obstructions: the outer-prime coordinate is rank one; absolute low-range control contains the target; fixed cofactors carry coherent PNT-scale modes. Decisive test: a proposed coefficient theorem must survive `d=1`, restore all bands, and exhibit a power saving not assumed through the full energy. Disposition: **CONTINUE AS SECONDARY MULTIPLICATIVE LANE; RETIRE WITHIN-SHELL q-DISPERSION**.

3. **ORIGINAL-VF cross-anchor payment - distinct direct route.** Independent input: an occurrence-faithful, once-only masked transfer and quantitative payment retaining native weights, clips, squareful restoration, historical anchor, global residual and the unchanged NNS norm. Owner's transfer cone, now compiled on main, proves scalar Mobius/native norm substitution is invalid and has PNT-sized raw slack. Decisive test: reconstruct the full native carrier at adverse roots with every cross term and no reused ancestor. Disposition: **CONTINUE SEPARATELY; DO NOT INFER IT FROM SHELL MOBIUS RESULTS**.

HECKE-LOW remains a valid stronger sufficient comparator, but no October 18 finding promotes it over these three. The portfolio is not widened by renaming `M=P0-2P1` or the full `d=1` row.

### D. Conceptual research performed

The new investigation worked backward from failure. A large `|delta_r|` cannot occur at an isolated square start: interval sums are 2-Lipschitz under translation, so it forces a neighborhood of about `|delta_r|` nearby starts with size at least `|delta_r|/2`. Cubing is therefore the correct deterministic cost of a bad shell. Summing and applying Holder yields (MW2).

This changes the analytic question. A direct square-start theorem could hide all square starts in an exceptional set. The moving-window theorem cannot: it asks for the complete local `L^2` mass around every shell. Conversely, it is genuinely stronger than Target A and may be false at the requested exponent; that is why the finite experiment and a literature-level mean-square attack are decisive rather than cosmetic.

No new quantitative Mobius bound was proved. The conceptual gain is a precise independent theorem with a numerical exponent budget and an explicit literature obstruction, not another exact rewriting of `E(H)`.

### E. Specialist findings

- Owner `4655c4379f9a5d4b13a9f43c1c1c0addfe90d836`: exact three-sector raw transfer cone and fixed-fibre PNT lower slack; Referee accepted it. Its scalar algebra is now `PROVED_IN_LEAN_ON_MAIN` through #980, while the occurrence partition and PNT lower application remain `PAPER_PROOF`.
- Analytic `f7b981952037bffa17c67b518edb0c5638f01f05`: the proposed within-shell outer-prime tile is rank one; cross-shell Abel is exact but needs a new variation theorem. `PAPER_PROOF / LOCAL TYPE-II NO-GO`.
- Wheel `1f2e83a07d2d277f1137fd0239109f3abea5cbee`: exact triangular cofactor incidence and compensated divisor-profile conservation. `PAPER_PROOF / IDENTITY_ONLY` for quantitative purposes. Earlier Wheel `62da494755501409879e894779d026aed70835f8` proves two-prime shell orbits are sign-coherent.
- Census `701b74c281d01f6727669808566d76b1e8758b26`: held-out finite data refute fixed shallow-depth and band-only sign predictors; `FINITE_COMPUTATION / REFUTED` at those stated scopes.
- Referee `c0360eaa56c34198f21f9387113fd565a19b542f`: accepts the anchor residue, `TAIL(Y)`, rank-one no-go and raw cone; rejects target-containing low complements. `PAPER_PROOF / ACCEPT`, no quantitative endpoint gain.
- Lean `bff111a9448b17061f4dc2be760ea8422245a3f6`: formalized the cone at head `c1d261e...`; its report's “open” PR status is superseded by the verified human merge #980 at `c2b075f...`.
- October 17 carry-forward remains as recorded above. The old one-prime toggle, two-prime orbit, fixed-depth, quotient-wall, and generic norm barriers remain active; no missing handoff was invented. The duplicate Wheel trigger is recorded rather than counted as a new schedule.
- External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` was consumed. Its PNT-first exact identity is live; older Hecke and cross-coordinate entries remain comparison lanes with their original evidence classes.

### F. Mathematical bottlenecks

- **SHIFT-L2:** prove or refute (MW3). Required power saving over the trivial `W(H)=O(H^4)` is `H^(3/4+3eta/2)` up to epsilon. “Almost all intervals” or a logarithmic saving is insufficient.
- **COFACTOR-PROFILE:** control the complete signed low-divisor channel, including `d=1`, without assuming the recombined shell energy. Neither PNT density nor outer-prime centering supplies it.
- **ORIGINAL-VF:** construct the exact masked occurrence bridge and prove a payment on the unchanged native norm. The on-main cone is an obstruction, not that bridge.

### G. Strategy decisions

- Retire the current within-shell `q/p` dispersion tile; its only surviving mode is the unpaid constant mode.
- Promote moving-window stability as the next falsifiable analytic experiment because it supplies a genuinely different carrier and exact power budget.
- Keep the triangular cofactor kernel as the principal multiplicative comparator, but reject any result that deletes `d=1` or takes norms before band reassembly.
- Keep direct #915 work separate. The raw cone prevents a scalar transfer from Mobius energy to native VF energy.
- Do not formalize the unproved bound (MW3). The deterministic lemma may be formalized after independent referee review because it is carrier-generic and assumption-free.

### H. Next specialist assignments

- **Owner Payment:** audit whether any translated interval in `W(H)` has a legal occurrence-level image in the original #915 carrier. Expected valid output is either an exact once-only map with every mask/anchor/restoration term or a minimal obstruction. Do not convert unit Mobius weights into native weights through the scalar cone.
- **Analytic Type II:** independently verify (MW1)-(MW3), then attack the literal all-start `W(H)` by Dirichlet-polynomial or bilinear short-interval methods. State the strongest theorem actually available, its exceptional set and power loss. Falsifier: a proof yielding only `o(H^4)` or logarithmic saving does not reach `H^(13/4+epsilon)`.
- **Finite Wheel & Incidence:** expand `W(H)` exactly by shifts `h`, gcd/squarefree gates, unshared-prime parity and translated square boundaries. Identify whether a multiplicative subkernel has a true power-saving complement. Falsifier: fixed-depth or favorable-sign truncations already fail.
- **Prime Census Laboratory:** compute exact `W(H)`, `sum|delta|^3`, `E(H)`, the ratio in (MW1), worst `S_r(t)`, and `W/H^(13/4)` on predeclared dyadic training and held-out blocks. Include boundary shifts and exact integer checks. Reject fitted exponents as proof.
- **Adversarial Referee:** audit the constant 16, integer endpoints, Holder exponent, non-equivalence claim, and literature transfer. Try bounded-sequence countermodels separating `W` from `E`, and determine whether any cited theorem really gives polynomial `L^2` saving at every start.
- **Lean Verification:** after Referee acceptance and repository search, formalize only the generic translation-stability/cubic-to-quadratic implication, with the quantitative `W` estimate as an explicit hypothesis if a consumer is included. Do not encode (MW3) as established arithmetic.

### I. Lean and PR status

PR #980 is merged, not open: proof head `c1d261e2a265f7ada3c6abf1e0b1a128009a4979`, merge `c2b075fca8a02079ebab7464a16e1fb58c2b5c7a`. All ten returned exact-head Actions runs completed successfully, including warning-fatal cone compilation and axiom audit. On main the declarations are:

- `RHLean.Analysis.rawTransferCone_sq_sub_sq`
- `RHLean.Analysis.rawTransferCone_sq_nonneg`
- `RHLean.Analysis.rawTransferCone_moebius_sq_le_native_sq`

Their audited axiom footprint is `[propext, Classical.choice, Quot.sound]`. No open or draft PR was returned at final search. These theorems establish only the raw scalar cone; no signed saving, occurrence bridge, canonical bound or RH result is compiled.

### J. Next-run resume capsule

- Main SHA: `c2b075fca8a02079ebab7464a16e1fb58c2b5c7a`.
- New claim: `20261018-coordinator-2`, (MW1)-(MW2), `PAPER_PROOF / NEW DETERMINISTIC REDUCTION`.
- Open quantitative input: (MW3), `W(H)<<H^(13/4-3eta/2+epsilon)`; no current literature theorem was verified to supply it.
- Surviving multiplicative claims: Analytic rank-one no-go; Wheel triangular kernel/profile; `TAIL(Y)` high-divisor budget; `d=1` remains the target mode.
- Formal update: #980 merged and CI green; raw cone now `PROVED_IN_LEAN_ON_MAIN` only at scalar scope.
- Highest-value next reasoning task: determine whether a genuine all-start short-interval Mobius `L^2` theorem reaches any fixed power below `H^4`; if not, prove a structural obstruction or locate an arithmetic subkernel whose complement is independently below the (MW3) threshold.

**Publication state:** final report content prepared for byte-identical write to `90-coordinator-pm.md` and compatibility mirror `00-coordinator-am.md`; readback and branch-head verification follow this paragraph.
