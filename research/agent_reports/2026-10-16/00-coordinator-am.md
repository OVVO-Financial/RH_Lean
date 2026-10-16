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


## K. Publication verification (metadata-only addendum, same run)

- Substantive publication commit on `agent-reports`: `cc967c03dea28b1f7e6e173238fe1b55487a5b94`. Every file was read back through the GitHub contents API at that commit and matched the local git blob:
  `00`/`90` mirrors `c851d93045c37bffd78d53b218fc07e37ce09a67` (identical); `10` `c8887d6daccbe2c3bf4aaa333f3344f2870349dc`; `20` `257f5f6651ec476a8890d4faf821d29687f680b5`; `30` `134eb9eb0558a622b6f042baa20f3feb847ed6f4`; `40` `26510606eea9f43450e5bb092c4542ab23fcb729`; `50` `e4c0a92301f032eb732a51f7bd997f4a19ac8b48`; `60` `6295cf70b289d7d8ba5700a9953fb466f33cb7d1`; `manual-cycle/README.md` `797dce4868581b0a455ff560fab846c25302334f`.
- The appended sections of `30`–`60` add lines only (no deletions of the scheduled runs' text).
- Lean PR #961: all eleven attached workflows green on exact head `dd066a06d752f5ee76017c687799c8b440c71609` (Lean source audits `38904295596`; four legacy VF suites `38904295487`, `38904295454`, `38904295391`, `38904295486` finished green after the synthesis); review-gap comment posted; PR marked ready for human review; **not merged**. Independent Python cross-check later extended to `6 <= R <= 520` (agreement `5.1e-11`, 0 complete-fibre failures; output sha256 `86bbfe91…0595`); the published `ledger_lab.cpp` regenerates `ledger5000.csv` byte-identically (sha256 `dbb8cd43…f926`).
- A file cannot contain its own blob hash; this addendum's commit is verified externally.


---

## Scheduled continuation — 2026-10-16T19:09-04:00

**Continuation status:** IN_PROGRESS
**Invocation:** configured Coordinator schedule, one execution; this section updates the earlier unified-manual-cycle synthesis without altering its provenance.
**Fresh authority:** `main@b9105f19fbbf25742a6909a6e8c995e6a9ddeddb`; merged #958 and #961 verified; no open PRs at intake; `agent-reports@2c55353b5e0c80799d3908840e49e99627a0074f`.

The active investigation has found an exact sign-coherence theorem for the genuine-Mobius product fibres underlying `K1/K2/K3`: for fixed product `d`, every nonzero `mu(i)mu(j)` with `ij=d` has the same sign. Equivalently, if `d=t^2 s` with `s,t` squarefree and coprime, the truncated product coefficient equals `mu(s)` times a nonnegative balanced-factorization multiplicity; if a prime cube divides `d`, it is zero. This is being audited against the full kernel and no-circularity requirements before final classification. The immediate consequence is that factor swap or any fixed-product reindexing cannot be a cancellation mechanism; any useful reflection must cross product fibres and account for the resulting sawtooth, floor, and boundary defects.


### L. What changed mathematically?

**Claim \`20261016-coordinator-3\` / \`PAPER_PROOF\` — squarefree-kernel compression of the truncated Mobius product fibre.**

For integers \`N>=1\` and \`d>=1\`, define the genuine truncated product coefficient
\`\`\`text
a_N(d) = sum_(i*j=d, i<=N, j<=N) mu(i)mu(j).
\`\`\`
If a prime cube divides \`d\`, then \`a_N(d)=0\`. Otherwise write uniquely
\`\`\`text
d=t^2*s,  s and t squarefree, gcd(s,t)=1.
\`\`\`
Define the nonnegative balanced-factorization multiplicity
\`\`\`text
A_N(s,t) = #{u | s : t*u<=N and t*(s/u)<=N}.
\`\`\`
Then
\`\`\`text
a_N(t^2*s) = mu(s) A_N(s,t).                                      (PF)
\`\`\`

**Proof.** A nonzero summand requires both \`i\` and \`j\` squarefree, so no prime exponent in \`ij\` can exceed two. For \`d=t^2s\`, every prime dividing \`t\` must occur in both factors and every prime dividing \`s\` occurs in exactly one. Thus every nonzero ordered factorization is uniquely
\`i=t*u\`, \`j=t*(s/u)\` for a divisor \`u|s\` satisfying the two truncation inequalities. Its sign is
\`\`mu(tu)mu(t(s/u))=mu(t)^2 mu(u)mu(s/u)=mu(s)\`\`.
Summing gives (PF). No analytic assumption is used.

The finite checker independently verified (PF) for every \`d<=X\` at \`N=8,17,31\`, with \`X=(N+1)^2-1\`. Repository search found the exact floor kernel and other product-fibre theorems, including a different log-square/Selberg carrier, but no existing statement of (PF) for this truncated genuine-Mobius coefficient.

**Claim \`20261016-coordinator-4\` / \`PAPER_PROOF\` — fixed-product reflection no-go.**

For fixed \`d\`, all nonzero terms \`mu(i)mu(j)\` with \`ij=d\` have the same sign. Since \`floor(X/(ij))\` and \`psi(X/(ij))\` are also constant on that fibre, no bijection or reordering that preserves \`ij\` can produce opposite-sign cancellation in \`Q_N\`, \`K1\`, \`K2\`, or \`K3\`. In particular the swap \`(i,j)<->(j,i)\` is sign-preserving, exactly as the merged hyperbola source already states. A useful reflection must move between distinct products \`d\`, flip either \`mu(s)\` or the sawtooth sign, and pay every nonintegral and boundary defect.

This is a genuine mechanism elimination, not a bound. It narrows the proposed two-dimensional involution search to cross-product transformations.

### M. Current proof objective and authority

- Live authority at this continuation: \`main@b9105f19fbbf25742a6909a6e8c995e6a9ddeddb\`; \`AGENTS.md\` and \`CURRENT_PROOF_CONTRACT.md\` were read at that exact revision.
- Canonical open theorem remains \`VFCanonicalSquareVonKochStatement\`: there exists \`C>=0\` such that \`|D_can(R)|<=C R log R\` for every \`R>=2\`.
- Merged #958 and #961 are \`PROVED_IN_LEAN_ON_MAIN\` structural incidence results only. No weighted signed estimate or returned-cell admission follows.
- All seven named reports for 2026-10-16 and 2026-10-15, plus \`EXTERNAL_HANDOFFS.md\`, were consumed. The earlier 2026-10-16 unified cycle remains one self-audited manual execution. No new external handoff postdates 2026-10-14.
- Live open-PR search returned none. The previous report's pending #961 state is superseded by live merge metadata.

The exact compression transports the full floor anatomy without changing carriers:
\`\`\`text
Q_N(X)  = sum_(d<=X) a_N(d) floor(X/d)
        = sum_(t^2*s<=X) mu(s) A_N(s,t) floor(X/(t^2*s)),
K3      = sum_(t^2*s<=X) mu(s) A_N(s,t) psi(X/(t^2*s)),
\`\`\`
with the same formula for \`K1\` and \`K2\` using weights \`1/2\` and \`X/(t^2s)\`. The sums are only over squarefree coprime \`s,t\`; \`A_N\` retains both original ordered multiplicities and both cutoffs. This is an exact coordinate change, not a quantitative gain.

### N. Competing mechanism portfolio

| Mechanism | Independent input and target route | First missing theorem | Obstruction / disposition |
| --- | --- | --- | --- |
| **SF-KERNEL / MU-LIFT** | Use (PF) to seek cancellation in the one-dimensional squarefree sign \`mu(s)\` against the nonnegative balanced weight \`A_N(s,t)\`, then recombine all \`K1/K2/K3\` regions into the whole-prefix recurrence with fixed \`r<2\` and subpower \`G\`. | A uniform cross-product estimate for the complete combined weight, with exact dyadic \`s,t\` losses and full \`B<=X<B^2\` coverage. | Fixed-product cancellation is impossible; ordinary absolute values count every nonzero pair. **CONTINUE / highest priority**, but (PF) itself is \`IDENTITY_ONLY\` as an endpoint tool. |
| **Nyman positive-Hilbert** | Exploit the independently proved coefficient extractors forcing \`c_q -> -mu(q)\`, and construct an approximant with a genuine upper norm decay. | A uniform Hilbert upper bound for an explicit full or squarefree-basis profile, with all residue correlations retained. | Rigidity is necessary, not sufficient; no decay is known. **CONTINUE** as the genuinely distinct alternative. |
| **Finite A/C or new nonlocal physical source** | Retain the native floor kernel / physical zero-target covariance and obtain a positive off-diagonal or response theorem unavailable to pure sector reassembly. | An independently proved signed restriction with exact source admission, masks, anchors, restoration and mixed terms. | Pure A/B, same-tag and fixed-cofactor variants remain suspended. No current candidate is mature enough for formalization. **REVISE / discovery mode**. |

The portfolio is deliberately not padded with the root-band inverse statistic: it is the same prime-reciprocal cut mode already identified and adds no independent input.

### O. Conceptual research and no-circularity audit

The compression is mathematically different from factor swap or hyperbola inclusion-exclusion. It quotients the full pair carrier by product and then identifies the exact surviving sign variable: the squarefree kernel \`s\` of \`d\`, not either factor separately. It also exposes a hidden positivity statement:
\`\`\`text
sum_(d<=X) |a_N(d)|
 = #{(i,j): i,j<=N, ij<=X, mu(i)mu(j) != 0}.
\`\`\`
Thus taking absolute values after grouping by product loses exactly as much as taking them on the original nonzero pair carrier; product compression does not create an unsigned saving.

**No-narrowing result.** The full desired inequality after substituting (PF) is exactly the existing MU-LIFT target, so it is not promoted as a smaller paid lemma. The genuinely new, falsifiable intermediate question is whether the structured positive multiplicity \`A_N(s,t)\` has an independently provable cross-\`s\` transform or recursion that changes the available analytic input. A rephrased bound on the whole displayed sum would be \`TARGET_EQUIVALENT\`.

**Inverse reading.** Failure of the desired bound cannot be attributed to concentration among factor pairs of one product: those terms are already coherent. A bad scale must force one or more of:
1. concentration of \`A_N(s,t)\` on squarefree kernels of one Mobius sign;
2. alignment of \`mu(s)\` with the quotient/sawtooth sign across many distinct products;
3. an uncompensated interaction between \`K1/K2\` and complementary \`K3\` regions.
These are precise cross-product configurations and can be tested without assuming the endpoint bound.

**Independent check of the manual-cycle analytic obstructions.** This continuation rechecked the logical cores of owner-4 and owner-5. The Mellin-difference argument is coherent at the stated \`[R,2R)\` / specified-prime-free-main-term scope: division by \`2^s-1\` introduces only imaginary-axis poles, while the known zero \`rho_0\` forces the prime-zeta logarithmic singularity at \`s=rho_0-1\`; the reported \`O(R/log^2 R)\` remainder is negligible for the contradiction (larger \`delta\` reduces to a smaller positive one). The B* bootstrap also closes at its stated model: after choosing \`lambda<1/4\`, iterating \`S(Y)<=C sqrt(Y)logY+lambda S(4Y)\` kills the trivial-tail remainder and sums the main series. No defect was found in this Coordinator audit. Status remains \`PAPER_PROOF\`, not Lean-certified; a dedicated independent Referee verdict is still requested, and neither result is generalized beyond its named carrier/model.

### P. Specialist findings and superseded states

- Today's Owner/Analytic/Wheel/Census/Referee/Lean reports remain the evidence summarized in the earlier synthesis. The manual-cycle self-audit does not become an independent Referee run by repetition.
- Claims owner-1/wheel-4 now have merged formal support through #961. The old report state \`PROVED_IN_LEAN_ON_PR_HEAD / NOT_MERGED\` is superseded.
- Exact-head #961 evidence was rechecked: all eleven attached workflows on \`dd066a06d752f5ee76017c687799c8b440c71609\` succeeded, including Lean source audits \`38904295596\`; the build-enforced axiom lists are \`[propext, Classical.choice, Quot.sound]\`. Merge commit is \`df47c8ae0e751ce12bd0e493156a957d86e02ee4\`.
- #958 is likewise merged at \`b0446d45037b10637522791e398a9c8ffd99f123\`. No open proof or documentation PR exists at final prepublication refresh.
- External claims \`EXT-20261014-1..5\` and \`CL-20261014-1..11\` retain their recorded scopes. In particular the original-denominator limsup no-go does not rule out the new product-fibre coordinate, but (PF) supplies no new source-payment estimate.

### Q. Mathematical bottlenecks

1. **SF-KERNEL:** determine whether \`A_N(s,t)\` admits a nontrivial transform across distinct \`s\` values. The first missing fact is quantitative cancellation of \`mu(s)\` against this exact balanced-divisor weight, not cancellation among divisors of one \`d\`.
2. **Full anatomy:** even a corner estimate must be recombined with \`K1\`, \`K2\`, and all other \`K3\` quotient ranges before comparing the final amplitude exponent \`r\` with two.
3. **Nyman:** coefficient rigidity lacks a constructive upper norm bound.
4. **Physical-source alternatives:** no exact bridge currently supplies an independently paid native zero-target covariance restriction.
5. **Formalization:** (PF) is a useful exact structural theorem, but its strategic value should be independently reviewed before Lean work; it is not a quantitative endpoint theorem.

### R. Strategy decisions

- **REJECT** fixed-product involution, factor swap, or any reordering that preserves \`ij\` as a cancellation mechanism for the genuine \`mu(i)mu(j)\` floor kernel.
- **PROMOTE** squarefree-kernel compression as the correct structural coordinate for the next MU-LIFT investigation.
- **REVISE** the proposed reflection search: require a cross-product map or transform with an explicit sign-change mechanism and exact quotient/boundary correction.
- **KEEP** Nyman positive-Hilbert as the primary independent alternative.
- **KEEP SUSPENDED** pure raw A/B reassembly and target-size control of the specified B* as independent subgoals.
- **NO QUANTITATIVE IMPROVEMENT:** the canonical endpoint, complete-source payment, finite A/C, CORR-4 and RH remain open.

### S. Next specialist assignments

- **Owner Payment:** formulate one genuine sieve/Buchstab/Vaughan or physical source identity whose bilinear remainder, after exact source admission, becomes a cross-product transformation rather than \`A+B=L\`. Falsifier: any dropped native weight, repeated occurrence, missing mask/restoration term, or remainder equal to the endpoint discrepancy.
- **Analytic Type II:** prove (PF) independently, then derive the sharpest block decomposition in squarefree \`s\` and square part \`t\`. State the smallest sufficient uniform block estimate, its final \`r,G,g\`, and whether known bounds for weighted Mobius sums apply without assuming a zero-free half-plane of comparable strength. Falsifier: the proposed estimate is merely the whole MU-LIFT target in block notation.
- **Finite Wheel & Incidence:** search for an actual map between **distinct** products \`t^2s\`, preserving integer multiplicity and cutoffs while flipping \`mu(s)\` or the sawtooth sign. Prove a boundary defect formula or a no-go for a declared local class. Fixed-product maps are now retired.
- **Prime Census Laboratory:** preregister a held-out test of squarefree-kernel sign concentration by dyadic \`s,t\` blocks, retaining exact \`K1/K2/K3\` totals and complementary regions. Compare the genuine arithmetic with a control preserving \`A_N(s,t)\` but scrambling only \`mu(s)\`; reject any proposed symmetry at its first exact counterexample. Do not rerun the settled root-band scans.
- **Adversarial Referee:** independently audit Claims \`20261016-coordinator-3/-4\`, including uniqueness of \`d=t^2s\`, truncation, zero terms and the distinction from the existing log-square product-fibre theorem. Also issue a dedicated ACCEPT/REVISE/REJECT on owner-4 and owner-5 at their exact scopes.
- **Lean Verification:** only after Referee acceptance, consider a small theorem formalizing fixed-product sign coherence and (PF) for the actual truncated Mobius coefficient. Reuse \`ArithmeticFunction.moebius\` and divisor-antidiagonal infrastructure. Do not open a PR for a conditional bound or duplicate \`signedHyperbola\`.

### T. Lean and PR status

At final refresh, \`main=b9105f19fbbf25742a6909a6e8c995e6a9ddeddb\`; no open PRs. #958 and #961 are merged. Main's documentation head has no PR-triggered workflow runs, which neither weakens nor upgrades the exact proof-head CI evidence. No new Lean implementation is authorized from this Coordinator role, and none was attempted.

### U. Next-run resume capsule

- Authority: \`main@b9105f19fbbf25742a6909a6e8c995e6a9ddeddb\`; report branch was \`agent-reports@2c55353b5e0c80799d3908840e49e99627a0074f\` before this continuation.
- New reusable claims: \`20261016-coordinator-3\` (PF squarefree-kernel compression) and \`20261016-coordinator-4\` (fixed-product reflection no-go), both \`PAPER_PROOF\`; finite regression passed at \`N=8,17,31\`.
- Highest-value next reasoning task: find or refute a cross-product transform for \`mu(s)A_N(s,t)\` that yields an estimate strictly weaker than the whole MU-LIFT target and recombines all \`K1/K2/K3\` terms.
- Preserve: full-prefix interval, ordered multiplicity, cube-free support, exact floor/sawtooth boundaries, and all source/covariance distinctions.
- Avoid: factor swap as cancellation, absolute values after product grouping, a corner-only conclusion, or treating the compressed full target as an independently paid lemma.
- Formal state: #958/#961 merged; no open PR; no new theorem requested before independent review.
- Canonical bound and RH remain open. No RH proof claim.

### V. Continuation completion

**Continuation status:** COMPLETED. The checkpoint and this final synthesis were published to both Coordinator compatibility paths with identical content; final GitHub readback is required and recorded by the invoking session because a file cannot contain its own final commit/blob hash.
