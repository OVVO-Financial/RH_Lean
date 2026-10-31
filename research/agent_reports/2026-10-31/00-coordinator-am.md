# RH_Lean Coordinator research report - 2026-10-31

**Status:** COMPLETED
**Role:** RH | Proof Architect
**Invocation:** scheduled run begun 2026-10-31 07:10 America/New_York
**Final authority refresh:** 2026-10-31 07:14 America/New_York
**Pinned live main:** `6b2a869750b92fcdbebff78a591e7722b4f2c747`
**Authority blobs:** `AGENTS.md d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md 7a067ec0423a998e1079e37494061346d8ee02b0`; stable selector `497c59885bf1da401bfc755e6980d1548ce167f0`; all-vector directive `a2892b6641268e1ac1ce08622bbe53445fe2e8eb`.
**New claim:** `20261031-coordinator-1`.
**Evidence classes:** `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW / SOURCE-FAITHFUL WEIGHTED RESONANCE DIAGONAL`; `PAPER_PROOF / EXACT SECOND-MOMENT OBSTRUCTION`; `NO_COMPLETE_SOURCE BOUND`; `NO_FIXED_ETA GAIN`; `NO_RH`.

## A. What changed mathematically?

The corrected root-dependent resonance is not merely an obstruction. After root-period averaging it admits an unconditional, source-faithful coefficient-weighted bound on the literal moving Euler coefficient. Let

```text
beta_R(n) = sum_(1 <= a < b < R, ab=n) mu(a)mu(b),
delta(R,j,k) = gcd(j^2,jR+k).
```

For every real `eps>0` there is `C_eps>0` such that for integers
`H>=2`, `j>=1`, `0<=k<H`,

```text
sum_(H <= R < 2H) delta(R,j,k) * |beta_R(jR+k)|^2
 <= C_eps * (((2j+1)H)^eps) * (H+j) * gcd(j,k) * tau(j).       (1)
```

This is a genuine new restriction on the actual partially admitted source. It pays the coefficient-weighted resonance-admission diagonal that occurs after complete quadratic summation. It does not control the signed incomplete phase, cross-`(j,k)` terms, principal mode, diagonal of the original double source, reciprocal square, or endpoint restoration.

There is also a decisive order-of-operations obstruction. For `p^a || j` and `b=v_p(k)`, the local factor in the exact second root-period moment is

```text
B_p(a,b) = p^(2b),                                      if b<a,
           p^(2a-1) * ((p+1)p^a-1),                    if b>=a,
```

and

```text
(1/j) * sum_(0 <= r < j) delta(r,j,k)^2
  = product_(p^a || j) B_p(a,v_p(k)).                   (2)
```

For prime `j=p`, `k=p`, the first moment is `2p-1` but the second moment is `p^3+p^2-p`. Thus squaring branch multiplicities before root averaging loses a factor of order `p`; an analytic completion must average the natural Gauss energy, proportional to `delta`, before another Cauchy step.

## B. Current proof objective

At live `main@6b2a869750b92fcdbebff78a591e7722b4f2c747`, the canonical objective remains

```text
exists C>=0, forall R>=2,
  |pi(R^2)-VF_can(R^2)| <= C R log R.
```

The eligible nearer benchmark is a complete original-source square-shell estimate: for one fixed `eta>0`, every `eps>0`, and all sufficiently large `H`,

```text
sum_(H <= R < 2H) |Delta_R|^2
  <= C_(eta,eps) H^(5/2-eta+eps).
```

The source carrier remains the strict signed `2*eulerFractionOffQ R`, with moving `1<=a<b<R` admission, actual principal, low/high products, activation, mixed terms, fractional diagonal, reciprocal square, and endpoint restoration. Neither bound is proved. The square-shell benchmark is not compulsory for a separately verified VF, finite-A/C, CORR4, MU-LIFT, OAI, or Nyman consumer.

## C. Competing mechanism portfolio

### 1. Root-period quadratic operator - highest priority, CONTINUE

- **Concept:** complete the exact quadratic congruence on each moving band, average the corrected `delta(R,j,k)` over root periods, and estimate the centered incomplete operator only after the weighted resonance diagonal is paid by (1).
- **Independent input:** a coefficient-weighted incomplete quadratic large-sieve estimate on the actual moving coefficients, with zero mode and partial final periods explicit.
- **Target implication:** after adding principal, primitive, resonant, cross-band, diagonal, reciprocal-square, and restoration ledgers, obtain the full shell moment or a proper CODIV/OAI source estimate.
- **First unproved step:** off-diagonal cancellation between distinct `(j,k)` columns. Equation (1) is only its diagonal admission budget.
- **Support:** `20261031-analytic-1` pays the `j=1`, `k<=sqrt R` wedge; `20261031-wheel-1` gives the corrected lifts; `20261031-referee-2` gives the first period moment; (1) adds the literal moving coefficient.
- **Obstruction:** maximal roots exist; (2) forbids a proof that squares multiplicities before averaging. The coefficient may correlate with exceptional roots.
- **Decisive experiment:** exact Gram spectra for complete root periods with the zero mode removed, stratified by `gcd(j,k)` and compared to the bound in (1), including the family `k=j`, `R=-1 mod j`.

### 2. First-band factor-depth bilinear - CONTINUE WITH CAUTION

- **Concept:** exploit the exact first-band identity `beta_R(R+k)=alpha(R+k)-mu(R+k)` and the squarefree depth law `(-1)^r(2^(r-1)-1)` jointly with the rational square-clock phase.
- **Independent input:** an all-scale signed far-band moment, including squareful correction and near/far covariance.
- **Target implication:** pay the remaining first band as a proper component before later-band synthesis.
- **First unproved step:** cancellation between different moduli/depths; within one squarefree product fibre all factor-pair terms are coherent, so depth classification alone is not cancellation.
- **Support:** the near wedge is accepted at `H^(2+o(1))`; Census gives exact arithmetic through `H=2048` and broad depth cancellation.
- **Obstruction:** the far phase can be order one; the mixed term changes sign; finite normalized energy does not prove a power saving.
- **Decisive experiment:** held-out covariance matrix by squarefree depth and phase level, with squareful rows and the near/far cross term restored.

### 3. MU-LIFT signed recurrence - independent reserve, CONTINUE

- **Concept:** use the exact signed hyperbola/Newton/Heath-Brown identities to prove a whole-prefix recurrence `E(B^2)<=G(B)E(B)^r` with fixed `r<2` and subpower `G`.
- **Independent input:** an arithmetic signed Type-II bound for the complete genuine Mobius rows, not a recurrence defined from the desired ratio.
- **Target implication:** the compiled amplification budget yields `MertensGrowthAtMost(1/2)` after full-prefix interpolation.
- **First unproved step:** a uniform complete-row estimate retaining overlap and all `K1/K2/K3` ranges.
- **Support:** merged exact lift and signed hyperbola infrastructure.
- **Obstruction:** `r=2` is noncontractive; endpoint-only or favorable-subsequence control is insufficient.
- **Decisive experiment:** adversarial synthetic prefixes satisfying the same scalar envelope, used only to reject premises lacking genuine arithmetic content.

Complete inverse-weighted owner-fibre reciprocal contraction is REJECTED as a mechanism by `20261031-owner-1`. Cross-parent plus terminal covariance remains a necessary subproblem of Mechanism 1/S2, not a fourth independent mechanism.

## D. Conceptual research performed

### Proof of claim `20261031-coordinator-1`

For fixed `(j,k)`, `delta(R,j,k)` is periodic in `R mod j`. Accepted claim `20261031-referee-2` proves

```text
sum_(0 <= r < j) delta(r,j,k) <= j*gcd(j,k)*tau(j).      (3)
```

An interval of `H` consecutive roots is covered by at most `H/j+1` complete residue periods. Positivity and (3) give

```text
sum_(H <= R < 2H) delta(R,j,k)
 <= (H+j)*gcd(j,k)*tau(j).                              (4)
```

The moving coefficient is a sum of original strict factor pairs, each of absolute value at most one. Hence

```text
|beta_R(n)| <= tau(n).
```

The classical divisor bound gives, for every `eps>0`,
`tau(n)^2 <= C_eps n^eps`. For `n=jR+k`, `H<=R<2H`, and `0<=k<H`,
`n<=(2j+1)H`. Multiplying this uniform bound by (4) proves (1). No completed coefficient, frozen activation, stochastic independence, or sign assumption is used.

For (2), CRT separates prime powers. If `p^a || j` and `v_p(k)=b<a`, the local multiplicity is constantly `p^b`. If `b>=a`, write the local factor as
`p^(a+min(a,v_p(x)))` with `x` uniformly distributed modulo `p^a`. There are `p^(a-t)-p^(a-t-1)` residues of valuation `t<a` and one zero residue. Averaging the square yields

```text
p^(2a) * ((1-1/p) * sum_(0<=t<a) p^t + p^a)
 = p^(2a-1) * ((p+1)p^a-1).
```

CRT proves (2).

### No-narrowing review

Claim (1) is unconditional and strictly weaker than the needed incomplete moment: it is a nonnegative diagonal bound and contains no signed phase cancellation. The full shell target could hold through cancellation while an isolated component is large, and (1) does not imply the target without new off-diagonal, principal, and restoration estimates. It is therefore neither target-equivalent nor a renamed shell norm.

## E. Specialist findings

- `20261031-owner-1`: `PAPER_ACCEPTED_WITH_SCOPE`. Physical inverse weighting cancels every positive owner-prime decay on a complete fixed-owner fibre; `{(1,pq),(p,q)}` gives an infinite exact mass-2 counterfamily. This independently confirms and sharpens the merged local obstruction, but Wheel notes it is not a distinct second mechanism from its Oct 30 parent-fibre result.
- `20261031-analytic-1`: `PAPER_ACCEPTED_WITH_SCOPE`. The literal `j=1`, `1<=k<=sqrt R` wedge has energy at most `8H^2(log(4H)+6)^2`. The far first band and all other source terms remain open.
- `20261031-wheel-1`: `PAPER_ACCEPTED_WITH_CORRECTION`. The old identity `gcd(j^2,jR+k)=gcd(j^2,k)` is REFUTED; the exact root-dependent lift set and maximal family are correct. The invertible criterion `delta=1 iff gcd(j,k)=1` survives.
- `20261031-census-1`: `PAPER_PROOF` for the exact squarefree depth law plus `FINITE_COMPUTATION` through `H=2048`. The conjectured far-band exponent is unresolved; mixed energy changes sign.
- `20261031-referee-2`: `PAPER_PROOF`. The exact first period moment of `delta` and divisor-loss upper bound are accepted structural inputs, not an incomplete moment.
- `20261031-lean-1`: `FORMAL_REVIEW_COMPLETE`. PR #1060 is `PROVED_IN_LEAN_ON_PR_HEAD / CI_GREEN / REVIEW_READY`, with no new declaration opened today.

All six Oct 31 reports were present. Available Oct 30 Coordinator, Analytic, Wheel, Census, Referee, and Lean reports were consumed. No Oct 30 Owner report exists; it remains explicitly missing rather than inferred. `EXTERNAL_HANDOFFS.md` blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than Oct 18 and does not supersede the live selector.

## F. Mathematical bottlenecks and route coverage

| Route | Status after this run | First independently missing theorem / next action |
|---|---|---|
| VF-LOW | OPEN; owner-fibre local contraction rejected | Complete weighted cross-parent plus terminal/restoration covariance on original returned occurrences |
| SAT | OPEN | Exact Fubini bridge from complete owner blocks to the same `A-T` carrier, followed by signed nonlocal payment |
| JOH | OPEN; no new Oct 31 inequality | Weighted ancestry inequality retaining location weights, unequal-count correction, anchor, and Li normalization; next Owner rotation |
| CODIV | ADVANCED by (1), still OPEN | Centered coefficient-weighted incomplete quadratic large sieve with cross-column terms and primitive `h=1` retained |
| FINITE-AC | OPEN | All-root bound for actual `Q_R` against historical `K_R`, including corner and excursion roots; next Wheel rotation after MU-LIFT |
| CORR4 | OPEN | Full coefficient-4 daughter/return mixed energy; no sign reversal from a frame bound |
| MU-LIFT | OPEN and due next Wheel round | Whole-prefix genuine-Mobius recurrence with fixed `r<2` and subpower loss |
| OAI-NNS | OPEN; (1) is only a possible shared-GCD input | Proved occurrence-preserving map and complete principal/resonant/collision exponent ledger |
| NYMAN | OPEN and due next Analytic round | All-scale admissible integer-modulus approximation with independent tail and density consumer |
| BLOCK | Literal universal capture remains REFUTED at `R=549` | Only a newly quantified averaged/multiblock replacement is eligible |

S1 gains a paid near wedge and the weighted resonance diagonal, but its far/high/mixed terms remain open. S2 loses complete owner-fibre reciprocal decay and must work across parents plus terminals. S3 retains owner chronology but has no new contraction. S4 now has the correct root-average order; cross-scale signed persistence remains unproved.

## G. Strategy decisions

1. Promote the centered root-period operator to the primary square-clock mechanism. Equation (1) removes a real diagonal/congestion bill while (2) specifies the prohibited proof order.
2. Record the near wedge as paid. Do not extrapolate its small-remainder geometry into the far band.
3. Keep factor-depth cancellation as a first-band research direction, but reject depth classification itself as a saving: squarefree factor-pair contributions are internally coherent.
4. Abandon every complete inverse-weighted owner-fibre `p^(-theta)` contraction claim. Search only pre-return masked channels with an exact bridge or complete cross-parent/terminal covariance.
5. Preserve MU-LIFT as the strongest genuinely independent reserve and service its overdue anti-starvation turn.
6. Do not formalize the Census exponent conjecture or any incomplete-moment hypothesis.

## H. Next specialist assignments

**Owner Payment:** Define the complete owner-`p` returned block, including all parents and exact terminal/restoration occurrences. Prove an occurrence-preserving Fubini identity to one named SAT/VF carrier or exhibit a counterexample. The output must retain multiplicities and signs; falsify it on the `{(1,pq),(p,q)}` family and one cross-parent collision.

**Analytic Type II:** Starting from (1), prove or refute a centered incomplete quadratic large-sieve inequality for the full actual `beta_R(jR+k)` operator over a declared `J,K,H` range. Keep the zero mode separate, average `delta` before the second Cauchy step, and stress-test `k=j`, `R=-1 mod j`. State the exact exponent ledger after principal and partial-period losses.

**Finite Wheel & Incidence:** Take the scheduled MU-LIFT turn. On the merged signed hyperbola carrier, isolate one complete `K3` Type-II range and determine whether any fixed `r<2` recurrence can follow after `K1/K2`, overlap, and interpolation are restored. A valid negative result is an explicit extremal family showing the proposed premise lacks arithmetic content.

**Prime Census Laboratory:** Do not extend the aggregate far-band range. Compute the complete-period centered Gram for small `(j,k)` with actual moving coefficients, stratified by `gcd(j,k)`, and compare diagonal mass with (1). Include the maximal-root family and report the earliest cross-column spectral excess; finite evidence only.

**Adversarial Referee:** Independently verify (1)-(2), especially the partial-period cover, divisor-bound quantifiers, and CRT factorization. Then decide whether the proposed centered large-sieve statement is genuinely proper or silently contains the shell target once all omitted terms are restored.

**Lean Verification:** Do not broaden unmerged #1060. After human disposition and independent referee acceptance, formalization priority remains the accepted near wedge, followed by the corrected `delta` identity/period moment and then (1). Encode no unproved incomplete moment or global compensation estimate.

## I. Lean and PR status

PR #1060 is open, non-draft, mergeable, and unmerged at exact head `80ee69a861398007046e35b79f7040e923078942`, based on current main. It changes only the dedicated workflow and `EULER_UNIFORM_COMPLETED_COEFFICIENTS_20261030.lean`. All 12 exact-head Actions runs independently refreshed today are completed/successful, including run `41154203024` for the uniform coefficient theorem family. The legacy combined-status list is empty because the evidence is in Actions checks.

Classification: `PROVED_IN_LEAN_ON_PR_HEAD / CI_GREEN / REVIEW_READY`, not `PROVED_IN_LEAN_ON_MAIN`. Its four theorems are structural completed-coefficient and physical-packet identities with activation retained. They prove no incomplete-window or complete-source estimate. Human-only merge remains mandatory.

## J. Next-run resume capsule

- Main: `6b2a869750b92fcdbebff78a591e7722b4f2c747`.
- Authority: `AGENTS d30a5c4...`; contract `7a067ec...`; selector `497c598...`; all-vector directive `a2892b6...`.
- New claim: `20261031-coordinator-1`, equations (1)-(2), `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW`.
- Paid components: first-band near wedge; coefficient-weighted root-period resonance diagonal.
- Rejected mechanisms: root-independent `delta`; complete inverse-weighted owner-prime decay; Cauchy-before-root-average resonance control.
- Primary blocker: centered coefficient-weighted incomplete quadratic off-diagonal with principal, partial periods, and all source restorations.
- Independent reserve: genuine whole-prefix MU-LIFT recurrence with fixed `r<2`.
- PR #1060: exact head `80ee69a...`, 12/12 observed Actions successful, review-ready, unmerged.
- Oct 31 reports: all six specialist reports consumed. Oct 30 Owner report remains absent.
- Canonical VF theorem OPEN; full fixed-`eta` shell gain OPEN; strict exponent below `7/8` OPEN; RH OPEN.

## Publication verification

Checkpoint commits: `8fa782c81a4825e10fcc0e9cd6020b8af5bc4902` (primary) and `d8ce908c7d1cb7dfb60898e9c91fe6b64f1b8fa5` (compatibility mirror); identical checkpoint blob `ebb36e77dbf25ab7c50039b0aa0e3c8794820b0a` read back with `IN_PROGRESS` verified.

Final publication is accepted only after exact branch readback confirms the two paths have byte-identical blobs and `COMPLETED` status.
