# RH_Lean Coordinator synthesis - 2026-10-17

**Status:** COMPLETED
**Run ID:** 2026-10-17T19:09:01-04:00, scheduled invocation
**Agent:** RH | Research Coordinator / Proof Architect
**Reporting rule:** `00-coordinator-am.md` and `90-coordinator-pm.md` are byte-identical compatibility mirrors of this one run, not two executions.

## A. What changed mathematically?

The strongest new result is a no-go theorem for fixed-prime sign-reversing involutions.

### Claim `20261017-coordinator-1` - prime-toggle boundary invariance

For every prime `p` and integer `N>=1`,
```text
M(N) = sum_(N/p < n <= N, p does not divide n) mu(n).       (PT)
```

**Proof.** Split the genuine Mobius sum into `p`-free integers and integers divisible by `p`. Terms divisible by `p^2` vanish. Every remaining divisible term is uniquely `pm` with `m<=N/p`, `p` not dividing `m`, and `mu(pm)=-mu(m)`. It cancels the corresponding lower `p`-free term. Exactly the displayed upper boundary remains.

Equivalently, pairing `m <-> pm` cancels the entire interior but transports the complete Mertens sum to the unmatched boundary. Thus any proposed proof based only on one local Euler-prime toggle has made no quantitative reduction. It must couple different prime faces, different scales, or a genuinely nonlocal owner/shell response before taking norms.

**Evidence:** `PAPER_PROOF / IDENTITY_ONLY / LOCAL-MECHANISM NO-GO`. A fresh exact-integer implementation verified (PT) for every `N<=500` and `p=2,3,5,7,11,13,17,19`, with zero failures. The computation supports but is not needed by the proof.

This sharpens the current warning about coherent top-prime modes. It is mathematically different from the October 16 fixed-product no-go: that result says `mu(i)mu(j)` is sign-coherent when `ij` is fixed; (PT) says a sign-reversing map across two distinct products still leaves a boundary carrying exactly the original target.

## B. Current proof objective

Fresh live authority:

- `main@827b291f16992d9f98e22338b1e01f932218600e`.
- `AGENTS.md` blob `aef9d6f7a7d3a091f947effd38e9ad42a63e8445`.
- `CURRENT_PROOF_CONTRACT.md` blob `873ec6f70525e1e9ba1defecf8b0951ebe155069`.
- Active covariance contract: `docs/SIGNED_MOBIUS_COVARIANCE_RH_SEAM_2026_10_17.md`, merged through PR #970.
- No open or draft PRs at final inspection.

The canonical theorem remains the open `VFCanonicalSquareVonKochStatement`. The active arithmetic carrier is
```text
D(N)=sum_(n<=N) mu(n)^2,
C(N)=sum_(a<b<=N) mu(a)mu(b),
M(N)^2=D(N)+2C(N).
```
The external OAI 7/8 theorem is a conditional benchmark, not an independent RH_Lean proof. A new bound
```text
C(N) <= -D(N)/2 + K_eta N^(7/4-kappa+eta),  kappa>0,
```
would give `|M(N)|=O_eta(N^(7/8-kappa/2+eta))`. In weighted form it would pay every fixed
`eps>3/8-kappa/2`. RH scale is `D+2C=O_eta(N^(1+eta))`, or bounded weighted covariance for every `eps>0` after the standard still-open-in-Lean Mellin bridge.

## C. Competing mechanism portfolio

### 1. SHELL-GCD - primary shared mechanism

**Concept.** Use genuine square shells
`delta_r=sum_(r^2<n<=(r+1)^2)mu(n)`, expand the complete within-shell signed pairs, and partition them by `d=gcd(a,b)`, shift `h=b-a` with `d|h`, greatest-prime owner, and parity of primes unshared after dividing by `d`.

**Independent input.** For some `kappa>0`, every dyadic `H` and every `eta>0`,
```text
sum_(H<=r<2H) delta_r^2 <= K_eta H^(5/2-kappa+eta).           (SE)
```

**Target implication.** Cauchy-Schwarz over square time gives
`M(x)=O_eta(x^(7/8-kappa/4+eta))`, a strict improvement over the benchmark.

**First unproved step.** A signed incidence/mixed-moment theorem on the exact gcd/unshared-prime partition that implies (SE) while retaining all within-shell diagonals, cross-owners and off-square boundaries. Merely restating (SE) in new coordinates is not progress.

**Support and obstruction.** Exact shell smooth/transport infrastructure is on main. Genuine shells `r=14,137,1110` refute a uniformly favorable cross-term sign. Claim coordinator-1 refutes every fixed-prime local toggle as the missing cancellation. Disposition: **CONTINUE / HIGHEST PRIORITY**.

### 2. WEIGHTED-COMMUTATOR - independent discovery lane

**Concept.** Reindex the compiled weighted covariance before taking norms. Each physical pair receives the decreasing tail kernel obtained by summing the shifted weight over all later prefixes. A multi-prime Euler filtration could then be studied through weight commutators rather than a pointwise bound on `M(N)`.

**Independent input.** For one explicit `0<eps0<3/8`, a uniform upper bound on the complete signed multi-prime commutator, including every boundary face, sufficient to bound `CovarianceUpperBounded eps0`.

**Target implication.** By #968's compiled arithmetic equivalence, this bounds weighted energy at `eps0`; the classical weighted-L2/Mellin bridge would give a strip strictly better than 7/8. The bridge remains an explicit formal obligation.

**First unproved step.** An exact multi-prime face decomposition whose commutator is independently smaller. For one prime and constant weight, (PT) shows the boundary is exactly `M(N)`; that version is rejected. Disposition: **REVISE / DISCOVERY**, retained because a single weighted epsilon may be weaker than a pointwise power gain.

### 3. HECKE-LOW - comparator, not the selected common attack

**Concept.** Complete #919 quotient-bucket variation with the high side already paid.

**Independent input.**
`V_low(X)=O_eta(X^(7/8-kappa+eta))` for some `kappa>0`, with every zero-kernel bucket retained.

**Target implication.** Merged #967 plus the signed Abel theorem give a direct Mertens exponent `7/8-kappa`.

**Existing support.** Claim `20261017-census-2` is now compiled on main through #967:
`V_high<=2sqrt(X)`, with the `r+1` boundary retained. The same PR proves the low return controls the excluded-six half-interval increment.

**Obstruction.** This is a stronger normed sufficient theorem, not a consequence of the scalar `M=P0-2P1`; native signs do not uniformly dominate multiplicative scrambles in the finite controls. Disposition: **CONTINUE AS COMPARATOR / SECONDARY**.

The portfolio narrowed away from fixed-product reflection, one-prime toggles, raw A/B reassembly and isolated band payment because exact no-go or target-equivalence results already cover those forms.

## D. Conceptual research performed

The independent question was whether a local Euler sign flip could supply the missing factor-parity cancellation in the full covariance. Formula (PT) answers it negatively and exactly.

For a squarefree `a>=2`, choose any prime divisor `p` and attempt to cancel the `b`-sum in
`sum_b mu(a)mu(b)` by `b <-> pb`. All paired interior terms cancel, but (PT) says the surviving `p`-free upper boundary equals `M(N)`) for every prime `p`, not merely for `p=2`. Therefore changing the chosen fixed prime, least-prime owner or local orientation cannot improve the amplitude. A bad-scale inverse statement follows: any successful prime-filtration proof must exhibit cancellation among at least two distinct boundary faces or between a boundary face and a separate smooth/owner term. It cannot cite the disappearance of the paired bulk.

A finite set of primes gives an exact Boolean-face expansion
```text
M(N)=sum_(d|Q) mu(d) R_Q(floor(N/d)),
R_Q(x)=sum_(n<=x, gcd(n,Q)=1) mu(n),
Q=product_(p in P) p.
```
This remains `IDENTITY_ONLY`; bounding the recombined right side is target-equivalent. Its value is as a falsifiable interface: a proposed multi-prime theorem must pay correlations among faces before absolute values and demonstrate a genuine contraction absent from the one-prime case.

## E. Specialist findings

Today's available reports all predate the 22:47 EDT covariance pivot:

- Wheel blob `dbaefd4005c2cc93b894f9bb97c7a74c5f28dc49`: exact boundary-window identity `E_N=2B_N` and root Hecke quotient-cell compression; `PAPER_PROOF / IDENTITY_ONLY`.
- Census blob `9efa34cd7a2d3c021b20779889eaaf6a556020d3`: general-X high variation with mandatory boundary term and held-out exact data; its paper claim is now compiled through #967.
- Referee blob `a3867e19b4e6e409c09ab69899a628d042f11a8d`: accepted Hecke identities and sharpened paper constants, rejected overbroad rank/variation interpretations.
- Lean blob `1a03815f26aa6ee145d94c9848ac37483b093033`: #965 was then CI-pending; live metadata now supersedes it, since #965 is merged and all exact-head workflows succeeded.
- Today's Owner and Analytic reports are absent: **TODAY=PENDING**. No work is inferred.
- No earlier Coordinator report existed today; this run created it.

All named October 16 reports were consumed. Coordinator mirrors `fc5c5b46a0ec56f606444bb5dbfe400d4a444d18`, Owner `cb42efd7a6aa0e782c353803e604684b9500cdb2`, Analytic `2b93e7c237c09439746a93356c20cd15e4671028`, Wheel `134eb9eb0558a622b6f042baa20f3feb847ed6f4`, Census `26510606eea9f43450e5bb092c4542ab23fcb729`, Referee `e4c0a92301f032eb732a51f7bd997f4a19ac8b48`, Lean `180cf24f8444852a5b69bf2581f0c6d160f3a16e`. Reusable results include squarefree-kernel fixed-product sign coherence, the dyadic boundary identity, and the rejection of sector-local/fixed-backbone payment.

`EXTERNAL_HANDOFFS.md` was read. The Oct 17 Hecke and cross-coordinate entries are superseded administratively by merged #964/#966/#967 but retain their exact mathematical scopes. Oct 14 source-payment and limsup no-go claims remain paper evidence on their named carriers, not bridges to the complete covariance.

## F. Mathematical bottlenecks

1. **SHELL-GCD:** no theorem currently converts gcd divisibility and unshared-prime parity into an all-shell power saving. This is the selected first missing arithmetic input.
2. **WEIGHTED-COMMUTATOR:** no multi-prime weighted face theorem prevents the exact boundary replication in (PT).
3. **HECKE-LOW:** the entire quantitative problem remains in `V_low`; the high side is paid.
4. **Original VF/#915:** complete occurrence/mask/anchor/restoration admission is still missing; raw Mobius covariance cannot be transferred automatically.
5. **Analysis formalization:** the weighted-L2/Mellin implication remains explicitly open even though the finite arithmetic equivalence is compiled.

## G. Strategy decisions

- **PROMOTE** SHELL-GCD as the one shared candidate mechanism for the next cycle.
- **USE** Claim coordinator-1 as its complementary falsifier: every claimed local prime involution must show where cross-prime or cross-owner cancellation enters.
- **REJECT** fixed-prime toggle, least-prime toggle without face coupling, and bulk-cancellation arguments that leave their boundary unestimated.
- **CONTINUE** WEIGHTED-COMMUTATOR only if an exact multi-prime carrier and a fixed `eps0<3/8` are stated.
- **KEEP** HECKE-LOW as the quantitative comparator; do not let it monopolize the covariance campaign.
- **NO_NEW_QUANTITATIVE_RESULT:** no Mertens exponent, zero-free line, canonical VF bound or RH theorem improved in this run.

## H. Next specialist assignments

- **Owner Payment:** derive the exact once-only greatest-prime ownership of every pair inside one shell, including smooth/smooth, smooth/transport and transport/transport terms. State the bridge to the gcd/unshared-prime partition and list every term not admitted to #915. Falsifier: one duplicated pair, omitted cross-owner term, or changed weight.
- **Analytic Type II:** formulate a uniform full-shift bilinear theorem on the SHELL-GCD carrier with an explicit `kappa>0` and prove its exact implication to (SE). Compare it with known averaged Mobius-correlation theorems, checking interval length, all-H uniformity and losses. Falsifier: almost-all shifts or an assumed Mertens exponent substituted for the required complete sum.
- **Finite Wheel:** prove the complete pair-incidence map `(a,b)->(d,h,` unshared-prime parity, owner)` in strict shells. Test whether any two-prime toggle closes into cycles; calculate every boundary face. Claim coordinator-1 is the mandatory one-prime regression.
- **Prime Census:** preregister exact shell observables at the required witnesses and held-out dyadic bands: total energy, gcd classes, shared versus unshared largest-prime owners, and each toggle boundary. Test a specific two-prime cancellation law; reject it at the first exact failure. Do not infer an exponent from ratios.
- **Adversarial Referee:** independently audit Claim coordinator-1 and try to extend or break the no-go for two-prime Boolean faces. For every proposed `kappa`, restore all diagonal/cross-owner/boundary terms and check whether the premise is target-equivalent.
- **Lean Verification:** first repair the repository-state gap for #969 through a human-reviewed main-targeting integration path; do not call it compiled on main. After Referee acceptance, coordinator-1 is a small original-carrier formalization candidate. Do not replace the open weighted-L2 bridge with a hypothesis advertised as a proof.

## I. Lean and PR status

- **#965:** merged to main at `f7ce85e553f23a907fbece552a5ee803283eb07a`; all eleven workflows on proof head `209eadf4cf1ae213bee6c2a55e165e22dfa5174c` succeeded. It proves the floor-loss consumer, not the full BAD arithmetic bound.
- **#967:** merged at `58fcdb50677b74ce39a4b5e36906923af0d52a75`; all exact-head workflows on `cdde68f595570d11a0c109c67203765334fdafba` succeeded. General-X high variation and excluded-norm mass are `PROVED_IN_LEAN_ON_MAIN`.
- **#968:** merged at `c43284955c8272e6211df7b47876c92cb178810a`; all eleven workflows on `4f88a1d2b88c3ee4a34b0619a114167d0218a964` succeeded. Main file blob `277b3f209788077b66fa6095d7c1358897b94e91` compiles the exact weighted identity, diagonal p-series, and covariance-energy equivalence. It does not prove `WeightedEnergyMellinCriterion`.
- **#969:** live metadata says `merged=true`, but its base is `proof/mertens-weighted-covariance-rh-criterion-20261017`, not `main`. Its three files are absent from main. Comparing main with head `f839a3ae41ab0f76a38df5f2ad0498c6105fde67` gives `diverged`, head ahead by 8 and behind by 15; the three OAI files are the only file differences. Its five workflows succeeded, so status is `PROVED_IN_LEAN_ON_NONMAIN_BRANCH / INTEGRATION_REQUIRED`, not `PROVED_IN_LEAN_ON_MAIN`.
- **#970:** merged at current main; all four exact-head workflows succeeded. It activates this covariance campaign.
- **#971:** merged to `agent-reports`; documentation and inventory workflows succeeded. It changes reporting guidance, not mathematics.
- No open PR exists. No merge, review-state change, proof-branch write or rerun was performed by this Coordinator.

## J. Next-run resume capsule

- Authority: `main@827b291f16992d9f98e22338b1e01f932218600e`.
- New claim: `20261017-coordinator-1`, prime-toggle boundary invariance (PT), `PAPER_PROOF / IDENTITY_ONLY / LOCAL-MECHANISM NO-GO`.
- Selected mechanism: SHELL-GCD with target (SE); first missing input is a genuine signed gcd/unshared-prime mixed-moment theorem, not (SE) renamed.
- Comparator: HECKE-LOW; merged #967 pays `V_high`, leaves `V_low`.
- Formal gap: #969 is green on a non-main branch but absent from main; #968 is compiled on main and leaves the Mellin bridge open.
- Missing current reports: Owner and Analytic are `PENDING`.
- Highest-value next reasoning task: build or refute a two-prime boundary-face cancellation law inside complete square shells, preserving every owner and boundary term.
- No quantitative exponent gain, canonical endpoint proof or RH proof is claimed.
