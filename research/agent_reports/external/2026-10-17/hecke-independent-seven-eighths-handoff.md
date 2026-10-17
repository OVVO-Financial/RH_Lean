# External research handoff — independent seven-eighths cancellation, original Hecke owners

**Date:** 2026-10-17 (America/New_York). **Source:** direct, user-requested cross-session research maintenance. **Audience:** all seven RH_Lean scheduled agent specialties on their next actual configured invocation. **Status:** EXTERNAL_HANDOFF / INDEPENDENT_REVIEW_REQUIRED. **No additional scheduled run was launched.**

**Main at publication (verify fresh on consumption):** `b9105f19fbbf25742a6909a6e8c995e6a9ddeddb`. Full work is in [DRAFT PR #964](https://github.com/OVVO-Financial/RH_Lean/pull/964), branch `research/independent-seven-eighths-square-shell-energy-20261016`. **PR #964 is NOT on main**. Its proposed revisions to `AGENTS.md`, `CURRENT_PROOF_CONTRACT.md`, `docs/FACTOR_DEPTH_RESEARCH_BRIEF.md` and `docs/DYNAMIC_RESEARCH_AGENTS.md` are not active instruction authority unless a human merges the PR. This handoff is a candidate portfolio intake in the precise sense of the external inbox protocol, not an override of main or of saved Studio agent instructions.

## Scope / user research priority

The user explicitly prioritizes explaining OpenAI's `7/8` bound **independently from RH_Lean arithmetic** rather than importing the external theorem as a premise. The two distinct unconditional *paper* large-prime-square estimates in draft #964 are actual source reductions, not a proof of the full exponent. The remaining problem is **nonlocal signed cancellation** across actual original owner and Hecke prime-cofactor populations. Independent weaker arithmetic constraints are useful; an exact identity or a target-equivalent renamed residual alone is not.

### EXT-20261017-HECKE-1 — compiled original source + paper large-square cutoff

Existing source on main: `research/VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP.lean` (`vf919Mertens_eq_excludedNorm_periodicKernel`). Put

```text
a6(n)=1_(gcd(n,6)=1)[mu*(chi_-3 pointwise*mu)](n)
K(t)=C_chi(t)-C_chi(floor(t/3))-C_chi(floor(t/4))+C_chi(floor(t/12))
M(X)=sum_(m<=X) a6(m)*K(floor(X/m)), X>=12.
```

`K` is periodic 36 in the **quotient** and `|K|<=2`. For split `p>=5`, local `a6(p)=-2, a6(p^2)=+1`; for inert `p>=5`, `a6(p)=0, a6(p^2)=-1`. Exponents `>=3` vanish. Exclude p=2,3 correctly. The fact that `chi_-3(p)=+1` on every surviving *first-power* large split prime is essential: **there is no varying character cancellation from this selector alone**.

Given `y>=2`, let `BAD_y` be the exact norm sum for `m` divisible by some `p^2`, `p>y`, and `CORE_y=M-BAD_y`. Union bound and `|a6|<=tau` give

```text
|BAD_y(X)| <= 2X(1+log X)/y.                [PAPER_PROOF]
y=floor(X^(1/8)): |BAD_y|<=4 X^(7/8)(1+log X)  [X>=256].
```

The **different** original VF odd, strict open-square physical seat sector with `p^2|n, p>R^(1/4)` and native `w_r` has `0<=H_R^large_square<=10R^(7/4)/log R`, **PAPER_PROOF** in the same PR. It is not identical to Hecke BAD and does not pay the rest of the signed VF ledger. Both paper bounds await independent referee verification and optional Lean formalization.

### EXT-20261017-HECKE-2 — seven layers versus *exact* root-wall two layers

At `y=floor(X^(1/8))`, `CORE_y(X)=sum_(k=0..7)(-2)^k P_k(X;y)`, with k distinct first-power *split* large prime factors and literal small-cofactor cutoff. A `7/8` bound on that whole signed core is **TARGET_EQUIVALENT** after the already paid BAD, not independent progress.

For `y=floor(sqrt X)`, no `p>y` has `p^2<=X`, so **BAD=0** and exactly

```text
M(X)=P0(X;y)-2P1(X;y),
P1 = sum_(sqrt X < q <= X, q prime, q mod 3=1)
       sum_(s<=X/q) a6(s) K(floor(X/(s*q))).
```

The cofactor s is automatically <sqrt X. This exact two-layer form is a potential *source interface*, not a gain: P0 remains difficult. The actual large-prime extension is `C_q(X)=C_(q^-)(X)-2 C_(q^-)(floor(X/q))`. Every split prime in `(X/2,X]` injects `-2`; `TopPrimeReplacementIsolation.lean` and `AdaptivePrimeMatching.lean` rule out paying their signed mass by mere local insertion pairings. Compensating them requires *nonlocal* depth/owner interaction, preserving all historical sources and masks.

### EXT-20261017-HECKE-3 — genuinely stronger independent sufficient inlets

**OPEN.** The already compiled `research/VF_MID_919_QUOTIENT_SIGNED_RETURN.lean` gives a signed Abel return with a 36-period bounded primitive, hence `|M(X)|<=4 V_X`, `V_X=sum_t|B_X(t)-B_X(t+1)|`, where `B_X(t)` contains **all** a6(m) with floor(X/m)=t even when K(t)=0. An independently proved `V_X=O_epsilon(X^(7/8+epsilon))` suffices to derive the 7/8 Mertens exponent without using OpenAI's theorem. This is **stronger than simply bounding |M|**, and currently unproved. The separate `SB-7/8` dyadic square-shell energy bound in the PR is also stronger sufficient arithmetic input; neither is a result.

A masked/multi-row analytic approach must satisfy physical coefficient equality, row admissibility, sharp/smooth error and uniform conductor constants. At R=317 the compiled rank obstruction rules out a single *unmasked centered two-factor rectangle*, not all multi-row variants. The fixed chi_-3 split-prime selector is not an oscillatory amplifier.

## Reproducers / finite evidence (independently recheck before relying on values)

Draft PR #964 adds `scripts/vf919_hecke_cutoff_sweep.cpp` (integer cutoff/CORE/BAD/variation) and `scripts/mertens_square_shell_energy_probe.py`. Intended independent numerical checks at X=10^7: `M=1037`; y=7 CORE=1147 BAD=-110; y=3162 two signed layers -47157,+48194, BAD=0; `158004` upper-half split primes inject -316008 and prior prime response +317045. Corresponding full quotient variations: V=25222 (y=7), V=25547 (y=3162). These are finite claims in the draft research note; **reproduce before promoting them to accepted measurements**. None proves an asymptotic saving. Keep zero-K buckets when calculating variation. Do not independently trigger a gigantic scan without a new prediction.

## Routing by specialty — one next-run candidate per role, not a forced Studio change

- **Coordinator:** read draft PR and this note, compare actual Hecke core, full signed quotient variation, separate square-shell sufficient gate, K1/K2/K3 and Nyman. Identify the smallest *independently provable* quantitative input and whether the rank obstruction affects it; report route selection with no-narrowing audit.
- **Owner Payment:** independently validate the original native VF large-square paper bound, align root-cutoff P0/P1 with unique greatest-prime owners and full original-weight/historical versus returned-source accounting. Identify missing source bridge before NNS.
- **Analytic Type II:** seek a uniform signed norm bucket **adjacent variation** or admissible varying-character multi-row Hecke moment / high split-prime cofactor bilinear estimate. Extract the top-half principal mode first; do not assume chi_-3 sign oscillation.
- **Finite Wheel & Incidence:** check full split/inert Euler factors, 1/8 to 1/2 cutoff transitions, exact prime-extension recurrence, upper-half single-neighbour obstruction and all floor/square boundary corrections.
- **Prime Census:** independently reconstruct the integer X=10^7 data and predeclare held-out cutoff stress tests, including K(t)=0 quotient buckets. Produce reproducible falsifiers, not more unmotivated large-range scans.
- **Adversarial Referee:** independently audit large-square constants 4 and 10, both carriers and the seven- versus two-layer source equality; check signed variation as a *strictly stronger* sufficient input and the single-rectangle rank no-go; label inference strengths precisely.
- **Lean Verification:** reuse the compiled #919 coefficient/quotient/owner identities and merged #958/#961. Formalize only a new nonduplicate referee-validated theorem on the authorized proof branch with head CI/axiom audits, **no automatic merge**. Nothing here certifies an independent 7/8 proof.

**Acceptance / handoff status:** `PAPER_PROOF` for elementary sectors and cutoff arguments pending independent review; `IDENTITY_ONLY` for finite prime-extension and signed layer rearrangements; `FINITE_COMPUTATION / TO_REPRODUCE` for numeric checks; `CONJECTURE / OPEN` for signed nonlocal uniform moment/variation. The exact canonical VF square-endpoint target and complete original #915 zero-target covariance remain separate **OPEN** consumers. No scheduled launch, saved Agent Studio configuration change, or main merge is performed by this handoff.
