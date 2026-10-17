# Cross-coordinate low-quotient program: complete seven-agent research instructions

**Date:** 2026-10-17 (America/New_York). **Status:** RESEARCH_CONTRACT / proposed on a user-authorized maintenance PR; no independent 7/8 result, canonical VF bound, finite A/C bound or RH proof is claimed. **Current reference:** merged #964 on `main@fef979286efa91b23bfced46f0a8a0143b000df0`. Independently checked Oct 17 Wheel, Census and Referee reports are on `agent-reports`; Lean's #965 is a separate draft PR. This document is subordinate to the current `AGENTS.md` (permissions), `CURRENT_PROOF_CONTRACT.md` (canonical objective), original Lean sources, and exact-current-head CI.

**Mandatory intake for every role:** read THIS WHOLE DOCUMENT, the dated Oct 17 Wheel/Census/Referee/Lean reports and their prior-day reports, then relevant source declarations. Do not start another scan, write another exact reindexing or repeat a role's accepted theorem before checking the compiled source, report claim ID, carrier and provenance. PR merge status must be refreshed from GitHub; earlier text saying #964 is draft is stale after its actual merge. Agent Studio schedules and saved instructions are not altered by this Markdown.

## 1. Three different `S=A-T` equations: keep their carriers separate

1. **Prime-counting square block (least-prime sieve):** `P_R=R-C_R` for the `R` odd interior seats of `(R^2,(R+1)^2)`, with `C_R` the number removed by their unique least prime owner. Here `S=P_R`, `A=R` and `T=C_R`. This is an unsigned population accounting theorem; it is NOT the signed coefficient cancellation below. Original discussion: `research/VF_MID_FIRST_BAD_FULL_PROOF_MECHANISM_AND_OPEN_PAYMENT.md`.
2. **Mertens square-prefix smooth/transport (signed):** for integer `R>=4`, `X=R^2-1`,
   ```text
   S_mu(R)=M(X)=A_mu(R)-T_mu(R),
   A_mu(R)=sum_(1<=m<=X, P+(m)<=R) mu(m),
   T_mu(R)=sum_(R<q<=X, q prime) M(floor(X/q)).
   ```
   Its exact signed source-to-smooth-minus-transport realization is compiled in `RHLean/Analysis/TwoABScaleTransfer.lean` (`squarePrefixMertens_eq_squareRootSmooth_sub_transport`); `RHLean/Analysis/SquareRootMatchedTransport.lean` proves the prime-first transform and splits smooth mass into positive-orientation and born-smooth. `RHLean/Proof/SquareRootLowPrimeSmoothTransportRecoupling.lean` proved a historical terminal-state bridge **conditional** on its explicit matched bound. These are EXACT identities, not norm estimates.
3. **#919 excluded-six norm/Hecke transport:** `research/VF_MID_919_OAI_EXCLUDED_SIX_SIGNED_KERNEL.lean` proves that a sitewise sharp mask `smooth-high=sharp` commutes with the four-shift signed Hecke transform for **arbitrary physical site weights**. This is linearity/source compatibility, not equality of arbitrary Hecke norm occurrence sets with the original square-prefix smooth sources and not a global NNS/first-bad payment.

**Forbidden conflations:** least-owner composite counts versus signed Möbius transport; original physical VF `w_r` versus unit Möbius coefficients; norm-aggregated ideals versus distinct rational integer occurrences; raw seats/eligible ancestry versus #915 clipped, anchored returned cells; first-bad NNS quadratic covariance versus an unweighted square-prefix scalar identity.

## 2. The exact #919 root-cutoff crosswalk — already derivable, NOT a new power saving

Let `chi=chi_{-3}`, `mu6(n)=mu(n)*1_(gcd(n,6)=1)`, `a6=mu6*(chi*mu6)` where `*` means Dirichlet convolution and `chi*mu6` means **pointwise** character multiplication for the right-hand factor. (For clarity, write `a6=mu6 * (chi pointwise mu6)` in prose.) The compiled principal coefficient map in `research/VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP.lean` gives
```text
M(X)=sum_(m<=X) a6(m)*K(floor(X/m)),
K(t)=C_chi(t)-C_chi(floor(t/3))-C_chi(floor(t/4))+C_chi(floor(t/12)),
C_chi(t)=1_(t mod 3=1).
```
The integer quotient kernel `K` has period 36, `|K|<=2`, with primitive bounded by 4. These periodic facts apply to the QUOTIENT variable, not the norms.

At `X=R^2-1`, **the Hecke root cutoff is `y=floor(sqrt X)=R-1`**, whereas the older `squareRootSmoothMass(R-1)` includes factors up to `R` and its transport starts at `q>R`. This one-integer difference matters precisely when **R itself is prime**. In particular, a split prime `R==1 mod 3` contributes `-2*M(R-1)` to the Hecke root `P1` but is absent from the older transport starting at q>R.

For a SAME-cutoff comparison define the positive cofactor transform and genuine signed smooth mass:
```text
A_y(X)=sum_(1<=m<=X, P+(m)<=y) mu(m),
T_y(X)=sum_(y<q<=X, prime q) M(floor(X/q)),
H_y(X)=sum_(y<q<=X, prime q==1 mod 3) M(floor(X/q)),
I_y(X)=sum_(y<q<=X, prime q==2 mod 3) M(floor(X/q)).
```
When `y=floor(sqrt X)`, every integer `m<=X` has at most one rational prime factor `q>y` and its cofactor `c<=floor(X/q)<q`; consequently `mu(qc)=-mu(c)` (including zero on nonsquarefree c). Therefore, **with the explicitly positive prime-transform convention**, all identities are exact:
```text
M(X)=A_y(X)-T_y(X),   T_y(X)=H_y(X)+I_y(X),
M(X)=P0(X;y)-2*P1(X;y),   P1(X;y)=H_y(X),
P0(X;y)=A_y(X)+H_y(X)-I_y(X).
```
The native `RHLean/Analysis/TwoABScaleTransfer.lean` defines `squareRootTransportMass` as **minus** the high-integer Möbius mass, exactly `T_y` at matching cutoff; `RHLean/Analysis/SquareRootMatchedTransport.lean` likewise uses a positive prime-first cofactor transform. Verify native source definitions and all endpoints rather than reinterpreting a positive cofactor transform as an integer-site Möbius charge.

The Oct 17 Wheel quotient-cell compression (PAPER_PROOF / independently checked) is
```text
P1(X;y)=sum_(1<=u<=y) c_X(u)*M(u),
c_X(u)=pi_split(floor(X/u))-pi_split(max(y,floor(X/(u+1)))),
```
where `pi_split` counts primes `q==1 mod 3`. Thus the operator itself was already historical: the #919 Hecke layer uses split primes, while original `T_y` also contains inert primes. The correction to smooth `P0` is a signed **character-weighted** transform, not a termwise identity with A.

**Important exact translation to the historical `R`-cutoff `A_R,T_R,H_R,I_R`:** write `A_R=A_R(X)=sum_(m<=X,P+(m)<=R)mu(m)`, `T_R=sum_(R<q<=X)M(floor(X/q))`, with `H_R,I_R` the split/inert parts of `T_R`. For prime `R` let `delta_R=1`; otherwise `delta_R=0`. The `q=R` endpoint yields
```text
A_y(X) = A_R(X) + delta_R*M(R-1),
T_y(X) = T_R(X) + delta_R*M(R-1),
H_y(X) = H_R(X) + delta_R*1_(R mod 3=1)*M(R-1),
I_y(X) = I_R(X) + delta_R*1_(R mod 3=2)*M(R-1).

P0(X;R-1) = A_R(X) + H_R(X) - I_R(X)
             + delta_R*(1+chi_{-3}(R))*M(R-1).
```
This is the **corrected cross-coordinate scalar identity**. The tempting omission of the last term is FALSE when `R` is a split prime with `M(R-1) !=0`. Independently verified exact examples:
```text
R=7, X=48:  A_R=1, T_R=4, H_R=2, I_R=2,
             P0=-1, M=-3, correction=-2;
             naive A_R+H_R-I_R=+1 (WRONG).
R=13, X=168: A_R=0, T_R=1, H_R=2, I_R=-1,
             P0=-1, M=-1, correction=-4;
             naive A_R+H_R-I_R=+3 (WRONG).
R=103,X=10608: A_R=-126,T_R=-110,H_R=-53,I_R=-57,
             P0=-124,M=-16,correction=-2.
```
These were computed by a separate exact-integer local sieve (Möbius, largest prime factors, Dirichlet-convolution a6 and quotient K), not Lean-verified. Test R prime split/inert, R composite, and arbitrary X around squares; **R=317 is inert**, so its zero correction concealed this issue in earlier informal crosswalk discussions.

The identity is **scalar / exact-coefficient algebra**. It does not give an occurrencewise identification of the Hecke `P0` contributions with the original physical `A_R` atoms or a new bound. A termwise/source-level crosswalk, especially to masked/anchored #915 returned cells, is a separate theorem obligation.

## 3. Low/high quotient buckets: the actual bound and its arithmetic meaning

Define, for every integer `X>=256`, with `r=floor(sqrt X)`,
```text
C6(z)=sum_(1<=m<=z) a6(m),
B_X(t)=sum_(m<=X, floor(X/m)=t) a6(m)
      =C6(floor(X/t))-C6(floor(X/(t+1))),     1<=t<=X,
D_X(t)=B_X(t)-B_X(t+1)
      =C6(floor(X/t))-2*C6(floor(X/(t+1)))+C6(floor(X/(t+2))),
B_X(X+1)=0,
V_low(X)=sum_(1<=t<=r) |D_X(t)|,
V_high(X)=sum_(r<t<=X) |D_X(t)|.
```
These are **second differences along the hyperbola**, not necessarily consecutive integer differences of `C6`. Keep all zero-`K(t)` quotient buckets in `B` and `D`; `K(2)=0` is an immediate diagnostic.

**Existing square-endpoint baseline, do not rediscover:** `research/VF_QUOTIENT_VARIATION_FIRSTBAD_ATTACK.lean` already compiles the exact `X=R^2-1` diagonal gap `B_X(R)=0` and a low/high Abel decomposition. Its paper note established `|M(R^2-1)|<=4V_low+2 A_short`, with `A_short=sum_(m<R)|a6(m)|<=R-1` accepted mathematically but not proven in that old module. **Census Oct 17 is a general-X boundary-corrected extension, not discovery of the low problem.**

**Oct 17 Census Claim `20261017-census-2` (PAPER_PROOF / referee confirmation outstanding):** for `N=floor(X/(r+1))`,
```text
V_high(X)=2*sum_(m<=N)|a6(m)|-|B_X(r+1)| <= 2N <= 2sqrt(X).
```
The boundary subtraction is essential (first observed uncorrected-equality failure `X=380`). Its proof uses `gcd(m,6)=1` support separation plus local `|a6(n)|<=d_chi(n)=(1*chi)(n)` and `sum_(m<=N)d_chi(m)<=N`. Note the original square-endpoint `R^2-1` diagonal bucket zero and the general-X `r+1` boundary are **different boundary statements**; keep them both.

**Compiled #919 signed Abel:** `|M(X)|<=4(V_low+V_high)`. Consequently, a GENUINELY INDEPENDENT all-X uniform arithmetic theorem
```text
for every epsilon>0, exists C_epsilon, for all X>=256:
V_low(X) <= C_epsilon X^(7/8+epsilon)
```
would imply `M(X)=O_epsilon(X^(7/8+epsilon))` and the corresponding zero-free implication through the existing verified Mertens growth/zeta boundary bridge. The stronger normed input is UNPROVED, and the original canonical VF von-Koch endpoint is still OPEN.

**Why old identities don't infer this automatically:** `S=A-T` or `M=sum K(t)B(t)` is one signed scalar after all cancellations; `sum |B(t)-B(t+1)|` takes absolute values BEFORE final cancellation. The cross-coordinate scalar identity cannot control this stronger `ell^1` variation without an independently proved, *arithmetic-specific* operator/Gram restriction. A bounded 36-period primitive, short high-quotient sector, or observed small `M` cannot provide that missing inequality.

At `X=10^7`, the exact native check is `M=1037`, `V_low=23765`, `V_high=1782`, total `V=25547`. The unsigned same-support variation was `1420759`; eight split-sign control permutations had `V=26687..44715` there, **but** the native sign did not dominate all controls across other X. Do not extrapolate a universal sign-domination law or an exponent from these finite figures.

## 4. Two independently meaningful ways to proceed — neither is proved

### Path L-VAR: bound the genuine low-bucket second differences

Aim for a *uniform* bound on the complete low quotient variation `V_low(X)` above, using genuine excluded-six Euler signs and exact hyperbolic intervals. A candidate per-dyadic-band theorem
```text
sum_(T<=t<min(2*T,r+1)) |D_X(t)| <= C_epsilon X^(7/8+epsilon)
for every dyadic T>=1, uniformly in X,
```
would suffice after at most `O(log X)` bands and an epsilon margin, but is stronger than the global condition and NOT known. The objective is not to write down this same desired inequality: derive a structurally new restriction on `D_X(t)` from exact `mu6*(chi pointwise mu6)` divisor couplings, correlated neighbors or a legitimate multi-row analytic theorem. A sign claim about an individual quotient bucket needs adversarial held-out tests and may fail.

Potential smaller lemma: prove a deterministic two-interval or cofactor-band cancellation bound on a **specified** subset of the signed `D_X(t)` with a rigorously controlled complement, even at a weaker exponent. Specify size, epsilon/scale, boundary and whether the untouched complement is small enough to improve any exponent.

### Path L-RETURN: exploit matched smooth-minus-transport before an absolute value

The old `A_mu^- - T_mu` is a *matched* signed difference; both legs are O(X/log X) in the observed range and cannot be bounded separately at 7/8. The original source-level equality `entered=smooth-transport` and the exact original transport transform
```text
sum_(R<q<=X, prime q) M(floor(X/q))
```
are available. Audit the exact character-weighted #919 layer and sign conventions, then derive a **source-preserving Fubini/Gram matrix** expressing a set of low-bucket differences jointly in terms of physical matched cofactor/owner occurrences, all squareful and boundary corrections, and original masks. Do not take absolute values until the new arithmetic restriction is applied.

A credible new theorem could control a *nonlocal weighted bilinear mixed moment* or a genuine *history-conditioned signed low return* with **all** matched terms, then use an explicitly proved inequality to reach the desired bound. The second route may be weaker than `V_low` and reach only the original first-bad #915 consumer; report it as such. **An exact matrix decomposition or the tautology that the recombined sum is small is not a bound.**

Prove the source and logical bridges separately:
```text
integer mu / a6 factorization (actual arithmetic)
 -> quotient bucket / cofactor prime owner (exact Fubini)
 -> original A-T matched source (correct signs and terminal boundary)
 -> if needed original VF physical weights and #915 returned-cell admission
 -> quantitative inequality (new arithmetic input)
 -> precise consumer (M 7/8 OR canonical VF first-bad).
```
Not every bridge is established on main. The `chi_{-3}` split-prime selector is +1 on surviving first-power large split primes: there is NO oscillatory high-prime character phase from it alone. The rank-3 obstruction at R=317 rules out a specific unmasked centered two-factor rectangle, not all masked/multi-row sources.

### Other non-superseded routes

- **Hecke BAD:** Referee accepted `|BAD_floor(X^(1/8))|<=3X^(7/8)(1+log X)` on its own coefficient carrier, separate from the original VF positive large-square bound `(51/8) R^(7/4)/log R`; both PAPER_PROOF. In #965 the Lean agent proved the **floor-loss numerical step** only, with the underlying BAD bound a visible premise; do not overreport full Lean verification.
- **One-layer root / seven-layer eighth:** exact algebra only; `M=P0-2P1` has a coherent `-2` split-prime top-half injection. An `O(X^(7/8+eps))` bound on the already recombined `P0-2P1` is target-equivalent and not an independent gain.
- **SB-7/8:** the dyadic genuine square-shell second moment `sum_(H<=r<2H)delta_r^2=O_epsilon(H^(5/2+epsilon))` is another stronger sufficient OPEN input and retains ALL pair diagonals/off-diagonals, smooth/transport cross terms.
- **MU-LIFT / full K1,K2,K3:** preserve the exact hyperbola signed source and full-prefix dependence (not only a corner); current amplification acceptance is fixed `r<2` with subpower `G(B)`, not a guaranteed arithmetic recurrence.
- **Nyman Hilbert, finite A/C, genuine VF owner-source and CORR-4:** parallel candidate lanes, no accidental retirement or transfer of a different norm/covariance carrier.

## 5. Mandatory falsification and acceptance protocol

Before using a substantive run budget, check relevant archived full-source identities and `proofq.py` search. **Baseline exact arithmetic:** X=10^7 with `(V_low,V_high,V)=(23765,1782,25547)`; held-out X=7654321 and 9999991 from Oct 17 Census; square X=R^2-1 at R=317,548,1027,3000; and the X=380 high-boundary counterexample. Include X just below, at and above perfect squares and both R prime and R composite to detect mismatched root cutoffs. Recompute `K=0` buckets, `C6`, `D_X(t)`, `P0,P1`, original `A,T`, and split/inert owner subtotals under explicitly **matched** cutoff/sign conventions. Record a digest and integer equality failure location before claiming compatibility.

**Nonnegotiable negative controls:** zero-quotient mask cases; split/inert prime swap; factor-preserving sign permutations; repeated/squareful primes; artificial bounded-prefix controls; disjoint/unmatched physical sources; the R=317 rank counterexample. These are falsifiers, NEVER a substitute for a uniform genuine-arithmetic theorem. Census existing controls showed no deterministic native-over-scramble dominance, so do not assume one.

Every role must publish: (i) exact source/claim IDs and statuses (`PROVED_IN_LEAN_ON_MAIN`, `PROVED_IN_LEAN_ON_PR_HEAD`, `PAPER_PROOF`, `FINITE_COMPUTATION`, `CONJECTURE`, `TARGET_EQUIVALENT`, `REFUTED`), (ii) original and target carrier dictionaries, (iii) full quantified *new* lemma versus identity, (iv) any coverage/epsilon losses and boundary, (v) a separate falsifier and outcome, (vi) remaining precise unpaid inequality and who's responsible. All numerical tools/reports require exact code/hash/readback. No `sorry`, added unproved axiom, CI weakening, manual merge by scheduled agents or extra automatic invocations. **CI must be green on the latest PR head before marking review-ready; historical green jobs are not a current-head certificate.**

## 6. Seven role-specific mandates and required next deliverables

**Research Coordinator — integration, not seventh repetition.** First reconcile the actual inherited `S=A-T` variants, already-compiled quotient variation and Oct 17 general-X high-side paper result. Allocate *distinct* hypotheses to Owner (occurrence bridge) and Analytic (real uniform saving). Produce a shared dependency DAG `known -> crosswalk -> candidate inequality -> consumer`, indicate arrow proof statuses and identify any mathematical redundancy or impossible implications. Choose L-VAR or L-RETURN as a lead without suspending true alternatives. Give each specialist one decisive test; do not falsely count pending reports as executed.

**Owner Payment — native source-coupling theorem.** Obtain the exact prime-cutoff and sign audit between source-level `squareRootSmoothMass`, `squareRootTransportMass`, `squareRootTransportPrimeFirst` and Hecke `P0,P1`, explicitly including the `q=R` equality case. Derive an original-occurrence-preserving crosswalk on an admissible carrier or exhibit a specific missing source term. Then test whether matched born-smooth/high-owner cancellation constrains low-bucket `D_X` jointly, preserving squareful cofactor mass, chronological ownership, original VF weights when used, #915 masks/clips, signed zero-target covariance and all mixed/anchor terms. Deliver one honest mathematical lemma or a decisive obstruction, NOT `S=A-T` restated.

**Analytic Type II — signed quantitative input.** Investigate a bona fide arithmetic theorem on `V_low` (or weaker signed low return) using adjacent hyperbola intervals, the genuine `a6=mu6*(chi pointwise mu6)` convolution, valid bilinear/dispersion/large-sieve inputs and full floor endpoints. Report whether the existing matched smooth/transport response yields a specific **independent** cross-owner/low-bucket moment bound rather than the definition of M. Keep coherent principal top-half mode, any varying-character profile/admissibility constraints, complete K1/K2/K3 and Nyman alternatives. Produce one actual theorem or explicit uniform missing estimate with attainable sublemma and an adverse test.

**Finite Wheel & Incidence — discrete bijection/source audit.** Independently check the exact quotient-cell count, both cutoff conventions `q>R` versus `q>floor(sqrt X)`, signs, unit cofactor, inert and split cases, prime squares, boundary `X=R^2-1`, `X=R^2`, and X=380. Seek one exact *local-to-nonlocal* incidence identity relating adjacent buckets to true owner packets, not another wheel capacity estimate. Preserve wheel-1 even boundary packet and its within-packet sign coherence, which forbids naive parity cancellation.

**Prime Census — discriminating held-out tests, no repeat scan.** Freeze candidate bridge before scanning; reproduce *jointly* original `A,T`, split/inert owner terms, Hecke `P0,P1`, signed low/high bucket second differences, and possible physical covariance in specified square and nonsquare X. Challenge every proposed termwise correspondence and aggregate/variation implication. Reuse X=10^7 and published held-out integer data; carry K=0 buckets; report first counterexample with full witness and exact integer values. Do not assert a power law from 10^7.

**Adversarial Referee — independent theorem-scope gate.** Before Analytic or Lean builds on it, audit the apparent `P0=A+H-I` crosswalk under native signs, the `q=R` cutoff discrepancy, the square endpoint versus all-X V_high boundary formula, the C6 second-difference identity, the accepted constants 3 and 51/8 and the precise orientation of `A-T`. Demand a counterexample to any inference that a small signed scalar forces small variation (K=0 buckets are a direct warning). Referee the Census general-X high quotient PAPER_PROOF separately: if accepted, nominate its precise nonduplicate Lean statement. A numerical sign coincidence is not a uniform mixed-moment theorem.

**Lean Verification — formalize only independently qualified, nonduplicate claims.** Consult `research/VF_QUOTIENT_VARIATION_FIRSTBAD_ATTACK.lean`, `RHLean/Analysis/TwoABScaleTransfer.lean`, `SquareRootMatchedTransport.lean`, `SquareRootLowPrimeSmoothTransportRecoupling.lean`, #919 principal map and signed Abel return before creating anything. #965 is an existing PR: its floor-loss consumer is formally proved, arithmetic BAD bound remains a premise, and its exact-head checks are GREEN; do not duplicate it. After Referee acceptance, candidate work: (a) source/cutoff-correct scalar crosswalk with explicit sign/endpoint; (b) general-X high-variation bound retaining the subtractive boundary; (c) exact quotient second-difference identity and full low/high split, or (d) separately proved arithmetic bound. Do not write a filler conditional `V_low` theorem and call it 7/8. Use GitHub Actions exact-head Lean/axiom audits; human-only merge.

## 7. Explicit stopping condition

A cycle counts as a substantive quantitative step **only** if a new uniform arithmetic estimate holds for genuine source coefficients with its full carrier and provides a genuinely paid portion of `V_low`, a nontrivial matched-owner moment, an improved genuine Mertens exponent, or the original physically admitted VF/NNS source. Otherwise report the exact identity, obstruction, counterexample or numerical evidence with its actual narrower status. The original canonical `VFCanonicalSquareVonKochStatement` remains the public target and OPEN.
