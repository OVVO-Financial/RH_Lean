# RH_Lean Prime Census Laboratory - 2026-10-17

**Status:** PARTIAL / IN_PROGRESS

## Early checkpoint - 2026-10-17T02:00-04:00

Authority refreshed from `main@fef979286efa91b23bfced46f0a8a0143b000df0` after human merge of PR #964. Source blobs: `AGENTS.md` `6e07fe3c550cd371cdd2121768757839b1f9a3f4`; `CURRENT_PROOF_CONTRACT.md` `a71c0abbb43ec996ccc7ec8385dfde558e438c0c`; Hecke note `e32cdf37f62a79dd68806a1b3cb1d960234f3a47`; upstream cutoff script `9949794af21ef8607fa2266439465b6749e6c39f`. Today Coordinator/Owner/Analytic/Census/Referee/Lean are `TODAY=PENDING`; today's Wheel `dbaefd4005c2cc93b894f9bb97c7a74c5f28dc49` and all named 2026-10-16 reports were consumed as continuity.

Pre-registered experiment: independently reconstruct genuine `mu`, `a6=1_(gcd(n,6)=1)[mu*(chi_-3 mu)]`, all four cutoff carriers, complete quotient buckets including zero-kernel buckets, and root top-half prime response. Compare root variation with an unsigned same-support control and multiplicative split-prime sign scrambles.

Checkpoint results are `FINITE_COMPUTATION`. An independent Dirichlet-convolution construction agrees coefficient-by-coefficient with the local Euler recurrence through `n=10^6`. At `X=10^7`, all published exact values reproduce: `M=1037`, cutoff variations `25222,25451,25514,25547`, root layers `-47157,+48194`, top-half split-prime count `158004`, injection `-316008`, prior response `317045`. New localization: root variation decomposes as `V_low=23765` for `t<=floor(sqrt X)` and `V_high=1782` above the quotient wall. Thus isolated high-quotient sparsity does not explain the small complete variation.

No all-scale bound or canonical progress is claimed. Held-out scales, control interpretation, exact commands, source hashes and a continuation capsule will be appended.


## Completion update - 2026-10-17T02:12-04:00

**Status:** COMPLETED  
**Result classes:** `PAPER_PROOF` (one exact quotient-wall lemma and bound), `FINITE_COMPUTATION` (independent reconstruction, held-out census and falsification), `CONJECTURE` (explicit benchmark only), `NO_NEW_RESULT` on the canonical theorem.

### A. Current objective and exact carrier

The live canonical theorem is still OPEN:

```text
VFCanonicalSquareVonKochStatement:
  exists C >= 0, forall R >= 2, |D_can(R)| <= C*R*log(R).
```

This run addresses the stronger sufficient #919 inlet only. For integer `X>=256`, use the compiled coefficient
`a6(n)=1_(gcd(n,6)=1)[mu*(chi_-3 mu)](n)`, quotient kernel `K`, and complete buckets
`B_X(t)=sum_(floor(X/n)=t) a6(n)`. At the root cutoff `y=floor(sqrt X)`, `BAD=0`, so the complete variation is
`V_X=sum_(1<=t<=X)|B_X(t)-B_X(t+1)|`, with `B_X(X+1)=0`. Zero-kernel buckets are retained. The compiled Abel consumer gives `|M(X)|<=4V_X`; no uniform estimate for `V_X` is compiled or assumed.

Today Coordinator, Owner, Analytic, Referee and Lean remain `TODAY=PENDING`. Today's Wheel `dbaefd4005c2cc93b894f9bb97c7a74c5f28dc49` was consumed. The complete named 2026-10-16 set was used as `YESTERDAY=CARRY_FORWARD`: Coordinator mirrors `fc5c5b46a0ec56f606444bb5dbfe400d4a444d18`; Owner `cb42efd7a6aa0e782c353803e604684b9500cdb2`; Analytic `2b93e7c237c09439746a93356c20cd15e4671028`; Wheel `134eb9eb0558a622b6f042baa20f3feb847ed6f4`; Census `26510606eea9f43450e5bb092c4542ab23fcb729`; Referee `e4c0a92301f032eb732a51f7bd997f4a19ac8b48`; Lean `180cf24f8444852a5b69bf2581f0c6d160f3a16e`. External Hecke handoff `de13ba37bf86f32d64923ddf5ebf96382aa6d006` and the earlier square-prefix variation script `92ccae182b7a7ea6a04ea1657550906150464982` were checked. There were no open PRs at intake.

### B. Mystery, rival hypotheses and discriminator

**Mystery.** Why is the finite full quotient variation tiny relative to the unsigned coefficient carrier, and which quotient scale contains the unpaid cancellation?

- **H1 (genuine Euler-sign smoothing):** native multiplicative signs force unusually small adjacent bucket changes. Native `V` should be consistently below multiplicative sign-scrambled controls.
- **H2 (generic bucket aggregation):** support sparsity plus many signed terms per low quotient explains most of the reduction. Factor-preserving sign scrambles should often have comparable `V`.
- **H3 (isolated high quotient):** the apparent saving is mostly the one-source-per-bucket region `t>sqrt X`. Then `V_high` should dominate.
- **Unexpected alternative:** a boundary-corrected exact isolation theorem pays `V_high`, but the low quotient aggregate remains the dominant open object.

The discriminator records native `V_low,V_high`, unsigned same-support variation, eight fixed-seed multiplicative controls (independent Rademacher signs on split-prime first-power Euler factors), and exact top-half prime response. Controls are diagnostics, not genuine arithmetic.

### C. Claim `20261017-census-1` - independent reproduction and held-out cutoffs

**Status: `FINITE_COMPUTATION`.** A local-Euler linear sieve was independently checked coefficient-by-coefficient through `n=10^6` against the literal Dirichlet convolution `mu*(chi_-3 mu)` followed by the prime-to-6 mask. Every tested cutoff passed `CORE+BAD=M(X)`; every root cutoff had `BAD=0`.

The published `X=10^7` values reproduced exactly: `M=1037`; variations by `d=8,4,3,2` are `25222,25451,25514,25547`; root layers are `-47157,+48194`; top-half split-prime count is `158004`, injection `-316008`, prior response `317045`.

Predeclared held-out results:

| X | M(X) | V d=8/4/3/2 | BAD d=8/4/3/2 | root layers | root V_low / V_high | top split / prior response |
|---:|---:|---:|---:|---:|---:|---:|
| 7,654,321 | -220 | 20,930 / 21,792 / 21,738 / 21,766 | -27 / -3 / 10 / 0 | -37,284 / 37,064 | 20,208 / 1,558 | 123,077 / 245,934 |
| 9,999,991 | 1,034 | 25,216 / 25,445 / 25,508 / 25,541 | -110 / -23 / 10 / 0 | -47,154 / 48,188 | 23,759 / 1,782 | 158,005 / 317,044 |

These are exact signed integers. At `X=10^7`, `V_low=23765` and `V_high=1782`: 93.0% of the complete variation lies at `t<=floor(sqrt X)`. H3 is refuted.

### D. Claim `20261017-census-2` - exact general-X high-quotient isolation

**Status: `PAPER_PROOF / NEW GENERAL-X ENDPOINT CORRECTION`.**

Let `r=floor(sqrt X)`, `N=floor(X/(r+1))`, and use the root-cutoff buckets above. Then

```text
V_high(X) := sum_(r<t<=X) |B_X(t)-B_X(t+1)|
 = 2*sum_(1<=n<=N)|a6(n)| - |B_X(r+1)|
 <= 2N <= 2*sqrt(X).
```

**Proof.** Nonzero `a6(n)` implies `gcd(n,6)=1`; hence distinct supported integers differ by at least two. If `n<m<=N<=r`, then
`X/n-X/m = X(m-n)/(nm) >= 2X/(m(m-2)) > 2`, because `m<=X/(r+1)` and `X<(r+1)^2`. Thus their integer quotients differ by at least two: every nonzero high bucket is isolated by a zero bucket. Each isolated bucket contributes twice to adjacent variation except a possible bucket at `t=r+1`, whose lower transition lies outside `V_high`; this proves the equality.

For the bound, local factors give `|a6(n)|<=d_chi(n)=(1*chi_-3)(n)`, with both sides multiplicative and the inequality immediate on split, inert, 2 and 3 prime powers. Also
`sum_(n<=N)d_chi(n)=sum_(a<=N) C_chi(floor(N/a))<=N`, since `C_chi(u)=1_(u mod 3=1)`. Hence `sum|a6|<=N`.

**Endpoint falsification.** The tempting uncorrected equality `V_high=2 sum|a6|` first fails in the exhaustive range at `X=380`: `V_high=12`, `2 sum|a6|=14`, and `|B(20)|=2`. The corrected formula had no failure for every `256<=X<=20000` and all larger test points. The older repository script states the uncorrected equality only for `X=R^2-1`, where its boundary bucket is zero; this claim extends it to arbitrary `X` without changing that valid scope.

**Proof impact.** The stronger sufficient condition `V_X=O_epsilon(X^(7/8+epsilon))` needs new work only on
`V_low=sum_(1<=t<=r)|B(t)-B(t+1)|`; the complete high side is already `O(sqrt X)`. This is a genuine carrier reduction, not a bound on `V_low`, `M`, the canonical VF defect or the #915 source.

### E. Claim `20261017-census-3` - mechanism controls

**Status: `FINITE_COMPUTATION / H1 NOT SUPPORTED`.** At `X=10^7`, unsigned same-support root variation is `1,420,759` versus native `25,547`, so signed bucket aggregation is essential. Eight fixed-seed multiplicative split-prime sign controls give `V` range `26,687..44,715` (median `29,521`). Native is smaller there, but not uniformly: at `X=531441`, native `5114` exceeds the control median `4822`. Therefore these data do not support a deterministic native-versus-scramble domination theorem. The controls change the arithmetic and carry no proof status.

A deliberately strong benchmark `V_X<=sqrt(X)log X` had no failure for every `256<=X<=20000`; the largest ratio was `0.610863` at `X=19862`, and all seven larger listed points also passed. This is `CONJECTURE / EXPLORATORY ONLY`, stronger than the requested 7/8 inlet and not promoted as a likely theorem from this range.

### F. Reproducibility and validation

Environment: x86_64; `g++ 13.3.0`; Python `3.12.14`. Census source SHA-256:
`e37e9dc85c4ac56630db8b6da8f686552bcd0a97bafcd21e8393272cafeadf51`.

```bash
g++ -O3 -std=c++17 -Wall -Wextra -Werror hecke_census.cpp -o hecke_census
./hecke_census 10000000
```

Discrete arithmetic is exact signed integer arithmetic. No floating-point value enters any identity; floating point is used only for the displayed exploratory normalized ratio. Independent checks: Dirichlet convolution versus local Euler recurrence through one million; exact `CORE+BAD=M`; root `BAD=0`; top-half injection recombination; general-X formula exhaustive through 20,000. No Lean compilation or formal proof was performed.

### G. Evidence status and decisions

Overall status: `PAPER_PROOF` for Claim census-2; `FINITE_COMPUTATION` for census-1/-3; `NO_NEW_RESULT` on `VFCanonicalSquareVonKochStatement`.

- **HIGH-QUOTIENT VARIATION:** `PAID / CONTINUE AS LEMMA`. It is exact, elementary, source-faithful for #919 and exposes the boundary term.
- **LOW-QUOTIENT VARIATION:** `CONTINUE`. This is now the precise dominant open carrier.
- **NATIVE-SIGN DOMINATION OF MULTIPLICATIVE SCRAMBLES:** `REJECT` as a proposed deterministic principle; finite ordering reverses.
- **ROOT-LOG BENCHMARK:** `CONJECTURE / DO NOT PROMOTE`.

### H. Continuation checkpoint

Do not repeat the cutoff totals. Resume with the low quotient carrier only:
`V_low(X)=sum_(t<=floor(sqrt X))|B(t)-B(t+1)|`.
Condition each adjacent difference jointly by squarefree kernel and the two hyperbola intervals
`(X/(t+1),X/t]`, and compare exact native signs with factor-preserving controls on a development range, then freeze a theorem-shaped discriminator before a larger held-out range. The first useful theorem would bound a deterministic aggregate of low-bucket differences without assuming Mertens growth; the high sector and its boundary correction are complete.
