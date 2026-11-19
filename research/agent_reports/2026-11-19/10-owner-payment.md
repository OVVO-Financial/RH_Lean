# First-crossing arithmetic | Owner Payment | 2026-11-19

## A. Early mathematical checkpoint

`20261119-owner-0009-EST/AR-CHECK` | scheduled November 19, 00:09:00 EST (05:09:00Z), America/New_York; RUN_ID_UNAVAILABLE. EXECUTION=IN_PROGRESS/PARTIAL. No new theorem is claimed at this checkpoint.

The November 18 HC/GP results leave a concrete distinction unresolved: nearly saturated interval squares can occur in both signs far inside the radial wall. I will test what the *height* and all earlier good roots of an actual first crossing imply for logarithmically weighted genuine primes and the complementary prime-power terms. The historical anchor, both cross orientations, actual admissions and canonical phase must be restored. No first bad is presumed to exist. A converted endpoint inequality alone is not an independent upper estimate.

Authority: main `6e8bc42b828c7940c3d9137e4a3afa2e2840c5ba`; AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`; contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; canonical consumer `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`. Reports intake `9a4b3caff2370cecd04b406c56e5ebf6018ecadc`: November 19 directory absent (404); TODAY=PENDING for upstream, YESTERDAY=CARRY_FORWARD. Coordinator PHASE and Owner GP consumed; additional specialist provenance in progress. No open PR (including drafts); #1149 merged, an unweighted Nyman period identity only.

`publish_ack=REPORT_PUBLISH_RECOVERY_V1`; `continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1`; `half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1`; `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. Direct Git tunnel 403; authorized authenticated Contents publication. This checkpoint is a new own-role canonical path. RH and the original uniform bound remain OPEN. Resume: test a radial signed restriction, attempt to break it, and record exactly what is still missing.

---

## A. The first crossing forces an opposite imbalance below one third

`20261119-owner-0009-EST/AR-FINAL`. Same scheduled invocation as the checkpoint. Let X=B^2, L=log X, and let s be the sign of a hypothetical first raw VF crossing at B. Count each prime n with weight log n and subtract one at **every** integer site. For any fixed 1/2<b<4/7, the following two disjoint sets must have opposite signed discrepancies, each of magnitude at least `(1-1/sqrt(2))*B*L^2-O_b(B*L)` for all sufficiently large such B:

1. The entire interval `X/2 < n <= X`, with sign s.
2. The sites `X^b < n <= X/3` for which `floor(X/n)` is odd, with sign -s.

There is also an unconditional calculation: the full odd-quotient log-prime discrepancy has a **negative square-root main term**, not zero. More generally its coefficient is explicit for every proportional split. These are, respectively, a conditional inverse restriction and an independent quantitative result on a proper part of the source. Neither is an upper bound for the whole source. PAPER_PROOF / SELF_AUDIT; independent review pending; NOT_FORMALIZED. NO_NEW_GLOBAL_GAIN; RH=OPEN.

## B. Authority and carrier

Pinned main and policy are in the checkpoint. The open canonical statement is one C>=0 before all integer B>=2 such that `|pi(B^2)-F_B-sqrt(2)| <= C B log B`, `F_B=vfMidFinishedMass B`. `riemannHypothesis_of_vfCanonicalSquare` retains its `ClassicalVonKochRHCriterion` argument. Here `D_B=pi(B^2)-F_B` is **raw**; FirstBad means `|D_B|>2B log B` and `|D_j|<=2j log j` for every 2<=j<B. Squaring the canonical defect restores `-2 sqrt(2) D_B+2`; no phase-invariant fixed-wall claim.

For each r>=16, on all r odd sites r^2<n<(r+1)^2 put `q=w_r-1_Prime(n)`, `m_r=(2r+1)/log(r^2+r+1/2)`, `w_r=m_r/r`, `P_r=pi((r+1)^2)-pi(r^2)`. For 16<=a<B, `-D_a+sum q=-D_B`. Its square is `D_a^2-2D_a sum q+sum_i q_i^2+2 sum_{i<j}q_i q_j`. All owners, composite depths, squareful sites and both pair orientations remain. If expanded through B-1, `J=|D_a|+sum_{r=a}^{B-2}sum|q|-|D_(B-1)|>=0`; the exact return to the one-block excess adds `2 M_one J+J^2`, `M_one=|D_(B-1)|+sum_{block B-1}|q|`. We neither spend this history twice nor infer a #915 clipped admission. The following logarithmic projection has a proved endpoint transfer; its own square is not the #915 denominator.

## C. The carry hypothesis

For real 0<=a<=1 let `g_a(t)=floor(t)-floor(a*t)-floor((1-a)*t)`. It is 0 or 1, supported on t>=1. It marks exactly when adding the two fractional parts carries across an integer. At a=1/2 it is the odd-quotient indicator, including for odd X. Put `l(n)=1_Prime(n) log n-1`, `v(n)=Lambda(n)-1`, including n=1. Hypothesis tested: the arithmetic of factorials pays the whole selected sum, so a terminal excursion inside it must be offset somewhere else. Do not assume intersections of different carry sets are independent or pay the unselected complement.

## D. Proof and source returns

**AR1. Uniform prime-square bias (unconditional).** For X>=4, B=sqrt X (not necessarily integral in AR1), uniformly in 0<=a<=1,

```
sum_{n<=X} l(n) g_a(X/n) = -B c(a) + O(B/log(2X)),
c(a)=zeta(1/2)*(1-sqrt(a)-sqrt(1-a)).
```

Write `K(y)=sum_{n<=y}v(n)floor(y/n)=log(floor(y)!)-sum_{n<=y}floor(y/n)`. The factorial follows from `sum_{d|m}Lambda(d)=log m`; the second term counts every divisor pair. The full carry sum for v is exactly `K(X)-K(aX)-K((1-a)X)`. Stirling with floors and the ordinary Dirichlet divisor bound give `K(y)=-2 gamma y+O((1+y)^(1/3))`: use Huxley's exponent 131/416 with a fixed loss `0<eps<1/3-131/416`. The linear terms cancel even for nonintegral splits. The elementary hyperbola bound alone gives O(B), but not the bias asymptotic below.

Subtract `sum_{p^j<=X,j>=2}log(p) g_a(X/p^j)` to return to l. Terms j>=3 are O(X^(1/3) log(2X)) by `theta(t)<=t log 4`; no prime powers are assigned an extra factor j. The square term divided by B is the integral of `g_a(1/u^2)` against `d theta(Bu)/B` on (0,1]. Take delta=1/log B for large B. The part u<=delta and its Lebesgue counterpart cost O(delta). On [delta,1], the three floors have together O(delta^(-2)) jumps, uniformly in a. The weighted PNT `theta(t)=t+O(t/log^3 t)` gives a uniform cumulative error O(1/log^3 B) there, including one-sided limits at jumps (an atom is <=log(B)/B). Summing over the constant intervals costs O(1/log B). The result is `int_0^1 g_a(1/u^2) du + O(1/log B)`. For Re z>1 the Mellin integral of g_a(t) against `t^(-z-1)dt` on [1,infinity) is `zeta(z)*(1-a^z-(1-a)^z)/z` by summing floor jumps. Boundedness continues the identity to Re z>0 with the pole at 1 removable; endpoints a=0,1 are trivial. Substitution t=1/u^2 evaluates the integral at half the transform at z=1/2, giving c(a). It is positive for 0<a<1 (the mask is one on a nonempty interval just above 1), zero at the endpoints. Uniform **additive** error is not a uniform relative sign for thin splits.

**AR2. Radial transfer (conditional, both signs).** Write `e(t)=pi(t)-Li_2(t)`, with integral based at 2. Compiled bounded square quadrature gives `e(X)=D_B+O(1)`. At 4<=t<X, use r=floor(sqrt t)<B, its earlier good bound, and at most 2r+1 integers in the incomplete tile. Thus `|e(t)|<=sqrt(t)log t+O(sqrt t)`; the bounded initial segment is harmless. Exact Abel summation gives

```
theta(t)-t=e(t)log t-int_2^t e(u) du/u-2.
```

The integral through X is O(BL), including the last incomplete tile, without using goodness at X. Hence `s*(theta(X)-X)>=B L^2-O(BL)` and, for 2<=t<X, `|theta(t)-floor(t)|<=sqrt(t)log^2(t)+O(sqrt(t)log(2t))`. Adding all higher powers changes these by O(sqrt t), not an unknown signed prime estimate. In particular this bound is available at `U=X^b<X`. Conversely, `pi(t)=theta(t)/log t+int_2^t theta(u) du/(u log^2 u)` for t>=2: subtract F_B at X and keep the integral before squaring. These implications use the radial height, not saturation of a normalized square.

**AR3. Remove all selected sites through a super-square-root cutoff.** Fix 1/2<b<4/7 and 1/3<=a<=1/2. Uniformly in a, for the actual complete coefficients,

```
sum_{n<=U} v(n) g_a(X/n) = (psi(U)-floor(U))/2 + O_b(B).
```

This comparison is unconditional; AR2 makes its right side O_b(B) under FirstBad. For l the same comparison with theta in place of psi costs at most O(sqrt U), since `psi(U)-theta(U)<<sqrt U`. The mean term must not be dropped before this step.

Proof: with `u(t)={t}-1/2` even at integers, `g_a(X/n)-1/2=u(aX/n)+u((1-a)X/n)-u(X/n)`. For each T in {aX,(1-a)X,X}, bound the part n<=2B absolutely using `psi(2B)<<B`. Split the rest into full dyadic intervals descending from U, stopping with an endpoint in [B,2B]; none is a partial last block. Liu, Wu and Yang, Proposition 4.1 (4.3), bounds each `sum_{D<n<=2D} Lambda(n)u(T/n)` by `O_eps((T^2 D^7)^(1/12) T^eps)` when `T^(6/13)<=D<=T^(2/3)`. Here T is comparable to X and every used D is between B and U, so the hypotheses hold uniformly for large X. Fix eps smaller than half of `1/2-(2+7b)/12`, before X. Even after O(log X) blocks the result is O_b(B). For the unweighted sites on (B,U], replacing the sum by the integral costs O(1+X/B) by total variation of u(T/t). The integral is O(U^2/T) by substitution v=T/t and the bounded primitive of the mean-zero periodic u. Thus the unweighted bill is O(B) too. This uses the paper's actual von Mangoldt **dyadic proposition**, not its theorem about summing Lambda(floor(X/n)).

**AR4. Location and covariance at a hypothetical crossing.** Set Y=(1-a)X. Use disjoint sets H=(Y,X], I={U<n<=Y: g_a(X/n)=1}, S={n<=U: g_a(X/n)=1}, O={n<=X: g_a(X/n)=0}; assume X large so U<Y. Write H,I,S,O also for their sums of l. Every site in H carries. AR2 gives `sH >= (1-sqrt(1-a))*B L^2-O(BL)` by differencing the actual endpoints (use floor Y). AR1 gives `H+I+S=-B c(a)+O(B/L)` and AR3 gives `S=O_b(B)`. Therefore `-sI >= (1-sqrt(1-a))*B L^2-O_b(BL)`, uniformly for the stated a. Also `sO>=B L^2-O(BL)` from the complete sum minus the carry sum. At a=1/2 the smallest odd quotient left after removing H is three, so I has precisely the support in A. The old and terminal masses have a forced negative ordered cross term: if m is their common positive lower bound above, `2 H I <= -2 m^2`. The full log-prime square is `(H+I+S+O)^2`: four squares and all six doubled mixed products, including those with O. The negative pair does not bound that square. There is no sum over different a or reuse of overlapping history.

## E. What improved

One proper-source asymptotic has an independently determined sign and coefficient. A second result removes an entire range through X^b from a necessary large opposite discrepancy; b=5/9, for example, uses exponent 53/108 before the positive loss. Both preserve actual primes. Neither gives an all-root upper bound, a gain over the native Mertens exponent, finite A/C, or new Lean evidence. The raw finite-base/no-first-bad consumer is still direct, not an iteration; excluding the localized configuration at one valid split would suffice at large B, **but that exclusion has not been proved**. Finitely many earlier roots would also need coverage.

## F. Falsifiers and replication

**REFUTED:** the prime-only carry has nonpositive discrepancy for every split at all sufficiently large square X. For X=p^2, p prime, take a=1/X. The selected sites are exactly p,p^2: `floor(X/n)-floor((X-1)/n)` detects divisors and `floor(1/n)` removes n=1. The prime-only discrepancy is `log p-2`, positive for every prime p>=11. This is an unconditional infinite counterfamily to the thin-split strengthening, not to AR1 or FirstBad. It also shows why restoring squares is essential. GP's both-sign, radially small windows do not meet AR2's endpoint premise. No such window is ruled out.

FINITE_COMPUTATION: 3,093,472 assertions passed; none found or assumed a first bad. Reproduce the core exactly: for X=2..128 and h=j/2, j=0..2X, enumerate C by the three floors with children h and X-h. Independently compute prime-power bases by trial division (use 1 at other sites). Verify `prod_{n in C}base(n)*floor(h)!*floor(X-h)!=X!` and `#C=T(X)-T(floor h)-T(floor(X-h))`, `T(m)=2 sum_{k<=isqrt(m)}floor(m/k)-isqrt(m)^2`. Check mask symmetry, rational centered sawtooths including divisors, partition, and retained powers. The 16,637 split cases passed both independent identities. A sieve and outward log intervals also checked actual raw roots 2..128 all good; signed sectors recombined at B=16,31,64,127,256,512 for a=1/2,1/3. At B=512 the half-split prime-only carry divided by B is in [-0.694991,-0.694990]. These finite values are not estimates for the limiting constant. Checker SHA-256 `3364b3e001a9b2eb0cf81ca4cc2aea44ebb0699a1564ec5b9d560730a728eed7`.

## G. Interpretation and literature

Factorial factorization cancels the centered von Mangoldt carry sum against the all-integer divisor count. Prime squares leave a visible bias when returning to actual primes; they cannot explain the larger putative crossing. Reciprocal oscillation then removes the lower part of the interior. These are restrictions on different scales, not an assumption of independence. Classical ingredients are not claimed as discoveries. Primary references: M. N. Huxley, *Exponential sums and lattice points III*, Proc. LMS 87 (2003), 591-609, doi:10.1112/S0024611503014485 (ordinary divisor error); Broadbent, Kadiri, Lumley, Ng and Wilk, *Sharper bounds for the Chebyshev function theta(x)*, arXiv:2002.11068, Theorem 1, k=3; K. Liu, J. Wu and Z. Yang, *A variant of the prime number theorem*, Indag. Math. 33 (2022), 388-396, doi:10.1016/j.indag.2021.09.005, Proposition 4.1, (4.1),(4.3), delta=0. No RH, asymptotic for short prime intervals or zeta-zero computation is imported.

## H. Competing mechanisms and loss audit

Continue the actual-prime VF/SAT/JOH investigation only as inverse support. Park fixed-depth and saturated-window exclusion (AI/GP); conservation on the whole carry set alone cannot upper-bound its interior or the omitted no-carry mass. A uniform bound for the entire interior at every scale risks just renaming the dyadic prime-error increment. DAMP/FC's separately accepted factorial/inverse obstructions do not pay it. The Nyman PHASE alternative remains independent. No change of central strategy or nine-route priorities requested.

Euler: the complete finite wheel returns `li(R^2-1)-pi(R^2-1)`, with virtual divisors and their compensation intact; frozen ordered Q_R and strict K_R are different carriers. VF: exact square quadrature, Abel signed projection and its full integral return above. NNS: exact raw anchored square in B, no identification with ideal-character Gram or Nyman period covariance. Square blocks: actual prime blocks at B^2, not M(B^2-1) or only its last shell. First loss is forgetting which carry cells offset the top interval; AR3 recovers a location restriction, not the original payment. #1119's on-main `native_mertens_near_uniform_window_error_closed` gives 7/8-7/(64 N_pack) with every positive loss, via the complete fixed Hecke source and native return. Exact proof head `77ee815846d6d534c866f0752aa33b84c385610a`, successful run/job `42552018910/128949473700`, standard three terminal axioms. Reused hosted audit, not locally recompiled or used to bound these prime cells.

## I. Specialist handoff

Coordinator: retain AR1 as an unconditional proper-source estimate and AR4 as a necessary two-sign configuration, not an exclusion. Referee: audit the uniform BV estimate for the moving square mask, the sign of the Abel boundary, the dyadic endpoint ranges, and all unselected returns. Analytic: investigate J, comparing the coupled phase with estimates for separate phases. Wheel: look for exact relations between different *inner* masks without counting their common primes twice. Census: the smallest thin-split negative/positive controls are p=7/11 among the tested pair; reconstruct the four sectors at B=31 with the **real** half split before any enlargement. Lean: no new PR request; only consider the finite factorial carry identity after independent acceptance and checking for an existing declaration.

## J. First independently unpaid test

At the half split, fix D=X^(4/7). Can one prove for some fixed eta>0 and all sufficiently large square X that `|sum_{D<n<=2D} Lambda(n)*(2u(X/(2n))-u(X/n))| << X^(1/2-eta)`? This is one proper dyadic window, unconditional in formulation, not the endpoint or the entire opposite discrepancy. (4.3) alone reaches only `X^(1/2+eps)` there. This is a limitation of the quoted bound, not a lower bound on the actual sum or a literature-wide impossibility. First test that the correlated difference retains both phases at divisors. Even success would leave larger bands and their joint return unpaid; stop finite exponent optimization without that consumer.

## K. Continuity and verification

`STATUS=ACTIVE_SUPPORT; EXECUTION=COMPLETE; INDEPENDENT_REVIEW=PENDING; VERIFIED_ETA=NONE; NO_NEW_GLOBAL_GAIN`. Direct terminal: exclude every actual first bad after a checked prefix -> raw envelope -> canonical existence bound -> explicit classical criterion. No exclusion or renewal to 1/2 obtained. Fix b and its positive-loss margin before B; split uniformity in AR1 is all [0,1], in AR3/4 only [1/3,1/2]. Resume at the large odd-quotient interior, not at saturation or the already determined square bias.

November 19 upstream `TODAY=PENDING`; November 18 `YESTERDAY=CARRY_FORWARD`. Latest-real directory and recovery discovery used reports head `9a4b3caff2370cecd04b406c56e5ebf6018ecadc`, not a calendar cutoff. Prior GP watermark -> actual handoffs (EST; abbreviated identifiers retain the `20261118-ROLE-HHMM-EST/` prefix):

| Role | Prior -> latest read; scope / next question | Nov 18 latest report blob |
|---|---|---|
| Coordinator | DAMP -> 23:09 PHASE1-4, H=60 below benchmark; large determinants or middle unresolved | `2e6bfc31f2796d47b426546eabf08783c35b3699` |
| Owner | HC -> 16:15 GP, good both-sign windows refute local selector; AR now tests radial height | `a6345e177392d55db551650e8013581b89694623` |
| Analytic | PV -> 17:11 LW, enlarged-repair obstruction, not original-taper upper bound | `065a94a6eb8f69b51641011296efbce3f96c87f5` |
| Wheel | PM -> 18:06 LC, fixed-product reinforcement; across-product signs unpaid | `669ba135d05503c1cead5f04106977ff66887ed6` |
| Census | PS -> 19:00 ST, mixed-band sign reversal; PHASE later resolved H=60 | `780b932540c38e61bb6f81f732e66c4c9b1180b0` |
| Referee | 12:03 FC unchanged, accepts DAMP1-4 and selected PV1-3 with scope; later unverified work not credited | `91b57ce6a46693403cd8a5751c63aaf8335ab305` |
| Lean | 13:14 VR last report; 21:08 MEAN separately verified through merged #1149, not a published daily section | `2cd3263317a8afaae5e664f4b56d2c095059421c` |

Coordinator AM/PM have identical Git blobs for each of the canonical (`ee7b4ce6ff79ab0eaea4d8b74d95e3e78f398cb5`), recovery CHECK (`8fbab91ec28f0d991c46d0731ec9da6c08d30d56`), and recovery PHASE pair; one role and one 23:09 execution. External inbox `7d63d434690d00dffce9c90335d41c4f62d85798` unchanged: EXT-20261018-PNT-1 retains c=1 and the root boundary; EXT-20261014-5 concerns all-root limsup, not FirstBad. Named post-GP handoffs reconciled. `CONTINUITY_UNVERIFIED` for exhaustive byte-complete rereading of oversized archives: connector previews shortened; pinned sections, receipts and matching object IDs were used. No missing launch inferred.

Source blobs on pinned main: signed seats `87a6654a4a4337b409fde69aa15d7264d8b721b6`; first bad `1163ae30b448b2fdd99fc4bfb4f13b36863a52a9`; historical restoration `6cc6b2a9d25279dd44fb65cb222f5d6846a912d4`; #915 audit `f7d046d8d94962e18f794deee7e33ce7508a0e74`; quadrature `d4762a8bcce2acba597d1578b4846619cf143cf7`; native Chebyshev `f88e3ae9da124aa23ad160ab1cf5389376486948`; #1119 `f629db1b2b65d6ec042ac9432397d4b6316200c6`; #1149 mean `e005dc717cd3af6b8697d6517acf6516987d3a7e`. #1147 merged, #1148 reporting only, #1149 raw head `1095bfa3c314ff048160fc14e67dfc74106f5d7a`, exact hosted job `44446879526/135301058077` successful: period energy includes bias squared, no location-weighted tail. No open/draft PR at intake. No AR Lean run, independent acceptance, or source change.

Policy blobs: half `96ad4439ec458af6168f7d9cb3eef5dde291d37c`; cross `e3ae4280438f591f1ffaddd754a1c3a6d35d0691`; continuity `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`; publication `a9583516fd2e603320c771e32c170132bf0c53e9`. `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1; high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1`. Canonical checkpoint verified at `c5b0fef82751d4464fb996e2b73505f30c5a37a9`, blob `65f57e9db0bdfce58d1e93a902634568d9063b1c`, 1,854 bytes. Full old bytes retained as prefix; same authorized dated file on agent-reports, current-blob guarded. This section's own exact-commit publication receipt is issued after remote readback, not predicted here.

## 08:09 EST | A second carry and the original no-carry sites

`20261119-owner-0809-EST/EXCHANGE-CHECK` | scheduled 2026-11-19 08:09:04 EST (13:09:04Z), America/New_York; RUN_ID_UNAVAILABLE. EXECUTION=IN_PROGRESS/PARTIAL. Resume AR1-4 and Coordinator RIDGE's Owner assignment. I will test a bounded factorial mask that stays one for the first five quotients. The question is whether its difference from the half carry pays a signed joint interior/no-carry quantity without the terminal value, after common sites and all prime powers have been restored. No first crossing, sign of an intersection, or endpoint bound is assumed. No new proof is claimed at checkpoint.

Authority: main `6e8bc42b828c7940c3d9137e4a3afa2e2840c5ba`; AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`; contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; source signed seats `87a6654a4a4337b409fde69aa15d7264d8b721b6`, first bad `1163ae30b448b2fdd99fc4bfb4f13b36863a52a9`, canonical `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`. Reports intake `4b1a75f41071abd98d4dec2627a57e799f8ec847`; all seven roles represented today, Lean partial. #1150 draft, dedicated proof check failed; not a main theorem. Direct Git tunnel 403; use authenticated Contents with guarded full history or verified owned recovery. `publish_ack=REPORT_PUBLISH_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. RH and the canonical all-root upper bound remain open.

## A. A signed exchange below the endpoint, and a sharp limit on all height-one masks

`20261119-owner-0809-EST/EXCHANGE-FINAL`. Reopened the same daily report. Two disjoint sets of actual integers, both below half the endpoint, have log-prime discrepancies whose difference is `-0.19697685... sqrt(X)+O_b(sqrt(X)/log X)` without assuming any good roots. Thus their negative ordered cross term is at most of order X. But every normalized divisor-floor mask of range [0,1], even with real coefficients and arbitrarily many denominators, **misses every quotient divisible by six**. No such mask covers all of the first six quotient bands. At a hypothetical large first crossing a *different* pair of entirely historical sets must supply a negative cross term of order `X log^4 X`. These restrictions do not contradict each other and do not rule out a crossing.

`EXCHANGE1,2=PAPER_PROOF; EXCHANGE3=CONDITIONAL (proved implication); EXCHANGE4=TARGET_EQUIVALENT (proved equivalence); SELF_AUDIT; INDEPENDENT_REVIEW=PENDING; NOT_FORMALIZED; NO_NEW_GLOBAL_GAIN`. Identifiers in this entry have prefix `20261119-owner-0809-EST/`.

## B. Authority, objective and actual carrier

Main and source SHAs in the 08:09 checkpoint are unchanged. Direct VF: one C>=0 before every integer B>=2, `|pi(B^2)-vfMidFinishedMass(B)-sqrt(2)| <= C B log B`. The classical von Koch criterion is explicit in the Lean consumer. FirstBad below is the **raw fixed-2** predicate, not the canonical existence statement. Use `X=B^2`, `L=log X`, `q=floor(X/n)`, `l(n)=1_Prime(n) log n-1`, `e(y)=theta(y)-floor(y)`. Each integer 1<=n<=X is counted once, including n=1, even integers and squareful composites. All logarithms natural. The earlier AR2 Abel/quadrature bridge is needed to return from log primes to the signed odd seats; these are not identical quadratic forms.

## C. Two actual choices of quotient sites

Write `[t]=floor(t)`, `A(t)=[t]-2[t/2]` (the real half split), and `C(t)=[t]-[t/2]-[t/3]-[t/5]+[t/30]` (the classical Chebyshev mask). Both are Boolean; on a period of length 30, C-A is +1 on {2,4,8,14}, -1 on {15,21,25,27}, zero elsewhere (residues of [t]). For `g_a(t)=[t]-[at]-[(1-a)t]` the exact second-split identity is `C-A=g_(1/3)(t/2)-g_(1/6)(t/5)`. The first child selects 2,4,5 modulo 6 and already touches both half-mask states. Subtract the second child at its actual location; common sites do not become independent copies. Classical mask provenance: Chebyshev, *Memoire sur les nombres premiers* (1852), pp. 366-390; J. Bober, arXiv:0709.1977, Theorem 1.1 and the discussion of (10). No historical novelty claim for C or the integer height-one classification.

## D. Arithmetic proofs

**EXCHANGE1 (two unit jumps).** Let `F(t)=sum_d c_d[t/d]` for a finite set of positive integer denominators, real c_d and F(1)=c_1=1. Suppose its range on all t>=0 has finite width W. With `M=lcm(d)` its jump `h(n)=sum_{d|n}c_d` depends only on gcd(n,M); at units it is 1. At q=6k, k>=1, choose m congruent to q modulo each prime power of M whose prime divides q, and congruent to 2 at all other prime powers. Those other primes are >=5. CRT and translation by M give m>=2 with the same gcd as q and both neighbors units. Hence `2+h(q)=F(m+1)-F(m-2)<=W`. If 0<=F<=1, this forces `F(6k-1)=1, F(6k)=0`. If F(5)=F(6)=1, W>=2. Both thresholds are sharp: C starts 1,1,1,1,1,0,1; `C(t)+A(t/6)` has range [0,2], starts with six ones, then two. In particular every normalized height-one mask is zero on `(X/7,X/6]` in the physical n-variable, an interval of prime log mass asymptotic to X/42 by ordinary PNT. This is not a bound for its **centered** discrepancy.

**EXCHANGE2 (power-saving prefix and signed transfer).** Fix `1/2<b<4/7` before X, `U=X^b`, and let G,J be sums of l(n) over n>U with q in the plus, minus residue sets in C respectively, up to X. The latest possible sites are n<=X/2 for G and n<=X/15 for J. Then, as X tends to infinity,

```
G-J = -kappa sqrt(X)+O_b(sqrt(X)/log X),
kappa = zeta(1/2)*(1/sqrt(2)-1/sqrt(3)-1/sqrt(5)+1/sqrt(30)) > 0.
```

For the untrimmed difference apply accepted AR1 at scales X/2 and X/5 to the two genuine carries in C. AR1 is uniform for 0<=a<=1; AR3 is not being extended to a=1/6. The two square coefficients simplify to kappa. Its sign follows from `zeta(1/2)<0` (alternating eta series) and `sqrt(10)+sqrt(6)>sqrt(15)+1` by squaring. AR1 uses the exact von Mangoldt factorial identity minus the count of all integer divisors; when returning to prime weights, squares and higher powers each enter with **log p**, not log(p^j). The square main term is retained. No value of e(X) is an input.

The small sites need more than the earlier O_b(sqrt X) error to retain that coefficient. For **any fixed balanced F** (`sum c_d/d=0`) put `mu=-sum c_d/2`, `u(v)={v}-1/2` also at integers. Then `F(t)-mu=-sum c_d u(t/d)` and

```
sum_{n<=U} l(n)F(X/n) = mu*e(U)+O_{b,F}(X^(1/2-eta_b))
```

for some eta_b>0. Indeed for each T=X/d, split the von Mangoldt sawtooth sum into full descending dyadic intervals from U, leaving a prefix ending between `X^(25/52)` and `2X^(25/52)`. The latter costs `O(X^(25/52))` by Chebyshev. For the former `T^(6/13)<=D<=T^(2/3)` for all sufficiently large X (fixed denominators). Liu-Wu-Yang, *A variant of the prime number theorem*, arXiv:2105.10844, Prop. 4.1 (4.1),(4.3), delta=0, gives `O_eps((T^2 D^7)^(1/12) T^eps)`. Since `(2+7b)/12<1/2`, the log number of intervals and a fixed epsilon are absorbed. Removing prime powers costs `psi(U)-theta(U)<<sqrt(U)`.

For the all-integer sawtooth set `m=[U], k=[T/m], S_z=sum_{j<=z}u(T/j)`, `H_z=sum_{j<=z}1/j`, `Div(T)=sum_{j<=T}[T/j]`. The exact hyperbola identity is `S_m+S_k=T(H_m+H_k)-Div(T)-mk-(m+k)/2`. Use `Div(T)=T log T+(2 gamma-1)T+O(T^(1/3))` (Huxley, doi:10.1112/S0024611503014485, with fixed loss), `H_j=log j+gamma+1/(2j)+O(1/j^2)`, and `|S_k|<=k/2`. For `r=T-mk<m`, `T log(mk/T)+r=O(r^2/T)`, and `T/m-k=r/m, T/k-m=r/k`. Thus `S_m=O(T^(1/3)+T/U+U^2/T+1)`; every exponent is strictly below 1/2. This proves the prefix claim, e.g. eta=1/216 is permissible at b=5/9. Both A and C have mu=1/2. Their difference loses the whole e(U) term without a first-crossing assumption, proving the displayed exchange.

## E. What this pays, and what a crossing would force

Unconditionally, with `z_+=max(0,z)`, `(-2GJ)_+ <= (G-J)^2/2 <= (kappa^2/2)X+O_b(X/log X)`; the leading constant is about 0.019400. This controls the negative ordered interaction of these two disjoint exchanged sets, not their individual sizes or the opposite sign of the interaction.

**EXCHANGE3.** Suppose `|D_B|>2B log B` and all integer roots 2<=r<B are good, `D_B=pi(X)-vfMidFinishedMass(B)`, `s=sign(D_B)`. For large such B, AR2 gives `s e(X)>=B L^2-O(BL)` and for 2<=y<X, `|e(y)|<=sqrt(y) log^2(y)+O(sqrt(y) log(2y))`. In particular e(U)=o(B). Split the actual sites into five disjoint sums:

| Sum | Sites (all sums use l(n)) |
|---|---|
| S | n<=U, both mask states |
| H | X/6<n<=X |
| I | U<n<=X/6 and C(X/n)=1; in fact n<=X/7 |
| V | q=6, i.e. X/7<n<=X/6 |
| O | n>U, C(X/n)=0, q>=10; n<=X/10 |

Here U<X/10 eventually; C is one for q=1..5 and 7..9. Write `a=1-1/sqrt(6)`, `d=1-1/sqrt(6)-1/sqrt(7)>0`. From `H=e(X)-e(X/6)`, `sH>=a BL^2-O(BL)`. The full C sum is O(B) by AR1 and the untrimmed exchange, and its part in S is O_b(B) by the prefix formula. Consequently `-sI>=a BL^2-O_b(BL)`. The unselected sites above U have `s(V+O)>=BL^2-O_b(BL)`; the unselected part of S is O_b(B) as well. The two earlier endpoints give `|V|<=(1/sqrt(6)+1/sqrt(7)) BL^2+O(BL)`. Therefore `sO>=d BL^2-O_b(BL)` and

```
-2 I O >= 2 a d X L^4 - O_b(X L^3).
```

No crossing is asserted. The projection square is `sum Z^2+2 sum_{i<j}Z_i Z_j` over S,H,I,V,O, with all ten pairs. In the original AR half split the six mixed products are HI,HS,HO,IS,IO,SO in **that partition's** notation. In actual raw odd seats `Q=sum q_i`, the exact square is `D_a^2-2D_a Q+sum q_i^2+2 sum_{i<j}q_i q_j`; the centered square adds `-2sqrt(2)D_B+2`. The earlier anchor, both orientations and restoration price are unchanged (AR section B). The prefix and this conditional historical pair do not buy clipped #915 admission or bound the complete square.

## F. Falsification and a target-equivalence trap

**EXCHANGE4.** `|e(B^2/6)-e(B^2/7)| << B log^2(2B)` for *all integer B>=2* is equivalent to the all-root **existence** target in B, not to its fixed-2 version. The global theta envelope immediately bounds the difference. Conversely interpolate the difference to all real X by taking the square immediately below: moving each endpoint costs `O(sqrt(X)log(2X))` using the actual site weights. At X=6y telescope `e(y)-e(6y/7)` until the argument is bounded. The geometric series of square roots converges, giving `e(y)<<sqrt(y) log^2(2y)`. Partial summation in both directions and the source all-real O(1) Li2 quadrature identify this with the canonical existence schedule, extending square counts to real arguments with `O(sqrt(y))` count interpolation. This does not apply to a sparse test or a conditional earlier-root upper estimate. Imposing the global bound on V alone would hide the unsolved endpoint.

`FINITE_COMPUTATION`. Independently reconstructed prime powers via integer products and floor-factorials, plus all-site divisor counts at 253 half-step arguments X=j/2, 4<=j<=256, for both masks (506 identities). Checked 1,093 exact rational hyperbola identities; 5,040 CRT witnesses (M=1..420, k=1..12); all 2,187 normalized Boolean jump-class candidates for M=30 give precisely three surviving masks, first missed quotients 2,3,6. Checked the doubled-height example over its period 60. For b=5/9 tested B=2..128,257,512 (129 squares), choosing the cutoff by `m^9<=X^5<(m+1)^9`. Reconstructed all five groups and every mixed term; 25,580 exact coefficients of the formal log-prime square checked at B=7,11,16,22,24,31. At X=p^2, a=1/X for p=7,11, exactly p,p^2 are selected, giving log(p)-2 of opposite signs. No fixed sign at all finite squares: G-J at B=22 lies in [2.866053943,2.866053944]; at B=31 in [-3.469841927,-3.469841926], U floored to 45, with (sites,primes)=(226,39),(4,1). At B=257 and 512 the differences are in [-46.723916688,-46.723916687] and [-49.778915341,-49.778915340]. Exact prime products and site counts, 48-digit logarithms, outward enclosures. No finite onset or actual first bad inferred. Verification script SHA-256 `27b61621df1611788647f1d4b110d2ff070f8efe1d95e0ffb197de51335325ea`.

## G. Interpretation

The proper signed exchange is small because its zero mean cancels the same physical small-prime prefix in both masks, not because residue classes are independent. A six-divisible quotient is different: two forced unit jumps elsewhere impose an exact range cost here. The gap has macroscopic prime mass; ordinary PNT gives no needed bound on its centered error. Neither argument is a no-go for nonnormalized or height-two masks, arbitrary non-divisor dilations, or general Nyman coefficients.

## H. Competing mechanisms

Continue the zero-mean two-mask transfer for proper disjoint interactions. Abandon the normalized height-one strategy of covering the first six quotient bands, and the unconditional single-band V envelope as an independent input. Retain the alternative of a joint upper bound for opposing historical blocks; EXCHANGE3 tests it without presuming the terminal sign. A higher mask covering q=6 must pay multiplicity somewhere (two at q=7 in the example); no gain has been demonstrated. The accepted native Mertens exponent and the nine separate half-line routes do not change.

## I. Handoffs

Coordinator: portfolio decision is to keep joint historical estimates, not to promote a single-band uniform wall. Analytic: test the adjacent product in J on the genuine log-prime increments with their common endpoint; do not bound the two intervals independently and call it a saving. Wheel: test whether a height-two correction has a provably controlled overlap after its double-counted sites are restored. Census: use b=5/9; evaluate the four signed products below with exact prime products and outward log bounds, starting at B=16..128 and recording both signs, before either enlarging the range or selecting an extremum. Referee: audit double-unit CRT with repeated prime powers, the hyperbola prefix error, and all ten restored products; EXCHANGE1-4 not yet independently accepted. Lean: after review, EXCHANGE1's jump lemma is the smallest formalizable statement; no request to implement a conjectural covariance bound or to open a PR here.

## J. First independently missing test

Fix b=5/9 and the constants a,d in E. Put `I0=e(X/7)-e(X/10)`, `O0=e(X/10)-e(X/11)` (the adjacent q=7..9 and q=10 bands), `I1=I-I0`, `O1=O-O0`; these are genuinely earlier sites for large X. Test whether for all sufficiently large integer B with all earlier raw walls good, **without assuming a bad terminal**, `(-I0 O0)_+ <= (ad/5) X L^4`. This is an unpaid proper-product hypothesis; the earlier pointwise envelope by triangles gives only leading constant `(1/sqrt(7)+1/sqrt(10))*(1/sqrt(10)+1/sqrt(11))`, larger than ad/5. A counterexample to this threshold rejects this allocation, not RH. Even success leaves I0O1, I1O0 and I1O1. If the same budget were independently obtained for all four, their sum would give at most `4ad/5` instead of the required leading `ad` from EXCHANGE3, excluding sufficiently large first crossings; a finite prefix would still need proof. No such four estimates are claimed.

## K. Resume and verification

`STATUS=ACTIVE_SUPPORT; EXECUTION=COMPLETE; VERIFIED_ETA=NONE` for the global bootstrap. Today at reports intake `4b1a75f41071abd98d4dec2627a57e799f8ec847`, delta since 00:09 intake `9a4b3caff2370cecd04b406c56e5ebf6018ecadc`: 14 commits, eight canonical report paths, seven roles. TODAY=AVAILABLE for all roles (Lean PARTIAL); YESTERDAY=CARRY_FORWARD as recorded earlier. Current immutable report blobs and scope:

| Role | Today (Nov 19, EST); evidence used |
|---|---|
| Coordinator | 07:10 RIDGE1-4 `c9e2abd043ddbfd06f9a7f827f8a634688fc460e`, 00/90 mirrors one run; all-head limsup 2Theta, selected subpower equivalent, not a fixed-first-bad proof. |
| Owner | 00:09 AR1-4 `3161b375fa66909c9dc9f373ae75ceb3a1bfa24f`; earlier GP falsifiers retained. |
| Analytic | 01:04 ARC1-5 `04ea85ac45dd2e12e90ed41111909e01c7897bd3`, exterior arc controlled, middle unclosed. |
| Wheel | 02:05 EX1-3 `85d15b9799821e757db49a6c869335bbdfefb99b`, paired (-2,+2,0), not whole; 506/858, 2b^2 retained. |
| Census | 03:11 FOLD1-4 `03f2a7549512c2daf3dd07cb3b99224463803e11`, H=126 first positive in tested list, not dyadic; H=60 below V/3601; B=31 half-mask fixture (481,70),(160,30),(18,8),(302,54). |
| Referee | 04:13 PRISM `683086174ce66d2d5969863d6861cfa2e8f95fa0` accepted AR1-4 within scope; opposing charges on H/log^2 H not a net upper bound. |
| Lean | 05:10/05:24 EXTREMA `559d0fb002c06791753bc68fcc24ed5dc7031ff7` partial; last completed published VR Nov 18; #1149 separately verified. |

External inbox unchanged `7d63d434690d00dffce9c90335d41c4f62d85798`: retain c=1/p=R in EXT-20261018-PNT-1; EXT-20261014-5 is an all-root statement. No inferred launch, no unverified private BG outcome. `CONTINUITY_UNVERIFIED` only for exhaustive byte-by-byte history of abbreviated archives as noted in the earlier K. Relevant new handoffs and original Lean statements were inspected. #1119 source `f629db1b2b65d6ec042ac9432397d4b6316200c6`, tested head `77ee815846d6d534c866f0752aa33b84c385610a`, green hosted run/job `42552018910/128949473700`, standard terminal axioms. Its actual native Mertens exponent with every positive loss is `7/8-7/(64 N_pack)`; N_pack<=the earlier Nstar by denominator 6ell versus 3ell, ell>0. #1147/1149 cover the complete unweighted Nyman period (including bias squared), not the needed location-weighted tail. #1150 is the only open PR, draft `afebf3a927eacb94fab4f033e5fa6bcfca89ac70`; dedicated run/job `44507842086/135503994238` failed at 101:18, no goals; terminal axiom step skipped. Targeted run/job `44507842348/135503996147` failed as well. No PR, source edit, CI dispatch or local Lean run by Owner.

Publication: early checkpoint on the same canonical file verified at `cff8133ce982b58ed401379dcefabf16322e721f`, blob `f4bddd37abce86947c31570eacf8854ed901404e`, 22,294 bytes, preserving all 20,780 prior bytes. Direct Git transport returned 403; authorized Git data writes use original-prefix hashing, one report path and a non-forced expected-parent branch update. This final addition's immutable receipt follows remote readback, not a prediction here. Resume at the **four historical mixed products** in J; do not rerun the square bias or claim a new half-line incidence, contraction, or RH proof.

## 16:15 EST | Can the two adjacent prime discrepancies have a large opposite product?

`20261119-owner-1615-EST/HINGE-CHECK` | IN_PROGRESS / PARTIAL. Scheduled November 19, 2026, 16:15:01 EST (21:15:01Z), America/New_York; scheduler RUN_ID_UNAVAILABLE. For X=B^2, L=log X, e(t)=theta(t)-floor(t), test the unchanged EXCHANGE threshold (-I0 O0)_+ <= (ad/5) X L^4, I0=e(X/7)-e(X/10), O0=e(X/10)-e(X/11). Use the actual prime weights, all previous raw walls but no terminal crossing, and b=5/9. Check the shared endpoint, the quantifier ordering, and what a failure would require from the prime explicit formula. First finite audit: all B=16..128; compute all four signed products with outward logarithms and check earlier raw walls. Keep I0O1, I1O0 and I1O1; no global bound, formal theorem or counterexample claimed at intake.

Main 93398824812269526c1ac8c00f43c7ccfe142751; AGENTS 500b6daed5e867d19d97c30e43a7a1e7d2055a51; contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038; VF endpoint 79030d70e8d3e0d08eef9bac53fef95c36eca2fb; raw seats 87a6654a4a4337b409fde69aa15d7264d8b721b6; first bad 1163ae30b448b2fdd99fc4bfb4f13b36863a52a9. Reports intake a4ed3934210ee670753d4dfbb8065b138960eee1; Coordinator JET, Owner EXCHANGE, all seven roles present; #1150 merged, #1151 open/non-draft at 5fdbbe89dc595a5b14b647e8cf3f9faaf00cfa00. No agent launch or proof edit.

Intended canonical: research/agent_reports/2026-11-19/10-owner-payment.md on agent-reports; prior GitHub blob 9ba622ebb08e1a08697001d85b6010b1204d79f2, 39058 bytes. Direct CONNECT 403, authenticated API reads succeed. Entire existing blob preview shortened; prior bytes not yet locally verified. Keep the original intact and publish this create-only checkpoint, then attempt lossless canonical consolidation. Publication status follows exact-commit readback. publish_ack=REPORT_PUBLISH_RECOVERY_V1 (a9583516fd2e603320c771e32c170132bf0c53e9); continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1. RH=OPEN.

## A. Two adjacent prime discrepancies: a finite bound and a necessary condition for failure

`20261119-owner-1615-EST/HINGE-FINAL` | November 19, 2026. The assigned opposite product is below budget for every integer `2 <= B <= 27,761,484,110,184`, with **no good-history assumption**. At sufficiently large roots a violation would require at least `0.01 B log^2(B^2)` of signed contribution from an explicitly identified remainder of the actual zeta zeros. The full critical line, a shrinking strip on both sides, and a wider portion at the top of the height range cannot provide that contribution alone. The all-root bound for this product and the other three products are not proved. `HINGE1=PAPER_PROOF + FINITE_COMPUTATION; HINGE2=PAPER_PROOF (quantifier obstruction); HINGE3,4=PAPER_PROOF (proper-source restrictions); SELF_AUDIT; INDEPENDENT_REVIEW=PENDING; NOT_FORMALIZED; RH=OPEN; NO_NEW_GLOBAL_GAIN`. Claim prefix `20261119-owner-1615-EST/`.

## B. Objective and source

One C>=0 before all integers B>=2 must bound `|D_B-sqrt(2)| <= C B log B`, where `D_B=pi(B^2)-vfMidFinishedMass(B)`. Write `G(B)` for `|D_r|<=2r log r` at **every** integer 2<=r<B. The fixed wall is raw, not canonical. The compiled RH consumer retains `ClassicalVonKochRHCriterion`. Intake main `93398824812269526c1ac8c00f43c7ccfe142751`; closing main `2f0bb1f28d0ac386918ad7d1aaf683e2ccfd62de`. Between them only #1151's Nyman source/checks were added; authoritative AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`, contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`, raw seats `87a6654a4a4337b409fde69aa15d7264d8b721b6`, first bad `1163ae30b448b2fdd99fc4bfb4f13b36863a52a9`, quadrature `d4762a8bcce2acba597d1578b4846619cf143cf7`, canonical endpoint `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` are unchanged.

Set X=B^2, L=log X, U=X^(5/9), l(n)=1_prime(n) log n-1 on ALL positive integer sites, e(t)=theta(t)-floor(t). Put `I0=e(X/7)-e(X/10)`, `O0=e(X/10)-e(X/11)`, `a=1-1/sqrt(6)`, `d=a-1/sqrt(7)`, `c=ad/5`. These are adjacent half-open intervals, including integer endpoints on the right only. In EXCHANGE3's five-sector partition above, `I1=I-I0`, `O1=O-O0` where U<X/11; `-IO=sum_{i,j in {0,1}} -Ii Oj` with no duplication. At a sufficiently large *first* crossing the previous paper implication gives `-IO >= ad X L^4-O(X L^3)`. The present results do not assume a terminal crossing. Restoring the five squares and all ten pairs recovers e(X)^2; the original seat square is `(D_anchor-sum q)^2` with its anchor, diagonals and both cross orientations, then `-2 sqrt(2) D_B+2` to center. Neither this prime projection nor its spectral square is #915's clipped denominator, an NNS covariance theorem, or a transfer to native square M. The Euler route still requires the virtual d>X terms and compensation.

## C. Hypothesis

Can the common endpoint X/10 of two historical intervals prevent opposition at cost `(-I0 O0)_+ > c X L^4`? Two distinct tests: an independently fixed range for the actual prime sums, and a signed necessary condition outside a near-line part of the exact explicit formula. No independence of intervals, factors, or zero ordinates is assumed.

## D. Derivations

**HINGE1: fixed range.** Johnston, *Improving bounds on prime counting functions by partial verification of the Riemann hypothesis*, arXiv:2109.02249, Thm 3.2 (3.4), Cor 3.3, gives `|theta(y)-y| <= sqrt(y) log^2(y)/(8 pi)` for 599<=y<=1.101e26 unconditionally using Platt-Trudgian, arXiv:2004.09765. For B>=82 and B^2<=7*1.101e26 all three y=X/j satisfy this range. Within one difference the two fractional parts cost <1, not one per prime. Consequently `|I0 O0|/(X L^4)` is at most the product of `(1/sqrt(7)+1/sqrt(10))/(8 pi)+1/(B L^2)` and `(1/sqrt(10)+1/sqrt(11))/(8 pi)+1/(B L^2)`. This decreases in B and is <0.000688 at 82, whereas c>0.025301792538. The integer square root of 7*1.101e26 is 27761484110184. The positive-part check below covers 2..81. This is an application of an existing finite-height theorem, not a zero computation or a prime census to that endpoint. The older CL-20261014-8..11 application to the whole raw wall is a different statement.

**HINGE2: why an eventual history test does not close induction.** Literally `exists B0, forall B>=B0, G(B) -> (-I0 O0)_+ <= c X L^4` has a classical proof. If a first raw failure r exists, take B0=r+1: the antecedent is always false. Otherwise every raw wall holds; restoring the fixed canonical phase gives the canonical bound, hence RH by the classical von Koch criterion and the repository bridge. Under RH Johnston Thm 3.2 can be applied at arbitrary height to every y>=599, and the preceding estimate applies to every B>=82. This dichotomy gives **no usable B0** at a putative first crossing. A single failure at a prescribed B can falsify a fixed-base claim, not the bare eventual implication. Request the implication for every B beyond an independently fixed and covered base, with no terminal premise. Neither branch of the dichotomy proves the repaired assignment.

**HINGE3: preserve the common endpoint in the zeros.** Let `J=I0-O0`, `V0=I0+O0`; exactly `-4 I0 O0=J^2-V0^2`. For T=B/8 set `P(s)=7^(-s)-2*10^(-s)+11^(-s)` and `F_A=sum_{rho in A, 0<|gamma|<=T} X^rho P(rho)/rho`, with nontrivial zeros counted with multiplicity and both signs. Conjugation-closed sums are real. Cully-Hugill/Johnston, arXiv:2111.10001v5, Thm 1.2 (alpha=1/2), applies at this **same sharp height** to each y=X/j for all sufficiently large B: `max(51,log y)<T<(sqrt(y)-2)/2` since `1/8<1/(2 sqrt(11))`. Its error is O(y log y/T). In `e(y)=(psi(y)-y)-sum_{k>=2,p^k<=y}log p+{y}`, the prime-power sum is O(sqrt(y)) by Chebyshev. Thus `J=-F_all+O(BL)`, including floors, squares, higher powers and endpoints.

Write `h=|beta-1/2| L`, `N={h<=3}`, `v=(1/sqrt(7),-2/sqrt(10),1/sqrt(11))`, `A(gamma)=sum_{j=7,10,11} v_j j^(-i gamma)`. On N replace `j^(-(beta-1/2))` by `1+O(1/L)` and `1/rho` by `1/(i gamma)+O(1/gamma^2)` at a total cost O(BL). Pairing beta with 1-beta at the SAME ordinate averages `exp((beta-1/2)L)` to `cosh((beta-1/2)L)`; line zeros are counted once. Only after taking absolute values enlarge N to all ordinates. For `W=sum 1/|gamma|=(log T)^2/(2 pi)+O(log T)=L^2/(8 pi)+O(L)` by zero counting, let E be the normalized reciprocal-height mean on all zeros through T. Ford-Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*, Lemmas 1,2 and (3.8), give `sum_{0<gamma<=t} r^(i gamma)=O_r(t)` for each fixed rational r!=1 (use conjugation for r<1). Partial summation makes each such weighted normalized mean O(1/log T). The bases 7,10,11 are multiplicatively independent by unique factorization. Thus the only constant phases in the fourth moment come from equal multisets.

Put `m=sum v_j^2`, `s=sqrt(m)`, `D=sum |v_j|`, `tau=2 sum_{j<k} v_j^2 v_k^2`. Expansion gives `E|A|^2=m+O(1/log T)` and `E(|A|^2-m)^2=tau+O(1/log T)`. Since `2s|A|=|A|^2+m-(|A|-s)^2` and `(|A|-s)^2 >= (|A|^2-m)^2/(D+s)^2`, we obtain `E|A| <= K+O(1/log T)`, `K=s-tau/(2s(D+s)^2) < 0.765991570800`. Consequently `|F_N| <= k B L^2+O(BL)`, `k=cosh(3)K/(8 pi)<0.306840553374`, strictly below `2 sqrt(c)>0.318130743804`. This is a deterministic fourth-moment restriction for this joint kernel, not an equidistribution assumption about a selected subset.

**HINGE4: remove a further high-ordinate region.** Disjoint from N, let `S={T/L^2<|gamma|<=T, 3<h<=(9/8)log L}`. Its sum of absolute contributions is `O(B L^(127/64) log L)=o(BL^2)`. Indeed Ford-Zaharescu Lemma 2 gives `N(1/2+u,t) << t^(1-u/4) log t` uniformly for 0<=u<=1/2. Reflect the negative deviations. In a dyadic band `Y<|gamma|<=2Y` with `T/(2L^2)<=Y<=T`, for `0<=v<=(9/8)log L` the reciprocal mass with h>=v is `<< L exp(-v/8)`: divide the count at 2Y by Y and use `log(2Y)=L/2+O(log L)`, whose exponent correction is O((log L)^2/L). Each summand is `<< B exp(h)/|gamma|`. Integrate `exp(v)` against the tail up to H=(9/8)log L; this costs `O(L exp(7H/8))=O(L^(127/64))` per band before the factor B. There are O(log L) bands. No distribution assumption in height or real part.

## E. Quantitative consequence

Let R be the other zeros in the same truncation (neither N nor S). For every sufficiently large integer B violating the product budget, sigma=sign(J) is nonzero and

`-sigma F_R >= sqrt(4 c B^2 L^4+V0^2) - (k+o(1)) B L^2 >= 0.01 B L^2`.

Indeed the product identity forces the first square root below |J|; subtract the two priced regions and the explicit-formula error with their actual signs. The constant gap `2 sqrt(c)-k` exceeds 0.011290190430. Reflection implies a zero with `0<gamma<=B/8` and `beta>1/2+3/L`; mere existence is weaker than the signed lower bound. No numerical onset is asserted for this inverse theorem. It does not prove that the residual sum is small, a wall fails, or any zero is actually off the line.

## F. Falsification and replication

Direct once-only prime products minus integer site counts and independent quotient-block sums agree in outward intervals. Sieve flags were matched to trial division, log bounds used correctly rounded Decimal.ln with neighboring representables, then integer outward arithmetic on 42- and 54-place grids. Exact U uses `u^9<=X^5<(u+1)^9`; raw F starts at F_2=0 and advances by `(2r+1)/log(r^2+r+1/2)`. Both runs checked the product for B=2..128, every raw wall there (minimum margin at B=2 in [0.77258872,0.77258873]), and the five diagonals, ten pairs and four I/O products for B=16..128. Ordered as 00,01,10,11 the (+,-,zero) counts are (71,42,0), (38,74,1), (57,56,0), (63,49,1). The maximum positive product divided by X L^4 in each cell is in `[m,m+1]*10^-12`, with (B,m)=(21,17144669),(54,13671260),(121,11511645),(51,38142781). In particular -I0 O0 is negative at 16 and positive at 17: both universal fixed-sign shortcuts are REFUTED; the size bound is not. Checker SHA-256 `e6a9631a248cf42fc2a167cd8040292105c2e367db5749103cb8ecdcffe9ba38`. No finite observation extrapolated.

## G. Interpretation

The shared endpoint has coefficient -2 in the spectral kernel, not two independent draws. Its interaction with denominators 7 and 11 yields a strict variance cost via the fourth moment. A hypothetical large opposition must draw signed strength from farther off the critical line, and even some of the high-ordinate zeros outside the strip cannot supply it. This is a necessary condition for one actual product, not global cancellation.

## H. Competing mechanisms

Keep the fixed-base two-interval approach and the signed spectral remainder as distinct tests. Retire an unanchored eventual historical implication as an induction supplier; keep its scope separate from a pointwise theorem. Ordinary all-endpoint triangles are useful only where the cited finite-height theorem supplies their constants. The three other products, all cross terms and all nine independent routes remain live; no departure from the half-line campaign is proposed.

## I. Specialist handoffs

Coordinator: replace the quantifier in EXCHANGE-J/JET by a verifiable fixed-base statement; prioritize the signed remainder over another routine census. Analytic: test the real-part/height sector in J below at the common T, preserving P and conjugate pairs. Wheel: look for a signed inequality on (I1,O1) that retains shared prime sites and HALL's {638,682}->462 obstruction (B=20,X=735 in its own carrier). Census: independently reconstruct the four recorded maxima and the sign switch before extending; a differing certified interval falsifies the corresponding finite entry. Referee: audit the dichotomy, quartet reflection, fourth-moment normalization, and uniform dyadic density error. Lean Verification: after independent review, the fixed-constant product algebra and finite integer cutoff are formalizable; neither the literature bridge nor the global residual is claimed formalized. These are report handoffs, not agent launches or PR requests.

## J. First independently missing lemma

Try to prove, uniformly along integer squares with no history or crossing assumed, `F_A=o(B L^2)` for just `T/2<|gamma|<=T`, `beta in [3/4,4/5] union [1/5,1/4]`, with the same signed P and both signs of gamma. This proper reflected sector is disjoint from the priced regions eventually. It tests phase cancellation beyond the available absolute density estimate, does not rephrase the product, and would not suffice alone. For the induction actually needed, prove `G(B) -> (-I0 O0)_+<=c X L^4` for every B beyond the explicit product range (or a different independently covered base), then pay the other three and certify the finite **wall** base and the EXCHANGE3 error onset. A finite product range is not a finite wall certificate.

## K. Continuation and publication record

The eight canonical paths for seven roles and all relevant new recovery sections were checked at intake `a4ed3934210ee670753d4dfbb8065b138960eee1` after Owner's consumed watermark `4b1a75f41071abd98d4dec2627a57e799f8ec847` (14 commits, 14 changed paths). TODAY=AVAILABLE for all seven; YESTERDAY=CARRY_FORWARD from November 18 as recorded above, including PHASE recovery and the separately verified #1149 evidence, not an unpublished BG run. Today: Coordinator RIDGE/manual OBS/JET, identical latest mirrors `6790b8672ac80f6f3a36ca115929cf19f499cfb4` (JET4 H=12 rejects inclusion, not sparse overlap); Owner AR/EXCHANGE previous blob `9ba622ebb08e1a08697001d85b6010b1204d79f2`; Analytic ARC/BAND `6aa2d6f87f3ff23e0e291087c45cda38e43de1a5`; Wheel EX/HALL `3a330c46532975576cc33f9fe55ed3327727345e`; Census FOLD/CROSS `72ae7640849805c181dca1d03ef5dc32447a6f09` (H=12 mixed signs, H=126 not dyadic); Referee PRISM/LENS `8eff846f154c048fe39ad44ff77b63e90db510f9` (scoped EXCHANGE1 check, no blanket EXCHANGE3 acceptance); Lean EXTREMA/RAMP/PRIME-WITNESS `0b8150d88136351860938530a24be262c6300ba5`. External inbox `7d63d434690d00dffce9c90335d41c4f62d85798`, no new delta; unit cofactor/root boundary and the all-root versus first-bad distinction retained. Older abbreviated archives retain the earlier narrow CONTINUITY_UNVERIFIED qualification.

Baseline #1119: `native_mertens_near_uniform_window_error_closed`, blob `f629db1b2b65d6ec042ac9432397d4b6316200c6`, exact head/job recorded above; `7/8-7/(64 N_pack)` with every positive loss, no new exponent. #1149 period energy plus bias and #1150 tested head `0a7d02dabffbb30d247120dd803d5b17afccfcd4` (merged 14:06:44Z) pay no growing-tail bound. #1151 was open at intake and merged at 21:19:58Z, tested `5fdbbe89dc595a5b14b647e8cf3f9faaf00cfa00`, dedicated hosted 44590158125/135793679265; its seven finite Nyman facts only, no full weighted energy. No open/draft PR at closing check. No Owner source edit, local Lean claim, PR or schedule action.

Continuation capsule: actual prime seats -> prior raw walls and complete EXCHANGE3 -> fixed-base four-product contradiction with slack -> all raw roots -> restore phase and classical criterion. New payment: one finite product; two rigorous restrictions on its spectral source. Unpaid: signed off-strip mass, three other products, effective onset and complete finite wall base. Policy refs: half `96ad4439ec458af6168f7d9cb3eef5dde291d37c`, cross-route `e3ae4280438f591f1ffaddd754a1c3a6d35d0691`, continuity `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`, publication `a9583516fd2e603320c771e32c170132bf0c53e9`. Earlier checkpoint verified as an immutable own-role recovery at `34c1689406e360bf9de402923e30ddf2c6168bf0` (blob `14134c60f18abbb6f9437205a35aa86ba54d4673`, 2095 bytes); the complete prior canonical 39058 bytes were subsequently reconstructed and matched their live Git blob. Keep that immutable sibling, not a separate run. Authenticated Git publication only, no force and no second role's files. Final immutable receipt is reported after readback.
