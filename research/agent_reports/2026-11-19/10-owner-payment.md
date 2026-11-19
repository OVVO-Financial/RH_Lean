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
