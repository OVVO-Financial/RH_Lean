# Nyman tail: where a hypothetical bad zero must appear

## A. What changed mathematically?

For the original two-band Mobius coefficients, a zero to the right of 1/2 would force polynomial energy in one of two places: the middle before the last modulus, or a **signed sum over large Farey determinants** in a finite window after it. The diagonal, every sufficiently small determinant class, and the entire more distant infinite tail can be paid independently. This excludes an arithmetic configuration; it does not exclude the zero. Separately, the unresolved Census head **H=60 is below its stationary benchmark**, opposite to H=6,12,...,54. Neither one-sided comparison holds for every legal H at the support cutoff.

Invocation `20261118-coordinator-2309-EST/PHASE`; actual scheduled trigger 2026-11-18 23:09:00 EST (2026-11-19T04:09:00Z), America/New_York, RUN_ID_UNAVAILABLE. This continues CHECK, not a second launch. PHASE1/3/4: PAPER_PROOF, SELF_AUDIT, independent review pending, NOT_FORMALIZED. PHASE2: FINITE_COMPUTATION plus PHASE1 and Census's published finite prefix. NO_NEW_GLOBAL_UPPER_GAIN; VERIFIED_ETA=NONE; RH=OPEN.

## B. Current proof objective

Main `6e8bc42b828c7940c3d9137e4a3afa2e2840c5ba`; AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`; CURRENT_PROOF_CONTRACT `95566e37c8eaeb99ee680660df4f9d2e06ea5038`. The open `VFCanonicalSquareVonKochStatement` is one real C>=0 before all natural R>=2 with |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R. The compiled `riemannHypothesis_of_vfCanonicalSquare` explicitly takes `ClassicalVonKochRHCriterion`. No classical interface or missing upper bound is silently discharged.

The strongest inspected native comparator is #1119, `native_mertens_near_uniform_window_error_closed`: MertensGrowthAtMost(7/8-7/(64 N_pack)), with every positive exponent loss. The fixed slot count satisfies N_pack<=N_star for the older #1108 boundary 7/8-1/(48 N_star). Preserve the complete fine probe/error return and the Hecke-to-Mertens bridge; this is reused CI, not a new proof. No baseline exponent is used in PHASE. On the Euler route keep all virtual divisors in F_R-D_R and their compensation; on VF keep actual primes, phase and strict first-bad masks; on NNS keep the original Hecke coefficients and ordered interactions; on square blocks keep every shell and return. Period averaging loses output location. #1147/#1149 recover the full period covariance, not a typed identification with those other carriers or the physical tail.

## C. Competing mechanisms

| Route | Independent input and test | Disposition and consumer |
|---|---|---|
| NYMAN: original location-weighted energy | The congruence for a prescribed determinant bounds how many modes can hit a given row. PHASE3 isolates the remaining signed, growing-determinant bilinear sum. Test it on the original coefficients, with the middle restored. | ACTIVE_SUPPORT: a falsifiable inverse theorem, not an upper estimate. One common unbounded sequence with subpower **whole** energy would exclude every off-line zero by D. |
| MU-LIFT: original strict prefix | For the ordered squarefree factorization counts, obtain a signed saving **across different products**, with the preceding lift and boundary terms restored. LC disproves the within-product absolute shortcut. | Bounded feasibility only. For fixed k=2 and r<2, an eventual gain E_M(B^2)<=G(B)E_M(B)^r with log G(B)=o(log B) on a sequence B tending to infinity is itself equivalent to Mertens-half (#1135); do not assume it. E_M(B)=max_{1<=n<B} abs(M(n))/sqrt(n). |
| VF/SAT/JOH: original first bad | Seek a radial-amplitude-dependent ancestry restriction on the once-anchored signed square; GP's genuinely good windows are controls against sign/length-only selection. | Retain as a distinct conditional contradiction route: exclude a first bad for one fixed constant after a verified base. No such exclusion, and no general transfer from Nyman. |

Preserve VF-LOW, SAT, CODIV, OAI-NNS, JOH, FINITE-AC, CORR4, MU-LIFT and NYMAN. Park OAI geometry-only restarts: 47/54 LOW floor, actual theta>3/5 coefficient gate and Re(s)>21/25 correction domain are not cleared by an initial gain. No change to the contract requested.

## D. Conceptual research and proof

**Carrier.** Throughout H>=6 is an integer multiple of six; N=H^2=6K, L=log H. Set q_k=log(N/max(H,k)), u=sum_{1<=k<=N}mu(k)q_k/k, v=2L+sum_{1<=k<=N}mu(k)q_k, I1=(3K,4K], I2=(5K,6K], s_i=sum_{k in Ii}1/k. Write alpha=(u-s2 v/K)/(s1-s2), z=v/K-alpha. For 2<=k<=N, c_k=(alpha 1_I1+z 1_I2-mu(k)q_k)/L. Keep squareful correction sites, both bands and k=1 in the solver. Define r(m)=1-sum c_k(m mod k)/k, w_m=1/[m(m+1)] for m>=1, T(s)=sum_{m>=s}w_m r(m)^2, E_H=T(1), P=lcm(2,...,N). The two moments are sum c_k/k=1 and sum c_k=3. Thus the literal periodic residual has zero mean, r(0)=1 and r(P-1-m)=-r(m); the original flat-head identity gives r(1)=...=r(H)=0. Do not zero-extend at m=0. Both finite middle and infinite tail are part of E_H.

**PHASE1: a denominator-sensitive tail bound.** Put e(x)=exp(2 pi i x), and sum over reduced fractions lambda=a/q in (0,1), 2<=q<=N. The coefficient of e(m lambda) in r is A_lambda=b_q/(1-e(-lambda)), b_q=sum_{q|k}c_k/k. Indeed the nonzero DFT coefficient of m mod k is -1/(1-e(-lambda)) at its grid points; fold coincident modes before squaring. For each q, v_q=sum_{(a,q)=1}|A_{a/q}|^2=J2(q)b_q^2/12: Parseval for one centered sawtooth gives the sum of |1-e(-a/k)|^-2 over all nonzero residues as (k^2-1)/12; separate primitive orders by divisor inversion. V=sum v_q is the complete mean square, not a diagonal-only approximation. W=(3N/2)sum q v_q. With absolute constants, all legal H and every integer s>=1,

```
|T(s)-V/s| <= W/[s(s+1)].
```

Input: H. L. Montgomery and R. C. Vaughan, *The large sieve*, Mathematika 20 (1973), 119-134, Theorem 1 (1.6), DOI 10.1112/S0025579300004708. For arbitrary distinct points mod 1 with local separation delta_i, the dual inequality on every shifted length-J integer interval has bill sum_i (J+3/(2 delta_i))|A_i|^2. Each reduced a/q has delta_i>=1/(qN), including wraparound. Hence the window energy is <=JV+W. Its consecutive complement inside sufficiently many whole periods gives >=JV-W. Summation by parts using w_s and monotone differences gives PHASE1. This is a new application here, not a new large sieve or a uniform improvement on every coefficient vector. PV's earlier worst-spacing bill N^2 V remains available. In fact PV1's untouched gap (2N/3,5N/6] alone forces W>=N^3/(20736 L^2) for N>=20736. That is a lower bound on this certificate's error budget, not on an actual tail.

**PHASE2: a resolved physical cutoff.** Test fixed in advance: H=60, N=3600, prefix ending T=1048576, s=T+1. No change to the cutoff, constant or coefficients. Census ST commit `73412899c499828f16391b7c7b0e813fda0e6235` supplies the finite prefix N<m<=T in [0.001757256969,0.001757256970]; it was not recomputed here. Independent reconstruction of all coefficient and divisor classes by integer interval arithmetic gave:

| Quantity | Outward enclosure |
|---|---|
| V | [6.504482159456, 6.504482159457] |
| W | [29493174.677741528845, 29493174.677741528846] |
| T(1048577) | [0, 0.000033026962] |
| Full T(3601) | [0.001757256969, 0.001790283932] |
| V/3601 | [0.001806298850, 0.001806298851] |
| T(3601)-V/3601 | [-0.000049041882, -0.000016014919] |

The last row is evaluated before decimal display rounding. Opposite witness: at H=6 the ST prefix 37..664 alone exceeds V/37 by at least 662327/18500000000000. For H=6,12,...,54 the strict positive witnesses remain ST's. The negative at 60 is not evidence for arbitrarily many negative heads at the physical cutoff. No uniform constant-C comparison is refuted. Computation: grid 10^-d for d=32,48, integer outward operations; reduce each log to powers of 2 and 2 atanh(t), 0<=t<=1/3. After M=d+6 terms add [0,9/(4(2M+1)3^(2M+1))]. Compute mu and J2 by divisor subtraction, then b_q, v_q, W; intersect the lower remote bound with zero. Both grids agree as printed. Check both moments, all head residues and reflections, and the centered c2=1,c4=2 period [1,0,0,-1] versus uncentered c2=1. The finite prefix is an explicit external input, not verified by two new executions. Registration SHA256 `d8a6024d70e47fc8d0061c4ec37e41cf5b295105743bcb4f5912d29d64f2154d`; companion checker SHA256 `ea0d5a31482e3aebfe6bbf86090924ace8deb5d8ccc177b3a489f42db88480df`.

**PHASE3: a determinant exclusion and zero-forced alternative.** For distinct lambda=a/q, nu=b/k let d(lambda,nu)=qk||lambda-nu|| (circle distance), a positive integer. Set B=1+log N. For ANY finite set S of positive integers, and ANY interval of outputs I contained in m>N (including the infinite interval), the absolute size of its complete ordered cross contribution obeys

```
sum_{d(lambda,nu) in S} |A_lambda A_nu| sum_{m in I}w_m <= C |S| B^5.
```

Here and below C is absolute, before H, S and I. Proof: s1-s2>=1/20, s2<=1/5, |u|<=LB, |v|/K<=7L, so max |c_k|<=C B. Thus |b_q|<=C B^2/q and v_q<=C B^4 using J2(q)<=q^2. For fixed a/q and fixed d, every partner has a k congruent to +d or -d mod q; since a is invertible this leaves at most 2(floor(N/q)+1) denominators, counting the two signs separately. For a fixed sign and k there is at most one b mod k. This includes both orientations and circle wrap, and does not assume primitive partners are independent. Apply 2|xy|<=|x|^2+|y|^2 to the symmetric ordered graph. Its absolute pair mass per d is <=2 sum_q v_q(N/q+1)<=C N B^5; sum_{m>N}w_m=1/(N+1). In particular the same bound holds for the signed oscillatory contribution with kernel sum_I w_m e(m(lambda-nu)). This arithmetic counting bound, not the frequency change of coordinates, is the independent input.

For integer D>=1 let F_{>D} be the REAL ordered signed sum with this kernel on N<m<=H^3 and d>D, retaining A_lambda conjugate(A_nu). Let M_H=sum_{H<m<=N}w_m r(m)^2. The diagonal on that window is <=V/(N+1)=O(B^4). Also V<=C N B^4 and W<=C N^3 B^4, so PHASE1 gives T(H^3+1)<=C B^4. The exact split therefore yields

```
|E_H-M_H-F_{>D}| <= C(1+D) B^5.                         (*)
```

For each nontrivial zeta zero rho with 1/2<sigma=Re(rho)<1, put kappa=2sigma-1. The exact-head Mellin test gives E_H >= kappa (H+1)^kappa / |rho|^2. Indeed r(floor(1/x))=1-sum c_k({1/(kx)}-{1/x}/k); its Mellin value at rho is 1/rho since each basis transform is (k^-1-k^-rho) zeta(rho)/rho. This identity follows first by integration of floors in Re(s)>1 and then continuation to Re(s)>0. The residual vanishes for x>1/(H+1) up to endpoints, its L2 norm squared is E_H, and Cauchy-Schwarz gives the claim. Fix any 0<eta<kappa, D=floor(H^eta). Then (*) implies for all sufficiently large legal H

```
max(M_H, F_{>D}) >= kappa H^kappa/(4 |rho|^2).
```

This is a necessary alternative for a hypothetical zero, not a contradiction. The second quantity is signed, not an absolute bill. No H-dependent zero or post-hoc coefficient choices. A fixed-determinant mechanism cannot carry this obstruction by itself. A slow-growing class count and the independently paid remote tail are not all pairs. Direct terminal consumer: if on ONE unbounded legal sequence E_H<=C_eps H^eps for every eps>0 (constants before H), take eps<kappa to exclude every such zero, then use zeta symmetry. No converse for this prescribed taper is established. Controlling M_H+F on one fixed subpower strip would merely restate the missing scale bound modulo (*); an independent arithmetic estimate is required. Post-discovery finite check, distinct from the H=60 registration: N=2..30, 328918 nonempty determinant rows, plus four signed cutoff checks on the centered toy fixture.

**PHASE4: no eventually one-sided cutoffs, even for a single fixed head.** Put g(m)=r(m)^2-V and G(s)=sum_{0<=m<s}g(m), extended periodically. Reflection implies G(P-s)=-G(s) and mean G=0. With forward difference Delta, define the finite Fourier primitive B2(s)=sum_{lambda!=nu} A_lambda conjugate(A_nu)e(s(lambda-nu))/(e(lambda-nu)-1)^2. Then Delta^2 B2=g and Delta B2=G (zero means). The frequencies have circular separation delta>=N^-2. On either semicircle the j-th neighbor is at distance >=j delta, and |e(x)-1|>=4||x||. Therefore each inverse-square row sum is <=2 sum_{j>=1}(4j delta)^-2<=N^4/4. Symmetry and 2|xy|<=|y|^2+|x|^2 give sup |B2|<=N^4 V/4. Two summations by parts now give

```
|T(s)-V/s+G(s)w_s| <= N^4 V/[s(s+1)(s+2)]  (s>=1).
```

The first remainder is sum_{m>=s+1}G(m)(w_{m-1}-w_m); its absolute value is <=2 sup|B2| (w_s-w_{s+1}). Now G(1)=1-V, G(H+1)=1-(H+1)V, so one has magnitude >=HV/2; its reflection has opposite sign. V>0 since r(0)=1. Along the corresponding two residue classes mod P, s(s+1)(T(s)-V/s) tends to the opposite primitive values. Its limsup is >=HV/2 and its liminf <=-HV/2 for EVERY fixed legal H. On those classes s+2>4N^4/H suffices for signed magnitude >=HV/4. Such cutoffs can be enormous. This does not decide sign at s=N+1 across growing H. The theorem would be invalid for arbitrary uncentered repairs without rechecking reflection.

## E. Specialist findings and continuity

`agent-reports` intake `2457a0f73b97e6154d1ea65f4b8ea0ca3f1dc1cd`. Dated directories enumerated without a calendar cap. Table gives Nov 17 carry-forward, last consumed at the prior Coordinator watermark, then intervening actual Nov 18 publications (all times EST); SHAs are Nov 18 owned-file blobs at intake. The two Coordinator stems count once.

| Role/stem | Nov 17; prior Nov 18 | Newly consumed / last verified | Nov 18 blob |
|---|---|---|---|
| 00/90 Coordinator | DUAL 23:09; DAMP 07:10 | DAMP and its receipt; this run CHECK then PHASE | ee7b4ce6ff79ab0eaea4d8b74d95e3e78f398cb5 |
| 10 Owner | PC 16:15; AI | HC 08:09, GP 16:15 | a6345e177392d55db551650e8013581b89694623 |
| 20 Analytic | CP 17:11; PAIR | PV 09:09, LW 17:11 | 065a94a6eb8f69b51641011296efbce3f96c87f5 |
| 30 Wheel | PP 18:06; FD | PM 10:12, LC 18:06 | 669ba135d05503c1cead5f04106977ff66887ed6 |
| 40 Census | MR 19:00; PN | PS 11:00, ST 19:00 | 780b932540c38e61bb6f81f732e66c4c9b1180b0 |
| 50 Referee | PR 20:13; DP | FC 12:03; later publication unavailable | 91b57ce6a46693403cd8a5751c63aaf8335ab305 |
| 60 Lean | PROFILE 21:08; DUAL | VR 13:14; MEAN 21:08 via #1149 only | 2cd3263317a8afaae5e664f4b56d2c095059421c |

Nov 17 blobs in the same order: `125e55aa191083d9c0a982b6dc5a66267e4e4256`, `6516bf78b096471ccfd2fb8c215e94002544a594`, `d4bc53ac1b68f6dadabc4a04a2f5fc8c74f6625f`, `5c26771c0a266d5112e0b4a4b28aba0132e35ef7`, `587b0bb3dd66834a18610ab86174f285f81c4b04`, `103ee17307ac799e20bd4ce17d97ff96101a9e5b`, `ee9ed0ace763bf99fea5812490f9541653917938`. The later six substantive commits in specialist order are `de88250d67c3e2dcdf12231a196a089afcd49e01`, `a8fab7e4059ff06ac60a5d8e04d806986baba896`, `bb46e802de2bb540688821fd9dcfa3d00ddb946e`, `73412899c499828f16391b7c7b0e813fda0e6235`, `85220798b01156db6babe094a3a0a9aef8ede7b3`, `37f7fcdb18cd87747034f962f54d9dac13e103b1`.

HC/GP: conditional backward persistence is not exclusion. Both signs and all fixed-length nearly saturated subwindows occur at radially good genuine roots; not a counterexample to FirstBad-conditional payment. PV: complete top-gap variance lower and repair restrictions; LW: N^3/T^2 obstruction for enlarged moment-null repairs, not a lower bound for the prescribed coefficients. PM restores the top-prime matching orientations to the original endpoint; LC gives same Liouville sign at each product in the first error collar, but not across products. PS breaks a fixed phase sign at H=18. ST shows the mixed-band sign can reverse between complete periods and a physical window when alpha*z<0; this is a component, not the global sign. FC independently accepted DAMP1-4 and PV1-3 with scope, not PV4, PS, or this work. Its own N=p^5 absolute repair bill >=exp(-6)N^(3/5)log N/40 after pricing cells through p-2 is not a signed obstruction. VR/MEAN establish finite identities as in I.

External ledger `7d63d434690d00dffce9c90335d41c4f62d85798`: EXT-20261018-PNT-1 retains the c=1 prime-discrepancy term; EXT-20261014-5 is an unconditional all-root limsup, not a first-bad exclusion. No new external execution inferred. Named handoffs reconciled; CONTINUITY_UNVERIFIED for byte-complete historical files: authenticated full blob responses were shortened in-session, supplemented by immutable commit diffs and source ranges. Nov 13-14 and earlier known Nov 15 role gaps remain NO_VERIFIED_REPORT. Later Referee text is NOT_PUBLISHED per #1148; Lean MEAN daily handoff PENDING despite its verified merge. Do not infer other missing launches.

## F. Mathematical bottlenecks

NYMAN: bound the finite middle or genuinely large-determinant **signed** correlations with complementary ranges paid on the same unbounded sequence. Neither the all-period mean, (*) nor infinitely many distant signs supplies that upper bound. MU-LIFT: control ordered terms of different products jointly with the preceding prefix, not merely a coefficientwise error. VF: find a radial restriction that distinguishes an actual first bad from GP's good saturated windows on the complete once-counted history.

## G. Strategy decisions

Retire both universal constant-one stationary signs and any eventual one-sided-cutoff proof. Retain a constant-C upper question and original signed selection; stop spending endpoint effort on finitely many determinant values. Keep DAMP absolute inversion and finite-cell repairs parked; signed DAMP prefix control is target-equivalent at the half exponent. No new renewable exponent map, global upper bound, formal proof assignment or priority amendment.

## H. Next specialist assignments

| Specialist | Decisive question and falsifier |
|---|---|
| Owner Payment | Starting at HC/GP's original D_a and full interval square, identify an amplitude-sensitive inequality forced by FirstBad. Restore the single historical anchor and every orientation. If it also predicts exclusion for GP's good windows, reject it. |
| Analytic Type II | In N<m<=H^3, group the original folded coefficients by growing determinant and retain their phases. Seek an independently bounded nontrivial band and its complement; document a loss at H<m<=N separately. An estimate for arbitrary bounded repairs, or a renamed assumption on the entire F, does not qualify. |
| Finite Wheel | On b^2<=n<2b^2 with b the first squarefree >=B, test a signed pairing between distinct products in LC's ordered counts. Include shared primes, the preceding lift and the 2b^2 endpoint when reached. Return a proved uncancelled remainder or a counterfamily, not a bound for a single product. |
| Prime Census | At exactly H=60 and the same cutoff, independently reconstruct b_q and W, compare a literal small-denominator Fourier/CRT calculation, and verify ST's prefix provenance. A sign mismatch, missing squareful band site or failure of either moment invalidates the PHASE2 certificate. No larger census requested. |
| Adversarial Referee | Audit PHASE1-4: dual normalization, both determinant orientations and wrap, adjoint coefficient, lower complement, both Abel boundary signs, Mellin normalization, and separate quantifiers. Use nonzero bias and an incorrect r(0)=0 as negative controls. Return first failure or independent acceptance by claim. |
| Lean Verification | No new PHASE PR before independent acceptance and a named consumer. Reuse #1147/#1149; no repair is pending. If PHASE3 is accepted, check for an existing reduced-fraction fixed-d degree lemma before considering its exact finite multiplicity statement; no hypothetical zero/target assumption inside the count. |

## I. Lean and PR status

Live open PR list empty, including drafts. #1145/#1146 merged finite lower-conditioning results (merges `56590f2075e01d8d7ff2c792d8d41730b8b6dcf0`, `935840aec9b1fcbc66fe4e0164061d661a8ca3b1`). #1147 branch `agent/lean-verification/20261118-variance-repair`, raw `e77d049ff83809c13c52e3d90922f34ed032efac`, run/job `44371410914/135038879279`: five public standard-axiom closures; merge `a892281ae5e384fe135ace941e43f0021372fd53` at 21:11:56 EST. #1148 reporting-only merge `77dfc94ec71b89998a478067fb5693c9be9efc11`. #1149 branch `agent/lean-verification/20261118-nyman-period-mean`, raw `1095bfa3c314ff048160fc14e67dfc74106f5d7a`, run/job `44446879526/135301058077`, human-merged to current main at 22:01:54 EST. Four raw-head closure sizes 265/337/385/424; standard terminal axioms propext, Classical.choice, Quot.sound. Pinned Lean 4.34.1, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Exact jobs inspected, not rerun. #1119 raw `77ee815846d6d534c866f0752aa33b84c385610a`, run/job `42552018910/128949473700`.

PROVED_IN_LEAN at tested heads: `nyman_covariance_divisor_squares` and same-support repair; `nyman_period_residual_energy` gives P*(bias^2+V) for a common period, not a weighted estimate. Source blobs: flat `2d23721027ecc44e85b7add02fc632b482f03352`, high `2da630c1d5fb9302e2097ec1e170cf41c2b40609`, repair `92608fc013c26102ac12250558a850209028e6d8`, mean `e005dc717cd3af6b8697d6517acf6516987d3a7e`, canonical `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`, native closure `f629db1b2b65d6ec042ac9432397d4b6316200c6`. No local Lean, new CI, proof branch, PR, merge, schedule edit or agent launch.

## J. Next-run resume and publication

Resume at PHASE3 (*): independent fixed-d degree audit, then growing-determinant signed correlation versus the true middle. PHASE2 settles only ST's H=60. PHASE4 fixes H and varies the cutoff. Distinguish all three quantifiers. STATUS=ACTIVE_SUPPORT; direct terminal as in D; no renewal, no changed source. The highest-value next arithmetic question is whether the large-determinant alternative has an independently provable cancellation law at physical output locations.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1; finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1; high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1. Policy blobs respectively: half `96ad4439ec458af6168f7d9cb3eef5dde291d37c`, cross `e3ae4280438f591f1ffaddd754a1c3a6d35d0691`, continuity `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`, publication `a9583516fd2e603320c771e32c170132bf0c53e9`.

Intended canonical paths `research/agent_reports/2026-11-18/{00-coordinator-am,90-coordinator-pm}.md`; original blob shared `ee7b4ce6ff79ab0eaea4d8b74d95e3e78f398cb5`, 55288 bytes (provider metadata; full old bytes not locally verified). Direct Git tunnel HTTP 403, authenticated Git data available. Canonical replacement is unsafe. CHECK pair was read back at `654bbf601526388c671d88bd56e3fafcbf53ec53`, blob `8fbab91ec28f0d991c46d0731ec9da6c08d30d56`, 2061 bytes. This full substantive section is a separate create-only pair at the same two stems with suffix `.recovery-20261119T040900Z-c2309-phase.md`, not an append or another invocation. Prepublication head is the CHECK commit. Use live-head guard, no force; on conflict refetch and reconcile once. CANONICAL=NOT_UPDATED. This immutable body does not certify its own publication; the external exact-commit receipt governs. Consolidate these unique sections once only if both entire canonical prefixes can later be verified.
