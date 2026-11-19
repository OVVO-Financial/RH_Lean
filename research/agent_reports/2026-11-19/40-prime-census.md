# Prime Census Laboratory | November 19, 2026

## Opening checkpoint: which of the two Nyman layers supplies the sign?

`20261119-census-0311-EST/FOLD-CHECK`. Actual scheduled trigger 2026-11-19 03:11:02 EST (08:11:02Z), America/New_York; RUN_ID_UNAVAILABLE. PARTIAL, no result claimed. Main `6e8bc42b828c7940c3d9137e4a3afa2e2840c5ba`, AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`, contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`, reports intake `6b046d6824e7b1e9cad9e96da901f6f795c7b2b1`. No open/draft PR; #1147 and #1149 are merged period identities, #1148 changes publication only.

Pre-register on the prescribed two-band coefficients, H a positive multiple of 6, N=H^2. In Analytic ARC5's second box (1/N,2/N), retain both raw numerator layers, even denominators, both corrections, the conjugate, and both ordered orientations. Test X12<=0 at every legal H=6,12,...,96 and on the fixed dyadic subfamily therein; identify the first positive, or report none. Compare with exactly equal frequencies l=2k, distinguish the unpaid off-line pairs from the exact arithmetic overlap, and recombine the two self-energies and cross. Rival: the coincidence is negative on account of mu(2k), while the complete sign need not be. A finite pass does not prove either sign or a subpower estimate. Independently check ARC's H=6 before extending. For Coordinator PHASE2 use exactly H=60, reconstruct folded coefficients, period energy and its denominator-weighted moment, check a small CRT/DFT fixture and the provenance of ST's prefix through 1048576. Do not enlarge that tail census. Restore the physical middle, all other boxes and the infinite tail in the endpoint discussion.

Intake since Census ST: separate Lean #1149 evidence; Coordinator PHASE; Owner AR; Analytic ARC; Wheel EX. Referee FC has not reviewed them. On November 19 Owner, Analytic and Wheel are published; Coordinator, Referee and Lean TODAY=PENDING / YESTERDAY=CARRY_FORWARD. `half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1`. Canonical path absent at intake. Direct Git tunnel HTTP 403; use authenticated Contents, compare whole bytes, then read by commit. No new Lean, exponent, or RH claim.

---

## A. The first positive cross is at H=126

`20261119-census-0311-EST/FOLD-FINAL`; final synthesis after 03:34 EST, same invocation as opening. **FOLD1 / REFUTED:** the cross between the two numerator layers in ARC5's second Nyman box is not nonpositive at every admissible head. At H=126, N=15876, it lies in **[0.0000002826456880, 0.0000002826456881]**. All 20 smaller positive multiples of six have strictly negative cross. The equal-frequency pairs still cancel; the unequal-frequency pairs more than pay for them. In particular it is unsafe to discard this cross when forming a global upper bound. This is not a counterexample on the fixed dyadic family or to a subpower upper bound, an actual first-bad predicate, or RH.

The hidden variable is the reduced ratio of the original denominators, not parity alone. At this witness all primitive ratios of height at most H together are still negative; larger heights account for the reversal. FOLD2 gives opposite limiting signs on two explicit ratios. FOLD3 retains both signed factors to bound a growing range of heights. Both are paper arguments on this box, not a new global Mertens exponent.

## B. Governing source and return

Main and instruction SHAs are in the checkpoint; main rechecked unchanged. `VFCanonicalSquareVonKochStatement` asks for one real C>=0 for every natural R>=2 with `|pi(R^2)-vfMidFinishedMass(R)-sqrt(2)|<=C R log R`. Its named RH consumer also takes `ClassicalVonKochRHCriterion`. The governing half directive admits the direct Nyman/Mellin endpoint; this is a bounded feasibility audit, not a change of campaign.

Starting theorem: #1119 `native_mertens_near_uniform_window_error_closed`, b0=7/8-7/(64 N_pack) with **every positive loss**; use fixed beta=7/8 by spending part of the strict gap. Its fixed-slot LOW/HIGH/principal, positive-error, compensated endpoint and native Hecke-to-Mertens return are not new assumptions. N_pack=ceil(max(1,1/(6 ell)))+2 <= N_star=ceil(max(1,1/(3 ell)))+2 for ell>0; compare #1108's 7/8-1/(48 N_star). Do not take an estimate at b0 with zero loss.

Lean source blobs: canonical `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`; flat taper and exact head `2d23721027ecc44e85b7add02fc632b482f03352`; residual `2da630c1d5fb9302e2097ec1e170cf41c2b40609`; variance `92608fc013c26102ac12250558a850209028e6d8`; period cells `0a506393f45a2e7882f39ae5c17a84505c97b1d5`; period mean `e005dc717cd3af6b8697d6517acf6516987d3a7e`; #1119 source `f629db1b2b65d6ec042ac9432397d4b6316200c6`. Checked hosted CI heads and run/job: #1119 `77ee815846d6d534c866f0752aa33b84c385610a` 42552018910/128949473700; #1147 `e77d049ff83809c13c52e3d90922f34ed032efac` 44371410914/135038879279; #1149 `1095bfa3c314ff048160fc14e67dfc74106f5d7a` 44446879526/135301058077 (four audited dependency counts 265,337,385,424; only propext/Classical.choice/Quot.sound). The last two give period identities, not physical tail control. No open/draft PR at intake; no new Lean run or formalization.

## C-D. Competing hypotheses and literal carrier

Can a negative equal-frequency contribution force a negative full cross, or do different primitive ratios reinforce? The discriminator was X itself, not the number of opposite signs. H ranges over positive multiples of 6, N=H^2=6K, L=log H. Put p(k)=log(N/max(H,k)), U=sum(mu(k)p(k)/k), V0=2L+sum(mu(k)p(k)), both sums over 1..N including the unit. Let I1=(3K,4K], I2=(5K,6K], s_i=sum_{k in Ii}1/k, a=(U-s2 V0/K)/(s1-s2), z=V0/K-a. For 2<=k<=N:

```text
c(k) = (a 1_I1(k) + z 1_I2(k) - mu(k)p(k))/L
r(m) = 1 - sum c(k)(m mod k)/k;   E_H = sum_{m>=1} r(m)^2/[m(m+1)]
A_j(k) = c(k)/[k(1-exp(-2 pi i j/k))];   delta=1/N
P_j(x,u) = sum_{x<j/k<=x+u} A_j(k)
X = 2N Re integral_{delta<x<2delta, 0<u<delta} P_1 conjugate(P_2) dx du.
```

Both band moments sum c(k)/k=1 and sum c(k)=3, r(0)=1, and r(1)..r(H)=0. These are prescribed coefficients, not arbitrary moment-null perturbations. With t=N/k, s=2N/l the cross is `N^-1 sum Re(A_1(k) conjugate(A_2(l))) w(t,s)`, where `w=[1+min(t,2)-max(t,s)]_+^2` on 1<=t<=3, 2<=s<=3, zero outside. It is twice the exact area of windows containing both sites in scaled coordinates. Positive area iff `k<N, 3k>N, 3l>2N, N|l-2k|<kl` on the original domain; hence k<l<3k. Equal frequencies l=2k enter twice by orientation; no physical occurrence or squareful correction is deleted. Self-energies Q11,Q22 use N, not 2N.

## E-F. Checked extrema and the sign reversal

Primary: all 16 heads H=6,12,...,96 negative at two precisions. Most negative H=6 (-54.213309 in units of 1e-6); closest to zero H=48 (-0.326569). Unequal frequencies alone are positive first at H=12, in [4.309235,4.309236] in these units, also at 30,48,96. Registered extension: H=102,108,...,192, stopping at the first positive, plus 192 regardless. H=102,108,114,120 negative; H=114 is closest to zero among the 20 earlier heads. The six tested H=6*2^j, 0<=j<=5, are negative, including X(192) in [-0.0000022774301025,-0.0000022774301024]. No claim about the unexamined intervening heads above 126.

| H=126 term | Outward enclosure, original units |
|---|---:|
| Coincident D (l=2k) | [-0.0000012734259907,-0.0000012734259906] |
| Unequal, l even | [0.0000012586428586,0.0000012586428587] |
| Unequal, l odd | [0.0000002974288201,0.0000002974288202] |
| All unequal | [0.0000015560716787,0.0000015560716788] |
| X | [0.0000002826456880,0.0000002826456881] |
| Q11; Q22 | [0.000017620013,0.000017620014]; [0.000000829846,0.000000829847] |
| Full second box Q11+Q22+X | [0.000018732504,0.000018732505] |

Post-hoc attribution, not a new registration: write k=dg,l=eg with gcd(d,e)=1; height is e=l/gcd(k,l), not a Farey determinant. Among 32,999,304 positive-area pairs, the 185,736 with e<=126 give [-0.0000007014577713,-0.0000007014577712]; e>126 gives [0.0000009841034593,0.0000009841034594] by exact complement. Counts include zero-coefficient sites. Even unequal pairs almost offset D but do not suffice without the odd part. At H=114 the odd contribution instead has negative sign. No averaging sign rule follows.

## G-H. Fixed primitive ratios explain opposite signs

**FOLD2 / PAPER_PROOF; independent review PENDING.** Write X_(d,e) for the full contribution with that fixed primitive ratio. For fixed coprime positive d,e, as admissible H tends to infinity,

```text
L^2 X_(d,e) -> mu(d)mu(e) rho_(de)/(8 pi^2) * integral_0^(1/max(d,e))
    w(1/(dy),2/(ey)) log(1/(dy)) log(1/(ey)) dy,
rho_m = (6/pi^2) product_{p|m} p/(p+1).
```

The integral is positive exactly for 1<e/d<3: necessity is the area test, and sufficiency holds on an interval just below y=1/e. For a squareful multiplier the limit is zero, not a finite vanishing assertion. The equal-frequency ratio 1:2 is eventually negative, while the unequal 2:3 is eventually positive. At H=192 their L^2-scaled values are [-0.000029852137,-0.000029852136] and [0.000004963000,0.000004963001]. Numerical quadrature of the limits gives -0.00002982025828 and +0.00000498365648 (diagnostic; signs follow analytically). Tested eight fixed ratios at H=102,108,120,192; 1:1 and 1:3 have no positive area, whereas the squareful 3:4 changes finite sign between 102 and 108.

Proof. M(x)=O(x^beta) from B. Partial summation gives sum_{n<=x}mu(n)/n=O(x^(beta-1)); its limiting constant is zero by the Euler product at s down to 1. U is the integral from H to N of this sum against dt/t; V0=2L+integral_H^N M(t)dt/t. Thus a,z=O(H^(beta-1)) since s1-s2>=1/20. On this box the two repairs in Lc are uniformly o(1), while 1/[k(1-exp(-2 pi i j/k))]=-i/(2 pi j)+O(1/k), j=1,2. The signed product of the bare Mobius factors is exactly mu(d)mu(e)mu(g)^2 1_{g coprime to de}. For fixed m, squarefree g coprime to m have count rho_m Y+O_m(sqrt Y), by the square-divisor expansion and finite inclusion-exclusion. Partial summation against the bounded-variation kernel with g/N=y gives the integral. No interchange between this limit and a growing sum of ratios.

## I. A signed bound for a growing height band

**FOLD3 / PAPER_PROOF; independent review PENDING.** Let B_Y be the sum of X_(d,e) over all primitive ratios with Y<e<=2Y, 1<=Y<=N, and put R=H^(beta-1). For each epsilon>0, uniformly in H,Y,

```text
L^2 |B_Y| <<_epsilon N^epsilon (Y^(2 beta-1) + R Y^beta + R^2 Y).
```

In particular at Y=H this is O_epsilon(H^(3/4+epsilon)), versus O(H) by absolute counting; likewise L^2 times the absolute signed total up to any 2<=J<=H is O_epsilon(N^epsilon J^(3/4)) by summing height bands (including a truncated band). This is power growth, not the sought subpower bound. It is not a restriction on all large Farey determinants.

Proof. Work before integrating the two scaled window indicators. Fix (x,u),g. The two window conditions are separate intervals for d and e, with d,e=O(Y) and N/(3Y)<=g<=N/Y whenever both occur. Open the coprimality filter as sum_{h|d,e}mu(h). Each remaining coordinate is independent: k=ghi or l=ghj. For T>=1 and Q<=O(N), `|sum_{i<=T,(i,Q)=1}mu(i)| <<_epsilon Q^epsilon T^beta`: convolve mu with the indicator of integers supported on primes dividing Q, and bound the positive Euler factor product (1-p^(-beta))^(-1) by O_epsilon(Q^epsilon), separating finitely many small primes. The bare sign is mu(ghi)=mu(gh)mu(i)1_{(i,gh)=1}, including a zero when gh is squareful. The log and complex reciprocal on each window have uniformly bounded size and total variation: k is between N/3 and N, j=1,2 fixed, and the imaginary reciprocal is -cot(pi j/k)/(2k). Partial summation therefore bounds either normalized coordinate sum by O_epsilon(N^epsilon (Y/h)^beta + R Y/h), h<=2Y. Both actual repairs remain in the second term even if mu(gh)=0. Multiply the two estimates, sum over h (2beta,1+beta,2 all exceed 1), allow smaller internal epsilons, and use at most N/Y choices of g and the original 2/N area scaling. This proves the bound, including sharp or truncated e intervals. Independent exact occurrence-map test of this rearrangement: 600 endpoint/window/height maps at H=6,12,18, with 9,140 admitted occurrences across tests, compared coefficient by coefficient. The test is not the proof.

## J. Physical H=60 check and the endpoint

**FOLD4 / FINITE_COMPUTATION with PHASE1's paper tail inequality.** Use exactly H=60, N=3600; b_q=sum_{q|k}c(k)/k, v_q=J_2(q)b_q^2/12 for q>=2, V=sum v_q, W=(3N/2)sum q v_q. Montgomery and Vaughan, *The large sieve*, Mathematika 20 (1973), Theorem 1 (1.6), DOI 10.1112/S0025579300004708: dual local-spacing bound on a length-J consecutive block gives <=JV+W since each reduced a/q has spacing >=1/(qN). Complement in whole periods gives the lower side; Abel then gives `|T(s)-V/s|<=W/[s(s+1)]` for T(s)=sum_{m>=s}r(m)^2/[m(m+1)]. This is not the identity T(s)=V/s.

| H=60 measurement | Outward enclosure |
|---|---:|
| V; W | [6.50448215945687,6.50448215945688]; [29493174.677741528845,29493174.677741528846] |
| Physical middle 61..3600 | [0.008014074183,0.008014074184] |
| Independently recomputed 3601..1048576 | [0.001757256969,0.001757256970] |
| Remaining tail from 1048577 | [0,0.000033026962] |
| T(3601); T(3601)-V/3601 | [0.001757256969,0.001790283931]; [-0.000049041881,-0.000016014919] |
| Entire physical E_60 | [0.009771331153,0.009804358115] |

Independent ordered gcd double sums give V=6.504482159456876 and W=29493174.67774152 (binary64). Conditional CRT means q=2..8 give the primitive energies by subtracting proper divisors; complex DFT coefficient error <=1.26e-16 independently. Example b_6 in [-0.034759117088,-0.034759117087]. The signed floor-jump reconstruction uses all m through 1048576 with a single conservative upper allowance for coefficient rounding; the preceding ST full-body commit is `73412899c499828f16391b7c7b0e813fda0e6235`, blob `b8767c41a4a44c8091b497a196f3044f8d4a5eb7`. No extension of this census.

Direct terminal: if rho is a zero with kappa=2 Re(rho)-1>0, the exact-head Mellin inequality gives E_H>=kappa(H+1)^kappa/|rho|^2. One common unbounded sequence with E_H<=C_epsilon H^epsilon for every epsilon>0 would contradict this for epsilon<kappa, then use symmetry. FOLD1-3 treat only a cross in a comparison norm. Both self-energies, other and reflected/zero cells, physical middle H<m<=N and the complete infinite tail are not thereby paid. No identification of Nyman with Euler's compensated virtual divisors, VF's actual prime/history source, or NNS's labeled principal/HIGH Gram. The compiled period mean restores the ordered gcd crosses on one period, not the phase of a physical cutoff. No change to the nine routes, OAI 47/54 barrier, or theta>3/5 gate.

## K-L. Independent checks, handoffs and provenance

Python 3.12.14, Linux x86_64, NumPy 2.3.5, SciPy 1.17.0, deterministic, no seeds. Primary: exact-rational breakpoints, integrate the full squared staircase and subtract two separately integrated self-energies, O(N log N). Integer grids 10^-30 and 10^-45; holdout 10^-32; sensitive heads recomputed at 10^-50. Decimal ln bracketed by adjacent decimals, Machin pi by alternating fractions, sine/cosine by Taylor with factorial remainder. Independent certificate: trial division, different two-moment solve, binary range reduction and rational atanh series for log, exact row-polynomial integration and parity splitting at 10^-40 for 126; it shares the outward interval and trig primitives. Third method literally sums ordered overlaps in binary64, O(N^2), including both squares. First a floating endpoint overcounted the zero-area (k,l)=(112,126) at H=12 by one; integer masks correct the geometric counts at 6/12/18 to 173/2726/13772. No sign changed. Main search about 7-9 s per precision; registered holdout 17 s, 50-digit spot checks 18 s, independent witness plus height 4.8 s. No stochastic trials or unreported precision substitutions.

Replay from the accompanying sources (arguments are explicit; no network or Lean needed):

```sh
python fold.py 45 $(seq 6 6 96)
python fold.py 42 phase
python direct_pairs.py phase $(seq 6 6 96) 126
python ray_check.py 32 holdout
python ray_check.py 36 rays 102 108 120 192
python ray_check.py 40 fixtures
python witness.py 40 height 126
python height_identity.py
```

SHA256: `fold.py` 489a69c50101ec4b1c7259b5ae1192843ab2bf64a16c42228fd0e3b2e7bbc05d; `direct_pairs.py` 88bf5cb41f6442e421c1434a98a9f0694e1247f563b92cf18f4b111fc13ae3c1; `ray_check.py` 7d928ae36f0e233f9d79721e44d4b23277ff00bbb4c71b02412a7cf0c25052c7; `witness.py` 0302a863d42f90d0284c9c1f896518386d8e6e73d45616458ed1ec3cee9068ba; `height_identity.py` 3b6de082de6d7d9e200832cbe299472c5de4b5d94918dbc2f4d87f0b569de2cf. Separate prospective holdout registration after the first 16 heads: cbc5c4208b49afe56fe6af32eb9db28d25370bbe889929a0ec892f3adad6f805. FOLD3 and the H=126 height attribution are subsequent deductions, not preregistered.

Continuity ledger (NY actual times; November 18 unless marked 19). Last own ST 19:00 `780b932540c38e61bb6f81f732e66c4c9b1180b0`. Lean VR 13:14 `2cd3263317a8afaae5e664f4b56d2c095059421c`; separate 21:08 MEAN evidence in merged #1149 is not a new daily report. Coordinator DAMP -> PHASE 23:09 `2e6bfc31f2796d47b426546eabf08783c35b3699`; 00/90 mirrors each identical, CHECK `8fbab91ec28f0d991c46d0731ec9da6c08d30d56`, canonical `ee7b4ce6ff79ab0eaea4d8b74d95e3e78f398cb5`; one invocation. Owner GP -> AR 19th 00:09 `3161b375fa66909c9dc9f373ae75ceb3a1bfa24f`; Analytic LW -> ARC 19th 01:04 `04ea85ac45dd2e12e90ed41111909e01c7897bd3`; Wheel LC -> EX 19th 02:05 `85d15b9799821e757db49a6c869335bbdfefb99b`. Referee FC 12:03 `91b57ce6a46693403cd8a5751c63aaf8335ab305` covers DAMP1-4 and scoped PV1-3 only. No later published Referee verdict inferred. External inbox `7d63d434690d00dffce9c90335d41c4f62d85798`: retain unit/cofactor cutoff for EXT-20261018-PNT-1; EXT-20261014-5 is all-R, not first-bad. CONTINUITY_UNVERIFIED for exhaustive historical whole-file backfill where large displays were shortened; material latest sections and immutable source identifiers checked. No stage inferred from its scheduled time.

Coordinator/Analytic: retire the all-head sign shortcut; retain the weaker dyadic positive-part question. See FOLD3 for the signed source it actually estimates. Owner: B=31, X=961, real half split, floor(X^(5/9))=45; H/I/S/O counts (sites,primes)=(481,70),(160,30),(18,8),(302,54). Signed total in [-46.085820920168,-46.085820920167], square with all six mixed terms restored; replacing equal real halves by 480+481 misclassifies 1,13,37,481. Thin p=7 and 11 have opposite signs of log(p)-2. Wheel: B=20, n=506 and 858 have (old,tail,mu)=(1,-2,-1),(-3,4,1); at B=250, b=251,L=28, rank rule matches 335 of 357 distinct-prime demands, first missing (251,389), not a Hall obstruction. Referee: audit the area factor two, fixed-ray density, both repair terms and h-sum in FOLD3. Lean: the finite overlap indicator or integer support equivalence is a candidate only after review; no formalization of the unproved endpoint requested.

## M-N. Ranked portfolio and resume capsule

1. **Continue:** signed primitive-height windows. FOLD3 at Y=H obtains H^(3/4+epsilon), not H^epsilon. Next falsifier: on the fixed H=6*2^j partition only H<e<=2H by the common factor g; before taking absolute values test whether the positive part of the band can be bounded subpower by cancellation across g, with both corrections, the exact windows and every ratio retained. This is a distinct sub-block conjecture, not known necessary or sufficient for RH. Start from the three verified small-head maps, not a larger undirected scan.
2. **Retain with narrower scope:** the dyadic assertion max(0,X)<=C_epsilon N^epsilon uniformly in j is a CONJECTURE; six finite negative signs and fixed-ratio asymptotics do not establish it. Replace no full norm by this one box.
3. **Reject:** X<=0 at all legal heads (FOLD1); any extrapolation from the negative 1:2 coincidence or from a finite collection of ratios. Stop extending the H=60 prefix unless the tail inequality or the actual coefficient source changes.

EXECUTION_COMPLETED; FINITE_COMPUTATION for the enclosures, REFUTED only as in FOLD1, FOLD2-3 PAPER_PROOF/SELF_AUDIT; INDEPENDENT_REVIEW=PENDING; VERIFIED_ETA=NONE; RH=OPEN. Policy SHAs: half `96ad4439ec458af6168f7d9cb3eef5dde291d37c`, cross `e3ae4280438f591f1ffaddd754a1c3a6d35d0691`, continuity `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`, publish `a9583516fd2e603320c771e32c170132bf0c53e9`. `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1; high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1`. Opening checkpoint exact-commit readback: `f4295bfd311175fbebac7e4ec64f0afff1f9854c`, 2294 bytes, blob `2debae768c2f8724171bd4b63f61c1675630f937`. The canonical update retains this full prefix; this body does not presume its own publication receipt. No other repository path, PR, schedule or branch was modified.

## 11:00 EST | Crossing heads: registration

`20261119-census-1100-EST/CROSS-CHECK`. Actual scheduled ChatGPT trigger November 19, 2026, 11:00:01 EST (16:00:01Z), America/New_York; scheduler RUN_ID_UNAVAILABLE. IN_PROGRESS / PARTIAL. Main `93398824812269526c1ac8c00f43c7ccfe142751`, AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`, contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`, report intake `fdc5e465203e4a5b94ccf393c2fd84e0edade6da`. Flat taper `2d23721027ecc44e85b7add02fc632b482f03352`, residual `2da630c1d5fb9302e2097ec1e170cf41c2b40609`. No open PR at intake; #1150 is merged and its dedicated job passed. It concerns two fixed-head tail phases, not this finite physical window.

Registration for RIDGE: let delta(x)=1-sum_{k<=x} mu(k) log(x/k)/k. Test every integer cell of [3,303] (legal centers H=6,12,...,300) by its endpoint signs and its affine dependence on log x. Record genuine crossings, ties at H+3, multiplicity per head and unresolved endpoints separately. Select the first three distinct legal centers in increasing crossing order, not by energy. For each, use the closest strictly smaller and larger nonselected legal center inside the scanned range when one exists; shared controls are counted once. Compare the closed integer window N/4<=m<=N/3, N=H^2: full literal two-band energy, bare square, drift square, and twice the signed mixed term, with direct vs split residual checks at every m. Test the strict shortcut 'each crossing head has lower window energy than both nonselected controls when both exist'; disjoint enclosures in the opposite order refute it, not the endpoint theorem. Also test whether the mixed term is always nonpositive on selected heads. As a structural check partition divisor jumps by a prime p>H and restore the H-smooth complement and its mixed product. No all-scale inference; no energy value was used to select the sample. Prior Analytic spot flags are not a blinded independent sample. Previous FOLD and the H=60 tail census stand; do not extend them to select heads.

All seven roles have entries today, Lean's canonical daily remains partial. RIDGE, EXCHANGE, BAND, HALL, PRISM, EXTREMA and earlier FOLD kept distinct. `half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1`. Publication policy `a9583516fd2e603320c771e32c170132bf0c53e9`. Intended canonical: `research/agent_reports/2026-11-19/40-prime-census.md` on `agent-reports`. Prior canonical metadata: 21,076 bytes, blob `03f2a7549512c2daf3dd07cb3b99224463803e11`. Direct Git CONNECT 403; the authenticated full-file preview is shortened. No byte-verified local original at this checkpoint. Preserve the canonical prefix; this immutable own-role checkpoint is not a canonical append. Attempt lossless consolidation with final results. Publication requires exact-commit readback.

## 11:00 EST continuation | A crossing is not a local energy minimum

`20261119-census-1100-EST/CROSS-FINAL`. Synthesis after 11:25 EST, same invocation as CROSS-CHECK. **CROSS1 / REFUTED:** the first admissible crossing head, H=12, has greater physical window energy than *both* closest noncrossing controls. Its signed drift cross term is positive, not negative. **CROSS2-3 / PAPER_PROOF, SELF_AUDIT:** an actual large-prime part of that window retains squared energy of order H^2/log^4 H even after its best possible head-dependent linear correction. The complementary smooth integers cancel the same nonconstant profile. This rules out separately charging the two parts at subpower cost; it does not rule out their signed sum. Independent mathematical review pending; no exponent improvement or RH proof.

### A. Registered crossing and signed-square evidence

For 300 unit cells [n,n+1] covering [3,303], set a(n)=sum_{k<=n}mu(k)/k. Exactly delta(x)=delta(n)-a(n)log(x/n) on that cell. All 301 integer endpoint signs were separated from zero; there are 16 genuine crossings, 14 distinct legal heads, no midpoint ties, no ambiguous cells. Left endpoints in order: 10,13,16,19,26,32,39,49,62,79,96,116,152,194,228,291. Nearest legal centers: 12,12,18,18,24,30,42,48,60,78,96,114,150,192,228,294. The five crossings at the first three heads, each in [v,v+1e-11], have lower endpoints v=10.91283766913, 13.10926456936, 16.42008808634, 19.88981696521, 26.81546397612. The signs alternate, starting positive to negative. All three heads share controls 6 and 36; H=30 is selected too and cannot be a control. These are not six independent comparisons. Nov 15 SS5 already saw early crossing cells with a different H,N rule; the physical-window comparison here is new.

Use the literal FOLD coefficient and both original repairs above, N=H^2, L=log H. On W=[N/4,N/3] inclusive, the RIDGE profiles satisfy D(m)=m, P(m)=0 because every repaired denominator exceeds m. Put A=1+sum_{k>=2}mu(k)p(k){m/k}/L, q=U/L. Then r=A-qm. Each table entry below is the LOWER endpoint of a certified interval of width 1e-12; no division by the number of outputs. The mixed term is -2q sum_W A(m)/(m+1). The three components reproduce the direct square with both orientations.

| H | Outputs | E=sum r^2/[m(m+1)] | Bare square | Drift square | Signed mixed term |
|---:|---:|---:|---:|---:|---:|
| 6 control | 4 | .000713588228 | .000979100637 | .000592089594 | -.000857602004 |
| 12 crossing | 13 | .001229640634 | .001209589367 | .000004278762 | .000015772504 |
| 18 crossing | 28 | .001698055329 | .001558882285 | .000029010856 | .000110162186 |
| 24 crossing | 49 | .000525367874 | .000543282970 | .000005757794 | -.000023672892 |
| 36 control | 109 | .000443017649 | .000528875963 | .000031659588 | -.000117517903 |

Thus H=18 is the largest of the five; 24 is below 6 but above 36. The shortcuts first fail at H=12, not at a fabricated VF first bad. Neither failure contradicts eventual behavior or a bound up to a constant. Direct residues, the actual two-profile solve, and an independent floor staircase agree at all 203 window outputs. The exact head, N/2 and the first nonzero repair floor at N/2+1 were checked separately.

### B. An exact prime-owner decomposition of the physical residual

Let j_B(n)=sum_{d|n,d>B}mu(d)log(d/B), J_B(m)=sum_{n<=m}j_B(n). By the original reciprocal moment and `nyman_flat_return_of_moment`, for every m>=1, L r(m)=J_H(m)-J_N(m)+sum_k h_k floor(m/k), where h_k are the actual two repairs. On W the last two terms are exactly zero. This is the previously proved starting bridge, not a new estimate.

For n<=N containing p>H, the prime is unique; write n=pt, t<H. All divisors >H which contribute contain p, so the jump is log(H/p) if t=1 and Lambda(t) otherwise. Indeed sum_{d|t}mu(d)=0 for t>1 and sum_{d|t}mu(d)log d=-Lambda(t). Squareful n and prime-power cofactors are retained. The unnormalized sum from these integers up to m<=N is therefore

`J(m)=sum_{H<p<=m} [psi(floor(m/p))-log(p/H)]`, with `psi(t)=sum_{q^a<=t}log q`.

Each owner's sign is exactly that of `H*lcm(1,...,floor(m/p))-p`; equality is impossible since p>H and floor(m/p)<p. Each owner can change sign at most once after admission. Define S(m) by summing the original jumps on all integers with no prime >H (including the unit); then Lr=J+S on W. At H=12 the energies of J/L, S/L and their mixed term are in intervals of width 1e-12 starting at .010938594919, .011420127833 and -.021129082118. Their total is the same .001229640634... whose *drift* cross is positive. At H=24 those three lower endpoints are .031309778629, .032081295981 and -.062865706738. Neither sign belongs to the total independently of grouping.

All-output check, without extending the pre-half formula illegally: for n=u v, u the B-smooth part, v>1, j_B(n)=j_B(u)+Lambda(u) when u>1; when u=1 it is log B-Lambda(v). For v=1 retain j_B(u). Proof: the low-divisor log sum depends only on u, and the complete divisor log sum is -Lambda(n) for n>1. Apply this at BOTH B=H and B=N and restore all repair floors, including repeats. Exact rational products before taking logs and direct coefficient jumps agree for all 4,757 outputs 1..2N+1 across the five heads; also 30 direct residue boundary checks. No tail energy was truncated and called a full norm.

### C. Why even an optimally centered prime sector is too large

**CROSS3 / PAPER_PROOF, not Lean.** Fix 0<a<f<=1/2 before H. Uniformly for integer aH^2<=m<=fH^2, let t=m/H^2, c0=log(2)-1/2 and gamma be Euler's constant. As legal H tends to infinity,

`J(m)/m = c0 + [log(t)/4 - 1/4 - gamma/2]/L + o(1/L).`              (1)

For w_m=1/[m(m+1)] let Pi subtract the best multiple of m on this precise window in the w-weighted norm. The fitted multiple can depend arbitrarily on H. Then

`(L^4/H^2) ||Pi(J/L)||^2 -> C(a,f) = (1/16) integral_a^f (log t - mean_[a,f](log))^2 dt > 0.`

The same limit holds for Pi(S/L); their mixed term after the same normalization tends to -2C(a,f). Thus even optimal separate linear detrending cannot give subpower energy on any unbounded selected subsequence. Only the separate cost is excluded. With a=1/4, f=1/3, C is in [.000035772407,.000035772408]; this small positive constant is distinct from the uncentered linear coefficient c0.

Proof of (1). Put z=log m, E(x)=psi(x)-x. The exact quotient formula gives J/m=sum_{H<p<=m}1/p-[theta(m)-theta(H)]/m+L[pi(m)-pi(H)]/m+sum_{H<p<=m}E(m/p)/m. Classical unconditional PNT with logarithmic-power remainder (e.g. Fiori, Kadiri and Swidinsky, arXiv:2204.02588 and 2206.12557) and partial summation give the first three terms together as `log(z/L)-1+L/z+L/z^2+o(1/L)`. Lower endpoints cost O(H L/m). For the last term multiply by z. For 1<=m/p<=T fixed, PNT for the rescaled primes and bounded Riemann integrability give the limit integral_1^T E(u)du/u^2. For m/p>T, |E(u)|<=C u/(1+log u)^2: on each dyadic bin the reciprocal prime sum above H is O(1/L) by the elementary prime-count upper bound, and z/L is bounded. The omitted normalized tail is O(1/(1+log T)), uniformly in t. Let T grow. The full integral is -1-gamma: integrate the Chebyshev Dirichlet series for s>1, subtract 1/(s-1) from -zeta'(s)/(s zeta(s)), then take s down to 1 using that integrable remainder. Substitution z=2L+log t proves (1) with the stated uniform little-oh.

Why the complementary profile is forced: take fixed beta=7/8 from the strict #1119 gap. Partial summation bounds the sum of mu(d)log(d/H) over H<d<=y by O_beta(y^beta(1+log(y/H))). Expand floor(m/d) into integer multiples and sum over i<=m/H; summation of i^(-beta)(1+log((m/H)/i)) gives J_H(m)=O_beta(m H^(beta-1)). Thus S/m=-J/m+o(1/L) uniformly on this window. The least-squares weights for J/m are m/(m+1), which tend uniformly to 1. Subtract the weighted mean in (1); Riemann sums give C, its smooth counterpart and the negative mixed term. This last power estimate uses the original Mertens baseline, not the desired selected norm. No literature-priority claim.

Falsification: for every multiple of 6 through 192, and 384,768,1536,3072, the aggregate J/m was evaluated by prime products and quotient bins at both window endpoints. First positive left endpoint H=150, first positive right H=96; each turns negative again (last tested negatives 168,114 respectively). At 3072 the ratios are [.075132683,.075132684] and [.084484132,.084484133], not c0. A separate prime-power jump sieve evaluated every window output at H=48,96,192,384,768,1536. At 1536 the scaled fitted energy was [.000043209368,.000043209369], and L times the endpoint contrast [.078709575344,.078709575345] versus limiting log(4/3)/4 in [.071920518112,.071920518113]. Nonmonotonicity is visible; convergence is from the paper proof, not fitted from the data.

### D. Resumed experiments and specialist handoffs

- **Analytic, BAND4:** for H=6,12,18,24,36 the triple (twice the tail integral, D1, their signed difference) has the following lower endpoints, width 1e-12 each: (-.000025364199,.022906135902,-.022931500101); (-.000078533521,-.001248248745,.001169715223); (.000011177057,-.002841278498,.002852455554); (-.000097329462,.001223031796,-.001320361258); (-.000021455506,.002886981638,-.002908437145). Here the first value is 2(gamma-log N)+sum mu(k)log(N/k)^2/k, D1=sum h_k log(N/k)/k. Direct integration on integer log-cells and the alternative band solve agree. Repairs can reinforce as at 18 and 24; there is no uniform cancellation conclusion from these finite signs.
- **Referee, earlier FOLD:** on the fixed band H<e<=2H, grouped by g before taking the positive part, the signed totals at H=6,12,24,48,96 have lower endpoints .0000184482278,.0000014508839,.0000000104237,-.0000003659419,.0000002414766 (width 1e-13). At H=126 the net is [-.0000000801120,-.0000000801119], although the entire cross is positive by FOLD/PRISM. On that same band, sum_g (B_g)_+ is [.0000002221179,.0000002221180], versus [.0000084494308,.0000084494309] when taking the positive part after summing each ray. Both repairs, even/odd denominators, ordered cross and exact areas retained. A positive dyadic band is not a refutation of a subpower bound. No H=60 tail extension.
- **Owner, EXCHANGE:** for B=16..128, all earlier raw walls good (checked roots 2..128); no actual first bad. Four signed values -I_i O_j/[X log^4 X] in order 00,01,10,11 have maxima at B=21,54,121,51 in width-1e-12 intervals starting .000017144669,.000013671260,.000011511645,.000038142781. Negative/zero/positive counts: (42,0,71),(74,1,38),(56,0,57),(49,1,63). All below ad/5 in [.025301792538,.025301792539]. Exact prime products, all integer subtractions, sharp ninth-power cutoff and all ten five-group interactions checked. This finite test does not pay the eventual four bounds.
- **Wheel, HALL:** independent physical enumeration at B=20 gives precisely {462} inside X=735 for the two negative outputs {638,682}; extra neighbors in the full collar are {770,858,870}. Both orders tested but capacity one per output. Independent prefix/rank sums give T_off=(1801467,1891185,-90453) at B=262144 and (11602403,12721796,-1227147) at B=1000000, on the left/right/U prefixes defined in HALL. The reversal tests HALL's stated finite examples, not every physical matching or the full #1135 recurrence.

### E. Authority, continuity, and continuation to one half

Canonical `VFCanonicalSquareVonKochStatement` remains the uniform bound |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)|<=C R log R for every R>=2, one C>=0; its named RH consumer takes `ClassicalVonKochRHCriterion`. Baseline: `native_mertens_near_uniform_window_error_closed` b*=7/8-7/(64 N_pack), every positive loss, no zero-loss substitution. Original source `f629db1b2b65d6ec042ac9432397d4b6316200c6`; hosted raw job 42552018910/128949473700 passed the positive-error, slot, LOW/principal, complete native transfer and dependency checks. Unchanged #1149 is an unweighted period identity; #1150 merged at 14:06:44Z, raw head `0a7d02dabffbb30d247120dd803d5b17afccfcd4`, job 44539205621/135612694340 passed exact types, warning-fatal imports and transitive axiom checks, phases blob `4967409ba4b71e5ddeb720aa502ac8b8e6ed89c8`. Neither estimates a growing-head window. No open/draft PR on closing list; no local Lean, new CI or PR. Policies/definitions pinned above.

Continuity: comparison of the last FOLD intake `6b046d6824e7b1e9cad9e96da901f6f795c7b2b1` to this intake gave 14 intervening commits, ten paths, no deletions. November 18 predecessor blobs and external inbox are in FOLD above. Latest November 19 verified report watermarks (EST; short IDs are Git blob prefixes): Coordinator 07:10 RIDGE `c9e2abd0` (00/90 identical); Owner 00:09 AR -> 08:09 EXCHANGE `9ba622eb`; Analytic 01:04 ARC -> 09:09 BAND `6aa2d6f8` (checkpoint sibling `34bca7e0`); Wheel 02:05 EX -> 10:12 HALL `3a330c46` (checkpoint `b244fd85`); Census 03:11 FOLD `03f2a754`; Referee 04:13 PRISM `68308617` accepted FOLD/PHASE/AR/ARC/EX only within scope; Lean 05:10/05:24 EXTREMA `559d0fb0` is partial, Nov 18 completed VR plus separate later #1149 and #1150 evidence. All roles have actual entries today; no new mathematical review inferred from a recovery file or merge. External `7d63d434690d00dffce9c90335d41c4f62d85798` unchanged; EXT-20261018-PNT-1 keeps the unit cofactor and p=R, EXT-20261014-5 is all-root, not first-bad. Nov 15 SS source `8ce64136c888c6ad7820ef69a78caa5ece07d61b` recovered for selector history. Named relevant delta consumed; exhaustive bytewise continuity of older shortened reports remains CONTINUITY_UNVERIFIED, not a claim of a missed run.

**Half capsule / ranked portfolio.** ACTIVE_SUPPORT on NYMAN. Direct Mellin consumer: at a zero with kappa=2 Re(rho)-1>0 the exact head yields E_H>=kappa(H+1)^kappa/|rho|^2. One common unbounded sequence with full E_H=O_epsilon(H^epsilon) for every epsilon excludes it; use symmetry. No iteration or estimate at a closed supremum is claimed. The window below N/2 has no repair floor, but elsewhere the upper log tail, two repair floors, the other output windows and the infinite weighted tail must be returned, including all mixed terms. Paid far-tail results apply only in their original ranges. Euler's physical-minus-virtual li-pi wheel, the prime/history VF source, the labeled ideal-character NNS/HIGH Gram, and native square-block Mertens/strict K_R are not equal to this window. The genuine prime coupling above is a signed prime-power divisor identity, not a transport of a VF or NNS bound. No change to the nine toolkits, the OAI 47/54 barrier, or its theta>3/5 gate.

1. **Continue jointly:** split W at 7N/24, lower half m<7N/24, upper the rest. Set b_m=1 on the lower half and a constant on the upper chosen so sum b_m m/(m+1)=0. First falsifier for an independent gain: test T_H=(sum_W b_m r(m)/(m+1))^2 / sum_W b_m^2 m/(m+1), a signed contrast orthogonal to the drift before squaring. Conjectural test: some fixed sigma>0 gives T_H=O_epsilon(H^(4b*-2-sigma+epsilon)) on the one prescribed unbounded crossing set G. Cauchy bounds T_H by E_H, not conversely. Start at the reported crossing cells; keep BOTH arithmetic owners. No improvement of this contrast or control of its complements has been proved.
2. **Reject separate payment:** even the best linear fit misses the nonconstant log(t) profile in CROSS3. Referee: audit the two-limit prime sum, the -1-gamma constant and the weighted minimization. Lean: only the finite j_B divisor reduction after independent review; do not assume the asymptotic or the endpoint.
3. **Retain without promotion:** FOLD's positive-part question and BAND4's two-amplitude question survive; larger unconditioned tables and head selection by observed energy do not test them.

**Reproducibility and receipt.** Python 3.12.14, Linux x86_64; GCC 13.3.0, C++17 -O2 -Wall -Wextra -Werror. Deterministic, no seeds. Direct reference O(N |W|); inversion of the constant-one divisor function and a multiple-jump sieve give an independent staircase. Integer grids 10^-38 and 10^-52; correctly rounded Decimal logs enclosed by neighbors; alternate log uses rational range reduction, positive atanh series and geometric remainder <1e-32. Separate Euler-Maclaurin brackets for gamma, rational Machin pi and Taylor remainder for FOLD. Computed interval overlaps are consistency checks, not proofs of formal identities. Runs: `python crossing.py 38` and `52` (0.76/0.81 s); `python independent.py 38 alt fibres fold`; `python returns.py 38 full fold`; `python slope.py 38` (6.8 s); `python handoff.py 38`; compile `wheel_prefix.cpp` with the flags above and run. SHA-256 in that source order: `d82fd92c30da22600c09ee43e5bacd0b28681f7dc0a8d92f6307da30eb21dfec`, `85f8dfef58d236c6a570f4e0a67e129ed7003716a532e71815b1e6ebd0e20883`, `31cddafeee23293cf82956bb6cb4f31985a022441cb0bcfba27d07629d2a9149`, `d88795cc36fab5707260f596151b4535fd5a7b1e5aeee09b12b21fb11e5b2257`, `bc6664976b7d492de9182f7d31c02a9f485386f8e71153eabe474e192afbe0ac`, `356cfbf71b2da126b7c232fe473a5beef53f93a6896e18b222953c29f8914723`.

Opening recovery verified by exact commit `97593f4d06c222f7a293debbc0944e40976e637a`, blob `bb684b7fcf854c3aa2c880cc1429b22b05355807`, 2,926 bytes. For canonical consolidation the prior 21,076 bytes were reconstructed from ordered chunks and independently matched GitHub blob `03f2a7549512c2daf3dd07cb3b99224463803e11`; the checkpoint is included once. No other role's report or source modified. Final publication is evidenced by the subsequent exact-commit readback, not by this paragraph. EXECUTION_COMPLETED; CROSS1=REFUTED (specified shortcuts only); finite values=FINITE_COMPUTATION; CROSS2-3=PAPER_PROOF/SELF_AUDIT; INDEPENDENT_REVIEW=PENDING; VERIFIED_ETA=NONE; RH=OPEN.
