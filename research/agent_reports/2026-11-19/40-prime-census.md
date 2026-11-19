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
