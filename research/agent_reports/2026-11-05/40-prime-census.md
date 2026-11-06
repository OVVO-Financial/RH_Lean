# RH | Prime Census Laboratory - 2026-11-05

## Result Summary

Exact joint prime-factor constraints improve the complete CORR4 cap certificate by 28/3 at R=57 and 12 at R=58. Two independent implementations agree; all held-out roots 65..80 have zero improvement, so no uniform gain is claimed. Wheel's R=59 and R=1024 finite certificates were verified, with a prose-only cutoff correction from 70 to 71. Full proof, hypotheses, code and limitations follow; the original early checkpoint is preserved.

## Early Research Checkpoint - 2026-11-05 03:11 EST Invocation

Actual trigger: SCHEDULED, 2026-11-05T03:11:01-05:00, America/New_York.
RUN_ID_UNAVAILABLE. IN_PROGRESS / PARTIAL; no new result asserted.

Main: ff620da3c0d2c29585805960c6be183c07f16556.
AGENTS blob: 547dda0d9456e7a4e1165dc72d59da6f70d5c023.
Proof contract blob: 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c.
Routing policy blob: ffd8f1c65cc4da656174956d4e03b48bea46768b.
Reporting intake: b6729c9b4777e588e8a99de7c3209abfea8a1c12.

The canonical actual-prime VFCanonicalSquareVonKochStatement remains OPEN.
This run independently selects CORR4: an exact joint-feasibility question
suggested by today's Wheel F1-F4. Fixed-prime models remain explicitly
auxiliary, never counterfeit Mobius data. Prior Nyman and OAI scans are not
repeated. SEARCH_BROAD; new net endpoint gain UNKNOWN.

### Preregistered Question And Discriminator

For R>=56 let X=R^2-1, y_q=floor(X/q^2), q odd prime with q^2<R,
m=M(R-1), G=M(X)-m, and J_q(d)=2Gd/q-2d^2.
Fix P={3,5,7}. An admissible auxiliary sign function preserves squarefree
support, all true coefficients below R, every prime's sign, and
f(pn)=-f(n) whenever p in P, p does not divide n, and pn<=X.
It also preserves the true endpoint sum M(X).

H-SEPARABLE: the sum of the individual attainable maxima of J_q is itself
attainable by one admissible function at all declared development roots.
Rival: the same unanchored composite core influences multiple daughter
cutoffs, so individual maxima cannot necessarily coexist.

Development R=56..64, increasing order. Held-out R=65..80, fixed before
execution. Compute exact integer feasible daughter vectors by grouping
original physical prime-factor orbits, with exact endpoint restoration.
If exact enumeration becomes excessive, stop and disclose the unfinished
range; do not substitute a floating solver's verdict. A strict rational
gap between the sum of marginal maxima and the joint maximum rejects
H-SEPARABLE. Also test the stronger rectangle assertion only as a separately
identified structural diagnostic, not as the primary claim.

Independent verification: reproduce Wheel's R=59 prime-anchored bounds
and one R=1024 P={3,5,7} fixture, including every physical sign rule,
the historical prefix, endpoint, all admitted daughter labels and complete
signed bill. That repetition has an explicit independent-verification
purpose; do not redo the unchanged 329-candidate scan.

Original source declarations fetched and inspected:
canonicalRoughLowQ2Owners / canonicalRoughLowQ2DaughterEnergy
(ebca096e83009a7df514d00b6a2696be86a94c55);
lowOwnerReciprocalMertensColumnReal / daughter weights
(f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8);
prefix-tail mixed identity (d17aeb639bb47d79333cf0d00760c2604feddfdf);
post789 signed remainder (ba95beda901719afaabca9011b8dbae6fc69662d);
Corr4PowerMixedTailBill and conditional exponent consumer
(bb0ee1252e7ba10c44ae5b8d827573d6c581b73a).

Retain B_R=G^2-H_R+sum_q J_q(d_q), with
H_R=sum_(R<=n<=X)mu(n)^2+
    2sum_q (1/q)sum_(R<=n<=y_q)mu(n)^2.
All daughter labels and mixed terms are retained in complete returns.

### Continuity And Pending Work

All November 4 role reports and the external inbox were retrieved.
November 5 Owner RC1-RC6 and Wheel F1-F4 are AVAILABLE.
Coordinator, Analytic, prior Census, Referee and Lean are TODAY=PENDING;
YESTERDAY=CARRY_FORWARD with original evidence scopes.
The external inbox has no entry newer than October 18; source-restoration
warnings remain relevant, historical routing does not override current main.
Open/draft PR search returned empty. Main includes the merge of #1093;
its source identity is not a new quantitative norm bound.

deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1 consumed. Selected
task CORR4-JOINT-PRIME-ANCHORED-CAPS resumes today's exact orbit model
and tests its first unproved joint-saturation inference. No agents launched,
no local Lean, and no repository writes outside this own report.
Final evidence, code, limitations and continuation capsule will be appended.

## Final Research Synthesis - 20261105-census-1

This completes the actual scheduled 2026-11-05T03:11:01-05:00 invocation, not a second run. RUN_ID_UNAVAILABLE. Mathematical status: FINITE_COMPUTATION; the preregistered simultaneous-maximizer claim is REFUTED. The short finite proofs below are PAPER_PROOF / SELF_AUDIT, with independent role review PENDING and no new Lean certification. Two independently implemented calculations agree; that is not independent Referee acceptance of the author's new claim.

### A. Most Important Mathematical Discovery

**Prime-anchored marginal caps cannot always be attained together.** At the smallest allowed failing root R=57, each coordinate's best value is individually realizable under the same squarefree support, complete old history, every prime sign, three prime-multiplication laws, and true endpoint. But the vector (3,-1,-1) is impossible. The genuine shared-core restriction is d_3+d_7<=0. The exact jointly attainable maximum of the COMPLETE CORR4 bill is lower than the sum-of-marginal-maxima certificate by **28/3**. At R=58 the corresponding improvement is **12**.

The mechanism is visible in two original composite cores, 58=2*29 and 62=2*31: their admitted orbit sums have vector (-1,+1,+1) across the three daughter cutoffs. A sign choice that helps the q=3 daughter hurts the q=5 and q=7 daughters. These are shared physical factors, not independent coordinates.

**The improvement is not uniform evidence.** The gap is zero at every other tested root R=56..80, including ALL held-out roots 65..80. Every tested feasible set is smaller than its marginal Cartesian box, yet most objective maxima still coincide. Non-product feasibility by itself does not imply a positive energy saving.

**Independent upstream verification succeeded**, with one prose correction: Wheel's R=59 cutoff Y_7 is 71, not 70. Its program and reported numerical bill used the correct value. The R=1024 auxiliary witness passes all 529,186 prime-law checks, and its full complementary-label bill agrees exactly. None of these auxiliary sign functions is claimed to be genuine Mobius.

### B. Current Authoritative Objective And Provenance

Repository: OVVO-Financial/RH_Lean. Main at intake: **ff620da3c0d2c29585805960c6be183c07f16556**, tree **958770679fb0146df80f44de258f694cd232434e**. Authority was fetched beginning shortly after 08:11 UTC, with the experiment checkpoint committed at 08:21 UTC. New York date is November 5; UTC and local dates are not conflated. Reporting intake was **b6729c9b4777e588e8a99de7c3209abfea8a1c12**.

The original declaration remains OPEN:

```text
VFCanonicalSquareVonKochStatement:
exists C>=0, forall R:Nat, R>=2 ->
  |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R.
```

Its classical RH consumer retains the explicit ClassicalVonKochRHCriterion argument. The actual-prime bound is not supplied by its VF-to-Li coordinate equivalence. This experiment concerns the separate genuine CORR4 sufficient route and its explicit finite relaxation; it makes no map to OAI ideal characters or original clipped first-bad VF cells.

| Main file inspected | Git blob SHA |
| --- | --- |
| AGENTS.md | 547dda0d9456e7a4e1165dc72d59da6f70d5c023 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md | ffd8f1c65cc4da656174956d4e03b48bea46768b |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 6c1d1c10e2755017ffe9d7f40df8b9ae7692f23a |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| RHLean/Proof/SignedTransportAmplificationAudit.lean | 746f35f126f36e024d39e38c92dde30aabca266b |
| research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean | ebca096e83009a7df514d00b6a2696be86a94c55 |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean | f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8 |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean | dbaf123113b544d0b19c7c3c6b92a1288a26cfb8 |
| research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY.lean | ac8015a1dd87aea23d35d57f5102efd38f4a105b |
| research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean | 29bb263ddd07b12a2dd5ccf6a12aecaf627134d8 |
| research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean | d17aeb639bb47d79333cf0d00760c2604feddfdf |
| research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean | ba95beda901719afaabca9011b8dbae6fc69662d |
| research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a |

The stable selector, breadth, role, multi-run and dynamic-protocol instructions were also retrieved and read. Current open/draft PR search was empty. Recent main commits include human merges #1090, #1091, #1092 and #1093; the last adds the Nyman source-return identity, not a quantitative middle estimate. This run did not audit new CI logs or execute Lean, and does not elevate carried-forward proof reports to new formal evidence. An exploratory lookup for an incorrectly guessed zero-frequency filename returned 404; the actual weighted-site definition was subsequently located through inspected imports in GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean, as recorded above. No required source remained missing.

deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1, selected CORR4-JOINT-PRIME-ANCHORED-CAPS. The newer Wheel handoff supplied a concrete exact finite test and an unexplored marginal-to-joint step. Coordinator's earlier JOH compression request is deliberately DEFERRED, not executed or silently counted as covered; it is the next distinct support task. No investigator's protected rotation is changed.

### C. Competing Hypotheses And Preregistration

Checkpoint commit **4907acd14d44bda63508f86f2569151978f7ed8a**, blob **f29bcba7793fd51a138ab39f2bdd9749a189e3af**, was read back exactly before the scan.

H-SEPARABLE: for each declared R, the sum of the individually attainable maxima of J_q is attained simultaneously by one admissible function. Rival: the same free composite core appears with different signs at several cutoffs, preventing simultaneous attainment. Development was fixed as 56..64; held-out was fixed as 65..80. Neither coefficients, ranges, objective nor threshold changed after observing the result.

The separate stronger rectangle diagnostic asks whether every tuple of individually attainable daughter values is jointly feasible. It was explicitly separated from the quadratic hypothesis before execution. A missing vector refutes the rectangle assertion but only a strictly positive exact objective gap refutes H-SEPARABLE. This distinction matters: the rectangle assertion fails at all 25 roots, while the primary objective gap is positive at just two.

The facet explanations and compact flip witnesses were derived AFTER the scan, then independently verified. They are explanatory certificates, not retroactively preregistered predictions.

### D. Exact Carrier, Return And Enumeration

For every integer R>=56 define the original quantities

```text
X=R^2-1; S_R={odd prime q:q^2<R}; y_q=floor(X/q^2);
m=M(R-1); G=M(X)-m; d_q=M(y_q);
V_0=sum_(R<=n<=X)mu(n)^2; V_q=sum_(R<=n<=y_q)mu(n)^2;
H_R=V_0+2 sum_q V_q/q;
J_q(d)=2Gd/q-2d^2;
B_R=2 lowOwnerPrefixTailMixedRawCellMass(R)
       -2 canonicalRoughLowQ2DaughterEnergy(R)
   =G^2-H_R+sum_q J_q(d_q).
```

The source uses unshifted daughter Mertens squares and strict q^2<R, not rounded child roots. The inspected common-clock sites are a(n)mu(n) and t(n)mu(n), with a(n)=sum_q 1_(n<=y_q)/q and t(n)=1_(n>=R). Thus H_R=sum_(n<=X)(t+2ta)mu(n)^2. The exact ordered off-diagonal identity is

```text
2 Mixed_R=sum_(i!=j)[t(i)t(j)+a(i)t(j)+t(i)a(j)]mu(i)mu(j)
         =G^2+2G sum_q d_q/q-H_R.
```

Every diagonal correction, both mixed orientations and all daughter labels are retained. The independent C++ implementation directly expands the i<j pairs at both new witnesses and doubles them, checking the above reconstruction exactly.

**Auxiliary family, explicitly not Mobius.** Fix P={3,5,7}, W=105. Let F_R contain functions f on 1..X with |f(n)|=mu(n)^2, f(n)=mu(n) for n<R, f(p)=-1 for every prime p<=X, f(pn)=-f(n) for p in P with p not dividing n and pn<=X, and sum f=M(X). Genuine mu is a member. We evaluate the same finite polynomial B(f), with d_q replaced by sum_(n<=y_q)f(n). This is not a claim that the source's actual-Mobius Lean declarations are defined on arbitrary f.

Write each squarefree n uniquely as a*d, gcd(a,105)=1, d|105. Then f(ad)=epsilon_a mu(d). The sign epsilon_a is fixed to mu(a) for a<R and for every prime core; other composite cores are free. Define

```text
K_y(a)=sum_(d|105)mu(d)1_(ad<=y),
v(a)=(K_X(a),K_y3(a),K_y5(a),K_y7(a)),
(sum_(n<=y_i)f(n))_i=A+sum_(free cores a)epsilon_a v(a).
```

No distinct integer occurrences are deduplicated: grouping sums all original occurrences in each fiber. Zero-Mobius sites retain zero support. Because R<=80, S_R is exactly {3,5,7}; there is no untested daughter complement in the new small-root maxima.

The reference computation groups equal three-coordinate vectors and enumerates every possible signed sum. The independent C++ version instead visits every physical n, builds its orbit-column contribution, and performs an ungrouped one-core-at-a-time dynamic program. Python obtains mu by divisor-convolution inversion and primes by trial division; C++ uses a smallest-prime-factor sieve. Their algorithms do not share a Mobius table or an intermediate feasible-set table.

The endpoint is NOT dropped. Free cores with zero daughter vector form a one-dimensional exact reachable-sum set. If L=sum_active |K_X(a)|, every active assignment has endpoint contribution in [-L,L] of fixed parity. For every tested root the exact inactive reachable set contains every required residual M(X)-A_0-s in that parity interval. Thus EVERY enumerated daughter assignment has a genuine endpoint-preserving extension. Both implementations check this coverage, not just min/max endpoints.

At R=57, L=56, M(X)-A_0=180, and inactive endpoint sums cover the required even range 124..236. At R=58 these values are 56 and 183, with required odd range 127..239. This justifies computing exact marginal as well as exact joint maxima under the full endpoint constraint.

### E. Executed Results

All objective comparisons are integers after multiplication by 105. Fractions below are exact, not decimal fits.

| R | Number of joint vectors | Marginal box size | Separate maximizer | Joint maximizer | Separate J maximum | Joint J maximum | Gap |
| ---: | ---: | ---: | --- | --- | ---: | ---: | ---: |
| 56 | 846 | 1140 | (2,-1,-1) | (2,-1,-1) | -716/105 | -716/105 | 0 |
| 57 | 858 | 1140 | (3,-1,-1) | (1,-1,-1) | 104/35 | -668/105 | 28/3 |
| 58 | 987 | 1287 | (2,-1,-2) | (0,-1,-2) | -88/7 | -172/7 | 12 |
| 59 | 730 | 840 | (2,-4,-3) | (2,-4,-3) | -2384/35 | -2384/35 | 0 |
| 60..64 | exact enumeration completed | all strictly larger | all attainable together | same objective | recorded in appendix | same | 0 |
| 65..80, held-out | exact enumeration completed | all strictly larger | all attainable together | same objective | recorded in appendix | same | 0 |

The maximum state count is 12,219 at R=80, well below the declared 2,000,000-state stop. No parameter range was skipped, no optimization solver was used, and no numerical tolerance decided feasibility. At R=61 there are two tied q=3 choices; both joint maximizers were retained.

The complete bill, including G^2 and H_R, is:

| R | G | H_R | Separate-cap B upper bound | Exact joint B maximum | Genuine B_R |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 57 | 19 | 6259/3 | -180848/105 | -181828/105 | -61496/35 |
| 58 | 15 | 32423/15 | -204656/105 | -205916/105 | -208856/105 |
| 59 | 9 | 15663/7 | -77864/35 | -77864/35 | -78704/35 |

An exact maximum over the auxiliary family bounds the genuine value because actual mu belongs to that family. The auxiliary maximizer generally is not mu. Negative values at these small roots do not prove a uniform signed bound.

### F. Small Certificates And Exceptional Cases

**R=57.** X=3248; (y_3,y_5,y_7)=(360,129,66); M(56)=-2 and M(X)=17. The anchored daughter vector is (-32,-10,-3). The FREE active core types are exactly:

| Vector (K_y3,K_y5,K_y7) | Count | Core information |
| --- | ---: | --- |
| (-1,1,1) | 2 | 58,62 |
| (0,1,0) | 6 | 74,82,86,94,106,118 |
| (1,0,0) | 34 | full exact list in audit certificate |
| (1,1,0) | 1 | 122 |

Hence every admissible f satisfies d_5<=-1, d_7<=-1 and

```text
d_3+d_7 <= -32-3 + 34+1 = 0.
```

The individual q=3 optimum is d_3=3; the others are d_5=d_7=-1. Their tuple violates the displayed inequality by 2. Individual feasibility is explicit: flip every admitted physical occurrence with 105-free core in {58,286,422,466}; the resulting endpoint/daughter vector is (17,3,-3,-3). Genuine mu itself attains d_5=d_7=-1. These are different admissible functions, not one simultaneous maximizer.

The joint optimum is (1,-1,-1). To prove the upper bound without trusting the dynamic program, all d_i are odd. If d_7=-1, the facet forces d_3<=1, and J_3 is increasing up to its vertex 19/6. If d_7<=-3, its loss from -1 is at least 188/7, whereas increasing J_3 from 1 to its best odd value 3 gains only 28/3. Since 188/7>28/3, this case cannot improve the proposed optimum. The q=5 component is maximized at -1. This proves the exact joint upper bound.

**Attainment and full physical witness.** Starting from true mu, flip the complete admitted orbits of only cores **286=2*11*13** and **422=2*211**. The eight changed integers are

```text
286,422,858,1266,1430,2002,2110,2954.
```

The two endpoint changes are -4 and +4. The q=3 daughter changes by +2; the other daughters do not change. Every historical coefficient, prime sign, squarefree zero, and prime law for 3,5,7 survives. The endpoint/daughter vector is exactly (17,1,-1,-1). Thus the upper bound is attained, not merely necessary. The function is not mu: for example its value at 286 is +1 instead of -1.

**R=58.** X=3363; cutoffs (373,134,68); anchor (-32,-11,-4). Add the core type (-1,1,0) at a=74; the remaining counts are 2,6,34,1 as recorded in the audit. Now

```text
d_3+d_5 <= -43+6+34+2 = -1,
d_5<=-1, d_7<=-2.
```

The tuple (2,-1,-2) violates the first inequality. When d_5=-1, the even d_3 is at most 0. Moving d_5 to -3 costs at least 28, while the best even d_3 can gain only 12 over d_3=0. Hence (0,-1,-2) is optimal. The SAME eight-site flip witness attains it with endpoint 14. Individual q=3 attainment follows by core flips {58,286,422,482}, giving (14,2,-3,-4). All hypotheses were checked on every physical site.

R=57 is the smallest failing root in the model's allowed R>=56 domain: R=56 was exhausted and has zero primary gap. R=58 has the largest gap in the declared range, namely 12. No larger-root maximality or eventual failure is claimed.

### G. Hidden Variable And Joint Arithmetic Structure

The relevant variable is the **signed vector of partial orbit admissions**, not just squarefree support, individual daughter capacity, or membership in a common prime-rule set. At core 58, for example, the cutoff 360 admits the multipliers 1,3,5, whose signs sum to -1. The two smaller cutoffs admit only multiplier 1, giving +1. Moving a root can change this vector, as the extra (-1,1,0) type at R=58 shows.

The general finite support inequality is inherited from Wheel F1:

```text
h dot (d-A) <= sum_(free cores a) |h dot v(a)|.
```

For two coordinates its difference from separate upper supports is exactly

```text
sum_a (|v_i(a)|+|v_j(a)|-|v_i(a)+v_j(a)|)
 = 2 sum_(v_i(a)*v_j(a)<0) min(|v_i(a)|,|v_j(a)|).
```

This elementary identity is not claimed as a new all-scale arithmetic theorem. The new finding is its decisive, fully realized application AFTER prime-anchored marginal reoptimization, and the exact resulting full-bill maxima. No daughter energy or negative square is spent twice.

### H. Mathematical Interpretation And Limits

Wheel's earlier test reported no mixed-only rejection among its original support/anchor cap candidates. There is no contradiction: those candidates could already fail coordinate bounds. This experiment first optimizes each coordinate WITH the prime-anchored constraints and then asks whether those new optima coexist under one common core-sign assignment. That second step produces the new obstruction.

Nor does this contradict Wheel F2-F3's sufficiently-large, fixed-parameter interpolation theorem. The tested gaps disappear in the held-out range; the finite witnesses are below any unspecified asymptotic threshold. This run does not independently certify that all-scale theorem. Fixed-wheel expansion is not recommended as a new asymptotic strategy.

The new constraint changes finite exact optimization, but the genuine all-root bound remains missing. A non-Cartesian feasible set need not exclude the nonlinear objective's optimum, as 23 of the 25 cases demonstrate. This is the most important adverse evidence against overinterpreting the positive examples.

### I. Exact Statement And First Missing Theorem

**20261105-census-1/J1, FINITE_COMPUTATION; finite PAPER_PROOF certificate.** For F_R defined in D, the exact maxima of B(f) at R=57 and R=58 are respectively -181828/105 and -205916/105. Their marginal-majorant gaps are 28/3 and 12. Each marginal maximum is attained by a member of F_R, but no member attains all marginal maxima. This refutes H-SEPARABLE with every original relaxation hypothesis checked.

**J2, FINITE_COMPUTATION / REFUTED.** The feasible daughter set is not the product of its projections at any R=56..80. This statement is strictly weaker in quantitative consequence than J1. No universal positive-gap conjecture survives the stated test.

**J3, FINITE_COMPUTATION.** Today's Wheel R=59 numerical bound and R=1024 construction are independently verified at their finite scopes, with the R=59 endpoint prose correction below.

The source-qualified open target remains, for a fixed eta>0 and every epsilon>0,

```text
exists C_epsilon,R_epsilon, forall integer R>=R_epsilon:
G_R^2-H_R+sum_(q in S_R)(2G_R M(y_q)/q-2M(y_q)^2)
 <= C_epsilon R^(7/2-eta+epsilon).
```

This is the original mixed bill, not a newly proved weaker supplier. A useful structural continuation would need a genuine signed restriction among residual core signs, or a uniform growing-parameter theorem, strong enough to control the complete bill. No such bound is inferred from the finite facet or assumed as a hypothesis to claim progress.

### J. Relationship To The Proof Objective

The inspected conditional consumer mertensSevenEighthsImprovement_of_corr4MixedTailPowerSaving converts a genuine uniform mixed-bill saving eta into a Mertens power 7/8-eta/4, within its stated beta and constant hypotheses. With arbitrary epsilon losses, epsilon must be chosen small enough to preserve a fixed gain. Any new advertised improvement must also exceed the already inherited strict-slot margin at its actual scope. This run supplies neither uniform premise nor a new exponent.

All three daughter labels are included in the new small-root calculations. At R=1024 the fixture check separately restores every other admitted label; no selected-subset maximum is substituted for the full bill. The canonical prime estimate, finite A/C, Nyman middle norm and RH remain OPEN. Net new endpoint gain UNKNOWN; SEARCH_BROAD.

### K. Independent Verification, Endpoint Correction And Uncertainty

**R=59 requested check.** Under P={3,5}, the q=5 cutoff is 139, fixed contribution -17, and exactly 13 free cores have coefficient +1. Thus d_5<=-4. Under P={3,7}, the literal q=7 cutoff is **71**, fixed contribution -5, and free cores are 62,65. Thus d_7<=-3. True mu attains both. The original bounds are

```text
old support/anchor bound = -2152;
prime-anchored bound = -77864/35;
genuine bill = -78704/35;
improvement = 2544/35.
```

Wheel's prose says Y_7=70, but floor((59^2-1)/49)=71. Since 71 is prime, M(70)=-2 and M(71)=-3. At the wrong cutoff 70 the corresponding anchored contribution would be -4 and the bound -2. The upstream code uses integer division and therefore evaluates 71 correctly; the numerical theorem is unchanged. The correction is recorded here only, without editing another role's report.

**R=1024 requested check.** The original Wheel construction algorithm was reused only to obtain its exact 102-core flip list. That is reproduction, not an independent construction. The new C++ verifier separately generates mu, strips prime factors from every physical integer, reconstructs the auxiliary function, and verifies all hypotheses. It checks support through 1,048,575, the complete old prefix, every prime sign, the genuine endpoint 257, selected daughters (44,26,18), and all 529,186 applicable 3/5/7 laws. The full signed return is

```text
G=261;
selected J=204424/35;
complement J=-157164723896/32932757;
H_R=10011222492496327/14325749295;
B_aux=-63140228062888528/100280245065.
```

These are auxiliary coefficients, not a Mobius counterexample. The original 329-candidate scan and R=2002 regression were not rerun; their unchanged reported status is retained without claiming independent reexecution.

All signs, intervals, primes, feasibility, energies and comparisons in this run are exact integers or rational numbers. There are no floating mathematical weights, random seeds, transcendental approximations or uncertain signs. Wall-clock timings alone are floating diagnostics. The observed runtime was Python **3.12.14**, g++ **13.3.0**, flags **-std=c++20 -O2 -Wall -Wextra -Werror**. Python syntax checks and warning-fatal C++ compilation passed. The reference scan took about 0.7 seconds; the final combined verification about 1.3 seconds, as recorded by the programs. No all-scale proof follows from those timings or finite counts.

### L. Research Continuity And Specialist Handoffs

| Report read | Blob SHA | Consumed scope |
| --- | --- | --- |
| Nov 4 Coordinator 00/90 | 68495a5e913eee0e788940a683cf16ec4d0984cc | C49-C52 separate-component warning; CORR4 and deferred JOH handoffs |
| Nov 4 Owner | 560b0b7617703b64e728e12e60a390646c9379ea | LC1-LC5; prior SAT and VF-LOW limitations, not new verification |
| Nov 4 Analytic | 04ffb1b41d8b6afe5a5d89754f5ccbc8d9682d58 | M1-M4 logarithmic maximal bounds, no fixed-power supplier |
| Nov 4 Wheel | 37ad6a1230fbb46369311790ed5686baf1775598 | C1-C2 support caps; L1-L4 coherent completion; QC1-QC3 class restriction |
| Nov 4 Census | 4bd5319fa3d13219cdad006dce4a854b606c2f7c | Nyman N=120 and N=42 falsifiers reused, not repeated |
| Nov 4 Referee | 0e4fdfbf90d52a74074e04ef6cb6988339dc8d84 | referee-9..12 full-return and divergent-split scope |
| Nov 4 Lean | 5fce0138779d67eda4e69c13230274e6419de894 | #1093 theorem/CI report, with PR state updated by actual main merge |
| Nov 5 Owner | 51d0ca5e2e16ab13a341143b56aefdbf4ab7993a | RC1-RC6 small-prime-core obstruction on distinct SAT source |
| Nov 5 Wheel | 2fe34fb6712c34db043e14b1046bb20b9da2f769 | F1-F4, direct source for selected test and independent checks |
| External inbox | 038018145c0fddb2f6306c0712373adf9cd1ea52 | No entry newer than Oct 18; endpoint/source-restoration warnings retained |

Coordinator mirrors have the same blob and are one evidence source. At intake, November 5 Coordinator, Analytic, previous Census, Referee and Lean were TODAY=PENDING / YESTERDAY=CARRY_FORWARD. A scheduled time is not evidence that a run succeeded. Retrieved reports are continuity evidence, not blanket independent approval.

**Coordinator:** record J1 as a finite genuine-factor joint restriction, not a uniform improvement. The newer Wheel test was chosen for its ready exact discriminator; the requested JOH fixtures remain next. Do not narrow the nine-route portfolio.

**Wheel:** after enforcing coordinate caps, recheck joint feasibility; the second optimization step fails at R=57,58. The R=59 and R=1024 requests are verified at finite scope. Correct Y_7=70 to 71 in a future own-report continuation. No larger fixed-wheel scan is requested.

**Referee:** independently verify the four/five core-type tables, endpoint-restoration argument, quadratic maxima, and eight-site attaining witness. Distinguish the original cap candidates from the reoptimized marginal candidates. New finite proof review remains PENDING.

**Lean:** no immediate proof branch is requested. If independently qualified and useful, the R=57 facet plus complete-bill finite certificate is an implementable statement. It must retain the auxiliary-family hypotheses and not claim a uniform Mobius theorem.

**Analytic:** any future quantitative bound must use the complete G^2-H_R+sum J source. A non-Cartesian feasible set or a logarithmic shell estimate does not pay the required fixed-power bill.

**Owner:** SAT's core-preserving cancellation limitation and this CORR4 shared-coordinate restriction are different carriers. The analogy motivates inspection of shared factors but supplies no norm-preserving transfer.

All handoffs are delivered through this own report only. No other agent was launched, and no other report, source, PR, issue, branch, workflow, setting or schedule was modified.

### M. Ranked Experimental Hypothesis Portfolio

| Rank | Exact question / evidence | Counterevidence and independent ingredient needed | Disposition / decisive next step |
| --- | --- | --- | --- |
| 1 | Joint core-sign restrictions can improve a full finite CORR4 certificate after marginal optimization. Exact R=57,58 proofs support this finite statement. | No gap in held-out 65..80; fixed-parameter large-scale freedom remains. Need new genuine inter-core arithmetic or uniform growing constraints. | KEEP the finite certificates; reject a universal positive-gap inference; request independent review, not a larger scan. |
| 2 | Owner LC4's original JOH compression has exact nonnegative placement restoration. Upstream paper result, not tested in this run. | Actual Li_2 arrival floors must be rigorously certified, including initial/final cells. | NEXT DISTINCT TEST: Coordinator's fixed N=512,1024 development and 2048,4096 held-out fixtures. |
| 3 | Individual prime-anchored maxima always coexist under a true endpoint. | Refuted at the smallest permitted failure R=57 by d_3+d_7<=0. | REJECT H-SEPARABLE; retain the correct joint feasible set. |
| 4 | Nyman initial-half energy or negative correction covariance can replace the full middle. | Prior N=120 and N=42 certified failures; no changed hypotheses here. | REJECT unchanged shortcuts; reuse prior results, do not rescan. |

No new all-scale conjecture is manufactured from two small successes. The genuine uniform supplier is explicitly open in I.

### N. Next-Run Resume Capsule

```text
RUN: scheduled 2026-11-05T03:11:01-05:00; RUN_ID_UNAVAILABLE.
MAIN: ff620da3c0d2c29585805960c6be183c07f16556.
POLICY: ffd8f1c65cc4da656174956d4e03b48bea46768b.
CLAIMS: 20261105-census-1/J1-J3.
PRIMARY: CORR4 exact prime-anchored joint caps; P={3,5,7}.
NEW: R=57 facet d3+d7<=0; exact joint gap 28/3.
     R=58 facet d3+d5<=-1; exact joint gap 12.
ATTAINMENT: flip complete 105-free cores 286 and 422, eight sites total.
RANGE: all 56..80; failures exactly 57,58; held-out 65..80 gap zero.
VERIFICATION: independent Python/C++ feasible sets/objectives agree;
             direct pair expansion, endpoint and every physical law checked.
UPSTREAM: R=59 finite bound and R=1024 102-core fixture verified.
CORRECTION: R=59 Y7=71, not prose 70; upstream numerical code is correct.
NOT CLAIMED: all-scale inequality, independent Referee acceptance,
             new Lean theorem, RH, or new exponent gain.
FIRST OPEN: genuine complete all-R mixed bill / new residual-core relation.
NEXT: JOH compression fixtures from coordinator-3 H, using certified Li_2
      floors, N=512,1024 then held-out 2048,4096, initial/final cells intact.
DO NOT REPEAT: this 25-root scan, upstream 329-candidate scan, fixed-wheel
              enlargement, unchanged Nyman or OAI scans.
GATE: SEARCH_BROAD; NEW NET ENDPOINT GAIN=UNKNOWN.
PUBLICATION: requires final commit and exact readback; receipt appended below.
```

### Reproducibility

The attached bundle includes the report, both implementations, the comparison audit, exact output/certificates, and the 102-core fixture. In its extracted directory run:

```bash
python joint_caps.py
g++ -std=c++20 -O2 -Wall -Wextra -Werror independent.cpp -o independent
python audit.py
```

The archive's fixture_flips.txt is the independently verified upstream witness, not an undisclosed generated random seed. The C++ audit checks it without executing upstream construction code. The original generating script is in the pinned November 5 Wheel report; its reuse in this run is clearly distinguished from verification. No network or Lean installation is needed to reproduce these finite checks. The source code is also embedded below so the authorized report is self-contained.

| Executed source | SHA256 |
| --- | --- |
| joint_caps.py | 986ca64ac3d5d27ad9416115d1f69b43ae58f53b4bca322ecc60918017a33c75 |
| independent.cpp | 537b7caceab0a4b40fd4f466d60b2b93e1bec609f601646492c73cf85215231a |
| audit.py | 30c24506264dac3298cb1ed368a68387de34612a951441c8a0f92e0a3118e5d3 |

Generated result files include timings, so their byte hashes can change across executions even when every exact mathematical output is unchanged. Source hashes identify the algorithms; the audit compares exact counts, rational objectives, facets and physical certificates.

#### joint_caps.py

```python
"""Exact prime-anchored CORR4 joint-cap experiment (no floating solver)."""
from collections import Counter
from fractions import Fraction as F
from itertools import product
from math import gcd, isqrt, prod
import json
from pathlib import Path
import time


def arithmetic(limit):
    # Divisor inversion is independent of the upstream prime-sieve algorithm.
    mu = [0] * (limit + 1)
    mu[1] = 1
    for n in range(1, limit + 1):
        for k in range(2*n, limit + 1, n):
            mu[k] -= mu[n]
    primes = [n for n in range(2, limit + 1)
              if all(n % d for d in range(2, isqrt(n) + 1))]
    prime_set = set(primes)
    M, S = [0], [0]
    for n in range(1, limit + 1):
        M.append(M[-1] + mu[n])
        S.append(S[-1] + mu[n]**2)
    return mu, M, S, prime_set


def wheel_divisors(P):
    return [(prod(p for p, b in zip(P, mask) if b), (-1)**sum(mask))
            for mask in product((0, 1), repeat=len(P))]


def source(R, data, P=(3, 5, 7)):
    mu, M, S, primes = data
    X = R*R-1
    labels = sorted(q for q in primes if q != 2 and q*q < R)
    ys = [X] + [X//(q*q) for q in labels]
    divs = wheel_divisors(P)
    W = prod(P)
    anchored = [0]*len(ys)
    free = []
    reconstructed = [0]*len(ys)
    for a in range(1, X + 1):
        if not mu[a] or gcd(a, W) != 1:
            continue
        v = tuple(sum(s for d, s in divs if a*d <= y) for y in ys)
        for i, v_i in enumerate(v):
            reconstructed[i] += mu[a]*v_i
        if a < R or a in primes:
            for i, v_i in enumerate(v):
                anchored[i] += mu[a]*v_i
        else:
            free.append((a, v))
    assert reconstructed == [M[y] for y in ys]
    return labels, ys, anchored, free


def signed_reachable_1d(coefficients):
    states = {0}
    for v, count in sorted(Counter(coefficients).items()):
        states = {x + v*t for x in states for t in range(-count, count+1, 2)}
    return states


def probe(R, data):
    mu, M, S, primes = data
    X = R*R-1
    labels, ys, anchored, free = source(R, data)
    assert labels == [3, 5, 7]
    active = [(a, v) for a, v in free if any(v[1:])]
    inactive = [(a, v) for a, v in free if not any(v[1:])]
    endpoint_states = signed_reachable_1d([v[0] for _, v in inactive])
    radius = sum(abs(v[0]) for _, v in active)
    endpoint_need = M[X] - anchored[0]
    # Sufficient and exact check that EVERY active assignment can be extended.
    required = set(range(endpoint_need-radius, endpoint_need+radius+1, 2))
    assert required <= endpoint_states, (R, "endpoint requires joint 4D enumeration")
    groups = Counter(v[1:] for _, v in active)
    states = {(0, 0, 0)}
    for v, count in sorted(groups.items(), key=lambda kv: kv[1]):
        states = {tuple(x[i] + t*v[i] for i in range(3))
                  for x in states for t in range(-count, count+1, 2)}
        assert len(states) <= 2_000_000, (R, "state budget")
    vectors = {tuple(x[i] + anchored[i+1] for i in range(3)) for x in states}
    assert tuple(M[y] for y in ys[1:]) in vectors
    G = M[X]-M[R-1]
    L = prod(labels)
    score = lambda i, d: 2*G*d*(L//labels[i]) - 2*L*d*d
    marginals = [sorted({v[i] for v in vectors}) for i in range(3)]
    maxima = [max(score(i, d) for d in marginals[i]) for i in range(3)]
    maxargs = [[d for d in marginals[i] if score(i, d) == maxima[i]] for i in range(3)]
    independent = sum(maxima)
    joint = max(sum(score(i, v[i]) for i in range(3)) for v in vectors)
    witnesses = sorted(v for v in vectors if sum(score(i, v[i]) for i in range(3)) == joint)
    impossible_best = [v for v in product(*maxargs) if v not in vectors]
    rectangle = prod(len(m) for m in marginals)
    missing = next((v for v in product(*marginals) if v not in vectors), None)
    Hgap = F(S[X]-S[R-1]) + sum((F(2*(S[y]-S[R-1]), q)
                for q, y in zip(labels, ys[1:])), F(0))
    result = {"R": R, "X": X, "labels": labels, "cutoffs": ys,
              "anchor_M": M[R-1], "G": G, "anchored_vector": anchored,
              "active_cores": len(active), "inactive_cores": len(inactive),
              "groups": [{"v": v, "n": c} for v, c in sorted(groups.items())],
              "endpoint_active_radius": radius, "endpoint_needed_center": endpoint_need,
              "endpoint_available_minmax": [min(endpoint_states), max(endpoint_states)],
              "endpoint_all_assignments_extend": True,
              "joint_vector_count": len(vectors), "rectangle_vector_count": rectangle,
              "marginals_minmax": [[min(m), max(m)] for m in marginals],
              "first_missing_rectangle_vector": missing, "marginal_maximizers": maxargs,
              "unattainable_marginal_maximizers": impossible_best,
              "independent_J": str(F(independent, L)), "joint_J": str(F(joint, L)),
              "gap": str(F(independent-joint, L)), "joint_maximizers": witnesses,
              "diagonal_gap": str(Hgap),
              "independent_bill": str(G*G-Hgap+F(independent, L)),
              "joint_bill": str(G*G-Hgap+F(joint, L)),
              "actual_daughters": [M[y] for y in ys[1:]],
              "actual_bill": str(G*G-Hgap+F(sum(score(i, M[y]) for i, y in enumerate(ys[1:])), L))}
    return result


def main():
    start = time.monotonic()
    data = arithmetic(80**2-1)
    results = []
    for R in range(56, 81):
        r = probe(R, data)
        r["phase"] = "development" if R <= 64 else "held-out"
        results.append(r)
        print(json.dumps({k: r[k] for k in ("R", "joint_vector_count", "rectangle_vector_count", "gap", "marginal_maximizers", "joint_maximizers")}), flush=True)
    output = {"results": results, "seconds": time.monotonic()-start}
    (Path(__file__).resolve().parent / "joint_results.json").write_text(json.dumps(output, indent=2)+"\n")


if __name__ == "__main__":
    main()
```

#### independent.cpp

```cpp
#include <algorithm>
#include <array>
#include <cassert>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <vector>
using V = std::array<int, 3>;
using V4 = std::array<int, 4>;

struct Arithmetic {
    std::vector<int> spf, mu, M, S, core;
    explicit Arithmetic(int N): spf(N+1),mu(N+1),M(N+1),S(N+1),core(N+1) {
        // Smallest-prime-factor recursion, separate from divisor inversion.
        for(int p=2;p<=N;++p) if(!spf[p]) {
            for(int n=p;n<=N;n+=p) if(!spf[n]) spf[n]=p;
        }
        mu[1]=1; core[1]=1;
        for(int n=1;n<=N;++n) {
            if(n>1) { int p=spf[n], m=n/p; mu[n]=(m%p==0?0:-mu[m]); }
            int c=n;
            for(int p:{3,5,7}) while(c%p==0) c/=p;
            core[n]=c; M[n]=M[n-1]+mu[n]; S[n]=S[n-1]+mu[n]*mu[n];
        }
    }
};

void exact_small(int R,const Arithmetic& a) {
    const int X=R*R-1;
    const V qs{3,5,7};
    const V4 ys{X,X/9,X/25,X/49};
    std::map<int,V4> columns;
    // Build columns by visiting actual integer occurrences, no divisor kernel.
    for(int n=1;n<=X;++n) if(a.mu[n]) {
        int c=a.core[n], s=a.mu[n]*a.mu[c];
        for(int i=0;i<4;++i) if(n<=ys[i]) columns[c][i]+=s;
    }
    V4 A{};
    std::vector<V> active;
    std::vector<int> inactive;
    int radius=0;
    for(const auto& [c,v]:columns) {
        if(c<R || a.spf[c]==c) {
            for(int i=0;i<4;++i) A[i]+=a.mu[c]*v[i];
        } else if(v[1]||v[2]||v[3]) {
            active.push_back(V{v[1],v[2],v[3]}); radius+=std::abs(v[0]);
        } else inactive.push_back(v[0]);
    }
    // Ungrouped physical-core DP, independent of the grouped Python DP.
    std::set<V> states{V{0,0,0}};
    for(auto v:active) {
        std::set<V> next;
        for(auto s:states) for(int e:{-1,1}) {
            V t; for(int i=0;i<3;++i) t[i]=s[i]+e*v[i]; next.insert(t);
        }
        states.swap(next);
    }
    std::set<int> endpoints{0};
    for(int v:inactive) {
        std::set<int> next;
        for(int s:endpoints) {next.insert(s-v);next.insert(s+v);}
        endpoints.swap(next);
    }
    int need=a.M[X]-A[0];
    for(int x=need-radius;x<=need+radius;x+=2) assert(endpoints.count(x));
    int G=a.M[X]-a.M[R-1];
    auto score=[&](int i,int d){return 2*G*d*(105/qs[i])-210*d*d;};
    std::array<int,3> marginal{-1000000000,-1000000000,-1000000000};
    int joint=-1000000000;
    for(auto s:states) {
        int total=0;
        for(int i=0;i<3;++i) {
            int value=score(i,s[i]+A[i+1]);total+=value;
            marginal[i]=std::max(marginal[i],value);
        }
        joint=std::max(joint,total);
    }
    int independent=std::accumulate(marginal.begin(),marginal.end(),0);
    if(R==57 || R==58) {
        std::vector<int> f=a.mu;
        for(int n=1;n<=X;++n) if(a.core[n]==286 || a.core[n]==422) f[n]=-f[n];
        V4 sums{};
        for(int n=1;n<=X;++n) {
            assert(std::abs(f[n])==std::abs(a.mu[n]));
            if(n<R) assert(f[n]==a.mu[n]);
            if(a.spf[n]==n) assert(f[n]==-1);
            for(int i=0;i<4;++i) if(n<=ys[i]) sums[i]+=f[n];
        }
        assert(sums[0]==a.M[X]);
        int total=0; for(int i=0;i<3;++i) total+=score(i,sums[i+1]);
        assert(total==joint);
        for(int p:{3,5,7}) for(int n=1;n<=X/p;++n) if(n%p) assert(f[n*p]==-f[n]);
        // Direct ordered pair expansion of the full mixed statistic.
        long long direct=0;
        for(int i=1;i<=X;++i) if(f[i]) for(int j=i+1;j<=X;++j) if(f[j]) {
            int ti=(i>=R),tj=(j>=R),ai=0,aj=0;
            for(int z=0;z<3;++z) {if(i<=ys[z+1]) ai+=105/qs[z];if(j<=ys[z+1]) aj+=105/qs[z];}
            direct+=2LL*f[i]*f[j]*(105*ti*tj+ai*tj+ti*aj);
        }
        long long H=105LL*(a.S[X]-a.S[R-1]);
        long long U=0,E=0;
        for(int i=0;i<3;++i) {H+=2LL*(105/qs[i])*(a.S[ys[i+1]]-a.S[R-1]);U+=(105/qs[i])*sums[i+1];E+=sums[i+1]*sums[i+1];}
        assert(direct==105LL*G*G+2LL*G*U-H);
        assert(direct-210*E==105LL*G*G-H+joint);
    }
    std::cout<<R<<" "<<states.size()<<" "<<independent<<" "<<joint<<" "<<independent-joint<<"\n";
}

void fixture(const Arithmetic& a, const char* path) {
    const int R=1024,X=R*R-1;
    std::ifstream in(path);
    std::set<int> flips; int c; while(in>>c) flips.insert(c);
    assert(flips.size()==102);
    std::vector<int> f(X+1),M(X+1);
    std::vector<int> qs;
    for(int p=3;p*p<R;p+=2) if(a.spf[p]==p) qs.push_back(p);
    for(int n=1;n<=X;++n) {
        f[n]=a.mu[n]*(flips.count(a.core[n])?-1:1);
        assert(std::abs(f[n])==std::abs(a.mu[n]));
        if(n<R) assert(f[n]==a.mu[n]);
        if(a.spf[n]==n) assert(f[n]==-1);
        M[n]=M[n-1]+f[n];
    }
    long long laws=0;
    for(int p:{3,5,7}) for(int n=1;n<=X/p;++n) if(n%p) {assert(f[p*n]==-f[n]);++laws;}
    assert(laws==529186);
    assert(M[X]==257 && M[X/9]==44 && M[X/25]==26 && M[X/49]==18);
    long long L=1;for(int q:qs) L*=q;
    __int128 H=(__int128)L*(a.S[X]-a.S[R-1]),J=0;
    long long G=M[X]-M[R-1];
    for(int q:qs) {int y=X/(q*q);H+=2*(__int128)(L/q)*(a.S[y]-a.S[R-1]);J+=2*(__int128)G*M[y]*(L/q)-2*(__int128)L*M[y]*M[y];}
    __int128 B=(__int128)L*G*G-H+J;
    assert(L==100280245065LL);
    assert(B==-63140228062888528LL);
    std::cout<<"FIXTURE "<<laws<<" "<<L<<" "<<(long long)B<<"\n";
}

int main(int argc, char** argv) {
    Arithmetic a(1024*1024-1);
    for(int R=56;R<=80;++R) exact_small(R,a);
    fixture(a, argc>1 ? argv[1] : "fixture_flips.txt");
}
```

#### audit.py

```python
"""Independently compare outputs and preserve compact exact certificates."""
from fractions import Fraction as F
import hashlib
import json
from math import gcd
from pathlib import Path
import platform
import subprocess
import time
import joint_caps as j

ROOT = Path(__file__).resolve().parent
start = time.monotonic()
run = subprocess.run([str(ROOT / 'independent'), str(ROOT / 'fixture_flips.txt')],
                     check=True, capture_output=True, text=True)
(ROOT / 'independent_output.txt').write_text(run.stdout)
results = json.loads((ROOT / 'joint_results.json').read_text())['results']
lines = run.stdout.splitlines()
for row, line in zip(results, lines[:25], strict=True):
    R, count, separate, joint, gap = map(int, line.split())
    assert R == row['R'] and count == row['joint_vector_count']
    assert F(separate, 105) == F(row['independent_J'])
    assert F(joint, 105) == F(row['joint_J'])
    assert F(gap, 105) == F(row['gap'])
assert len(lines) == 26 and lines[-1] == 'FIXTURE 529186 100280245065 -63140228062888528'
data = j.arithmetic(80**2-1)
mu, M, S, primes = data
certificates = []
for R in (57, 58):
    labels, ys, A, free = j.source(R, data)
    grouped = {}
    for a, v in free:
        if any(v[1:]):
            grouped.setdefault(v[1:], []).append(a)
    h = (1, 0, 1) if R == 57 else (1, 1, 0)
    lhs_anchor = sum(h[i]*A[i+1] for i in range(3))
    cap = sum(abs(sum(h[i]*v[i+1] for i in range(3))) for _, v in free)
    rhs = lhs_anchor + cap
    assert rhs == (0 if R == 57 else -1)
    X = ys[0]
    divs = j.wheel_divisors((3, 5, 7))
    flipped_sites = sorted(a*d for a in (286, 422) for d, _ in divs if a*d <= X)
    f = mu[:X+1]
    for n in flipped_sites:
        f[n] = -f[n]
    sums = [sum(f[1:y+1]) for y in ys]
    assert sums[0] == M[X]
    assert sums[1:] == ([1, -1, -1] if R == 57 else [0, -1, -2])
    for n in range(1, X+1):
        assert f[n]*f[n] == mu[n]*mu[n]
        if n < R: assert f[n] == mu[n]
        if n in primes: assert f[n] == -1
    for p in (3, 5, 7):
        for n in range(1, X//p+1):
            if n % p: assert f[n*p] == -f[n]
    certificates.append({'R': R, 'facet_h': h, 'facet_rhs': rhs,
                         'groups': [{'vector': k, 'cores': v} for k, v in sorted(grouped.items())],
                         'flipped_cores': [286, 422], 'flipped_sites': flipped_sites,
                         'realized_endpoint_and_daughters': sums})
    individual_flips = [58, 286, 422, 466 if R == 57 else 482]
    individual = mu[:X+1]
    for a in individual_flips:
        for d, _ in divs:
            if a*d <= X:
                individual[a*d] = -individual[a*d]
    individual_sums = [sum(individual[1:y+1]) for y in ys]
    assert individual_sums == ([17, 3, -3, -3] if R == 57 else [14, 2, -3, -4])
    for n in range(1, X+1):
        assert abs(individual[n]) == abs(mu[n])
        if n < R: assert individual[n] == mu[n]
        if n in primes: assert individual[n] == -1
    for p in (3, 5, 7):
        for n in range(1, X//p+1):
            if n % p: assert individual[n*p] == -individual[n]
    certificates[-1]['individual_d3_maximizer'] = {
        'flipped_cores': individual_flips, 'sums': individual_sums}

# Independently reconstruct the two pair-rule certificates requested by Wheel.
R = 59
pair_audit = []
for P, q in [((3, 5), 5), ((3, 7), 7)]:
    _, ys, A, free = j.source(R, data, P)
    i = [3, 5, 7].index(q) + 1
    active = [(a, v[i]) for a, v in free if v[i]]
    upper = A[i] + sum(abs(v) for _, v in active)
    pair_audit.append({'P': P, 'q': q, 'cutoff': ys[i], 'anchor': A[i],
                       'free_core_weights': active, 'upper': upper, 'actual': M[ys[i]]})
assert pair_audit[0]['upper'] == -4
assert pair_audit[1]['upper'] == -3
assert M[70] == -2 and M[71] == -3 and mu[71] == -1
row59 = next(r for r in results if r['R'] == 59)
assert F(row59['joint_bill']) == F(-77864, 35)
assert F(row59['actual_bill']) == F(-78704, 35)
assert F(-2152) - F(row59['joint_bill']) == F(2544, 35)

out = {'python': platform.python_version(), 'cross_implementation_roots': 25,
       'primary_first_failure': 57, 'primary_failures': [r['R'] for r in results if F(r['gap']) > 0],
       'held_out_failures': [r['R'] for r in results if r['phase'] == 'held-out' and F(r['gap']) > 0],
       'rectangle_failures': sum(r['joint_vector_count'] != r['rectangle_vector_count'] for r in results),
       'max_joint_state_count': max(r['joint_vector_count'] for r in results),
       'new_certificates': certificates, 'R59_pair_audit': pair_audit,
       'R59_endpoint_correction': {'literal_cutoff': 71, 'reported_typo': 70, 'M70': M[70], 'M71': M[71]},
       'fixture_1024_independent': lines[-1],
       'elapsed_seconds': time.monotonic()-start,
       'hashes': {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                  for name in ('joint_caps.py', 'independent.cpp', 'audit.py', 'joint_results.json', 'wheel_fixture.json')}}
(ROOT / 'audit_results.json').write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out, indent=2))
```

#### fixture_flips.txt

```text
7046 7102 7606 7613 7619 7627 7631 7633 7642 7646 7661 7663 7666 7694 7697 7702 7706 7709 7711 7726 7729 7739 7747 7751 7754 7762 8041 8062 8066 8074 8086 8122 8126 8138 8174 8177 8194 8206 8222 8227 8234 8242 8249 8251 8254 8257 8258 8261 8266 8278 8279 8282 8294 8299 8306 8314 8318 8321 8326 8327 8333 8338 8339 8341 8342 8347 8354 8357 8359 8362 8366 8371 8374 8378 8383 9514 9526 9538 9542 9554 9581 9622 9638 9658 9682 9686 9694 9698 9706 9718 9734 9746 9766 9782 9794 9823 9854 9878 9889 9911 9958 9962
```

#### wheel_fixture.json

```json
{
  "R": 1024,
  "P": [
    3,
    5,
    7
  ],
  "labels": [
    3,
    5,
    7
  ],
  "cutoffs": [
    1048575,
    116508,
    41943,
    21399
  ],
  "actual": [
    257,
    88,
    -28,
    22
  ],
  "target": [
    257,
    44,
    26,
    18
  ],
  "realized": [
    257,
    44,
    26,
    18
  ],
  "flipped_composite_cores": [
    7046,
    7102,
    7606,
    7613,
    7619,
    7627,
    7631,
    7633,
    7642,
    7646,
    7661,
    7663,
    7666,
    7694,
    7697,
    7702,
    7706,
    7709,
    7711,
    7726,
    7729,
    7739,
    7747,
    7751,
    7754,
    7762,
    8041,
    8062,
    8066,
    8074,
    8086,
    8122,
    8126,
    8138,
    8174,
    8177,
    8194,
    8206,
    8222,
    8227,
    8234,
    8242,
    8249,
    8251,
    8254,
    8257,
    8258,
    8261,
    8266,
    8278,
    8279,
    8282,
    8294,
    8299,
    8306,
    8314,
    8318,
    8321,
    8326,
    8327,
    8333,
    8338,
    8339,
    8341,
    8342,
    8347,
    8354,
    8357,
    8359,
    8362,
    8366,
    8371,
    8374,
    8378,
    8383,
    9514,
    9526,
    9538,
    9542,
    9554,
    9581,
    9622,
    9638,
    9658,
    9682,
    9686,
    9694,
    9698,
    9706,
    9718,
    9734,
    9746,
    9766,
    9782,
    9794,
    9823,
    9854,
    9878,
    9889,
    9911,
    9958,
    9962
  ],
  "unmet": [],
  "verified_prime_laws": 529186,
  "full_auxiliary_return": {
    "G": 261,
    "diagonal_gap": "10011222492496327/14325749295",
    "selected_J": "204424/35",
    "complement_J": "-157164723896/32932757",
    "B_auxiliary": "-63140228062888528/100280245065"
  },
  "scope": "Auxiliary signs with exact support, prime signs, old prefix, P-laws; not Mobius."
}
```

#### independent_output.txt

```text
56 846 -716 -716 0
57 858 312 -668 980
58 987 -1320 -2580 1260
59 730 -7152 -7152 0
60 940 -3872 -3872 0
61 1443 -1308 -1308 0
62 1494 -1440 -1440 0
63 1088 -252 -252 0
64 1605 1362 1362 0
65 2176 530 530 0
66 2360 -1100 -1100 0
67 2624 -1858 -1858 0
68 3070 -3708 -3708 0
69 3606 -4188 -4188 0
70 4094 -9970 -9970 0
71 4289 -9134 -9134 0
72 5015 -4136 -4136 0
73 6216 -2558 -2558 0
74 7008 -3584 -3584 0
75 6422 -8508 -8508 0
76 7071 -6210 -6210 0
77 8052 -1704 -1704 0
78 9288 -1278 -1278 0
79 10349 -228 -228 0
80 12219 3696 3696 0
FIXTURE 529186 100280245065 -63140228062888528
```

#### audit_results.json

```json
{
  "python": "3.12.14",
  "cross_implementation_roots": 25,
  "primary_first_failure": 57,
  "primary_failures": [
    57,
    58
  ],
  "held_out_failures": [],
  "rectangle_failures": 25,
  "max_joint_state_count": 12219,
  "new_certificates": [
    {
      "R": 57,
      "facet_h": [
        1,
        0,
        1
      ],
      "facet_rhs": 0,
      "groups": [
        {
          "vector": [
            -1,
            1,
            1
          ],
          "cores": [
            58,
            62
          ]
        },
        {
          "vector": [
            0,
            1,
            0
          ],
          "cores": [
            74,
            82,
            86,
            94,
            106,
            118
          ]
        },
        {
          "vector": [
            1,
            0,
            0
          ],
          "cores": [
            134,
            142,
            143,
            146,
            158,
            166,
            178,
            187,
            194,
            202,
            206,
            209,
            214,
            218,
            221,
            226,
            247,
            253,
            254,
            262,
            274,
            278,
            286,
            298,
            299,
            302,
            314,
            319,
            323,
            326,
            334,
            341,
            346,
            358
          ]
        },
        {
          "vector": [
            1,
            1,
            0
          ],
          "cores": [
            122
          ]
        }
      ],
      "flipped_cores": [
        286,
        422
      ],
      "flipped_sites": [
        286,
        422,
        858,
        1266,
        1430,
        2002,
        2110,
        2954
      ],
      "realized_endpoint_and_daughters": [
        17,
        1,
        -1,
        -1
      ],
      "individual_d3_maximizer": {
        "flipped_cores": [
          58,
          286,
          422,
          466
        ],
        "sums": [
          17,
          3,
          -3,
          -3
        ]
      }
    },
    {
      "R": 58,
      "facet_h": [
        1,
        1,
        0
      ],
      "facet_rhs": -1,
      "groups": [
        {
          "vector": [
            -1,
            1,
            0
          ],
          "cores": [
            74
          ]
        },
        {
          "vector": [
            -1,
            1,
            1
          ],
          "cores": [
            58,
            62
          ]
        },
        {
          "vector": [
            0,
            1,
            0
          ],
          "cores": [
            82,
            86,
            94,
            106,
            118,
            122
          ]
        },
        {
          "vector": [
            1,
            0,
            0
          ],
          "cores": [
            142,
            143,
            146,
            158,
            166,
            178,
            187,
            194,
            202,
            206,
            209,
            214,
            218,
            221,
            226,
            247,
            253,
            254,
            262,
            274,
            278,
            286,
            298,
            299,
            302,
            314,
            319,
            323,
            326,
            334,
            341,
            346,
            358,
            362
          ]
        },
        {
          "vector": [
            1,
            1,
            0
          ],
          "cores": [
            134
          ]
        }
      ],
      "flipped_cores": [
        286,
        422
      ],
      "flipped_sites": [
        286,
        422,
        858,
        1266,
        1430,
        2002,
        2110,
        2954
      ],
      "realized_endpoint_and_daughters": [
        14,
        0,
        -1,
        -2
      ],
      "individual_d3_maximizer": {
        "flipped_cores": [
          58,
          286,
          422,
          482
        ],
        "sums": [
          14,
          2,
          -3,
          -4
        ]
      }
    }
  ],
  "R59_pair_audit": [
    {
      "P": [
        3,
        5
      ],
      "q": 5,
      "cutoff": 139,
      "anchor": -17,
      "free_core_weights": [
        [
          62,
          1
        ],
        [
          74,
          1
        ],
        [
          77,
          1
        ],
        [
          82,
          1
        ],
        [
          86,
          1
        ],
        [
          91,
          1
        ],
        [
          94,
          1
        ],
        [
          106,
          1
        ],
        [
          118,
          1
        ],
        [
          119,
          1
        ],
        [
          122,
          1
        ],
        [
          133,
          1
        ],
        [
          134,
          1
        ]
      ],
      "upper": -4,
      "actual": -4
    },
    {
      "P": [
        3,
        7
      ],
      "q": 7,
      "cutoff": 71,
      "anchor": -5,
      "free_core_weights": [
        [
          62,
          1
        ],
        [
          65,
          1
        ]
      ],
      "upper": -3,
      "actual": -3
    }
  ],
  "R59_endpoint_correction": {
    "literal_cutoff": 71,
    "reported_typo": 70,
    "M70": -2,
    "M71": -3
  },
  "fixture_1024_independent": "FIXTURE 529186 100280245065 -63140228062888528",
  "elapsed_seconds": 1.2637532840001313,
  "hashes": {
    "joint_caps.py": "986ca64ac3d5d27ad9416115d1f69b43ae58f53b4bca322ecc60918017a33c75",
    "independent.cpp": "537b7caceab0a4b40fd4f466d60b2b93e1bec609f601646492c73cf85215231a",
    "audit.py": "30c24506264dac3298cb1ed368a68387de34612a951441c8a0f92e0a3118e5d3",
    "joint_results.json": "ade3a1b3c74cd9fcf0f9664e8f0c77dc490bec35d4ab5b6610617dd4d4cb69eb",
    "wheel_fixture.json": "2303c0b0cfe89d8afb528e592de5695d2db985c2959ad792a76aa2dc67d70848"
  }
}
```

### Closeout Source Check

At 2026-11-05 08:41:17 UTC / 03:41:17 EST, main remained ff620da3c0d2c29585805960c6be183c07f16556. Today's Owner and Wheel blobs were unchanged. The only added dated file was this run's own checkpoint; Coordinator, Analytic, Referee and Lean remain TODAY=PENDING / YESTERDAY=CARRY_FORWARD. No new execution or review was inferred. Research calculations are COMPLETE; new mathematical status remains FINITE_COMPUTATION / SELF_AUDIT with the stated REFUTED finite claim, not a new global bound.

### Verified Publication Receipt

At 2026-11-05 08:43:14 UTC, the substantive report was re-fetched at commit **453f144360502b111a4cc6c7e0898b54441e30f6**, blob **9b22fbdaef66195ad9546a1fbc700b9e023f4e79**, and matched the submitted content exactly. The commit changes only `research/agent_reports/2026-11-05/40-prime-census.md` on the reporting branch. This receipt identifies that already verified substantive commit, not its own future commit. The early checkpoint is preserved, all A-N sections and code fences passed validation, and each embedded implementation matches the executed source SHA256. Publication: PUBLISHED_AND_READBACK_VERIFIED. Research: FINITE_COMPUTATION; H-SEPARABLE REFUTED at the stated finite scope; independent role review PENDING; new global gain UNKNOWN.


## Scheduled JOH Checkpoint - 2026-11-05 19:00 EST Invocation

Actual trigger: SCHEDULED, 2026-11-05T19:00:01-05:00, America/New_York.
RUN_ID_UNAVAILABLE. Research state PENDING; no new result asserted.
Main: 1667c3cf9b4e898bb9afd62ec48e24610b2156ab.
AGENTS: 547dda0d9456e7a4e1165dc72d59da6f70d5c023.
Contract: 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c.
Policy: ffd8f1c65cc4da656174956d4e03b48bea46768b.
Report intake: e22e2ddd080f4b5c3d8bb27e6365083ecd6b2b63.
All seven November 5 stages are now AVAILABLE; November 4 findings are
CARRY_FORWARD at their stated scopes. Earlier PENDING records are preserved.

Independently selected JOH, resuming the deferred census-1 support task and
Owner 20261104-owner-3/LC4 plus 20261105-owner-3/MC1,MC3,MC5.
No OAI side audit, larger CORR4 scan, or repeated Nyman scan is selected.
Canonical VF bound remains OPEN; SEARCH_BROAD; new endpoint gain UNKNOWN.

### Frozen Question Before Execution

Let Q(n)=floor(Li_2(n)), b_j=min{n>=2:Q(n)>=j},
a_j=pi(b_(j+1))-pi(b_j), e_j=a_j-1. Preserve the original
right-closed interval (b_j,b_(j+1)], not Q(p) admission.
For J_X={j:X<=b_j<2X} and h=floor(X^(1/4)), define
V=sum_(j in J_X)(sum_(r=0..h-1)e_(j+r))^2,
D=sum_(j in J_X)sum_(r=0..h-1)e_(j+r)^2,
C_d=sum_(j in J_X)sum_(r=0..h-1-d)e_(j+r)e_(j+r+d).
Thus V=D+2sum_(d=1..h-1)C_d, with exact overlapping multiplicities
and the complete upper halo.

H-LAG: every C_d<=0 at the declared scales.
Rival H-AGG: individual positive C_d may occur, while sum_d C_d<=0.
A positive C_d refutes only H-LAG; a positive sum_d C_d refutes H-AGG.
Both surviving is finite evidence only, never an all-scale theorem.
Classify each lag into surplus-surplus, empty-empty and opposite-sign
products; no empirical mean subtraction or omitted class is allowed.

Development X={128,256,512,1024}; held-out X={2048,4096,8192}.
Certify Q at integers 2..16640, including halos; stop if any floor is
ambiguous or the halo exceeds that range. No exponent fitting.
This extends the five MC5 fixtures only to test the new lag hypothesis,
not to claim a larger successful census.

Independently verify LC4 single-cell compression, the signed coarse P-D
return and full K/P/D square through N=4096 for h in {1,2,3,5,8}, with
nonzero starting anchors; verify [5,8), prime 163, and the five MC5 Grams.
Use a new certified composite-Simpson/log-series calculation of Li_2,
separate high-precision Ei checks, exact sieve primes and independent
trial-division/discrete-statistic reconstruction. Record which parts of
the verification share the certified floor table.

Source inspected: VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean
9a9336dad72171b6d572a1c1ae88d1ae8b56b530; discrete backlog
4255ca0dffe480f2aec6bd0b68797bbd293396c3; transport
eb84f59055bd31dc117be034d45c92eb9dab8f27; JOH consumer
27e28f09e9f79e8a60d524e5fcb6f19904fa55f5.
B=pi-Q-1 is the centered JOH coordinate, not the uncentered Lean backlog;
its first difference is unchanged. No claim of independently reviewing
Owner MC2's external analytic theorem is made by this finite test.

deployment_ack: current independent multi-front policy consumed.
Only this own report is written remotely; no agent launches or local Lean.
Final findings, exact certificates, source code and resume capsule follow
after actual execution and checks.

## Scheduled JOH Final Synthesis - 20261105-census-2

Actual invocation: SCHEDULED, 2026-11-05T19:00:01-05:00, America/New_York; RUN_ID_UNAVAILABLE. This completes the preceding checkpoint, not an additional run. New mathematical evidence is FINITE_COMPUTATION, with a scoped REFUTED sign assertion. The exploratory aggregate statement remains CONJECTURE. Independent computational reconstructions are reported below; independent Referee acceptance and Lean certification of the new findings remain PENDING.

### A. Most Important Mathematical Discovery

**The original arrival-clock lag correlation can change sign when its upper halo is omitted.** At X=209, h=3, the full source has lag correlations C_1=-13 and C_2=+1. Keeping only windows whose right endpoint lies below 2X changes them to -8 and -1. The apparent favorable sign obtained by that truncation is a statement about a DIFFERENT source.

The complete original energy is V=23, its cell diagonal is D=47, and its full cross contribution is 2(C_1+C_2)=-24. Thus the positive lag does NOT refute aggregate cancellation. This is the smallest lag-sign failure among every integer X in the tested domain 128..8192, not a claim of absolute minimality below 128.

The result discriminates two mechanisms. All-separations-negative is REFUTED, including at the preregistered development scale X=1024 and held-out scales. Full signed recombination remains favorable throughout the tested domain: sum_d C_d<0 at all 8,065 integer cutoffs. In fact 7,571 of those cutoffs have at least one positive lag. Favorable aggregate behavior cannot be justified here by treating every lag as a negative payment.

**Independent upstream verification is also complete at finite scope:** Owner LC4 single-cell compression, MC3's signed coarse return, MC1/MC5's five complete prime/model Grams, the negative [5,8) coarse example, and the boundary prime 163 all agree with separately constructed arithmetic. No defect in those finite upstream claims was found. This does not independently certify Owner MC2's external analytic estimate.

| Claim | Result | Evidence |
| --- | --- | --- |
| JL1 | Original clock lag sign fails; exact X=209 certificate and held-out failures | FINITE_COMPUTATION / REFUTED for H-LAG |
| JL2 | Deleting the upper-halo windows reverses C_2 at X=209 | FINITE_COMPUTATION |
| JL3 | Full C_total remains negative on 128..8192 | FINITE_COMPUTATION only |
| JL4 | LC4, MC1, MC3 and MC5 source checks reproduced independently | FINITE_COMPUTATION |
| JL5 | Lag recombination formula and baseline-only conditional power accounting | PAPER_PROOF / SELF_AUDIT; upper supplier CONDITIONAL |

### B. Current Authoritative Objective And Provenance

Repository OVVO-Financial/RH_Lean. Main at intake and the 2026-11-06 00:16:38 UTC refresh: **1667c3cf9b4e898bb9afd62ec48e24610b2156ab**, tree **6351bbacd22d7abb34eefed1e2cbf5f674642010**. Research date is November 5 in New York. Authority retrieval began with the 00:00:27 UTC check. Reporting intake: **e22e2ddd080f4b5c3d8bb27e6365083ecd6b2b63**. These are observed snapshots, not future freshness claims.

The unchanged canonical target remains OPEN:

```text
VFCanonicalSquareVonKochStatement:
exists C>=0, forall integer R>=2,
 |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R.
```

The canonical RH consumer keeps its explicit ClassicalVonKochRHCriterion premise. This investigation uses the separate native JOH floor-Li prime carrier. It does not identify it with Mobius atoms, OAI Hecke characters, or the original clipped first-bad #915 norm.

| Material source inspected on pinned main | Git blob SHA |
| --- | --- |
| AGENTS.md | 547dda0d9456e7a4e1165dc72d59da6f70d5c023 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md | ffd8f1c65cc4da656174956d4e03b48bea46768b |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 6c1d1c10e2755017ffe9d7f40df8b9ae7692f23a |
| research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean | 9a9336dad72171b6d572a1c1ae88d1ae8b56b530 |
| research/VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean | 4255ca0dffe480f2aec6bd0b68797bbd293396c3 |
| research/VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean | eb84f59055bd31dc117be034d45c92eb9dab8f27 |
| RHLean/Analysis/PrimeSieveLipschitzExcursion.lean | 3eec4abf544310871088dae648fbed1f400cf35a |
| research/LI_FAN_ONE_SIDED_WEIGHTED_COMPOSITE_RH_CONTRACT_20261022.md | 27e28f09e9f79e8a60d524e5fcb6f19904fa55f5 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

Current open/draft PR collection was empty. The latest accepted changes were the #1095 Euler audit repair, #1094 finite Nyman correction-energy theorem, and #1093 exact Nyman return. Their merge commits were inspected directly. This run did not re-audit their CI or claim new formal verification: none changes the inspected JOH source blobs or proves a JOH bound. No Lean execution occurred.

deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1. JOH was independently selected to finish the deferred census-1/Coordinator LC4 support request and to test the new MC1 original overlap Gram. The newest Coordinator Nyman finite-mixture ticket was not selected and remains unexecuted by this run. No protected investigator rotation or source policy is changed. ETA_GATE=SEARCH_BROAD; new net endpoint gain UNKNOWN / NONE_ESTABLISHED.

### C. Competing Hypotheses And Preregistration

The frozen checkpoint was published and read back before execution at commit **07d4288a97b6097f32411004d6db51398e4d11e4**, blob **b2a6dd27a71c7618240537e50a37a8f15036f73a**.

H-LAG asserted C_d<=0 for every lag 1<=d<h at the registered scales. The rival H-AGG allowed positive individual lags but asserted sum_d C_d<=0. A positive individual lag rejects only H-LAG; only a positive complete sum rejects H-AGG. The comparison is an exact uncentered quadratic decomposition, not a statistical covariance estimate.

Development: X=128,256,512,1024. Held-out: X=2048,4096,8192. In every case h=floor(X^(1/4)), fixed in advance. The integer floor-certification domain was 2..16640, including the full halo. No range, coefficient or threshold was fitted after seeing the dyadic results.

**Disclosed follow-up, not retroactive preregistration:** after H-LAG failed, the boundary test froze every integer X=128..8192 on the SAME certified table, seeking the smallest failure and testing whether moving admission could also defeat H-AGG. Its result was then independently recomputed in C++. The halo-truncation control was motivated by the resulting X=209 witness and labeled a changed-source control. It is not part of the original held-out test. No larger arithmetic domain was added.

### D. Exact Carrier And Full Reconstruction

Let L(x)=Li_2(x)=integral_2^x dt/log t, Q(n)=floor(L(n)), and

```text
B(n)=pi(n)-Q(n)-1,
G(N)=sum_(2<=n<N) B(n),
b_j=min{n>=2:Q(n)>=j},
a_j=pi(b_(j+1))-pi(b_j), e_j=a_j-1,
J_X={j:X<=b_j<2X}={u,...,v}, h=floor(X^(1/4)).
```

The centered B differs by -1 from the Lean integer backlog; its first difference agrees exactly. The primitive at physical integer k is the Lean vfMidFloorLiPrimitiveMismatch at k-1. All tested b_j are above the small exceptional domain. Each a_j counts actual primes in **(b_j,b_(j+1)]**, preserving right-boundary primes. In particular lambda(p)=Q(p-1), not Q(p), labels the source cell.

Define the complete original moving-window energy and its cell decomposition:

```text
V(X)=sum_(j in J_X) [pi(b_(j+h))-pi(b_j)-h]^2,
D(X)=sum_(j in J_X)sum_(0<=r<h) e_(j+r)^2,
C_d(X)=sum_(j in J_X)sum_(0<=r<h-d) e_(j+r)e_(j+r+d),
V=D+2 sum_(1<=d<h) C_d.                                  (JL5a)
```

The exact once-per-physical-cell-pair weight is

```text
C_d=sum_i w_(i,d) e_i e_(i+d),
w_(i,d)=max(0,min(v,i)-max(u,i+d-h+1)+1).                 (JL5b)
```

Proof: the two cells i and i+d occur in the same h-window starting at j precisely when i+d-h+1<=j<=i. Intersect with [u,v] and count its integer points. This finite Fubini identity preserves overlap multiplicity and both ends of the interval. It is not an independent size estimate.

Separately, the full prime/model Gram from MC1 was rebuilt with each actual prime p in (b_u,b_(v+h)], its occurrence weight w(p), and the exact clipped pair-overlap K(p,q):

```text
V = sum_p w(p) + 2 sum_(p<q)K(p,q)
    -2h sum_p w(p) + h^2*#J_X.                          (JL5c)
```

D in JL5a is the CELL-innovation diagonal, not the prime diagonal in JL5c. Mixing those two decompositions would change the claim. All same-cell and cross-cell primes, model cross terms, model square, and the upper halo are included. A repeated physical prime across different windows is counted with the actual multiplicity, not deduplicated.

### E. Executed Results

| X | h | Windows | Last halo endpoint | V | Cell diagonal D | C_total | Individual lags C_1,...,C_(h-1) |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| 128 | 3 | 25 | 271 | 18 | 34 | -8 | -6,-2 |
| 256 | 4 | 43 | 533 | 26 | 58 | -16 | -14,0,-2 |
| 512 | 4 | 77 | 1045 | 69 | 151 | -41 | -24,-12,-5 |
| 1024 | 5 | 140 | 2078 | 305 | 415 | -55 | -28,-12,-18,3 |
| 2048 | 6 | 256 | 4139 | 533 | 957 | -212 | -105,-81,-3,-34,11 |
| 4096 | 8 | 471 | 8258 | 1550 | 2202 | -326 | -158,-118,28,-48,27,-61,4 |
| 8192 | 9 | 872 | 16464 | 2456 | 5128 | -1336 | -830,-328,198,-136,-65,-182,23,-16 |

Each row satisfies V=D+2C_total exactly. H-LAG first fails among the registered dyadic scales at X=1024,d=4. All three held-out scales also have a positive lag. H-AGG survives each registered scale.

The separate boundary scan exhausts all **8,065 integers 128<=X<=8192**. The smallest positive lag is X=209,d=2. At **7,571** cutoffs at least one lag is positive, but at **zero** cutoffs is C_total positive or zero: the largest total is **-7**, first attained at X=147. The largest individual positive lag within this declared domain is **217**, first at X=7684,d=3. These maxima are finite-domain statements only. No h other than floor(X^(1/4)) is covered by this scan.

The five MC5 rows were checked against the literal four-term prime/model expansion, not only their totals. For example X=2048 gives **533=1531+8158-18372+9216**, and the new X=8192 row gives **2456=7842+65138-141156+70632**.

### F. Small Exact Certificate And Boundary Sign Reversal

At X=209, h=3, J_X=51..87. The five and ONLY five nonzero terms in C_2=sum_(j=51..87)e_j e_(j+2) are:

| j | First cell | Actual primes | Second cell | Actual primes | e_j,e_(j+2) | Product |
| ---: | --- | --- | --- | --- | --- | ---: |
| 61 | (265,271] | 269,271 | (276,282] | 277,281 | 1,1 | 1 |
| 67 | (299,305] | none | (310,316] | 311,313 | -1,1 | -1 |
| 69 | (310,316] | 311,313 | (322,328] | none | 1,-1 | -1 |
| 86 | (410,416] | none | (422,428] | none | -1,-1 | 1 |
| 87 | (416,422] | 419,421 | (428,434] | 431,433 | 1,1 | 1 |

Their exact sum is 1. Floor certificates for each listed endpoint and its preceding integer, divided by the common denominator 2^128, are in the audit appendix. The prime/composite assertions were checked by both sieve and trial division. The preceding range 128..208 was exhausted, so the stated domain-minimality is verified, not inferred from sparse sampling.

Moving X from 208 to 209 leaves the leftmost admitted index at 51 but admits j=87, since b_87=416 was excluded by b_j<416 and is included by b_j<418. This adds the last +1 above, changing C_2 from 0 to 1. Its right endpoint is b_90=434, which is part of the original source even though 434>2X.

Now compare a deliberately DIFFERENT source that discards every window with b_(j+3)>418:

| Source | Windows | V | D | C_1 | C_2 | C_total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Original, j=51..87 | 37 | 23 | 47 | -13 | 1 | -12 |
| Halo-truncated control, j=51..84 | 34 | 21 | 39 | -8 | -1 | -9 |

Both full reconstructions agree in Python and C++. The truncation removes exactly j=85,86,87. It does not merely remove negligible rounding error: it reverses the lag sign. Neither table permits deletion of the cross-lag return in the other table.

### G. Hidden Variables And Arithmetic Classification

Write e_i=s_i-z_i, where s_i=max(a_i-1,0) and z_i=1_(a_i=0). Because a_i is a nonnegative integer, this equality is exact. Each lag has three signed classes:

```text
C_d = sum_i w_(i,d) s_i s_(i+d)
      + sum_i w_(i,d) z_i z_(i+d)
      - sum_i w_(i,d)(s_i z_(i+d)+z_i s_(i+d)).
```

Thus a positive contribution need not be a prime cluster: two EMPTY clock cells also contribute positively. The X=209,d=2 totals are surplus-surplus 2, empty-empty 1, and opposite signs -2. At the held-out X=8192,d=3 they are **544+408-754=198**. Other lags restore the full negative C_total=-1336.

The relevant hidden data are therefore cell occupancy, separation, and moving admission, including the halo. This is a deterministic explanation of the sign reconstruction. It is not a causal independence claim, a fixed-residue theorem, or a claim that either positive population is individually small. No model primes or randomized coefficients were substituted.

### H. Independently Verified Compression And Its Meaning

Using the original centered B, retained initial anchor, and final partial cell, the requested LC4 coordinates at a=5 are:

| N | G(N) | U_5(N) | E_place(N) | Exact identity |
| ---: | ---: | ---: | ---: | --- |
| 512 | -2595 | -2808 | 213 | G=U+E_place |
| 1024 | -6703 | -7134 | 431 | G=U+E_place |
| 2048 | -16599 | -17485 | 886 | G=U+E_place |
| 4096 | -42284 | -44049 | 1765 | G=U+E_place |

Both implementations also check every integer a<=N<=4096 at a=5,194,820 and h=1,2,3,5,8: **56,360** complete G=K+P-D_model identities and **56,360** full quadratic reconstructions each. Python additionally checks every corresponding stated coarse error bound using a certified LOWER bound for log N. For h=1 it checks 0<=E_place<=pi(N)log N, and E_place<=13N/10 for N>=17. These finite checks do not replace the prior paper proof.

At a=5,h=2,N=8, **G=-1, K=0, P=1, D_model=2**. At a=5,h=3,N=15, **G=-9, K=-10, P=9, D_model=8**. The signed coarse correction can have either sign. For the nonzero anchor a=194,h=3,N=512, **G(a)=-675** and the returned values are G=-2595, K=-2753, P=471, D_model=313. The anchor is neither zeroed nor duplicated.

The five MC5 prime/model Grams and their endpoint telescopes agree exactly. The certified arrivals b_39=148 and b_42=163 give the interval (148,163] with primes 149,151,157,163. Its correct label uses Q(162)=41; the incorrect Q(163)=42 drops the actual right-boundary prime 163. This is independent computational confirmation of the upstream finite witness, not a new discovery credited to this run.

### I. Precise Conjecture And First Missing Estimate

**Exploratory CONJECTURE, not a theorem:** for every integer X>=128, with the exact J_X, h and original prime coefficients above,

```text
sum_(1<=d<h) C_d(X) <= 0.                              (JOH-AGG)
```

The threshold 128 is the registered test-domain boundary, not an optimized universal threshold. There are no observed exceptions through 8192, including all h-transition and boundary cases in that interval. The strongest attempted falsification here was the complete 8,065-cutoff scan, not only seven dyadic points. The componentwise strengthening is false. Future tests of JOH-AGG are prospective; no all-scale probability or optimal constant is inferred.

**Even if JOH-AGG were proved, it would not by itself deliver a new strict power beyond 7/8.** An elementary complete-return budget explains the limitation. For all sufficiently large X the entire h-cell halo lies below 3X, since Q(3X)-Q(2X)>h. Minimal-arrival overshoot bounds every included cell length by O(log X): its Li increase is at most 1+1/log 2<3, and the integral is at least its length divided by log(3X). Consequently max a_i=O(log X), sum a_i<=3X, and the number of cells is at most 3X. Hence, without any short-interval prime hypothesis,

```text
sum_i (a_i-1)^2 <= (max a_i) sum_i a_i + #cells = O(X log X),
D <= h sum_i (a_i-1)^2 = O(X h log X).                  (JL5d)
```

If JOH-AGG held uniformly, V<=D would give V=O(X^(5/4)log X). The exact boundary telescope and Cauchy give an average-backlog difference at most sqrt(#J_X*V)/h. Since #J_X<=X and the boundary averages are within O(h log X) of B(X) and B(2X), this yields O(X^(7/8)sqrt(log X)) plus the lower-order boundary term. Summing dyadic increments back to a finite initial anchor, and paying the integer/real rounding, yields only the corresponding 7/8+epsilon prime-error scale. No initial level is discarded. This is a CONDITIONAL calibration with an elementary PAPER_PROOF / SELF_AUDIT budget, not a proved bound for V or a new endpoint theorem.

Owner's stronger OPEN-JOH-CLOCK-POWER still asks for a fixed kappa>0 and

```text
forall epsilon>0, V(X) <<_epsilon X^(5/4-kappa+epsilon)
uniformly at all sufficiently large X.
```

That supplier is not established, and is not asserted necessary for JOH. A direct one-sided weighted retained-level estimate could use a different consumer. Neither finite aggregate negativity nor payment of positional error supplies it.

### J. Relationship To The Current Proof Objective

JL1-JL2 identify a source-fidelity obstruction to a local-negative-lag proof and provide a small regression for future incomplete-window estimates. JL4 removes the pending independent finite-verification gap in LC4/MC1/MC3/MC5. The new finite evidence suggests that any useful count-energy mechanism must combine signed lags and retain the halo, rather than demand negative sign from every separated class.

No canonical VF estimate, original first-bad payment, Mertens improvement, OAI LOW estimate, or RH theorem follows. The 7/8 baseline and any already qualified fixed-slot improvement retain their own exact scopes. This run establishes **no new endpoint gain**. It does not retire JOH, the native prime-pair route, or the other protected investigations.

### K. Numerical, Independence And Falsification Audit

All discrete arithmetic, correlations, counts, quadratic identities and counterexamples are exact integers. Every Q(n) for 2<=n<=16640 is certified by rational enclosures, not rounded floating evaluations.

The new certifier uses composite Simpson integration of f(x)=1/log x on each unit interval [n,n+1]. It uses 64 equal subintervals for n<16, 16 for 16<=n<128, and 4 thereafter. For even subdivision count m, the error is bounded by max|f''''|/(180m^4). Direct differentiation gives

```text
f''''(x)=x^(-4)(6/log(x)^2+22/log(x)^3+36/log(x)^4+24/log(x)^5).
```

Since log x>1/2 for x>=2, 1544/n^4 bounds this derivative on [n,n+1]. All Simpson weights are positive. Fixed-point intervals use denominator 2^128 with outward rounding for each operation. Logarithms are reduced to y in [1,2] and evaluated by 48 terms of 2*sum_(k>=0)t^(2k+1)/(2k+1), t=(y-1)/(y+1)<=1/3. The omitted tail is at most 18/(8*97*3^97), added with outward rounding. Reciprocals and integration errors are also rounded outward.

Maximum final enclosure width is **less than 1.183e-7**. The minimum certified distance of any noninitial enclosure from an integer is **greater than 8.2788e-7**. Both endpoints of every enclosure have the same floor. The exceptional initial Li_2(2)=0 is exact. A separate 60-digit Decimal computation using the 200-term positive-argument Ei series agrees at every integer; this second calculation is a diagnostic, not the rational certificate.

The reference implementation uses an Eratosthenes sieve, prefix counts and direct window expansion. C++ instead uses trial division, sums the original physical primitive events, groups each cell pair by its clipped overlap count, and reconstructs the compression directly from integer sites. It shares the **certified Q table**, not the prime table or intermediate Gram arrays. This is independent discrete reconstruction, not two independent interval libraries. The floor certifier itself is newly written and differs from Owner's previous log/Ei certificate. All 16,639 prime flags were additionally compared with trial division. The audit compares 236 selected exact fields, all five upstream Gram rows, the complete scan summaries, four LC4 fixtures, and the halo control.

Actual environment: Python **3.12.14**; g++ **13.3.0**, flags **-std=c++17 -O2 -Wall -Wextra -pedantic**. No random seed or probabilistic primality test is used. Reference elapsed time was about **7.597 seconds**; final C++ elapsed time about **0.385 seconds**; the boundary search about **0.064 seconds**. These are observed program timers, not total research time or performance promises.

One initial reference execution completed the certified arithmetic checks but stopped at an unavailable optional mpmath import. The diagnostic was replaced by a standard-library Decimal/Ei implementation and the complete program was rerun successfully. The final sources have no third-party Python dependency. All required computations and syntax/compile checks finished; no running job is left outstanding.

The new proof discussion is SELF_AUDIT. Agreement of separate implementations is not independent Referee acceptance or kernel certification. No global H-AGG assertion, external MC2 analytic theorem, or quantitative infinite bound is labeled proved by these finite checks.

### L. Continuity And Specialist Handoffs

All seven roles' relevant November 4 and November 5 reports were retrieved at the pinned reporting snapshot. Relevant conclusions, scope warnings and continuations were read; executable appendices outside the selected JOH task were not rerun. **TODAY=AVAILABLE** for all seven stages at this intake; **YESTERDAY=CARRY_FORWARD** at original scopes. Earlier runs' valid TODAY=PENDING snapshots remain intact. Coordinator AM/PM tree entries match on both dates.

| Role | November 4 blob | November 5 intake blob |
| --- | --- | --- |
| Coordinator | 68495a5e913eee0e788940a683cf16ec4d0984cc | 88c4b9f83cc3dcea885d0c9ddb1fc26cedef4632 |
| Owner | 560b0b7617703b64e728e12e60a390646c9379ea | 39665b5b28fc48378519ab9d56cee8df4d3e2681 |
| Analytic | 04ffb1b41d8b6afe5a5d89754f5ccbc8d9682d58 | 9490aa2eecafcd19d8007043cc5f978fe421a7c9 |
| Wheel | 37ad6a1230fbb46369311790ed5686baf1775598 | afc85d800c47f82f2db634591a7798005cb668de |
| Census | 4bd5319fa3d13219cdad006dce4a854b606c2f7c | 44f070eed4302f3d8d560346c6fb9b66c35be18a |
| Referee | 0e4fdfbf90d52a74074e04ef6cb6988339dc8d84 | df74121b0a07297776a106ccd1b9d80a36b12fc5 |
| Lean | 5fce0138779d67eda4e69c13230274e6419de894 | c9e8255d2c00a2b317f39531589ac2a16f8e3518 |

Consumed distinctions: the current CORR4 finite joint caps and growing-rule countermodels are not JOH estimates; the Nyman fixed-profile obstruction does not apply to this prime clock; CODIV logarithmic Mobius results require a source bridge before transfer; the latest OAI physical-annulus limitation and MU-LIFT top-prime matching retain their separate carriers; the Euler audit repair is verification infrastructure, not new cancellation. The external inbox **038018145c0fddb2f6306c0712373adf9cd1ea52** has no entry later than October 18. EXT-20261018-PNT and EXT-20261014-5 continue to warn against deleting discrepancy/history or generalizing an unconditional denominator obstruction to first-bad hypotheses; they supply no missing JOH bound.

**Proof Architect:** close only the pending independent finite LC4/MC1/MC3/MC5 verification request. Register JL1-JL2 as a native original-source falsifier and regression. Do not promote H-AGG's finite survival or the older MC2 claim to VERIFIED_ETA. The unselected Nyman three-profile C59/C61 support ticket remains separate and unexecuted here.

**Owner:** the reported finite identities and all five full Grams reproduce. The complete h-cell clock must retain b_(v+h), even for a lag-sign claim. Explore a signed aggregate or one-sided weighted level estimate; componentwise lag negativity is false. Continue the protected SAT task without assuming this prime-clock statistic supplies its cofactor weights.

**Analytic:** assess whether a genuine prime-pair estimate can control the complete clipped C_total, with both empty-cell and surplus-cell terms and the original prime/model return. Before seeking another finite table, specify the arithmetic prediction and a genuine improvement beyond the baseline-only JL5d budget. Independent review of MC2 remains a different task.

**Finite Wheel:** any residue/owner conditioning must restore both classes of positive cell products and the upper-halo windows. X=209 is a minimal tested boundary regression; X=8192,d=3 shows the effect is not confined to the first small witness. No uniform residue or parity theorem is asserted.

**Adversarial Referee:** independently audit the Simpson remainder/tail certificate, JL5b overlap endpoints, the five-row X=209 certificate, and the precise finite versus all-scale scope. JL5d is a conditional exponent diagnosis, not an asserted new source estimate. No independent acceptance of these new findings is claimed in advance.

**Lean Verification:** no new proof branch is requested for unreviewed infinite conjectures. If useful after review, the exact overlap formula and small certified source regression are available; do not treat external rational computation as a Lean numerical certificate or displace higher-readiness quantitative work with duplicate identities.

These are asynchronous published handoffs only. No agent was launched or promised to execute.

### M. Ranked Experimental Hypothesis Portfolio

| Rank | Exact idea and evidence | Counterevidence / independent ingredient / next action | Disposition |
| ---: | --- | --- | --- |
| 1 | JOH-AGG: original C_total<=0 for all integer X>=128; survives 128..8192 | No all-scale proof. Needs genuine complete prime-pair/model control, not component signs. Ask for an analytic discriminator before another larger scan. Even this sign alone supplies no new strict exponent. | CONJECTURE; continue cautiously |
| 2 | Uniformly negative individual lags | Exact C_2(209)=1; registered and held-out failures; positive lags at 7,571 cutoffs | REFUTED; reject this strengthening |
| 3 | Truncating at 2X preserves the relevant sign | X=209 changes C_2 from +1 to -1 | REFUTED at this precise source-comparison scope |
| 4 | Original LC4/MC3 compression with full anchor and P-D_model return | Independently verified 56,360 finite cases; all-scale proof remains the upstream paper argument | FINITE_COMPUTATION; reuse, do not repeat |

### N. Next-Run Resume Capsule

```text
RUN: 20261105-census-2; actual scheduled 19:00:01 EST; RUN_ID_UNAVAILABLE.
MAIN: 1667c3cf9b4e898bb9afd62ec48e24610b2156ab.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1 / ffd8f1c65cc4da656174956d4e03b48bea46768b.
REPORT INTAKE: e22e2ddd080f4b5c3d8bb27e6365083ecd6b2b63.
CHECKPOINT: 07d4288a97b6097f32411004d6db51398e4d11e4; exact readback PASS.
ROUTE: JOH; original Q=floor(Li_2), centered B=pi-Q-1; no carrier substitution.
NEW: JL1 C_2(209)=1; JL2 halo deletion changes that sign to -1.
FULL: V=23=D47+2*(-13+1); halo to 434 is mandatory.
FINITE: all integer X=128..8192, h=floor(X^(1/4)); C_total<0 throughout.
POSITIVE LAGS: 7,571/8,065 cutoffs; no all-scale extrapolation.
INDEPENDENT: Python/C++ discrete reconstruction; shared certified Q table
  explicitly disclosed; independently factored primes; Decimal/Ei diagnostic.
UPSTREAM: LC4/MC1/MC3/MC5 finite checks PASS; MC2 analytic review NOT performed.
PRECISION: all Q(2..16640) certified; width<1.183e-7, margin>8.2788e-7.
REVIEW: new findings await independent Referee; no Lean certification.
FIRST OPEN: complete uniform signed clock-energy/weighted-level inequality.
GAIN: NONE_ESTABLISHED; SEARCH_BROAD; canonical VF and RH OPEN.
NEXT: test a proposed source-exact weighted/pair mechanism against X=209
  and the held-out positive lags BEFORE scaling; retain the complete halo.
DISTINCT SUPPORT OPTION: pending Coordinator C59/C61 three-profile source test,
  if still relevant under fresh authority. Do not repeat unchanged old norm scans.
PERMISSIONS: only this own report changed remotely; no main, other report,
  Lean source, branch, PR, issue, workflow, schedule, or merge action.
```

### Reproducibility And Publication

The following appendix contains all four executed sources, exact output summaries, code hashes and the minimal floor certificates. They are published inside this authorized report, not as arbitrary new repository files. Run the commands in their printed order in one scratch directory; no network or third-party Python package is required.

```bash
python joh_clock.py
g++ -std=c++17 -O2 -Wall -Wextra -pedantic joh_verify.cpp -o joh_verify
./joh_verify
python joh_boundary_test.py
python joh_audit.py
python -m py_compile joh_clock.py joh_boundary_test.py joh_audit.py
```

The synthesis is not declared published merely because it was prepared. Its immutable commit/readback receipt follows after the actual authorized write. All earlier daily report contents and the preregistration are preserved as an exact prefix.


### Executed Source And Data Hashes

| Artifact | SHA-256 |
| --- | --- |
| joh_clock.py | 6af10a960d5e92f93fd0fd72b4daac542f4f36dd3be1669e471840fd48865ba7 |
| joh_verify.cpp | 9de4d2cff7f1d01c2c97b453e3599e8bc8f6e84c15f4b42900040b4f6ce77f78 |
| joh_boundary_test.py | a72ea96e08e3ccce92f9b6040689ac41a039b5d85f6e838f957f4c8119204f6b |
| joh_audit.py | 26fb2353469e6ae31c700bfd84ec7de335b23885c38014bd8a0853e3aba7ad2b |
| Certified floor table, Q(2)..Q(16640), newline-separated | df1a6bdff4cedb3d2195766677edcc3ebbe45d01673124ee0133b4a85b655892 |

### Executed Source: joh_clock.py

```python
"""Exact JOH clock test with independently certified Li_2 floors."""

import hashlib
import json
import platform
import time
from collections import Counter
from decimal import Decimal, localcontext
from math import isqrt
from pathlib import Path

S = 1 << 128
LIMIT = 16640
SCALES = (128, 256, 512, 1024, 2048, 4096, 8192)


def ceildiv(a, b):
    return -((-a) // b)


def mul(a, b):
    return a[0] * b[0] // S, ceildiv(a[1] * b[1], S)


def log_unit(num, den):
    # 1 <= num/den <= 2; 48 atanh terms, with an explicit geometric tail.
    t = ((num - den) * S // (num + den),
         ceildiv((num - den) * S, num + den))
    t2 = mul(t, t)
    p = t
    lo = hi = 0
    for k in range(48):
        lo += p[0] // (2 * k + 1)
        hi += ceildiv(p[1], 2 * k + 1)
        p = mul(p, t2)
    tail = ceildiv(18 * S, 8 * 97 * 3 ** 97)
    return 2 * lo, 2 * hi + tail


LOG2 = log_unit(2, 1)


def log_ratio(num, den=1):
    assert num >= den > 0
    k = (num // den).bit_length() - 1
    v = log_unit(num, den << k)
    return v[0] + k * LOG2[0], v[1] + k * LOG2[1]


def invlog(num, den):
    lo, hi = log_ratio(num, den)
    assert lo > 0
    return S * S // hi, ceildiv(S * S, lo)


def certify_floors(limit):
    q = [0] * (limit + 1)
    bounds = [(0, 0)] * (limit + 1)
    lo = hi = 0
    maxwidth = 0
    minmargin = S
    for n in range(2, limit):
        m = 64 if n < 16 else 16 if n < 128 else 4
        lower = upper = 0
        for i in range(m + 1):
            w = 1 if i in (0, m) else 4 if i % 2 else 2
            f = invlog(n * m + i, m)
            lower += w * f[0]
            upper += w * f[1]
        # f''''(x)=x^-4(6/log^2+22/log^3+36/log^4+24/log^5).
        # log(x)>1/2 at x>=2, so |f''''| <= 1544/n^4 on [n,n+1].
        error = ceildiv(1544 * S, 180 * m ** 4 * n ** 4)
        lo += lower // (3 * m) - error
        hi += ceildiv(upper, 3 * m) + error
        assert lo // S == hi // S, ("ambiguous_floor", n + 1, lo, hi)
        q[n + 1] = lo // S
        bounds[n + 1] = (lo, hi)
        maxwidth = max(maxwidth, hi - lo)
        minmargin = min(minmargin, lo - q[n + 1] * S,
                        (q[n + 1] + 1) * S - hi)
    return q, bounds, maxwidth, minmargin


def sieve(n):
    prime = bytearray(b"\x01") * (n + 1)
    prime[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if prime[p]:
            prime[p * p:n + 1:p] = b"\x00" * ((n - p * p) // p + 1)
    pi = [0] * (n + 1)
    for k in range(1, n + 1):
        pi[k] = pi[k - 1] + prime[k]
    return prime, pi


def decimal_ratio(a, b):
    with localcontext() as ctx:
        ctx.prec = 32
        return str(Decimal(a) / Decimal(b))


def clock(q):
    b = [2]
    for n in range(3, len(q)):
        assert q[n] - q[n - 1] in (0, 1)
        if q[n] > q[n - 1]:
            assert q[n] == len(b)
            b.append(n)
    return b


def energy(X, b, prime, pi, q):
    h = isqrt(isqrt(X))
    starts = [j for j, n in enumerate(b) if X <= n < 2 * X]
    u, v = starts[0], starts[-1]
    assert v + h < len(b)
    e = [pi[b[i + 1]] - pi[b[i]] - 1 for i in range(len(b) - 1)]
    V = sum((pi[b[j + h]] - pi[b[j]] - h) ** 2 for j in starts)
    D = sum(sum(e[j + r] ** 2 for r in range(h)) for j in starts)
    lag = []
    for d in range(1, h):
        parts = Counter()
        witness = None
        for j in starts:
            for r in range(h - d):
                i = j + r
                a, c = e[i], e[i + d]
                label = "empty_empty" if a < 0 and c < 0 else (
                    "surplus_surplus" if a > 0 and c > 0 else "opposite")
                parts[label] += a * c
                if witness is None and a * c > 0:
                    witness = {"start": j, "i": i, "d": d,
                               "cells": [b[i], b[i + 1], b[i + d], b[i + d + 1]],
                               "e": [a, c]}
        lag.append({"d": d, "C": sum(parts.values()), **parts,
                    "first_positive_pair": witness})
    assert V == D + 2 * sum(t["C"] for t in lag)
    primes = [p for p in range(b[u] + 1, b[v + h] + 1) if prime[p]]
    labels = [q[p - 1] for p in primes]
    diagonal = off = 0
    for k, p in enumerate(primes):
        lp = labels[k]
        diagonal += max(0, min(v, lp) - max(u, lp - h + 1) + 1)
        for lq in labels[k + 1:]:
            off += 2 * max(0, min(v, lp, lq) - max(u, lp - h + 1, lq - h + 1) + 1)
    assert V == diagonal + off - 2 * h * diagonal + h * h * len(starts)
    # Endpoint telescope with both complete h-cell boundary groups.
    H = [pi[n] - q[n] - 1 for n in b]
    delta_sum = sum(H[j + h] - H[j] for j in starts)
    boundary = sum(H[v + r] for r in range(1, h + 1)) - sum(H[u + r] for r in range(h))
    assert delta_sum == boundary
    assert boundary * boundary <= len(starts) * V
    return {"X": X, "h": h, "windows": len(starts), "u": u, "v": v,
            "halo": b[v + h], "V": V, "D": D,
            "C_total": sum(t["C"] for t in lag), "lags": lag,
            "prime_diagonal": diagonal, "prime_off": off,
            "prime_model": -2 * h * diagonal, "model_square": h * h * len(starts),
            "delta_sum": delta_sum}


def compression(b, prime, pi, q):
    B = [pi[n] - q[n] - 1 for n in range(len(q))]
    G = [0] * len(q)
    for n in range(3, len(q)):
        G[n] = G[n - 1] + B[n - 1]
    count = 0
    fixtures = []
    starts = (2, 48, 150)
    for j0 in starts:
        a = b[j0]
        for h in (1, 2, 3, 5, 8):
            j = j0
            complete_K = complete_P = complete_D = 0
            for N in range(a, 4097):
                while b[j + h] <= N:
                    c, t = b[j], b[j + h]
                    complete_K += (t - c) * B[c]
                    complete_P += sum(t - p for p in range(c + 1, t) if prime[p])
                    complete_D += sum(t - b[k] for k in range(j + 1, j + h))
                    j += h
                c, t = b[j], N
                K = G[a] + complete_K + (t - c) * B[c]
                P = complete_P + sum(t - p for p in range(c + 1, t) if prime[p])
                D = complete_D + sum(t - b[k] for k in range(j + 1, j + h) if b[k] < t)
                assert G[N] == K + P - D
                assert G[N] ** 2 == K*K + P*P + D*D + 2*K*P - 2*K*D - 2*P*D
                # Use a certified LOWER log bound for the theorem's RHS.
                log_lower = log_ratio(max(2, N))[0]
                if h == 1:
                    assert D == 0 and P >= 0
                    assert P * S <= pi[N] * log_lower
                    if N >= 17:
                        assert 10 * P <= 13 * N
                assert abs(P - D) * S <= h * log_lower * max(pi[N], q[N])
                count += 1
                if (a, h, N) in ((5, 2, 8), (5, 3, 15), (194, 3, 512), (820, 5, 1024)):
                    fixtures.append({"a": a, "h": h, "N": N, "G": G[N],
                                     "anchor_G": G[a], "anchor_B": B[a],
                                     "K": K, "P": P, "D": D})
    return count, fixtures


def main():
    began = time.perf_counter()
    q, bounds, width, margin = certify_floors(LIMIT)
    print("Certified all floors", flush=True)
    prime, pi = sieve(LIMIT)
    b = clock(q)
    rows = [energy(X, b, prime, pi, q) for X in SCALES]
    count, fixtures = compression(b, prime, pi, q)
    assert (b[2], b[3], b[4]) == (5, 6, 8)
    assert (b[39], b[42]) == (148, 163)
    assert prime[163] and q[162] == 41 and q[163] == 42
    wrong = [p for p in range(149, 164) if prime[p] and 39 <= q[p] < 42]
    assert wrong == [149, 151, 157]
    # Independent Ei power series; only the Simpson enclosures certify floors.
    with localcontext() as ctx:
        ctx.prec = 60

        def ei_without_gamma(x):
            total = x.ln()
            term = Decimal(1)
            for k in range(1, 201):
                term = term * x / k
                total += term / k
            return total

        li2 = ei_without_gamma(Decimal(2).ln())
        for n in range(2, LIMIT + 1):
            value = ei_without_gamma(Decimal(n).ln()) - li2
            assert bounds[n][0] <= value * S <= bounds[n][1], n
            assert int(value) == q[n], n
    floor_text = "\n".join(str(v) for v in q[2:]) + "\n"
    Path("floors.txt").write_text(floor_text)
    cert_points = sorted({2, 4, 5, 6, 7, 8, 148, 162, 163,
                          *(v for row in rows for lag in row['lags'] if lag['C'] > 0
                            for v in lag['first_positive_pair']['cells'])})
    out = {"environment": platform.python_version(), "limit": LIMIT,
           "scale": str(S), "log_terms": 48,
           "floor_max_width": decimal_ratio(width, S),
           "floor_min_margin": decimal_ratio(margin, S),
           "floors_sha256": hashlib.sha256(floor_text.encode()).hexdigest(),
           "ei_diagnostic_precision": 60, "ei_checks": LIMIT - 1,
           "compression_checks": count, "fixtures": fixtures, "rows": rows,
           "floor_certificates": {str(n): {"Q": q[n], "lo": str(bounds[n][0]),
                                           "hi": str(bounds[n][1])} for n in cert_points},
           "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           "elapsed_seconds": time.perf_counter() - began}
    Path("joh_results.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
```

### Executed Source: joh_verify.cpp

```cpp
#include <algorithm>
#include <cassert>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <vector>

using I = long long;

int main() {
    const auto started = std::chrono::steady_clock::now();
    constexpr int limit = 16640;
    std::vector<int> q(limit + 1), prime(limit + 1), pi(limit + 1), b{2};
    std::ifstream floors("floors.txt");
    for (int n = 2; n <= limit; ++n) assert(bool(floors >> q[n]));
    for (int n = 2; n <= limit; ++n) {
        prime[n] = 1;
        for (int d = 2; d * d <= n; ++d) {
            if (n % d == 0) { prime[n] = 0; break; }
        }
        pi[n] = pi[n - 1] + prime[n];
        if (n >= 3 && q[n] != q[n - 1]) {
            assert(q[n] == int(b.size()));
            b.push_back(n);
        }
    }
    std::vector<int> event(limit + 1), e(b.size() - 1);
    for (int n = 3; n <= limit; ++n) event[n] = prime[n] - q[n] + q[n - 1];
    for (int i = 1; i + 1 < int(b.size()); ++i)
        for (int n = b[i] + 1; n <= b[i + 1]; ++n) e[i] += event[n];

    std::ofstream out("cpp_results.json");
    out << "{\"rows\":[";
    bool firstrow = true;
    for (int X : {128, 256, 512, 1024, 2048, 4096, 8192}) {
        int h = 1;
        while (I(h + 1)*(h + 1)*(h + 1)*(h + 1) <= X) ++h;
        int u = int(std::lower_bound(b.begin(), b.end(), X) - b.begin());
        int v = int(std::lower_bound(b.begin(), b.end(), 2*X) - b.begin()) - 1;
        assert(v + h < int(b.size()));
        I V = 0, diagonal = 0, off = 0, D = 0;
        for (int j = u; j <= v; ++j) {
            I change = 0, count = 0;
            for (int n = b[j] + 1; n <= b[j + h]; ++n) {
                change += event[n];
                count += prime[n];
            }
            assert(change == count - h);
            V += change * change;
            diagonal += count;
            off += count * (count - 1);
        }
        for (int i = u; i < v + h; ++i) {
            I w = std::max(0, std::min(v, i) - std::max(u, i - h + 1) + 1);
            D += w * e[i] * e[i];
        }
        std::vector<I> C(h), ss(h), zz(h), mixed(h);
        for (int d = 1; d < h; ++d) {
            for (int i = u; i + d < v + h; ++i) {
                I w = std::max(0, std::min(v, i) - std::max(u, i + d - h + 1) + 1);
                I value = w * e[i] * e[i + d];
                C[d] += value;
                if (e[i] > 0 && e[i + d] > 0) ss[d] += value;
                else if (e[i] < 0 && e[i + d] < 0) zz[d] += value;
                else mixed[d] += value;
            }
        }
        I total = std::accumulate(C.begin(), C.end(), I(0));
        assert(V == D + 2*total);
        assert(V == diagonal + off - 2*h*diagonal + I(h)*h*(v-u+1));
        if (!firstrow) out << ',';
        firstrow = false;
        out << "{\"X\":" << X << ",\"h\":" << h << ",\"windows\":" << v-u+1
            << ",\"V\":" << V << ",\"D\":" << D << ",\"C_total\":" << total
            << ",\"prime_diagonal\":" << diagonal << ",\"prime_off\":" << off
            << ",\"lags\":[";
        for (int d = 1; d < h; ++d) {
            if (d > 1) out << ',';
            out << "{\"d\":" << d << ",\"C\":" << C[d]
                << ",\"surplus_surplus\":" << ss[d] << ",\"empty_empty\":" << zz[d]
                << ",\"opposite\":" << mixed[d] << '}';
        }
        out << "]}";
    }
    out << "],\"fixtures\":[";
    int checks = 0;
    bool first = true;
    for (int j0 : {2, 48, 150}) {
        int a = b[j0];
        I anchor = 0;
        for (int n = 2; n < a; ++n) anchor += pi[n] - q[n] - 1;
        for (int h : {1, 2, 3, 5, 8}) {
            for (int N = a; N <= 4096; ++N) {
                I G = 0, K = anchor, P = 0, M = 0;
                for (int n = 2; n < N; ++n) G += pi[n] - q[n] - 1;
                int j = j0;
                for (int n = a; n < N; ++n) {
                    if (n == b[j + h]) j += h;
                    int c = b[j], t = std::min(N, b[j + h]);
                    K += pi[c] - q[c] - 1;
                    if (n > c) {
                        P += I(t-n)*prime[n];
                        M += I(t-n)*(q[n]-q[n-1]);
                    }
                }
                assert(G == K + P - M);
                assert(G*G == K*K+P*P+M*M+2*K*P-2*K*M-2*P*M);
                ++checks;
                bool special = (a == 5 && h == 2 && N == 8) ||
                    (a == 5 && h == 3 && N == 15) ||
                    (a == 194 && h == 3 && N == 512) ||
                    (a == 820 && h == 5 && N == 1024) ||
                    (a == 5 && h == 1 && (N == 512 || N == 1024 || N == 2048 || N == 4096));
                if (special) {
                    if (!first) out << ',';
                    first = false;
                    out << "{\"a\":" << a << ",\"h\":" << h << ",\"N\":" << N
                        << ",\"G\":" << G << ",\"K\":" << K << ",\"P\":" << P
                        << ",\"D\":" << M << ",\"anchor_G\":" << anchor << '}';
                }
            }
        }
    }
    int first_lag = 0, positive_lag = 0, positive_total = 0, max_X = 0;
    I max_C = -1000000000;
    for (int X = 128; X <= 8192; ++X) {
        int h = 1;
        while (I(h+1)*(h+1)*(h+1)*(h+1) <= X) ++h;
        int u = int(std::lower_bound(b.begin(), b.end(), X)-b.begin());
        int v = int(std::lower_bound(b.begin(), b.end(), 2*X)-b.begin())-1;
        I V = 0, D = 0, C = 0;
        std::vector<I> lags(h);
        for (int j = u; j <= v; ++j) {
            I sum = 0;
            for (int r = 0; r < h; ++r) {
                sum += e[j+r];
                D += I(e[j+r])*e[j+r];
                for (int s = r+1; s < h; ++s) lags[s-r] += I(e[j+r])*e[j+s];
            }
            V += sum*sum;
        }
        C = std::accumulate(lags.begin(), lags.end(), I(0));
        assert(V == D + 2*C);
        bool has_positive = std::any_of(lags.begin(), lags.end(), [](I z) { return z > 0; });
        if (has_positive) { ++positive_lag; if (!first_lag) first_lag = X; }
        if (C > 0) ++positive_total;
        if (C > max_C) { max_C = C; max_X = X; }
    }
    I halo[2][4] = {};
    for (int j = 1; j+3 < int(b.size()); ++j) {
        if (b[j] < 209 || b[j] >= 418) continue;
        for (int mode = 0; mode < 2; ++mode) {
            if (mode == 1 && b[j+3] > 418) continue;
            I count = 0;
            for (int n = b[j]+1; n <= b[j+3]; ++n) count += prime[n];
            halo[mode][0] += (count-3)*(count-3);
            for (int r = 0; r < 3; ++r) halo[mode][1] += e[j+r]*e[j+r];
            halo[mode][2] += e[j]*e[j+1]+e[j+1]*e[j+2];
            halo[mode][3] += e[j]*e[j+2];
        }
    }
    auto elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
    out << "],\"boundary\":{\"first_lag_X\":" << first_lag
        << ",\"positive_lag_scales\":" << positive_lag << ",\"positive_total_scales\":" << positive_total
        << ",\"max_C\":" << max_C << ",\"max_C_X\":" << max_X << "}"
        << ",\"halo_witness\":[[" << halo[0][0] << ',' << halo[0][1] << ',' << halo[0][2] << ',' << halo[0][3]
        << "],[" << halo[1][0] << ',' << halo[1][1] << ',' << halo[1][2] << ',' << halo[1][3] << "]]"
        << ",\"compression_checks\":" << checks << ",\"trial_primality_checks\":" << limit-1
        << ",\"elapsed_seconds\":" << elapsed << "}\n";
    std::cout << "Independent checks PASS; compression=" << checks << "; elapsed=" << elapsed << '\n';
}
```

### Executed Source: joh_boundary_test.py

```python
"""Post-development boundary falsification, with no larger Li domain."""

import bisect
import hashlib
import json
import time
from collections import Counter
from pathlib import Path
from math import isqrt

from joh_clock import clock, sieve


def main():
    started = time.perf_counter()
    q = [0, 0] + [int(x) for x in Path('floors.txt').read_text().splitlines()]
    b = clock(q)
    prime, pi = sieve(len(q) - 1)
    e = [pi[b[i+1]] - pi[b[i]] - 1 for i in range(len(b)-1)]
    cache = {}
    for h in range(3, 10):
        V = [0]
        D = [0]
        Cs = [[0] for _ in range(h-1)]
        for j in range(len(b)-h):
            V.append(V[-1] + (pi[b[j+h]] - pi[b[j]] - h)**2)
            D.append(D[-1] + sum(x*x for x in e[j:j+h]))
            for d in range(1, h):
                Cs[d-1].append(Cs[d-1][-1] + sum(e[i]*e[i+d] for i in range(j, j+h-d)))
        cache[h] = V, D, Cs
    first_lag = first_aggregate = strongest = None
    positive_total = 0
    positive_lag_scales = 0
    extrema = {d: [None, None] for d in range(1, 9)}
    # Frozen before this script's execution: exact 128..8192, same floor table.
    for X in range(128, 8193):
        h = isqrt(isqrt(X))
        u = bisect.bisect_left(b, X)
        v = bisect.bisect_left(b, 2*X)
        Vp, Dp, Cs = cache[h]
        V, D = Vp[v]-Vp[u], Dp[v]-Dp[u]
        lag = [C[v]-C[u] for C in Cs]
        assert V == D + 2*sum(lag)
        row = {'X': X, 'h': h, 'u': u, 'v': v-1, 'windows': v-u,
               'V': V, 'D': D, 'C_total': sum(lag), 'C': lag,
               'halo': b[v+h-1]}
        if any(C > 0 for C in lag):
            positive_lag_scales += 1
            if first_lag is None: first_lag = row
        if sum(lag) > 0:
            positive_total += 1
            if first_aggregate is None: first_aggregate = row
        if strongest is None or row['C_total'] > strongest['C_total']:
            strongest = row
        for d, C in enumerate(lag, 1):
            a, z = extrema[d]
            if a is None or C < a['C']: extrema[d][0] = {'X': X, 'h': h, 'C': C}
            if z is None or C > z['C']: extrema[d][1] = {'X': X, 'h': h, 'C': C}
    out = {'domain': [128,8192], 'scales': 8065, 'first_lag': first_lag,
           'first_aggregate': first_aggregate, 'max_aggregate': strongest,
           'positive_total_scales': positive_total,
           'positive_lag_scales': positive_lag_scales, 'lag_extrema': extrema,
           'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'elapsed_seconds': time.perf_counter()-started}
    Path('boundary_results.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
```

### Executed Source: joh_audit.py

```python
"""Compare independent reconstructions and emit a small exact lag witness."""

import hashlib
import json
from pathlib import Path
from math import isqrt

from joh_clock import S, certify_floors, clock, sieve


def main():
    py = json.loads(Path('joh_results.json').read_text())
    cpp = json.loads(Path('cpp_results.json').read_text())
    scan = json.loads(Path('boundary_results.json').read_text())
    checked = 0
    for a, b in zip(py['rows'], cpp['rows'], strict=True):
        for key in ('X', 'h', 'windows', 'V', 'D', 'C_total', 'prime_diagonal', 'prime_off'):
            assert a[key] == b[key], (key, a, b)
            checked += 1
        for c, d in zip(a['lags'], b['lags'], strict=True):
            for key in ('d', 'C', 'surplus_surplus', 'empty_empty', 'opposite'):
                assert c.get(key, 0) == d[key], (key, c, d)
                checked += 1
    assert py['compression_checks'] == cpp['compression_checks'] == 56360
    for a in py['fixtures']:
        b = next(b for b in cpp['fixtures'] if all(a[k] == b[k] for k in ('a','h','N')))
        for k in ('G','K','P','D','anchor_G'):
            assert a[k] == b[k]
            checked += 1
    assert cpp['boundary']['first_lag_X'] == scan['first_lag']['X'] == 209
    assert cpp['boundary']['positive_lag_scales'] == scan['positive_lag_scales'] == 7571
    assert cpp['boundary']['positive_total_scales'] == scan['positive_total_scales'] == 0
    assert cpp['boundary']['max_C_X'] == scan['max_aggregate']['X'] == 147
    assert cpp['boundary']['max_C'] == scan['max_aggregate']['C_total'] == -7
    expected = [(18,73,158,-438,225), (26,166,500,-1328,688),
                (69,301,944,-2408,1232), (305,683,2952,-6830,3500),
                (533,1531,8158,-18372,9216)]
    for row, vals in zip(py['rows'][:5], expected, strict=True):
        assert tuple(row[k] for k in ('V','prime_diagonal','prime_off','prime_model','model_square')) == vals
    q = [0,0] + [int(x) for x in Path('floors.txt').read_text().splitlines()]
    b = clock(q)
    prime, pi = sieve(len(q)-1)
    for n in range(2,len(q)):
        assert bool(prime[n]) == all(n % d for d in range(2,isqrt(n)+1))
    e = [pi[b[i+1]]-pi[b[i]]-1 for i in range(len(b)-1)]
    witness = []
    points = {208,209,210,417,418}
    for j in range(51,88):
        z = e[j]*e[j+2]
        if z:
            cells = [b[j], b[j+1], b[j+2], b[j+3]]
            points.update(n for c in cells for n in (c-1,c))
            witness.append({'j': j, 'cells': cells, 'e': [e[j],e[j+2]],
                            'product': z,
                            'primes_left': [p for p in range(cells[0]+1,cells[1]+1) if prime[p]],
                            'primes_right': [p for p in range(cells[2]+1,cells[3]+1) if prime[p]]})
    assert sum(row['product'] for row in witness) == 1
    # Independently materialize the requested LC4 coordinates from Python's source.
    lc4 = []
    for N in (512,1024,2048,4096):
        G = sum(pi[n]-q[n]-1 for n in range(2,N))
        U = E = 0
        for j in range(2,len(b)-1):
            if b[j] >= N: break
            c,t = b[j],min(N,b[j+1])
            U += (t-c)*(pi[c]-q[c]-1)
            E += sum(t-p for p in range(c+1,t) if prime[p])
        assert G == U+E
        row = next(x for x in cpp['fixtures'] if x['a']==5 and x['h']==1 and x['N']==N)
        assert (G,U,E) == (row['G'],row['K'],row['P'])
        lc4.append({'N':N,'G':G,'U':U,'E_place':E})
    smallq, bounds, _, _ = certify_floors(max(points))
    assert smallq[2:] == q[2:len(smallq)]
    class_totals = {'surplus_surplus':0,'empty_empty':0,'opposite':0}
    for row in witness:
        a,c = row['e']
        key = 'surplus_surplus' if a>0 and c>0 else 'empty_empty' if a<0 and c<0 else 'opposite'
        class_totals[key] += row['product']
    halo_rows = []
    for trim in (False,True):
        J = [j for j,n in enumerate(b) if 209 <= n < 418 and (not trim or b[j+3] <= 418)]
        V = sum((pi[b[j+3]]-pi[b[j]]-3)**2 for j in J)
        D = sum(sum(e[j+r]**2 for r in range(3)) for j in J)
        C1 = sum(e[j]*e[j+1]+e[j+1]*e[j+2] for j in J)
        C2 = sum(e[j]*e[j+2] for j in J)
        halo_rows.append([V,D,C1,C2])
    assert halo_rows == cpp['halo_witness'] == [[23,47,-13,1],[21,39,-8,-1]]
    assert q[415] == 86 and q[416] == 87 and b[90] == 434
    before = [j for j,n in enumerate(b) if 208 <= n < 416]
    assert (before[0],before[-1]) == (51,86)
    assert sum(e[j]*e[j+2] for j in before) == 0
    files = ('joh_clock.py','joh_verify.cpp','joh_boundary_test.py','joh_audit.py')
    out = {'independent_field_checks':checked, 'all_comparisons':'PASS',
           'smallest_lag_witness_in_128_8192':witness,
           'witness_class_totals':class_totals,'LC4':lc4,'halo_witness':halo_rows,
           'sieve_vs_trial_flags_checked':len(q)-2,
           'source_hashes':{f:hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in files},
           'small_witness_floor_scale':str(S),
           'small_witness_floors':{str(n):{'Q':q[n],'lo':str(bounds[n][0]),'hi':str(bounds[n][1])}
                                   for n in sorted(points)}}
    Path('audit_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='small_witness_floors'},indent=2))


if __name__ == '__main__':
    main()
```

### Complete Audit Output And Minimal Floor Certificate

```json
{
  "environment_and_precision": {
    "environment": "3.12.14",
    "limit": 16640,
    "scale": "340282366920938463463374607431768211456",
    "log_terms": 48,
    "floor_max_width": "1.1820665287790296613941555728695E-7",
    "floor_min_margin": "8.2788088501359898850481962541418E-7",
    "floors_sha256": "df1a6bdff4cedb3d2195766677edcc3ebbe45d01673124ee0133b4a85b655892",
    "ei_diagnostic_precision": 60,
    "ei_checks": 16639,
    "compression_checks": 56360,
    "elapsed_seconds": 7.597195517000046
  },
  "independent_cpp": {
    "rows": [
      {
        "X": 128,
        "h": 3,
        "windows": 25,
        "V": 18,
        "D": 34,
        "C_total": -8,
        "prime_diagonal": 73,
        "prime_off": 158,
        "lags": [
          {
            "d": 1,
            "C": -6,
            "surplus_surplus": 2,
            "empty_empty": 2,
            "opposite": -10
          },
          {
            "d": 2,
            "C": -2,
            "surplus_surplus": 0,
            "empty_empty": 1,
            "opposite": -3
          }
        ]
      },
      {
        "X": 256,
        "h": 4,
        "windows": 43,
        "V": 26,
        "D": 58,
        "C_total": -16,
        "prime_diagonal": 166,
        "prime_off": 500,
        "lags": [
          {
            "d": 1,
            "C": -14,
            "surplus_surplus": 0,
            "empty_empty": 3,
            "opposite": -17
          },
          {
            "d": 2,
            "C": 0,
            "surplus_surplus": 4,
            "empty_empty": 2,
            "opposite": -6
          },
          {
            "d": 3,
            "C": -2,
            "surplus_surplus": 0,
            "empty_empty": 1,
            "opposite": -3
          }
        ]
      },
      {
        "X": 512,
        "h": 4,
        "windows": 77,
        "V": 69,
        "D": 151,
        "C_total": -41,
        "prime_diagonal": 301,
        "prime_off": 944,
        "lags": [
          {
            "d": 1,
            "C": -24,
            "surplus_surplus": 3,
            "empty_empty": 9,
            "opposite": -36
          },
          {
            "d": 2,
            "C": -12,
            "surplus_surplus": 6,
            "empty_empty": 4,
            "opposite": -22
          },
          {
            "d": 3,
            "C": -5,
            "surplus_surplus": 2,
            "empty_empty": 2,
            "opposite": -9
          }
        ]
      },
      {
        "X": 1024,
        "h": 5,
        "windows": 140,
        "V": 305,
        "D": 415,
        "C_total": -55,
        "prime_diagonal": 683,
        "prime_off": 2952,
        "lags": [
          {
            "d": 1,
            "C": -28,
            "surplus_surplus": 32,
            "empty_empty": 32,
            "opposite": -92
          },
          {
            "d": 2,
            "C": -12,
            "surplus_surplus": 24,
            "empty_empty": 30,
            "opposite": -66
          },
          {
            "d": 3,
            "C": -18,
            "surplus_surplus": 12,
            "empty_empty": 16,
            "opposite": -46
          },
          {
            "d": 4,
            "C": 3,
            "surplus_surplus": 9,
            "empty_empty": 11,
            "opposite": -17
          }
        ]
      },
      {
        "X": 2048,
        "h": 6,
        "windows": 256,
        "V": 533,
        "D": 957,
        "C_total": -212,
        "prime_diagonal": 1531,
        "prime_off": 8158,
        "lags": [
          {
            "d": 1,
            "C": -105,
            "surplus_surplus": 71,
            "empty_empty": 75,
            "opposite": -251
          },
          {
            "d": 2,
            "C": -81,
            "surplus_surplus": 56,
            "empty_empty": 76,
            "opposite": -213
          },
          {
            "d": 3,
            "C": -3,
            "surplus_surplus": 60,
            "empty_empty": 78,
            "opposite": -141
          },
          {
            "d": 4,
            "C": -34,
            "surplus_surplus": 36,
            "empty_empty": 34,
            "opposite": -104
          },
          {
            "d": 5,
            "C": 11,
            "surplus_surplus": 26,
            "empty_empty": 25,
            "opposite": -40
          }
        ]
      },
      {
        "X": 4096,
        "h": 8,
        "windows": 471,
        "V": 1550,
        "D": 2202,
        "C_total": -326,
        "prime_diagonal": 3712,
        "prime_off": 27086,
        "lags": [
          {
            "d": 1,
            "C": -158,
            "surplus_surplus": 186,
            "empty_empty": 217,
            "opposite": -561
          },
          {
            "d": 2,
            "C": -118,
            "surplus_surplus": 165,
            "empty_empty": 186,
            "opposite": -469
          },
          {
            "d": 3,
            "C": 28,
            "surplus_surplus": 155,
            "empty_empty": 188,
            "opposite": -315
          },
          {
            "d": 4,
            "C": -48,
            "surplus_surplus": 132,
            "empty_empty": 132,
            "opposite": -312
          },
          {
            "d": 5,
            "C": 27,
            "surplus_surplus": 105,
            "empty_empty": 123,
            "opposite": -201
          },
          {
            "d": 6,
            "C": -61,
            "surplus_surplus": 38,
            "empty_empty": 61,
            "opposite": -160
          },
          {
            "d": 7,
            "C": 4,
            "surplus_surplus": 26,
            "empty_empty": 35,
            "opposite": -57
          }
        ]
      },
      {
        "X": 8192,
        "h": 9,
        "windows": 872,
        "V": 2456,
        "D": 5128,
        "C_total": -1336,
        "prime_diagonal": 7842,
        "prime_off": 65138,
        "lags": [
          {
            "d": 1,
            "C": -830,
            "surplus_surplus": 356,
            "empty_empty": 495,
            "opposite": -1681
          },
          {
            "d": 2,
            "C": -328,
            "surplus_surplus": 490,
            "empty_empty": 442,
            "opposite": -1260
          },
          {
            "d": 3,
            "C": 198,
            "surplus_surplus": 544,
            "empty_empty": 408,
            "opposite": -754
          },
          {
            "d": 4,
            "C": -136,
            "surplus_surplus": 280,
            "empty_empty": 358,
            "opposite": -774
          },
          {
            "d": 5,
            "C": -65,
            "surplus_surplus": 260,
            "empty_empty": 283,
            "opposite": -608
          },
          {
            "d": 6,
            "C": -182,
            "surplus_surplus": 162,
            "empty_empty": 188,
            "opposite": -532
          },
          {
            "d": 7,
            "C": 23,
            "surplus_surplus": 150,
            "empty_empty": 157,
            "opposite": -284
          },
          {
            "d": 8,
            "C": -16,
            "surplus_surplus": 71,
            "empty_empty": 67,
            "opposite": -154
          }
        ]
      }
    ],
    "fixtures": [
      {
        "a": 5,
        "h": 1,
        "N": 512,
        "G": -2595,
        "K": -2808,
        "P": 213,
        "D": 0,
        "anchor_G": 0
      },
      {
        "a": 5,
        "h": 1,
        "N": 1024,
        "G": -6703,
        "K": -7134,
        "P": 431,
        "D": 0,
        "anchor_G": 0
      },
      {
        "a": 5,
        "h": 1,
        "N": 2048,
        "G": -16599,
        "K": -17485,
        "P": 886,
        "D": 0,
        "anchor_G": 0
      },
      {
        "a": 5,
        "h": 1,
        "N": 4096,
        "G": -42284,
        "K": -44049,
        "P": 1765,
        "D": 0,
        "anchor_G": 0
      },
      {
        "a": 5,
        "h": 2,
        "N": 8,
        "G": -1,
        "K": 0,
        "P": 1,
        "D": 2,
        "anchor_G": 0
      },
      {
        "a": 5,
        "h": 3,
        "N": 15,
        "G": -9,
        "K": -10,
        "P": 9,
        "D": 8,
        "anchor_G": 0
      },
      {
        "a": 194,
        "h": 3,
        "N": 512,
        "G": -2595,
        "K": -2753,
        "P": 471,
        "D": 313,
        "anchor_G": -675
      },
      {
        "a": 820,
        "h": 5,
        "N": 1024,
        "G": -6703,
        "K": -6773,
        "P": 478,
        "D": 408,
        "anchor_G": -4938
      }
    ],
    "boundary": {
      "first_lag_X": 209,
      "positive_lag_scales": 7571,
      "positive_total_scales": 0,
      "max_C": -7,
      "max_C_X": 147
    },
    "halo_witness": [
      [
        23,
        47,
        -13,
        1
      ],
      [
        21,
        39,
        -8,
        -1
      ]
    ],
    "compression_checks": 56360,
    "trial_primality_checks": 16639,
    "elapsed_seconds": 0.384958
  },
  "all_integer_boundary_scan": {
    "domain": [
      128,
      8192
    ],
    "scales": 8065,
    "first_lag": {
      "X": 209,
      "h": 3,
      "u": 51,
      "v": 87,
      "windows": 37,
      "V": 23,
      "D": 47,
      "C_total": -12,
      "C": [
        -13,
        1
      ],
      "halo": 434
    },
    "first_aggregate": null,
    "max_aggregate": {
      "X": 147,
      "h": 3,
      "u": 39,
      "v": 66,
      "windows": 28,
      "V": 28,
      "D": 42,
      "C_total": -7,
      "C": [
        -6,
        -1
      ],
      "halo": 310
    },
    "positive_total_scales": 0,
    "positive_lag_scales": 7571,
    "lag_extrema": {
      "1": [
        {
          "X": 7811,
          "h": 9,
          "C": -868
        },
        {
          "X": 128,
          "h": 3,
          "C": -6
        }
      ],
      "2": [
        {
          "X": 8102,
          "h": 9,
          "C": -334
        },
        {
          "X": 4941,
          "h": 8,
          "C": 14
        }
      ],
      "3": [
        {
          "X": 878,
          "h": 5,
          "C": -29
        },
        {
          "X": 7684,
          "h": 9,
          "C": 217
        }
      ],
      "4": [
        {
          "X": 7840,
          "h": 9,
          "C": -199
        },
        {
          "X": 625,
          "h": 5,
          "C": 11
        }
      ],
      "5": [
        {
          "X": 8034,
          "h": 9,
          "C": -68
        },
        {
          "X": 2440,
          "h": 7,
          "C": 38
        }
      ],
      "6": [
        {
          "X": 8189,
          "h": 9,
          "C": -182
        },
        {
          "X": 2686,
          "h": 7,
          "C": -13
        }
      ],
      "7": [
        {
          "X": 6123,
          "h": 8,
          "C": -17
        },
        {
          "X": 8034,
          "h": 9,
          "C": 39
        }
      ],
      "8": [
        {
          "X": 6561,
          "h": 9,
          "C": -23
        },
        {
          "X": 7493,
          "h": 9,
          "C": 9
        }
      ]
    },
    "source_sha256": "a72ea96e08e3ccce92f9b6040689ac41a039b5d85f6e838f957f4c8119204f6b",
    "elapsed_seconds": 0.06379309499993724
  },
  "audit_and_minimal_exact_floor_certificate": {
    "independent_field_checks": 236,
    "all_comparisons": "PASS",
    "smallest_lag_witness_in_128_8192": [
      {
        "j": 61,
        "cells": [
          265,
          271,
          276,
          282
        ],
        "e": [
          1,
          1
        ],
        "product": 1,
        "primes_left": [
          269,
          271
        ],
        "primes_right": [
          277,
          281
        ]
      },
      {
        "j": 67,
        "cells": [
          299,
          305,
          310,
          316
        ],
        "e": [
          -1,
          1
        ],
        "product": -1,
        "primes_left": [],
        "primes_right": [
          311,
          313
        ]
      },
      {
        "j": 69,
        "cells": [
          310,
          316,
          322,
          328
        ],
        "e": [
          1,
          -1
        ],
        "product": -1,
        "primes_left": [
          311,
          313
        ],
        "primes_right": []
      },
      {
        "j": 86,
        "cells": [
          410,
          416,
          422,
          428
        ],
        "e": [
          -1,
          -1
        ],
        "product": 1,
        "primes_left": [],
        "primes_right": []
      },
      {
        "j": 87,
        "cells": [
          416,
          422,
          428,
          434
        ],
        "e": [
          1,
          1
        ],
        "product": 1,
        "primes_left": [
          419,
          421
        ],
        "primes_right": [
          431,
          433
        ]
      }
    ],
    "witness_class_totals": {
      "surplus_surplus": 2,
      "empty_empty": 1,
      "opposite": -2
    },
    "LC4": [
      {
        "N": 512,
        "G": -2595,
        "U": -2808,
        "E_place": 213
      },
      {
        "N": 1024,
        "G": -6703,
        "U": -7134,
        "E_place": 431
      },
      {
        "N": 2048,
        "G": -16599,
        "U": -17485,
        "E_place": 886
      },
      {
        "N": 4096,
        "G": -42284,
        "U": -44049,
        "E_place": 1765
      }
    ],
    "halo_witness": [
      [
        23,
        47,
        -13,
        1
      ],
      [
        21,
        39,
        -8,
        -1
      ]
    ],
    "sieve_vs_trial_flags_checked": 16639,
    "source_hashes": {
      "joh_clock.py": "6af10a960d5e92f93fd0fd72b4daac542f4f36dd3be1669e471840fd48865ba7",
      "joh_verify.cpp": "9de4d2cff7f1d01c2c97b453e3599e8bc8f6e84c15f4b42900040b4f6ce77f78",
      "joh_boundary_test.py": "a72ea96e08e3ccce92f9b6040689ac41a039b5d85f6e838f957f4c8119204f6b",
      "joh_audit.py": "26fb2353469e6ae31c700bfd84ec7de335b23885c38014bd8a0853e3aba7ad2b"
    },
    "small_witness_floor_scale": "340282366920938463463374607431768211456",
    "small_witness_floors": {
      "208": {
        "Q": 50,
        "lo": "17235752169100639885310824778226521006372",
        "hi": "17235752208473488638222867732662617913002"
      },
      "209": {
        "Q": 50,
        "lo": "17299476201943273682221549793547545726930",
        "hi": "17299476241328305342061080572925414263120"
      },
      "210": {
        "Q": 51,
        "lo": "17363143187655150054433588069033202825714",
        "hi": "17363143227052133123624164023269987447672"
      },
      "264": {
        "Q": 60,
        "lo": "20725437900379077173452651929479745614662",
        "hi": "20725437940187250023732742994290045430808"
      },
      "265": {
        "Q": 61,
        "lo": "20786444013844642043881440442896082109155",
        "hi": "20786444053657509385680018553884492467413"
      },
      "270": {
        "Q": 61,
        "lo": "21090860090791370372910449833307738701858",
        "hi": "21090860130626679172693420219050778366506"
      },
      "271": {
        "Q": 62,
        "lo": "21151621855201096138793907516604081105914",
        "hi": "21151621895040695846641496155377327485504"
      },
      "275": {
        "Q": 62,
        "lo": "21394270800017656243532173766448841903320",
        "hi": "21394270839873801125401606272974991014363"
      },
      "276": {
        "Q": 63,
        "lo": "21454834492263072133364707714805999848367",
        "hi": "21454834532123204265456316370408088295658"
      },
      "281": {
        "Q": 63,
        "lo": "21757071298612292795176179984445764133197",
        "hi": "21757071338491519391579250542298786665429"
      },
      "282": {
        "Q": 64,
        "lo": "21817403642408493096967377757441435321932",
        "hi": "21817403682291377148329935457816255067232"
      },
      "298": {
        "Q": 66,
        "lo": "22777685304227019000071282115316628290874",
        "hi": "22777685344161978315351408619566596468602"
      },
      "299": {
        "Q": 67,
        "lo": "22837396857535145291152895159348563870577",
        "hi": "22837396897472996213050291121737442198663"
      },
      "304": {
        "Q": 67,
        "lo": "23135432413636315184657138559547808317014",
        "hi": "23135432453588059366448111259506189387395"
      },
      "305": {
        "Q": 68,
        "lo": "23194936168585529312592358393171474969521",
        "hi": "23194936208539943486209329817573053525455"
      },
      "309": {
        "Q": 68,
        "lo": "23432611726937438786398857983780839156446",
        "hi": "23432611766902190093637075765814259658883"
      },
      "310": {
        "Q": 69,
        "lo": "23491946493862957230559617297879434045612",
        "hi": "23491946533830209864092380953625845409210"
      },
      "315": {
        "Q": 69,
        "lo": "23788122862994078885538657714836978387617",
        "hi": "23788122902973366492203510185216053549071"
      },
      "316": {
        "Q": 70,
        "lo": "23847259640250138528426242847033481893855",
        "hi": "23847259680231742260393779722213534940606"
      },
      "321": {
        "Q": 70,
        "lo": "24142458696950524194558902727012251071376",
        "hi": "24142458736943279898920886991049300446915"
      },
      "322": {
        "Q": 71,
        "lo": "24201402494576112628606034354269392958806",
        "hi": "24201402534571016084990239097763897064996"
      },
      "327": {
        "Q": 71,
        "lo": "24495648730187594972195613448724773860674",
        "hi": "24495648770192846918307773023490293364490"
      },
      "328": {
        "Q": 72,
        "lo": "24554404337448940650108593625827224841465",
        "hi": "24554404377456187000767576416724837923416"
      },
      "409": {
        "Q": 85,
        "lo": "29220751459270078556902278410123831783771",
        "hi": "29220751499382211961976382497168057912037"
      },
      "410": {
        "Q": 86,
        "lo": "29277324352904770711486627089224495470265",
        "hi": "29277324393017719029163333250954307336855"
      },
      "415": {
        "Q": 86,
        "lo": "29559846339825551496686516750220863312789",
        "hi": "29559846379942457457012611440870802671752"
      },
      "416": {
        "Q": 87,
        "lo": "29616282755157582852190171478541433707445",
        "hi": "29616282795275257609869301490945339402254"
      },
      "417": {
        "Q": 87,
        "lo": "29672696679247100629870866165875300123541",
        "hi": "29672696719365536819232964167338066545223"
      },
      "418": {
        "Q": 87,
        "lo": "29729088183885111779688292840245314060898",
        "hi": "29729088224004302123063370418642375349910"
      },
      "421": {
        "Q": 87,
        "lo": "29898128892909861709290637942767281747421",
        "hi": "29898128933031271709931380779243299694376"
      },
      "422": {
        "Q": 88,
        "lo": "29954431429554469065308170726802609546094",
        "hi": "29954431469676604964422035678015263628095"
      },
      "427": {
        "Q": 88,
        "lo": "30235614496777562992187740605142131283401",
        "hi": "30235614536903227139754587283730378241111"
      },
      "428": {
        "Q": 89,
        "lo": "30291785667399671268057137822970230926211",
        "hi": "30291785707526021366106827706058443609451"
      },
      "433": {
        "Q": 89,
        "lo": "30572318018380237879718403044950576152090",
        "hi": "30572318058509923373931634767044915591389"
      },
      "434": {
        "Q": 90,
        "lo": "30628360252803706751997263331957026835180",
        "hi": "30628360292934040959329522526862296955301"
      }
    }
  }
}
```


### Verified Publication Receipt - 20261105-census-2

Execution COMPLETE for the declared finite domain. At 2026-11-06 00:22:23 UTC,
the full substantive report was re-fetched from immutable commit
**57c35707817bb34e1b859d67f8c331f4acb87ea4**, blob **c1f269b08cf3f0688471897a085dfcf0d6b73309**, and matched the submitted
**138844-character** content exactly. The commit changed ONLY
research/agent_reports/2026-11-05/40-prime-census.md on agent-reports.
All 64294 characters of the prior report and checkpoint were preserved as
an exact prefix. The preregistration was separately published and read back
before the experiment at 07d4288a97b6097f32411004d6db51398e4d11e4.

JL1-JL4 remain FINITE_COMPUTATION, with the stated local sign rule REFUTED.
JOH-AGG remains CONJECTURE; JL5's conditional budget is PAPER_PROOF /
SELF_AUDIT, not an upper estimate for the missing source. Independent
Referee review and Lean certification of the new findings remain PENDING.
No new exponent gain or RH proof is claimed.

Only the authorized own report was changed remotely. Source, policy,
other reports, proof branches, PRs, issues, workflows, schedules, and main
were not modified; no agent was launched. The downloadable standalone
report contains this invocation's full source and certificates.
