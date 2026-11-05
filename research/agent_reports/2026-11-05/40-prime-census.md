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
