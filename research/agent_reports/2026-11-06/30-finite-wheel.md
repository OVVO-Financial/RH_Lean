# RH | Finite Wheel & Incidence - 2026-11-06

## Result Summary (Final)

**PAPER_PROOF / INDEPENDENT_REVIEW_PENDING.** A new explicit cross-root comparison shows that the full original CORR4 mixed bill retains control of the corresponding weighted Mertens energy after all square-sampling, historical-prefix and diagonal costs are paid. A fixed daughter's integrated cap defect has a related bound. These are structural comparisons and precisely scoped limitations of an averaging strategy, **not a new upper estimate, exponent improvement or RH proof**. Exact source checks and false-transfer certificates passed. The complete proofs, limitations and executable verifier are below.

## Early CORR4 Checkpoint - 20261106-wheel-1

**PARTIAL / IN_PROGRESS. No new theorem is asserted at this checkpoint.**

Actual invocation: SCHEDULED, 2026-11-06T02:05:01-05:00, America/New_York; RUN_ID_UNAVAILABLE. Authority verified at main **4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a**, tree **48b193cd105e21183b1cfd68b059894c8056f35c**. AGENTS blob **547dda0d9456e7a4e1165dc72d59da6f70d5c023**; proof-contract blob **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**; current routing policy **ffd8f1c65cc4da656174956d4e03b48bea46768b**.

deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1. Selected route **CORR4**, following the actual November 5 CORR4 / FINITE-AC / MU-LIFT rotation. No other agent is launched. The next distinct protected route is FINITE-AC.

### Structural Question

Resume Wheel 20261105-wheel-1/F1-F4, Census 20261105-census-1's joint R=57/58 caps, and Coordinator C53-C56. Fixed-label per-root relaxation countermodels already survive every sub-square-root prime rule and a sublinear whole-prefix envelope. Do not rerun or relabel that construction.

Investigate instead the common sequence across roots. For genuine Mertens prefixes,

```text
X_R=R^2-1; S_R={odd prime q:q^2<R};
m_R=M(R-1); G_R=M(X_R)-m_R; d_q(R)=M(floor(X_R/q^2));
H_R=sum_(R<=n<=X_R)mu(n)^2
    +2 sum_(q in S_R) q^(-1)sum_(R<=n<=floor(X_R/q^2))mu(n)^2;
B_R=G_R^2-H_R+sum_(q in S_R)(2G_R*d_q(R)/q-2d_q(R)^2).
```

Test whether the exact square dilation and its occurrence multiplicities force a nontrivial WEIGHTED CROSS-ROOT cap defect, or a coercive comparison for the entire B_R. Preserve the historical prefix, strict moving q^2<R mask, all daughters, all mixed terms, and finite lower/upper boundaries. An integrated comparison is not a pointwise estimate or a new endpoint bound.

Preregistered development: exact source reconstruction at R=56..128, held-out 129..256 and 317/1027; strict activation R=q^2 and q^2+1; integer dilation equalities on q-multiple roots; exact rational finite weighted tests at exponents with rational antiderivatives. Genuine Mobius and explicitly synthetic coherent controls remain distinct. No unchanged large wheel scan or exponent fit.

### Continuity And Formal State

Reports pinned at **aa215fa54489b8662a551dfe0296ba33b14b66c5**. Today Owner and Analytic are available. Coordinator, Census, Referee and Lean: **TODAY=PENDING / YESTERDAY=CARRY_FORWARD**. Yesterday's own three invocations were retrieved. External inbox blob **038018145c0fddb2f6306c0712373adf9cd1ea52** has no entry after October 18; its scope safeguards persist, its old routing/cadence does not.

Today Owner BT1-BT2 reclassifies old OPEN-SAT-I at paper scope using inherited input; RZ1-RZ3 retain the genuine floor response. Today Analytic FP1-FP5 preserves the constant parent and prime-square birth under frequency averaging. Neither is a new CORR4 signed supplier. These new claims remain independently review-pending.

PR #1096 is now human-merged at current main; open/draft collection is empty. The exact finite cancellation source was retrieved (blob **3cbc5159536d6b9e5000f74c5bd018bd2d62daf1**). Previous exact-head CI/axiom evidence is carried forward until directly checked; its finite theorem is not a new summatory estimate.

### Pending Work

Proof, falsification, novelty search, complete return, precise missing inequality, source/evidence ledger and final resume capsule are PENDING. eta_gate **SEARCH_BROAD**; net new endpoint gain **UNKNOWN**. The canonical VF von-Koch objective and RH remain OPEN.


## Final CORR4 Synthesis - 20261106-wheel-1

This completes the actual scheduled invocation begun **2026-11-06T02:05:01-05:00**, America/New_York; RUN_ID_UNAVAILABLE. It is not a second invocation. New results below are **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. The executed checks are **FINITE_COMPUTATION**, not proofs of the all-scale inequalities. The early checkpoint is preserved above.

### A. Most Important Structural Discovery

**The complete original CORR4 mixed bill cannot become uniformly bounded merely through signed averaging across square roots while the corresponding weighted Mertens energy diverges.** The common arithmetic prefix imposes a quantitative restriction absent from the previously studied independent-per-root relaxations.

For every beta>=1/2 and every finite T>=3135, the literal sampled bill satisfies the fully explicit comparison

```text
E_beta(T)/36 - E_beta(3135) - 1300 J_beta(3135,T)
  <= W_beta(T)
  <= integral_(3135)^T |B_floor(sqrt(x+1))| x^(-1-2 beta) dx
  <= 3 E_beta(T) + 57 J_beta(3135,T),                 (CP2)

E_beta(T)=integral_1^T M(floor x)^2 x^(-1-2 beta) dx,
W_beta(T)=integral_(3135)^T B_floor(sqrt(x+1)) x^(-1-2 beta) dx,
J_beta(a,T)=integral_a^T x^(-2 beta) dx.
```

For beta>1/2 the J term is uniformly bounded. Consequently bounded-above signed W prefixes, absolute integrability of this original sampled bill, and finite E_beta(infinity) are equivalent. If E diverges, W actually tends to positive infinity. This is a **source-specific weighted-energy equivalence and method limitation**, not an independently proved upper estimate or a new Mertens exponent.

A single fixed daughter also has a cross-root restriction. If q is an odd prime and q^(2 beta-1)>2, its integrated continuous-cap defect controls E_beta, with all history and square-rounding costs explicit in CP3. For example q=5 works at beta=3/4. This does not assert a positive cap gap at every root or refute yesterday's per-root constructions.

The mechanism is exact integer square geometry plus one coherent bounded-step prefix. It does **not** uncover a new unique-factorization cancellation theorem: the norm argument also works for coherent bounded real coefficients with their corresponding diagonal. Its useful new content is the quantified transfer to the original moving CORR4 carrier and the resulting restriction on an averaging proposal. The generic dilation and Hilbert-space inequalities are standard, not claimed as new mathematics.

| Claim | Actual scope | Status |
| --- | --- | --- |
| CP1 | Original-source square sampling, strict-mask rounding bounds, exact q-multiple-root identification | PAPER_PROOF; elementary enabling comparison |
| CP2 | Uniform finite weighted coercivity for the complete mixed bill | PAPER_PROOF; structural comparison, not an upper supplier |
| CP3 | One-daughter integrated cap-defect control; qualified anchored-cap consequence | PAPER_PROOF; fixed q and explicit exponent condition |
| CP4 | Weighted boundedness equivalences and narrowly scoped averaging obstruction | TARGET_EQUIVALENT reformulation with proved comparison |
| CP5 | Physical reconstruction, boundary checks and two false-transfer certificates | FINITE_COMPUTATION |

eta_gate: **SEARCH_BROAD**. Net new endpoint gain: **UNKNOWN / NONE ESTABLISHED**.

### B. Current Authoritative Objective

Pinned main: **4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a**, tree **48b193cd105e21183b1cfd68b059894c8056f35c**. Main was retrieved at the start, not inferred from a report. The public arithmetic goal remains

```text
VFCanonicalSquareVonKochStatement:
exists C>=0, forall integers R>=2,
  |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R.
```

The canonical goal is OPEN. Its compiled classical RH consumer explicitly takes `ClassicalVonKochRHCriterion`; the VF-to-Li coordinate theorem is not an actual-prime bound.

Deployment acknowledgement: **NO_PIGEONHOLING_ROUTE_SELECTOR_V1**, policy blob **ffd8f1c65cc4da656174956d4e03b48bea46768b**. The current breadth, complete-return, engine, role, multi-run and dynamic-protocol instructions were retrieved. This is the due **CORR4** turn after November 5 FINITE-AC and MU-LIFT, not a new common campaign. FINITE-AC is next.

The live declaration `native_mertens_fixed_strict_power` states an inherited positive fixed gap below 7/8. It was read at blob **b33a4883e1ddb0551b0f11f062bce46680d87450**; its whole analytic dependency chain was not rebuilt in this run. That existing result is neither withdrawn nor credited as today's gain. CP1-CP2 and the continuous-cap CP3 use no such input. Only the separately labeled anchored-lattice corollary uses a sublinear envelope.

### C. Structural Mechanism Investigated

Wheel F2-F3 and Coordinator C53-C56 already permit prescribed fixed-label daughter caps in different functions f_R at each root, even under strong local prime rules. Census's genuine R=57/58 joint restrictions give small-root gaps, not a uniform estimate. Repeating those scans would not test a new mechanism.

This invocation instead asks what changes when every root uses the SAME Mertens prefix. Two complementary calculations were pursued on that one source:

1. A prime-square daughter is a dilation of the common prefix, up to a controlled sample-and-hold error. Its weighted norm has the factor q^(-2 beta), and its squared norm has q^(-4 beta).
2. The entire mixed bill contains a parent square whose coefficient exceeds the maximum weighted daughter and mixed losses. This gives a lower comparison, not the desired upper comparison.

The first careless version would have identified the native square-sampled daughter with an exact continuous dilation. CP5 refutes that transfer by a coherent two-site example. The repaired argument explicitly retains the rounding, history and finite lower boundary, using the strict q^2<R mask to absorb the rounding unit.

### D. Exact Statements And Original Carrier

#### D0. The actual mixed bill

For integer R>=56, use the genuine Mobius function throughout:

```text
X_R=R^2-1; S_R={odd primes q:q^2<R}; Y_q=floor(X_R/q^2);
m_R=M(R-1); G_R=M(X_R)-m_R; d_q(R)=M(Y_q);
V_0(R)=sum_(R<=n<=X_R)mu(n)^2;
V_q(R)=sum_(R<=n<=Y_q)mu(n)^2;
H_R=V_0(R)+2 sum_(q in S_R)V_q(R)/q;
U_R=sum_(q in S_R)d_q(R)/q; Dchild_R=sum_(q in S_R)d_q(R)^2;

B_R=2 lowOwnerPrefixTailMixedRawCellMass(R)-2 Dchild_R
   =G_R^2+2 G_R U_R-2 Dchild_R-H_R.                 (D0)
```

Here H_R is the full physical diagonal minus the reciprocal-prefix diagonal, NOT a new historical budget. In site notation t(n)=1_[R,X_R](n) and a(n)=sum_(q in S_R)1_(n<=Y_q)/q, it is exactly sum_(n<=X_R)(t+2ta)mu(n)^2. Both mixed orientations and tail/tail remain.

This B_R is the complete **mixed-tail bill** consumed by the live CORR4 theorem. It is not the similarly lettered physical amplitude C_R-U_R, not the original clipped VF #915 source, and not the whole NNS statistic before its already-justified reciprocal-prefix payment. The compiled consumer separately retains the prefix energy, with `2 Prefix <= Dchild/4`, and the full diagonal, with `D<=3R^2`. No additional cross-daughter credit is spent here.

#### CP1. Literal sampling and masked dilation

For real x>=A=3135 set r(x)=floor(sqrt(x+1)) and F(x)=M(floor x), with F(x)=0 for 0<=x<1. Put

```text
g(x)=G_r(x);
d_q^s(x)=1_(q^2<r(x)) d_q(r(x));
d_q^0(x)=1_(q^2<r(x)) F(x/q^2).
```

Every q is an odd prime. Then uniformly in every x>=A and every q,

```text
|g(x)-F(x)| <= 4 sqrt(x),
|d_q^s(x)-d_q^0(x)| <= 1_(q^2<r(x)) 4 sqrt(x)/q^2,
0<=H_r(x)<=2x.                                      (CP1)
```

If q divides an integer R, the exact endpoint identity is

```text
floor((R^2-1)/q^2)=(R/q)^2-1.                       (CP1b)
```

It is not asserted for nonmultiples. A root q^2 is excluded; the q daughter is first admitted at R=q^2+1, with Y_q=q^2+2.

#### CP2. Finite weighted full-bill comparison

The statement is the boxed finite inequality in A, for EVERY real beta>=1/2 and EVERY real finite T>=A. The constants 36, 1300 and 57 are absolute. E_beta(A) is an explicitly finite lower-prefix cost, not an assumed all-scale bound.

For beta>1/2,

```text
0<=J_beta(A,T)<=(A^(1-2 beta))/(2 beta-1).
```

At beta=1/2, J=log(T/A); it must NOT be called uniformly bounded.

At a complete square boundary the native weight is exactly

```text
w_beta(R)=[(R^2-1)^(-2 beta)-((R+1)^2-1)^(-2 beta)]/(2 beta).
W_beta((K+1)^2-1)=sum_(56<=R<=K) w_beta(R) B_R.
```

For a partial final block its weight is the same integral truncated at T. Thus the theorem is about the original sampled values, not silently interpolated replacement coefficients.

#### CP3. A single original daughter's integrated cap defect

Fix beta>1/2 and an odd prime q satisfying q^(2 beta-1)>2, BEFORE T varies. Define

```text
a_q=max(3135,(q^2+1)^2-1),
kappa=1/(2q)-q^(-2 beta)>0,
K_q(T)=integral_(a_q)^T 2[d_q(r(x))-G_r(x)/(2q)]^2
                              x^(-1-2 beta) dx.
```

For every finite real T>=a_q,

```text
kappa^2 E_beta(T)
 <= K_q(T)+E_beta(a_q)/q^2
       +4(4/q^2+2/q)^2 J_beta(a_q,T),                (CP3a)

K_q(T) <= 4(q^(-2 beta)+1/(2q))^2 E_beta(T)
       +4(4/q^2+2/q)^2 J_beta(a_q,T).                (CP3b)
```

The integrand is precisely the continuous-cap defect

```text
G_R^2/(2q^2) - [2G_R d_q(R)/q-2d_q(R)^2].
```

It is NOT automatically the anchored parity-cap defect. At beta=3/4, q=5 satisfies the condition because sqrt(5)>2. The constants may depend on the fixed beta,q through kappa and a_q; no uniformity as beta decreases to 1/2 is claimed.

**Qualified anchored-cap corollary.** Assume an available genuine bound |M(n)|<=C n^b for fixed b<1. For fixed q, the anchored interval is

```text
A_q(R)={m_R-V_q(R),m_R-V_q(R)+2,...,m_R+V_q(R)}.
C_q^anc(R)=max_(d in A_q(R))[2G_R d/q-2d^2].
```

For all sufficiently large R, the difference between its cap and the continuous cap is in [0,2]. Thus replacing K_q by the integrated actual anchored-cap deficit changes it by a uniformly bounded quantity, including its finite initial segment. In the CP3 exponent range, that integrated deficit is bounded iff E_beta(infinity) is finite. This is a **conditional target-equivalence consequence**, not an independent lower growth estimate for genuine mu or a positive pointwise gap.

### E. Mathematical Proofs

#### E1. Source, rounding and reciprocal budget

The common-clock Fubini and prefix/tail split in the inspected Lean sources give D0. Alternatively expand the ordered off-diagonal sum of t_i t_j+t_i a_j+a_i t_j with the original mu(i)mu(j). Its full sum is G^2+2GU and its diagonal is H. Subtract exactly 2 Dchild. This recovers D0 with no independence assumption, omitted orientation or reclassification of a site.

For r=r(x),

```text
r^2-1 <= x < (r+1)^2-1,
0 <= floor(x)-(r^2-1) <= 2r.
```

Bounded Mobius steps give |g-F|<=2r+(r-1)<=4 sqrt(x). For an active q,

```text
|M(floor((r^2-1)/q^2))-M(floor(x/q^2))|
 <= 2r/q^2+1 < 3r/q^2 <= 4 sqrt(x)/q^2.
```

The strict q^2<r mask is used in the middle inequality. It is not frozen, averaged or discarded. Inactive daughters and errors are zero. CP1b follows by dividing R^2-1 when q|R, and the birth formula follows by division at R=q^2+1.

Use the already familiar, deliberately nonoptimized constant c=17/72. For odd k>=3,

```text
sum_(k odd,k>=3) 1/(k^2-1)=1/4,
1/8-1/9=1/72,
sum_(q odd prime) q^(-2) <= 1/4-1/72 = c.
```

The first equality telescopes after k=2j+1. Subtract just the k=3 difference and keep every other positive difference. Consequently sum q^(-3)<=c/3 and sum q^(-4)<=c/9. Since V_0<=X_r and V_q<=X_r/q^2,

```text
H_r <= X_r(1+2 sum_q q^(-3)) <= x(1+2c/3)<2x.
```

These are elementary bounds, not new wheel computations or prime-distribution assumptions.

#### E2. Dilation at finite upper cutoff

All norms in this section use the measure x^(-1-2 beta) dx on [A,T]; vector daughter norms include the sum over q. Write a=sqrt(E_beta(T)) and j=sqrt(J_beta(A,T)).

For every q, changing variables x=q^2 y gives

```text
||d_q^0||^2
 <= q^(-4 beta) integral_1^(T/q^2) F(y)^2 y^(-1-2 beta)dy
 <= q^(-4 beta) a^2,
```

where an integral with T/q^2<1 is zero. Enlarging this NONNEGATIVE integral is an inequality only; no extra high-q site is inserted in the original signed bill. For beta>=1/2 both sum q^(-4 beta) and sum q^(-1-2 beta) are <=c. Hence, for U^0=sum d_q^0/q and U^s=sum d_q^s/q,

```text
||U^0||<=c a;                    ||(d_q^0)_q||<=sqrt(c) a;
||g-F||<=4j;
||U^s-U^0||<=4c j/3;
||(d_q^s-d_q^0)_q||<=4 sqrt(c) j/3.                  (E2)
```

There are only finitely many active primes for each finite T. No integrability at infinity, hidden Mertens bound or desired source estimate is assumed.

#### E3. Retain the whole square and prove CP2

The exact weighted identity is

```text
W=||g||^2+2<g,U^s>-2||(d_q^s)_q||^2-integral H_r(x) w(x)dx.
```

The finite omitted lower interval is explicit:

```text
||g||^2 >= a^2-E_beta(A)-8aj.
```

Use E2 to bound the potentially negative mixed term and negative daughter square. Keeping every error and the H term yields

```text
W >= (1-4c)a^2 -(8+16c)aj -(2+128c/9)j^2-E_beta(A)
  = a^2/18 -(106/9)aj -(434/81)j^2-E_beta(A).
```

The elementary inequality

```text
(106/9)aj <= a^2/36 + (11236/9)j^2
```

leaves a^2/36. The total j^2 coefficient is 101558/81<1300, proving CP2's lower bound.

For the absolute bill, the same terms with their absolute upper bounds give

```text
integral |B_r(x)|w(x)dx
 <= (1+4c)a^2 +(106/9)aj +(1730/81)j^2.
```

Now use (106/9)aj<=a^2+(2809/81)j^2. Since 1+4c+1=53/18<3 and (1730+2809)/81=1513/27<57, the upper bound follows. Constants were rounded UP, and their exact rational arithmetic was separately checked.

For beta>1/2, E_beta(A) and the J upper bound are finite constants independent of T. If E diverges, the lower bound forces W to positive infinity. If E is finite, the absolute upper bound gives absolute convergence of W. This proves CP4 without assuming absolute convergence in advance. At beta=1/2 retain the logarithmic cost; no boundedness equivalence is asserted there.

#### E4. Prove CP3 and its precise cap interpretation

Use norms on [a_q,T]; the chosen q is active throughout. The finite dilation estimate and CP1 give

```text
kappa sqrt(E_beta(T))
 <= ||d_q^s-g/(2q)||
      +sqrt(E_beta(a_q))/(2q)+(4/q^2+2/q)sqrt(J_beta(a_q,T)).
```

This follows from the reverse triangle inequality and
sqrt(E_beta(T))-sqrt(E_beta(a_q))<=||F||_[a_q,T].
Square twice using (u+v)^2<=2u^2+2v^2. The resulting first term is exactly K_q, and the other terms are E_beta(a_q)/q^2 and 4(4/q^2+2/q)^2 J. This proves CP3a. The ordinary triangle inequality gives

```text
||d_q^s-g/(2q)||
 <= (q^(-2 beta)+1/(2q))sqrt(E_beta(T))
       +(4/q^2+2/q)sqrt(J_beta(a_q,T)),
```

and the same square inequality proves CP3b. The exponent condition is indispensable to this particular reverse-triangle argument.

For the qualified anchored corollary, one does not need PNT. The count of nonsquarefree integers <=Y is at most Y sum_(d>=2)d^(-2)<=3Y/4; the latter bound is 1/4+integral_2^infinity t^(-2)dt. Thus

```text
V_q(R)>=Y_q/4-(R-1).
```

For fixed q this grows linearly in X_R, whereas the stated sublinear envelope gives |m_R|+|G_R|=o(X_R). A closest allowed parity point to G_R/(2q) is therefore eventually inside A_q(R), at distance at most one. Completing the square gives

```text
0 <= G_R^2/(2q^2)-C_q^anc(R) <= 2.
```

The integral of this difference is bounded, and the finitely many earlier roots contribute a finite explicit cost. This proves the qualified corollary. It makes no assertion that the actual daughter attains the cap.

### F. Structural Consequences And Falsification

**Genuine nonmultiple-root failure.** At R=56,q=3, the original daughter cutoff is 348, while the naively rounded smaller square endpoint is 323. The actual Mertens values are 2 and -3. CP1b is therefore not an identity at arbitrary roots.

**A coherent rounding counterexample.** Define the SYNTHETIC, NOT-MOBIUS sequence f(399)=1, f(400)=-1, f(n)=0 otherwise. Its prefix is one on [399,400) and zero elsewhere. At R=60,q=3, the native daughter is one for the entire sample block [3599,3720), since floor(3599/9)=399. At beta=1,

```text
integral_(3599)^(3720) x^(-3)dx
  > (1/81) integral_(399)^(400) x^(-3)dx.
```

The exact ratio is **126889421759100/9945665767039**, greater than twelve. Thus dropping CP1's sampling error gives a false dilation-norm assertion even for a single coherent bounded-step sequence. This does not refute the genuine-Mobius theorem or CP2, which pays that error.

**No pointwise upgrade.** At genuine R=57, B_R=-61496/35 while M(3248)=17. Thus a pointwise positive-parent lower bound without diagonal/history/boundary payment is false. CP2 is integrated with explicit finite costs, not a claim of pointwise positivity.

The executed finite results are:

| Check | Domain and result |
| --- | --- |
| Independent coefficient calculation | Divisor-convolution inversion agrees with the sieve at indices 0..2048 |
| Complete physical mixed-bill reconstruction | 203 roots: 56..256 and 317,1027; all exact equalities passed |
| Literal square-sampling error controls | 20,502 checks at left/middle/right integer sites of admitted root/prime cells |
| Exact q-multiple-root identity | 912 admitted pairs; all passed |
| Strict prime-square activation | q=11,13,17,19,23,29,31: excluded at q^2, admitted at q^2+1, daughter cutoff q^2+2 |
| Finite weighted inequalities | beta=1 at T=3136,3152,3248,16640,66048,101123,1056783; CP2 and q=3 CP3 passed |
| Boundary countercontrols | R=56 nonmultiple failure, coherent 399/400 impulse, genuine R=57 pointwise failure |

All acceptance decisions used integer/rational arithmetic. For long integrals each exact rational term was enclosed by downward rounding on a 10^30 denominator and an explicit one-unit-per-term upper error. This is a certified finite enclosure, not floating-point quadrature. Partial final square blocks were included. The beta=1 tests do not numerically establish the other exponents; their proof is E1-E4.

Selected genuine bill fixtures, retaining every admitted label:

| R | G_R | Complete B_R |
| ---: | ---: | ---: |
| 56 | 8 | -68464/35 |
| 57 | 19 | -61496/35 |
| 58 | 15 | -208856/105 |
| 59 | 9 | -78704/35 |
| 317 | -25 | -808806894/12155 |
| 1027 | 371 | -57206636365510048/100280245065 |

These are source regressions, not evidence for all-root nonpositivity. The wide root range was used to test the new square-sampling comparison and activation boundaries, not to rerun yesterday's cap optimization or infer an exponent.

### G. Signed And Quantitative Relevance

The original full mixed bill is retained before norms. All q labels in S_R are included. The q-mask is used pointwise in the error bound; comparison with an unmasked positive integral happens only inside a justified norm bound. The exact physical H_R, root history and partial final block are paid. No historical occurrence or negative daughter square is spent twice.

CP2 is a LOWER comparison and a boundedness equivalence, not the UPPER inequality needed by `mertensPowerBound_of_corr4MixedTailBill`. It rules out only the claim that this particular weighted signed averaging automatically eliminates the parent-energy problem. It does not rule out an independently proved arithmetic upper bound, a one-sided signed closure, or another weighting/consumer with its own proof.

For comparison, the existing pointwise consumer still requires

```text
exists A>=0, forall R>=56: B_R <= A R^(4 beta_out), beta_out>=1/2.
```

An independently proved root-energy saving R^(7/2-eta) would yield the Mertens exponent 7/8-eta/4 through that consumer. CP2 supplies no eta, no such upper bound, and no pointwise inference from a signed weighted average. Its weighted E uses beta=1/2+epsilon in the existing weighted-Mertens convention, up to ordinary comparable integral/discrete weights. Any terminal Mellin continuation argument must preserve its own explicit hypotheses; it is not newly formalized here.

In particular the CP4 boundedness supplier is **TARGET_EQUIVALENT to the corresponding weighted Mertens energy**, not a newly discovered easier lemma. The result is meaningful as a precise restriction on a proposed proof mechanism, not as progress in the global exponent itself.

### H. Novelty, No-Circularity And Formal Evidence

Repository searches covered CORR4/integral, mixed/coercive, daughter/dilation and cap/weighted, followed by actual relevant sources rather than search snippets alone. No identical all-root sampled CP2/CP3 comparison was found in the inspected sources or consumed recent handoffs. This is not an exhaustive literature-priority claim.

Important prior results are explicitly NOT new:

- `corr4_mixed_tail_eq_actual_endpoint_gap` already gives the full finite source identity.
- `corr4_mixed_excess_lower_of_record_energy` already gives a pointwise positive remainder under an explicit record-energy hypothesis. CP2 replaces that hypothesis by an integrated dilation comparison and pays the sampling costs; it does not prove the hypothesis pointwise.
- `CORR4_FRAME_ONLY_INVERSE_20261026.lean` already supplies a scalar inverse obstruction from the daughter frame.
- `CORR4_OAI_POWER_GRAM_EQUIVALENCE_20261025.lean` and the mixed-tail gate already supply the pointwise power reduction/consumer. The general principle that the full source is target-strength is inherited.
- `MERTENS_WEIGHTED_COVARIANCE_RH.lean` already identifies weighted Mertens energy with its own weighted pair covariance. That is a different carrier from the present square-sampled mixed bill.
- `LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE.lean` has a different literal covariance-owner congestion norm; its 79/81 statement is not silently reused as CP2.

No desired upper bound is assumed in E1-E4. All T are finite during the proof, so using a global norm does not presuppose convergence. Constants are independent of T. The beta=1/2 boundary is disclosed. The fixed-q anchored corollary alone takes the explicitly stated inherited sublinear envelope. It does not imply growing-q uniformity or global feasibility of yesterday's auxiliary functions.

**Fresh formal evidence, at its actual scope.** The open/draft PR collection was empty. PR #1096 is human-merged at the pinned main. Its source blob is **3cbc5159536d6b9e5000f74c5bd018bd2d62daf1**; final proof head **ecf701ff2fea1de52e505ee34048a2b3c220f0fc**. All 15 exact-head check jobs were freshly returned as completed/success. The dedicated [run 42150511056, job 127672350630](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42150511056/job/127672350630) was read: warning-fatal exact-type and ten-name axiom audit passes. Nine declarations list propext, Classical.choice, Quot.sound; the static-partner theorem lists propext, Quot.sound. Source-addressed compilation artifacts were reused (`compiled=0 cached=3`), and the audit harness ran freshly at that head. This is not a claim of a new full compilation today.

That formal result constructs finite equal-cardinality prime/semiprime endpoint subsets, the exact signed residual, a complete-square equality and a strict-cutoff coefficient lift. The raw occurrence involution, PNT asymptotic, new CP claims and global norm estimate are NOT thereby formalized. The currently merged #1095 is the previously verified fail-closed Euler audit repair, superseding yesterday Wheel's earlier V1 warning. No new CI was triggered and no local Lean ran.

### I. Conceptual Interpretation

Independent-per-root flexibility and coherence across roots are genuinely different constraints. The former allows different residual core signs at each root. The latter makes every daughter a smaller view of one prefix, with a fixed dilation cost. That cost limits how much the signed daughter terms can cancel the parent after the specified weighting.

The calculation also limits its own strategic value. Coherence creates a valid global restriction, but in this norm it exposes the same weighted Mertens problem. It supplies no genuinely new prime-factor sign information. A useful continuation must now add such information, or change the independently justified source estimate, instead of renaming W or optimizing the harmless constants 36/1300/57.

### J. Competing Structural Hypotheses

| Hypothesis or approach | Verdict |
| --- | --- |
| Native daughters are exact continuous dilations with no sampling error | REFUTED at bounded-step model scope by the 399/400 fixture; genuine nonmultiple endpoint identity also fails at R=56 |
| Common-prefix coherence permits arbitrarily complete weighted cancellation of a divergent parent energy | REFUTED for CP2's exact weighting, beta>1/2 and complete bill |
| A single fixed-label cap can stay integrably saturated while parent energy diverges | REFUTED in CP3's exponent range, with explicit costs and the anchored corollary's stated extra input |
| CP2 gives pointwise positivity, all-root cap gaps or a new power bound | NOT IMPLIED; genuine R=57 refutes an unqualified pointwise version |
| New multiplicative information between remaining cores could give a useful signed upper bound | OPEN; no general impossibility theorem is claimed |

### K. Continuity And Specialist Handoffs

Intake reports were pinned at **aa215fa54489b8662a551dfe0296ba33b14b66c5**. Relevant result, proof, correction and resume sections from November 5 and November 6 were read. Unrelated executable appendices were not all rerun. At intake, only Owner and Analytic had November 6 reports. Coordinator, Census, Referee and Lean are **TODAY=PENDING / YESTERDAY=CARRY_FORWARD**; schedules are not execution evidence. Yesterday's Coordinator AM/PM blobs match and represent one mirrored record.

| Role/date | Verified blob | Consumed original claims and limits |
| --- | --- | --- |
| Coordinator Nov 5 | be661bb2ed2830fc4aeddf14713455e550d982cc | C53-C56 sub-root relaxation; C63-C68 matching scope; final receipt 23:35 EST; CORR4 is next Wheel route |
| Wheel Nov 5 | afc85d800c47f82f2db634591a7798005cb668de | F1-F4 fixed-law caps; P1-P5 four-block cancellation; PE1-PE5 finite odd boundary; preserve all three actual turns |
| Owner Nov 5 | 39665b5b28fc48378519ab9d56cee8df4d3e2681 | RC/CR/MC scopes; JOH moving clock, signed coarse return and upper halo |
| Owner Nov 6 | a86a79671728b3ddfc3fdc4e4e0a7f509e1ffaf9 | Receipt 05:29 UTC; BT1-BT2 pays old SAT threshold at paper scope; RZ1-RZ3 zero-mode response is not actual Delta; new review pending |
| Analytic Nov 5 | 9490aa2eecafcd19d8007043cc5f978fe421a7c9 | SP fixed-profile Nyman obstruction; CR1-CR3 rebase domain excludes physical all-selected rows; no CORR4 supplier |
| Analytic Nov 6 | 8ad0bdd80168555773271bbc70cda5c78746a4b4 | Receipt 06:30:36 UTC; FP1-FP5 averaging preserves parent and true birth; R=56 response -11+exp(-2it log3); no signed upper bound |
| Census Nov 5 | 24fcd6a631eca9ae44238d927215f49e1d8a174f | CORR4 R=57/58 joint gaps 28/3 and 12; R=59 Y7=71 correction; JOH X=209 upper-halo sign reversal |
| Referee Nov 5 | 789ed87021fe98963c244a8d0c9075638e76be43 | referee-11 accepts PE1-PE4 WITH_SCOPE; new referee-12..14 remain own paper work, not a recurrence |
| Lean Nov 5 | 5e0ecdd8f08c2e19b4614f00c1a5657f58722344 | lean-3 exact-head finite source/axioms; its UNMERGED status is superseded by today's live merge |
| External inbox | 038018145c0fddb2f6306c0712373adf9cd1ea52 | No entry after October 18; EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain carrier/cutoff/conditional-scope warnings |

Retrieval/verification occurred during this actual run beginning 07:05 UTC. Original report receipts remain evidence in those files, not new independent audits. The new CP1-CP4 have no independent Referee verdict yet.

| Recipient | Precise asynchronous request |
| --- | --- |
| Coordinator | Record CP2 as a new sampled-source comparison, not a prime arithmetic gain. Its uniform upper supplier is weighted-energy-equivalent. Preserve FINITE-AC next and the nine-route breadth policy. |
| Referee | Independently audit E2's q^(-4 beta) factor, moving mask, use of q^2<r to pay +1 rounding, lower finite E(A), constants and beta=1/2 exception. Check CP3's fixed-q quantifiers and continuous versus parity cap. |
| Census | No enlarged scan needed. Independently reproduce the compact R=56/57 and 399/400 countercontrols, and one physical full-bill identity; verify exact sample-block length and all mixed orientations. |
| Analytic | CP2 concerns real cutoff averaging, not FP's frequency average. Check whether an actual arithmetic input can upper-bound the complete bill beyond this equivalence; do not infer a new supplier from a norm identity. |
| Owner | No SAT/JOH or #915 transport is asserted. The relevant method warning is to preserve sampling and historical terms before using a continuous operator estimate. |
| Lean Verification | No immediate branch requested for self-audited CP claims. If independently accepted and useful, CP1's masked error bound is the smallest enabling lemma; CP2 additionally needs weighted integration. Do not formalize an assumed upper supplier as a breakthrough. |

Handoffs are published in this own report only. No agent was launched, and no other report, issue, PR, source, policy, workflow or schedule was changed.

### L. First Independently Missing Theorem

The original genuine all-root upper estimate remains open:

```text
exists beta_out>=1/2, A>=0 at a genuinely improved output scale,
forall R>=56: B_R<=A R^(4 beta_out).
```

For a weighted alternative at a fixed beta>1/2 not already supplied by the inherited input, the proposed condition sup_T W_beta(T)<infinity is now explicitly equivalent to E_beta(infinity)<infinity. It must NOT be advertised as a smaller independent premise. CP3 similarly shows that a small integrated fixed-daughter cap defect in its exponent range can hide the same energy demand.

No independently proved arithmetic upper supplier was found in this run. The strongest valid new result is the explicit lower/absolute comparison and its false-transfer certificates. The next CORR4 question should be an actual multiplicative signed restriction absent from bounded-step coherence, with the complete B return, rather than another fixed-wheel relaxation, coefficient frame constant, or weighted target rename.

### M. Source Ledger And Next-Run Capsule

All sources below were retrieved at the pinned main; relevant definitions, theorem statements and proof steps were inspected. The source identities and old bounds are inherited, not new formal claims.

| Source | Git blob SHA |
| --- | --- |
| AGENTS.md | 547dda0d9456e7a4e1165dc72d59da6f70d5c023 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md | 4fbab59cc6fcc33a4f4e7a8ef447b2f7947b53dd |
| docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md | 8317f08996b65f2e4b32c00c91b31cb6d0c09718 |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 6c1d1c10e2755017ffe9d7f40df8b9ae7692f23a |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| RHLean/Proof/SignedTransportAmplificationAudit.lean | 746f35f126f36e024d39e38c92dde30aabca266b |
| research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean | ebca096e83009a7df514d00b6a2696be86a94c55 |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean | f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8 |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean | dbaf123113b544d0b19c7c3c6b92a1288a26cfb8 |
| research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY.lean | ac8015a1dd87aea23d35d57f5102efd38f4a105b |
| research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean | ba95beda901719afaabca9011b8dbae6fc69662d |
| research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean | 29bb263ddd07b12a2dd5ccf6a12aecaf627134d8 |
| research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean | d17aeb639bb47d79333cf0d00760c2604feddfdf |
| research/CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026.lean | a4abeb13653076bedd8e1173c933ee3324bfea26 |
| research/CORR4_MIXED_TAIL_RECORD_PLATEAU_FEJER_20261026.md | a61a0a2d13577c0c8757ba00a9d309415e4e0e00 |
| research/CORR4_FRAME_ONLY_INVERSE_20261026.lean | fe318e29f348644bdd0896eba897a1d12b8d38ec |
| research/CORR4_OAI_POWER_GRAM_EQUIVALENCE_20261025.lean | 49a3ecb8fbb934d58c1d171ce1cc0275f1e6c8b9 |
| research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a |
| research/MERTENS_WEIGHTED_COVARIANCE_RH.lean | fb7de64c09835483107f171126d07a50677808a7 |
| research/LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE.lean | 73447e8c73ea60affec36a25b9f4794862331359 |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| research/MERTENS_ODD_BOUNDARY_PRIME_ESCAPE_20261105.lean | 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1 |

```text
RUN: 20261106-wheel-1; scheduled 02:05:01 EST; RUN_ID_UNAVAILABLE.
MAIN: 4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1 / SEARCH_BROAD.
ROUTE: CORR4, complete native mixed bill on one coherent prefix.
RESUMED: Nov5 F1-F4; Census R57/58; Coordinator C53-C56.
CP1: literal masked square-sampling errors, no false continuous identity.
CP2: E/36-E(A)-1300J <= weighted B <= weighted |B| <=3E+57J.
CP3: one fixed q with q^(2 beta-1)>2 controls integrated cap defect;
     anchored-lattice version explicitly uses a sublinear genuine envelope.
CP4: weighted boundedness is E_beta-equivalent, not an easier supplier.
CP5: 203 complete-source checks, 20502 geometry checks, 912 chain checks,
     7 weighted cutoffs, strict births, and exact failed-transfer fixtures.
REVIEW: PAPER_PROOF / SELF_AUDIT; independent review PENDING.
FORMAL: new claims NOT_FORMALIZED; merged #1096 finite proof audit verified.
FIRST OPEN: genuine source upper estimate, not another weighted reformulation.
NET NEW ENDPOINT GAIN: UNKNOWN / NONE; canonical VF and RH remain OPEN.
NEXT DISTINCT ROUTE: FINITE-AC, resume Nov5 P1-P4 prime-sampled increments
     and full four-block cancellation, not the already completed frame.
NEXT MU-LIFT: consume referee-14 and Coordinator C63-C66 on typical-depth
     / large-prime coverage, preserve moving endpoints and signed remainder.
NEXT CORR4: actual cross-core arithmetic beyond bounded-step coherence;
     do not optimize CP2 constants or repeat unchanged cap scans.
```

Early publication commit **c007fef1958672fcde45ef05d86530db2afe275c**, blob **fddd638b8aacc87f370a2eeae5ed39a32ccd53fe**, was exactly read back. The final verified receipt is appended after publication. Direct shell GitHub access failed with CONNECT 403; connected GitHub reads and authorized own-report writes worked. No local Lean execution, source edits, proof branches/PRs, autonomous merge, other-agent launch, schedule change or ongoing background test occurred.

The complete executed standard-library verifier follows. SHA256 **4548c83b3ac13d7f1c5b8add55f37177da1754cde8f80e905dd93efa3d254fc7**. Runtime assertions and syntax compilation passed. The analytic proofs above, not finite testing, establish the universal quantifiers.


### Complete Executed CP5 Verifier

```python
"""Exact finite CORR4 cross-root tests. No Lean and no fitted exponent."""

from array import array
from fractions import Fraction as Q
from math import isqrt, lcm
import json


SCALE = 10**30
A = 56**2 - 1
ROOTS = list(range(56, 257)) + [317, 1027]
N = (max(ROOTS) + 1)**2


def sieve(n):
    mu = array("b", [1]) * (n + 1)
    mu[0] = 0
    prime = bytearray(b"\1") * (n + 1)
    prime[0] = prime[1] = 0
    for p in range(2, n + 1):
        if prime[p]:
            for k in range(p, n + 1, p):
                mu[k] = -mu[k]
                if k != p:
                    prime[k] = 0
            for k in range(p * p, n + 1, p * p):
                mu[k] = 0
    m = array("i", [0]) * (n + 1)
    sf = array("i", [0]) * (n + 1)
    for k in range(1, n + 1):
        m[k] = m[k - 1] + mu[k]
        sf[k] = sf[k - 1] + mu[k] ** 2
    return mu, prime, m, sf


def mass(lo, hi):
    """Exact integral of x^-3, the beta=1 test weight."""
    return Q(1, 2 * lo**2) - Q(1, 2 * hi**2)


def scaled_floor(value):
    return value.numerator * SCALE // value.denominator


def enclosure(values):
    count = total = 0
    for value in values:
        total += scaled_floor(value)
        count += 1
    return Q(total, SCALE), Q(total + count, SCALE)


def native(r, m, sf, primes):
    x = r * r - 1
    owners = [q for q in primes if q * q < r]
    g = m[x] - m[r - 1]
    daughters = {q: m[x // (q * q)] for q in owners}
    u = sum((Q(daughters[q], q) for q in owners), Q(0))
    energy = sum(d * d for d in daughters.values())
    h = Q(sf[x] - sf[r - 1]) + 2 * sum(
        (Q(sf[x // (q * q)] - sf[r - 1], q) for q in owners), Q(0)
    )
    bill = g * g + 2 * g * u - 2 * energy - h
    return bill, h, g, daughters


def physical_bill(r, mu, primes):
    x = r * r - 1
    owners = [q for q in primes if q * q < r]
    den = lcm(*owners)
    exits = {}
    aw = 0
    for q in owners:
        aw += den // q
        n = x // (q * q) + 1
        exits[n] = exits.get(n, 0) + den // q
    pt = pp = pairs = diag = 0
    child = {q: 0 for q in owners}
    for n in range(1, x + 1):
        aw -= exits.get(n, 0)
        tv = den * mu[n] if n >= r else 0
        av = aw * mu[n]
        pairs += tv * pt + tv * pp + av * pt
        diag += tv * tv + 2 * tv * av
        pt += tv
        pp += av
    for q in owners:
        child[q] = sum(mu[1 : x // (q * q) + 1])
    return Q(2 * pairs, den * den) - 2 * sum(v * v for v in child.values()), Q(diag, den * den)


def energy_prefixes(m, cutoffs):
    wanted = set(cutoffs)
    out = {}
    lower = 0
    for n in range(1, max(wanted)):
        numerator = m[n] ** 2 * (2 * n + 1)
        denominator = 2 * n * n * (n + 1) * (n + 1)
        lower += numerator * SCALE // denominator
        if n + 1 in wanted:
            out[n + 1] = (Q(lower, SCALE), Q(lower + n, SCALE))
    return out


def main():
    mu, prime, m, sf = sieve(N)
    primes = [p for p in range(3, isqrt(max(ROOTS)) + 2) if prime[p]]
    # Independent divisor-convolution inversion checks the small coefficient table.
    inverse = [0] * 2049
    inverse[1] = 1
    for d in range(1, 2049):
        for multiple in range(2 * d, 2049, d):
            inverse[multiple] -= inverse[d]
    assert list(mu[:2049]) == inverse
    physical_checks = 0
    fixtures = {}
    for r in ROOTS:
        b, h, g, d = native(r, m, sf, primes)
        bp, hp = physical_bill(r, mu, primes)
        assert b == bp and h == hp
        physical_checks += 1
        if r in [56, 57, 58, 59, 317, 1027]:
            fixtures[r] = {"G": g, "bill": str(b), "diagonal": str(h), "daughters": d}
    geometry_checks = 0
    exact_chain_checks = 0
    first_nondilation = None
    for r in range(56, 1028):
        x = r * r - 1
        for q in primes:
            if q * q >= r:
                continue
            y = x // (q * q)
            if r % q == 0:
                assert y == (r // q)**2 - 1
                assert m[y] == m[(r // q)**2 - 1]
                exact_chain_checks += 1
            elif first_nondilation is None and m[y] != m[(r // q)**2 - 1]:
                first_nondilation = [r, q, y, (r // q)**2 - 1, m[y], m[(r // q)**2 - 1]]
            for t in [x, x + r, x + 2 * r]:
                assert isqrt(t + 1) == r
                eg = m[x] - m[r - 1] - m[t]
                eq = m[y] - m[t // (q * q)]
                assert eg * eg <= 16 * t
                assert (eq * q * q)**2 <= 16 * t
                geometry_checks += 1
    births = []
    for q in primes:
        r = q * q
        if r < 56 or r > 1027:
            continue
        assert q not in native(r, m, sf, primes)[3]
        assert q in native(r + 1, m, sf, primes)[3]
        assert ((r + 1)**2 - 1) // (q * q) == r + 2
        births.append([q, r, m[r + 2]])

    # Weighted full-source tests, with certified integer-scaled enclosures.
    cutoffs = [A, A + 1, A + 17, 57**2 - 1, 129**2 - 1, 257**2 - 1, 318**2 - 1, 1028**2 - 1]
    ep = energy_prefixes(m, cutoffs)
    weighted = []
    for t in cutoffs[1:]:
        last = isqrt(t + 1)
        terms = []
        absolute = []
        defect = []
        for r in range(56, last + 1):
            lo = r * r - 1
            hi = min((r + 1)**2 - 1, t)
            if lo >= hi:
                continue
            b, _, g, ds = native(r, m, sf, primes)
            w = mass(lo, hi)
            terms.append(b * w)
            absolute.append(abs(b) * w)
            defect.append(2 * (Q(ds[3]) - Q(g, 6))**2 * w)
        wl, wu = enclosure(terms)
        _, al = enclosure(absolute)
        dl, _ = enclosure(defect)
        el, eu = ep[t]
        e0l, e0u = ep[A]
        j = Q(1, A) - Q(1, t)
        assert wl >= eu / 36 - e0l - 1300 * j
        assert al <= 3 * el + 57 * j
        assert dl >= eu / 324 - e0l / 9 - Q(400, 81) * j
        weighted.append({"T": t, "energy_interval": [str(el), str(eu)], "bill_interval": [str(wl), str(wu)]})

    c = Q(17, 72)
    assert 1 - 4 * c == Q(1, 18)
    linear = 8 + 16 * c
    assert linear == Q(106, 9)
    assert 2 + 128 * c / 9 + 9 * linear**2 < 1300
    assert 18 + 128 * c / 9 + linear**2 / 4 < 57
    assert Q(35, 18) + 1 < 3
    assert Q(1, 4) - (Q(1, 8) - Q(1, 9)) == c

    # Legal coherent synthetic impulse: sample-and-hold is NOT exact dilation.
    # f(399)=1, f(400)=-1, every other f(n)=0. This is explicitly not Mobius.
    q, r, t = 3, 60, 61**2 - 1
    assert (r * r - 1) // (q * q) == 399
    sampled = mass(r * r - 1, t)
    continuous_bound = mass(399, 400) / q**4
    assert sampled > continuous_bound
    # A claimed pointwise coercivity without boundary payment fails for genuine mu.
    assert native(57, m, sf, primes)[0] < 0 < Q(m[57**2 - 1]**2, 36)
    result = {
        "independent_mobius_coefficients": 2049,
        "physical_full_bill_checks": physical_checks,
        "geometry_checks": geometry_checks,
        "exact_prime_multiple_chain_checks": exact_chain_checks,
        "strict_births": births,
        "first_genuine_nonmultiple_dilation_failure": first_nondilation,
        "fixtures": fixtures,
        "weighted_beta_one_tests": weighted,
        "synthetic_no_rounding_counterexample_ratio": str(sampled / continuous_bound),
        "all_assertions": "PASS",
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
```

## Final Authority Freshness Check

At the final authority review, completed **2026-11-06 07:40 UTC (02:40 EST)**, the latest retrieved `main` remained **4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a**. Today's directory still contained only Owner, Analytic and this Wheel checkpoint; Owner and Analytic blobs matched the intake ledger. Today's other priority roles therefore remain **TODAY=PENDING / YESTERDAY=CARRY_FORWARD**, not assumed executions. The current own-report blob was freshly fetched as **fddd638b8aacc87f370a2eeae5ed39a32ccd53fe** and its full content matched the preserved early checkpoint before this replacement.

## Verified Publication Receipt

**PUBLISHED / READBACK_VERIFIED**, checked **2026-11-06T07:41:14Z (02:41:14 EST)**. The substantive final report commit is **74f4411e6f930693c9b1629e429b62f8cd7ec8b0**, content blob **edd91fd3037e45c4d56a64439683fb8958a05403**. An immutable-commit fetch returned the exact submitted content, and commit metadata confirmed that only `research/agent_reports/2026-11-06/30-finite-wheel.md` changed: **740 additions, 0 deletions**. The prior checkpoint body was preserved in full. This receipt is appended in a subsequent own-report-only commit and does not promote CP1-CP4 beyond **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING**. CP5 remains **FINITE_COMPUTATION**. The authorized research invocation is complete; the canonical objective and independent improved source upper bound remain **OPEN**.


## Scheduled FINITE-AC Continuation Checkpoint - 20261106-wheel-2

Actual invocation: scheduled **2026-11-06T10:12:01-05:00**, America/New_York; RUN_ID_UNAVAILABLE. Checkpoint recorded **2026-11-06 15:16:35 UTC**. Status: **PARTIAL / IN_PROGRESS**. This is a new actual invocation appended to the preserved earlier CORR4 report, not a retroactive revision of its results.

Selected route: **FINITE-AC**, resuming **20261105-wheel-2/P1-P4** and the earlier complete-extension obstruction. The last proved step is the exact four-block prime-mask return for the original historical rank-one kernel. The first open input is genuine signed control after all four blocks are restored. This run will test the successive-root boundary of the prime-sampled remainder, including changing prime admission, historical cutoff, and every return term. No theorem or power saving is claimed yet.

Authority: main **4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a**; AGENTS **547dda0d9456e7a4e1165dc72d59da6f70d5c023**; proof contract **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**; policy **ffd8f1c65cc4da656174956d4e03b48bea46768b**. deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1; eta_gate=SEARCH_BROAD; net new endpoint gain UNKNOWN. Canonical VFCanonicalSquareVonKochStatement remains OPEN.

Today/yesterday priority reports and external inbox were retrieved from reporting snapshot **34fafc2801539e603e05b5ce7a3b57812021c229**. Today's Coordinator has only a PARTIAL checkpoint: **TODAY=PENDING** for completed synthesis; **YESTERDAY=CARRY_FORWARD** from November 5 C63-C68 and earlier finite-AC discussion. Today's other named roles have substantive reports. The earlier CP1-CP4 now have independent ACCEPT_WITH_SCOPE from 20261106-referee-1; Lean reports sampling-only proof PR #1097, which is being checked at its exact current head. This does not promote the weighted-integral claims or supply finite C. #1096 is merged; yesterday's V1 Euler audit finding was repaired by merged #1095. No new upstream execution is inferred from schedules.

Source declarations inspected: eulerRankOneFloorKernelQ, eulerRankOneResidualQ, eulerFloorBilinearQ, eulerSelfDualBilinear_eq_two_mertens_sub_endpoint and EulerSelfDualFiniteCStatement. Preserve **N=R-1, X=R^2-1**, genuine mu, ordered floor occurrences, the nonsymmetric rank-one subtraction, and **K_R=max_(0<=y<R)(M(y)-1)^2/(y+1)**. The finite-C estimate is an explicit unpaid hypothesis, not a proved input.

Pending: exact boundary derivation, independent code paths for finite tests, novelty/no-circularity review, full signed return, specialist handoffs, and final commit/readback. Writes remain restricted to this own report; no local Lean or other agent launch.

## Scheduled FINITE-AC Final Synthesis - 20261106-wheel-2

Actual invocation: **2026-11-06T10:12:01-05:00**, SCHEDULED, America/New_York; RUN_ID_UNAVAILABLE. This completes the checkpoint above, not another invocation. New arguments are **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. Exact tests are **FINITE_COMPUTATION**. Earlier valid sections, claim IDs, and receipts are preserved. No new endpoint gain or RH proof is claimed.

Pre-publication freshness: **2026-11-06T15:40:06Z / 10:40:06 EST**. Latest main is unchanged; the November 5/6 upstream report blobs in section K are unchanged. The current own-report blob exactly matches the previously verified checkpoint. PR #1097 was re-read and remains open, non-draft and unmerged at the stated head. The completed Coordinator synthesis remains TODAY=PENDING / YESTERDAY=CARRY_FORWARD.

### A. Most Important Structural Discovery

**The prime-band remainder has a coherent historical boundary that survives after the old four-block leading terms have been recombined.** Its complete successive-root change is a disjoint fresh-cofactor sum minus `k_R*mu(R)`, plus explicitly controlled admission/exit terms. The square of that historical boundary has the unconditional asymptotic

```text
D_H := sum_(H<=R<2H) k_R^2 mu(R)^2
     ~ [7/(48 zeta(2))] H^3/log(H)^2.                  (PB3)
```

This is the energy of ONE specified component, **not a lower bound for the complete signed source**. Nevertheless it gives a useful inverse restriction: a prime-column increment bound smaller than this scale would force an explicit, almost perfectly positive, weighted correlation between `mu(R)` and the fresh cofactors above R. An independent estimate for that correlation is not currently available. Disjoint fresh occurrences do not establish the needed cancellation.

The exact geometry is stronger than a raw degree cap: each old selected prime contributes a consecutive block of two or three cofactors; different selected primes have disjoint cofactor blocks at that root; physical products are distinct; and the full endpoint boundary has an exact interval lifetime with all exits retained. The elementary shell-spacing ingredient is inherited from existing work, not claimed as a new general theorem. The new application is the complete moving prime-column boundary, its paid exceptional terms, and the quantitative inverse statement PB4.

| Claim | Result and scope | Status |
| --- | --- | --- |
| PB1 | Exact prime-band boundary, original rank-one correction, and full-source reconstruction | EXACT_IDENTITY / PAPER_PROOF |
| PB2 | Disjoint fresh cofactor intervals, unique physical products, and complete occurrence lifetimes | PAPER_PROOF; includes an application of inherited spacing |
| PB3 | Positive historical-component energy asymptotic; admission/exit error is smaller at that scale | PAPER_PROOF; classical inputs explicitly identified |
| PB4 | Finite and asymptotic inverse correlation criterion for a small selected-column increment | PAPER_PROOF; no upper supplier asserted |
| PB5 | 2,032-root exact checks, boundary counterexamples and seven dyadic diagnostics | FINITE_COMPUTATION |

### B. Current Authoritative Objective

Pinned main: **4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a**, tree **48b193cd105e21183b1cfd68b059894c8056f35c**. AGENTS **547dda0d9456e7a4e1165dc72d59da6f70d5c023**; CURRENT_PROOF_CONTRACT **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**. deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1, policy **ffd8f1c65cc4da656174956d4e03b48bea46768b**. The stable selector, broad-search, complete-return, persistent-engine, role and dynamic instructions were retrieved. FINITE-AC is the protected route following November 5 MU-LIFT and November 6 CORR4.

The canonical actual-prime objective remains

```text
exists C>=0, forall integer R>=2:
 |pi(R^2)-vfCanonical(R^2)| <= C R log R.
```

The canonical source and its explicit ClassicalVonKochRHCriterion consumer were inspected. The current finite-C route instead asks, with its original history,

```text
N=R-1, X=R^2-1, ell=R+1;
Q_R=sum_(1<=a,b<R) mu(a)mu(b) floor(X/(ab));
K_R=max_(0<=y<R) (M(y)-1)^2/(y+1);
exists C>=0, forall R>=2: |Q_R|<=C R sqrt(K_R).       OPEN
```

The compiled EulerSelfDualFiniteCStatement quantifies over every valid LowerMertensCriticalEnvelope R K. Its actual minimal K_R is valid; this is not a replacement normalization. The compiled endpoint identity is `Q_R=2M(R-1)-M(R^2-1)`. The conditional finite-C -> finite-A -> Mertens energy -> RH consumer does not prove its finite-C premise. No VF, returned-cell, or Hecke occurrence identification is asserted here.

### C. Structural Mechanism Investigated

Resume **20261105-wheel-2/P1-P4**, especially the exact complete prime columns `r_R+Z_R`. Yesterday showed why the four original prime/complement blocks cannot be normed separately. Repeating that asymptotic would not address the remaining source. Today's changed question is whether taking successive square endpoints yields a genuinely simpler signed source after that cancellation.

Two moves were examined. A pointwise sum of the inherited Mertens bounds gives only the already known `Z_R=O(R^(1+b)/log R)` for an incoming exponent b<1; no improvement was found that way. The developed alternative follows the exact boundary of the partial prime mask before squaring. It identifies a necessary correlation for any stronger local-energy proposal, and supplies finite counterexamples to omitting its non-product boundaries.

No wheel was enlarged, no accepted census was rerun merely for scale, and no arbitrary-sign model was substituted for genuine mu. The 2,032-root experiment tests the NEW moving-root identities, not yesterday's four-block asymptotic.

### D. Exact Statements And Original Carrier

All statements below use integer R>=17 unless a separate range is stated; H>=17 is an integer. Let M(t)=sum_(1<=n<=t)mu(n), with all divisions in M interpreted by integer floor. Define

```text
P_R={p prime: 3R<=4p and p<R};  k_R=|P_R|;
d_R=sum_(p in P_R)1/p;  r_R=(R+1)d_R-k_R;
Z_R=sum_(p in P_R)[M(floor((R^2-1)/p))-M(R-1)].

T_R(a,b)=floor((R^2-1)/(ab))-(R+1)/b*floor((R-1)/a);
B_R(u,v)=sum_(a,b<R, a,b>=1) u(a)v(b)T_R(a,b);
f(a)=mu(a), g_R(a)=-1_(a in P_R), h_R=f-g_R;
A_R=sum_(a<R,a>=1)mu(a)/a;
C_R=B_R(f,g_R)=r_R+Z_R;
V_R=(R+1)A_R+B_R(f,h_R);  Q_R=C_R+V_R.             (D0)
```

C_R here is a selected COLUMN of the nonsymmetric historical rank-one kernel, not a CORR4 bill or a new name for the full Q_R. Both mixed orientations remain in D0. Specifically C_R=B_R(g_R,g_R)+B_R(h_R,g_R), while V_R includes the other two blocks and the original linear term.

The `(p,n)` objects below are the actual signed boundary created by exact finite row completion, with n>=R. They are NOT claimed to be original historical `(a,b)` rows with a<R. The bridge is the exact scalar row identity proved in E1, with its constant retained. There is no unproved returned-source admission map.

#### PB1. Full Successive-Root Boundary

Let

```text
L_R={p in P_R: 3R<=4p<3R+3};
F_R=sum_(p in P_R) sum_(R^2<=p*n<(R+1)^2) mu(n);
H_R=k_R*mu(R);
B_R^new=1_(R prime)*(mu(R+1)+mu(R+2));
J_R=sum_(p in L_R)[M(floor((R^2+2R)/p))-M(R)].
```

The use of B_R^new distinguishes the scalar birth from the bilinear B_R(u,v). H_R denotes this report's historical component only, not the earlier positive VF residual. Then

```text
P_(R+1)\P_R = {R} if R prime, else empty;
P_R\P_(R+1) = L_R,  |L_R|<=1;
Z_(R+1)-Z_R = F_R-H_R+B_R^new-J_R.                (PB1a)

r_(R+1)-r_R = d_R + 1_(R prime)*2/R
               -sum_(p in L_R)[(R+2)/p-1];
|r_(R+1)-r_R|<=2.                                 (PB1b)

e_R=B_R^new-J_R+r_(R+1)-r_R;
C_(R+1)-C_R=F_R-H_R+e_R.                          (PB1c)
```

Every floor and birth is literal. The exiting row is evaluated at the UPDATED endpoint and UPDATED history M(R); replacing it by the old row without its fresh/history adjustment is incorrect.

#### PB2. Arithmetic Incidence And Lifetime

At each R>=17, for every p in P_R the fresh n form the consecutive interval

```text
floor((R^2-1)/p)+1 <= n <= floor((R^2+2R)/p),
```

of length exactly two or three. Distinct p have disjoint such intervals. Every fresh n satisfies `R<n<2p`; hence p does not divide n, and `mu(p*n)=-mu(n)`, including squareful zero coefficients. Distinct fresh pairs have distinct products. Thus F_R is the sum of mu over a genuine cofactor subset with coefficient exactly one, and also the NEGATIVE physical mu sum over its distinct product image. In particular `|F_R|<=3k_R`.

For an endpoint pair with prime p and integer p<n, define

```text
I_(p,n)=[isqrt(p*n)+1, min(n,floor(4p/3))] intersect the integers.
```

An empty interval means no admission. For every integer R>=2 the pair appears in Z_R exactly when R belongs to I_(p,n). Its signed coefficient is mu(n). Thus, for every finite root interval [A,B],

```text
sum_(R=A)^B Z_R^2
 =sum_(u=(p,n),v=(q,m)) mu(n)mu(m)
    max(0,min(upper(u),upper(v),B)-max(lower(u),lower(v),A)+1). (PB2)
```

The sum is over the finitely many admitted pairs whose intervals meet [A,B]; it is an ORDERED double sum, including diagonal and same-cofactor interactions. This is an exact Gram representation, not a favorable-sign estimate. Fixed-root disjointness does not extend across different roots.

#### PB3. Quantitative Boundary Budget

With `D_H=sum_(H<=R<2H)H_R^2` and `E_e(H)=sum e_R^2`, classical PNT and the classical Mertens estimate give

```text
D_H ~ [7/(48 zeta(2))] H^3/log(H)^2;
E_e(H) = o(D_H).                                   (PB3a)
```

More explicitly, for every fixed A>0,

```text
E_e(H) <<_A H^3/log(H)^(2A+1)+H.                   (PB3b)
```

Separately, under ANY explicitly supplied fixed envelope `|M(n)|<=C n^b`, 0<b<1,

```text
E_e(H) <<_(C,b) H^(1+2b)/log H+H.                 (PB3c)
```

PB3c is a conditional consequence of that input, not a new exponent theorem. PB3a-b use only classical logarithmic estimates. The same derivation gives `|C_(R+1)-C_R|=O(R/log R)` and `sum_(H<=R<2H)|C_(R+1)-C_R|^2=O(H^3/log^2 H)`. This proper-source bound remains above the useful `H^(5/2-eta)` scale by a polynomial factor. Summing it in R does not improve yesterday's pointwise Z estimate.

#### PB4. Source-Explicit Inverse Correlation

Put

```text
E_C(H)=sum_(H<=R<2H)(C_(R+1)-C_R)^2;
E_F(H)=sum_(H<=R<2H)F_R^2;
I_H=sum_(H<=R<2H) k_R mu(R)
       sum_(p in P_R) sum_(R^2<=p*n<(R+1)^2) mu(n).
```

For EVERY H>=17, without assuming an upper bound or convergence,

```text
|I_H-D_H| <= sqrt(D_H)*(sqrt(E_C(H))+sqrt(E_e(H))). (PB4a)
```

When D_H>0, set t_H=(sqrt(E_C)+sqrt(E_e))/sqrt(D_H). Then

```text
(max(0,1-t_H))^2 <= E_F/D_H <= (1+t_H)^2.          (PB4b)
```

Consequently, along any sequence H tending to infinity,

```text
E_C(H)=o(H^3/log^2 H) ==> I_H/D_H -> 1
                           and E_F(H)/D_H -> 1.    (PB4c)
```

In particular a hypothetical all-H bound `E_C(H)<<H^(5/2-eta)` with fixed eta>0 would REQUIRE that positive correlation. It is not implied by nonoverlap, prime spacing, squarefreeness, or PB3. Conversely, if for some fixed delta>0 a scale satisfies `I_H<=(1-delta)D_H`, then

```text
E_C(H) >= max(0,delta*sqrt(D_H)-sqrt(E_e(H)))^2.    (PB4d)
```

An independent such deficit on infinitely many large H would rule out that separately-small COLUMN-increment mechanism. No such infinite deficit is proved here; finite data are not substituted for it. This is a necessary correlation criterion on an explicit prime/cofactor graph, not an equivalent reformulation of the canonical objective.

### E. Mathematical Proofs

#### E1. Exact Source And Boundary

For p in P_R, write Y=floor((R^2-1)/p). Then R<=Y<4R/3<2R. Genuine Mobius inversion gives

```text
sum_(a<R,a>=1)mu(a)floor(Y/a)
 =1-sum_(R<=a<=Y)mu(a)=1-M(Y)+M(R-1).
```

The omitted floors are one, and the nested floor is exactly floor((R^2-1)/(ap)). Multiplication by mu(p)=-1 and summation gives the original floor column `Z_R-k_R`. Historical inversion at R-1 is one, so the original rank-one subtraction contributes +(R+1)d_R. This proves D0's C_R=r_R+Z_R and reuses yesterday's row-completion mechanism without re-crediting it.

First keep the OLD prime set P_R while changing the endpoint and historical cutoff. Each prime contributes its fresh interval minus mu(R), producing F_R-H_R. Now restore the actual new mask. Its only possible entry is p=R; its new quotient is `(R^2+2R)/R=R+2`, giving B_R^new. Its exits satisfy exactly `3R<=4p<3R+3`; that interval has width 3/4 and at most one integer. Remove their entire UPDATED rows J_R. This proves PB1a, including cases with simultaneous entry and exit.

Direct subtraction of `(R+1)d_R-k_R` proves PB1b. Since `k_R<=R/4+1`, `d_R<=1/3+4/(3R)`. Each possible exit contributes at most `1/3+8/(3R)` in absolute value and the entry contributes at most 2/R. The sum is at most `2/3+6/R<2` for R>=17. This proves the advertised safe uniform constant, without optimizing it. PB1c follows.

#### E2. Incidence Proof And Limits

The interval length before flooring is `(2R+1)/p`, strictly between two and three at the stated R and p. Its integer count is therefore two or three. If the same n occurs for two primes, those primes lie in the closed real interval `[R^2/n,(R^2+2R)/n]`, of length `2R/n<2` because n>R. Both primes are odd, and distinct odd primes differ by at least two. Thus they cannot both occur.

Also

```text
n <= (R^2+2R)/p <= 4R/3+8/3 < 3R/2 <= 2p
```

for R>=17. Since n>R>p, this proves p does not divide n. If `p*n=q*m` with distinct selected primes, unique factorization forces q|n. But n>q and `n<3R/2<=2q`, a contradiction. This establishes product injectivity and the true Mobius sign. Neither boundary square is a selected product: a selected prime cannot divide R or R+1 in this range. The inclusive lower product convention in PB1 is nevertheless retained.

For PB2's lifetime, the endpoint conditions are exactly `p<R`, `R<=n`, `3R<=4p`, and `p*n<R^2`. Since n>p, the last condition forces `R>=isqrt(p*n)+1>p`. The remaining inequalities give precisely I_(p,n). Squaring this finite sum and summing the intersection lengths proves PB2 with ALL ordered interactions. Replacing this overlap Gram by a sum of isolated squares is not valid.

The fixed-root spacing proof is an elementary specialization of the already compiled `shellHighOwnerCofactorsAdjacent`: its multiplier need not be prime, so use n as multiplier, then use oddness of the two candidate prime factors. The present p<R carrier and two/three-cofactor rows differ from that module's usual high-prime interpretation. No new general spacing or unique-factorization theorem is claimed.

#### E3. Historical Energy And Sparse Exit Cost

PNT gives `k_R~R/(4log R)`, uniformly for H<=R<2H as H tends to infinity. This uses a fixed-ratio prime band, not a prime-in-short-interval hypothesis or a replacement of individual prime indicators by density. The classical inputs were checked at [DLMF 27.12.4-5](https://dlmf.nist.gov/27.12#E4) and [DLMF 27.11.12](https://dlmf.nist.gov/27.11#E12); neither is a new discovery.

For completeness, the squarefree mean needed here follows directly from

```text
mu(n)^2=sum_(d^2|n)mu(d),
sum_(n<=y)mu(n)^2=y/zeta(2)+O(sqrt y).
```

The floor errors and the tail of the absolutely convergent d^-2 series are both O(sqrt y). Partial summation therefore gives `sum_(H<=R<2H)R^2 mu(R)^2=(7/(3zeta(2)))H^3+O(H^(5/2))`. Multiplying by the uniform asymptotic `k_R^2/R^2~1/(16log^2 H)` proves PB3a's constant. There is no probabilistic squarefree-independence premise.

Each prime exits at the unique root `R=floor(4p/3)`. Thus only O(H/log H) roots in [H,2H) have J_R nonzero. Its two Mertens arguments lie between R and 3R/2. The classical Mertens bound implies, for every fixed A>0, `|J_R|<<_A H/log^A H` on those roots. Since `|B_R^new|<=2` and `|delta r_R|<=2`,

```text
E_e(H) <= 2 sum J_R^2 +32H
        <<_A H^3/log^(2A+1) H+H.
```

Taking A>1/2 proves E_e=o(D_H). With the separate input `|M(n)|<=C n^b`, the same support count gives PB3c. The support sparsity alone does not turn a logarithmic Mertens bound into a power saving. PB3's pointwise increment estimate follows from PB1 and `|F_R|<=3k_R`; use A>1 for J_R=O(R/log R). Its dyadic consequence is only a logarithmic improvement on the elementary root energy.

#### E4. Inverse Step Without An Assumed Target

Treat F,H,e and delta C as finite real vectors indexed by H<=R<2H. PB1c says `F-H=delta C-e`. Hence `||F-H||_2<=sqrt(E_C)+sqrt(E_e)`. Cauchy-Schwarz applied to `I_H-D_H=<H,F-H>` proves PB4a; the reverse triangle inequality proves PB4b. PB3 then gives PB4c. The reverse estimate `||delta C||_2>=||F-H||_2-||e||_2` gives PB4d. These finite inequalities do not assume convergence of any infinite norm.

The generic Hilbert-space inequalities are inherited mathematics. The independent arithmetic content is the exact source for I_H, its once-only fresh-cofactor multiplicities, its nonzero asymptotic reference D_H, and the proved smaller complete admission/exit error. No desired source upper bound appears among those inputs.

### F. Structural Consequences And Exact Falsification

The historical term H_R is not k_R independent supplies of one old occurrence. It is the same mu(R) appearing with the exact multiplicity k_R in distinct prime-column boundaries. Treating those columns as independent would erase the compulsory square k_R^2 mu(R)^2. The disjoint fresh intervals do not remove this coherence.

Exact counterexamples from the registered R>=17 domain:

| R | k_R | F_R | H_R | B_R^new | J_R | Z_(R+1)-Z_R |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 17 | 1 | -1 | -1 | -1 | 0 | -1 |
| 19 | 1 | 0 | -1 | 1 | 0 | 2 |
| 22 | 2 | -2 | 2 | 0 | -3 | -1 |
| 57 | 3 | -1 | 3 | 0 | -2 | -2 |
| 317 | 14 | -4 | -14 | 0 | 0 | 10 |
| 1027 | 36 | 12 | 36 | 0 | 0 | -24 |
| 2002 | 64 | 17 | 64 | 0 | 0 | -47 |

R=19 refutes `delta Z=F` and the automatic-payment inequality `(F-H)^2<=F^2`. R=22 has exiting prime 17; omitting its UPDATED row changes the answer by three. R=17 tests simultaneous entry R=17 and exit p=13, with a nonzero birth. These are exact finite refutations, not asymptotic obstructions.

The cofactor 31 occurs as `(R,p,n)=(24,19,31)` and `(26,23,31)`. Fixed-root disjointness therefore cannot be upgraded to global cofactor disjointness. These are distinct physical products, 589 and 713; the coefficient mu(31) is legitimately reused at different roots and products.

The complete executed verifier checks:

| Check | Scope / result |
| --- | --- |
| Independent coefficient check | Trial factorization agrees with sieve at n=1..10000 |
| Full boundary and complement identities | Every R=17..2048, 2,032 roots; PASS |
| Prime rows and physical sites | 74,048 rows, 170,640 fresh pairs; two/three size, both injectivities, gcd and signs; PASS |
| Reverse enumeration | Independent cofactor-first construction agrees at every tested root |
| Literal original floor columns | 67 roots: 17..80 and 317,1027,2002; no row-completion formula used in this calculation |
| Endpoint lifetimes | 64 roots, 17..80; exact source agreement |
| Complete interval Gram | 8,464 ordered pairs on roots 17..40; resulting energy 133 |
| Moving masks | 303 prime-entry roots and 237 exit roots checked |
| Finite inverse/energy tests | H=17,32,64,128,256,512,1024; rational inequalities and complete-square return PASS |

Some exact dyadic diagnostics are:

| H | D_H | E_F | I_H | sum(F-H)^2 | sum(delta Z)^2 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 17 | 22 | 31 | -2 | 57 | 42 |
| 64 | 1014 | 471 | -105 | 1695 | 1675 |
| 256 | 41247 | 4364 | 358 | 44895 | 43590 |
| 1024 | 1759325 | 62690 | -15522 | 1853059 | 1850263 |

Both signs of I_H occur. The necessary asymptotic alignment is NOT seen in these finite samples; this does not prove it impossible eventually. No exponent was fitted. In particular these finite values cannot refute an all-scale big-O assertion with an unspecified constant.

Verifier SHA256: **e6a4fbf33bb9c4afd584c46da9dbc968b8b575593df7362237839463f7a639d5**. Deterministic exact-result payload SHA256: **2aa76aca7decc7bed8d112741f0c2cacf45b329ae67a2a00e2fa13fc8e7a9674**. Runtime assertions and Python syntax compilation passed. Two enumeration methods are same-session verification, not an independent Referee verdict. The full executed code follows this synthesis.

### G. Complete Signed Return And Quantitative Relevance

The actual full source is still Q_R=C_R+V_R. For the genuine square-shell sum `S_R=sum_(R^2<=n<(R+1)^2)mu(n)`, the compiled endpoint identity gives

```text
S_R=2mu(R)-delta C_R-delta V_R;
S_R^2=(delta C_R)^2+(delta V_R)^2+2delta C_R delta V_R
      -4mu(R)(delta C_R+delta V_R)+4mu(R)^2.        (RETURN)
```

All historical, prime/complement and within/between-column interactions are restored. Large C and V increments may cancel; their separate smallness is not required by finite C or by the shell consumer. PB4 constrains a proposed componentwise proof mechanism, not every legitimate signed recombination.

The new upper estimate for E_C has scale H^3/log^2 H. It does not pay H^(5/2-eta), improve the inherited Mertens exponent, or bound Q_R at R sqrt(K_R). A bound on I_H alone does not establish finite C either. `NEW_NET_ENDPOINT_GAIN=UNKNOWN / NONE_ESTABLISHED; ETA_GATE=SEARCH_BROAD`.

### H. Novelty, No-Circularity And Formal Evidence

Repository searches included prime-sampled, prime-band birth, cofactor retirement and square-shell prime incidence, followed by actual source inspection. The existing admissible-prime chronology fixes X and adds primes p>=R; PB1 instead changes X and the p<R partial historical mask simultaneously. The older `shellHighOwnerCofactorsAdjacent` already supplies the relevant elementary width restriction, and the two-prime orbit theorem already supplies the same-sign fresh-prime law at its own scope. Neither is claimed new here. Yesterday's row completion and four-block identity, unique factorization, squarefree mean, PNT, Mertens logarithmic cancellation, and Cauchy-Schwarz are also inherited.

No identical complete partial-prime-mask increment, reference-energy constant, and PB4 inverse statement was found in the inspected source and two-day handoffs. This is a scoped repository novelty check, not a literature-originality claim. PB2 by itself is a representation; PB3 is independently proved quantitative component information; PB4 is a necessary inverse implication, not a proved desired bound. The full finite-C upper estimate remains explicitly target-strength and open.

**Formal evidence freshly checked:** PR #1095 is merged, final head **46e68178192c6e429a02abee9d5b8ebca5de46c8**, merge **1667c3cf9b4e898bb9afd62ec48e24610b2156ab**. All three attached checks returned success. The [dedicated log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42084042187/job/127444267657) records 17 successful audit regressions, seven newly compiled research modules, and exact coverage of eight requested Euler declarations with standard axioms. The current original floor/rank-one blobs match the reviewed source. Thus yesterday's V1 fail-open warning is superseded by a verified repair, not silently retained as an active defect. No CI was triggered by this run.

PR #1096 is merged at the pinned main, final head **ecf701ff2fea1de52e505ee34048a2b3c220f0fc**; its finite odd-boundary proof is not an input to PB1-PB4. The only open PR at intake is non-draft **#1097**, head **bc727dc9f7dd655fdd2addc943b246ad70ef576d**, still UNMERGED. All 13 attached checks returned success. Its source blob **e823a1a124dc1bfe4c38d4af4ee10c1e481cad2a** and the [nine-declaration sampling audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42203731194/job/127845057234) were inspected; each audited declaration lists propext, Classical.choice, Quot.sound. That job reused three compiled modules and freshly ran its theorem/axiom harness. This certifies its sampling scope, not CP2's weighted integrals and certainly not today's PB claims. No local Lean was run.

### I. Conceptual Interpretation

The same arithmetic data has two different incidence structures. New physical products have disjoint cofactor labels at a fixed root, but advancing the historical cutoff removes one shared cofactor sign from many different prime columns at once. The latter creates a coherent square, not a small diagonal proportional only to the number of primes. Exact prime geometry identifies both mechanisms and keeps them in the same signed equation.

This makes a proposed cancellation assertion falsifiable: it must create the explicit positive correlation I_H near D_H, or preserve compensation with the complete complementary columns. Merely saying the new products are disjoint supplies neither conclusion.

### J. Competing Structural Hypotheses

| Proposal | Disposition |
| --- | --- |
| Count only new products to obtain delta Z | REFUTED at R=19; births, history and mask exits are genuine |
| Fixed-root cofactor disjointness extends across all roots | REFUTED by cofactor 31 at roots 24 and 26 |
| Historical subtraction always reduces fresh energy | REFUTED at R=19 and the displayed dyadic tests |
| Separately small E_C follows automatically from the exact four-block endpoint cancellation | NOT ESTABLISHED; PB4 exposes the additional positive-correlation demand |
| I_H has a fixed fractional deficit on infinitely many large H | OPEN, a possible proper-source obstruction; seven finite windows do not prove it |
| Full delta C/delta V signed cancellation can bypass separate column estimates | OPEN and not excluded by this report |

### K. Continuity And Specialist Handoffs

Intake reports were retrieved from **34fafc2801539e603e05b5ce7a3b57812021c229**, beginning during this actual 15:12 UTC invocation. Applicable result, proof, correction, verdict and resume sections from both Eastern calendar days were read. Unrelated executable appendices were not all rerun or blanket-endorsed. The Coordinator's matching AM/PM blobs represent one mirrored record.

| Role | November 5 blob | November 6 blob at intake | Consumed original claims / status |
| --- | --- | --- | --- |
| Coordinator | be661bb2ed2830fc4aeddf14713455e550d982cc | ed98da5ddf755803c0fb9249ccf5bdb58f59658c | C53-C57 finite-AC/CORR4 distinctions; C63-C68 fixed-bank and cross-core limits. Today's completed synthesis TODAY=PENDING; YESTERDAY=CARRY_FORWARD |
| Owner | 39665b5b28fc48378519ab9d56cee8df4d3e2681 | fd30796d1b10e58e694f1d85252dac3cd8099a94 | RC/CR/MC; today's BT/RZ and DR1-DR7. Distinct SAT/VF/JOH carriers, no finite-C upper supplier |
| Analytic | 9490aa2eecafcd19d8007043cc5f978fe421a7c9 | b075be67af6294e41f6eb232f611c208799c5e04 | SP obstruction, CR physical-row limitation; FP parent survives phase averaging; RM moment design still owes middle return |
| Wheel | afc85d800c47f82f2db634591a7798005cb668de | d7bf40e297ed87f0899f759fa7aab7f577e134ed | P1-P4 resumed; PE1-PE4 retained; today's CP1-CP4 now independently accepted on paper |
| Census | 24fcd6a631eca9ae44238d927215f49e1d8a174f | dfe20627512b4ad1fe62c83bbb2e0412390c100f | R=57/58 joint caps and JOH X=209 halo sign; GM1/GM2 exact matching evidence, X=145 frozen-edge obstruction; GM3 paper scope |
| Referee | 789ed87021fe98963c244a8d0c9075638e76be43 | 01cf41cbc62f430f9034870509f6b3947866a4e9 | referee-11 ACCEPT_WITH_SCOPE for PE1-PE4; referee-14 13c/15c extension; today's referee-1 accepts CP1-CP4; TD is separate self-derived paper work |
| Lean | 5e0ecdd8f08c2e19b4614f00c1a5657f58722344 | 7138b713a44f514ade3a64db44268c1934b215d0 | #1095 repair and #1096 finite proof now merged; 20261106-lean-1/CP1-SAMPLING verified at unmerged #1097 only |

Original publication receipts inspected include Coordinator November 5 at November 6 04:35:36 UTC; Analytic November 5 at 17:37 EST; Referee November 5 at November 6 01:33:35 UTC; today's Owner 08:37 EST, Analytic 14:48:55 UTC, Census 08:44:24 UTC, Referee 09:41:27 UTC and Lean 05:43:31 EST. These are upstream recorded receipts, not claims that this agent independently reran all their experiments. P1-P4 have no newly located independent acceptance; today's CP acceptance does not cover them or PB1-PB4.

The external inbox remains **038018145c0fddb2f6306c0712373adf9cd1ea52**, with no entry newer than October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain original-source, cutoff and conditional-versus-unconditional cautions. Their old compulsory route and cadence prose is superseded. They do not supply a finite-C estimate.

| Recipient | Precise report-only handoff |
| --- | --- |
| Coordinator | Register PB3/PB4 as component-energy and inverse information, not VERIFIED_ETA. Preserve the complete delta C/delta V alternative and MU-LIFT next. Today's incomplete Coordinator stage is not counted as completed. |
| Referee | Reconstruct PB1 with updated exit rows; audit R>=17, the PB3 constant 7/(48zeta(2)), unique exit roots, and PB4's necessary-only scope. PB1-PB4 await independent review. |
| Analytic | Assess I_H on its literal prime strip, with k_R mu(R), both signs and n>R. A fixed deficit would obstruct only separate-column smallness; positive alignment is not assumed. Do not import a fixed-endpoint or differently weighted correlation. |
| Census | Reproduce R=19/22 and H=64/256 from independent coefficients and both enumeration orders. No larger scan or fitted exponent is requested. Distinguish finite sign changes from an asymptotic deficit. |
| Owner | Shared historical coefficients can create k_R^2 energy despite disjoint new products. This is a method warning, not a map to VF prime-seat supply, chronological charge, or returned masks. |
| Lean Verification | No immediate new proof branch requested for self-audited PB claims. If independently accepted and useful, PB1's exact finite boundary is the smallest implementation unit; PB3 requires separate analytic infrastructure. Reuse #1097 rather than duplicate it. |

These handoffs are published only inside this own authorized report. No other agent is launched or presumed to act.

### L. First Independently Missing Theorem

The original finite-C upper bound for the FULL Q_R remains open. Today's new source-specific missing input is a genuine quantitative theorem for

```text
I_H=sum_(H<=R<2H) k_R mu(R)
       sum_(prime 3R/4<=p<R) sum_(R^2<=p*n<(R+1)^2) mu(n),
```

at its natural reference scale D_H. Neither `I_H/D_H -> 1` nor a fixed asymptotic deficit has been proved. Even proving one would not, by itself, settle the complete finite-C consumer. Alternatively, work directly on the full signed increment return (RETURN), where separate E_C smallness is not required.

The pointwise Z_R improvement requested in yesterday's capsule was not obtained. The strongest valid continuation is PB1-PB4 plus the finite falsifiers. No missing inequality was hidden as an admissibility condition or assumed bound.

### M. Source Ledger And Next-Run Capsule

All listed main sources were retrieved at 4a6e6b8c; relevant definitions, statements and arguments were inspected. Historical CI was reused at its exact scope, not rerun locally.

| Source | Git blob SHA |
| --- | --- |
| AGENTS.md | 547dda0d9456e7a4e1165dc72d59da6f70d5c023 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md | ffd8f1c65cc4da656174956d4e03b48bea46768b |
| research/EULER_RANK_ONE_FRACTIONAL_ROWS_20261027.lean | e482711a3f55c1f59fc771f108671477f51732f2 |
| research/EULER_FRACTIONAL_COUPLED_20261027.lean | e6c4b1690e497760d366e36b28a1f7aa60e19f85 |
| research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean | e97561ef330a9996fd807d8910369f0698147b01 |
| research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| RHLean/Proof/SquareRootMertensEndpointAmplification.lean | 7793d7bfd842348facf62a7ad856bc802ffcd15c |
| RHLean/Proof/SquareRootLegalAncestryGramReduction.lean | 1270d4d91c53b50b110d10014f223f427fb7a575 |
| research/EULER_ADMISSIBLE_PRIME_POPULATION_CODIV_20261028.lean | 08493abd6ac18bff5d8ac0560b4e0d9444e99355 |
| research/EULER_ADMISSIBLE_SIGNED_RETURN_TELESCOPE_20261028.lean | 99453a189ed19fd5c3a78ed1bf735bc3cb73c8f2 |
| research/EULER_PRIME_RAY_SOURCE_ADMISSION_20261031.lean | d164dccf992e24fe1c6378fefa75c03535ad5de8 |
| research/SQUARE_SHELL_INCIDENCE_COMPENSATION_20261017.md | d7826257273473e80948117ea5c0fcd04713af6f |
| research/SQUARE_SHELL_INCIDENCE_COMPENSATION_LEAN.lean | 6f6fb9ef3e7bba68f4a1b015a90c96f61c120917 |
| research/SQUARE_SHELL_TWO_PRIME_ORBIT_20261018.lean | 639cc98a1f8c2afc4053006996d52bc94cd3230d |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| .github/workflows/euler-fractional-coupled.yml | ca6547a55198256ce9b5d71ab1b43eb97b98067c |

```text
RUN: 20261106-wheel-2, scheduled 10:12:01 EST; RUN_ID_UNAVAILABLE.
MAIN: 4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1; SEARCH_BROAD.
ROUTE: FINITE-AC, actual partial historical prime column.
RESUMED: 20261105-wheel-2/P1-P4, full prime-column r_R+Z_R.
NEW: complete moving boundary, sparse paid exits, compulsory component
     D_H~7/(48zeta(2))*H^3/log^2H, and explicit inverse correlation.
NOT NEW: row completion, shell spacing, PNT, squarefree mean, norm algebra.
FINITE: 2032 roots, 170640 fresh pairs, 67 literal source columns,
        64 lifetime roots, 8464 ordered overlap pairs; all assertions PASS.
REVIEW: PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING.
FORMAL: PB1-PB4 NOT_FORMALIZED. No local Lean or proof-source edits.
LIMIT: no new pointwise Z improvement; no infinite correlation deficit;
       complete complement and every mixed term still owed.
LAST THREE: Nov5 MU-LIFT; Nov6 CORR4; this FINITE-AC turn.
NEXT DISTINCT ROUTE: MU-LIFT, resume referee-14, Coordinator C63-C66
       and Census GM1-GM3; X=145 freezes a nonextendible partial matching,
       not a full-graph obstruction. Do not repeat fixed-bank pool counts.
NEXT FINITE-AC: independently assess the actual I_H or complete RETURN;
       do not infer component smallness from nonoverlap or optimize constants.
NET NEW ENDPOINT GAIN: UNKNOWN / NONE_ESTABLISHED.
CANONICAL VF / FINITE-C / RH: OPEN.
```

Checkpoint commit **3f28020bf5100e1f3adde7d70bdb0d942d9d98b2**, blob **928d5c10438d283993adf896a82ebe01392baf86**, was read back exactly. Final publication is certified only in the subsequent receipt. Direct shell GitHub cloning failed with CONNECT 403; connected source/report reads and authorized own-report writes succeeded. Only this authorized report was changed remotely: no Lean source, workflow, other report, issue, PR, policy, permission, schedule or main change, and no branch creation. No agent was launched and no background computation is promised.

### Complete Executed PB5 Verifier

```python
"""Exact prime-band boundary tests; finite evidence, not an exponent proof."""

from array import array
from collections import Counter, defaultdict
from fractions import Fraction as Q
from hashlib import sha256
from math import gcd, isqrt
import json


def sieve(limit):
    mu = array('b', [1]) * (limit + 1)
    mu[0] = 0
    prime = bytearray(b'\1') * (limit + 1)
    prime[0] = prime[1] = 0
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p, limit + 1, p):
                mu[n] = -mu[n]
                if n != p:
                    prime[n] = 0
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    m = array('i', [0]) * (limit + 1)
    for n in range(1, limit + 1):
        m[n] = m[n - 1] + mu[n]
    return mu, prime, m


def trial_mu(n):
    value, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            value = -value
            if n % p == 0:
                return 0
        p += 1
    return -value if n > 1 else value


def main():
    last = 2048
    mu, prime, m = sieve((last + 2)**2)
    primes = [p for p in range(2, last + 2) if prime[p]]
    assert all(mu[n] == trial_mu(n) for n in range(1, 10001))
    counts = Counter(independent_trial_coefficients=10000)

    def band(r):
        return [p for p in primes if 3 * r <= 4 * p and p < r]

    def data(r):
        ps = band(r)
        x = r * r - 1
        z = sum(m[x // p] - m[r - 1] for p in ps)
        reciprocal = sum((Q(1, p) for p in ps), Q(0))
        rank = (r + 1) * reciprocal - len(ps)
        return ps, z, reciprocal, rank

    values = {r: data(r) for r in range(17, last + 2)}
    rows = {}
    failures = {}
    fixtures = {}
    for r in range(17, last + 1):
        ps, z, reciprocal, rank = values[r]
        qs, zn, _, rankn = values[r + 1]
        old, new = set(ps), set(qs)
        enters, exits = new - old, old - new
        assert enters == ({r} if prime[r] else set())
        assert exits == {p for p in ps if 3 * r <= 4 * p < 3 * r + 3}
        assert len(exits) <= 1
        atoms = []
        for p in ps:
            ns = list(range((r * r - 1) // p + 1, (r * r + 2 * r) // p + 1))
            assert len(ns) in (2, 3)
            counts['prime_rows'] += 1
            for n in ns:
                assert r < n < 2 * p
                assert gcd(p, n) == 1 and mu[p * n] == -mu[n]
                assert r * r < p * n < (r + 1)**2
                atoms.append((p, n))
        assert len({n for p, n in atoms}) == len(atoms)
        assert len({p * n for p, n in atoms}) == len(atoms)
        fresh = sum(mu[n] for p, n in atoms)
        # Independent cofactor-first enumeration of the same physical strip.
        reverse = []
        for n in range(r + 1, (4 * r + 8) // 3 + 1):
            candidates = [p for p in range(max((3 * r + 3) // 4, (r * r + n - 1) // n),
                                            min(r - 1, (r * r + 2 * r) // n) + 1)
                          if prime[p]]
            assert len(candidates) <= 1
            reverse.extend((p, n) for p in candidates)
        assert sorted(atoms) == sorted(reverse)
        birth = mu[r + 1] + mu[r + 2] if prime[r] else 0
        leave = sum(m[(r * r + 2 * r) // p] - m[r] for p in exits)
        history = len(ps) * mu[r]
        dz = zn - z
        assert dz == fresh - history + birth - leave
        dr = rankn - rank
        dr_formula = reciprocal + sum((Q(r + 2, p) - 1 for p in enters), Q(0))
        dr_formula -= sum((Q(r + 2, p) - 1 for p in exits), Q(0))
        assert dr == dr_formula and abs(dr) <= 2
        dc = dz + dr
        error = Q(birth - leave) + dr
        assert dc == fresh - history + error
        assert abs(fresh) <= 3 * len(ps)
        assert abs(dz) <= 4 * len(ps) + 2 + abs(leave)
        assert abs(dc) <= 4 * len(ps) + 4 + abs(leave)
        q0 = 2 * m[r - 1] - m[r * r - 1]
        q1 = 2 * m[r] - m[(r + 1)**2 - 1]
        c0, c1 = z + rank, zn + rankn
        dw = (q1 - c1) - (q0 - c0)
        shell = m[(r + 1)**2 - 1] - m[r * r - 1]
        assert shell == 2 * mu[r] - dc - dw
        assert (q1 - q0)**2 == dc**2 + dw**2 + 2 * dc * dw
        counts['root_identities'] += 1
        counts['physical_shell_atoms'] += len(atoms)
        counts['mask_exit_roots'] += bool(exits)
        counts['prime_birth_roots'] += bool(enters)
        record = {'R': r, 'k': len(ps), 'mu_R': mu[r], 'Z': z, 'Z_next': zn,
                  'fresh': fresh, 'history': history, 'birth': birth,
                  'exit': leave, 'exit_primes': sorted(exits), 'delta_Z': dz,
                  'delta_rank': str(dr), 'delta_column': str(dc)}
        if dz != fresh:
            failures.setdefault('fresh_only', record)
        if leave:
            failures.setdefault('omit_mask_exit', record)
        if birth:
            failures.setdefault('omit_birth', record)
        if history and (fresh - history)**2 > fresh**2:
            failures.setdefault('automatic_history_payment', record)
        if r in [17, 18, 19, 20, 23, 24, 26, 31, 32, 56, 57, 317, 1027, 2002]:
            fixtures[r] = record
        rows[r] = {'F': fresh, 'h': history, 'J': leave, 'B': birth,
                   'dz': dz, 'dc': dc, 'error': error}

    # The historical floor column is computed without the row-completion formula.
    for r in list(range(17, 81)) + [317, 1027, 2002]:
        ps, z, reciprocal, rank = values[r]
        floor_column = -sum(mu[a] * ((r * r - 1) // (a * p))
                            for p in ps for a in range(1, r))
        assert floor_column == z - len(ps)
        actual_column = floor_column + (r + 1) * reciprocal
        assert actual_column == rank + z
        counts['literal_floor_column_checks'] += 1

    # Occurrence lifetimes and the COMPLETE ordered interval-overlap square.
    occurrences = []
    for p in primes:
        if p > 80:
            break
        for n in range(p + 1, 2 * p):
            lo, hi = isqrt(p * n) + 1, min(n, 4 * p // 3)
            if lo <= hi:
                occurrences.append((p, n, lo, hi))
    for r in range(17, 81):
        active = [(p, n) for p, n, lo, hi in occurrences if lo <= r <= hi]
        direct = [(p, n) for p in band(r)
                  for n in range(r, (r * r - 1) // p + 1)]
        assert sorted(active) == sorted(direct)
        assert sum(mu[n] for p, n in active) == values[r][1]
        counts['lifetime_roots'] += 1
    overlap = 0
    small = [o for o in occurrences if o[2] <= 40 and o[3] >= 17]
    for p, n, lo, hi in small:
        for q, v, low, high in small:
            length = max(0, min(hi, high, 40) - max(lo, low, 17) + 1)
            overlap += mu[n] * mu[v] * length
            counts['ordered_overlap_pairs'] += 1
    assert overlap == sum(values[r][1]**2 for r in range(17, 41))
    assert (19, 31) in [(p, n) for p in band(24)
                       for n in range((24**2 - 1) // p + 1, (25**2 - 1) // p + 1)]
    assert (23, 31) in [(p, n) for p in band(26)
                       for n in range((26**2 - 1) // p + 1, (27**2 - 1) // p + 1)]

    energies = []
    for h in [17, 32, 64, 128, 256, 512, 1024]:
        block = [rows[r] for r in range(h, 2 * h)]
        diagonal = sum(v['h']**2 for v in block)
        fresh_energy = sum(v['F']**2 for v in block)
        mixed = sum(v['F'] * v['h'] for v in block)
        difference_energy = sum((v['F'] - v['h'])**2 for v in block)
        assert difference_energy == diagonal + fresh_energy - 2 * mixed
        assert (mixed - diagonal)**2 <= diagonal * difference_energy
        column_energy = sum((v['dc']**2 for v in block), Q(0))
        error_energy = sum((v['error']**2 for v in block), Q(0))
        assert difference_energy <= 2 * (column_energy + error_energy)
        if column_energy <= Q(diagonal, 16) and error_energy <= Q(diagonal, 16):
            assert 2 * mixed >= diagonal
        energies.append({'H': h, 'D': diagonal, 'fresh_energy': fresh_energy,
                         'mixed': mixed, 'difference_energy': difference_energy,
                         'delta_Z_energy': sum(v['dz']**2 for v in block),
                         'exit_energy': sum(v['J']**2 for v in block),
                         'automatic_half_alignment': 2 * mixed >= diagonal})
    payload = {'checks': dict(counts), 'failures': failures,
               'fixtures': fixtures, 'dyadic_energies': energies,
               'overlap_energy_17_40': overlap,
               'cross_root_reuse': [[24, 19, 31], [26, 23, 31]],
               'all_assertions': 'PASS'}
    digest = sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()
    print(json.dumps({'payload_sha256': digest, **payload}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
```

### Verified Publication Receipt - 20261106-wheel-2

At **2026-11-06T15:40:51Z / 10:40:51 EST**, final synthesis commit **35bebb491500af17262c3d4045e80670430281ff**, report blob **190a890f5215c5849cffa193e5265e795bba841f**, was retrieved at its immutable commit and matched the complete intended text exactly. The changed-file audit shows exactly this authorized dated report, **647 additions / 0 deletions**. All earlier report sections and the early checkpoint were preserved byte-for-byte. This receipt records a verified prior commit, not an unperformed future action.

**EXECUTION=COMPLETE; PUBLICATION=VERIFIED; PB1-PB4=PAPER_PROOF/SELF_AUDIT/INDEPENDENT_REVIEW_PENDING/NOT_FORMALIZED; PB5=FINITE_COMPUTATION_PASS; NEW_NET_ENDPOINT_GAIN=NONE_ESTABLISHED.** The current canonical bound and finite-C upper supplier remain open. No source/PR/CI change or agent launch was made. Next protected distinct route: MU-LIFT, using the exact resume capsule above. No future scheduled execution is presumed.
