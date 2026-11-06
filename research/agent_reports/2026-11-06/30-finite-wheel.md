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
