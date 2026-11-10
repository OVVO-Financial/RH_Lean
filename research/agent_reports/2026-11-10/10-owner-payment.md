# RH | Owner Payment - 2026-11-10

## Early Checkpoint - 20261110-owner-1/HM

### A. Most Important Mathematical Development

IN_PROGRESS. Investigating the actual cross-prime interaction inside Referee AP's adaptively paid owner packet. The proposed hypothesis is that cofactor saturation forces a common reciprocal-prime profile, so a small total can coexist with large individual fibre energy and forced negative aggregate off-diagonal interaction. This is not yet a proved claim, an independent Referee verdict, or a new RH supplier.

### B. Current Authoritative Objective

Scheduled invocation: 2026-11-10 00:09 EST (America/New_York).
MAIN=7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9.
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.
AGENTS=6695522a45d67fd1e80a7cff1f98d909405036e2.
CONTRACT=95566e37c8eaeb99ee680660df4f9d2e06ea5038.
DIRECTIVE=e505f35522b675c6b5b263eac73618d717346973.
COMPLETE_WHEEL_SOURCE=ecb482e52deeee5e9b3853592a3ffdace662d2ff.

For integer R>=2, X=R^2-1, y=R-1, P_y=product_(prime p<=y)p:
F_R=sum_(d|P_y)mu(d)fract(X/d),
D_R=X*delta(y)+pi(y)-1-li(X),
Z_R=F_R-D_R=li(X)-pi(X).
OPEN: one C>=0 such that every R>=2 satisfies |Z_R|<=C R log R.
All physical/virtual Euler compensation, d=X, root primes, and principal-value li remain unchanged.

### C. Registered Investigation

Reuse CF1-CF4, AP1-AP3 and CD1-CD4; do not rediscover their totals or fixed-cutoff obstructions.
For Q={prime q:R<=q<2R}, test the individual original owner packet
T_q(z)=sum_(prime p<=z or R/2<=p<R)[N_p(floor(X/q))-(X/q)*delta(p-1)/p],
where 2<=z<R/2 and z^2>=R. Recover the exact cofactor formula, all cross-q terms, and the full original complement before any conclusion.

Competing predictions:
1. A common adaptive cutoff makes every individual T_q small.
2. It makes only the total small; arithmetic reciprocal dispersion forces large fibre energy and organized sign change.

Registered tests BEFORE execution: all admissible cutoffs for integer R=8..128, plus held-out roots 257,549,1024 at admissible cutoffs; exact integer/Fraction arithmetic; direct physical least-factor implementation against the saturated formula; independent divisor checks at small roots; root-prime, squareful-cofactor, d=X and virtual controls. If an adaptive crossing is absent, report that absence, never infer a large-root threshold from it. Seek smallest literal counterexamples to the pointwise |T_q|<=1/2 and monotonicity strengthenings when their exact hypotheses hold. Do not fit constants.

### D-K. Continuity, Scope And Next Action

At refresh, November 10 upstream reports are absent: TODAY=PENDING; YESTERDAY=CARRY_FORWARD. November 9 Coordinator 00/90 mirrors agree at 6fba43130391ad4a606aa3809c20f344d668c709; Owner 643e8a004d9d8e0be102b03e2f79bb3b217ae916; Analytic d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3; Wheel 0624246d03b19cf76c01e186b7d868a248d896ef; Census 8c927cc6c323533ba1cfd369404b25aa4f9cef91; Referee a5d0192eb31c0efb3767187a7752f1a0d07f8534; Lean 8b60c6136ac151774be2db0aee8f543f286b53aa. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry after October 18.

Latest Coordinator CD rejects both pure fixed-cutoff families but retains AP's adaptive proper packet. CF's same-q upper/lower sign rule is refuted at R=8 and its positive-upper version at R=11. ZD's proper middle-band improvement, RF/NC's paid matching subsets, and the full missing return remain separate. No all-scale endpoint gain is inferred.

Live PR discovery: only open PR #1127, non-draft, head 866b3d2121309cdd854f9d64e2a6adbbc708ef9b; sharper density/cofactor result is not on main. Recent #1124/#1125/#1126 are merged. Prior reports distinguish #1125's missing exact-head execution from #1126's conditional consumers; current evidence will be checked before final classification.

Next action: derive source-exact reciprocal-profile and complete covariance inequalities, falsify pointwise upgrades, and determine whether anything beyond AP's already-paid packet follows. Only the owned daily report may be modified remotely. No Lean execution, branch/PR change, agent launch, schedule change or main write is authorized/performed.

## Reciprocal-Prime Profile, Harmonic Sign Boundary, And Forced Cross-Fibre Cancellation
### Final Research Synthesis - 20261110-owner-1/HM

### A. Most Important Mathematical Development

**The adaptively paid owner packet is not small fibre by fibre. Its large individual contributions follow a rigid reciprocal-prime profile and cancel across distinct large-prime fibres.** Every saturated cutoff changes the mean-centered vector in only ONE direction, proportional to 1/q. The remaining transverse squared norm is at most m/4, uniformly in the root and cutoff, where m counts the actual primes in [R,2R).

Combined with the previously proved adaptive prefix and ordinary PNT/Mertens inputs, this forces a sign boundary near the harmonic mean of those genuine primes, with only an O(log R)-wide possible exception interval. The entire selected packet has total O(R/log R), but its sum of fibre squares is asymptotic to
exp(-2 gamma)*(1/2-log(2)^2)*R^3/log(R)^3.
Its COMPLETE unordered cross-fibre sum is asymptotic to minus half that quantity. Even cutting this already-paid packet at 3R/2 destroys its affordable total: the two resulting disjoint totals have opposite nonzero leading terms of order R^2/log(R)^2.

This is a genuine arithmetic restriction and a scoped no-go for localizing the adaptive payment. It is NOT a new bound for the full centered discrepancy. The complement and every mixed term remain unpaid.

| Claim | Exact advance | Classification |
| --- | --- | --- |
| 20261110-owner-1/HM1 | Saturated packet family is affine in the reciprocal-prime vector; transverse energy <=m/4 and explicit complete variance bounds | PAPER_PROOF; source-specific uniform proper-component restriction |
| HM2 | Finite harmonic-mean sign localization with explicit uncertainty interval | PAPER_PROOF, conditional only on the displayed finite balance test |
| HM3 | Adaptive all-root-eventual sign profile, positive L1/diagonal asymptotics and negative complete off-diagonal asymptotic | PAPER_PROOF, using AP's paper selection and independently checked classical inputs |
| HM4 | Every fixed proper q-prefix cut has an explicit positive leading residual; separate RH-scale payment of those pieces is false | PAPER_PROOF / REFUTED auxiliary localization |
| HM5 | Exact smallest balanced-packet counterexamples and registered source/variance tests | FINITE_COMPUTATION / REFUTED pointwise strengthenings |

All new HM mathematics is **SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. AP and CD retain their original attribution. No novelty is claimed for elementary variance inequalities, PNT, or the existing first-crossing argument. NEW_VERIFIED_GLOBAL_ENDPOINT_GAIN=NONE. Complete finite-wheel RH bound, canonical VF, finite A/C and RH remain OPEN.

### B. Current Authoritative Objective

MAIN=7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9; finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1. The original source is the [complete square-root wheel module](https://github.com/OVVO-Financial/RH_Lean/blob/7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9/research/CompleteSquareRootWheelFractionalBoundary.lean), not a stochastic or ideal-character model.

For every integer R>=2:
~~~text
X=R^2-1, y=R-1, P_y=product_(prime p<=y)p,
delta(y)=product_(prime p<=y)(1-1/p),
F_R=sum_(d|P_y)mu(d)fract(X/d),
D_R=X*delta(y)+pi(y)-1-li(X),
Z_R=F_R-D_R=li(X)-pi(X).

OPEN: exists ONE C>=0, forall integer R>=2, |Z_R|<=C R log R.
~~~

The source theorem finiteWheel_squareFractional_centered_eq_reference_sub_pi accepts an arbitrary real reference L. Its equality is certified, not its desired bound. Principal-value li is retained; Li_2 differs by a fixed constant. R^2 is composite, but the Li endpoint still has its own adapter. The canonical terminal riemannHypothesis_of_vfCanonicalSquare explicitly takes ClassicalVonKochRHCriterion; this invocation does not construct it.

Every virtual d>X stays until its fractional X/d term cancels against its own Euler contribution. d=X, root primes, squareful physical cofactors and cofactor-one primes are retained. No signed-to-unsigned substitution is used to define the new source.

| Material file inspected | Blob SHA |
| --- | --- |
| AGENTS.md | 6695522a45d67fd1e80a7cff1f98d909405036e2 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_SEVEN_AGENT_FINITE_WHEEL_BOUNDARY_20261108.md | e505f35522b675c6b5b263eac73618d717346973 |
| docs/DYNAMIC_RESEARCH_AGENTS.md | e8d913ff9663bb5163eaf0eddca9f76e0508a7ef |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| research/CompleteWheelRootAdmission.lean | a412632c1028d7728cd8d87ee6e5ac365377d338 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| RHLean/Proof/AmplificationExponentIteration.lean | d78be4509e5dcc35b833c3786258b94fc6e71915 |
| RHLean/Proof/SquareRootAmplificationZeroLogConsumer.lean | b7e6b9170a22a77ac1be56c5d1da2956906e99c6 |

### C. Structural Hypothesis Investigated

The latest Coordinator CD and Referee AP handoffs ask whether the adaptively selected proper packet leads to a genuinely new interaction with its complement. Before proposing such a transfer, this execution resolves a smaller uncertainty: does adaptive payment make its genuine constituent fibres individually small, or does it require their large cross-prime interaction?

Registered rivals were pointwise smallness versus organized cross-fibre cancellation. The original CF mask, AP saturation and cutoff were fixed before testing. The exact profile, transverse norm and harmonic boundary were proof-led consequences of that question, not fitted to samples. HM does not repeat CF's same-q upper/lower sign scan or CD's fixed-cutoff expansions.

The new finite claims work at EVERY admissible root and saturated cutoff. Only the asymptotic consequences invoke the eventual AP choice. No finite test is used to infer AP's unknown onset.

### D. Mathematical Derivation

#### HM1. Exact Physical Row And Its One-Dimensional Cutoff Dependence

Fix integer R>=8 and integer z satisfying
~~~text
2<=z<R/2, z^2>=R.
Q={prime q:R<=q<2R}, m=#Q>0,
x_q=X/q, t_q=floor(x_q), r_q=fract(x_q),
h=floor((R-1)/2), H=pi(h),
w_p=delta(p-1)/p, W=delta(h)-delta(y),
N_p(t)=#{integers 2<=a<=t: leastPrime(a)=p}.
~~~
The finite assertions below need only m>0; ordinary PNT supplies it eventually. They require no prime-gap or independence hypothesis.

Define the INDIVIDUAL original packet
~~~text
T_q(z)=sum_(prime p<=z or R/2<=p<R)[N_p(t_q)-x_q*w_p],
E(z)=sum_(q in Q)T_q(z),
a(z)=delta(z)-W, b(z)=pi(z)-H-1.                 (HM.1)
~~~
The selected owner ranges are disjoint. A physical integer aq has a<R<=q; it cannot belong to two different Q fibres, since qq'>=R^2>X. The prime q itself has a=1 and is not in N_p. Squareful a are included.

The original inclusion-exclusion bridge, credited to CF1, is
~~~text
N_p(t_q)-x_q*w_p
 = -sum_(e|P_(p-1))mu(e)*fract(X/(p*q*e)).       (HM.2)
~~~
Here p is the least physical owner but the greatest prime in the divisor packet p*e. q is only a physical mask; the sign is mu(e), NOT mu(q*e). The allocated reciprocal reference is exactly x_q*w_p. Thus (HM.2) preserves the complete virtual compensation, not a truncated fractional cube.

Since t_q<R and z^2>=R, every composite cofactor has least prime <=z. Also t_q>=h>=z. Upper owners p>=R/2 can contribute only prime cofactors. Therefore the two selected counts are
~~~text
sum_(p<=z)N_p(t_q)=t_q-1-pi(t_q)+pi(z),
sum_(R/2<=p<R)N_p(t_q)=pi(t_q)-H.
~~~
The pi(t_q) terms cancel EXACTLY, leaving
~~~text
T_q(z)=a(z)*x_q+b(z)-r_q.                       (HM.3)
~~~
This individual-row version exposes information not supplied by AP's scalar total. Because z<=h, delta(z)>=delta(h), so
0<delta(y)<=a(z)<=delta(z)<=1/2.

Let xbar=(sum_Q x_q)/m, rbar=(sum_Q r_q)/m and
V_x=sum_Q(x_q-xbar)^2, V_r=sum_Q(r_q-rbar)^2. Then
~~~text
T_q(z)-E(z)/m=a(z)*(x_q-xbar)-(r_q-rbar).        (HM.4)
~~~
For any two admissible z,z':
~~~text
[T_q(z)-E(z)/m]-[T_q(z')-E(z')/m]
 =[a(z)-a(z')]*(x_q-xbar).                     (HM.5)
~~~
Thus the centered family is an affine line in the ORIGINAL q-indexed vector space. Changing the common prefix cannot independently adjust the fibre signs or the directions orthogonal to the reciprocal-prime vector.

Since 0<=r_q<1,
~~~text
V_r=sum_Q r_q^2-m*rbar^2
   <=m*rbar*(1-rbar)<=m/4.
~~~
Consequently the exact source-specific uniform restriction is
~~~text
sum_Q [T_q-E/m-a(z)*(x_q-xbar)]^2 = V_r <= m/4. (HM.6)
~~~
For EVERY real coefficient family v_q with sum v_q=0 and sum v_q*x_q=0:
~~~text
|sum_Q v_q*T_q|^2 <= (m/4)*sum_Q v_q^2.         (HM.7)
~~~
Proof: (HM.4) identifies the response as -sum v_q*(r_q-rbar); use finite Cauchy-Schwarz. These constants are fixed before R,z,v. This pays only the stated transverse response, not the constant or reciprocal mode.

For the full diagonal D_T=sum_Q T_q^2, the reverse triangle inequality gives
~~~text
|sqrt(D_T-E^2/m)-a(z)*sqrt(V_x)|<=sqrt(m)/2.    (HM.8)
~~~
Equivalently, retain the explicit mixed term:
~~~text
D_T-E^2/m
 =a(z)^2*V_x-2*a(z)*sum_Q(x_q-xbar)*(r_q-rbar)+V_r.
~~~
No off-diagonal term is omitted. The map aggregates original owner cells; it is not invertible to every physical label and is not claimed to be. It is exact for the displayed rows and their complete aggregate square.

#### HM2. Finite Sign Localization At The Genuine Harmonic Mean

Assume additionally the directly checkable finite balance |E(z)|<=m/2. From (HM.4),
~~~text
|T_q(z)-a(z)*(x_q-xbar)|<=3/2.                  (HM.9)
~~~
Set q_h=X/xbar=m/(sum_Q 1/q), the ACTUAL harmonic mean, and eps_x=3/(2*a(z)). If xbar>eps_x, every admitted prime outside
~~~text
I_R=[X/(xbar+eps_x), X/(xbar-eps_x)]             (HM.10)
~~~
has forced sign: T_q>0 below this interval and T_q<0 above it. The interval width is exactly
~~~text
3*X/[a(z)*(xbar^2-9/(4*a(z)^2))].
~~~
This does not assert monotonicity inside the interval, an exact sign switch at q_h, or any short-prime-gap theorem. Fractional rounding can reverse both of those stronger assertions, as HM5 shows.

#### HM3. Eventual Adaptive Profile And Complete Covariance

Credit and premise check: AP2 proves a finite crossing residual <=m/2 using the genuine jump m-V*w_p<=m, with V=sum_Q x_q. AP3 proves an eventual bracket at floor(R/16), floor(R/4), then chooses one intact prefix. Its source-dependent choice is not a free assumed bound. This execution checked that argument against (HM.3): the total is a(z)V+m*b(z)-sum r_q; ordinary PNT/Mertens yield the two opposite eventual bracket signs. The estimate and bracket remain AP's discovery, not a new HM theorem. No explicit eventual R_0 is asserted.

Let z_R be that choice for all sufficiently large R, L=log R, c=exp(-gamma), ell=log 2. Independent classical inputs used here are the ordinary [prime number theorem](https://dlmf.nist.gov/27.12#E5) and [Mertens' product limit](https://www.numdam.org/item/JTNB_2009__21_3_523_0/). Neither assumes RH. All ensuing profile and covariance conclusions are deductions on the present carrier, not claims quoted from those references.

PNT on the fixed interval [R,2R] implies
~~~text
m~R/L, xbar/R -> ell,
V_x/(m*R^2) -> v:=integral_1^2(1/u-ell)^2 du
                  =1/2-ell^2>0.                       (HM.11)
~~~
To justify the weighted limits, (L/R)*#{q in Q:q/R<=u}->u-1 uniformly on [1,2]; partial summation then applies to 1/u and 1/u^2. Strict positivity follows because 1/u is not constant, not from a floating comparison.

Uniform Mertens on the fixed proportional z bracket gives delta(z_R)*L->c. Also W=O(L^-2), by prime partial summation of delta(p-1)/p over [R/2,R). Therefore a(z_R)*L->c. Equations (HM.4) and |E|/m<=1/2 now give the UNIFORM individual profile
~~~text
max_(q in Q) |(L/R)*T_q(z_R)-c*(R/q-ell)| -> 0. (HM.12)
~~~
Uniformity is valid for the source-dependent z_R because the product estimate is uniform over the entire fixed bracket.

The exact harmonic center satisfies q_h/R->1/ell. The width in (HM.10) is asymptotic to 3*L/(c*ell^2). Hence all exceptions to the sign rule lie in an O(log R)-wide interval about the ACTUAL harmonic center. Its prime population is at most its length plus one by integer counting. We do NOT replace q_h by R/ell at O(log R) accuracy; the leading center limit is much weaker.

Integrating the bounded uniform profile against the genuine PNT counting measures gives
~~~text
D_T ~ c^2*v*R^3/L^3,
sum_Q |T_q| ~ 2*c*(ell-1-log ell)*R^2/L^2.      (HM.13)
~~~
The positive constant in the second formula follows from log ell<ell-1 for 0<ell<1. These are signed-source norm asymptotics, not an inference from the finite scan.

Let C_T=sum_(q<q', q,q' in Q)T_q*T_q'. Retain EVERY unordered pair:
~~~text
E^2=D_T+2*C_T,
E^2<=m^2/4=o(R^3/L^3),
C_T ~ -(c^2*v/2)*R^3/L^3.                      (HM.14)
~~~
Thus negative COMPLETE cross-fibre interaction is forced inside this selected packet. It does not require every pair to be negative, and it is not the original compressed #915 NNS statistic.

There is also a useful uniform no-go independent of selecting a balanced cutoff. For ALL saturated z, a(z)>=delta(y). Apply (HM.8), delta(y)*L->c and (HM.11). There exists one R_1 such that
~~~text
forall R>=R_1, forall admissible z:
  sum_Q (T_q(z)-E(z)/m)^2 >= (c^2*v/2)*R^3/L^3. (HM.15)
~~~
The threshold precedes z. In particular, a uniform O(R^2 log(R)^2) bound on this diagonal, or uniform boundedness of every adaptive fibre, is false. This refutes auxiliary diagonal/pointwise strengthenings, NOT the affordable scalar sum.

#### HM4. A Fixed Cross-Mask Cut Breaks The Adaptive Payment

For any FIXED real 1<lambda<2, keep the disjoint original prime submask Q_lambda={q in Q:q<lambda R}. Equation (HM.12) and PNT give
~~~text
sum_(q in Q_lambda)T_q(z_R)
 ~ c*[log lambda-(lambda-1)*ell]*R^2/L^2.        (HM.16)
~~~
The bracket is strictly positive by strict concavity of log, which lies above its endpoint chord between 1 and 2. The complementary q total has its NEGATIVE leading coefficient because E=O(R/L).

For lambda=3/2 the coefficient is c*log(3/(2*sqrt(2)))>0. Consequently, for EVERY fixed C, both separate absolute submask totals exceed C R log R eventually, while their combined total is already paid by AP. Their doubled cross product has leading coefficient -2*c^2*[log lambda-(lambda-1)ell]^2*R^4/L^4; it cancels the leading squares, not an omitted error.

This is the new packet-to-packet compensation statement: the two large signed q populations compensate as complete groups with explicit leading coefficients. The affordable combined error is credited to AP. HM provides no additional improvement in that error.

#### Complete Return To The Original Source

For the unmasked original owner B_R(p)=N_p(X)-X*w_p, the greatest-prime partition of nonunit divisors gives F_R=sum_(p<R)B_R(p); the unit divisor contributes fract(X)=0. Put b_Q(p)=sum_Q N_p(t_q)-V*w_p. The complement B_R(p)-b_Q(p) counts the actual outside-Q sites with reference (X-V)*w_p. This is not a newly fitted reference: for R>=8, all Q primes are odd and sum_Q 1/q<1, so 0<V<X.

Retain CF's full Q-mask total S_Q=delta(y)*V-m-sum_Q r_q. Define J_R=S_Q-E_R as the unselected owners in those same fibres and C_Q=sum_(p<R)[B_R(p)-b_Q(p)]-D_R=F_R-S_Q-D_R as the complete outside-mask/reference source. Then
~~~text
Z_R=E_R+J_R+C_Q,
Z_R^2=E_R^2+J_R^2+C_Q^2
       +2*E_R*J_R+2*E_R*C_Q+2*J_R*C_Q,
E_R^2=sum_Q T_q^2+2*sum_(q<q')T_q*T_q'.         (RETURN)
~~~
If E is divided at lambda R, keep both new squares, their mixed product and BOTH orientations of their products with J_R and C_Q. No occurrence is reused within the root. No allocation across different roots is claimed.

AP already pays E_R. HM now explains its internal cancellation but does not pay J_R+C_Q. The equivalence
J_R+C_Q=O(R log R) iff Z_R=O(R log R)
remains TARGET_EQUIVALENT. It is not an independent hypothesis licensed by (HM.6), (HM.14) or a finite test.

### E. Quantitative Consequence

The independent all-scale contribution is (HM.6)-(HM.8) on the exact selected carrier, with fixed constants m/4 and sqrt(m)/2. The finite sign interval (HM.10) is explicit and requires only its stated finite balance and denominator conditions. The eventual norm/covariance and localization no-gos are paper theorems using unconditional classical inputs and the separately credited AP selection.

This changes which local proof steps are plausible. A later consumer may use the transverse response bound if its coefficients satisfy BOTH exact orthogonality conditions. It cannot discard the constant or reciprocal mode, replace a complete squared sum by its diagonal, or localize the paid packet to a fixed q-submask at RH scale.

No changed exponent or constant for Z_R is proved. The strongest existing analytic middle-band improvement remains a different source result; HM does not supply its missing mixed/reference return.

### F. Falsification And Circularity Review

The exact finite balanced-packet strengthening
~~~text
|sum_Q T_q(z)|<=m/2  ==>  forall q in Q, |T_q(z)|<=1/2
~~~
is FALSE first at R=9 in the stated R>=8 saturated domain. With z=3:
~~~text
Q={11,13,17},
(T_11,T_13,T_17)=(30/77,23/91,-75/119),
E=206/17017,
D_T=177481126/289578289,
C_T=-36495/119119.
~~~
The full equality E^2=D_T+2*C_T was checked exactly. This is a balanced-prefix witness, not falsely labeled the eventual proportional-bracket selection.

For the actual finite first-crossing rule, the first crossing root is R=12, chosen z=4:
~~~text
Q={13,17,19,23},
T=(107/105,-184/1785,-919/1995,-1234/2415),
E=-14472/260015.
~~~
Thus the rule itself does not force |T_q|<=1/2 either.

Monotone decrease in q is FALSE first at R=10, z=4:
T_17=-293/595 < T_19=-13/665.
Both have floor(99/q)=5. In general on one constant-quotient cell,
T_q=t+b-(1-a)*X/q increases with q because 0<a<=1/2. The weak reciprocal profile survives; exact monotonicity does not.

The sign rule with NO uncertainty interval, sign(T_q)=sign(q_h-q), fails first at R=11, z=4: q_h=46189/3225<17 but T_17=3/119>0. This was a disclosed proof-led boundary test, not an assumed exact sign theorem.

Registered computations, all Python integers and Fraction:
- 124 roots: all R=8..128 plus held-outs 257,549,1024.
- 3,139 admissible cutoffs and 53,663 individual physical-row versus saturated-formula identities.
- 3,138 exact transverse-response checks and 3,015 cutoff-affine-line checks.
- 68 cutoffs satisfy the finite balance test; every (HM.9) sign implication passed.
- First-crossing roots in the registered discovery range: 12,13,15,27, retaining their actual chosen prefixes.
- Independent trial-prime/full-divisor reconstruction at R=2,3,8..16, including full original centered scalar and all E/J/C quadratic terms.
- Syntax validation passed; every arithmetic execution completed successfully.

Held-out roots tested three admissible cutoffs each, not all cutoffs. All nine tested totals were positive; no adaptive crossing or asymptotic onset is claimed there. The established AP eventual bracket is NOT numerically verified by this run. The paper limits are proved separately.

Boundary controls: empty R=2 wheel; q=R prime included; squareful a retained; R=12's pq=X=143; R=14's d=X=195 with mu(d)=-1. At R=8, physical fraction 3/5 plus virtual correction -6/5 equals complete -3/5. The arbitrary reference 355/113 checks the complete source without numerically evaluating li.

There were no failed arithmetic assertions. Output was subsequently shortened to avoid printing huge held-out rationals; crossing vectors and the new transverse checks were added, then the final program was rerun. These reporting/proof-led additions did not change any registered prediction, root range or source coefficient.

Scoped main searches for finiteWheel/variance and harmonic/cofactor found related other-carrier infrastructure, not a matching HM theorem in returned excerpts. The retrieved November 9 reports contain no harmonic-mean/reciprocal-profile claim matching HM. This is not an exhaustive literature novelty claim. The finite variance bound and first-crossing method themselves are standard; the source-specific restriction and no-go consequences are the reported contribution.

### G. Conceptual Interpretation

Saturation below the historical root removes the apparent independent freedom of the fibre signs. All selected physical cofactor counts collapse to t_q plus the SAME prime-count offset; the exact reference leaves a common coefficient times 1/q, and only one bounded fractional error per fibre.

The adaptive prefix therefore pays a coherent signed population, not a collection of small owners. Large positive and negative populations across the q mask are structurally necessary. The moving prefix cannot adjust the transverse pattern at all; it changes only the constant and reciprocal directions. This is an explicit arithmetic dependence, not statistical independence or an empirical zero-covariance claim.

The new coordinate is useful only at its typed scope. It does not retain or bound every label in the outside-Q source, and it cannot be used as a replacement for the full original zero-target statistic.

### H. Competing Mechanisms

| Mechanism | Evidence, missing step and smallest decisive test | Disposition |
| --- | --- | --- |
| Pointwise or diagonal payment of the adaptive packet | HM5 refutes small pointwise fibres; (HM.15) proves an eventual diagonal obstruction. No extra unproved premise needed for the rejection. | ABANDON these precise strengthenings. |
| Common-prefix reciprocal-profile compensation | (HM.6)-(HM.16) constrain every selected fibre and its complete cross interaction. Its scalar endpoint was already paid by AP; no complement theorem follows. | RETAIN as a proper-source structural tool, not a new global route. |
| Independent signed transfer to the outside-mask source | Exact RETURN remains available; a genuine map must preserve reference, once-only incidence and all mixed terms. No such sufficient map or inequality was obtained here. | CONTINUE DISCOVERY only after defining a new actual source operation. |
| Spectral and matched-product routes | ZD, RF and NC retain their stated different carriers and unpaid complements. HM supplies no automatic bridge. | Preserve current Coordinator assessment; do not redirect the campaign. |

### I. Specialist Handoffs

**Coordinator:** add (HM.6)'s transverse restriction and (HM.16)'s localization obstruction to AP's consumer record. The strongest new concept is the one-dimensional common-cutoff family on actual q fibres. The mechanism is clearer, not closer to RH by an improved bound. Avoid assigning another fixed-q-submask RH norm: it is now disproved for this selected packet.

**Referee:** independently check individual saturation, the distinction between least physical owner and greatest divisor-packet prime, the inherited mu(e), m/4 variance bound, eventual UNIFORMITY over source-dependent z_R, and the actual-harmonic-center qualifier. Reproduce R=9,10,11,12. Review (HM.13)-(HM.16) without silently upgrading AP's finite onset or identifying the covariance with #915.

**Analytic:** for any proposed weighted response on these rows, test sum v_q=0 and sum v_q/q=0 BEFORE invoking (HM.7). It pays those transverse directions only. A usable original-middle-band bridge still needs its real coefficient map and both mixed/reference terms; none is supplied here.

**Wheel:** (HM.5) shows all common saturated cutoffs have the same transverse component. A promising new incidence operation must introduce genuinely different arithmetic information, such as a proved once-only one-factor transfer with its Euler defect, not another common-prefix regrouping. No blanket impossibility of such a transfer is claimed.

**Census:** the registered local strengthenings are decisively refuted; no larger supporting scan is requested. A useful next experiment requires a concrete proposed cross-mask map. Check its physical admission and reference defect on held-out roots, not just its favorable signs.

**Lean Verification:** after independent acceptance and only if a real consumer uses it, (HM.3)-(HM.8) are a compact possible source/finite-vector lemma family. Do not formalize all paper asymptotics as conditional wrappers or duplicate #1127. No conjectural full discrepancy estimate is submitted for implementation.

These are asynchronous report handoffs. No agent was launched, assigned a new schedule, or promised background work.

### J. First Independently Missing Lemma

**No smaller sufficient lemma for the complete RH target was obtained.** In this investigation the selected packet was already paid; HM explains why certain proposed local norm replacements are false. The new transverse estimate is independently proved, but there is no source-faithful consumer demonstrating that the unpaid original complement lies in its transverse subspace.

The first missing BRIDGE for using (HM.7) is a source construction: identify a genuine outside-mask signed functional and an exact representation sum_Q v_q*T_q with BOTH sum v_q=0 and sum v_q/q=0, retaining original references and multiplicities. Any remainder and coefficient norm would need independent bounds at the actual consumer's scale. No such functional/representation or bounds have been obtained, so this is a research prerequisite, NOT a formulated sufficient theorem or a proved reduction. There is no justified reason to demand this particular bridge from all other routes.

In particular, simply naming G_R=J_R+C_Q and assuming |G_R|<=C R log R is TARGET_EQUIVALENT, not that bridge. The next research step should propose an actual cross-mask arithmetic operation, calculate its defect, then test it; repeating common-prefix tuning cannot add a transverse degree of freedom.

### K. Next-Run Resume Capsule, Evidence And Publication

Scheduled trigger=2026-11-10 00:09:00 EST; RUN_ID_UNAVAILABLE.
Intake reports HEAD=12a51809df94dcdb29c8969c0a9c79ebcd503ac3.
Early checkpoint commit=5fec64bb0b3bc664cd4f42216cff7d5d012b01aa,
blob=f05a123c2b8620c823d2c7099fb54a6b9e2917d6; exact commit/file readback succeeded BEFORE tests.

TODAY=PENDING for upstream roles at refresh; YESTERDAY=CARRY_FORWARD. The exact November 9 role blobs are preserved in the checkpoint. Consumed relevant latest claims: Coordinator CD1-CD4; Owner CF1-CF5 and CT; Referee AP1-AP6; Analytic ZD proper-band bound; Wheel RF; Census NC; Lean CF2 strengthening. ZD/RF/NC were not independently reviewed here. External inbox remains 038018145c0fddb2f6306c0712373adf9cd1ea52 with no newer entry; EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain their source/anchor/normalization safeguards, not obsolete routing.

Actual GitHub evidence:
- #1122 merged source unchanged. Historical targeted job 128980092032 was read: it emitted the complete-wheel module under Lean 4.34.1 and printed both standard-axiom lists. Checkout was the synthetic merge containing c53e9cf, not falsely described as a literal current-main build.
- #1124 is merged, original admission declarations were read; its previous verified report evidence remains proper-component evidence, not a new full-shell theorem.
- #1125 is merged but the literal proof head 538aa743a3e0de86b5ec44c9b4f159df3f5bd050 still has zero check-runs and 12 failed workflow records in a fresh all-event query. Preserve FORMAL_VERIFICATION_NOT_VERIFIED; this is not evidence of a mathematical counterexample or a compiler diagnostic.
- #1126 is merged as current main. Its tested head e8969ad76d4c5694273cefc934316fc528c56648 has 17 successful check-runs. The inspected declarations explicitly retain upgrade and hzero. CONDITIONAL consumers do not establish their premises.
- #1127 remains the only open PR, non-draft, at 866b3d2121309cdd854f9d64e2a6adbbc708ef9b. Thirteen successful checks were observed. The literal-head job 129590019152 actually compiled both modules and passed source-dependency closure=828. Acceptance source has six executed standard-axiom guards. The new density 3*z*delta(z)^2>=1 and fibre positivity for R>=47 are PROVED_IN_LEAN at that UNMERGED head, not on main. Source f83a3daefc2b9d603014af912ec82b4a7f52cfac; acceptance 94eecdbf8cea32bf80e7e0939e40c951bc72febd. HM does not need this sharper threshold.

Final executed program SHA-256:
ccfe7b914a42e0ff854769d05d299bc1bdc63b37ad147d74e1d06f2a21f16363.
The complete program and compact exact output follow. Python 3.12.13; no optional numerical packages, no floating sign decisions, no local Lean. Independent trial-factor/source reconstruction was by this SAME author, not external review. No source, central policy, other role report, proof branch/PR, workflow, schedule, permission or main was changed.

Resume from HM1/HM3/HM4, especially (HM.6)/(HM.15)/(HM.16). Do not repeat the pointwise/monotonicity scans, ignore the finite harmonic uncertainty interval, treat q_h=R/log2 with an unproved sharp error, or call C_T the original NNS covariance. Best next step: a concrete reference-preserving cross-mask operation that introduces information outside the already controlled reciprocal profile. NEW_GLOBAL_ENDPOINT_GAIN=NONE; RH remains OPEN.

Research is complete at the stated paper/finite scope. Publication status is PENDING until the immutable commit readback recorded below.

### Prepublication Freshness - 2026-11-10 00:24 EST

At 05:24:23 UTC the main SHA was unchanged. Today's directory still contained only this Owner checkpoint, so upstream TODAY=PENDING remains literal, not an assumption about missed runs. #1127 was still the sole open PR at the same non-draft head. No changed source or new upstream publication alters the derivation. The original checkpoint is retained verbatim below the daily heading; the completed synthesis appends to it.


### Reproducibility Appendix - Exact Executed Program

~~~python
"""Exact registered checks for 20261110-owner-1/HM; no floating decisions."""

from fractions import Fraction as F
from itertools import combinations
from math import isqrt
import json


def sieve(n):
    least = list(range(n + 1))
    least[1] = 1
    for p in range(2, isqrt(n) + 1):
        if least[p] == p:
            for k in range(p * p, n + 1, p):
                if least[k] == k:
                    least[k] = p
    return least, [p for p in range(2, n + 1) if least[p] == p]


LP, PRIMES = sieve(2 * 1024)
DENS = [F(1)] * (2 * 1024 + 1)
PI = [0] * len(DENS)
for n in range(2, len(DENS)):
    prime = LP[n] == n
    DENS[n] = DENS[n - 1] * (F(n - 1, n) if prime else 1)
    PI[n] = PI[n - 1] + int(prime)


def divisors_with_sign(primes):
    out = [(1, 1)]
    for p in primes:
        out += [(d * p, -mu) for d, mu in out]
    return out


def frac(x):
    return x - x.numerator // x.denominator


def trial_prime(n):
    return n >= 2 and all(n % a for a in range(2, isqrt(n) + 1))


stats = {"roots": 0, "cutoffs": 0, "fibre_identities": 0,
         "balanced_cutoffs": 0, "transverse_checks": 0,
         "cutoff_rank_checks": 0, "crossing_roots": [], "held_out": [],
         "small_cube_roots": [], "first_pointwise_failure": None,
         "first_monotonicity_failure": None,
         "first_balanced_monotonicity_failure": None,
         "first_exact_harmonic_sign_failure": None}


def record(R, z, Q, vec, E, A, xbar, D, pair):
    return {"R": R, "z": z, "Q": Q, "T": list(map(str, vec)),
            "E": str(E), "A": str(A), "harmonic_centre": str(F(R * R - 1) / xbar),
            "diagonal": str(D), "unordered_pairs": str(pair)}


def check_root(R, held=False):
    X = R * R - 1
    Q = [q for q in PRIMES if R <= q < 2 * R]
    m = len(Q)
    assert m > 0
    xs = [F(X, q) for q in Q]
    rs = list(map(frac, xs))
    xbar, rbar = sum(xs) / m, sum(rs) / m
    vx = sum((x - xbar) ** 2 for x in xs)
    vr = sum((r - rbar) ** 2 for r in rs)
    assert vr <= F(m, 4)
    h = (R - 1) // 2
    W = DENS[h] - DENS[R - 1]
    zmin = isqrt(R) + int(isqrt(R) ** 2 < R)
    zmax = (R - 1) // 2
    zs = list(range(max(2, zmin), zmax + 1))
    if held:
        zs = sorted(set([zs[0], zs[len(zs) // 2], zs[-1]]))
    history = []
    previous_vec = None
    for z in zs:
        A = DENS[z] - W
        B = PI[z] - PI[h] - 1
        assert 0 < A < 1
        vec = []
        for q, x, r in zip(Q, xs, rs):
            t = X // q
            # Direct least-owner counts, including squareful cofactors.
            count = sum(LP[a] <= z or 2 * LP[a] >= R for a in range(2, t + 1))
            direct = count - x * (1 - DENS[z] + W)
            saturated = A * x + B - r
            assert direct == saturated
            vec.append(direct)
            stats["fibre_identities"] += 1
        E = sum(vec)
        assert E == A * sum(xs) + m * B - sum(rs)
        D = sum(t * t for t in vec)
        pair = (E * E - D) / 2
        if R <= 32:
            assert pair == sum(a * b for a, b in combinations(vec, 2))
        err = [t - E / m - A * (x - xbar) for t, x in zip(vec, xs)]
        assert err == [-(r - rbar) for r in rs]
        assert sum(e * e for e in err) == vr
        vt = sum((t - E / m) ** 2 for t in vec)
        cross = sum((x - xbar) * (r - rbar) for x, r in zip(xs, rs))
        assert vt == A * A * vx - 2 * A * cross + vr
        assert cross * cross <= vx * vr
        assert vt <= 2 * A * A * vx + F(m, 2)
        assert D == vt + E * E / m
        if m >= 3:
            weights = [xs[1] - xs[2], xs[2] - xs[0], xs[0] - xs[1]]
            assert sum(weights) == 0
            assert sum(w * x for w, x in zip(weights, xs)) == 0
            response = sum(w * t for w, t in zip(weights, vec))
            assert response == -sum(w * r for w, r in zip(weights, rs))
            assert response * response <= F(m, 4) * sum(w * w for w in weights)
            stats["transverse_checks"] += 1
        if previous_vec is not None:
            old, old_E, old_A = previous_vec
            for t, old_t, x in zip(vec, old, xs):
                assert t - E / m - old_t + old_E / m == (A - old_A) * (x - xbar)
            stats["cutoff_rank_checks"] += 1
        previous_vec = vec, E, A
        balanced = abs(E) <= F(m, 2)
        item = record(R, z, Q, vec, E, A, xbar, D, pair)
        if balanced:
            stats["balanced_cutoffs"] += 1
            for t, x in zip(vec, xs):
                assert abs(t - A * (x - xbar)) <= F(3, 2)
                if A * (x - xbar) > F(3, 2):
                    assert t > 0
                if A * (x - xbar) < -F(3, 2):
                    assert t < 0
            if max(map(abs, vec)) > F(1, 2) and stats["first_pointwise_failure"] is None:
                stats["first_pointwise_failure"] = item
            if any(t * (x - xbar) < 0 for t, x in zip(vec, xs)) and stats["first_exact_harmonic_sign_failure"] is None:
                stats["first_exact_harmonic_sign_failure"] = item
        increases = [(Q[j], Q[j + 1]) for j in range(m - 1) if vec[j] < vec[j + 1]]
        if increases and stats["first_monotonicity_failure"] is None:
            stats["first_monotonicity_failure"] = dict(item, increases=increases)
        if increases and balanced and stats["first_balanced_monotonicity_failure"] is None:
            stats["first_balanced_monotonicity_failure"] = dict(item, increases=increases)
        history.append((z, E, item))
        stats["cutoffs"] += 1
    if not held:
        for (_, prev, left), (_, cur, right) in zip(history, history[1:]):
            if prev < 0 <= cur:
                chosen = left if abs(prev) <= abs(cur) else right
                assert abs(F(chosen["E"])) <= F(m, 2)
                stats["crossing_roots"].append({"R": R, "chosen_z": chosen["z"], "E": chosen["E"],
                                                "Q": chosen["Q"], "T": chosen["T"]})
                break
    if held:
        stats["held_out"].append({"R": R, "tested_z": zs,
                                  "total_signs": [(v > 0) - (v < 0) for _, v, _ in history],
                                  "total_integer_floors": [v.numerator // v.denominator for _, v, _ in history]})
    stats["roots"] += 1


for root in range(8, 129):
    check_root(root)
for root in [257, 549, 1024]:
    check_root(root, held=True)


for R in [2, 3] + list(range(8, 17)):
    X = R * R - 1
    small = [p for p in range(2, R) if trial_prime(p)]
    Q = [q for q in range(R, 2 * R) if trial_prime(q)]
    ds = divisors_with_sign(small)
    density = sum(F(mu, d) for d, mu in ds)
    whole = sum(mu * frac(F(X, d)) for d, mu in ds)
    physical = sum(mu * frac(F(X, d)) for d, mu in ds if d <= X)
    virtual = sum(F(X * mu, d) for d, mu in ds if d > X)
    assert whole == physical + virtual
    prime_count = sum(trial_prime(n) for n in range(2, X + 1))
    reference = F(355, 113)
    deterministic = X * density + len(small) - 1 - reference
    Z = whole - deterministic
    assert Z == reference - prime_count
    S = sum(sum(mu * frac(F(X, q * d)) for d, mu in ds if d != 1) for q in Q)
    assert S == sum(density * F(X, q) - 1 - frac(F(X, q)) for q in Q)
    if R >= 8:
        zmin = isqrt(R) + int(isqrt(R) ** 2 < R)
        h = (R - 1) // 2
        for z in range(zmin, h + 1):
            selected = [p for p in small if p <= z or 2 * p >= R]
            vec = []
            for q in Q:
                original = -sum(mu * frac(F(X, p * q * d)) for p in selected
                                for d, mu in divisors_with_sign([a for a in small if a < p]))
                dz = sum(F(mu, d) for d, mu in divisors_with_sign([p for p in small if p <= z]))
                dh = sum(F(mu, d) for d, mu in divisors_with_sign([p for p in small if p <= h]))
                A = dz - dh + density
                B = sum(p <= z for p in small) - sum(p <= h for p in small) - 1
                assert original == A * F(X, q) + B - frac(F(X, q))
                vec.append(original)
            E = sum(vec)
            J, C = S - E, Z - S
            assert Z == E + J + C
            assert Z * Z == E * E + J * J + C * C + 2 * E * J + 2 * E * C + 2 * J * C
    if R == 8:
        assert physical == F(3, 5) and virtual == F(-6, 5) and whole == F(-3, 5)
    if R == 14:
        assert (195, -1) in ds
    stats["small_cube_roots"].append(R)

print(json.dumps(stats, indent=2))
~~~

### Recorded Exact Output

~~~json
{
  "roots": 124,
  "cutoffs": 3139,
  "fibre_identities": 53663,
  "balanced_cutoffs": 68,
  "transverse_checks": 3138,
  "cutoff_rank_checks": 3015,
  "crossing_roots": [
    {
      "R": 12,
      "chosen_z": 4,
      "E": "-14472/260015",
      "Q": [
        13,
        17,
        19,
        23
      ],
      "T": [
        "107/105",
        "-184/1785",
        "-919/1995",
        "-1234/2415"
      ]
    },
    {
      "R": 13,
      "chosen_z": 4,
      "E": "-1387388/5311735",
      "Q": [
        13,
        17,
        19,
        23
      ],
      "T": [
        "446/715",
        "-159/935",
        "-434/1045",
        "-379/1265"
      ]
    },
    {
      "R": 15,
      "chosen_z": 6,
      "E": "-311742688/462120945",
      "Q": [
        17,
        19,
        23,
        29
      ],
      "T": [
        "31099/36465",
        "-3221/40755",
        "-24671/49335",
        "-58991/62205"
      ]
    },
    {
      "R": 27,
      "chosen_z": 6,
      "E": "-3162049293092/4805853896085",
      "Q": [
        29,
        31,
        37,
        41,
        43,
        47,
        53
      ],
      "T": [
        "66914593/35547765",
        "42398893/37999335",
        "19519/1225785",
        "-26245067/50257185",
        "-47083412/52708755",
        "-45857627/57611895",
        "-1790359/1225785"
      ]
    }
  ],
  "held_out": [
    {
      "R": 257,
      "tested_z": [
        17,
        73,
        128
      ],
      "total_signs": [
        1,
        1,
        1
      ],
      "total_integer_floors": [
        195,
        376,
        712
      ]
    },
    {
      "R": 549,
      "tested_z": [
        24,
        149,
        274
      ],
      "total_signs": [
        1,
        1,
        1
      ],
      "total_integer_floors": [
        667,
        1147,
        2683
      ]
    },
    {
      "R": 1024,
      "tested_z": [
        32,
        272,
        511
      ],
      "total_signs": [
        1,
        1,
        1
      ],
      "total_integer_floors": [
        2142,
        3292,
        7696
      ]
    }
  ],
  "small_cube_roots": [
    2,
    3,
    8,
    9,
    10,
    11,
    12,
    13,
    14,
    15,
    16
  ],
  "first_pointwise_failure": {
    "R": 9,
    "z": 3,
    "Q": [
      11,
      13,
      17
    ],
    "T": [
      "30/77",
      "23/91",
      "-75/119"
    ],
    "E": "206/17017",
    "A": "8/35",
    "harmonic_centre": "7293/551",
    "diagonal": "177481126/289578289",
    "unordered_pairs": "-36495/119119"
  },
  "first_monotonicity_failure": {
    "R": 10,
    "z": 4,
    "Q": [
      11,
      13,
      17,
      19
    ],
    "T": [
      "37/35",
      "57/455",
      "-293/595",
      "-13/665"
    ],
    "E": "19706/29393",
    "A": "8/35",
    "harmonic_centre": "46189/3225",
    "diagonal": "5944488492/4319742245",
    "unordered_pairs": "-68092/146965",
    "increases": [
      [
        17,
        19
      ]
    ]
  },
  "first_balanced_monotonicity_failure": {
    "R": 10,
    "z": 4,
    "Q": [
      11,
      13,
      17,
      19
    ],
    "T": [
      "37/35",
      "57/455",
      "-293/595",
      "-13/665"
    ],
    "E": "19706/29393",
    "A": "8/35",
    "harmonic_centre": "46189/3225",
    "diagonal": "5944488492/4319742245",
    "unordered_pairs": "-68092/146965",
    "increases": [
      [
        17,
        19
      ]
    ]
  },
  "first_exact_harmonic_sign_failure": {
    "R": 11,
    "z": 4,
    "Q": [
      11,
      13,
      17,
      19
    ],
    "T": [
      "24/77",
      "45/91",
      "3/119",
      "-60/133"
    ],
    "E": "122952/323323",
    "A": "31/105",
    "harmonic_centre": "46189/3225",
    "diagonal": "57060593802/104537762329",
    "unordered_pairs": "-64863/323323"
  }
}
~~~

### Verified Publication Receipt - 2026-11-10 00:25:50 EST

PUBLISHED / COMPLETE at PAPER_PROOF + FINITE_COMPUTATION scope, not a Lean theorem or an RH proof.
Substantive commit: 09ad4d12a4cbe2df0155ca1bdd63a034562144aa.
Report blob: 4a91735b7e2bebd559959a0e7b8359b33b755beb.
Immutable GitHub re-fetch matched all 46,296 characters exactly. Commit inspection confirmed only research/agent_reports/2026-11-10/10-owner-payment.md changed, with 822 additions and zero deletions; the early checkpoint was preserved.
The final program passed all registered assertions and syntax validation. New HM1-HM4 paper claims remain SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED; HM5 is finite evidence. No new full discrepancy estimate, finite A/C or RH result was claimed.
This receipt records an executed verification, not a promise of later work.


## Scheduled Continuation Checkpoint - 20261110-owner-2/BR
### A. Most Important Mathematical Development
IN_PROGRESS / PARTIAL. The new task is an original-weight recovery test: does the already-proved complete reciprocal-band theorem (#1115) control the prime/floor-Li weighted Buchstab innovation, or does its transport leave a full-size unmatched source? No new theorem or quantitative gain is claimed at this checkpoint. Earlier HM, CF, CT and FW evidence remains unchanged.

### B. Current Authoritative Objective
Scheduled trigger 2026-11-10 08:09:05 EST; platform run ID unavailable. main=655f897e274a8ba8a2fed80ecc1fc75a0d849174. cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1. Read current AGENTS (c9c89f01b90b526de9f3e8ea92478e36504711b6), proof contract (95566e37c8eaeb99ee680660df4f9d2e06ea5038), and governing directive (e922d4ba9362a1ae196af8f6de88f7417f92087c). New authority supersedes only task selection; all previous mathematical qualifications remain. Exact canonical actual-prime VF bound and complete wheel Z_R=li(R^2-1)-pi(R^2-1) remain OPEN. Certified #1119 baseline intake is b=7/8-7/(64*N_pack), every positive loss; source/dependency/CI receipt is being checked, not assumed from a green label.

### C. Registered Structural Investigation
Follow Coordinator 20261110-coordinator-0710-EST M3: retain X=R^2-1, y=R-1, post-root prime q, genuine mu(a), M(floor(X/q)), the actual floor-Li integer event lambda(q), and epsilon(q)=1_Prime(q)-lambda(q). Compare exact coefficient pushforward to complete 2ab bands, keeping long cofactor tails, squareful terms, root-prime q=R, virtual Euler compensation and every quadratic mixed term. No local cutoff optimization is planned.

### D-K. Work In Progress And Continuity
Today's seven role reports and yesterday's reports have been retrieved; no upstream report is absent. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD, with relevant original derivations being read. Current open/draft PR list is empty; #1127/#1128/#1129 are merged. HM's proper-packet cancellation, UC's unsaturated counterexamples, LC's fixed-rank obstruction and UB's all-cutoff obstruction must not be promoted to a complete-source estimate.
Planned falsification: compare literal event/cofactor expansions to direct genuine Mobius sums, preserve both cross orientations, seek the first failure of an unweighted or prime-only substitution, and distinguish an exact bridge from a paid recovery. Small exact roots first; held-outs 47,64,97,127,549,5561 only when the relevant source can be computed exactly and economically. Source-level uncertainty or a mismatch will be reported explicitly. No local Lean build, source/PR edit, other-agent launch or schedule change is authorized.


## Composite Event Admission And The True Completed Buchstab Source
### Final Research Synthesis - 20261110-owner-2/BR

### A. Most Important Mathematical Development

**The proposed direct recovery has an exact arithmetic obstruction: a floor-Li event is not a fresh prime, and lifting it as one can change its Mobius sign and duplicate a physical integer.** This is not just a warning about different notation. The necessary and sufficient admission condition, the complete correction, and genuine small counterexamples are given below.

For integers 2<=q<=X, the full cofactor family satisfies mu(aq)=-mu(a) for EVERY 1<=a<=floor(X/q) if and only if

```text
mu(q)=-1 and q*leastPrime(q)>X.                 (BR.1)
```

In particular, among post-root q with q^2>X and q^4<=X^3, this property holds EXACTLY for primes. Every composite in that whole range fails admission, not just a sampled exception. The prime condition in the existing family theorem therefore cannot be removed when transporting it to the actual floor-Li stream.

The literal physical lift of the prime-minus-floor-Li innovation has an explicit signed defect. It is nonzero already at R=3, and the complete defect has both signs at actual roots. The already-proved general Mobius renewal theorem DOES recover the unweighted prime discrepancy, but only after admitting every descendant and its divisor multiplicity. It does not bound the recovered discrepancy.

| Claim | Result and status |
| --- | --- |
| 20261110-owner-2/BR1 | Exact all-cofactor flip admission and the composite exclusion region. PAPER_PROOF / SELF_AUDIT. |
| BR2 | Full original-weight physical-lift defect and multiplicity formula; direct zero-defect/once-only extension REFUTED on genuine floor-Li events. PAPER_PROOF plus FINITE_COMPUTATION. |
| BR3 | Complete fixed-cutoff renewal bridge from the weighted innovation to the actual prime backlog. IDENTITY_ONLY, an application of an ALREADY-PROVED theorem, not a newly discovered renewal law. |
| BR4 | Compulsory within-event signed descendant cancellation and a linear absolute-value loss. PAPER_PROOF; proper coefficient row, not a global endpoint gain. |
| BR5 | Explicit signed-box rounding budget <=(sum mu(a)^2+abs(M(N)))/2. PAPER_PROOF; supporting refinement of an already-known O(R) rounding cost. |
| BR6 | Exact carrier, defect, completion and Gram tests, including independent small integral certificates. FINITE_COMPUTATION, not an all-scale estimate. |

New paper arguments are **INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. The refuted hypotheses were investigated in this run; they are not falsely attributed to a specialist who asserted them. **NO_NEW_GLOBAL_GAIN. NO_NEW_ACCEPTED_ROUTE.** The canonical VF bound, complete-wheel RH bound, finite A/C and RH remain OPEN.

### B. Current Authoritative Objective

Scheduled invocation: 2026-11-10 08:09:05 EST, America/New_York. Run label 20261110-owner-2/BR; platform run ID unavailable. This continues the same daily Owner report and preserves HM and all previous valid evidence.

Main source: **655f897e274a8ba8a2fed80ecc1fc75a0d849174**. Governing acknowledgement: **cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1**. The previous finite-wheel acknowledgement remains historical context; the merged November 10 cross-route directive now controls task selection.

The canonical statement is still: there exists ONE C>=0 such that for EVERY integer R>=2,

```text
abs(pi(R^2)-VF_can(R^2)) <= C R log R.
```

With X=R^2-1, y=R-1, P_y the product of primes <=y, and delta(y)=product_(p<=y)(1-1/p), the exact complete-wheel source is

```text
F_R=sum_(d|P_y)mu(d)fract(X/d),
D_R=X delta(y)+pi(y)-1-li(X),
Z_R=F_R-D_R=li(X)-pi(X).
```

All d>X remain until their X/d fractional contribution cancels its matching Euler term. d=X is retained. Moving the prime endpoint from R^2-1 to R^2 adds no prime for R>=2, but the Li endpoint and fixed normalization still require their own adapters. The canonical terminal theorem continues to take ClassicalVonKochRHCriterion explicitly; this execution does not construct that interface.

#### 1. BASELINE / DEPENDENCY RECEIPT

Read the current exact declaration `native_mertens_near_uniform_window_error_closed`, its source/count construction, native Mertens adapter, the actual `MertensGrowthAtMost` definition, and the hosted live-dependency/axiom audit. The applicable certified repository baseline is

```text
b_base=7/8-7/(64*N_pack), N_pack=nearUniformSlotCount,
forall eps>0, exists C_eps>=0, forall n>=1:
  abs(M(n)) <= C_eps*n^(b_base+eps).
```

There is NO asserted no-loss bound at b_base. Credit Coordinator CR1 for the numerical comparison: actual definitions give
N_pack=ceil_nat(max(1,1/(6*explicitFineLength)))+2 and
N_old=ceil_nat(max(1,1/(3*explicitFineLength)))+2.
Since explicitFineLength>0, N_pack<=N_old; hence 7/(64*N_pack)>1/(48*N_old). The counts are not identified. This rechecks the existing comparison, not a new exponent result.

The exact-head receipt for #1119 was re-fetched: head 77ee815846d6d534c866f0752aa33b84c385610a; run 42552018910, job 128949473700; completed/success. Its log prints the five theorem types and all five PASS dependency checks, with closure sizes 35358,35375,35736,35737,35753 and only propext, Classical.choice, Quot.sound. Source file blob f629db1b2b65d6ec042ac9432397d4b6316200c6 matches current main. A direct tree-blob comparison found no changed existing research/oai_434 or RHLean module below RHLean/ since that exact head; the root import file changed and later modules were added. This is source continuity, not a fresh main-head Lean execution. The audit traverses live OAI/RHLean/private proof values and separately collects terminal axioms transitively; it is not an assertion that this specialist independently reproved every external analytic argument.

The inspected chain is original moments and complete total-mass LOW plus anchored HIGH/principal -> native_fixed_total_mass_probe_bounds -> native_beta_le_total_mass_boundary -> window-saturated positive-error closure -> actual modulus-one Dirichlet/Hecke product -> native_zeta_rightmost_le_hecke_beta -> native_mertens_growth_at_hecke_beta -> the displayed bound. No desired arithmetic bound is an ordinary hypothesis of the final declaration. Imported analytic proofs remain part of the dependency receipt, not a newly independent proof by this run.

The log verifies Lean 4.34.1/compiler 5045d0056413266e57c625dcd7c365b10e377c52; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; unpatched PrimeNumberTheoremAnd c39a751132c88b6e8080b74c74023fd95b3d8be0; upstream openai/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a; anchored generator source pin 9cbfce5295343bcb411e6d2cb159b59995cd985b. Warning-fatal Lean checks appear in the actual hosted log. No local Lean was run.

#1115 has a verified successful dedicated run 42517562043 at head 7256681db5adfc907426deaef676244aeb4384dd. Its actual changed-file list contains TWOAB_RENEWAL_COMPLETE_BAND and its growth consumer, not PrimeCombReciprocalBandCancellation. The latter is a separate existing source used below. This corrects an imprecise attribution in the incoming assignment, without changing any theorem.

#1127 and #1128 are now merged, superseding earlier reports' unmerged status. Their exact-head dedicated runs 42743502306 and 42798625661 were fetched and are successful at 866b3d2121309cdd854f9d64e2a6adbbc708ef9b and d5b8003f6239611a457560b6fd16e29f16255e75, respectively. The current cofactor positivity source was read. These are proper-source facts, not endpoint improvements. Open/draft PR collection was empty at intake.

### C. Structural Hypothesis Investigated

Resume Coordinator 20261110-coordinator-0710-EST/M3, not the now-exhausted local-cutoff optimization. The proposed reuse has two possible meanings, which must be distinguished:

1. Transport the already-proved post-root prime family -M(floor(X/p)) onto every actual floor-Li event as a physical prime-like family.
2. Use the completed reciprocal-band renewal to recover the unweighted prime discrepancy from the genuine cofactor-weighted innovation.

The first interpretation requires an arithmetic admission and an occurrence map; BR1-BR2 prove the exact condition and refute the unrestricted extension. The second interpretation is valid ONLY with the complete divisor convolution; BR3 identifies what the already-paid theorem actually recovers. Neither route licenses using the endpoint bound for Mobius parent coefficients on different prime-event coefficients.

Continuity: today's Coordinator UB/CR, own HM, Analytic HF, Wheel PC, Census UC, Referee LC and Lean repair report were available and retrieved. Yesterday's Coordinator CD/SA/FB, own CF/CT/FW, Analytic ZD/MB/SC, Wheel RF/DG/RA, Census NC/BL/CR, Referee AP/DA and Lean reports were read at their relevant claims and continuation checkpoints. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD. No scheduled execution was presumed. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no new entry after October 18; EXT-20261018-PNT-1 and the #915 target-equivalence/anchor safeguards remain relevant.

In particular: HM1 is accepted only in its saturated domain; UC's R=8,10,29 counterexamples and LC's fixed-rank obstruction stay intact. CF2's sharpened positivity is #1127, not a bound on this new defect. HF's 71/52+eps high-frequency result remains a proper-sector PAPER_PROOF with independent review pending; it is not used as a premise here. AP's adaptive common-prefix payment and UB's greedy-optimization obstruction are not rederived.

### D. Mathematical Derivation

#### Exact Original Carrier

For the floor-Li formulas take integer R>=3, X=R^2-1, y=R-1, N=floor(X/(y+1))=R-1. Define

```text
L(n)=floor(Li_2(n)), lambda(q)=L(q)-L(q-1),
epsilon(q)=1_Prime(q)-lambda(q), B(n)=pi(n)-L(n),
I_y(T)=sum_(y<q<=T) epsilon(q) M(floor(T/q)),
P_lambda,y(T)=sum_(y<q<=T) lambda(q) M(floor(T/q)),
S_y(T)=sum_(1<=n<=T, P+(n)<=y)mu(n), including n=1,
A_y(T)=S_y(T)-P_lambda,y(T).
```

The original compiled Buchstab declaration gives M(T)=A_y(T)-I_y(T) whenever 1<=y and floor(sqrt(T))<=y. This includes EVERY T=floor(X/k) used below. The cutoff y stays FIXED across these T. It is not replaced by floor(sqrt(T)) separately. All q, prime or composite, are present in lambda and epsilon. q=R is included when prime. Cofactor a=1 and every squareful a remain, with mu(a)=0 where appropriate.

Finite Fubini gives the exact cofactor form

```text
I_y(T)=sum_(1<=a<=floor(T/(y+1)))
          mu(a)[B(floor(T/a))-B(y)].              (BR.2)
```

The upper support is essential: extending a past T/(y+1) without max(y,floor(T/a)) would manufacture negative empty-interval charges. This is the clipping already documented in the October 22 source audit.

#### BR1. Complete Sign-Flip Admission

For integers 2<=q<=X let t=floor(X/q), p0=leastPrime(q). Then

```text
[forall 1<=a<=t, mu(aq)=-mu(a)]
  iff [mu(q)=-1 and q*p0>X].                    (BR.3)
```

Proof of necessity: a=1 forces mu(q)=-1, so q is squarefree with odd prime-factor parity. If p0<=t, choose a=p0. Then mu(a)=-1 but p0^2 divides aq, so mu(aq)=0, contradicting the required value +1. Thus p0>t, equivalently q*p0>X, with strict inequality because aq=X is admitted.

Proof of sufficiency: if p0>t, every 1<=a<=t is coprime to q. Multiplicativity gives mu(aq)=mu(a)mu(q)=-mu(a), also for squareful a. No statistical assumption is used.

Corollary: suppose q^2>X and q^4<=X^3. Primes satisfy (BR.3). If q is composite with mu(q) not -1, a=1 already fails. Otherwise q is squarefree with at least three distinct prime factors, so p0^3<=q. Hence (q*p0)^3<=q^4<=X^3, giving q*p0<=X and the collision witness above. Therefore only primes are admitted in this entire post-root region. This is an all-scale structural exclusion, not a numerical regularity.

#### BR2. The Exact Missing Physical-Lift Defect

For any integer q>=2 and t>=1 define M_q^cop(t)=sum_(a<=t,gcd(a,q)=1)mu(a). The valid multiplicative identity is

```text
sum_(a<=t)mu(aq)=mu(q)*M_q^cop(t),
d_X(q)=sum_(a<=floor(X/q))[mu(aq)+mu(a)]
      =M(floor(X/q))+mu(q)*M_q^cop(floor(X/q)).  (BR.4)
```

For squareful q both mu(q) and every mu(aq) vanish. For squarefree q, the coprimality mask is indispensable. Thus d_X(q) has three exact sectors: M(t) if mu(q)=0; M(t)+M_q^cop(t) if mu(q)=+1; and M(t)-M_q^cop(t)=sum_(a<=t,gcd(a,q)>1)mu(a) if mu(q)=-1. For post-root PRIME q the defect is zero, as already proved by primeCombLargePrimeFamilyMass_eq_neg_mertens.

Set

```text
J_y(X)=sum_(y<q<=X)epsilon(q)*sum_(a<=X/q)mu(aq),
mathcalD_y(X)=sum_(y<q<=X)lambda(q)*d_X(q).
```

Then the exact original innovation is

```text
-I_y(X)=J_y(X)+mathcalD_y(X).                  (BR.5)
```

Proof: expand J+mathcalD, combine epsilon+lambda=1_Prime, and apply the valid sign flip ONLY on the actual prime terms. This proves the identity without assuming any composite event has a prime ancestry.

The equality also holds with any prescribed real weight/mask chi(q,a) inserted in EVERY displayed double sum, because the prime flip is pointwise. It does not establish that any particular chi is the original #915 returned-cell mask or that its coefficients equal mu(a). That source admission remains separate.

The occurrence multiplicity is explicit. Put

```text
ell_y(n)=sum_(q|n, q>y)lambda(q),
c_y(n)=1_(P+(n)>y)-ell_y(n), with the indicator zero at n=1.
J_y(X)=sum_(n<=X)mu(n)*c_y(n).                 (BR.6)
```

There is at most one actual prime divisor >y in n<=X, since (y+1)^2>X. This proves the indicator in (BR.6), not ell_y(n)<=1. Composite floor-Li divisors can reuse the same n. No repeated label is converted into independent historical credit.

The full Mertens square is therefore

```text
M(X)=A_y(X)+J_y(X)+mathcalD_y(X),
M(X)^2=A^2+J^2+mathcalD^2+2AJ+2A*mathcalD+2J*mathcalD.  (BR.7)
```

In particular, replacing G=-I by J drops mathcalD^2+2J*mathcalD and its interaction with A. These terms have not been proved favorable or small. The atom-level criterion (BR.3) is sufficient for zero defect of each admitted atom but is NOT necessary for an aggregate d_X(q)=0, which can also cancel accidentally; that distinction is preserved.

#### BR3. What The Already-Proved Renewal Actually Recovers

The existing `sum_convolveOne_mul_mertensSummatory_div` says, for EVERY g and X,

```text
sum_(n<=X) [sum_(d|n)g(d)] M(floor(X/n)) = sum_(q<=X)g(q).
```

Apply it to g(q)=epsilon(q)1_(q>y). The divisor coefficient is exactly c_y(n) in (BR.6), but the outer weight is M(floor(X/n)), NOT mu(n). Thus

```text
B(X)-B(y)=sum_(n<=X)c_y(n) M(floor(X/n))
         =sum_(k=1..N)I_y(floor(X/k)).          (BR.8)
```

Equivalently, swap the k,q sums. For each q, t=floor(X/q), the coefficient is sum_(k<=t)M(floor(t/k))=1 by the existing unit renewal theorem. This is an exact coefficient-by-coefficient bridge on the genuine epsilon stream. It is NOT a norm-preserving bijection of physical prime occurrences. Every (q,k,a) label and its mu(a) weight is retained until the divisor sum cancels it.

This is the successful PAID algebraic recovery. It is credited to MobiusRenewalTelescope, not promoted to a new cancellation estimate. Replacing c_y(n) by epsilon(n), replacing M(floor(X/n)) by mu(n), retaining only k=1, or changing y separately at each descendant changes the statement.

For #1115, the actual completed parent coefficient is instead
t_R(z)=M(floor(X/z))-M(floor(X/(z+1))). Its completed band is the difference of two Mertens endpoints. The prime-event coefficient on that same reciprocal interval is sum epsilon(q), which is different: at R=3,z=2, t_R(2)=mu(3)+mu(4)=-1 whereas epsilon(3)+epsilon(4)=0. Its existing endpoint estimate cannot be transferred by renaming z or q.

#### BR4. Compulsory Descendant Cross Terms And Absolute-Value Tax

For EVERY integer t>=1 write u_k=M(floor(t/k)), 1<=k<=t. The paid renewal says sum u_k=1. For all k>t/2, u_k=M(1)=1, and there are c=ceil(t/2) such entries. Hence

```text
sum_(k<=t)abs(u_k) >= c+abs(1-c)=2ceil(t/2)-1,
sum_(k<=t)u_k^2 >= ceil(t/2),
2sum_(k<l)u_k*u_l = 1-sum_k u_k^2 <= 1-ceil(t/2).  (BR.9)
```

This is a genuine deterministic within-event signed restriction: the completed coefficient stays 1 despite an unavoidable linearly growing absolute mass and diagonal. It does not assert that every pair is negative or that interactions BETWEEN different q are controlled.

Choose ONCE alpha=(1+b_base)/2<1 and spend the existing positive growth loss alpha-b_base. The certified Mertens envelope gives an associated C_alpha>=0, so

```text
sum_(k<=t)abs(M(floor(t/k)))
 <= C_alpha*t^alpha*sum_(k<=t)k^(-alpha)
 <= C_alpha*t/(1-alpha).                      (BR.10)
```

The last step is the elementary decreasing-integrand bound. Thus the absolute mass is Theta(t), with constants chosen before t, while the signed sum is exactly 1. This quantifies the loss of taking absolute values before completion. It does not improve the Mertens input used to prove its upper bound, nor bound the complete prime-side source after multiplying by epsilon(q).

#### BR5. The Rounding Part Is Already Affordable

Let l(q)=Li_2(q)-Li_2(q-1), r(n)=Li_2(n)-L(n) in [0,1), and let P_l denote the same cofactor-weighted tail with l instead of lambda. Swapping the finite cofactor/event sums gives

```text
P_lambda,y(X)-P_l,y(X)
 = r(y)M(N)-sum_(a<=N)mu(a)r(floor(X/a)).       (BR.11)
```

Let D_mu(N)=sum_(a<=N)mu(a)^2, P=(D_mu+M(N))/2 and Q=(D_mu-M(N))/2, the actual positive and negative Mobius populations. The second sum lies in [-Q,P]. If M(N)>=0, the first term lies in [0,M(N)]; if M(N)<0 it lies in [M(N),0]. In both cases

```text
abs(P_lambda-P_l) <= max(P,Q)
                   =(D_mu(N)+abs(M(N)))/2 <= N.   (BR.12)
```

The constant is uniform before X,y and uses the genuine signs, including zero squareful coefficients. This is a finite signed-box refinement; the O(R) order was already recorded in the October 22 Mellin audit and is NOT claimed as a new endpoint saving. Bounded floor rounding does not bound epsilon, J or mathcalD. Squaring a corrected bracket still requires the mixed rounding term.

### E. Quantitative Consequence And Complete Return

Let c_li=li(x)-Li_2(x), the fixed normalization constant, and H_R=c_li+r(X)-B(y). The complete prime-side source, including its historical anchor, is exactly

```text
Z_R=H_R-sum_(k=1..N)I_y(floor(X/k)),
Z_R^2=H_R^2+sum_k I_k^2+2sum_(k<l)I_k I_l-2H_R sum_k I_k.  (BR.13)
```

H_R=O(R) is elementary: pi(y)<=y and 0<=Li_2(y)<=(y-2)/log 2 for y>=2. The fixed constant and r(X) are retained. Consequently an RH-scale bound on the COMPLETE descendant sum is TARGET_EQUIVALENT to the present prime-side objective, not an independently established missing lemma.

#### 2. FOUR-WAY SOURCE MAP

All sources are at the main SHA in B; material blob SHAs follow in K. No new normalizer is introduced.

| Euler / finite AC | VF / actual prime discrepancy | NNS / OAI | Square blocks / native HIGH | Prime/Mobius coupling |
| --- | --- | --- | --- | --- |
| Complete F_R includes all primorial divisors and Euler compensation. Finite-AC Q_R=sum_(a,b<R)mu(a)mu(b)floor(X/(ab))=2M(y)-M(X) is a DIFFERENT exact Mobius source. K_R=max_(0<=v<R)(M(v)-1)^2/(v+1) is unchanged. | Z_R=li(X)-pi(X); BR.13 is an EXACT_IDENTITY using every epsilon event, fixed y and B(y). Compiled complete-wheel theorem supplies the Euler/prime bridge. | BR.7 and BR.13 preserve all real signed cross terms. OAI `actual_low_tuple_polynomial_sq_eq_signed_gram` is exact on ideal-labelled Hecke atoms with original masks, Gaussian and normalizer. No coefficient map from those atoms to c_y or epsilon is proved: OPEN_BRIDGE, not an isometry-based saving. | Compiled Buchstab gives M(X)=A-I; Euler gives M(X)=2M(y)-Q_R. These are EXACT_IDENTITIES on the full prefix, not shell energies. LOW/HIGH/coherent and mixed return remains unchanged. | Prime q>y has the exact injective occurrence map (q,a)->aq and mu(aq)=-mu(a). Composite floor-Li q requires BR.4-BR.6. Weighted renewal is convolution, not pointwise coefficient identification. |

For #915, `vfMid915HistoricalMovingOwner_eq_signedMismatch` is an existing exact whole-history scalar bridge. It explicitly retains its original signed anchor and deterministic floor-Li/VF difference; its reference demand is not claimed to be a manufactured physical sieve. No BR identity admits new clipped returned cells. The raw source remains D_raw(R+1), denominator (abs(D_raw(R))+beta_R)^2 with beta_R=m_R+(1-2w_R)P_R. The canonical phase correction is -2sqrt(2)D_raw+2 in squared defects. No uncompressed historical absolute mass or unproved first-bad payment is inserted.

#### 3. FIRST SIGNED LOSS

| Source / declaration | Lost information and exact tax | Consumer / paid recovery / complement / falsifier |
| --- | --- | --- |
| PrimeCombReciprocalBandCancellation: primeCombLargePrimeFamilyMass_eq_neg_mertens | Extending the PRIME hypothesis to lambda events is an invalid equality, not a harmless norm inequality. Lost correction is mathcalD, including all parity/gcd sectors. | BR.5 recovers the exact weighted innovation; its size and 2J*mathcalD remain unpaid. R=3,q=6,a=1 is a genuine falsifier. |
| Buchstab: buchstab_innovation_eq_signed_high_prime_cofactor | Dropping M(floor(X/q)) or keeping only k=1 in the renewal loses sum_(k>=2)I_k. | Paid renewal restores the whole event discrepancy; no bound is gained. R=5 has I_1=0 but completed sum=-2. |
| MobiusRenewalTelescope: sum_convolveOne_mul_mertensSummatory_div | Triangle before completion replaces the exact coefficient 1 by at least 2ceil(t/2)-1. Dropping off-diagonal Gram replaces 1 by a diagonal >=ceil(t/2). | BR.9 restores the forced within-event cross terms; cross-q and the full original backlog are not thereby bounded. t=3 already gives (-1,1,1). |
| TWOAB_RENEWAL_COMPLETE_BAND: twoABCompleteReciprocalBand_eq_mertensDifference | Completion is paid for t_R(z), not epsilon reciprocal-bin coefficients. Restricting to high z removes the long-fibre band. | Existing growth consumer bounds root-adjacent a~R at O_eps(R^(b_base+eps)); a=1 still reaches X and costs O_eps(R^(2b_base+eps)). R=3,z=2 disproves coefficient identification. |
| CompleteSquareRootWheelFractionalBoundary: finiteWheelFract_sub_density_eq_physical_floorError | Triangle on virtual d>X before Euler subtraction discards exact termwise cancellation. | Already paid by #1122, not new BR mathematics. R=8 gives physical 3/5 plus virtual -6/5, not physical alone. |
| BR.13 full prime-side square | Replacing square of the completed sum by its diagonal discards every mixed descendant and historical term. | R=5561: diagonal 6629267, doubled off-diagonal -6593546, completed square 35721. This finite cancellation is not a global zero-covariance theorem. |

These are the actual losses on the selected transfer, not a claim to have enumerated every inequality in the 35,753-node OAI closure.

#### 4. PAID RECOVERY TEST

MobiusRenewalTelescope successfully recovers the exact discarded descendants on the literal g(q)=epsilon(q)1_(q>y) source, producing (BR.8). The sharper #1119 bound pays (BR.10) after spending a positive loss. #1115's numerical endpoint bound does NOT transfer to epsilon bins because their coefficients differ. #1127's complete cofactor positivity concerns the original wheel mu(e) fractional row, not mu(aq) or the floor-Li defect. #1128's near-resonance is a scope warning, not a bound on this real signed convolution. NNS algebra reconstructs all cross terms but supplies no new sign or norm bound. The remaining mixed/full-source bill is stated in (BR.7) and (BR.13), not suppressed.

#### 5. NET RESULT / ADMISSION VERDICT

**NO_NEW_GLOBAL_GAIN.** BR1 is a new source-admission classification for this proposed transfer; BR2 is a precise unmatched-source formula and decisive falsifier. They prevent a false cross-route recovery. BR3 is reused exact algebra, BR4 is a proper-row restriction, and BR5 only sharpens a paid rounding constant. No new route meets the directive's complete-source/global-exponent admission criterion. The baseline remains b_base, with its original positive-loss quantifiers.

### F. Falsification And Circularity Review

**Genuine floor-Li witnesses, with no stochastic events:** L(2)=0,L(3)=1,L(5)=2,L(6)=3. Thus at R=3,X=8, lambda(6)=1, but mu(6)=+1 whereas the fictional fresh-prime image of mu(1) is -1. Also lambda(3)=lambda(6)=1, so the REFERENCE lift of n=6 has the two labels (q,a)=(3,2),(6,1); ell_2(6)=2. This is reference-lift multiplicity, not a claim that epsilon(3) is nonzero.

At R=3, A=-3,J=-2,mathcalD=3, so M(8)=-2 exactly. At R=5,X=24,y=4, the complete innovation vector is (0,0,-1,-1); its total -2 equals B(24)-B(4), while I_y(24)=0. Here J=-6 and mathcalD=6, so their cancellation is necessary. No multiplicative estimate of the form abs(completed sum)<=C*abs(I_y(X)) can hold for all R>=3. This refutes that particular proposed uniform recovery, not an estimate with an additional independently bounded term.

The complete defect has no universal sign: mathcalD_2(8)=3 but mathcalD_13(195)=-6. The latter is a primary-program certificate, not claimed independently reproduced by the small integral program.

Primary program: standard-library Python integer/Fraction arithmetic, sieve through X=30924720, trial-factor comparison for mu(1)..mu(1599), and rigorous fixed-point interval evaluation of Li_2. Discovery R=3..40; held-outs R=47,64,97,127,549,5561. It checked 21318 full-q admission classifications and exact defect formulas, including 3590 genuine prime families, 38 direct event/cofactor equalities, 44 complete renewals, 44 full Gram identities and 44 rounding bounds. Separately every t=1..5560 passed the signed-renewal and BR.9 inequalities. Small-root witnesses were selected by the registered exact scan; the defect sign comparison was a disclosed proof-led follow-up, not a preregistered asymptotic prediction.

| R | I_y(X) | Complete B(X)-B(y) | All strict descendants | Diagonal | Doubled off-diagonal |
| --- | ---: | ---: | ---: | ---: | ---: |
| 47 | 0 | -9 | -9 | 129 | -48 |
| 64 | 18 | -9 | -27 | 491 | -410 |
| 97 | 19 | -13 | -32 | 695 | -526 |
| 127 | 36 | -11 | -47 | 1749 | -1628 |
| 549 | -96 | -77 | 19 | 27957 | -22028 |
| 5561 | 2145 | -189 | -2334 | 6629267 | -6593546 |

Every large-root quantity in this table is exact, including the floor-Li integer potential. It is not a floating Li diagnostic. The program certifies L(30924720)=1911875 and pi(30924720)=1911671; the low anchor B(5560)=-15 yields the displayed difference -189. These finite values do not certify any asymptotic.

**Numerical enclosure proof:** range-reduced log uses the positive atanh series with its geometric tail. For t>0, F(t)=log(t)+sum_(k>=1)t^k/(k*k!) has derivative exp(t)/t, so Li_2(n)=F(log n)-F(log 2). Every operation is an outward-rounded integer interval at scale 10^45; the 180-term series has an explicitly bounded positive tail. Each potential is accepted only when BOTH interval endpoints have the same integer floor. No numerical library's accuracy is assumed.

Independent small program uses a DIFFERENT method: monotone left/right rectangles of 1/log(t) on a 1/512 grid, with rational log enclosures, plus trial factorization and direct summation. It certifies all L(n),2<=n<=24, reproduces the R=3 and R=5 failures, and verifies all six terms of (BR.7) at R=3,4,5. It also independently restores complete wheel physical/virtual terms at R=2,3,8,12,14,16, using an explicitly arbitrary rational reference for the algebraic identity. This includes d=X=195 at R=14, q=R prime, squareful coefficients, and the empty R=2 wheel. It does not repeat the author's entire large-root computation or claim a second human review.

Both programs completed with exit code zero and passed syntax checks. SHA-256: primary e988c276be6139702ee640e09dcec4f194871822a57eb82bc82ab5c6682f55cd; independent 6ad9c803ca9dc2174e3cb0d26ee1b1aa1eab593fab52a516b8bac4f7bea5c760. Full programs and recorded output follow this synthesis.

Novelty/scope check: the October 22 audit already warns that floor-Li is not prime membership and pays O(R) rounding. MobiusRenewalTelescope explicitly calls its general identity classical. BR does NOT claim either observation as new. The inspected source and scoped repository search did not supply the exact BR.3 all-cofactor admission classifier or this completed physical-lift defect application. This is not an exhaustive literature-priority claim. All new proof review is SELF_AUDIT.

### G. Conceptual Interpretation

There are two distinct operations: a fresh-prime multiplicative sign flip, and a linear floor-Li event decomposition. Their resemblance does not identify their physical sources. The exact obstruction is the parity of q plus collisions between its prime factors and the admitted cofactor prefix. Even an event with the correct aggregate sign may have the wrong pointwise ancestry.

The valid common operation is divisor convolution. It restores the unweighted event count through all descendants, with forced cancellation already present in the Mobius inverse. That restoration can have large positive diagonal and negative complete off-diagonal contributions. It is not a free upper bound on the restored count and cannot be spent a second time as independent physical history.

### H. Competing Mechanisms

| Mechanism | Decision / independent gap / decisive next check |
| --- | --- |
| Prime-like physical lift of all floor-Li events | ABANDON this unrestricted version. BR.3 is the corrected atom-level criterion; BR.5 is the mandatory defect. Both an actual wrong-sign event and duplicate reference occurrence are already certified. |
| Complete renewal as automatic quantitative transfer from #1115 | REVISE. Exact algebra survives and is already proved, but epsilon parents are not Mobius parents. Any new consumer must control the actual divisor coefficient c_y and full cross-return, not only diagonal I_y(X). R=5 is the smallest tested falsifier. |
| Genuine nonlocal arithmetic correlation of actual prime innovations and their companion smooth bracket | CONTINUE only as an open investigation. BR.4 separates squareful, even-parity and shared-factor odd-parity defects without assuming them small. The full A/J/mathcalD combination is the consumer. No new independently sufficient size lemma is supplied here. |
| Existing complete OAI endpoint and independent finite-AC route | RETAIN separately. Their source coefficients, K_R, losses and conditional consumers are unchanged; BR does not replace them or launch duplicate specialist work. |

All nine route families remain available. This execution does not claim rolling coverage of every family or retire a full route based on a failed auxiliary map.

### I. Specialist Handoffs

**Coordinator:** consume BR.3-BR.8 as the answer to the requested exact weighted bridge. Correct the #1115/post-root-family attribution. The common paid theorem is divisor renewal, not coefficient equality. Do not promote M3 on the basis of this identity; its direct physical shortcut is refuted and its signed complement remains unpaid.

**Analytic:** the precise new residual is mathcalD=sum lambda(q)[M(t_q)+mu(q)M_q^cop(t_q)], with the three sectors in BR2. A proposed analytic estimate must retain J and A or prove a justified centering/transfer. HF's prime-frequency sector does not currently map to these composite-event coprime prefixes. No new arbitrary-covariance entrance test is imposed on OAI.

**Wheel:** compare the actual t_R(z) coefficients with epsilon-bin coefficients BEFORE applying the complete-band endpoint theorem. The R=3,z=2 mismatch and full g*1 convolution provide compact tests. Preserve the long-fibre band and both mixed orientations in Q_R; the current prime-side completion is not a proof of the finite-AC input.

**Census:** no range extension is requested merely to confirm BR.3. For a new hypothesis, preregister a sector-resolved test of J and mathcalD on the same integer source, distinguishing squareful, mu(q)=+1 and shared-factor mu(q)=-1 events. The diagnostic is their signed joint residual, not their individual absolute masses. Reuse the exact Li certificate method; finite data cannot justify an exponent.

**Referee:** independently check the necessity/sufficiency of BR.3, especially qp0=X; the q^4<=X^3 corollary; BR.5's sign; the distinction between lambda reference multiplicity and epsilon multiplicity; fixed-y completion; and BR.12's shared r(y) term. Review the mathematical claims, not only successful computation. New results are awaiting your verdict.

**Lean Verification:** NO_NEW_ENDPOINT_THEOREM_TO_FORMALIZE. Existing unit and g-weighted renewal should be reused rather than duplicated. BR.3 and the weighted BR.5 adapter are possible small enabling lemmas only after independent acceptance and an actual consumer need. Do not encode smallness of mathcalD, I or the completed sum as an assumed premise and label it recovered cancellation. No proof branch or PR was created by this role.

### J. First Independently Missing Lemma

**No independently sufficient size lemma was identified for this proposed recovery.** Its initially missing unconditional prime-like admission is now REFUTED, and its corrected algebra is BR.5/BR.8. The exact first unpaid arithmetic is a coefficient-sensitive restriction on the joint A_y+J_y+mathcalD_y source, or on the full fixed-y descendant sum with its anchor. Merely asserting the desired bound on either COMPLETE expression would rename the corresponding target.

The next genuinely narrower research question is whether the actual floor-Li-selected shared-factor correlation

```text
C_odd(X,y)=sum_(y<q<=X, q composite, mu(q)=-1)
  lambda(q) * sum_(a<=floor(X/q), gcd(a,q)>1)mu(a)
```

has an independently provable signed restriction AFTER its original companion parity and squareful terms are retained. This is the exact odd-parity defect sector, not an arbitrary owner energy. No exponent, sign, centering, or sufficiency theorem for it is conjecturally inserted as a premise here. First inspect already-proved coprime-prefix/ancestry results for this literal coefficient and choose a falsifiable estimate; otherwise return NO_NEW_RECOVERY rather than introduce another target-equivalent hypothesis. The sharp atom classifier and known nonzero full defect make that next test well-defined.

### K. Next-Run Resume Capsule, Evidence And Publication

Resume from main 655f897e274a8ba8a2fed80ecc1fc75a0d849174, refreshing actual main first. New claims are 20261110-owner-2/BR1-BR6. Keep HM/CF/AP/UC/LC/UB at their exact original status; none is silently strengthened or superseded. Strongest baseline remains #1119 at b_base with every positive loss. BR admission status is NO_NEW_GLOBAL_GAIN / NO_NEW_ACCEPTED_ROUTE, with exact falsification and supporting paper arithmetic.

The early IN_PROGRESS checkpoint was published at commit 1b3d5fbc89e4f82039fdc5edc82779feb8a16d19, report blob b0cfc10c3d66dd7b450703bea9f53b1a87885096. Commit metadata confirmed that only today's own report changed; immutable readback matched exactly. Final publication verification will be recorded after successful commit/readback.

Tool limitations: direct git clone failed with a proxy 403, so all repository authority/source/CI reads used the authenticated GitHub connector. An optional mpmath diagnostic import was unavailable; no conclusion uses it, and both final programs use only the standard library with rational/integer certificates. No local Lean execution, proof-source edit, other report edit, issue/PR/workflow mutation, agent launch, merge, permission change or schedule change occurred. No background continuation is asserted.

### K1. Material Source And Continuity Ledger

All following source reads are pinned to main 655f897e274a8ba8a2fed80ecc1fc75a0d849174. Blob hashes are actual GitHub file blobs, not report-derived labels.

| Source | Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/AGENTS.md) | c9c89f01b90b526de9f3e8ea92478e36504711b6 |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/CURRENT_PROOF_CONTRACT.md) | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| [docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md) | e922d4ba9362a1ae196af8f6de88f7417f92087c |
| [research/CompleteSquareRootWheelFractionalBoundary.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/CompleteSquareRootWheelFractionalBoundary.lean) | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| [research/VF_MID_FLOOR_LI_BUCHSTAB_EXACT_BRACKETS_20261022.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/VF_MID_FLOOR_LI_BUCHSTAB_EXACT_BRACKETS_20261022.lean) | 918876c6ad7697388d565d39b15db5b8c3cc9952 |
| [research/FiniteWheelCofactorPositivity.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/FiniteWheelCofactorPositivity.lean) | f83a3daefc2b9d603014af912ec82b4a7f52cfac |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919WindowErrorClosure.lean) | f629db1b2b65d6ec042ac9432397d4b6316200c6 |
| [research/oai_434/VF919ExplicitSquareBlockPacking.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | 32999039fdeea99c58a070c1c4ee9c140720dd44 |
| [research/oai_434/VF919ExplicitFixedSourceSlotCount.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | 1f17f9401a63d16227db2e2aad020b9f74bc5f4e |
| [docs/COORDINATE_ATLAS.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/docs/COORDINATE_ATLAS.md) | cd0419d00a37739fe5a292f5cb738e33213949d5 |
| [research/VF_MID_DYADIC_PREFIX_OWNER.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/VF_MID_DYADIC_PREFIX_OWNER.lean) | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| [lean-toolchain](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/lean-toolchain) | ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5 |
| [lake-manifest.json](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/lake-manifest.json) | a34d142c3d75a602a8b0f8241a4fb504d5c7c5a4 |
| [RHLean/Proof/PrimeCombReciprocalBandCancellation.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/RHLean/Proof/PrimeCombReciprocalBandCancellation.lean) | 7c2b4c8a55a1a2fe5bfa0dfe95996e416b0fd19f |
| [research/VF_MID_FLOOR_LI_CRITICAL_BALANCE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/VF_MID_FLOOR_LI_CRITICAL_BALANCE.lean) | 0bd3fa8229e338647dbc6e1de484e98d14f8e911 |
| [RHLean/Analysis/PrimeSieveCollapseIdentity.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/RHLean/Analysis/PrimeSieveCollapseIdentity.lean) | 7a7e47fe4bc31588ebafa9011d89205dbf0bf1f2 |
| [research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean) | 9a9336dad72171b6d572a1c1ae88d1ae8b56b530 |
| [research/oai_434/VF919OriginalLowTupleSignedGram.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919OriginalLowTupleSignedGram.lean) | dd2fde01ae6e2446da4e69b30f6fc80fcadb858d |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| [research/EULER_SELF_DUAL_POINTWISE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/EULER_SELF_DUAL_POINTWISE_20261027.lean) | c327c556f39ee7014fd774b24d0f95a1ece050e0 |
| [research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| [research/oai_434/VF919NativeStrictMertens.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919NativeStrictMertens.lean) | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| [research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean) | 028d9f2bbfa1a8de1fe63e9bd368aca13aae6825 |
| [research/TWOAB_RENEWAL_OAI_CONSUMER_20261108.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/TWOAB_RENEWAL_OAI_CONSUMER_20261108.lean) | 4880969f71f4668b18a9e09fd6f4007b7e62a5d5 |
| [research/MERTENS_EXPONENT_ENVELOPES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/MERTENS_EXPONENT_ENVELOPES.lean) | 655b896e8d5a41c9f8fc3c456eae3944a98bfefe |
| [research/VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean) | eb84f59055bd31dc117be034d45c92eb9dab8f27 |
| [research/VF_MID_FLOOR_LI_BUCHSTAB_MELLIN_ASYMPTOTIC_AUDIT_20261022.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/VF_MID_FLOOR_LI_BUCHSTAB_MELLIN_ASYMPTOTIC_AUDIT_20261022.md) | ef0c149efd2c5cb6a63feb0b538e2f076e695f04 |
| [RHLean/Analysis/MobiusRenewalTelescope.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/RHLean/Analysis/MobiusRenewalTelescope.lean) | 223013cd640148a1513ef9e836653aa86cf01cdb |
| [research/VF_MID_915_FLOOR_LI_TRANSPORT_BOUNDARY.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/VF_MID_915_FLOOR_LI_TRANSPORT_BOUNDARY.lean) | 10829c3857b6a375d1dd8179f78a35550c9e67d8 |

Report evidence read from agent-reports at intake; these are historical input blobs, not a claim that another agent has reviewed BR.

| Date / report | Input blob SHA |
| --- | --- |
| [2026-11-09/00-coordinator-am](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-09/00-coordinator-am.md) | 6fba43130391ad4a606aa3809c20f344d668c709 |
| [2026-11-09/10-owner-payment](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-09/10-owner-payment.md) | 643e8a004d9d8e0be102b03e2f79bb3b217ae916 |
| [2026-11-09/20-analytic-type-ii](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-09/20-analytic-type-ii.md) | d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3 |
| [2026-11-09/30-finite-wheel](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-09/30-finite-wheel.md) | 0624246d03b19cf76c01e186b7d868a248d896ef |
| [2026-11-09/40-prime-census](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-09/40-prime-census.md) | 8c927cc6c323533ba1cfd369404b25aa4f9cef91 |
| [2026-11-09/50-adversarial-referee](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-09/50-adversarial-referee.md) | a5d0192eb31c0efb3767187a7752f1a0d07f8534 |
| [2026-11-09/60-lean-verification](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-09/60-lean-verification.md) | 8b60c6136ac151774be2db0aee8f543f286b53aa |
| [2026-11-10/00-coordinator-am](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-10/00-coordinator-am.md) | 1cf71a74d0e80d5dc05ab1ef08f1ad6fcf134c9a |
| [2026-11-10/10-owner-payment](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-10/10-owner-payment.md) | 2bed3da8ed4ddd49c0708378a1c3da5b4883cb54 |
| [2026-11-10/20-analytic-type-ii](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-10/20-analytic-type-ii.md) | d8337353a94b465f53a0c6a65ad46aac1dc1927e |
| [2026-11-10/30-finite-wheel](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-10/30-finite-wheel.md) | 79ff39e0f79a30f4cf1657b22f96ebe49de4d717 |
| [2026-11-10/40-prime-census](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-10/40-prime-census.md) | 8a89d1a899850e39320a96bf35a6f221060fc8a7 |
| [2026-11-10/50-adversarial-referee](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-10/50-adversarial-referee.md) | ae7de1cb1900818b8844c2c3c7da597cc8f7eaa9 |
| [2026-11-10/60-lean-verification](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-11-10/60-lean-verification.md) | 0355c3203ede834e1abbe9bc2fc161bc7d7ece04 |

External inbox: [EXTERNAL_HANDOFFS.md](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/EXTERNAL_HANDOFFS.md), blob 038018145c0fddb2f6306c0712373adf9cd1ea52. Today's original Owner input is preserved byte-for-byte above; the later early-checkpoint blob is separately recorded in K.

Final pre-publication main refresh at 2026-11-10 08:41:16 EST remained 655f897e274a8ba8a2fed80ecc1fc75a0d849174. The open/draft pull-request collection remained empty on the later refresh; merged reports were checked against actual PR/run metadata, not schedule assumptions.

### K2. Hosted Audit Evidence

Existing exact-head checks, not new runs launched by Owner:

| Input | Verified run | Head / conclusion |
| --- | --- | --- |
| OAI window-saturated LOW versus principal gain | [42552018910](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910) | 77ee815846d6d534c866f0752aa33b84c385610a, completed/success |
| Complete-wheel cofactor positivity | [42743502306](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42743502306) | 866b3d2121309cdd854f9d64e2a6adbbc708ef9b, completed/success |
| Genuine dyadic prime near resonance | [42798625661](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42798625661) | d5b8003f6239611a457560b6fd16e29f16255e75, completed/success |
| Complete reciprocal-band consumer #1115 | [42517562043](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42517562043) | 7256681db5adfc907426deaef676244aeb4384dd, completed/success |

Actual #1119 job 128949473700 closing audit lines:

~~~text
2026-11-09T03:01:16.0190718Z PASS window-error-closure OAI.SevenEighths.RHLeanWindowSaturated.native_beta_le_window_error_closed_of_fine: #[propext, Classical.choice, Quot.sound], closure=35358
2026-11-09T03:01:16.0201132Z PASS window-error-closure OAI.SevenEighths.RHLeanWindowSaturated.native_beta_le_near_uniform_window_error_closed: #[propext, Classical.choice, Quot.sound], closure=35375
2026-11-09T03:01:16.0203239Z PASS window-error-closure RHLean.Analysis.native_mertens_window_error_closed_of_fine: #[propext, Classical.choice, Quot.sound], closure=35736
2026-11-09T03:01:16.0208723Z PASS window-error-closure RHLean.Analysis.native_mertens_fixed_window_error_closed_of_fine: #[propext, Classical.choice, Quot.sound], closure=35737
2026-11-09T03:01:16.0213448Z PASS window-error-closure RHLean.Analysis.native_mertens_near_uniform_window_error_closed: #[propext, Classical.choice, Quot.sound], closure=35753
~~~

### K3. Reproducible Finite Certificates

The programs below were executed as ordinary Python research checks, not Lean or proof-source modifications. They rely only on the standard library. The primary output's progress-only lines are omitted; its complete terminal result is retained. The second program uses a different integral enclosure and direct factorization on the small witnesses.

#### Primary Program

~~~python
"""Exact source tests for 20261110-owner-2/BR; no Lean execution."""

from bisect import bisect_right
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, isqrt
import json

SCALE = 10**45


def ceildiv(a, b):
    return -(-a // b)


def atanh_log_bounds(x, terms=55):
    z = (x - 1) / (x + 1)
    assert 0 <= z <= F(1, 3)
    z2 = z * z
    power = z
    total = F(0)
    for j in range(terms):
        total += 2 * power / (2 * j + 1)
        power *= z2
    tail = 2 * power / ((2 * terms + 1) * (1 - z2))
    return total, total + tail


LOG2 = atanh_log_bounds(F(2))


@lru_cache(None)
def log_bounds(x):
    assert x > 0
    if x < 1:
        lo, hi = log_bounds(1 / x)
        return -hi, -lo
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    lo, hi = atanh_log_bounds(x)
    return k * LOG2[0] + lo, k * LOG2[1] + hi


def fixed_bounds(bounds):
    lo, hi = bounds
    return (lo.numerator * SCALE // lo.denominator,
            ceildiv(hi.numerator * SCALE, hi.denominator))


def ei_without_gamma(tlo, thi):
    """Enclose log(t)+sum t^k/(k*k!), with exact directed integers."""
    low = fixed_bounds(log_bounds(F(tlo, SCALE)))[0]
    high = fixed_bounds(log_bounds(F(thi, SCALE)))[1]
    power_lo = power_hi = SCALE
    terms = 180
    for k in range(1, terms + 1):
        power_lo = power_lo * tlo // (SCALE * k)
        power_hi = ceildiv(power_hi * thi, SCALE * k)
        low += power_lo // k
        high += ceildiv(power_hi, k)
    next_hi = ceildiv(power_hi * thi, SCALE * (terms + 1))
    # Successive terms t^k/(k*k!) have ratio < t/(k+1).
    assert thi < SCALE * (terms + 2)
    tail = F(next_hi, terms + 1) / (1 - F(thi, SCALE * (terms + 2)))
    high += ceildiv(tail.numerator, tail.denominator)
    return low, high


EI2 = ei_without_gamma(*fixed_bounds(LOG2))


@lru_cache(None)
def li2_bounds(n):
    assert n >= 2
    if n == 2:
        return 0, 0
    lo, hi = ei_without_gamma(*fixed_bounds(log_bounds(F(n))))
    return lo - EI2[1], hi - EI2[0]


@lru_cache(None)
def potential(n):
    lo, hi = li2_bounds(n)
    assert lo // SCALE == hi // SCALE, (n, lo, hi)
    return lo // SCALE


def sieve(limit):
    prime = bytearray(b"\x01") * (limit + 1)
    prime[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if prime[p]:
            start = p * p
            prime[start::p] = b"\x00" * ((limit - start) // p + 1)
    return prime, [p for p in range(2, limit + 1) if prime[p]]


def mobius_sieve(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    least = [0] * (limit + 1)
    for p in range(2, limit + 1):
        if not least[p]:
            for n in range(p, limit + 1, p):
                mu[n] = -mu[n]
                if not least[n]:
                    least[n] = p
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    mertens = [0]
    for v in mu[1:]:
        mertens.append(mertens[-1] + v)
    return mu, mertens, least


def trial_mu(n):
    sign = 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            sign = -sign
            if n % d == 0:
                return 0
        d += 1
    return -sign if n > 1 else sign


def main():
    heldouts = [47, 64, 97, 127, 549, 5561]
    discovery = list(range(3, 41))
    prime, primes = sieve(heldouts[-1] ** 2 - 1)
    mu, mertens, least = mobius_sieve(max(5560, 40**2))
    assert all(mu[n] == trial_mu(n) for n in range(1, 1600))
    pi = lambda n: bisect_right(primes, n)
    events = {q: potential(q) - potential(q - 1) for q in range(3, 1600)}
    first_flip = first_overlap = first_completion = first_unweighted = None
    counters = dict(rows=0, classification=0, defect=0, renewal=0,
                    gram=0, prime_families=0, rounding=0)
    reports = []

    for R in discovery + heldouts:
        X, y, N = R * R - 1, R - 1, R - 1
        def backlog(n):
            return pi(n) - potential(n)
        base = backlog(y)
        def innovation(n):
            return sum(mu[a] * (backlog(n // a) - base)
                       for a in range(1, n // (y + 1) + 1))
        values = [innovation(X // k) for k in range(1, N + 1)]
        E = backlog(X) - base
        assert sum(values) == E
        counters['renewal'] += 1
        diag = sum(v*v for v in values)
        cross2 = 2 * sum(values[i] * values[j]
                         for i in range(len(values)) for j in range(i))
        assert diag + cross2 == E * E
        counters['gram'] += 1
        if first_completion is None and values[0] != E:
            first_completion = dict(R=R, E=E, I=values[0], descendants=values[1:])
        if first_unweighted is None and values[0] != E:
            first_unweighted = first_completion

        # Sharp signed-box rounding budget, using certified Li_2 endpoints.
        r0lo, r0hi = li2_bounds(y)
        r0lo -= potential(y) * SCALE
        r0hi -= potential(y) * SCALE
        mN = mertens[N]
        rho_lo, rho_hi = ((mN*r0lo, mN*r0hi) if mN >= 0
                          else (mN*r0hi, mN*r0lo))
        for a in range(1, N+1):
            if not mu[a]:
                continue
            u = X // a
            lo, hi = li2_bounds(u)
            lo -= potential(u)*SCALE
            hi -= potential(u)*SCALE
            if mu[a] == 1:
                rho_lo -= hi
                rho_hi -= lo
            else:
                rho_lo += lo
                rho_hi += hi
        squarefree = sum(abs(v) for v in mu[1:N+1])
        bound2 = squarefree + abs(mN)
        assert 2*rho_lo >= -bound2*SCALE and 2*rho_hi <= bound2*SCALE
        counters['rounding'] += 1

        if R <= 40:
            direct = sum((int(prime[q])-events[q])*mertens[X//q]
                         for q in range(y+1, X+1))
            assert direct == values[0]
            counters['rows'] += 1
            multiplicity = {}
            defect_total = 0
            literal_lift = 0
            reference = 0
            for q in range(y+1, X+1):
                t = X // q
                full_flip = all(mu[a*q] == -mu[a] for a in range(1,t+1))
                criterion = mu[q] == -1 and q*least[q] > X
                assert full_flip == criterion
                if q**4 <= X**3:
                    assert full_flip == bool(prime[q])
                counters['classification'] += 1
                C = sum(mu[a] for a in range(1,t+1) if gcd(a,q)==1)
                family = sum(mu[a*q] for a in range(1,t+1))
                assert family == mu[q]*C
                defect = family + mertens[t]
                assert defect == mertens[t] + mu[q]*C
                counters['defect'] += 1
                if prime[q]:
                    assert defect == 0
                    counters['prime_families'] += 1
                if events[q]:
                    reference += events[q]*mertens[t]
                    literal_lift += events[q]*family
                    defect_total += events[q]*defect
                    if not full_flip and first_flip is None:
                        a = next(a for a in range(1,t+1) if mu[a*q] != -mu[a])
                        first_flip = dict(R=R,X=X,q=q,a=a,lam=events[q],
                                          mu_a=mu[a],mu_aq=mu[a*q])
                    for a in range(1,t+1):
                        n = a*q
                        multiplicity.setdefault(n,[]).append(q)
            assert literal_lift + reference == defect_total
            for n, qs in sorted(multiplicity.items()):
                if len(qs)>1 and mu[n] and first_overlap is None:
                    first_overlap = dict(R=R,X=X,n=n,mu_n=mu[n],qs=qs)
            if R in [3,4,5,6,8,10,14,40]:
                reports.append(dict(R=R,I=values[0],E=E,desc=E-values[0],
                                    lift=literal_lift,reference=reference,
                                    defect=defect_total))
        else:
            reports.append(dict(R=R,X=X,piX=pi(X),L=potential(X),E=E,
                                I=values[0],desc=E-values[0],diag=diag,cross2=cross2,
                                rounding_bound2=bound2))
        print(json.dumps({'progress':R}),flush=True)

    # Renewed one-event descendants contain a large compulsory positive sector.
    for t in range(1,5561):
        terms = [mertens[t//k] for k in range(1,t+1)]
        assert sum(terms)==1
        assert sum(abs(v) for v in terms) >= 2*((t+1)//2)-1
        assert sum(v*v for v in terms) >= (t+1)//2
    print(json.dumps(dict(counters=counters,first_flip=first_flip,
                          first_overlap=first_overlap,first_completion=first_completion,
                          examples=reports,
                          certified_L={n:potential(n) for n in range(2,21)},
                          li_certificates={n:list(li2_bounds(n)) for n in [5,6,8,9,10]},
                          scale=SCALE,renewal_t_range=[1,5560]),indent=2))


if __name__ == '__main__':
    main()

~~~

#### Primary Terminal Result

~~~json
{
  "counters": {
    "rows": 38,
    "classification": 21318,
    "defect": 21318,
    "renewal": 44,
    "gram": 44,
    "prime_families": 3590,
    "rounding": 44
  },
  "first_flip": {
    "R": 3,
    "X": 8,
    "q": 6,
    "a": 1,
    "lam": 1,
    "mu_a": 1,
    "mu_aq": 1
  },
  "first_overlap": {
    "R": 3,
    "X": 8,
    "n": 6,
    "mu_n": 1,
    "qs": [
      3,
      6
    ]
  },
  "first_completion": {
    "R": 5,
    "E": -2,
    "I": 0,
    "descendants": [
      0,
      -1,
      -1
    ]
  },
  "examples": [
    {
      "R": 3,
      "I": -1,
      "E": -1,
      "desc": 0,
      "lift": 0,
      "reference": 3,
      "defect": 3
    },
    {
      "R": 4,
      "I": -2,
      "E": -2,
      "desc": 0,
      "lift": 3,
      "reference": 3,
      "defect": 6
    },
    {
      "R": 5,
      "I": 0,
      "E": -2,
      "desc": -2,
      "lift": 4,
      "reference": 2,
      "defect": 6
    },
    {
      "R": 6,
      "I": -1,
      "E": -3,
      "desc": -2,
      "lift": 1,
      "reference": 2,
      "defect": 3
    },
    {
      "R": 8,
      "I": 1,
      "E": -3,
      "desc": -4,
      "lift": 1,
      "reference": 1,
      "defect": 2
    },
    {
      "R": 10,
      "I": -1,
      "E": -3,
      "desc": -2,
      "lift": 6,
      "reference": 0,
      "defect": 6
    },
    {
      "R": 14,
      "I": 6,
      "E": -4,
      "desc": -10,
      "lift": -4,
      "reference": -2,
      "defect": -6
    },
    {
      "R": 40,
      "I": 9,
      "E": -7,
      "desc": -16,
      "lift": -8,
      "reference": -23,
      "defect": -31
    },
    {
      "R": 47,
      "X": 2208,
      "piX": 329,
      "L": 340,
      "E": -9,
      "I": 0,
      "desc": -9,
      "diag": 129,
      "cross2": -48,
      "rounding_bound2": 32
    },
    {
      "R": 64,
      "X": 4095,
      "piX": 564,
      "L": 575,
      "E": -9,
      "I": 18,
      "desc": -27,
      "diag": 491,
      "cross2": -410,
      "rounding_bound2": 40
    },
    {
      "R": 97,
      "X": 9408,
      "piX": 1163,
      "L": 1180,
      "E": -13,
      "I": 19,
      "desc": -32,
      "diag": 695,
      "cross2": -526,
      "rounding_bound2": 62
    },
    {
      "R": 127,
      "X": 16128,
      "piX": 1877,
      "L": 1892,
      "E": -11,
      "I": 36,
      "desc": -47,
      "diag": 1749,
      "cross2": -1628,
      "rounding_bound2": 78
    },
    {
      "R": 549,
      "X": 301400,
      "piX": 26112,
      "L": 26196,
      "E": -77,
      "I": -96,
      "desc": 19,
      "diag": 27957,
      "cross2": -22028,
      "rounding_bound2": 338
    },
    {
      "R": 5561,
      "X": 30924720,
      "piX": 1911671,
      "L": 1911875,
      "E": -189,
      "I": 2145,
      "desc": -2334,
      "diag": 6629267,
      "cross2": -6593546,
      "rounding_bound2": 3384
    }
  ],
  "certified_L": {
    "2": 0,
    "3": 1,
    "4": 1,
    "5": 2,
    "6": 3,
    "7": 3,
    "8": 4,
    "9": 4,
    "10": 5,
    "11": 5,
    "12": 5,
    "13": 6,
    "14": 6,
    "15": 7,
    "16": 7,
    "17": 7,
    "18": 8,
    "19": 8,
    "20": 8
  },
  "li_certificates": {
    "5": [
      2589424529915159079547753817666198134847795779,
      2589424529915159079547753817666198134847796150
    ],
    "6": [
      3177058610421608419958964383092369905129882314,
      3177058610421608419958964383092369905129882685
    ],
    "8": [
      4208554519441438393679223170282899379827390303,
      4208554519441438393679223170282899379827390677
    ],
    "9": [
      4676073972710067587286574891795319463021194911,
      4676073972710067587286574891795319463021195284
    ],
    "10": [
      5120435724669805152678392863474909612607987035,
      5120435724669805152678392863474909612607987407
    ]
  },
  "scale": 1000000000000000000000000000000000000000000000,
  "renewal_t_range": [
    1,
    5560
  ]
}

~~~

#### Independent Small Program

~~~python
"""Independent small certificates via monotone integral rectangles, not Ei."""
from fractions import Fraction as Q
from math import isqrt
import json

UNIT=10**24
GRID=512


def log_enclosure(v):
    k=0
    while v>=2:
        v/=2
        k+=1
    def series(z):
        a=(z-1)/(z+1)
        p=a
        value=Q(0)
        for j in range(30):
            value+=2*p/(2*j+1)
            p*=a*a
        return value,value+2*p/(61*(1-a*a))
    l,h=series(v)
    l2,h2=series(Q(2))
    return l+k*l2,h+k*h2


def inverse_log(v):
    lo,hi=log_enclosure(v)
    lower=Q(1,1)/hi
    upper=Q(1,1)/lo
    return (lower.numerator*UNIT//lower.denominator,
            -(-upper.numerator*UNIT//upper.denominator))


def factors(n):
    ans=[]
    p=2
    while p*p<=n:
        if n%p==0:
            e=0
            while n%p==0:
                n//=p
                e+=1
            ans.append((p,e))
        p+=1
    if n>1:
        ans.append((n,1))
    return ans


def mu(n):
    fs=factors(n)
    if any(e>1 for _,e in fs):
        return 0
    return (-1)**len(fs)


def prime(n):
    return n>=2 and factors(n)==[(n,1)]


def pi(n):
    return sum(prime(i) for i in range(2,n+1))


def M(n):
    return sum(mu(i) for i in range(1,n+1))


def main():
    bounds={2:(0,0)}
    lo=hi=0
    prev=inverse_log(Q(2))
    for j in range(2*GRID+1,24*GRID+1):
        cur=inverse_log(Q(j,GRID))
        lo+=cur[0]
        hi+=prev[1]
        prev=cur
        if j%GRID==0:
            bounds[j//GRID]=(lo,hi)
    den=GRID*UNIT
    L={n:lo//den for n,(lo,hi) in bounds.items()}
    assert all(lo//den==hi//den for lo,hi in bounds.values())
    lam={q:L[q]-L[q-1] for q in range(3,25)}
    assert lam[3]==lam[6]==1 and mu(6)==1
    output=[]
    for R in [3,4,5]:
        X=R*R-1
        y=R-1
        eps=lambda q:int(prime(q))-lam[q]
        I=lambda T:sum(eps(q)*M(T//q) for q in range(y+1,T+1))
        vals=[I(X//k) for k in range(1,R)]
        E=(pi(X)-L[X])-(pi(y)-L[y])
        assert sum(vals)==E
        J=sum(eps(q)*sum(mu(a*q) for a in range(1,X//q+1))
              for q in range(y+1,X+1))
        D=sum(lam[q]*sum(mu(a*q)+mu(a) for a in range(1,X//q+1))
              for q in range(y+1,X+1))
        assert -I(X)==J+D
        S=sum(mu(n) for n in range(1,X+1)
              if all(p<=y for p,e in factors(n)))
        P=sum(lam[q]*M(X//q) for q in range(y+1,X+1))
        A=S-P
        assert M(X)==A+J+D
        assert M(X)**2==A*A+J*J+D*D+2*A*J+2*A*D+2*J*D
        output.append(dict(R=R,I=I(X),completed=vals,E=E,J=J,D=D,A=A,M=M(X)))

    wheel=[]
    for R in [2,3,8,12,14,16]:
        X=R*R-1
        ps=[p for p in range(2,R) if prime(p)]
        divs=[(1,1)]
        density=Q(1)
        for p in ps:
            divs+= [(p*d,-s) for d,s in divs]
            density*=Q(p-1,p)
        physical=sum((s*Q(X%d,d) for d,s in divs if d<=X),Q(0))
        virtual=sum((s*Q(X,d) for d,s in divs if d>X),Q(0))
        full=physical+virtual
        assert full-X*density==-(1+pi(X)-pi(R-1))
        reference=Q(22,7)
        deterministic=X*density+pi(R-1)-1-reference
        assert full-deterministic==reference-pi(X)
        wheel.append(dict(R=R,physical=str(physical),virtual=str(virtual)))
    print(json.dumps(dict(L=L,checks=output,wheel=wheel,
                          rectangular_bounds={n:[str(Q(a,den)),str(Q(b,den))]
                                              for n,(a,b) in bounds.items() if n in [3,5,6,24]}),indent=2))


if __name__=='__main__':
    main()

~~~

#### Independent Terminal Result

~~~json
{
  "L": {
    "2": 0,
    "3": 1,
    "4": 1,
    "5": 2,
    "6": 3,
    "7": 3,
    "8": 4,
    "9": 4,
    "10": 5,
    "11": 5,
    "12": 5,
    "13": 6,
    "14": 6,
    "15": 7,
    "16": 7,
    "17": 7,
    "18": 8,
    "19": 8,
    "20": 8,
    "21": 9,
    "22": 9,
    "23": 9,
    "24": 10
  },
  "checks": [
    {
      "R": 3,
      "I": -1,
      "completed": [
        -1,
        0
      ],
      "E": -1,
      "J": -2,
      "D": 3,
      "A": -3,
      "M": -2
    },
    {
      "R": 4,
      "I": -2,
      "completed": [
        -2,
        0,
        0
      ],
      "E": -2,
      "J": -4,
      "D": 6,
      "A": -3,
      "M": -1
    },
    {
      "R": 5,
      "I": 0,
      "completed": [
        0,
        0,
        -1,
        -1
      ],
      "E": -2,
      "J": -6,
      "D": 6,
      "A": -2,
      "M": -2
    }
  ],
  "wheel": [
    {
      "R": 2,
      "physical": "0",
      "virtual": "0"
    },
    {
      "R": 3,
      "physical": "0",
      "virtual": "0"
    },
    {
      "R": 8,
      "physical": "3/5",
      "virtual": "-6/5"
    },
    {
      "R": 12,
      "physical": "29/35",
      "virtual": "-39/35"
    },
    {
      "R": 14,
      "physical": "-227/154",
      "virtual": "-19/154"
    },
    {
      "R": 16,
      "physical": "183/1001",
      "virtual": "-272/1001"
    }
  ],
  "rectangular_bounds": {
    "3": [
      "572367401573572846519746811/512000000000000000000000000",
      "572899857387834972533493007/512000000000000000000000000"
    ],
    "5": [
      "33134370901965327304827017/12800000000000000000000000",
      "1326196196184942443789734941/512000000000000000000000000"
    ],
    "6": [
      "1626211877261235302407470243/512000000000000000000000000",
      "406774115418893254640278703/128000000000000000000000000"
    ],
    "24": [
      "1299718495479872483231027969/128000000000000000000000000",
      "5200002018979934771464656151/512000000000000000000000000"
    ]
  }
}

~~~

### Verified Publication Receipt - 2026-11-10 08:43:47 EST

PUBLISHED / COMPLETE for this invocation at PAPER_PROOF + IDENTITY_ONLY + FINITE_COMPUTATION / REFUTED scope. NO_NEW_GLOBAL_GAIN; canonical VF, complete-wheel RH bound, finite A/C and RH remain OPEN. New paper claims are SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.

Substantive publication commit: 7a859de76f9db95d87a6bf7cfd233dd58eab3c11. Report blob: 7c9dd5e5b15b5684c81a12a0c6c5457f6f9e8f46. Immutable re-fetch matched all 116,961 characters exactly, including all earlier evidence and the IN_PROGRESS checkpoint. Commit metadata confirmed only research/agent_reports/2026-11-10/10-owner-payment.md changed, with 1,216 additions and zero deletions. Both certificate programs completed successfully; no local Lean or proof-source edit was performed. This receipt records completed verification, not a promise of later validation.

Next meaningful action is independent review of BR1-BR2 and a coefficient-faithful assessment of the remaining parity/gcd residual, as specified in I-J. The valid full renewal is already paid algebra, not an unproved endpoint improvement. No background continuation or specialist launch is asserted.


## Scheduled Continuation Checkpoint - 20261110-owner-3/DR

### A. Most Important Mathematical Development

IN_PROGRESS / PARTIAL. Resume the complete weighted floor-Li defect exposed by 20261110-owner-2/BR, not a fresh prime-like lift. The registered test is whether the exact coprime-prefix / shared-factor decomposition provides a controlled smaller-scale response on the SAME genuine Mobius source, and whether its full event aggregation preserves cancellation. Competing predictions: a uniform contractive response versus a multiplicity/coherent obstruction. No result or global gain is claimed at this checkpoint.

### B. Current Authoritative Objective

Actual trigger: 2026-11-10 16:15:01 EST; America/New_York reporting date 2026-11-10; platform run ID unavailable. Main f7947bee036c4dddb0c36fc9f53ab46b4fa90995. cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1. Read main AGENTS.md (c9c89f01b90b526de9f3e8ea92478e36504711b6), CURRENT_PROOF_CONTRACT.md (95566e37c8eaeb99ee680660df4f9d2e06ea5038), and governing cross-route directive (e922d4ba9362a1ae196af8f6de88f7417f92087c).

Canonical actual-prime VF and complete compensated wheel O(R log R) targets remain OPEN. Strongest certified explicit baseline retained: native_mertens_near_uniform_window_error_closed, b_base=7/8-7/(64*N_pack), every positive exponent loss. Original declaration and hosted job 128949473700 live-dependency/standard-axiom checks were retrieved. Latest #1130 is MERGED and certifies the local signed principal remainder only, not RD2-RD5 or Coordinator MD. No open/draft PR was present at intake.

### C. Registered Structural Investigation

Use X=R^2-1, y=R-1, lambda(q)=floor(Li_2(q))-floor(Li_2(q-1)), t_q=floor(X/q), and the literal full defect
mathcalD=sum_(y<q<=X)lambda(q)[M(t_q)+mu(q)*sum_(a<=t_q,gcd(a,q)=1)mu(a)].
Preserve the composite event, every (q,a) occurrence, squareful and even-parity companions, original J and A, and every mixed term in M(X)=A+J+mathcalD.

First derive the exact prime-factor recurrence for the coprime prefix; test any claimed contraction, sign, one-use property or small aggregate against actual admitted floor-Li events and a complete coefficient reconstruction. Existing BR completion and within-event renewal are paid inputs, not new discoveries. Before computation, freeze the proposed inequalities and smallest witness ranges. Any #915 source claim requires its own unchanged clipping/anchor/normalizer bridge.

### D-K. Continuity And Work Pending

TODAY=AVAILABLE for all six upstream roles; YESTERDAY=CARRY_FORWARD for 2026-11-09. Latest Coordinator 20261110-coordinator-1513-EST/MD and M3 assignment consumed; prior BR/HM/CF, Analytic RD and ZD, Wheel JC/RF, Census UC/NC, Referee SR/AP, and Lean #1130/#1127 evidence retained at their individual scopes. MD and SR extensions remain paper/self-audited, not a certified baseline upgrade. EXTERNAL_HANDOFFS.md is unchanged at 038018145c0fddb2f6306c0712373adf9cd1ea52; no new entry after October 18.

Direct clone is unavailable (proxy CONNECT 403); authenticated repository reads work. No local Lean, source/policy edits, other-report edits, proof branch, PR, workflow, schedule, permission change or agent launch. Only this owned report is authorized for publication. Substantive derivation, falsification, quantitative relevance and final handoffs remain IN_PROGRESS. This append preserves all earlier daily evidence byte-for-byte.
