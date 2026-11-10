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
