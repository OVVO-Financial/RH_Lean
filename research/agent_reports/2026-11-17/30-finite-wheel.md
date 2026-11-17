# RH | Finite Wheel & Incidence - 2026-11-17

## Early Checkpoint - 20261117-wheel-0205-EST/GD

### A. Structural Question

IN_PROGRESS / PARTIAL. No new mathematical result is claimed at this checkpoint. Investigate Coordinator 20261116-coordinator-2309-EST/SC's growing-deletion assignment on the genuine u_6 source. For fixed 1/2 <= beta < 1, determine the literal truncated inverse mass at y=log x and y=x^(1/4), including all higher prime powers. An infinite Euler product alone is not a lower bound for the truncated sum.

### B. Authority And Continuity

Actual scheduled trigger: 2026-11-17 02:05:03 EST; RUN_ID_UNAVAILABLE. Main=4d5482805bac6a8f29d4fb4dadc61eca0bc06525. AGENTS blob=c4f36b772f8a4b0c24fe566b90fafb646073c60f; CURRENT_PROOF_CONTRACT blob=95566e37c8eaeb99ee680660df4f9d2e06ea5038; half policy=96ad4439ec458af6168f7d9cb3eef5dde291d37c.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1.

Intake reporting revision=340d4615ce36a377756b5bc5837f5cf0bc0cdbb5, with an untruncated tree. Latest actual publications: Coordinator SC, Owner FB, Analytic EF, own TP, Census MC, Referee CF, Lean CR. All latest files and relevant November 16 predecessors were retrieved; task-relevant new findings and review statuses are being reconciled. Coordinator mirrors have identical blob fda92549dd9291c491005fdf70847b90d9be385a. Today Owner/Analytic available; other upstream roles TODAY=PENDING, YESTERDAY=CARRY_FORWARD. External inbox 7d63d434690d00dffce9c90335d41c4f62d85798 is unchanged, with no entry after October 18.

Main's canonical VF square von-Koch estimate remains OPEN. The native Q_R=2M(R-1)-M(R^2-1) source and strict K_R were inspected in original Lean. #1139 is merged; the complete open/draft PR collection is empty. Exact-head CI reuse and source dependency checks remain to be completed in the final synthesis. No local Lean is permitted.

### C. Registered Hypothesis And Consumer

Let P_y={primes 5<=p<=y}. Put u(n)=(-1)^(number of distinct prime divisors >3), S(x)=sum_(n<=x)u(n), and T_y(x)=sum_(n<=x,(n,product P_y)=1)u(n). Reuse accepted TP1-TP2:

    T_y(x)=sum_(d<=x)b_y(d)S(floor(x/d)),
    b_y(1)=1, b_y(p^e)=2^(e-1) for p in P_y, e>=1,
    b_y(d)=0 if d has a prime factor outside P_y.

Proposed investigation: factor b_y into a positive smooth-count coefficient and a powerful coefficient; derive an explicit truncation error at logarithmic y and a genuine polynomial-scale bound at y=x^(1/4). Compare the exact forward restoration as well, so deletion cost is not misidentified as a source gain. All cutoffs are fixed for each outer x throughout every inner summation.

Preregistered finite checks: independent trial-factor coefficients; b_y convolved with the signed local kernel equals the unit; b_y equals the proposed positive convolution; literal forward/inverse prefix identities; prime-power and cross-prime endpoint controls. Tests will use small predetermined cutoffs and scales, not a repeated large wheel or factor-incidence scan. No finite pass will establish asymptotics.

### D-M. Pending Work And Half-Continuation Capsule

ROUTE=FINITE-AC bounded feasibility, not a new accepted RH route. The existing closed-boundary consumer requires an independently derived complete-source cost eta(h)<h at actual h=Theta-1/2>0; it then gives b_next=1/2+(h+eta(h))/2<Theta. Preserve every ordered row, J's strict radical mask, unit/history/powerful terms and cross-row interactions. The present work audits whether a growing deletion could supply that arithmetic input; it does not assume the input.

STATUS=IN_PROGRESS. PROOF/COMPUTATION/INDEPENDENT_REVIEW=PENDING. RH=OPEN; VERIFIED_ETA=NONE. Only this owned report is authorized for remote publication.

## Growing Deletion: Subpower Cost Versus A Full-Power Return

### Final Research Synthesis - 20261117-wheel-0205-EST/GD

### A. Most Important Structural Discovery

**The actual truncated prime-deletion inverse has two sharply different costs.** For each fixed 1/2 <= beta < 1, deleting primes through log x costs

```text
exp((1+o(1))*(log x)^(1-beta)/((1-beta)*log log x)) = x^o(1),
```

whereas deleting primes through x^(1/4) costs

```text
(rho(4)*H_1/(3*(1-beta)) + o(1))*x^(1-beta),
H_1 = product_(prime p>=5) (1+1/(p*(p-2))) < infinity.
```

These are statements about the LITERAL d<=x sum, not a lower bound guessed from its infinite Euler product. The second cost is a sharp power loss for the floor-faithful positive inverse on prefix envelopes, including an explicit unit-sign model. The model is not genuine u_6.

**There is also an actual-source signed restriction.** At the quarter-power cutoff the inverse's unit-quotient layer is asymptotic to c_4*x/2, where c_4=rho(4)*H_1/3>0. The sum of ALL other inverse layers on the genuine source is asymptotic to -c_4*x/2. Thus these layers must cancel to o(x); their full quadratic cross term cancels the leading sum of squares. This is genuine arithmetic cancellation in the transformed source, but only at a coarse density scale. It does not control the original S, the fixed-gcd row, or Q_R at an improved power.

The bounded feasibility assignment is completed. Logarithmic deletion can transmit an independently supplied power improvement without a fixed power tax, but supplies none itself. Quarter-power deletion cannot produce a gain by the displayed separate absolute-envelope estimates. Signed alternatives are not refuted.

| Stable claim | Evidence and scope |
| --- | --- |
| 20261117-wheel-0205-EST/GD1 | PAPER_PROOF / SELF_AUDIT: exact positive convolution for the deletion inverse, its literal truncation bound, and logarithmic-cutoff asymptotic. Local TP inversion is reused, not new. |
| GD2 | PAPER_PROOF / SELF_AUDIT: quarter-power weighted asymptotic from classical smooth-integer counting, with a completely explicit source transfer and constant. Also an elementary lower bound independent of that asymptotic. |
| GD3 | PAPER_PROOF / SELF_AUDIT: sharp floor-prefix inverse cost and a bounded/unit-sign model obstruction, scoped to coefficient-generic transfer. |
| GD4 | PAPER_PROOF / SELF_AUDIT: forced genuine unit-layer/complement cancellation and complete quadratic accounting; coarse transformed-source information only. |
| GD5 | FINITE_COMPUTATION: 39,618 exact/rational-interval assertions passed; changing the inner cutoff fails at x=625. No asymptotic follows from these tests. |

All new claims are INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. The November 17 GD labels are distinct from the November 11 complete-gcd-norm GD claims. **NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_RH_ROUTE; VERIFIED_ETA=NONE; RH=OPEN.**

### B. Current Authoritative Objective

Actual trigger: 2026-11-17 02:05:03 EST, America/New_York; platform RUN_ID_UNAVAILABLE. Main is [4d5482805bac6a8f29d4fb4dadc61eca0bc06525](https://github.com/OVVO-Financial/RH_Lean/commit/4d5482805bac6a8f29d4fb4dadc61eca0bc06525). The current main AGENTS and proof contract were retrieved, together with the governing half-continuation, cross-route, continuity, dynamic and complete-return instructions and relevant DAG/atlas entries. Newer main priorities supersede older task-selection prose only.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1. Prior HIGH, finite-wheel and cancellation-chain safeguards are preserved, not treated as competing current task assignments.

The canonical `VFCanonicalSquareVonKochStatement` remains one C>=0 before every integer R>=2 with |pi(R^2)-vfCanonical(R^2)|<=C*R*log R, vfCanonical=vfMid+sqrt(2). Its inspected terminal still explicitly assumes `ClassicalVonKochRHCriterion`. The native Mertens/finite-AC consumer is separate; no missing arithmetic premise is proved here.

**Baseline receipt.** The inspected `native_mertens_near_uniform_window_error_closed` gives every-positive-loss Mertens growth at b_base=7/8-7/(64*N_pack), with its actual fixed `nearUniformSlotCount`. Spending that positive difference gives a fixed bound |M(n)|<=C*n^(7/8). No comparison with an unrelated N_* or no-loss bound at b_base is asserted. At tested head 77ee815846d6d534c866f0752aa33b84c385610a all 14 checks pass. The actual [type/dependency/axiom audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700) and audit source were read: five checked closures have sizes 35358,35375,35736,35737,35753 and only propext, Classical.choice, Quot.sound. A fresh untruncated tree comparison of 2,514 preexisting Lean/pin/scripts/lean files found only aggregate RHLean.lean changed. This is scoped reuse of unchanged certification, not a fresh full-main compilation or a new independent derivation of the imported analytic chain.

The complete open/draft PR collection is empty. Recent #1135-#1139 are human-merged. #1139's tested head 760a105553788fa7005e86b1230699fd871a2934 has the SAME tree as current main, 987c764248812e4e587d1e076d9a1d6277515fb7, and 13/13 passing checks. Its [actual eight-root audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43929804765/job/133518873411) reports only standard axioms and closure sizes 92,77,49,48,585,590,618,619. It certifies the R=139 pointwise obstruction, not FR's full analytic recovery or the present GD claims. No CI was launched; no local Lean was run.

### C. Structural Mechanism Investigated

Coordinator SC specifically requested the truncated cost for P_y={primes 5<=p<=y} at y=log x and y=x^(1/4). Accepted TP1-TP4 already settle fixed finite prime rules, including the missing higher powers and mixed returns. Accepted FR1-FR3 give the genuine u_6/fixed-row bridge. CF/CR's generic critical inverse review is closed as a supplier search; it is not repeated here.

The new step is to expose the arithmetic multiplicities of the GROWING deletion inverse as a convolution of ordinary smooth integers with a nonnegative powerful coefficient. This proves where its mass actually lies below x. In particular it permits a direct test of truncation, reveals a linear-sized unit layer, and prevents silently renewing the cutoff after each division.

### D. Exact Definitions And Theorems

For integer R>=2 retain

```text
X_R=R^2-1, M(t)=sum_(1<=n<=floor(t))mu(n), M(0)=0,
K_R=max_(0<=t<R, integer t)(M(t)-1)^2/(t+1),
C_R(g)=sum_(1<=a,b<R,gcd(a,b)=g)mu(a)mu(b)floor(X_R/(ab)),
Q_R=sum_g C_R(g)=2M(R-1)-M(X_R).
```

Original Lean definitions `eulerSelfDualFloor`, `eulerSelfDualBilinear`, `eulerFixedGcdRowInt` and `squareRootHistoricalK` were read. The accepted PAPER bridge, not newly formalized mathematics, is

```text
u(n)=u_6(n)=(-1)^(number of DISTINCT primes >3 dividing n), u(1)=1,
S(t)=sum_(1<=n<=floor(t))u(n), S(t)=0 for 0<=t<1,
Y_R=floor(X_R/36), J(R)=sum_(m<=Y_R,rad(36m)<R)u(m),
C_R(6)=2J(R)-S(Y_R), |J(R)|=O_epsilon(R^(1+epsilon)).
```

u is neither genuine mu, FP's square-excluding f_6, nor Hecke a6. Its powers at 2,3 have sign +1; every positive power of any other prime has sign -1. FR supplies same-power transfers between S and M for every fixed exponent >1/2, with the unit, history and powerful returns intact.

For real y>=2, let P_y={prime p:5<=p<=y}. Define multiplicative coefficients, all equal to 1 at n=1 and zero when any prime divisor lies outside P_y:

```text
c_y(p^e)=1, k_y(p^e)=-1, b_y(p^e)=2^(e-1)       (e>=1),
h_y(p)=0, h_y(p^e)=2^(e-2)                     (e>=2).
T_y(t)=sum_(n<=floor(t), no p in P_y divides n)u(n).
A_beta(x,y)=sum_(d<=x)c_y(d)*d^(-beta),
B_beta(x,y)=sum_(d<=x)b_y(d)*d^(-beta),
N_y(t)=sum_(d<=t)c_y(d), B_y(t)=sum_(d<=t)b_y(d).
```

The symbol B_y(t) is UNWEIGHTED; B_beta(x,y) is weighted. Neither is the historical K_R. Empty products include the unit. Throughout each identity y is frozen at its outer chosen value, including every smaller argument t=x/d.

**GD1: literal convolution and logarithmic cutoff.** Coefficientwise,

```text
k_y*b_y=delta_1, b_y=c_y*h_y,
S(x)=sum_(d<=x)k_y(d)T_y(floor(x/d)),
T_y(x)=sum_(d<=x)b_y(d)S(floor(x/d)).                         (GD.1)
```

The first and the two source equalities are TP infrastructure. Let

```text
F_beta(y)=product_(p in P_y)(1-p^(-beta))/(1-2p^(-beta)),
G_beta(y)=product_(p in P_y)(1-p^(-beta))^(-1).
```

For ALL sufficiently large x, uniformly for 1/2<=beta<1,

```text
0<=1-B_beta(x,log x)/F_beta(log x)<=x^(-1/64),
0<=1-A_beta(x,log x)/G_beta(log x)<=x^(-1/64).               (GD.2)
```

For each FIXED beta in that interval, using classical PNT,

```text
log B_beta(x,log x) ~ log A_beta(x,log x)
  ~ (log x)^(1-beta)/((1-beta)*log log x).                  (GD.3)
```

Thus both costs are subpower but exceed every fixed power of log x eventually. The asymptotic is not asserted uniformly as beta approaches 1. The truncation bound GD.2 does not require PNT.

**GD2: the quarter-power cost.** Define the all-prime coefficient h by the h_y rule at EVERY p>=5 and zero at 2,3. Then

```text
H_1=sum_d h(d)/d=product_(p>=5)(1+1/(p*(p-2)))<infinity,
c_4=H_1*rho(4)/3>0.
```

rho is the classical Dickman function for genuine smooth INTEGER counting. For every fixed lambda>0, as x tends to infinity with y=x^(1/4),

```text
N_y(lambda*x) ~ rho(4)*lambda*x/3,
B_y(lambda*x) ~ c_4*lambda*x.                              (GD.4)
```

For every FIXED 1/2<=beta<1,

```text
A_beta(x,x^(1/4)) ~ rho(4)*x^(1-beta)/(3*(1-beta)),
B_beta(x,x^(1/4)) ~ c_4*x^(1-beta)/(1-beta).                (GD.5)
```

In addition, for all x>=1 and y>=2,

```text
B_y(x)<=H_1*x, B_beta(x,y)<=H_1*x^(1-beta)/(1-beta).         (GD.6)
```

A weaker elementary lower bound at y=x^(1/4) is a fixed positive multiple of x^(1-beta)/(log x)^4 for all sufficiently large x. Thus the exact POWER 1-beta is already forced without using the Dickman asymptotic. No assertion here extends beta to 1.

**GD3: sharp floor-prefix cost.** On functions F:{1,...,floor(x)}->R with max_n |F(n)|/n^beta<=1, define L_(x,y)F=sum_(d<=x)b_y(d)F(floor(x/d)). Then its output norm, divided by x^beta, is exactly

```text
mathcal N_beta(x,y)=x^(-beta)*sum_(d<=x)b_y(d)*floor(x/d)^beta,
2^(-beta)*B_beta(x,y)<=mathcal N_beta(x,y)<=B_beta(x,y).     (GD.7)
```

At y=x^(1/4), this is bounded above and below by positive fixed multiples of x^(1-beta). Even a SINGLE fixed synthetic +/-1 coefficient sequence with F(n)=n^beta+O(1) can have L_(x,x^(1/4))F of order x. This is a coefficient-generic obstruction, not a counterexample to the genuine u source.

**GD4: forced signed return on the genuine source.** At y=x^(1/4), put

```text
U(x)=sum_(x/2<d<=x)b_y(d)=B_y(x)-B_y(x/2),
V(x)=sum_(d<=x/2)b_y(d)S(floor(x/d)).
```

Then, with exact strict/nonstrict endpoints,

```text
T_y(x)=U(x)+V(x),
U(x)~c_4*x/2, V(x)~-c_4*x/2, T_y(x)=o(x).                (GD.8)
T_y(x)^2=U(x)^2+V(x)^2+2U(x)V(x)=o(x^2),
U(x)^2~V(x)^2~c_4^2*x^2/4,
2U(x)V(x)~-c_4^2*x^2/2.                                 (GD.9)
```

No favorable sign is asserted at every finite x, no quantitative power rate is supplied for o(x), and T_y is not identified with S or the original Euler statistic.

### E. Mathematical Proof

#### E1. Exact Multiplicity And Powerful Factorization

Unique factorization gives each integer exactly one decomposition n=d*m with all prime factors of d in P_y and none of m in P_y. The genuine weight is u(n)=k_y(d)u(m). This proves the forward source identity with no missing prime powers. The inverse local series is

```text
(1-z)/(1-2z)=1+sum_(e>=1)2^(e-1)z^e.
```

Multiplication by k_p(z)=(1-2z)/(1-z) gives 1. Every coefficient convolution is finite; composing floor dilations is exact. These are the accepted TP statements, now used at a different finite set for each outer x.

To expose the positive inverse's incidence, multiply its local series by 1-z:

```text
(1-z)^2/(1-2z)=1+z^2/(1-2z)
              =1+sum_(e>=2)2^(e-2)z^e.
```

Hence b_y=c_y*h_y. An exponent e at a prime is counted as the sum of its allowable smooth/powerful splits; this is a weighted convolution identity, not a claim of a unique split or permission to spend one physical occurrence repeatedly. h_y is nonnegative and supported on powerful integers including 1. At s=1 its local sum is 1+1/(p*(p-2)). The logarithms are summable by comparison with sum_(n>=5)1/n^2. This proves H_1<infinity and h_y<=h coefficientwise.

Since N_y(t)<=t,

```text
B_y(t)=sum_(d<=t)h_y(d)N_y(t/d)<=t*H_1.
```

Partial summation proves GD.6. All constants are independent of growing y; H_1 is an actual convergent product.

#### E2. A Genuine Truncation Estimate At Logarithmic Cutoff

Choose delta=1/32. For 1/2<=beta<1 put sigma=beta-delta, so 15/32<=sigma<31/32. The exact integer inequality 5^15>2^32 implies 2*5^(-sigma)<1 throughout this range. Thus every local series converges absolutely, and for a universal constant C,

```text
log F_sigma(y)<=C*sum_(5<=n<=y)n^(-sigma)
              <=C'*(1+y^(17/32)).
```

For example expand the logarithm into sum_(e>=1)(2^e-1)p^(-e*sigma)/e and bound it by a fixed multiple of p^(-sigma). The lower bound on sigma keeps that multiple uniform even at p=5.

Positivity gives the ACTUAL discarded tail bound

```text
0<=F_beta(y)-B_beta(x,y)
  =sum_(d>x)b_y(d)d^(-beta)
  <=x^(-1/32)*F_(beta-1/32)(y).                            (GD.10)
```

At y=log x the right side is at most exp(-log(x)/32+C'*(1+(log x)^(17/32)))<=x^(-1/64) for all sufficiently large x. Divide by F_beta>=1. Since c_y<=b_y, the same argument bounds G_beta-A_beta and division by G_beta>=1 proves GD.2. This direction matters: the infinite product supplies an upper bound first; the explicit missing-tail estimate supplies the lower comparison.

For fixed beta, log F_beta(y)=sum_(p in P_y)p^(-beta)+O_beta(sum_(p<=y)p^(-2beta)), and the same holds for log G_beta. The error is O(log y) at beta=1/2 and O_beta(1) above half, using only integer comparisons. Classical PNT and partial summation give sum_(p<=y)p^(-beta)~y^(1-beta)/((1-beta)*log y). This dominates those errors for every fixed beta<1 and proves GD.3. In particular log(cost)/log x tends to zero, but log(cost)/log log x tends to infinity.

#### E3. Smooth-Integer Transfer At A Polynomial Cutoff

External input, explicitly separate from new research: the classical fixed-u theorem is Psi(t,t^(1/u))~t*rho(u), u>0 fixed, with rho continuous and positive. It is stated in [Hildebrand and Tenenbaum, *On Integers Free of Large Prime Factors*, Transactions AMS 296 (1986), pp. 265-290, equations (1.1)-(1.3)](https://tenenb.perso.math.cnrs.fr/PPP/Psi%2B.pdf). This is a research-paper source; the theorem is credited to Dickman, not claimed here. Only this actual-integer count and its continuity are imported. The present transfer to b_y is proved below. No RH-conditioned small-y smooth estimate is used.

For any fixed a>0, monotonicity in the prime cutoff and continuity of rho squeeze Psi(a*x,x^(1/4))/(a*x) to rho(4): compare x^(1/4) with (a*x)^(1/(4+epsilon)) and (a*x)^(1/(4-epsilon)), then let epsilon decrease to zero. No undocumented uniform estimate in a growing u is needed.

For y>=3, inclusion-exclusion at the two OMITTED primes gives EXACTLY

```text
N_y(t)=Psi(t,y)-Psi(t/2,y)-Psi(t/3,y)+Psi(t/6,y).
```

Every division has its literal floor convention inside Psi. Therefore N_y(a*x)~rho(4)*a*x*(1-1/2-1/3+1/6)=rho(4)*a*x/3. The factor 1/3 must not be omitted.

For each fixed d, h_y(d) eventually equals h(d), and the preceding count at a=lambda/d applies. The remaining convolution tail divided by x is bounded by lambda*sum_(d>D)h(d)/d, uniformly in x,y. Let x tend to infinity at fixed D, then D tend to infinity. This proves GD.4 with c_4=rho(4)*H_1/3.

For weighted mass, partial summation yields

```text
B_beta(x,y)=x^(-beta)B_y(x)
             +beta*integral_1^x B_y(t)t^(-beta-1)dt.
```

Set t=x*v. GD.6 supplies the integrable dominating function H_1*v^(-beta), because beta<1. GD.4 applies for each fixed v>0, and dominated convergence gives c_4*(1+beta/(1-beta))=c_4/(1-beta). The same proof with N_y(t)<=t gives the A_beta constant. This proves GD.5, including beta=1/2. Constants may depend on fixed beta, never on x.

For the separate elementary lower bound let y=x^(1/4) and take FOUR DISTINCT primes in (y/2,y]. Their products are distinct by unique factorization, all at most x, and have b_y=1. Thus

```text
B_beta(x,y)>=binomial(pi(y)-pi(y/2),4)*x^(-beta)
             >>_beta x^(1-beta)/(log x)^4.
```

PNT supplies the last elementary prime-count size. Together with GD.6 this already gives log B_beta/log x ->1-beta, independently of the sharp constant. Thus the full power conclusion is not an artifact of smooth-number notation.

The UNTRUNCATED log F_beta(x^(1/4)) instead grows as 4*x^((1-beta)/4)/((1-beta)*log x). It is enormously larger than log B_beta, which is (1-beta)*log x+O_beta(1). Treating that product as a truncated lower bound would give a false conclusion.

#### E4. Floors And A Sharp Coefficient-Generic Obstruction

All b_y(d)>=0. Therefore F(n)=n^beta attains the norm of L_(x,y) under the stated prefix envelope, and no function can exceed it. For x/d>=1, (x/d)/2<=floor(x/d)<=x/d, proving GD.7. This retains the quotient collisions rather than substituting a real dilation for a floor.

There is also a single unit-sign model for every fixed beta in [1/2,1): let F(0)=0 and

```text
F(n)=2*floor((n+n^beta)/2)-n.
```

As in accepted TP's rounding construction, consecutive increments are +/-1, F(1)=1, F(n)=n^beta+O(1), and F(n)>=0. For n>=4 the latter follows from n^beta>=2 and F(n)>n^beta-2; check n=1,2,3 directly. The unit-quotient layer alone then gives

```text
L_(x,x^(1/4))F >= B_y(x)-B_y(x/2) ~ c_4*x/2,
L_(x,x^(1/4))F <= x^beta*B_beta(x,y)=O_beta(x).
```

This proves a linear-sized output for a fixed bounded-increment model, not merely a large majorant. It is NOT u and does not obey its full prescribed prime coefficients. It settles only the proposed envelope-only inverse transfer; it is not a new generic critical-inverse campaign or a refutation of signed original-source methods.

#### E5. Restoring The Genuine Signed Complement

On the genuine source, S(1)=1, so x/2<d<=x has exactly the unit contribution U. The remaining integers have d<=x/2 and form V, proving T=U+V without overlap. GD.4 at lambda=1 and lambda=1/2 proves U~c_4*x/2.

For each fixed z>=5, eventually P_z is a subset of P_(x^(1/4)). Hence

```text
|T_(x^(1/4))(x)|
 <= #{n<=x:no p in P_z divides n}
 = x*product_(p in P_z)(1-1/p)+O_z(1).
```

The product tends to zero as z tends to infinity, by the elementary Euler product/divergence of the harmonic series. First let x tend to infinity for fixed z, then z tend to infinity. This proves T=o(x) without a prime-distribution rate, sign independence or the Mertens baseline. Subtracting U gives V~-c_4*x/2 and squaring the EXACT two-term equality proves GD.9. Negative cross energy is spent only in this equality, not twice or in the original row square.

For further interpretation, the exact quotient-fibre identity is

```text
T_y(x)=sum_(1<=m<=floor(x))S(m)*[B_y(x/m)-B_y(x/(m+1))].   (GD.11)
```

Every fixed m bracket divided by x tends to c_4/(m*(m+1)). The paid fixed b=7/8 bound for M and accepted FR transfer give |S(m)|<=C*m^b, b<1. The absolute tail with m>=L, divided by x, is at most

```text
C*x^(b-1)*B_b(x/L,y)<=C*H_1*L^(b-1)/(1-b).
```

Thus dominated truncation of GD.11 recovers sum_(m>=1)S(m)/(m*(m+1))=0. This is the familiar first-order Euler/PNT cancellation in these coordinates, NOT a new RH estimate or a newly independent supplier. It explains why the leading positive smooth-density coefficient cancels. Bounding the remaining growing quotient-weight discrepancy at the required strict power is not provided by this scalar identity.

### F. Structural Consequence

The inverse's weighted population is not arbitrary. Its higher prime powers are organized by a positive powerful convolution of finite total 1/d mass, so its quarter-power cutoff has ordinary smooth-integer density, not the astronomical size of the untruncated weighted Euler product. The exact cost exponent is 1-beta.

The genuine signed input is also not free: its unit-quotient layer and the complete remaining layers MUST have opposite linear leading terms. Their full quadratic interaction removes the leading energy. This distinguishes the actual all-prime source from GD3's nonnegative model. It supplies a precise arithmetic configuration restriction, but only on the deleted/weighted transform. It is insufficient to make a new complete-source half-continuation active.

### G. Signed And Quantitative Relevance

The first signed loss is explicit. From GD.1, |S(t)|<=A*t^beta gives |T_y(x)|<=A*x^beta*B_beta(x,y). At logarithmic cutoff this is x^(beta+o(1)); at quarter-power cutoff it is only O_beta(x). GD3 shows that the inverse envelope cost is real, although the genuine input has the additional cancellation GD4.

Conversely, a UNIFORM two-parameter estimate |T_y(t)|<=A*t^gamma for EVERY 1<=t<=x at the SAME frozen y gives |S(x)|<=A*x^gamma*A_gamma(x,y). For fixed 1/2<=gamma<1, logarithmic deletion preserves gamma up to every positive loss, while quarter-power absolute restoration again only gives O_gamma(x). The latter is a limitation of this triangle bound, not a lower bound for the signed forward operator. Floor-quotient collisions can cancel its signed coefficients, so no false sharp forward norm is asserted.

Knowing only T_(log t)(t) or T_(t^(1/4))(t) on its moving diagonal does not supply the frozen-y estimate needed inside GD.1. At x=625 the genuine S is -223; replacing the inner frozen cutoff 5 by floor((625/d)^(1/4)) gives -210. This is an exact change of arithmetic source.

**Complete continuation, with its input still OPEN.** Write G(b) for every-positive-loss genuine Mertens growth and h=Theta-1/2>0 at the actual closed boundary. The available starting theorem is G(b_base), and the compiled closed-envelope result supplies G(Theta). A genuinely proved row estimate

```text
|C_R(6)| <<_epsilon R^(1+eta+epsilon)*sqrt(K_R), eta<h,
```

with eta>=0 fixed before R, plus accepted FR's all-prefix recovery would give G(1/2+(h+eta)/2), contradicting Theta=1/2+h. There is no need for a zero to attain the supremum or for a gain uniform as h tends to zero. The strict inequality eta<h is the unpaid arithmetic step, not a premise proved by deletion. In S coordinates the desired exponent is gamma=1/2+(h+eta)/2<Theta. Logarithmic restoration would retain an independently proved such gamma; quarter-power separate absolute restoration would not. No new gamma is obtained.

| Coordinate | Exact bridge or remaining barrier |
| --- | --- |
| Euler / FINITE-AC | Original Q_R and C_R(6) definitions retained; FR's C_R(6)=2J-S bridge and same-power inverse are accepted paper inputs. Growing deletion acts on S with frozen y. |
| Square blocks / MU-LIFT | FR's square interpolation pays all intervening sites; J remains O_epsilon(R^(1+epsilon)). No new whole-prefix subcritical lift or nonlinear recurrence is proved. |
| VF / prime discrepancy | F_R-D_R=li(X)-pi(X), actual prime seats, clipping, anchors and first-bad source remain distinct. No equality with T_y or its unit layer is supplied. |
| NNS / OAI | Original ideal-character signs, height/conductor/Gaussian factors and all physical returns have no coefficient map to u here. The baseline is a one-way size input only. |
| CORR4 / NYMAN | Their q^2 mixed-tail and complete taper obligations are neither replaced nor paid by a smooth-integer count. This run is not claimed as substantive coverage of those routes. |

The full identities Q_R^2=sum_g C_R(g)^2+2sum_(g<g')C_R(g)C_R(g') and D_G=||H||^2+||E||^2-2<H,E> remain. No cross-row term, unit response, radical/history return or powerful tail is removed. GD.9 is the square of T_y, not one of these original squares.

**Paid-recovery test:** TP/FR recover the exact signed source and a same-power dictionary. Classical smooth counting pays positive coefficient mass only. GD4 recovers a leading transformed cross term, but no power remainder. Existing cofactor positivity, reciprocal-band and OAI theorems have no source-compatible strict-cost transfer furnished here. FB's prime-seat minority bound and EF's floor-response pulse apply to different carriers. NET RESULT=NO_NEW_GLOBAL_GAIN.

### H. Falsification And No-Circularity Review

The checker was written before execution. Primary scope from the checkpoint: independent prime-factor coefficients, inverse and positive convolutions, literal forward/inverse prefixes, prime powers and boundary controls. Proof-led additions in that same pre-execution checker: quotient grouping, the unit/complement split, the nonnegative unit-sign model and the adaptive-cutoff control. They are not retroactively described as the original checkpoint's complete test list.

Parameters: coefficient checks n<=2048 at cutoffs 4,5,7,11,13; all prefix x=0..256 at those cutoffs; selected logarithmic and quarter-power scales 64,624,625,626,2400,2401,2402,14640,14641,14642,28560,28561,28562,65536. One sieve through 65536 supplies genuine u, checked independently by trial factorization through 2048. Logarithmic cutoffs are certified with rational atanh-series remainder intervals. Half and three-quarter weighted sums have rational intervals from exact integer roots, not floating estimates. Every checked floor and prime boundary is literal.

39,618 assertions passed. Syntax validation passed. Repeating the identical subsecond checker solely to capture its complete result produced the same output; this is one test campaign, not two independent verifications. The complete source and compact output are embedded below.

| x | cutoff regime; floor(y) | S(x) | T_y(x) | unit U | full return V |
| ---: | --- | ---: | ---: | ---: | ---: |
| 625 | quarter; 5 | -223 | -268 | 8 | -276 |
| 28561 | quarter; 13 | -505 | -5660 | 142 | -5802 |
| 65536 | log; 11 | 8 | -7310 | 84 | -7394 |
| 65536 | quarter; 16 | 8 | -9206 | 146 | -9352 |

These small samples do NOT exhibit the eventual asymptotic ratio V/U -> -1; no such extrapolation is claimed. GD.8 is proved independently. Negative controls: b_5(25)=2, not 1; k_5(25)=-1, not +1; excluding d=x at x=25 loses weight 2; b_y(2)=b_y(3)=0 although u(2)=u(3)=1. Crossing y=5,7,11,13 changes the actual masked source. Recomputing y inside a quotient fails at x=625 as stated above.

**Novelty scope.** Main code searches covered b_y, Dickman, growing deletion, smooth/powerful and truncated inverse. Original `PrimeWheelPartialError.lean`, the exact-Li Dickman note, the Hecke square-exclusion cutoff note, TP, FP/FR, HB/CF/CR and current SC handoff were inspected where relevant. Their carriers differ: the continuous exact-Li Dickman model is not the genuine smooth-integer count; Hecke b_y excludes large squares and is not this positive inverse. No equivalent literal two-regime cost/forced-unit-return theorem was found in this scoped search. No exhaustive historical-corpus or literature-priority claim is made. Ordinary Euler multiplication, TP inversion, FR recovery, classical PNT/Dickman and the scalar Euler zero at 1 are credited as prior inputs.

This investigation proves an independent cost theorem and coarse transformed-source cancellation, not a renamed proof of eta<h. No RH assumption, prime-density replacement of signed coefficients, hidden random signs, untruncated lower-bound shortcut, simultaneous infinite-iteration constant or finite-to-infinite inference occurs. Neither coefficient-generic model is a genuine u counterexample.

### I. Conceptual Interpretation

Increasing the deleted prime range does not simply strengthen the fixed-prime mechanism. At a polynomial cutoff the positive inverse creates a new linear-sized population, including a large unit-quotient layer. The real arithmetic cancels that layer only after all other quotients return. An argument that estimates those layers independently pays the full missing power before it reaches the original statistic.

A logarithmic cutoff avoids that fixed power tax, but this is a feasibility condition, not a cancellation theorem. Its main mathematical demand remains a new sign-sensitive estimate uniform for the frozen cutoff and all required inner scales.

### J. Competing Structural Hypotheses

1. Retain logarithmic deletion as a potentially compatible representation ONLY if a genuine two-parameter signed supplier is independently derived. Cost control alone is not an active RH mechanism.
2. Park quarter-power deletion followed by separate absolute envelope transfer as a strict-power supplier. Its positive inverse has the sharp 1-beta cost; its forward majorant also pays that power.
3. Preserve a jointly signed quarter-power approach. GD4 identifies mandatory cancellation but only at o(x) scale; it neither proves nor forbids an adequate remainder estimate.
4. Do not replace the frozen inner cutoff by its scale-dependent diagonal. The exact x=625 control rules out that identity.
5. Preserve FINITE-AC, CORR4 and MU-LIFT route memory and all other independent toolkits. No new global consumer, source equivalence, route reclassification or policy change is proposed on the basis of this audit.

### K. Specialist Handoffs

**Coordinator:** SC's precise growing-deletion cost assignment is complete at paper/self-audit scope. Record GD.2/GD.5 and the frozen-cutoff failure. Logarithmic deletion is subpower-compatible, not an independently qualified supplier. Quarter-power scalar transfer is parked; the genuine coarse cancellation is supporting structure, not a half-continuation. Do not launch a larger scan of the same cost.

**Adversarial Referee:** independently check the direction of GD.10, uniform sigma>=15/32 and 5^15>2^32, the omitted-2/3 factor 1/3, h_y<=h domination, fixed-lambda smooth limit, beta<1 endpoint, and the frozen-y source. Check the model/genuine split and every term in GD.9. The strongest falsifier is an overlooked d>x tail or a changed inner cutoff, not a numerical failure to approach an asymptotic at small x.

**Analytic Type II:** the potentially useful task is an original-sign correlation beyond the first-order smooth-density cancellation, with a frozen two-parameter source. Any estimate stated only on T_(y(t))(t) needs its exact off-diagonal-in-parameter return. The positive inverse's floor-envelope norm is sharp; do not transfer EF's additive pulse or a Hecke moment to u without a map. No new sufficient magnitude estimate is supplied here.

**Owner Payment:** GD4 is not a donor allocation or actual-prime first-bad payment. Its inverse multiplicities are formal convolution weights, not independently reusable historical seats. FB's original compressed anchor/minority constraint remains separate, with its post-cancellation target-equivalent residual unpaid.

**Prime Census:** no range extension requested. A useful independent check is the local positive convolution and exact frozen/adaptive distinction at x=625, or a new genuinely signed proposed inequality with a declared smallest falsifier. The asymptotic proof is not validated by plotting a larger inverse mass.

**Lean Verification:** NO_NEW_ENDPOINT_THEOREM_TO_FORMALIZE and no immediate PR request. GD is unreviewed paper work. Local convolution infrastructure is already TP/FR mathematics; only formalize a genuinely necessary new theorem after acceptance and a named qualifying supplier needs it. Do not encode the desired frozen-cutoff saving or eta<h as a hidden premise.

These are asynchronous report handoffs, not agent launches or promises of background work.

### L. First Independently Missing Theorem

No independently weaker sufficient arithmetic supplier was discovered. The precise unpaid step is a genuine sign-sensitive improvement of the complete original S/row source, or a different complete source with its own terminal. Within logarithmic deletion, an adequate all-inner-prefix frozen-y bound would transmit a gain, but this execution has no independent argument for it. Merely asserting that bound is not progress beyond the target specification.

Within polynomial deletion the leading inverse-density cancellation is now paid at o(x); it gives no required power rate and is not the original-source bound. Subtracting its scalar mean and naming the remaining convolution a new remainder does not prove it smaller. Future work must identify arithmetic information controlling that complete weighted discrepancy before renewing this path.

### M. Continuity, Evidence And Next-Run Resume

The untruncated agent-reports tree at 340d4615ce36a377756b5bc5837f5cf0bc0cdbb5 was enumerated without a calendar-day cap. Every role's latest actual report was retrieved. The own latest TP receipt is the consumed watermark; relevant later publications were consumed in order MC, CF, CR, SC, FB, EF. Earlier accepted FR/FP/TP and relevant original derivations were recovered, rather than inferred from a SHA. Complete Coordinator 00/90 content was fetched and compared byte-for-byte.

CONTINUITY_COMPLETE here means latest-real discovery plus task-relevant backfill, not an independent review or complete reread of every historical appendix. Latest publications are complete, not partial-only. November 17 Coordinator/Census/Referee/Lean have TODAY=PENDING / NO_VERIFIED_REPORT at intake; their November 16 reports are YESTERDAY=CARRY_FORWARD. Owner and Analytic have actual completed November 17 reports. Own prior completed report is November 16 TP. No silent day is counted as an execution.

| Role | Latest verified path under research/agent_reports/; blob | Actual verified receipt, EST; consumed change; resume |
| --- | --- | --- |
| Coordinator 00/90 | 2026-11-16/00-coordinator-am.md and identical 90; fda92549dd9291c491005fdf70847b90d9be385a | SC, Nov16 23:34:49; HB -> SC; growing inverse cost assignment and source-faithful portfolio. |
| Owner | 2026-11-17/10-owner-payment.md; 90463617e54793a00a8ca7af44e589d5a81ccbab | FB substantive Nov17 00:25:10; DB -> FB; minority saturation, payment-equivalent residual; new paper results pending review. |
| Analytic | 2026-11-17/20-analytic-type-ii.md; 85754c6ad366d5457bbabd6dd41a7214a99a812d | EF substantive Nov17 01:29:31; LM -> EF; scalar-energy floor transfer has a polynomial cost, not a source gain. |
| Wheel | 2026-11-16/30-finite-wheel.md; 713826840694e39a141fbdbe813f1d47245928e7 | TP, Nov16 18:28:09; prior own watermark; TP1-TP4 now ACCEPT_ON_PAPER by CF at stated model scopes. |
| Census | 2026-11-16/40-prime-census.md; 53e6be517dc11037fe3b42a8ed6ad3a06cfce956 | MC, Nov16 19:16:22; SG -> MC; H19/H20 finite signs, MC3 accepted at finite-depth range; no magnitude supplier. |
| Referee | 2026-11-16/50-adversarial-referee.md; 240b97ce1c8ddc87d5f520bc9a8cd6ea00df3d32 | CF, Nov16 20:34:29; FR -> CF; TP/HB/LM scoped verdicts, critical-frequency constraints. |
| Lean | 2026-11-16/60-lean-verification.md; 0bada0352d54be7c46a7d928f4c4e3bee440ad8f | CR, Nov16 21:24:23; FR-AUDIT -> CR; CF1-CF4 ACCEPT_ON_PAPER; CR1 accepted at model scope by SC; no missing accepted source supplier. |

Yesterday Owner DB (a52b439e693e069502b0c299a5f074a19bae0807) and Analytic LM (84aaa2103225565607b5b033f273462bbe865246) were separately retrieved and task-relevant findings read. DB's R=5 correction and R=137 restoration counterexample, FR's R=139 no-pointwise-row result, TP's x=35/49 omitted terms and x=245 genuine same signs, MC's limited two-head signs, and EF/FB's different-carrier restrictions remain intact. No whole-paper acceptance is inferred from a narrower review.

The external inbox 7d63d434690d00dffce9c90335d41c4f62d85798 was read; no entry is later than October 18. EXT-20261018-PNT-1 retains its cofactor-weighted prime error and strict root endpoints; EXT-20261014-5 concerns unconditional all-R strict fractions, not a conditional first-bad refutation. No newly unconsumed external supplier was found.

```text
RUN=20261117-wheel-0205-EST/GD; PLATFORM_RUN_ID=UNAVAILABLE
MAIN=4d5482805bac6a8f29d4fb4dadc61eca0bc06525
half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1
cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1
continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1
ROUTE=FINITE-AC bounded growing-deletion feasibility audit
ORIGINAL=ordered Q_R/C_R(6), strict K_R; accepted FR bridge to genuine u_6
START=G(b_base), b_base=7/8-7/(64*N_pack); fixed 7/8 used only where declared
CONTINUATION=closed-boundary eta(h)<h => contradiction at Theta=1/2+h
VALID_RANGE=all x>=1 for exact identities; fixed 1/2<=beta<1 for costs
RENEWAL=consumer already exists; no new strict arithmetic cost supplied
RETURNS=frozen y, unit, every prime power, J, both orientations, all cross terms
NEW=literal log/quarter costs; sharp inverse norm; genuine coarse unit cancellation
FALSIFIER=x625 adaptive cutoff gives -210 instead of -223
STATUS=ACTIVE_SUPPORT completed; quarter-power absolute supplier PARKED
MATHEMATICS=PAPER_PROOF/SELF_AUDIT/INDEPENDENT_REVIEW_PENDING/NOT_FORMALIZED
FINITE=39618 exact/rational checks PASS; no asymptotic inference
NO_NEW_GLOBAL_GAIN; VERIFIED_ETA=NONE; RH=OPEN
FIRST_OPEN=genuine strict signed complete-source estimate, not its restatement
NEXT=independent GD review; no repeated unchanged scan or generic inverse wrapper
PUBLICATION=READBACK_PENDING until verified receipt
```

The early checkpoint commit 811d4bdd03847bb187292f25a34b9af52344b65f, blob fee9a2a8f9fba0a63e1d116d9a931073f8805136, was read at its immutable commit and matched exactly before the computation. Direct git transport failed with CONNECT tunnel 403; authenticated connector reads and authorized own-report writes worked. A primary de Bruijn PDF exceeded the web reader's size limit; the needed classical theorem was verified in the accessible Hildebrand-Tenenbaum research paper instead. No unavailable claim is used as evidence.

Only this owned dated report is written remotely. No Lean/source/main/policy/other-role report, proof branch, PR, issue, workflow, schedule, permission or agent configuration is changed. No other agent was launched. The report, checker and proof are self-audited; independent review remains genuinely pending.

### Reproducibility Appendix

The complete executed standard-library checker follows. Its SHA-256 is 5cc80c19e5fabd640ad29946253fc09177fc7546ffcff56bf6df9d9996270583. The exact genuine source-array SHA-256 is 17ae400848b7f54e3aacf857cf1e48ea9660304b767a297068667c628c9e29e7. The following finite evidence does not certify any infinite assertion or Lean theorem.

```python
"""Exact finite checks for the growing-deletion cost audit, not a limit proof."""

import hashlib
import json
from collections import Counter
from fractions import Fraction
from math import isqrt


LIMIT = 65536
DENSE = 2048
CUTOFFS = [4, 5, 7, 11, 13]
SCALES = [64, 624, 625, 626, 2400, 2401, 2402, 14640, 14641,
          14642, 28560, 28561, 28562, 65536]
checks = Counter()


def check(label, truth):
    checks[label] += 1
    assert truth, (label, checks[label])


def trial(n):
    out = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            out.append((p, e))
        p += 1
    if n > 1:
        out.append((n, 1))
    return out


spf = list(range(LIMIT + 1))
for p in range(2, isqrt(LIMIT) + 1):
    if spf[p] == p:
        for n in range(p * p, LIMIT + 1, p):
            if spf[n] == n:
                spf[n] = p

factorizations = [[], []]
for n in range(2, LIMIT + 1):
    p, m, e = spf[n], n, 0
    while m % p == 0:
        m //= p
        e += 1
    factorizations.append([(p, e)] + factorizations[m])

u = [0] + [(-1) ** sum(p > 3 for p, e in factorizations[n])
           for n in range(1, LIMIT + 1)]
S = [0]
for n in range(1, LIMIT + 1):
    S.append(S[-1] + u[n])
for n in range(1, DENSE + 1):
    check('independent_factorization', trial(n) == factorizations[n])


def arrays(y):
    k = [0] * (LIMIT + 1)
    b = [0] * (LIMIT + 1)
    c = [0] * (LIMIT + 1)
    h = [0] * (LIMIT + 1)
    T, B, C = [0], [0], [0]
    for n in range(1, LIMIT + 1):
        fs = factorizations[n]
        smooth = all(5 <= p <= y for p, e in fs)
        c[n] = int(smooth)
        if smooth:
            k[n] = (-1) ** len(fs)
            b[n] = 2 ** sum(e - 1 for p, e in fs)
            if all(e >= 2 for p, e in fs):
                h[n] = 2 ** sum(e - 2 for p, e in fs)
        T.append(T[-1] + (u[n] if all(p < 5 or p > y for p, e in fs) else 0))
        B.append(B[-1] + b[n])
        C.append(C[-1] + c[n])
    return k, b, c, h, T, B, C


tables = {y: arrays(y) for y in CUTOFFS}


def convolution(a, b, limit):
    result = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for m in range(1, limit // d + 1):
            result[d * m] += a[d] * b[m]
    return result


def kernel_sum(a, prefix, x):
    return sum(a[d] * prefix[x // d] for d in range(1, x + 1))


for y, (k, b, c, h, T, B, C) in tables.items():
    inverse = convolution(k, b, DENSE)
    positive = convolution(c, h, DENSE)
    for n in range(1, DENSE + 1):
        check('local_inverse', inverse[n] == int(n == 1))
        check('positive_convolution', positive[n] == b[n])
        check('powerful_support', not h[n] or all(e >= 2 for p, e in trial(n)))
    for x in range(257):
        check('literal_inverse', kernel_sum(b, S, x) == T[x])
        check('literal_forward', kernel_sum(k, T, x) == S[x])
        grouped = sum((B[x // m] - B[x // (m + 1)]) * S[m]
                      for m in range(1, x + 1))
        check('quotient_groups', grouped == T[x])
        unit = B[x] - B[x // 2]
        check('unit_return', kernel_sum(b, S, x) - unit
              == sum(b[d] * S[x // d] for d in range(1, x // 2 + 1)))


def log_interval(n, terms=48):
    def series(q):
        z = (q - 1) / (q + 1)
        value = 2 * sum((z ** (2 * j + 1) / (2 * j + 1)
                         for j in range(terms)), Fraction())
        error = 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
        return value, value + error
    e = n.bit_length() - 1
    a, b = series(Fraction(n, 2 ** e))
    c, d = series(Fraction(2))
    return a + e * c, b + e * d


def fourth_root(n):
    r = isqrt(isqrt(n))
    check('fourth_root_exact', r ** 4 <= n < (r + 1) ** 4)
    return r


def effective_cutoff(y):
    return max([4] + [p for p in (5, 7, 11, 13) if p <= y])


def mass_interval(b, x, numerator, denominator, scale=10 ** 12):
    lo = 0
    hi = 0
    for d in range(1, x + 1):
        if not b[d]:
            continue
        q = scale ** denominator // d ** numerator
        r = isqrt(q) if denominator == 2 else isqrt(isqrt(q))
        check('weight_interval', r ** denominator * d ** numerator <= scale ** denominator
              < (r + 1) ** denominator * d ** numerator)
        lo += b[d] * r
        hi += b[d] * (r + 1)
    return [str(lo), str(hi), str(scale)]


rows = []
for x in SCALES:
    low, high = log_interval(x)
    log_y = low.numerator // low.denominator
    check('log_cutoff_certified', log_y == high.numerator // high.denominator)
    for regime, y in [('log', log_y), ('quarter', fourth_root(x))]:
        key = effective_cutoff(y)
        k, b, c, h, T, B, C = tables[key]
        check('large_inverse', kernel_sum(b, S, x) == T[x])
        check('large_forward', kernel_sum(k, T, x) == S[x])
        unit = B[x] - B[x // 2]
        remainder = sum(b[d] * S[x // d] for d in range(1, x // 2 + 1))
        check('large_unit_return', unit + remainder == T[x])
        F = [0] + [2 * ((m + isqrt(m)) // 2) - m for m in range(1, x + 1)]
        check('model_nonnegative', all(v >= 0 for v in F))
        check('model_unit_sign', all(abs(F[m] - F[m - 1]) == 1 for m in range(1, x + 1)))
        model = kernel_sum(b, F, x)
        check('floor_faithful_model', model >= unit)
        rows.append({'x': x, 'regime': regime, 'floor_y': y,
                     'B': B[x], 'smooth_count': C[x], 'S': S[x], 'T': T[x],
                     'unit': unit, 'signed_return': remainder,
                     'positive_model': model,
                     'mass_half_interval': mass_interval(b, x, 1, 2),
                     'mass_three_quarters_interval': mass_interval(b, x, 3, 4)})

k5, b5, c5, h5, T5, B5, C5 = tables[5]
check('negative_omit_prime_powers', b5[25] == 2 and c5[25] == 1)
check('negative_alternating_powers', k5[25] == -1)
check('negative_wrong_endpoint', B5[25] - B5[24] == 2)
check('negative_small_primes', b5[2] == b5[3] == 0 and u[2] == u[3] == 1)
adaptive = sum(k5[d] * tables[effective_cutoff(fourth_root(625 // d))][4][625 // d]
               for d in range(1, 626) if k5[d])
check('negative_adaptive_cutoff', adaptive != S[625])
boundary = []
for p in (5, 7, 11, 13):
    x = p ** 4
    before = tables[effective_cutoff(p - 1)][4][x]
    after = tables[p][4][x]
    check('prime_cutoff_changes_source', before != after)
    boundary.append({'p': p, 'x': x, 'old_mask_at_x': before, 'new_mask_at_x': after})

payload = {'status': 'PASS', 'limit': LIMIT, 'dense_coefficient_limit': DENSE,
           'checks': dict(sorted(checks.items())), 'total_checks': sum(checks.values()),
           'rows': rows, 'cutoff_boundary': boundary,
           'adaptive_counterexample': {'x': 625, 'actual_S': S[625], 'incorrect': adaptive},
           'source_array_sha256': hashlib.sha256(json.dumps(u, separators=(',', ':')).encode()).hexdigest(),
           'scope': 'Finite exact regressions and rational enclosures only; no asymptotic or Lean proof.'}
print(json.dumps(payload, indent=2))
```

### Compact Exact Output

```json
{
  "status": "PASS",
  "limit": 65536,
  "dense_coefficient_limit": 2048,
  "checks": {
    "floor_faithful_model": 28,
    "fourth_root_exact": 19,
    "independent_factorization": 2048,
    "large_forward": 28,
    "large_inverse": 28,
    "large_unit_return": 28,
    "literal_forward": 1285,
    "literal_inverse": 1285,
    "local_inverse": 10240,
    "log_cutoff_certified": 14,
    "model_nonnegative": 28,
    "model_unit_sign": 28,
    "negative_adaptive_cutoff": 1,
    "negative_alternating_powers": 1,
    "negative_omit_prime_powers": 1,
    "negative_small_primes": 1,
    "negative_wrong_endpoint": 1,
    "positive_convolution": 10240,
    "powerful_support": 10240,
    "prime_cutoff_changes_source": 4,
    "quotient_groups": 1285,
    "unit_return": 1285,
    "weight_interval": 1500
  },
  "total_checks": 39618,
  "cutoff_boundary": [
    {
      "p": 5,
      "x": 625,
      "old_mask_at_x": -223,
      "new_mask_at_x": -268
    },
    {
      "p": 7,
      "x": 2401,
      "old_mask_at_x": -691,
      "new_mask_at_x": -842
    },
    {
      "p": 11,
      "x": 14641,
      "old_mask_at_x": -2606,
      "new_mask_at_x": -3199
    },
    {
      "p": 13,
      "x": 28561,
      "old_mask_at_x": -4724,
      "new_mask_at_x": -5660
    }
  ],
  "adaptive_counterexample": {
    "x": 625,
    "actual_S": -223,
    "incorrect": -210
  },
  "source_array_sha256": "17ae400848b7f54e3aacf857cf1e48ea9660304b767a297068667c628c9e29e7",
  "scope": "Finite exact regressions and rational enclosures only; no asymptotic or Lean proof."
}
```


### Immutable Source Ledger

Every main file below was fetched at 4d5482805bac6a8f29d4fb4dadc61eca0bc06525. Original proof status remains distinct from the new paper derivation.

| Path | Blob SHA |
| --- | --- |
| AGENTS.md | c4f36b772f8a4b0c24fe566b90fafb646073c60f |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_BOOTSTRAP_TO_HALF_20261116.md | 96ad4439ec458af6168f7d9cb3eef5dde291d37c |
| docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md | e3ae4280438f591f1ffaddd754a1c3a6d35d0691 |
| docs/RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md | 3e71820a4af722eae7098da6945bb5bcba50dd0d |
| docs/DYNAMIC_RESEARCH_AGENTS.md | b76d595f09403fc54eca71d04bf9e0306e0a9c09 |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| research/EULER_HYBRID_ABEL_GRAM_20261027.lean | 2a94dd8fd56fc03e95f732fb44b778a8d4f83e26 |
| research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| research/EULER_FIXED_GCD_ROW_OBSTRUCTION.lean | 9003eb1c226f0b114be6402e63f325b60c80bf92 |
| RHLean/Proof/SquareRootAmplificationLogGrowth.lean | 2599db31079f388229d072ee616957fba6ffc555 |
| RHLean/Proof/AmplificationExponentIteration.lean | d78be4509e5dcc35b833c3786258b94fc6e71915 |
| research/MERTENS_CONVERSE_IDENTIFICATION.lean | 768c8255850bf4074aff265c3fe17a1f5c43979b |
| research/half_bootstrap_20261116/native_renewal.md | 18b00148e405be3115b5ebb2066e9e67c417b563 |
| research/oai_434/VF919WindowErrorClosure.lean | f629db1b2b65d6ec042ac9432397d4b6316200c6 |
| scripts/lean/window_error_closure/WindowErrorClosureAudit.lean | 1f17f9401a63d16227db2e2aad020b9f74bc5f4e |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| research/EXACT_LI_DICKMAN_ATTACK.md | 2811de980aaf38703d2c822d58b5dd10a6e4bd2b |
| RHLean/Arithmetic/PrimeWheelPartialError.lean | 5e63ade78dd534cc4d29e30d2640bd88b966650b |
| research/HECKE_SPLIT_PRIME_CUTOFF_TRADEOFF_20261016.md | e32cdf37f62a79dd68806a1b3cb1d960234f3a47 |
| docs/PROOF_DEPENDENCY_DAG.md | 342025ac7be37ae148f4c9826923150ad3930328 |
| docs/COORDINATE_ATLAS.md | cd0419d00a37739fe5a292f5cb738e33213949d5 |


### Prepublication Validation

Verified 2026-11-17 07:31:13 UTC (America/New_York date 2026-11-17). Main remains 4d5482805bac6a8f29d4fb4dadc61eca0bc06525; the complete open/draft PR collection remains empty. Compared with intake, the only reporting-tree change is this run's own preserved checkpoint at 811d4bdd03847bb187292f25a34b9af52344b65f. No newly published upstream section was left unconsumed. The current owned blob was fetched immediately before the write and matches the checkpoint byte-for-byte. Final self-audit checked theorem hypotheses, endpoints, signs, multiplicities, source/restoration scope, Markdown/code fences, citation, embedded reproduction source and exact output. All 39,618 finite assertions pass; asymptotic claims remain PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. No local Lean or new CI was run. Publication is verified only by the immutable readback receipt appended after the substantive commit.


### Verified Publication And Resume Receipt

Publication verification at 2026-11-17 07:31:57 UTC. Substantive synthesis committed at 2026-11-17T07:31:28Z (02:31:28 EST) in [5a86d22e26c08bfee995810847119427425ca2b2](https://github.com/OVVO-Financial/RH_Lean/commit/5a86d22e26c08bfee995810847119427425ca2b2). Immutable readback matched all 54246 ASCII characters exactly; blob=9c1e7a84a9f3396c73fbd1737c6b483337a57f5a. The commit changes ONLY this owned daily report, with 763 additions and zero deletions. The early checkpoint is preserved. No source, policy, other report, PR, issue, workflow, branch or schedule was changed.

RUN_STATUS=COMPLETE; PUBLICATION=VERIFIED; RESEARCH_REVIEW=SELF_AUDIT_ONLY; INDEPENDENT_REVIEW=PENDING; FORMALIZATION=NONE; VERIFIED_ETA=NONE; RH=OPEN. Resume from GD1-GD5 and the full proofs above, not the superseded checkpoint's pending items. Do not repeat this cost census without a new hypothesis or an independent review requirement. The next substantive research step needs genuine signed information beyond GD4's first-order cancellation; merely assuming a frozen-cutoff improvement is target repackaging. Latest upstream consumption remains SC/FB/EF/TP/MC/CF/CR at the ledger SHAs. Await actual new reports, not presumed scheduled execution.


## In-Progress Checkpoint - 20261117-wheel-1012-EST/SB

### A. Structural Question

IN_PROGRESS / PARTIAL. Resume Coordinator INV's small-prefix boundary assignment on the genuine u_6 prime-deletion source. No new result is claimed at this checkpoint. Investigate the complete forward sum with frozen y=log x and isolate all d with floor(x/d)<=floor(2y), retaining k_y(p^e)=-1 for EVERY e>=1. Test whether paying this boundary suffices to make a uniform remaining-prefix saving plausible.

### B. Authority And Continuity

Actual scheduled trigger: 2026-11-17 10:12:01 EST; platform RUN_ID_UNAVAILABLE. Verified at 2026-11-17 15:15:39 UTC. Main=319fc5798658e66baea1fed758b0d4b6dd126889; AGENTS=c4f36b772f8a4b0c24fe566b90fafb646073c60f; contract=95566e37c8eaeb99ee680660df4f9d2e06ea5038; half policy=96ad4439ec458af6168f7d9cb3eef5dde291d37c. Reporting intake=89b9961c9f146cabf3ff5b8de87f8e8b3e4de9ae. Complete trees were enumerated without a calendar cap. Latest actual roles are INV, HF, HA, own GD, DJ, SG and NYMAN-JUMP; all current and preceding-day role files retrieved. Relevant sections and original-source verification are being completed; hashes alone are not credited as reading.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1. External inbox=7d63d434690d00dffce9c90335d41c4f62d85798, unchanged. Today's reports exist for all roles. The canonical VF bound, finite-AC arithmetic estimate and RH remain OPEN. Main includes merged #1140 and #1141; open #1142 and stacked #1143 are not main authority. Their verification status will be refreshed before the final report. No local Lean or new CI is authorized or claimed.

### C. Registered Investigation And Continuation

Reuse TP/GD's exact signed restoration S(x)=sum_(d<=x)k_y(d)T_y(floor(x/d)), with d supported on primes 5<=p<=y, and accepted FR's all-scale same-power bridge between S and M above 1/2. Attempt an elementary bound for the support of the short-prefix boundary, independent of any desired cancellation. Then test the smallest deeper one-large-prime range rather than silently extend INV.10 or assume its removal pays the full source.

Potential consumer: an independently supplied strict all-scale S bound below a fixed input Mertens exponent transfers through FR; a renewal at each actual gap, or the existing finite-AC closed-boundary consumer with genuinely proved eta(h)<h, is still required for 1/2. All strict radical masks, unit/history/powerful terms, ordered rows and quadratic cross terms remain. This is a bounded feasibility audit, not a new RH route.

### D-M. Pending Work

PENDING: complete proof, independent boundary falsification, source/novelty audit, exact finite regression and final synthesis. Intended finite checks use small predetermined x,y and exact integer arithmetic, including prime powers, strict thresholds and a wrong moving-cutoff negative control. No finite check will certify an asymptotic. Only this owned report may be changed remotely.


## The Small-Prefix Boundary Is Paid; The Remaining Pure-Power Supplier Is False

### Final Research Synthesis - 20261117-wheel-1012-EST/SB

Actual scheduled trigger: 2026-11-17 10:12:01 EST / 15:12:01 UTC, America/New_York. PLATFORM_RUN_ID=UNAVAILABLE. SB is a research label. The earlier GD report and this invocation's checkpoint remain unchanged. Preparation status is READBACK_PENDING until the appended publication receipt.

### A. Most Important Structural Discovery

**All short inner prefixes in logarithmic prime deletion have a subpower TOTAL return, without assuming cancellation.** With the genuine u_6 source, frozen y=log x and L=floor(2y), the complete boundary B_L(x) obeys, for every epsilon>0,

~~~text
|B_L(x)| <= C_epsilon x^epsilon,
|S(x)^2 - U_L(x)^2| <= D_epsilon x^(1+epsilon),
S(x)=B_L(x)+U_L(x).
~~~

The second assertion retains the full boundary/middle cross term. Consequently this boundary is negligible at every amplitude power beta>1/2 and corresponding squared power 2beta. It does not require prime distribution, RH, a model population, or the previous GD inverse-mass asymptotic.

**Deleting that boundary does not make a constant-uniform inner power bound true.** There is a genuine, source-admitted infinite family

~~~text
x_k=5^k*k^2, d_k=5^k, y_k=log x_k, t_k=floor(x_k/d_k)=k^2,
t_k>2y_k, k_yk(d_k)=-1,
T_yk(t_k) ~ -3k^2/(2 log k).
~~~

Thus for every gamma<1 and fixed A, the assertion |T_log x(floor(x/d))|<=A*floor(x/d)^gamma at EVERY active quotient beyond 2log x is false. This is not a synthetic coefficient example. These counterterms are themselves subpower in x_k, so they do NOT disprove logarithmic deletion or a correctly outer-loss-weighted bound.

Finally the repaired, outer-loss-weighted large-prefix condition is proved equivalent to the original every-positive-loss growth statement, not a weaker independently paid supplier. This closes Coordinator INV's bounded boundary assignment. No strict arithmetic gain was obtained.

| Stable Claim | Classification And Scope |
| --- | --- |
| 20261117-wheel-1012-EST/SB1 | PAPER_PROOF / SELF_AUDIT: literal boundary bill, logarithmic-cutoff subpower bound, full quadratic return. Elementary Rankin counting is established methodology, not a claimed new classical theorem. |
| SB2 | PAPER_PROOF / SELF_AUDIT: complete one-large-prime classification, its weighted PNT asymptotic, and genuine source-admitted post-boundary counterfamily. |
| SB3 | PAPER_PROOF / SELF_AUDIT / TARGET_EQUIVALENCE_AUDIT: corrected uniformity range is equivalent to every-loss S/M growth at the stated exponent. No premise is proved merely by proving the equivalence. |
| SB4 | FINITE_COMPUTATION: 951,822 exact/rational assertions passed, including strict endpoints, original occurrences, prime powers, cross terms and moving-cutoff controls. No asymptotic inference. |

New SB results are INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_RH_ROUTE; VERIFIED_ETA=NONE; RH=OPEN.

### B. Current Authoritative Objective

Final authority is main [fd4085e20602bc210cc6b630abbdeeeaf1bf28eb](https://github.com/OVVO-Financial/RH_Lean/commit/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb), advanced from intake 319fc5798658e66baea1fed758b0d4b6dd126889 by human merge #1142 at 15:37:26 UTC. AGENTS=c4f36b772f8a4b0c24fe566b90fafb646073c60f; CURRENT_PROOF_CONTRACT=95566e37c8eaeb99ee680660df4f9d2e06ea5038; continuation policy=96ad4439ec458af6168f7d9cb3eef5dde291d37c. AGENTS and the contract were fetched again at the new head and are byte-identical. The newer half-continuation priority overrides older task-selection banners only.

~~~text
half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1
cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1
continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1
high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1
chain_ack=CANCELLATION_CHAIN_REUSE_V1
~~~

The canonical VFCanonicalSquareVonKochStatement remains OPEN: ONE C>=0 before every integer R>=2, |pi(R^2)-vfCanonical(R^2)|<=C R log R, with vfCanonical=vfMid+sqrt(2). Its source-read terminal still takes ClassicalVonKochRHCriterion explicitly. Native Mertens/finite-AC consumers are distinct.

The strongest reused compiled Mertens baseline is native_mertens_near_uniform_window_error_closed: every-positive-loss growth at b_base=7/8-7/(64*N_pack), with the fixed nearUniformSlotCount. Spending that positive margin permits a fixed 7/8 power. No zero-loss bound at b_base, comparison with an unrelated N_*, or newly proved analytic chain is claimed. The separately reported stronger IR/FFR paper comparison remains paper evidence, not a completed physical Lean return.

The terminal source and its exact dependency-audit program were read. At #1119 tested head 77ee815846d6d534c866f0752aa33b84c385610a, all 14 checks are successful; the actual [five-root log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700) reports closures 35358,35375,35736,35737,35753 and only propext, Classical.choice, Quot.sound. The audit checks live source construction, complete comparison and native transfer. A fresh nontruncated comparison of 2,508 preexisting Lean/pin/scripts/lean files with main finds only RHLean.lean's aggregate imports changed. This is scoped reuse, not a new build. Pins observed include Lean 4.34.1 / 5045d0056413266e57c625dcd7c365b10e377c52, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and openai/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a.

Recent source changes were not treated as report-only evidence. #1140 and #1141 are human-merged. #1141 head dfd3197117410ad491d7c94b66448753ae8e4d63 has 17 successful checks and three superseded cancelled checks. The actual [owner audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44099085547/job/134093953266) and [Euler audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44099085547/job/134093952768) verify 20 and 27 public declarations with standard axioms and original dependencies; these jobs reused pinned cached closures, not fresh local builds. Their source definitions and terminal hypotheses were inspected. The owner capacity is paid, and the complete Xi/divisor decomposition is exact; their signed compensation bounds remain unpaid. They do not bound T_y here.

The initial refresh found #1142 and stacked #1143 open, with respectively 7/7 and 13/13 successful checks. During final publication review, #1142 was human-merged into main at 15:37:26 UTC. Its exact three-file diff changes only the preservation source note, generated DAG and obligation registry; no Lean source or pin changes. The full new note was read: its graded owner/Xi targets remain target-equivalent supporting infrastructure, fixed constants differ from every-positive-loss bounds, and balanced hyperbolic interactions remain present. These session-reviewed deductions are not new Lean declarations or SB premises.

#1143 was then human-merged at 15:37:48 UTC, but INTO docs/preservation-target-strength-20261117, not main, with merge d1a5936939eda3c2d8cc74cc9082ecbf11249e18. Its tested head remains b02c724221a74eb0835e7a090c615c8cdbc808fc. The final main tree does not contain its new prime-phase files. Its inspected lifetime-survivor prime fibre uses a different moving square-root cutoff from this u_6 source and supplies no SB premise. The open/draft collection is now empty. This distinction was checked from the actual PR base and main tree, not inferred from the word merged. No local Lean, workflow launch, repair or rerun was performed.

### C. Structural Mechanism Investigated

Coordinator 20261117-coordinator-0710-EST/INV assigned the complete small-prefix bill, not another inverse-mass census. The key arithmetic fact is that the restoring divisors use only primes <=log x. There are subpower many such divisors below x, even after retaining ALL powers. This controls every short-prefix occurrence before using its sign.

The competing hypothesis was that INV.10's obstruction disappears after omitting t<=2y, allowing a pure t^gamma estimate on the rest. Unique factorization instead exposes the entire one-large-prime sector up to y^2. Its 2,3-smooth cofactor multiplicities survive and force a negative main term. Choosing a restoring prime POWER makes that obstruction occur at a literal quotient of the original forward sum.

This is a bounded FINITE-AC feasibility audit with an exact same-growth bridge to Mertens. It is not a new finite-wheel density route, a signed-prime independence assumption, or an artificial alteration of the complete source.

### D. Exact Theorem Statements

For positive integers n define u(n)=(-1)^(number of distinct prime divisors of n exceeding 3), u(1)=1. Let S(t)=sum_(1<=n<=floor(t))u(n), with S(t)=0 for t<1. For real y>=3 put

~~~text
P_y={prime p:5<=p<=y},
D_y={d>=1: every prime divisor of d is in P_y},
k_y(d)=(-1)^omega(d) for d in D_y, and 0 otherwise,
T_y(t)=sum_(n<=floor(t), no p in P_y divides n)u(n),
N_y(x)=#{d in D_y:d<=x}.
~~~

The unit belongs to D_y; k_y(p^e)=-1 for EVERY positive e, not (-1)^e. All cutoffs stay frozen within an outer sum. For integer x>=1 and integer L>=0 define

~~~text
B_L(x;y)=sum_(d in D_y,d<=x,(L+1)d>x) k_y(d)T_y(floor(x/d)),
U_L(x;y)=sum_(d in D_y,d<=x,(L+1)d<=x) k_y(d)T_y(floor(x/d)).
~~~

The strict condition is exactly floor(x/d)<=L. TP's exact forward identity gives S=B_L+U_L with once-only occurrences; it is reused, not claimed as new.

**SB1.** For every fixed 0<sigma<1, every x>=1 and y>=3,

~~~text
N_y(x) <= x^sigma exp(C_sigma(1+y^(1-sigma))),
C_sigma=1/((1-sigma)(1-5^(-sigma))),
|B_L(x;y)| <= L N_y(x).
~~~

Hence N_log x(x)=x^o(1). For y=log x and L=floor(2log x), the bounds in A hold with constants preceding x. More generally, for every fixed delta>=0 and epsilon>0, uniformly over integer 0<=L<=x^delta,

~~~text
|B_L(x;log x)| <= C_(delta,epsilon) x^(delta+epsilon).
~~~

The asymptotic assertions concern x>=21; the finitely many smaller integer x can be absorbed after defining P_y in the same way.

**SB2.** Define A_6(t)=#{2^a3^b<=t:a,b>=0}. For EVERY real y>=3 and 1<=t<=y^2,

~~~text
T_y(t)=A_6(t)-sum_(m=2^a3^b<=t/y) [pi(t/m)-pi(y)].          (SB.1)
~~~

For any sequence y->infinity, t<=y^2 and log t/log y->a with 1<a<=2,

~~~text
T_y(t) ~ -3t/log t.                                      (SB.2)
~~~

The limit is not claimed uniformly as a tends to 1. For x_k=5^k*k^2, d_k=5^k and y_k=log x_k, every integer k>=7 has d_k in D_yk and 2y_k<t_k=k^2<y_k^2. Formula SB.2 yields the genuine post-boundary no-go in A. INV.10 at t=2y is independently recovered as the special exact identity A_6(2y)-pi(2y)+pi(y), with PNT asymptotic -y/log y.

**SB3.** Fix 1/2<=gamma<1 and 0<delta<gamma. Let G_S(gamma) mean

~~~text
forall epsilon>0 exists C_epsilon>=0 forall integer n>=1:
  |S(n)|<=C_epsilon n^(gamma+epsilon).
~~~

Let H_actual(gamma,delta) mean

~~~text
forall epsilon>0 exists A_epsilon>=0 forall integer x>=21
forall d in D_log x with d<=x:
  t=floor(x/d)>x^delta ==> |T_log x(t)|<=A_epsilon x^epsilon t^gamma.
~~~

Let H_all be the same bound for every integer x^delta<t<=x, whether or not realized by a restoring divisor. Then

~~~text
H_actual(gamma,delta) <=> G_S(gamma) <=> H_all(gamma,delta).
~~~

Through accepted FR's coefficientwise convolution bridge, these are equivalent to native MertensGrowthAtMost gamma. At gamma=1/2 the every-loss statement is RH-equivalent through the source-read mertens_half_iff_riemannHypothesis. This is NOT a fixed O(sqrt x) assertion and not a new proof of any condition.

### E. Mathematical Proof

#### E1. Every Occurrence And The Complete Boundary

Unique factorization writes each n uniquely as d*m, where d contains the full valuations at primes in P_y and m contains none. Since u(n)=k_y(d)u(m), summing n<=x gives TP's forward formula. Thus the boundary is the exact original population whose selected-prime part satisfies d>x/(L+1); it is not merely a superset of candidate occurrences. Prime powers, the unit and all signs are retained.

Every boundary summand has |T_y(floor(x/d))|<=floor(x/d)<=L, proving |B_L|<=L N_y(x). This triangle discards signs, but only on the designated small source.

For fixed sigma in (0,1), a finite-prime geometric product gives

~~~text
N_y(x)<=x^sigma sum_(d in D_y)d^(-sigma)
       =x^sigma product_(5<=p<=y)(1-p^(-sigma))^(-1).
~~~

Use -log(1-z)<=z/(1-z), p^(-sigma)<=5^(-sigma), and

~~~text
sum_(p<=y)p^(-sigma)<=sum_(n<=y)n^(-sigma)
                     <=1+y^(1-sigma)/(1-sigma).
~~~

This proves SB1 with the displayed C_sigma. At y=log x, y^(1-sigma)=o(log x). Given epsilon>0 choose a fixed sigma<min(epsilon,1) and then x sufficiently large. It follows that N_log x(x)<=x^epsilon eventually. No PNT or infinite smooth-count asymptotic is used. Multiplying by L proves both boundary assertions, including polylogarithmic L.

For L=floor(2log x), write B=B_L and U=U_L. Exactly

~~~text
S^2=U^2+B^2+2UB,
|S^2-U^2|=|2SB-B^2|<=2x|B|+|B|^2.
~~~

Here |S|<=x because u has unit magnitude. Spend smaller positive losses in the subpower bound to obtain O_epsilon(x^(1+epsilon)). For beta>1/2 choose epsilon<2beta-1; the quadratic correction is o(x^(2beta)). No cross term was omitted or assumed negative.

#### E2. Exact One-Large-Prime Geometry

An admitted n<=y^2 either has no prime divisor >3, or has a prime p>y. It cannot have a second such factor, even a repeated one, since their product exceeds y^2. Thus it is uniquely m*p with m=2^a3^b and p>y. Its sign is -1. All 2,3-smooth integers have sign +1. Counting those unique pairs proves SB.1, with pi(t/m)-pi(y) and the displayed m<=t/y boundary. Equality at m=t/y contributes zero; it must not be changed to an extra prime occurrence.

The only imported analytic fact is the classical unconditional PNT pi(v)~v/log v, also furnishing pi(v)<=C v/log v for v>=3. A primary proof reference is [Sutherland, MIT 18.785 Lecture 16, Theorem 16.15](https://math.mit.edu/classes/18.785/2025/LectureNotes16.pdf). No short-interval PNT, RH error term or independence estimate is imported.

A_6(t)<= (1+log t/log 2)(1+log t/log 3). Under SB2's limiting hypotheses, the subtraction pi(y)A_6(t/y) is O(y log y)=o(t/log t), and A_6(t)=o(t/log t). For each FIXED 2,3-smooth m,

~~~text
(log t/t) pi(t/m) -> 1/m.
~~~

The moving cofactor tail is controlled, not silently interchanged with a limit: for m<=t/y, log(t/m)>=log y, so

~~~text
(log t/t) sum_(m>M,m smooth23,m<=t/y)pi(t/m)
 <= C (log t/log y) sum_(m>M,m smooth23)1/m.
~~~

The right-hand tail tends to zero as M->infinity because the full sum is

~~~text
sum_(a,b>=0)2^(-a)3^(-b)=3.
~~~

Taking the finite-m limit and then M->infinity proves SB.2. This explicitly retains growing cofactor ranges and every multiplicity.

For the actual quotient family, y_k=k log 5+2log k. Since 1<log5<2 and 2log k<=k for k>=2, k<y_k<3k. For k>=7, k^2>6k>2y_k and k^2<y_k^2. Also y_k>=5, so d_k=5^k is admitted and k_yk(d_k)=-1. The integer quotient is exactly k^2. Finally log(k^2)/log y_k->2, hence T_yk(k^2)~-3k^2/(2log k). Dividing by (k^2)^gamma diverges in magnitude for every gamma<1. This proves the stated all-constant refutation, not merely failure of A=1.

These terms have size x_k^o(1) and positive restoring sign eventually, because k_yk(d_k)=-1. Their existence does not imply a large total S, forbid compensation with other d, or refute the corrected H_actual condition, whose threshold x^delta eventually excludes them.

#### E3. Corrected Uniformity And Both Directions

For fixed gamma in [1/2,1), the two finite-prime products are

~~~text
G_gamma(y)=sum_(d in D_y)d^(-gamma)
         =product_(p in P_y)(1-p^(-gamma))^(-1),
F_gamma(y)=sum_(d in D_y)b_y(d)d^(-gamma)
         =product_(p in P_y)(1-p^(-gamma))/(1-2p^(-gamma)),
b_y(p^e)=2^(e-1), e>=1.
~~~

TP supplies the exact inverse T_y(t)=sum_(d<=t)b_y(d)S(floor(t/d)), with b_y supported on D_y. Since 2*5^(-gamma)<1, both logarithms are O_gamma(1+y^(1-gamma)) by the same integer-series comparison. For F use log((1-z)/(1-2z))<=z/(1-2z). Therefore BOTH products at y=log x are x^o(1). This uses a simple bound; the GD sharp logarithmic asymptotic is not reproved or needed.

Assume H_actual and set L=floor(x^delta). The entire short part is O_eta(x^(delta+eta)) by SB1. On every remaining actual quotient,

~~~text
|U_L|<=A_eta x^eta sum_(d in D_y,d<=x)floor(x/d)^gamma
     <=A_eta x^(gamma+eta)G_gamma(log x).
~~~

Choose eta sufficiently smaller than the requested final epsilon, and use delta<gamma. This proves G_S(gamma), with every constant before x. The implication H_all=>H_actual is immediate.

Conversely assume G_S(gamma). For any integer 1<=t<=x and fixed eta>0, the exact inverse gives

~~~text
|T_log x(t)|<=C_eta t^(gamma+eta) F_gamma(log x)
            <=C_eta t^gamma x^eta F_gamma(log x).
~~~

Spend the product's subpower loss and choose 2eta<epsilon. This proves H_all, in fact for every t<=x. Small x are absorbed in a constant. It also explains why an OUTER x^epsilon allowance can coexist with SB2's genuine polylogarithmic counterfamily.

Accepted FR2 has u_6=mu*kappa_6 and mu=u_6*lambda_6 with absolutely summable weighted coefficients at every fixed power >1/2. Applying these finite convolution identities with smaller positive losses gives G_S(gamma)<=>MertensGrowthAtMost gamma, including gamma=1/2. No fixed critical weighted inverse mass is asserted. The original row bridge remains

~~~text
C_R(6)=2J(R)-S(floor((R^2-1)/36)),
J(R)=sum_(m<=floor((R^2-1)/36),rad(36m)<R)u(m),
|J(R)|=O_epsilon(R^(1+epsilon)).
~~~

It is ACCEPT_ON_PAPER FR infrastructure, not newly Lean-certified by #1139. This execution does not drop J, identify C_R(6) with all Q_R, or assume a pointwise row domination.

### F. Structural Consequence

The complete source cannot accumulate a polynomial-amplitude obstruction from restoring divisors whose quotient is at most 2log x: the whole population is too small. The same argument pays ANY x^o(1) cutoff, and a cutoff x^delta costs at most x^(delta+o(1)). This is an all-scale statement, not a density extrapolation.

On the other hand the genuine y-rough residual has a coherent negative prime/cofactor sector throughout the one-large-prime range. The coefficient 3 comes from all 2,3-smooth cofactors, not from a prime-only approximation. Higher selected-prime powers place that sector inside the restoration source. The false supplier is therefore ruled out even on actual quotient sites, not only on an unnecessarily enlarged test population.

### G. Signed And Quantitative Relevance

| Coordinate / Step | Exact Transfer Or Barrier | Remaining Quantitative Cost |
| --- | --- | --- |
| Euler / FINITE-AC | Original eulerSelfDualBilinear is the complete ordered sum mu(a)mu(b)floor((R^2-1)/(ab)); its compiled endpoint is 2M(R-1)-M(R^2-1). S reaches M by accepted FR convolutions, not equality. | Strict-history K_R, both orientations, unit/history/powerful terms and all rows remain. SB does not prove eta(h)<h. |
| Square blocks | FR gives C_R(6)=2J-S(Y_R) with strict rad(36m)<R and all-prefix inverse. SB pays a portion of S with its full quadratic correction. | No source-omitting replacement of C_R(6) by Q_R; J and the other gcd rows are not paid by short-prefix counting. |
| VF / primes | SB.1 uses actual prime counts with ALL 2,3-smooth cofactors on a stated proper range. | It is not li-pi, clipped #915 source admission, or canonical VF payment. |
| NNS / OAI | Real signed squaring in SB1 preserves the complete cross term on its own source. | No norm isometry to ideal-labelled compensated OAI tuples, and no lower LOW bill or phase saving follows. |
| First signed loss | Triangle on B costs subpower; triangle on the remaining forward sum costs G_gamma(log x)=x^o(1). | No positive fixed power is won by either triangle. The unpaid input is a new genuine signed growth estimate. |
| Already-paid recovery tested | TP/FR/GD; #1141 owner capacity and Euler double centering; outside-prime CRT deletion and its unit-prefix no-go. | TP/FR are same-growth interfaces. #1141 leaves complete compensation/Xi open. CRT and lifetime survivor masks differ. None supplies H_actual at a smaller exponent. |

For a transparent possible continuation, define gamma(b)=1/2+(b-1/2)/2 and delta(b)=gamma(b)/2. An INDEPENDENT arithmetic derivation of G_M(b)=>H_actual(gamma(b),delta(b)) for every fixed 1/2<b<=7/8 would renew through SB3/FR and converge geometrically to 1/2. Constants may depend on the fixed stage and requested positive loss, never on the growing scale. Alternatively substitution at the actual closed Theta>1/2 would contradict its definition. No zero attaining Theta is required.

The implication just displayed is OPEN and, by SB3, has exactly the strength of the desired improved G_M(gamma(b)). It is included to expose the missing step, not as a new consumer to formalize or an independent supplier. SB1 pays the cutoff boundary; it does not supply the strict exponent. At gamma=1/2, H_actual is an RH-equivalent target, while a fixed finite-A constant remains a separate stronger sufficient criterion with no converse claimed.

### H. Falsification And No-Circularity Review

Registration preceded execution and is reproduced below. Checks use integers and exact Fractions; logarithms needed only to determine actual cutoff membership are bounded by the atanh series with its positive geometric remainder. No floating-point inequality or fitted exponent is credited.

The checker completed with PASS_EXACT and 951,822 assertions. Domains: x=1..512 for restoration/boundaries, with 257..512 held out; integer y=3..48 plus four half-integer cutoffs for the complete one-prime range; k=7..64 plus held-out 73,97,127 for literal source quotients. The many assertions are repeated checks inside these small domains, not a large-scale extrapolation.

| Check | Exact Count / Witness |
| --- | --- |
| Original occurrence map | 787,940 assertions; full valuations and unique n=d*m |
| Full restoration | 3,065 source cases |
| Boundary mask, reconstruction, bill, partition and square | 21,197 assertions EACH |
| One-large-prime identity | 38,343 prefixes; INV.10 additionally checked at 50 cutoffs |
| Admitted quotient family | 61 cases; five separate exact assertions each |
| Independent primality | 16,128 trial-factor versus sieve comparisons |
| Omitted cross term | Detected in 9,779 cases |
| Wrong x/L boundary | Detected in 6,123 cases |
| Omitted selected-prime powers | Detected in 2,316 cases |
| Omitted 2,3 cofactor multiplicities | Detected in 35,725 cases |
| Wrong adaptive inner cutoff | New log-scheduled witness x=149: true S=-69, wrong sum=-63 |
| Extending SB.1 past its range | y=5,t=49 detects the missing 7^2 occurrence |

Representative genuine T values: k=16 gives y floor 31, t=256, T=-56; k=64 gives y floor 111, t=4096, T=-1415; held-out k=127 gives y floor 214, t=16129, T=-5390. At k=7, T=3: the proof correctly claims an eventual asymptotic, not a negative sign at every finite k. Full S(x_k) was not numerically enumerated at the enormous x_k; the tests certify its exact divisor/quotient admission and compute only the required inner prefix.

Checker SHA256=6179d04a944315d41ef2406b8e266dbfde6d0857157bc1912a6b03d4bf74f5ab. Registration SHA256=e0d4d03b2eb8d86873b68f8937f75703887a007ed9cfa389b023ba1b4cc56746.

Novelty search covered current main code queries T_y, prime deletion, small-prefix and Rankin, the relevant full November 16/17 report files, and actual definitions behind the closest hits. OutsidePrimeDeletionMask and OutsidePrimeLeastSquareEndpoint concern complete CRT/six-coordinate populations; GlobalFirstJumpCriticalCorrelationBridge's unit-prefix obstruction concerns another normalized prime-partner source. Neither is the present frozen u_6 small-prefix theorem. #1143's lifetime-survivor prime fibre is also distinct. No equivalent SB boundary/counterfamily result was found in that scoped search; no exhaustive literature-novelty claim is made. TP's identities, FR's same-power equivalence and standard Rankin/PNT machinery are explicitly credited as prior work.

The strongest potential overclaim was tested algebraically: the corrected large-prefix premise is NOT a weaker known input. SB3 proves both directions. The pure-power no-go cannot be promoted to failure of H_actual or all signed deletion mechanisms. No synthetic model, finite pass, report assertion or green conditional Lean declaration is used to supply a missing infinite bound.

### I. Conceptual Interpretation

There are two different scales. A prefix can be large compared with its own inner power yet tiny compared with the outer x. The prime/cofactor obstruction lives at the first scale; the subpower restoring-support estimate pays it at the second. Confusing them either falsely rejects logarithmic deletion or falsely declares its remaining signed problem solved.

The new information is the explicit full boundary payment and the actual-quotient obstruction beyond the originally proposed cutoff. The ultimate growth estimate is unchanged. This is useful completion of a feasibility assignment, not a conceptual RH breakthrough.

### J. Competing Structural Hypotheses And Route Memory

The t<=2y boundary is PAID_ON_PAPER and need not be censused again. A constant-uniform t^gamma supplier on the entire remainder is REFUTED at its stated scope. Larger polylogarithmic boundaries remain cheap, and an x^delta boundary is affordable when delta<gamma, but SB3 shows why that repair alone does not produce arithmetic improvement.

FINITE-AC logarithmic deletion remains supporting representation only until a genuinely new complete signed correlation is derived. CORR4's multiplicity-two image theorem and signed mixed tail, and MU-LIFT's full-prefix r<k recurrence, retain their separate protected entry points. No new CORR4 or MU-LIFT supplier was proved or tested in this invocation; their coverage is not fabricated. Under the half-continuation policy, a next protected rotation should choose one with a concrete independent source mechanism, rather than repeat this finished boundary audit. No repository policy or team-wide route status is changed by this recommendation.

### K. Specialist Handoffs

- Coordinator: INV's exact boundary assignment is complete at paper/self-audit level. Preserve SB1 as paid support, the SB2 actual-quotient falsifier, and SB3's target-equivalence warning. HA's new all-head obstruction remains author/self-audit evidence; it is not imported into this proof.
- Owner Payment: SB.1 is an example of exact prime/cofactor accounting with all 2,3 multiplicities; do not transfer its negative sign to the clipped first-bad source. HF's full-history mask obstruction remains separate.
- Analytic Type II: any frozen-deletion proposal must state outer x loss, lower inner range and constants before x,d. The complete actual-quotient condition with subpower outer loss is equivalent to the desired growth class; an independently derived signed input is still needed.
- Prime Census: no expanded scan requested. Independent reproduction may target one held-out k and the wrong-cutoff x=149 control. A future computation should first name a genuinely new correlation inequality on the complete remaining source.
- Adversarial Referee: independently check SB1's entire quadratic return, SB2's dominated cofactor-tail argument and literal d=5^k admission, and both directions of SB3 including gamma=1/2's positive-loss treatment. Review status is PENDING, not self-acceptance.
- Lean Verification: no implementation PR is commissioned. After independent acceptance and a named consumer, SB1's finite source partition may be a useful supporting lemma. Do not formalize another conditional growth wrapper or infer the paper FR bridge from #1139's finite witness alone.

These are asynchronous report handoffs for later authorized runs, not agent launches or promises of background work.

### L. First Independently Missing Theorem

No independently weaker sufficient supplier was found. The remaining task is a genuinely arithmetic strict improvement for the COMPLETE S/M source, or another route's complete source. In these coordinates it must control the signed large-prefix restoration, or prove H_actual at gamma<the current actual boundary, from information beyond the same-boundary growth estimate and the already-paid support count. SB3 proves why merely naming that condition does not reduce its mathematical strength.

The paid upper bound at the existing exponent transmits through the inverse with only subpower loss but does NOT lower that exponent. There is no hidden small-prefix bill left that automatically creates the missing strict inequality.

### M. Continuity, Source Receipt And Next-Run Resume

The full reporting tree at 89b9961c9f146cabf3ff5b8de87f8e8b3e4de9ae was enumerated without a calendar cap. Latest actual publication files for all seven roles and every November 16 predecessor were retrieved. The previous own GD receipt supplies the consumed watermark SC/FB/EF/TP/MC/CF/CR. Relevant new publications were consumed in chronological order DJ, SG, NYMAN-JUMP, INV, HF, HA. FR/TP and the relevant GD source derivations were recovered explicitly. This is task-relevant backfill, not a claim to reread every historic appendix. Both dates' complete Coordinator mirrors were fetched and compared byte-for-byte.

Latest files below are under research/agent_reports/2026-11-17/. Times are substantive publication times verified against the cited commits, in EST. The blob column is the fetched latest file INCLUDING its receipt, not the earlier substantive-only blob.

| Role | LAST_VERIFIED Blob / Section / Publication | LAST_CONSUMED -> Newly Consumed / First Open Step |
| --- | --- | --- |
| Coordinator 00/90 | 21ae56b8856c02eea79efd6c2ffa01381d08710e; INV; 07:43:16 | SC -> INV1-INV6; small-prefix request answered here; original selected Nyman supplier remains open |
| Owner 10 | efab9f519e086b7b7cf78e7d6112a4b6ab0089ea; HF; 08:33:19 | FB -> HF1-HF6; genuine history-sensitive source input missing; synthetic witness is not primes |
| Analytic 20 | 686c0a992692db9a53e7416745f37ee9b79f9fbb; HA; 09:31:51 | EF -> HA1-HA4; uniform all-head supplier author-refuted; sparse heads not refuted |
| Wheel 30 | d05b58d49e7957a6747d8c47883b4f355c8e68a3; GD; 02:31:28 | Own GD1-GD5 resumed; sharp inverse-cost calculation not rerun |
| Census 40 | 0baa1581ac5ef1f4a7f82ded3850af6af4095d8b; DJ; 03:38:07 | MC -> DJ1-DJ4; H26,m210 selected parity falsifier and low-depth repair |
| Referee 50 | 64ce6e54e708767cb7053a2af17206597551ee74; SG; 04:35:55 | CF -> SG; SC1-SC3, EF1-EF3 and DJ2 ACCEPT_ON_PAPER at stated scopes; SG self-audit only; GD not wholesale accepted |
| Lean 60 | 16d7a3b3c94f213c6407a97fd1f84eb7b5a1a9d5; NYMAN-JUMP; 05:31:10 | CR -> #1140 finite original sign proof; current merge supersedes old unmerged receipt |

TODAY=AVAILABLE for every role. YESTERDAY=READ / CARRY_FORWARD where used; all seven November 16 files exist. NEW_UNCONSUMED=NONE for relevant sections in this intake; earlier gaps retain prior reports' evidence and are not invented executions. CONTINUITY_COMPLETE denotes this verified discovery/backfill only. The external inbox 7d63d434690d00dffce9c90335d41c4f62d85798 was read and is unchanged, with no entry after October 18. Preserve EXT-20261018-PNT-1's true cofactor weights and EXT-20261014-5's unconditional-versus-first-bad distinction.

The early SB checkpoint was committed at 15:15:41 UTC as 8606c00fbb136d89cc303d45240d3870d3119082, blob 032f6f288b6fd0e3611fdb08ae4930c292e1e1db. Immutable readback matched exactly; commit inspection confirms only this owned report changed, with 23 additions and zero deletions.

~~~text
RUN=20261117-wheel-1012-EST/SB; PLATFORM_RUN_ID=UNAVAILABLE
ROUTE=FINITE-AC bounded feasibility / genuine u_6 deletion
ORIGINAL_SOURCE=full ordered Q_R, strict K_R; accepted FR bridge via full S and J
CURRENT_P(b)=native every-positive-loss Mertens growth, b_base as above
NEW_SUPPORT=boundary O_epsilon(x^epsilon), full square correction O_epsilon(x^(1+epsilon))
COUNTERFAMILY=x=5^k*k^2,d=5^k,t=k^2; genuine post-2log x pure-power failure
ADVANCE=OPEN G_M(b)=>H_actual(gamma(b),delta(b)); gamma=1/2+(b-1/2)/2
RENEWAL=conditional gap-halving only; no arithmetic implication proved
ENDPOINT=H_actual(1/2,delta) iff RH on its exact every-loss quantifiers
ALL_RETURN_BILLS=prime powers, frozen cutoff, once-only n=d*m, J, unit/history,
                 powerful convolution, ordered orientations and quadratic cross terms
PRESENT_WORK=complete INV small-prefix assignment; no new global supplier
STATUS=ACTIVE_SUPPORT; TASK_STATUS=BOUNDED_FEASIBILITY_COMPLETE
INDEPENDENT_REVIEW=PENDING; FORMALIZATION=NONE; CI=REUSED_ONLY
VERIFIED_ETA=NONE; RH=OPEN
NEXT=independent SB review or a genuinely new signed large-prefix correlation;
     do not repeat TP/GD costs, INV.10 alone, this boundary census, or SB3 wrapper
~~~

Execution limitation: direct git clone was unavailable (CONNECT tunnel failed, HTTP 403). All repository reads and authorized report writes used the GitHub connector and immutable refs instead; no continuity or publication claim relies on the failed clone. No main/source/shared-policy/other-report/branch/PR/workflow/schedule/permission change and no agent launch occurred.

### N. Immutable Source Ledger

Every row below is a fetched source whose blob SHA was cross-checked against the nontruncated final main tree at fd4085e20602bc210cc6b630abbdeeeaf1bf28eb. Sources were fetched at intake, or refetched after the late merge when changed; unchanged bytes remain available. The only changed prior ledger row is the DAG, whose intake blob was 0376426a49ae44582e828350311e4421c17bd22f. Reading a source does not claim a new build. The ledger differentiates compiled input, paper interfaces and non-main comparisons in the text above.

| Exact Source Path | Git Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/AGENTS.md) | c4f36b772f8a4b0c24fe566b90fafb646073c60f |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/CURRENT_PROOF_CONTRACT.md) | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| [docs/RHLEAN_BOOTSTRAP_TO_HALF_20261116.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/docs/RHLEAN_BOOTSTRAP_TO_HALF_20261116.md) | 96ad4439ec458af6168f7d9cb3eef5dde291d37c |
| [docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md) | e3ae4280438f591f1ffaddd754a1c3a6d35d0691 |
| [docs/RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/docs/RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md) | 3e71820a4af722eae7098da6945bb5bcba50dd0d |
| [docs/DYNAMIC_RESEARCH_AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/docs/DYNAMIC_RESEARCH_AGENTS.md) | b76d595f09403fc54eca71d04bf9e0306e0a9c09 |
| [docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md) | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| [docs/PROOF_DEPENDENCY_DAG.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/docs/PROOF_DEPENDENCY_DAG.md) | 098f88f9b8e727ce78e52e5dc5158d68c930bf1b |
| [docs/COORDINATE_ATLAS.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/docs/COORDINATE_ATLAS.md) | cd0419d00a37739fe5a292f5cb738e33213949d5 |
| [research/EULER_HYBRID_ABEL_GRAM_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/EULER_HYBRID_ABEL_GRAM_20261027.lean) | 2a94dd8fd56fc03e95f732fb44b778a8d4f83e26 |
| [research/EULER_SELF_DUAL_POINTWISE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/EULER_SELF_DUAL_POINTWISE_20261027.lean) | c327c556f39ee7014fd774b24d0f95a1ece050e0 |
| [research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean) | e97561ef330a9996fd807d8910369f0698147b01 |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| [research/EULER_FIXED_GCD_ROW_OBSTRUCTION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/EULER_FIXED_GCD_ROW_OBSTRUCTION.lean) | 9003eb1c226f0b114be6402e63f325b60c80bf92 |
| [RHLean/Proof/SquareRootAmplificationLogGrowth.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/RHLean/Proof/SquareRootAmplificationLogGrowth.lean) | 2599db31079f388229d072ee616957fba6ffc555 |
| [RHLean/Proof/AmplificationExponentIteration.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/RHLean/Proof/AmplificationExponentIteration.lean) | d78be4509e5dcc35b833c3786258b94fc6e71915 |
| [research/MERTENS_CONVERSE_IDENTIFICATION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/MERTENS_CONVERSE_IDENTIFICATION.lean) | 768c8255850bf4074aff265c3fe17a1f5c43979b |
| [research/UNIVERSAL_ENVELOPE_RH_BRIDGES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/UNIVERSAL_ENVELOPE_RH_BRIDGES.lean) | 02a88cadc1eb984557b9dd7ee2e03e29bd3e5287 |
| [research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/oai_434/VF919WindowErrorClosure.lean) | f629db1b2b65d6ec042ac9432397d4b6316200c6 |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | 1f17f9401a63d16227db2e2aad020b9f74bc5f4e |
| [research/half_bootstrap_20261116/native_renewal.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/half_bootstrap_20261116/native_renewal.md) | 18b00148e405be3115b5ebb2066e9e67c417b563 |
| [research/EULER_DOUBLE_CENTERED_SOURCE_20261117.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/EULER_DOUBLE_CENTERED_SOURCE_20261117.lean) | 7cb66c07ff3bb784f1b1d4434647326f06f0f2b2 |
| [research/EULER_DOUBLE_CENTERED_REMAINDER_20261117.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/EULER_DOUBLE_CENTERED_REMAINDER_20261117.lean) | fffc2c07a82368d56b0b4075c625dd3f9a09e147 |
| [research/NATIVE_OWNER_DIAGONAL_CAPACITY_20261117.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/research/NATIVE_OWNER_DIAGONAL_CAPACITY_20261117.lean) | 4d7d7e173c335b4a807dabaa6b9ec38c1509dbd4 |
| [RHLean/Analysis/OutsidePrimeDeletionMask.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/RHLean/Analysis/OutsidePrimeDeletionMask.lean) | f3dd71442bccc7581d245203e38e474faec06f4d |
| [RHLean/Analysis/OutsidePrimeLeastSquareEndpoint.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/RHLean/Analysis/OutsidePrimeLeastSquareEndpoint.lean) | 6d52fa60de2215495065e13af5ef47ae7986e960 |
| [RHLean/Proof/GlobalFirstJumpCriticalCorrelationBridge.lean](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/RHLean/Proof/GlobalFirstJumpCriticalCorrelationBridge.lean) | a51f642952583e0fa134252f6b88ebbf32a0f550 |
| [docs/PRESERVATION_SOURCE_REDUCTIONS_20261117.md](https://github.com/OVVO-Financial/RH_Lean/blob/fd4085e20602bc210cc6b630abbdeeeaf1bf28eb/docs/PRESERVATION_SOURCE_REDUCTIONS_20261117.md) | 25404d0fe24f32f339297b78d4d5fe8facfcf216 |

The inspected non-main comparison research/SURVIVOR_PRIME_COMPOSITE_ACCOUNTING_20261117.lean has blob eb72870402ee8314adfcc332b89b376777406630 at #1143 head b02c724221a74eb0835e7a090c615c8cdbc808fc. #1143 is merged into the docs branch only; its source is absent from final main and is not an SB premise.

November 16 predecessor file blobs (full files retrieved at the report intake):

| Role File Prefix | Git Blob SHA |
| --- | --- |
| 00/90 | fda92549dd9291c491005fdf70847b90d9be385a |
| 10 | a52b439e693e069502b0c299a5f074a19bae0807 |
| 20 | 84aaa2103225565607b5b033f273462bbe865246 |
| 30 | 713826840694e39a141fbdbe813f1d47245928e7 |
| 40 | 53e6be517dc11037fe3b42a8ed6ad3a06cfce956 |
| 50 | 240b97ce1c8ddc87d5f520bc9a8cd6ea00df3d32 |
| 60 | 0bada0352d54be7c46a7d928f4c4e3bee440ad8f |

Original latest-run claim namespaces and verified substantive publication commits (all dates November 17, 2026):

| Original Run / Claim Namespace | Substantive Commit | UTC Time |
| --- | --- | --- |
| 20261117-coordinator-0710-EST/INV | [0127b6edb91677c877d14395ea130643ffa0ffe7](https://github.com/OVVO-Financial/RH_Lean/commit/0127b6edb91677c877d14395ea130643ffa0ffe7) | 12:43:16 |
| 20261117-owner-0809-EST/HF | [71a2e0b2bc3183d3c330f771f7a461bdd573b4cf](https://github.com/OVVO-Financial/RH_Lean/commit/71a2e0b2bc3183d3c330f771f7a461bdd573b4cf) | 13:33:19 |
| 20261117-analytic-0909-EST/HA | [e79b05135514ef216b0187b8567c97633694cf24](https://github.com/OVVO-Financial/RH_Lean/commit/e79b05135514ef216b0187b8567c97633694cf24) | 14:31:51 |
| 20261117-wheel-0205-EST/GD | [5a86d22e26c08bfee995810847119427425ca2b2](https://github.com/OVVO-Financial/RH_Lean/commit/5a86d22e26c08bfee995810847119427425ca2b2) | 07:31:28 |
| 20261117-census-0311-EST/DJ | [6cc512ec7ec182c886785ff9d6c019e7f8d1fbd9](https://github.com/OVVO-Financial/RH_Lean/commit/6cc512ec7ec182c886785ff9d6c019e7f8d1fbd9) | 08:38:07 |
| 20261117-referee-0413-EST/SG | [d3aac3c313a3d0326f0ac0b5d81c40a34c6a8a52](https://github.com/OVVO-Financial/RH_Lean/commit/d3aac3c313a3d0326f0ac0b5d81c40a34c6a8a52) | 09:35:55 |
| 20261117-lean-0510-EST/NYMAN-JUMP | [79bc536945f35b74b4d68f6caf1a02db00356623](https://github.com/OVVO-Financial/RH_Lean/commit/79bc536945f35b74b4d68f6caf1a02db00356623) | 10:31:10 |

Commit timestamps were checked through GitHub, not inferred from schedules. These substantive commits are distinguished from the later receipt-containing file blobs in M.

### O. Reproducibility Appendix

The following are the complete registered and executed versions, using only Python's standard library. The checker expects the registration text as registration.md beside check_sb.py; both hashes are fixed in H. The single completed execution exited zero with PASS_EXACT and 951,822 counted assertions. The report's tables transcribe its observed counts and witnesses. No new Lean execution, external data or random seed is involved. Finite output does not certify any asymptotic claim.

#### O1. Exact Pre-Execution Registration

~~~~text
# SB Exact Regression Registration

Run: 20261117-wheel-1012-EST/SB. Registered before checker execution.

1. Boundary source: integer x=1..256 discovery and 257..512 held out; prime cutoffs y=3,5,7,11,17 and actual y=log x for x>=8. Thresholds L=0,1,2, floor(2y), floor(sqrt x), floor(x/3),x, deduplicated. Verify the full forward sum, the literal (L+1)d>x mask, original-occurrence reconstruction, absolute boundary bound L*N_y(x), and complete quadratic cross term.
2. One-large-prime source: y=3..48 and y=7/2,11/2,17/2,29/2; every integer 1<=t<=floor(y^2). Independently compare the original signed source with the 2,3-smooth/cofactor-weighted prime formula. Retain equal endpoints. Also verify INV.10 at t=floor(2y).
3. Actual-quotient family: k=7..64, then held-out 73,97,127; x=5^k*k^2,d=5^k,t=k^2,y=log x. Certify cutoff membership and floor(2y) using rational log intervals. Compute genuine T_y(t), but do not infer asymptotics from finite ratios.
4. Negative controls: delete d with a repeated selected prime; replace strict threshold by the wrong x/L threshold; omit the boundary/middle quadratic cross term; change the frozen inner cutoff; ignore 2,3-smooth cofactors; extend the one-large-prime formula beyond its valid range (y=5,t=49).
5. Exact arithmetic: all primality, factorization, counts, signs, floors, endpoints and source identities use integers/Fraction. Log bounds use the atanh series plus explicit positive geometric remainder. No binary floating-point inequality is accepted as proof. Tests certify only their finite domains.

No new wheel census, inverse-mass asymptotic, local Lean execution or hosted CI run is commissioned.
~~~~

#### O2. Complete Executed Checker

~~~~python
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import isqrt
from pathlib import Path
import hashlib
import json


COUNTS = Counter()
NEGATIVE = Counter()


def check(label, statement):
    assert statement, label
    COUNTS[label] += 1


@lru_cache(None)
def factor(n):
    out = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            out.append((p, e))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def u(n):
    return (-1) ** sum(p > 3 for p, e in factor(n))


def coefficient(n, y):
    fac = factor(n)
    return (-1) ** len(fac) if all(5 <= p <= y for p, e in fac) else 0


def smooth_part(n, y):
    # Independent occurrence map, using divisions rather than factor tuples.
    d = 1
    for p in range(5, int(y) + 1):
        if all(p % q for q in range(2, isqrt(p) + 1)):
            while n % p == 0:
                n //= p
                d *= p
    return d, n


@lru_cache(None)
def prefixes(y, limit):
    total = [0]
    for n in range(1, limit + 1):
        admitted = all(not (5 <= p <= y) for p, e in factor(n))
        total.append(total[-1] + (u(n) if admitted else 0))
    return total


@lru_cache(None)
def smooth23(t):
    values = []
    a = 1
    while a <= t:
        b = a
        while b <= t:
            values.append(b)
            b *= 3
        a *= 2
    return sorted(values)


def log_unit_bounds(v, terms=24):
    z = (v - 1) / (v + 1)
    partial = 2 * sum((z ** (2*j + 1) / (2*j + 1) for j in range(terms)), F())
    remainder = 2*z**(2*terms + 1) / ((2*terms + 1)*(1-z*z))
    return partial, partial + remainder


@lru_cache(None)
def log_bounds(n):
    e = n.bit_length() - 1
    lo2, hi2 = log_unit_bounds(F(2))
    lo, hi = log_unit_bounds(F(n, 2**e))
    return e*lo2 + lo, e*hi2 + hi


def certified_floor(interval):
    lo, hi = interval
    a, b = lo.numerator // lo.denominator, hi.numerator // hi.denominator
    assert a == b
    return a


def prime_counts(limit):
    flags = [True] * (limit + 1)
    flags[0] = flags[1] = False
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            for n in range(p*p, limit + 1, p):
                flags[n] = False
    out = [0]
    for n in range(1, limit + 1):
        out.append(out[-1] + flags[n])
    return flags, out


def one_prime_formula(y, t, pi):
    return len(smooth23(t)) - sum(pi[t // m] - pi[int(y)]
        for m in smooth23(t) if F(m)*y <= t)


def main():
    flags, pi = prime_counts(127**2)
    for n in range(2, 127**2 + 1):
        check('independent_primality', flags[n] == (factor(n) == ((n, 1),)))

    for x in range(1, 513):
        cases = [(F(y), 2*y) for y in (3, 5, 7, 11, 17)]
        if x >= 8:
            logx = log_bounds(x)
            q = certified_floor(logx)
            cases.append((F(q), certified_floor((2*logx[0], 2*logx[1]))))
        source = sum(u(n) for n in range(1, x + 1))
        for y, boundary in cases:
            T = prefixes(y, x)
            support = [d for d in range(1, x + 1) if coefficient(d, y)]
            terms = {d: coefficient(d, y)*T[x//d] for d in support}
            check('full_restoration', sum(terms.values()) == source)
            mapped = [smooth_part(n, y) for n in range(1, x + 1)]
            for n, (d, m) in enumerate(mapped, 1):
                check('once_only_occurrence', d*m == n and coefficient(d, y)*u(m) == u(n))
            for L in sorted({0, 1, 2, boundary, isqrt(x), x//3, x}):
                B = sum(v for d, v in terms.items() if x//d <= L)
                U = sum(v for d, v in terms.items() if x//d > L)
                check('strict_floor_boundary', all((x//d <= L) == ((L+1)*d > x) for d in support))
                check('original_boundary', B == sum(u(n) for n, (d, m) in enumerate(mapped, 1) if x//d <= L))
                check('complete_partition', source == B + U)
                check('boundary_absolute_bill', abs(B) <= L*len(support))
                check('complete_quadratic', source*source == B*B + U*U + 2*B*U)
                NEGATIVE['quadratic_cross'] += source*source != B*B + U*U
                if L:
                    wrong = sum(v for d, v in terms.items() if L*d > x)
                    NEGATIVE['wrong_endpoint'] += wrong != B
            without_powers = sum(v for d, v in terms.items() if all(e == 1 for p, e in factor(d)))
            NEGATIVE['omitted_powers'] += without_powers != source

    ys = [F(y) for y in range(3, 49)] + [F(n, 2) for n in (7, 11, 17, 29)]
    for y in ys:
        limit = int(y*y)
        T = prefixes(y, limit)
        for t in range(1, limit + 1):
            check('one_large_prime_identity', T[t] == one_prime_formula(y, t, pi))
            naive = len(smooth23(t)) - max(0, pi[t]-pi[int(y)])
            NEGATIVE['omitted_23_cofactors'] += naive != T[t]
        t = int(2*y)
        check('INV10_exact', T[t] == len(smooth23(t)) - (pi[t]-pi[int(y)]))

    actual = []
    for k in list(range(7, 65)) + [73, 97, 127]:
        lo5, hi5 = log_bounds(5)
        lok, hik = log_bounds(k)
        ylo, yhi = k*lo5 + 2*lok, k*hi5 + 2*hik
        yf = certified_floor((ylo, yhi))
        L = certified_floor((2*ylo, 2*yhi))
        d, t = 5**k, k*k
        x = d*t
        check('actual_floor_quotient', x//d == t)
        check('actual_support_power', yf >= 5 and coefficient(d, yf) == -1)
        check('beyond_small_boundary', t > L)
        check('inside_one_prime_range', t < ylo*ylo)
        value = prefixes(F(yf), t)[t]
        check('actual_quotient_identity', value == one_prime_formula(F(yf), t, pi))
        if k in (7, 16, 32, 64, 73, 97, 127):
            actual.append({'k': k, 'floor_log_x': yf, 'L': L, 't': t,
                           'T': value, 'abs_T_over_sqrt_t': str(F(abs(value), k))})

    check('range_extension_negative_control', prefixes(F(5), 49)[49] != one_prime_formula(F(5), 49, pi))
    # A new, log-scheduled control; the earlier x=625 quarter-root control is not rerun.
    wrong_inner = None
    for x in range(25, 513):
        y = certified_floor(log_bounds(x))
        total = 0
        for d in range(1, x + 1):
            c = coefficient(d, y)
            if c:
                t = x//d
                inner = certified_floor(log_bounds(t))
                total += c*prefixes(F(inner), t)[t]
        if total != sum(u(n) for n in range(1, x + 1)):
            wrong_inner = {'x': x, 'floor_log_x': y, 'wrong_sum': total,
                           'true_sum': sum(u(n) for n in range(1, x + 1))}
            break
    check('moving_cutoff_negative_control', wrong_inner is not None)
    for label in ('quadratic_cross', 'wrong_endpoint', 'omitted_powers', 'omitted_23_cofactors'):
        check('negative_control_'+label, NEGATIVE[label] > 0)

    print(json.dumps({'status': 'PASS_EXACT', 'checks': dict(COUNTS),
        'total': sum(COUNTS.values()), 'omission_detections': dict(NEGATIVE),
        'actual_quotient_rows': actual, 'wrong_moving_cutoff': wrong_inner,
        'asymptotic_inference': 'NONE',
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'registration_sha256': hashlib.sha256(Path(__file__).with_name('registration.md').read_bytes()).hexdigest()}, indent=2))


if __name__ == '__main__':
    main()
~~~~

### P. Prepublication Freshness And Validation

At 2026-11-17 15:40:20 UTC, main remained fd4085e20602bc210cc6b630abbdeeeaf1bf28eb after the late human merge, and the reporting head remained 8606c00fbb136d89cc303d45240d3870d3119082. The refreshed nontruncated report tree differs from intake only in this invocation's early owned checkpoint. No intervening upstream publication or external handoff was omitted. Open/draft discovery is empty. #1142 is merged to main; #1143 is merged only to its docs-branch base and its new source is absent from main, as detailed in B. The tested heads retain respectively 7/7 and 13/13 successful completed checks. No checks were launched. An earlier publication attempt stopped BEFORE any write when its freshness guard detected the main advance; the changed documentation and authoritative files were then read and the final source ledger revalidated.

The owned file was fetched immediately before update and matched the complete checkpoint exactly. The proposed append preserves every prior byte. A-O sections, ASCII, balanced Markdown fences, tables, embedded registration/checker identity, syntax, source-hash equality, theorem quantifiers, constant order, original occurrence masks and finite-versus-infinite evidence status were checked. The executed checker completed; no process needed for this work remains running. Publication is READBACK_PENDING until an immutable receipt is appended below.

### SB Publication Receipt

The substantive [commit 7426a5cae2795c43c1176d20a562c09a41d96add](https://github.com/OVVO-Financial/RH_Lean/commit/7426a5cae2795c43c1176d20a562c09a41d96add), committed at 2026-11-17T15:40:21Z / 10:40:21 EST, was inspected. At 2026-11-17 15:40:50 UTC this report was fetched at that IMMUTABLE commit: all 112,738 ASCII characters matched the submitted content exactly, blob 0e2662dd55afbae2de4ec1dbcc47e612350a5fed. Commit inspection confirms ONLY this authorized daily report changed, with 681 additions and zero deletions. The full earlier GD history, prior receipts and the verified SB checkpoint remain exact preserved prefixes.

EXECUTION=COMPLETED; SUBSTANTIVE_PUBLICATION=PUBLISHED_IMMUTABLE_READBACK_VERIFIED. SB1-SB3 remain PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED, with SB3 explicitly a target-equivalence audit. SB4 is FINITE_COMPUTATION: 951,822 exact/rational assertions passed, syntax and embedded-byte validation passed, and all preregistered omission controls were detected. No all-scale conclusion is inferred from the finite tests.

The full logarithmic small-prefix boundary and its quadratic cross return are paid at the stated paper scope. The pure-inner-power supplier beyond 2log x is refuted by genuine source-admitted quotients; the repaired outer-loss condition remains growth-equivalent. No strict exponent gain, new accepted RH route or Lean theorem is claimed. VERIFIED_ETA=NONE; RH=OPEN.

Resume at the completed Coordinator INV boundary assignment, SB1-SB4 and the exact independent large-prefix obstruction in L. Next work requires independent review or a genuinely new complete signed arithmetic mechanism; do not repeat this finite census or promote SB3's equivalent premise to a paid supplier. Final source authority is fd4085e20602bc210cc6b630abbdeeeaf1bf28eb; #1143's separate docs-branch merge is not on that main tree. No Lean/source/main/shared-policy/other-report/proof-branch/PR/workflow/schedule/permission edit and no agent launch occurred. This receipt records the already-verified substantive commit, not its own future containing commit; the containing update is separately read back before delivery.


## IN_PROGRESS Checkpoint - 20261117-wheel-1806-EST/PP

### A. Structural Question
Test whether the newly compiled complete double-centering makes its balanced prime-pair sector individually small enough for a subcritical historical-power estimate. Investigate the exact kernel on genuine primes, product-preserving factor exchange, and the entire complementary signed return. This is a bounded FINITE-AC feasibility audit, not a new accepted route or a claimed exponent gain.

### B. Authority And Continuity
Scheduled trigger: 2026-11-17 18:06:00 EST. PLATFORM_RUN_ID=UNAVAILABLE.
Pinned main: 13b31c6313e274a073d82a01175201185e59e37e; reports intake: b41106ac4acd44632f7f3efb55e25f21c8a35c44.
Read live AGENTS/current contract, BOOTSTRAP_TO_HALF_V1, CROSS_ROUTE_SIGNED_RECOVERY_V1 and LAST_ACTUAL_REPORT_CONTINUITY_V1. Both November 16/17 Coordinator mirrors match. All seven latest actual reports and yesterday's reports were retrieved; relevant post-SB handoffs TC, IC, HF1, TAIL, PC and CP were consumed. IC accepts SB1-SB3 on paper; do not rerun that boundary census. CP is an author/self-audited necessary condition, not a positive complete Nyman bound. External inbox 7d63d434690d00dffce9c90335d41c4f62d85798 is unchanged.
Latest main includes #1144; #1143 merged only into its non-main base. No proof source or other report will be edited.

### C. Registered Mechanism And Consumer
Original source: Q_R=sum_(1<=a,b<R)mu(a)mu(b)floor((R^2-1)/(ab)), strict K_R, and literal Xi_R from EULER_DOUBLE_CENTERED_SOURCE_20261117.lean. The complete removed remainder is already O_epsilon(R^(1+epsilon)).
Hypothesis to test: separate factor-defined components of Xi admit the prospective strict grade individually. Candidate falsifier: P_R={(p,q): p,q prime, R/2<p,q<=R-2}; retain p=q and both ordered orientations.
Starting comparator: every-positive-loss b_base=7/8-7/(64*N_pack), with no zero-loss assertion at b_base. A genuine complete estimate |Xi_R|<=C_epsilon R^(1+eta+epsilon)K_R^(lambda/2), eta<(2-lambda)(b-1/2), would improve b; lambda=1 and eta=(b-1/2)/2 renew by the existing factor-3/4 map. This arithmetic supplier is OPEN, and the whole grade is target-strength.
Predicted alternative: a nonzero R^2/log^2 R prime-sector main term survives centering and must be canceled by the literal complement before any norm. Exact PNT-scale asymptotics, if established, do not pay the subcritical remainder.

### D-M. Pending Work
PENDING: full proof, novelty audit, exact small-root/endpoint falsification, complete interaction reconstruction, specialist handoffs and final source/publication validation.
half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1.
EXECUTION=IN_PROGRESS; MATHEMATICS=UNVERIFIED_CANDIDATE; INDEPENDENT_REVIEW=PENDING; NO_NEW_LEAN; VERIFIED_ETA=NONE; RH=OPEN.

## Prime-Pair Coherence Survives Complete Double-Centering

### Final Research Synthesis - 20261117-wheel-1806-EST/PP

Actual scheduled trigger: November 17, 2026, 18:06:00 EST / 23:06:00 UTC.
PLATFORM_RUN_ID=UNAVAILABLE. PP is a research label, not a platform identifier.
Earlier GD/SB work and the PP checkpoint are preserved verbatim. New claims
below are PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED,
except where explicitly classified as existing infrastructure or finite tests.

### A. Most Important Structural Discovery

**The complete double-centered Euler kernel retains a genuinely arithmetic
prime-pair main term of order R^2/log^2 R. Its three balanced primality classes
have forced leading proportions -1 : 2 : -1, not separately small contributions.**

Set c=(log(9/2)-1)/6>0 and A_R=R^2/log^2 R. For the literal balanced nondivisor
interval I_R={a: R/2<a<=R-2}, let PP, PC, CC denote the original signed kernel
sums over respectively two primes, exactly one prime (BOTH orientations), and
two nonprimes. Then

```text
PP_R = -c A_R + o(A_R),
PC_R =  2c A_R + o(A_R),
CC_R = -c A_R + o(A_R).
```

PP uses ordinary PNT only. PC/CC additionally use the already-paid genuine
subunit Mertens bound, not a new cancellation premise. The original complete
source and every return term are reconstructed below. In particular, taking
absolute values of these three classes before recombination loses
4c A_R+o(A_R). Such a classwise estimate cannot supply any fixed exponent below
2, including any qualifying strict historical-power grade for the half-bootstrap.

There is also a pointwise genuine-prime obstruction: for R>=10 and
3R/4<p,q<=4R/5, the actual centered kernel is <=-1/2. Distinct-prime pairs occur
at the same quadratic/logarithmic scale; this is not a square-diagonal artifact.
However, the stronger assertion that EVERY balanced prime entry is nonpositive
is FALSE: R=9, p=q=5 gives J=1/4.

This completes a bounded feasibility test of separate-component payment after
centering. It is not a new RH route, global exponent improvement, independent
reproof of the baseline, or a proof that joint cancellation is impossible.
NO_NEW_GLOBAL_GAIN; VERIFIED_ETA=NONE; RH=OPEN.

### B. Current Authoritative Objective

Main: `13b31c6313e274a073d82a01175201185e59e37e`. Reports intake:
`b41106ac4acd44632f7f3efb55e25f21c8a35c44`. Live AGENTS and current contract,
the half-bootstrap, cross-route recovery, continuity and complete-return
instructions were consumed. The newer BOOTSTRAP_TO_HALF_V1 task priority
supersedes conflicting dated priority banners, not theorem hypotheses.

```text
half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1
cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1
continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1
high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1
chain_ack=CANCELLATION_CHAIN_REUSE_V1
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1
```

Canonical objective: `VFCanonicalSquareVonKochStatement`, one C>=0 before all
natural R>=2 with |pi(R^2)-VF_can(R^2)|<=C R log R, where
VF_can=VF_mid+sqrt(2). It is OPEN. The inspected terminal
`riemannHypothesis_of_vfCanonicalSquare` explicitly takes
`ClassicalVonKochRHCriterion` and the arithmetic bound. The distinct internal
Mertens-energy consumer is not that unfilled interface.

The reused compiled comparator is
`RHLean.Analysis.native_mertens_near_uniform_window_error_closed`:
every-positive-loss growth at b_base=7/8-7/(64*N_pack), with the actual fixed
`nearUniformSlotCount`. Spending its positive margin gives a fixed
|M(x)|<=C x^(7/8). No zero-loss bound at b_base or comparison with a different
slot count is asserted. The original theorem type has no extra open supplier
argument. Its transitive native analytic chain is reused, not independently
re-proved in this report.

#### Formal Evidence Actually Checked

The #1119 tested head `77ee815846d6d534c866f0752aa33b84c385610a` has 14 successful
completed checks. Its [actual audit log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700)
was retrieved: the five window-error closures have sizes
35358,35375,35736,35737,35753 and only propext, Classical.choice, Quot.sound.
A nontruncated tree comparison of 2,508 preexisting Lean/pin/scripts/lean
files against current main finds only aggregate RHLean.lean changed. Thus
the relevant prior source dependencies and pins are unchanged; this is
scoped certification reuse, not a fresh full-main build.

#1141 is merged on main at tested head
`dfd3197117410ad491d7c94b66448753ae8e4d63`: 17 successful checks and three
superseded cancellations, not 20 successes. Its [Euler audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44099085547/job/134093952768)
was read. It reused nine cached modules, checked the exact source inventory
and types, and audited all 27 declarations with permitted terminal axioms.
It does not prove a bound on Xi. #1144 is now human-merged on main, with
13/13 successful checks at `abd9bb34c8fac459e67c63009961b6c26548d7e9`.
#1143 merged into `docs/preservation-target-strength-20261117`, NOT main.
The live open/draft collection was empty. No local Lean or new CI was run.

#### Material Source Blobs

All paths in this table were fetched at the pinned main; definitions and
relevant theorem signatures were inspected. Reading them does not certify PP.

| Source Path | Git Blob SHA |
| --- | --- |
| AGENTS.md | c4f36b772f8a4b0c24fe566b90fafb646073c60f |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_BOOTSTRAP_TO_HALF_20261116.md | 96ad4439ec458af6168f7d9cb3eef5dde291d37c |
| docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md | e3ae4280438f591f1ffaddd754a1c3a6d35d0691 |
| docs/RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md | 3e71820a4af722eae7098da6945bb5bcba50dd0d |
| docs/DYNAMIC_RESEARCH_AGENTS.md | b76d595f09403fc54eca71d04bf9e0306e0a9c09 |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| docs/PRESERVATION_SOURCE_REDUCTIONS_20261117.md | 25404d0fe24f32f339297b78d4d5fe8facfcf216 |
| research/EULER_DOUBLE_CENTERED_SOURCE_20261117.lean | 7cb66c07ff3bb784f1b1d4434647326f06f0f2b2 |
| research/EULER_DOUBLE_CENTERED_REMAINDER_20261117.lean | fffc2c07a82368d56b0b4075c625dd3f9a09e147 |
| research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean | e97561ef330a9996fd807d8910369f0698147b01 |
| research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| RHLean/Proof/SquareRootAmplificationLogGrowth.lean | 2599db31079f388229d072ee616957fba6ffc555 |
| RHLean/Proof/AmplificationExponentIteration.lean | d78be4509e5dcc35b833c3786258b94fc6e71915 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| research/oai_434/VF919WindowErrorClosure.lean | f629db1b2b65d6ec042ac9432397d4b6316200c6 |
| RHLean/Analysis/BalancedPrimeBilinearCentering.lean | 50e16feb11a935851409c0cd0ef1ba00c71c10e0 |
| research/DyadicPrimeNearResonance.lean | f416e0149b73656e30a7f68a3934a937353d3f8d |
| docs/COORDINATE_ATLAS.md | cd0419d00a37739fe5a292f5cb738e33213949d5 |
| docs/PROOF_DEPENDENCY_DAG.md | 098f88f9b8e727ce78e52e5dc5158d68c930bf1b |

### C. Structural Mechanism Investigated

The previous SB run paid the logarithmic small-prefix boundary; IC now accepts
SB1-SB3 on paper. Its repaired large-prefix supplier is target-strength, not
a newly paid input. The latest Coordinator TAIL synthesis instead permits a
bounded structural test of complete Xi, explicitly forbidding replacement of
its moving hyperbolas by a fixed collection of low-rank rectangles.

The tested mechanism is precise: could centering permit separate estimates
on genuine factor-defined populations at a strict historical-power grade?
The alternative is that true primality leaves a coherent macroscopic sector
whose cancellation requires the retained complementary signed occurrences.
No model primes, arbitrary signs, larger wheel or assumed independence enter.

For a possible terminal use, let GROWTH(b) mean every-positive-loss genuine
Mertens growth. An independently supplied complete grade

```text
forall eps>0 exists C_eps>=0 forall R>=2:
  |Xi_R| <= C_eps R^(1+eta+eps) K_R^(lambda/2),
0<=lambda<2, eta>=0,
```

with eta<(2-lambda)(b-1/2) would improve b. The complete remainder is already
root-subpower and K_R>=1; it is not omitted. For lambda=1 and
eta=(b-1/2)/2 the existing consumer contracts the gap by 3/4. Renewal would
require an independent supplier at EVERY fixed 1/2<b<=7/8; finitely many
iterations reach any chosen exponent above 1/2. Constants may depend on the
fixed stage and positive loss, but precede R. This supplier remains OPEN;
the grade has the documented target strength. PP tests a proposed way of
paying it and rejects that way, not the complete grade itself.

### D. Exact Theorem Statements

Let R be an integer >=2, N=R-1, P=R+1, X=R^2-1, t=P/N. Retain exactly

```text
Q_R = sum_(1<=a,b<R) mu(a)mu(b) floor(X/(ab)),
K_R = max_(0<=y<R) (M(y)-1)^2/(y+1),
J_R(a,b) = t {N/a}{N/b} - {X/(ab)},
Xi_R = sum_(1<=a,b<R; a does not divide N; b does not divide N)
                 mu(a)mu(b) J_R(a,b).
```

Braces mean fractional part. Q_R=2M(N)-M(X), and

```text
Q_R=E_R+Xi_R,
E_R=2P sum_(a<R)mu(a)/a - t
       + sum_(a,b<R; a|N OR b|N)mu(a)mu(b)J_R(a,b).
```

These are EXISTING compiled identities. The union is counted once.
The EXISTING bound is |E_R|=O_eps(R^(1+eps)), not a fixed root constant.

Define I_R as above and its prime subset P_R. Every a in I_R is a nondivisor
of N. PP, PC and CC are a disjoint partition of the balanced I_R x I_R
signed sum B_R, with PC including both orders. Define
O_R=Xi_R-B_R as the literal remaining nondivisor pairs, and Z_R=O_R+E_R.
Thus Q_R=PP_R+PC_R+CC_R+Z_R and Xi_R=B_R+O_R. No occurrence is spent twice.

**PP1: exact arithmetic geometry and a coherent negative subpopulation.**
For every a,b in I_R,

```text
J_R(a,b)=1+t-P/a-P/b+1_(2ab<=X)+1_(3ab<=X).
```

For prime a,b, neither 2ab nor 3ab equals R^2. If s=card(P_R),
v=sum_(p in P_R)1/p and H_j counts ORDERED prime pairs with jpq<=X, then

```text
PP_R=(1+t)s^2-2Psv+H_2+H_3.
```

For R>=10 and primes 3R/4<p,q<=4R/5, the pair belongs to I_R^2 and
J_R(p,q)<=-1/2. This includes, but is not restricted to, p=q.

**PP2: nonzero prime-sector main term.** As integer R tends to infinity,

```text
PP_R / (R^2/log^2 R) -> -(log(9/2)-1)/6 = -c < 0.
```

This uses ordinary PNT and exact kernel geometry, without a Mertens-growth
assumption. The distinct-prime-only sum has the same limit. Consequently PP
is not O(R^k log^d R) for any fixed k<2 and real d.

**PP3: source-faithful joint class balance and complete return.**
For every R>=2, the elementary historical Abel estimate is

```text
|B_R| <= 8 R^(3/2) sqrt(K_R).
```

It is a supporting bound, not a subcritical supplier. If FIXED
1/2<b<1 and C>=1 satisfy |M(n)|<=C n^b for all integers n>=1, then

```text
PC_R=2c A_R+o(A_R), CC_R=-c A_R+o(A_R),
Z_R=O_(b,C)(R^(b+1)), Q_R=O_(b,C)(R^(2b)).
```

The implied constants also include a fixed chosen remainder exponent when
E_R is used. The paid baseline supplies b=7/8. Thus the leading proportions
of the ENTIRE reconstructed Q source are (-c,2c,-c,0) times A_R.
For Y_R=Q_R-PP_R, eventually Y_R~c A_R and

```text
rho_R=2 PP_R Y_R/(PP_R^2+Y_R^2),
1+rho_R=Q_R^2/(PP_R^2+Y_R^2)
        =O_(b,C)(R^(4b-4) log^4 R).
```

This last rate is a CONSEQUENCE of the paid growth bound, not a new estimate
feeding back to improve it. At b=7/8 its power is -1/2. No independent
supplier is extracted by renaming this ratio.

**PP4: finite verification and a stronger-claim falsifier.** The registered
checker below passed 483,964 exact assertions. The universal pointwise
nonpositivity extension is REFUTED at (R,p,q)=(9,5,5), J=1/4. PP1's stated
subinterval and PP2's eventual aggregate claim survive that counterexample.

### E. Mathematical Proof

#### E1. Literal Geometry, Multiplicity And Endpoints

If a in I_R divides N, then a>N/2 forces a=N, excluded by a<=R-2.
Also floor(N/a)=1. Expanding both historical fractional parts cancels
tN^2/(ab)=X/(ab), giving J=floor(X/(ab))+t-P/a-P/b.
Since R^2/4<ab<X, the floor is 1,2 or 3; its two jumps are exactly those
in PP1. This is the balanced-kernel identity already described in the
preservation note, reused rather than advertised as a new identity.

For primes p,q, the total number of prime factors of jpq with multiplicity
is three when j=2 or 3. A square has even total multiplicity. Thus jpq!=R^2,
including p=q and primes equal to j. The masks jpq<=R^2-1 and jpq<=R^2
therefore agree EXACTLY on this prime carrier. No real endpoint approximation
has been made. Since mu(p)mu(q)=1, finite summation gives the displayed PP
count formula. In particular mu(p)^2=1 on p=q: replacing this by mu(p^2)=0
would silently delete genuine diagonal occurrences.

For the smaller prime band, ab>9R^2/16>X/2, so its floor is one. Its upper
endpoint <=4R/5 is <=R-2 when R>=10. Therefore

```text
J_R(p,q) <= 1+(R+1)/(R-1)-5(R+1)/(2R)
          = (-R^2+5)/(2R(R-1)) <= -1/2.
```

Unique factorization gives only (p,q),(q,p) as balanced factorizations of
pq for distinct primes, and only (p,p) for p^2. The two ordered off-diagonal
occurrences have equal signs and kernel values. A product-preserving
exchange cannot cancel this negative subpopulation. This is a specialization
of familiar factorization/sign bookkeeping, NOT a new general cubefree theorem.

#### E2. Prime-Pair Asymptotic Without A Prime-Independence Assumption

The only external analytic input needed here is classical
pi(x)~x/log x; see [NIST DLMF 27.12](https://dlmf.nist.gov/27.12), E4-E5.
The following limiting argument and constant are derived here for this
specific source; they are not quoted as a theorem from that reference.

On [1/2,1], the measure
(log R/R) sum_(p in P_R) delta_(p/R) converges to Lebesgue measure. This
follows on every fixed interval from PNT; the strict lower endpoint and
deleted upper integer R-1 affect at most finitely many points. Its Cartesian
product is EXACTLY the ordered prime-pair counting measure, not a stochastic
independence hypothesis. Grid rectangles then prove convergence against any
bounded function whose discontinuity curves have area zero.

On prime pairs, E1 removes the moving square-endpoint issue exactly. Uniformly
on the interval square, the remaining kernel differs by O(1/R) from

```text
j(u,v)=2-1/u-1/v+1_(2uv<=1)+1_(3uv<=1).
```

The two hyperbolas have zero area. They can also be covered by grid rectangles
of arbitrarily small total area before taking R to infinity, so no uniform
prime-distribution theorem for shrinking intervals is being assumed.
Integration on [1/2,1]^2 gives

```text
integral (2-1/u-1/v) = 1/2-log 2,
area(uv<=1/2)       = (log 2)/2-1/4,
area(uv<=1/3)       = log(4/3)/3-1/12.
sum                 = (1-log(9/2))/6 = -c.
```

The O(1/R) kernel error times the bounded normalized pair mass tends to zero.
Also c>0: log 2>1/2, hence log(9/2)>log 4>1. The diagonal contributes only
O(card(P_R))=O(R/log R), using |J|<=3, so deleting it changes no leading limit.

As an independent check on the mechanism, PNT gives
card{p:3R/4<p<=4R/5}~R/(20 log R). E1 then forces a negative contribution
whose magnitude has liminf, after normalization by A_R, at least 1/800.
Distinct-prime pairs give the same lower scale. The full constant c is not
inferred from this proper band; it comes from the full prime-pair integral.

#### E3. Historical Abel Control And The Three Signed Classes

Fix b0 in I_R and increase a through I_R. The integer floor X/(a b0) is
nonincreasing and drops by at most two in total. The increasing smooth term
-P/a varies by at most P/min(I_R)<2(R+1)/R<=3. Hence the total discrete
variation is <=5. The last kernel value has absolute value <=3, because
0<=t{N/a}{N/b}<3 and 0<={X/(ab)}<1. Variation plus the last value is <=8.

Every historical partial interval sum is
M(a)-M(min(I_R)-1), of absolute value <=2 sqrt(R K_R), with BOTH arguments
strictly below R. Discrete Abel summation bounds each signed inner row by
16 sqrt(R K_R). Summing |mu(b0)| over at most R/2 rows proves the historical
bound in PP3, including empty intervals.

Under the fixed Mertens input the same partial intervals are <=2C R^b, so
|B_R|<=8C R^(b+1). Define W_R as the balanced sum with the first variable
prime and the second unrestricted, retaining BOTH original Mobius factors.
The same row bound gives
|W_R|<=16C R^b card(P_R)=O_(b,C)(R^(b+1)/log R). Exact finite partitions give

```text
W_R=PP_R+PC_R/2,
PC_R=2W_R-2PP_R,
CC_R=B_R+PP_R-2W_R.
```

Because b<1, both B_R/A_R and W_R/A_R tend to zero. Combining these exact
identities with PP2 gives the stated -1:2:-1 leading proportions. The
class-expansion algebra is standard and agrees with the earlier compiled
prime-indicator inclusion-exclusion principle; the source-specific main
constant and restored estimates are the present deductions.

#### E4. Complete Source Return And All Cross Terms

The compiled endpoint identity gives |Q_R|<=3C R^(2b). Choose a fixed
0<eps<2b-1 in the EXISTING remainder theorem. Then E_R=O(R^(2b)),
Xi_R=O(R^(2b)), and O_R=Xi_R-B_R=O(R^(b+1)); also
Z_R=Q_R-B_R=O(R^(b+1)). Constants are fixed before R. No complement is
called zero merely because its leading normalized limit is zero.

For T=(PP_R,PC_R,CC_R,Z_R), the exact original square is

```text
Q_R^2=sum_(i=1..4) T_i^2 + 2 sum_(1<=i<j<=4) T_i T_j.
```

All six cross interactions remain. Their leading accounting is

```text
sum_i T_i^2 / A_R^2 -> 6c^2,
2 sum_(i<j) T_i T_j / A_R^2 -> -6c^2.
```

In particular the PP/CC interaction is POSITIVE at leading order and cannot
be discarded under an all-cross-negative rule. For Xi, replace Z by the
literal O; Q=Xi+E additionally retains 2Xi E+E^2. Equivalently, Y=Q-PP
includes every other original term and every centering return exactly once.
PP~-cA, Q=o(A) imply Y~cA. The rho formula and rate in PP3 follow by exact
algebra and the paid Q bound. No empirical correlation is used in this proof.

### F. Structural Consequence

The tested separation mechanism is REFUTED on genuine coefficients, not on
a synthetic alternative to Mobius. Centering cancels its specified rank-one
term; it does not make the three primality classes separately subquadratic.
They are arithmetically coupled with the explicit leading signs above.

More precisely, fixed |M(n)|<=C n^b gives K_R=O(R^(2b-1)). If
eta<(2-lambda)(b-1/2), then
1+eta+lambda(b-1/2)<2b<2. Choosing a sufficiently small positive loss shows
that a classwise bound at that grade contradicts PP2/PP3 for EACH of PP,PC,CC.
Thus this method cannot instantiate the half-continuation supplier.
This says nothing adverse about bounding the full signed Xi jointly.

The Abel estimate is also not an advance: in fixed Mertens coordinates it
costs R^(b+1), larger than the already-paid complete Q cost R^(2b) when b<1.
At the displayed historical normalization it has eta=1/2. Reiterating it
does not approach one-half. This explicit cost prevents promotion of a
correct local bound into a false bootstrap.

### G. Signed And Quantitative Relevance

| Coordinate Or Loss | Exact Source Relation | Remaining Bill |
| --- | --- | --- |
| Euler / FINITE-AC | Literal ordered Q, strict K, exact double-centered Xi and E are retained. | New strict complete Xi grade remains OPEN; root-subpower E is not a fixed-C root bound. |
| Square blocks / MU-LIFT | Q=2M(R-1)-M(R^2-1) is compiled; interval gaps can only be restored with the actual unit coefficient bound. | No full-prefix subcritical MU-LIFT recurrence has been supplied. |
| VF / actual primes | PP uses genuine prime pairs, with no density substitution in the exact finite source. | This is not pi-li, #915 clipping/admission, or a canonical first-bad theorem. |
| NNS / OAI | The displayed real square preserves all cross terms of THIS arithmetic carrier. | No isometry identifies it with ideal-labelled Hecke tuple coefficients or supplies the missing normalized LOW bound. |
| First irreversible loss | Absolute values after PP/PC/CC separation cost 4c A_R+o(A_R); the full prime-versus-rest split costs 2c A_R+o(A_R). | That tax has root exponent 2 and cannot fit the desired strict grade. |
| Paid recovery tested | Complete #1141 centering, historical Abel, prime-indicator inclusion-exclusion, and the paid Mertens comparator recover the coarse balance. | They do not independently improve the complete residual. #1128 phase near-resonance is a different Hermitian carrier. |

Neither positive cofactor fibres nor sign constraints on a proper sector
bound the total source. Complete cancellation is compatible with, and already
necessary for, the paid baseline. No stronger inverse/covariance premise is
introduced as if it were proved.

### H. Falsification And No-Circularity Review

Registration preceded the single arithmetic run. All primality, Mobius,
floor, mask, coefficient and identity checks used integers/Fraction.
The only logarithm check used rational atanh-series bounds with an explicit
positive remainder; no floating-point comparison or asymptotic fit was used.

| Check | Domain Or Exact Result |
| --- | --- |
| Independent arithmetic | Sieve versus trial factorization for 1..19321; 19,321 checks each for primes and Mobius. |
| Balanced literal kernel and nondivisor mask | Every ordered pair for R=2..128 plus held-out 139,257,317; 208,152 checks each. |
| PP formula, mixed and CC identities | 130 roots; prime-square endpoint exclusions checked on 9,692 ordered prime pairs. |
| Row variation and exact Abel | 4,258 rows each; upper bill 8 and all partial sums retained. |
| Complete Q, Xi and cross terms | R=2..64 plus held-out 101,139; 65 roots; exact endpoint, divisor union, four-way Xi square, two-way Xi square and strict-history Abel bound. |
| Negative prime band | 132 ordered pairs; first distinct-prime witness in the declared increasing-root domain: R=54, a=43, b=41, J=-54456/93439. |
| False all-entry sign | R=9,a=b=5,J=1/4; universal nonpositivity is rejected. |
| Omitted quotient jumps | First detections R=5 for jump 2 and R=9 for jump 3. |
| Missing orientation / square cross | R=8: mixed contribution 1/35; omitted four-way Xi cross sum 128/1225. |
| Deleted prime diagonal | R=5: exact omitted contribution -1/2. |
| Wrong divisor-prime admission | R=4: incorrectly including a=b=R-1=3 adds -2/3. |
| Constant | Rational certificate 0.084012<c<0.084014. |

Total: **483,964 assertions, PASS_EXACT**. Python syntax compilation passed.
Checker SHA256: `b5b5e704049f9aa3f8714cee8075a9f659c40d63c17f56838f01ff07514dd142`.
Registration SHA256: `9cd2e71fc96ef7f9b14d594f004dbe49b3ff5d095694de1d2effc7fa7b86992c`.
The exact large fractions and the program's finite sign variations are not
evidence for a limiting constant; PP2's all-scale argument is E2.

Novelty audit: current-main code searches for Xi, balanced primes, fractional
prime pairs, cubefree factor exchange, and the log(4/3) constant; relevant
November 16/17 reports; the original balanced-prime centering and #1128
near-resonance sources; and #1141/#1142's complete-kernel note. The old cubefree
sign grouping is PRIOR WORK, not a new theorem here. The prior balanced-prime
file uses u<v<2u in a different square shell and proves exact coefficient
centering, not this full Xi prime-sector asymptotic. Its algebra is credited.
No equivalent PP constant/class-balance theorem was found in this scoped
search. No exhaustive repository or literature novelty claim is made.

The new estimates either use PNT alone or explicitly reuse the already-paid
Mertens exponent. They do not prove that exponent again or imply a stronger
one. The full grade remains target-strength. No finite result, self-audit,
or green conditional consumer is substituted for the missing supplier.

### I. Conceptual Interpretation

Double-centering removes a specified continuous term, not every arithmetically
coherent mode. On actual prime pairs, both Mobius signs are negative and their
product is positive; the centered geometric kernel still has a nonzero signed
average. The complementary composite signs must restore it. The forced
-1:2:-1 balance identifies this requirement quantitatively on the new kernel.

This is source-specific supporting information and a decisive method test,
not a new general principle that coarse cancellation proves RH. Owner PC's
Selberg audit finds an analogous distinction between canceled main terms and
an unpaid residual on another source; neither result supplies the other's
missing estimate.

### J. Competing Structural Hypotheses And Route Memory

The separate-primality-class strict-grade mechanism is REFUTED. A
product-preserving sign reversal within the exhibited prime band is also
impossible at its literal source scope. The stronger whole-prime-block
pointwise sign is REFUTED and is not used to prove its aggregate limit.

A joint moving-hyperbola argument remains possible, but its cancellation
must cross the factor classes before absolute values and retain the entire
outside block and E. No new independent quantitative supplier for it was
found. Merely subtracting -c A_R and treating the resulting exact residual
as small would repeat the target-equivalent error.

FINITE-AC has now received the requested bounded Xi test after GD/SB.
CORR4 retains its first-owner signed mixed-tail consumer; MU-LIFT retains
its full-prefix r<k recurrence and chain coverage. No substantive new
CORR4 or MU-LIFT supplier is claimed or fabricated here. The half-bootstrap
policy permits bounded feasibility rather than a compulsory return to a
route lacking an independent mechanism. Do not count this scalar identity
as full-prefix MU-LIFT coverage or restart the accepted SB census.

### K. Specialist Handoffs

- Coordinator: close this particular classwise-payment feasibility test as REFUTED; retain PP2's exact constant and PP3's complete return as supporting paper results. No new route or implementation task is admitted.
- Owner Payment: the PP/PC/CC signs belong to the actual Q/Xi carrier, not clipped #915 occurrences. Any use in first-bad payment needs a genuine occurrence/weight bridge.
- Analytic Type II: a proposed joint estimate must beat the already-paid complete residual, not merely subtract the PNT main term. The row-Abel cost R^(b+1) does not improve R^(2b).
- Prime Census: no larger scan requested. An independent small reproduction may use R=9,54 and held-out 139, testing original signs, both jumps and every return. Finite data cannot certify PP2.
- Adversarial Referee: independently review E2's product-measure limit with exact square equality exclusion, E3's signed mixed-class orientation, and E4's full return. PP1-PP3 await that review; the author has not accepted them independently.
- Lean Verification: no proof-source edit or conditional wrapper is commissioned. Only consider a nonduplicate needed theorem after independent review and an explicit surviving downstream use. Current hosted evidence proves prior inputs, not PP.

These are report handoffs for later authorized actual invocations, not agent
launches, synchronized tasks, or promises of background execution.

### L. First Independently Missing Theorem

Still missing: an independently derived signed estimate on the COMPLETE
moving-hyperbola source that supplies a strict grade, or a genuinely different
complete-source mechanism with its own terminal consumer. The exact original
arithmetic must create a gain beyond the paid exponent; PNT class proportions,
centering, existing Abel, and the complete grade's reformulation do not do so.

The highest-value next decision is whether a concrete cross-factor mechanism
can control that residual WITHOUT separately estimating PP/PC/CC. In the
absence of such an independently motivated mechanism, park this split and
select another qualifying native continuation. Do not rerun its leading
constant census or rename rho as a new sufficient lemma.

### M. Continuity And Next-Run Resume Capsule

The full nontruncated reports tree was enumerated without a calendar cap.
All seven latest actual files are November 17, with completed publication
receipts. The full November 16 predecessor files were also retrieved. Both
dates' Coordinator mirrors were independently fetched and matched byte-for-byte.
The prior own SB ledger supplies the consumed watermark; relevant subsequent
sections were recovered in chronological order TC, IC, HF1, TAIL, PC, CP.
The scope is latest-real discovery and relevant backfill, not an assertion
that every historical numerical appendix was independently reviewed.

| Role / Latest Section | November 17 File Blob | Verified Substantive Commit / UTC Time |
| --- | --- | --- |
| Coordinator TAIL | ae2d8ed2c9199d5b0b174fd8b3436286f5541226 | a23911c4df515ba9b953ebc3b6fc02e6ea0d73de / 20:42:13 |
| Owner PC | 6516bf78b096471ccfd2fb8c215e94002544a594 | d26b9f690801cca97f1bf4831380989c45e7e93a / 21:41:44 |
| Analytic CP | d4bc53ac1b68f6dadabc4a04a2f5fc8c74f6625f | ef7fd73c318d34c76fdb3c3948da0ec56a6b6f9f / 22:29:05 |
| Wheel SB before PP | 49882b854f2df6d2ee426da70fa465d083733c78 | 7426a5cae2795c43c1176d20a562c09a41d96add / 15:40:21 |
| Census TC | 701a6d15ba711d9a4ca3677709802def12c46c07 | 3f15ce3d3fc76660e1625b72afbec74ae7145804 / 16:25:05 |
| Referee IC | 6e7f24cf5f790bab4ac1c19da6dc1c81546ad0e0 | 63fb53ef06a2752e42be83c370d5cde30ffc1005 / 17:31:10 |
| Lean HF1 | f064afb482138dc59123713f11082809b04e7c3c | 9b84c4db78cdb4af6beb7ba34dd9bde02d436199 / 18:42:44 |

These timestamps were checked against Git commit metadata, not schedules.
All paths are the role-owned November 17 files under research/agent_reports;
Coordinator's 00/90 are one role. Today=AVAILABLE, yesterday=READ/CARRY_FORWARD.
No new publication gap after SB was discovered. Previously recorded silent
November 13/14 folders remain NO_VERIFIED_REPORT, not invented executions.

November 16 carry-forward blobs in the same role order:
`fda92549dd9291c491005fdf70847b90d9be385a`,
`a52b439e693e069502b0c299a5f074a19bae0807`,
`84aaa2103225565607b5b033f273462bbe865246`,
`713826840694e39a141fbdbe813f1d47245928e7`,
`53e6be517dc11037fe3b42a8ed6ad3a06cfce956`,
`240b97ce1c8ddc87d5f520bc9a8cd6ea00df3d32`,
`0bada0352d54be7c46a7d928f4c4e3bee440ad8f`.
Relevant SC/DB/LM/TP/MC/CF/CR limitations remain in force: preserve the R=5
correction, R=137 restoration reversal, proper-region versus complete source,
and finite-prime-model versus genuine-Mobius distinctions. These tests were
not rerun merely for continuity.

IC's independently scoped ACCEPT_ON_PAPER verdicts include INV1-INV4,
HA1-HA3, TC1-TC2, HF1 and SB1-SB3; INV.9 is refuted at its all-head scope.
IC1-IC3, TAIL, PC and CP retain their own self-audit/pending-review status.
CP's simultaneous-small-defect condition is necessary, not sufficient.
No report is upgraded wholesale by a single accepted claim.

External inbox `7d63d434690d00dffce9c90335d41c4f62d85798` was retrieved and
is unchanged, with no entry after October 18. EXT-20261018-PNT-1 retains its
complete cofactor-weighted error; EXT-20261014-5 is an unconditional fraction
obstruction, not a disproof of a conditional first-bad strategy.

The PP checkpoint was committed at 23:10:58 UTC as
`4873630e09c4d30aff5cc2877bd996dfedd75eaa`, blob
`644a70a0375842cddabe94d55d57e2a3eef02a8e`; immutable readback matched exactly.

```text
RUN=20261117-wheel-1806-EST/PP; PLATFORM_RUN_ID=UNAVAILABLE
ROUTE=FINITE-AC complete-Xi bounded feasibility; no new route admission
SOURCE=original Q and strict K; full Xi, both divisor orientations, E
START=every-positive-loss b_base=7/8-7/(64*N_pack); fixed 7/8 spent legally
PP1=exact prime-band negativity and endpoint geometry; PAPER_PROOF/SELF_AUDIT
PP2=PP~-((log(9/2)-1)/6)R^2/log^2 R; PAPER_PROOF/SELF_AUDIT, ordinary PNT
PP3=three-class -1:2:-1 balance and entire return; PAPER_PROOF/SELF_AUDIT
PP4=483964 exact assertions; stronger universal entry sign REFUTED
CLASSWISE_STRICT_GRADE=REFUTED; JOINT_SUPPLIER=OPEN
ADVANCE=conditional existing lambda1 eta=(b-1/2)/2 map, gap factor3/4
RENEWAL=requires new complete arithmetic at every fixed b>1/2; NOT supplied
RETURNS=both jumps, ordered multiplicities, prime diagonals, mixed classes,
        outside balanced block, divisor union, linear term and all cross terms
STATUS=BOUNDED_FEASIBILITY_COMPLETE / SUPPORTING_PAPER_RESULT
INDEPENDENT_REVIEW=PENDING; NEW_LEAN=NONE; CI=REUSED_ONLY
NO_NEW_GLOBAL_GAIN; VERIFIED_ETA=NONE; RH=OPEN
NEXT=independent scoped PP review or a new genuinely joint source mechanism;
     no larger unchanged scan, no wrapper, no pointwise sign extrapolation
PUBLICATION=READBACK_PENDING until the verified receipt below
```

Direct git clone failed with CONNECT tunnel HTTP 403; authenticated connector
reads and authorized report writes worked. No proof source, main, shared
policy, other report, proof branch/PR, workflow, schedule or permission was
changed; no agent was launched. All necessary computation processes finished.

### N. Reproducibility Appendix

The following are the exact registered and executed files. They use Python's
standard library only. The report is the durable copy; no external scratch
file is required to inspect the methodology. Run the checker with its
registration file beside it to reproduce the checks and hashes.

#### N1. Pre-Execution Registration

~~~~text
# PP Exact Verification Registration

Run: 20261117-wheel-1806-EST/PP. Registered before arithmetic execution.

1. Use genuine Mobius values from a sieve, independently verified by trial
factorization. Original source is the complete ordered square 1<=a,b<R,
N=R-1, X=R^2-1. Use exact fractions throughout.
2. Exhaust all balanced pairs at R=2..128, held-out R=139,257,317.
Check the literal fractional kernel against its two-hyperbola formula,
the nondivisor mask, endpoint equality exclusion for prime pairs, exact
prime-count formula, and total row variation plus last value <=8.
3. On R=2..64 and held-out R=101,139, reconstruct every original term,
Q=2M(N)-M(X), the divisor union once, Xi, and PP/mixed/CC/outside.
Check all four-way square terms, the two-way square, and the historical
row-Abel bound by squaring exact rational inequalities. No square root
or fitted exponent is evaluated in binary floating point.
4. Check every prime pair in 3R/4<p,q<=4R/5, R>=10, satisfies J<=-1/2.
Keep diagonals and both ordered orientations. Record the first genuine
distinct-prime witness, not merely a diagonal artifact.
5. Negative controls: omit the quotient-2 or quotient-3 jump, omit an
ordered mixed orientation, omit prime diagonals, include the forbidden
R-1 prime row, or discard quadratic cross terms. Require a witness for
each. Test the stronger all-balanced-prime-entry nonpositive claim;
if false, record its first genuine counterexample instead of asserting it.
6. Certify c=(log(9/2)-1)/6>0 with rational atanh-series bounds. The
PNT asymptotic is a paper proof, not a finite-test conclusion. No large
prime census, asymptotic fit, or local Lean execution is commissioned.
~~~~

#### N2. Executed Checker

~~~~python
from collections import Counter
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import hashlib
import json


COUNTS = Counter()
WITNESSES = {}


def check(label, statement):
    assert statement, label
    COUNTS[label] += 1


def record(label, condition, value):
    if condition and label not in WITNESSES:
        WITNESSES[label] = value


def factor(n):
    out = []
    p = 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            out.append((p, e))
        p += 1
    if n > 1:
        out.append((n, 1))
    return out


def sieve(limit):
    mu = [1] * (limit + 1)
    prime = [True] * (limit + 1)
    prime[0] = prime[1] = False
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p, limit + 1, p):
                mu[n] *= -1
                if n != p:
                    prime[n] = False
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
    mu[0] = 0
    return mu, prime


def kernel(R, a, b):
    N, P, X = R - 1, R + 1, R * R - 1
    return F(P * (N % a) * (N % b) - N * (X % (a * b)), N * a * b)


def balanced_kernel(R, a, b):
    X, P = R * R - 1, R + 1
    return 1 + F(P, R - 1) - F(P, a) - F(P, b) + int(2*a*b <= X) + int(3*a*b <= X)


def log_bounds(x, terms=160):
    z = (x - 1) / (x + 1)
    lo = 2 * sum((z ** (2*j + 1) / (2*j + 1) for j in range(terms)), F())
    err = 2 * z ** (2*terms + 1) / ((2*terms + 1) * (1-z*z))
    return lo, lo + err


def main():
    mu, prime = sieve(139**2)
    M = [0]
    for n in range(1, len(mu)):
        fac = factor(n)
        expected = 0 if any(e > 1 for p, e in fac) else (-1)**len(fac)
        check('independent_mu', mu[n] == expected)
        check('independent_prime', prime[n] == (fac == [(n, 1)]))
        M.append(M[-1] + mu[n])

    roots = list(range(2, 129)) + [139, 257, 317]
    full_roots = set(range(2, 65)) | {101, 139}
    rows = []
    for R in roots:
        N, P, X = R-1, R+1, R*R-1
        I = list(range(R//2 + 1, R-1))
        primes = [a for a in I if prime[a]]
        Tpp = Tpc = Tcc = W = F()
        H2 = H3 = 0
        for b in I:
            row = []
            partial = 0
            maximum = 0
            signed_row = F()
            for a in I:
                J = kernel(R, a, b)
                check('balanced_kernel', J == balanced_kernel(R, a, b))
                check('balanced_nondivisor', N % a != 0 and N % b != 0)
                row.append(J)
                partial += mu[a]
                maximum = max(maximum, abs(partial))
                signed_row += mu[a] * J
                value = mu[a] * mu[b] * J
                if prime[a] and prime[b]:
                    Tpp += value
                    H2 += 2*a*b <= X
                    H3 += 3*a*b <= X
                    check('prime_pair_original_sign', mu[a]*mu[b] == 1)
                    check('prime_square_clock_no_equality', 2*a*b != R*R and 3*a*b != R*R)
                    record('positive_prime_entry', J > 0, {'R': R, 'a': a, 'b': b, 'J': str(J)})
                    if R >= 10 and 3*R < 4*a and 5*a <= 4*R and 3*R < 4*b and 5*b <= 4*R:
                        check('negative_band_exact_endpoints', 5*a <= 4*R and 5*b <= 4*R)
                        check('negative_band', J <= F(-1, 2))
                        record('negative_band_distinct', a != b,
                               {'R': R, 'a': a, 'b': b, 'J': str(J)})
                elif prime[a] or prime[b]:
                    Tpc += value
                else:
                    Tcc += value
                if prime[a]:
                    W += value
            if row:
                variation = abs(row[-1]) + sum(abs(v-u) for u, v in zip(row, row[1:]))
                check('row_variation', variation <= 8)
                check('row_abel', abs(signed_row) <= variation * maximum)
        nP = len(primes)
        V = sum((F(1, p) for p in primes), F())
        formula = (1 + F(P, N))*nP*nP - 2*P*nP*V + H2 + H3
        check('prime_count_formula', Tpp == formula)
        check('mixed_full_identity', Tpc == 2*W - 2*Tpp)
        balanced = Tpp + Tpc + Tcc
        check('composite_full_identity', Tcc == balanced + Tpp - 2*W)
        record('omit_jump_2', H2 != 0, {'R': R, 'missing': H2})
        record('omit_jump_3', H3 != 0, {'R': R, 'missing': H3})
        record('omit_mixed_orientation', Tpc != 0, {'R': R, 'mixed': str(Tpc)})
        diagonal = sum((kernel(R, p, p) for p in primes), F())
        record('omit_diagonal', diagonal != 0, {'R': R, 'diagonal': str(diagonal)})
        if prime[N] and 2*N > R:
            forbidden = sum((2*kernel(R, N, p) for p in primes), kernel(R, N, N))
            record('include_divisor_prime', forbidden != 0,
                   {'R': R, 'prime': N, 'wrong_extra': str(forbidden)})
        if R in full_roots:
            Q = 0
            Xi = Div = source = F()
            for a in range(1, R):
                for b in range(1, R):
                    c = mu[a]*mu[b]
                    Q += c*(X//(a*b))
                    value = c*kernel(R, a, b)
                    source += value
                    if N % a == 0 or N % b == 0:
                        Div += value
                    else:
                        Xi += value
            mR = sum((F(mu[a], a) for a in range(1, R)), F())
            linear = 2*P*mR - F(P, N)
            check('complete_q_endpoint', Q == 2*M[N] - M[X])
            check('full_centered_source', Q == linear + source)
            check('once_only_divisor_union', source == Div + Xi)
            outside = Xi - balanced
            parts = [Tpp, Tpc, Tcc, outside]
            check('complete_partition', sum(parts) == Xi)
            diagonal_squares = sum(v*v for v in parts)
            cross = 2*sum(parts[i]*parts[j] for i in range(4) for j in range(i+1, 4))
            check('complete_four_way_square', Xi*Xi == diagonal_squares + cross)
            Vcomp = Xi-Tpp
            check('complete_two_way_square', Xi*Xi == Tpp*Tpp + Vcomp*Vcomp + 2*Tpp*Vcomp)
            record('omit_cross_terms', cross != 0, {'R': R, 'cross': str(cross)})
            K = max(F((M[y]-1)**2, y+1) for y in range(R))
            check('strict_history_balanced_bound', balanced*balanced <= 64*R**3*K)
            if R in [14, 32, 64, 101, 139]:
                rows.append({'R': R, 'prime_count': nP,
                             'PP': str(Tpp), 'mixed': str(Tpc), 'CC': str(Tcc),
                             'outside': str(outside), 'Xi': str(Xi), 'Q': Q,
                             'K': str(K), 'cross': str(cross)})

    lo, hi = log_bounds(F(9, 2))
    clo, chi = (lo-1)/6, (hi-1)/6
    check('positive_main_constant', F(84012, 1000000) < clo < chi < F(84014, 1000000))
    for name in ['omit_jump_2', 'omit_jump_3', 'omit_mixed_orientation', 'omit_diagonal',
                 'include_divisor_prime', 'omit_cross_terms', 'positive_prime_entry',
                 'negative_band_distinct']:
        check('control_'+name, name in WITNESSES)
    print(json.dumps({'status': 'PASS_EXACT', 'checks': dict(COUNTS),
                      'assertions': sum(COUNTS.values()), 'witnesses': WITNESSES,
                      'rows': rows, 'constant_interval': ['0.084012', '0.084014'],
                      'infinite_inference_from_tests': False,
                      'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                      'registration_sha256': hashlib.sha256(Path(__file__).with_name('pp_registration.md').read_bytes()).hexdigest()}, indent=2))


if __name__ == '__main__':
    main()
~~~~

### O. Prepublication Validation

At 2026-11-17 23:21:22 UTC the refreshed main remained
13b31c6313e274a073d82a01175201185e59e37e. The nontruncated report tree
at 4873630e09c4d30aff5cc2877bd996dfedd75eaa differs from intake only in this
owned PP checkpoint; no intervening upstream report or external handoff was
missed. The latest inspected open/draft collection was empty.

The complete new A-M synthesis, source hashes, exact checker and registration
bytes, ASCII, Markdown tables/fences, constant order, source masks, both
ordered orientations, diagonals and full quadratic return were checked.
All 483,964 arithmetic assertions and syntax compilation completed successfully.
The new estimates remain self-audited paper results, not independently
accepted or Lean-certified. This preparation paragraph does not certify its
own publication. An immutable commit/readback receipt follows after success.


### P. Verified PP Publication Receipt

The substantive PP synthesis and exact reproducibility bundle were committed
at 2026-11-17 23:22:11 UTC (18:22:11 America/New_York) in
[5fa41b6b2318f5646c7078baaf4abf7bdc30f981](https://github.com/OVVO-Financial/RH_Lean/commit/5fa41b6b2318f5646c7078baaf4abf7bdc30f981).
The resulting report blob is
`01ef1b0649183b996244913ba5cff29bd93148f3`.

At 2026-11-17 23:25:43 UTC the immutable blob was read back and matched all
161,471 submitted ASCII bytes exactly. The nontruncated tree at that exact
commit separately binds this owned report path to the same blob and byte
count. A stalled large path-content read was replaced by this immutable
blob-plus-tree verification; the stalled read is not counted as evidence.

The comparison against checkpoint
`4873630e09c4d30aff5cc2877bd996dfedd75eaa` reports exactly one changed file,
this report, with 863 additions and zero deletions. All preexisting report
bytes were preserved. The subsequent nontruncated agent-reports refresh
still showed no changed upstream handoff or external inbox since intake:
only this owned report differed.

Publication status of sections A-O: **VERIFIED**.
Mathematical status is unchanged: the stated all-scale PP results are
**SELF_AUDIT, INDEPENDENT_REVIEW_PENDING**, not Lean-certified; the
483,964 successful exact assertions are finite verification, not an
infinite proof. The pointwise nonpositivity strengthening is refuted by
the recorded genuine prime example. The obstruction applies to the
specified separate-class strict-grade method, not every joint signed method.

No main/source file, other agent report, branch, PR, CI workflow, or schedule
was changed or launched. No new global gain or endpoint theorem is claimed.
The canonical global obligation remains open. Next action is independent
review of the source-specific prime-sector constant and joint cancellation
ledger; no unchanged census rerun or filler formalization is requested.
