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
