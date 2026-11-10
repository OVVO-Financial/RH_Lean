# RH | Finite Wheel & Incidence - 2026-11-10

## Early Checkpoint - 20261110-wheel-1/PC

### A. Most Important Structural Question

IN_PROGRESS. Can independently choosing a different saturated lower-owner prefix in EACH genuine large-prime fibre remove the large fibre costs found by Owner HM? Investigate prime-rank convexity of the actual adjunction increments, the exact minimum attainable by each fibre, and the compulsory positive population near the lower edge q=R. No new result, independent acceptance, Lean proof or endpoint gain is claimed at this checkpoint.

### B. Current Authoritative Objective

Scheduled invocation: 2026-11-10 02:05:01 EST, America/New_York.
Checkpoint prepared: 2026-11-10 07:14 UTC.
MAIN=7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9.
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.
AGENTS=6695522a45d67fd1e80a7cff1f98d909405036e2.
CONTRACT=95566e37c8eaeb99ee680660df4f9d2e06ea5038.
DIRECTIVE=e505f35522b675c6b5b263eac73618d717346973.
COMPLETE_WHEEL_SOURCE=ecb482e52deeee5e9b3853592a3ffdace662d2ff.
ROOT_ADMISSION_SOURCE=a412632c1028d7728cd8d87ee6e5ac365377d338.

For integer R>=2, X=R^2-1, y=R-1, P_y=product_(prime p<=y)p,
F_R=sum_(d|P_y)mu(d)fract(X/d),
D_R=X delta(y)+pi(y)-1-li(X),
Z_R=F_R-D_R=li(X)-pi(X).
OPEN: exists ONE C>=0, forall R>=2, |Z_R|<=C R log R.
The li reference is principal-value li. Every virtual divisor stays until its own Euler compensation; d=X and q=R primes stay. The canonical VF statement and its explicit classical-criterion interface are unchanged.

### C. Continuity And Selected Source

Report snapshot b6efd2c5d2ce340f4bd6ce614d9a72df564e56f5.
November 10 Owner HM is available at blob 2bed3da8ed4ddd49c0708378a1c3da5b4883cb54; Analytic HF at d8337353a94b465f53a0c6a65ad46aac1dc1927e. Both remain paper/self-audit at their stated scopes. Other upstream November 10 stages are TODAY=PENDING; use YESTERDAY=CARRY_FORWARD, not an inferred scheduled completion.

November 9 intake: Coordinator 6fba43130391ad4a606aa3809c20f344d668c709; Owner 643e8a004d9d8e0be102b03e2f79bb3b217ae916; Analytic d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3; own Wheel 0624246d03b19cf76c01e186b7d868a248d896ef; Census 8c927cc6c323533ba1cfd369404b25aa4f9cef91; Referee a5d0192eb31c0efb3767187a7752f1a0d07f8534; Lean 8b60c6136ac151774be2db0aee8f543f286b53aa. Coordinator mirrors agree. Relevant latest mathematical sections and the external inbox were read. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry after October 18; retain EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 for source/endpoint/noncircularity safeguards, not superseded task selection.

Carry forward CF and its actual independent Referee AP acceptance; AP's adaptive scalar payment and Coordinator CD's fixed-cutoff failures; HM's common-cutoff affine reciprocal profile and transverse bound; HF's claimed entire high-frequency exponent 71/52+epsilon (not an endpoint theorem); RA's already-certified root-admission bound; RF/NC's restricted matching costs with unmatched source still open. No unchanged reflection or wheel census is planned.

Actual PR metadata: #1124/#1125/#1126 are merged; #1127 is the sole open non-draft PR at 866b3d2121309cdd854f9d64e2a6adbbc708ef9b. #1125's prior missing dedicated compilation evidence is not erased by merge. Exact relevant execution evidence will be checked before final status. No new formal certification claimed here.

### D. Registered Structural Investigation And Finite Tests

For R>=8, Q={prime q:R<=q<2R}, x_q=X/q, r_q=fract(x_q),
h=floor((R-1)/2), H=pi(h), W=delta(h)-delta(R-1),
Zcut={integers z:2<=z<R/2, z^2>=R}, and w_p=delta(p-1)/p, use the EXACT original row
T_q(z)=sum_(prime p<=z or R/2<=p<R)[N_p(floor(x_q))-x_q*w_p],
N_p(t)=#{2<=a<=t:leastPrime(a)=p}.
CF/AP/HM give T_q(z)=[delta(z)-W]x_q+pi(z)-H-1-r_q.
The q is a physical mask, NOT another Mobius sign. Each physical aq is unique within R.

New hypothesis class: permit an arbitrary choice z_q in Zcut independently for every q, without fractional ownership or duplicate sites. Test whether all rows can be small, and derive the strongest genuine uniform restriction if not. Inspect the ordered prime increments 1-x_q*w_p and their dependence on q. Investigate whether the positive part of cR/q-1/2, c=exp(-gamma), governs the optimized fibre cost. This is a proof-led candidate, not a numerical finding.

Frozen exact test domain BEFORE execution: EVERY R=8..128, every admissible integer cutoff, and every q in Q; held-out R=257,549,1024 with the same full cutoff test. Compare saturated formula to a separate least-prime physical implementation, test convexity in PRIME RANK (not integer coordinate), minimum/crossing claims and all proposed fixed constants using Fraction arithmetic. Record the first failure of the stronger each-row |T_q|<=1/2 existence assertion. R=2,3 empty/first-wheel controls, R=14 d=X=195, prime q=R, and squareful cofactors must remain. Finite data do not prove asymptotics or give an unstated large-root onset.

### E-M. Remaining Work And Permission Boundary

Derive the finite theorem and a complete paper proof of any asymptotic conclusion using independently checked PNT/Mertens inputs, or preserve the precise failed argument. Restore every complementary owner and cross-fibre interaction before explaining scope. New results will be SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED unless actual evidence changes that status. Only this own report is authorized for remote changes. No Lean execution, main/branch/PR/other-report change, agent launch or schedule change.

## Prime-Rank Convexity And The Failure Of Fibrewise Optimization
### Final Research Synthesis - 20261110-wheel-1/PC

### A. Most Important Structural Discovery

**Even allowing a DIFFERENT saturated lower-owner cutoff for every genuine large-prime fibre does not make the fibres separately affordable. Optimizing each fibre independently leaves a positive SIGNED aggregate of order R^2/log^2 R.** Thus the known small common-prefix total genuinely needs large contributions of opposite signs across different q; replacing it by locally optimal absolute residuals destroys that cancellation.

Write c=exp(-gamma), L=log R. For the exact rows T_q(z) defined below, let e_R(q)=min_z |T_q(z)|, over ALL saturated cutoffs, not a fixed proportional bracket. Then

~~~text
sum_(R<=q<2R, q prime) e_R(q)
  ~ kappa_1 R^2/L^2,
sum_(R<=q<2R, q prime) e_R(q)^2
  ~ kappa_2 R^3/L^3,

kappa_1=c log(2c)-c+1/2 > 0,
kappa_2=c^2-c log(2c)-1/4 > 0.
~~~

Every selection attaining those individual absolute minima has signed total asymptotic to the SAME positive kappa_1 R^2/L^2. These estimates use ordinary unconditional PNT and Mertens' finite-product limit, not RH, the native 7/8 theorem, or a fitted constant.

The exact structural mechanism is prime-rank convexity: each newly selected prime p adds the ONE physical cofactor p, with its original Euler-reference defect 1-X*delta(p-1)/(p*q). These increments strictly increase with p. Unique factorization and parity also give a sharp exceptional classification: a zero prime increment is possible ONLY at (R,p,q)=(16,5,17). Integer-cutoff plateaus are different and remain.

| Claim ID | Result | Evidence class |
| --- | --- | --- |
| 20261110-wheel-1/PC1 | Exact prime-rank convexity, nested minimizing ranks, and unique zero-prime-adjunction classification | PAPER_PROOF; genuine original-source restriction |
| PC2 | Uniform sharp minimum profile and finite half-unit crossing estimate | PAPER_PROOF; independent of AP's adaptive bracket |
| PC3 | Sharp optimized L1/L2 costs and failure of greedy fibrewise SIGNED payment | PAPER_PROOF / REFUTED scoped auxiliary strategy |
| PC4 | Every affordable assignment must retain macroscopic negative cross-fibre mass | PAPER_PROOF; explicit finite inverse restriction |
| PC5 | Registered exact tests, small counterexamples and complete-source boundary checks | FINITE_COMPUTATION |

All NEW PC claims are **SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. They have not been accepted by an independently executing Referee or proved in Lean. NEW_VERIFIED_GLOBAL_ENDPOINT_GAIN=NONE. Complete-wheel RH bound, canonical VF, finite A/C and RH remain OPEN.

### B. Current Authoritative Objective

Main remains pinned to 7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9; finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1. The exact target and authority SHAs are preserved in the checkpoint.

The original source is [CompleteSquareRootWheelFractionalBoundary.lean](https://github.com/OVVO-Financial/RH_Lean/blob/7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9/research/CompleteSquareRootWheelFractionalBoundary.lean). Its arbitrary-reference theorem finiteWheel_squareFractional_centered_eq_reference_sub_pi establishes F_R-D_R=li(R^2-1)-pi(R^2-1), not a bound. The required ONE constant uniform over R in |F_R-D_R|<=C R log R remains unpaid.

Material original declarations read:

| File | Blob SHA and scope |
| --- | --- |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff; full divisor, fractional, physical/virtual, Euler and Legendre source |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58; actual positive survivor count and finite prime Euler density |
| research/CompleteWheelRootAdmission.lean | a412632c1028d7728cd8d87ee6e5ac365377d338; already-paid RA prime-root component, with physical-shell term retained |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb; canonical goal and explicit ClassicalVonKochRHCriterion consumer |
| docs/DYNAMIC_RESEARCH_AGENTS.md | e8d913ff9663bb5163eaf0eddca9f76e0508a7ef; own-report-only and evidence protocol |

The public canonical goal is VFCanonicalSquareVonKochStatement. Its terminal riemannHypothesis_of_vfCanonicalSquare still takes ClassicalVonKochRHCriterion explicitly. The current finite-wheel equality is an exact source adapter, not a construction of that classical interface.

This investigation uses no new zero boundary and makes no changed Mertens exponent claim. Analytic HF's reported high-frequency exponent 71/52+epsilon is relevant current paper work, independently unreviewed here and NOT a premise of PC.

### C. Structural Mechanism Investigated

Prior credit: CF introduced the genuine large-prime mask and Euler allocation; Referee AP independently accepted CF and derived a saturated scalar prefix; Coordinator CD accepted AP's displayed source reconstruction and analyzed fixed cutoffs; today's Owner HM derived the individual-row formula and common-cutoff reciprocal profile. Their identities and accepted conclusions are not new PC claims.

HM's uniform common-cutoff diagonal obstruction does not automatically cover DIFFERENT choices z_q for each q. The latter destroys the common affine-line restriction and is a genuine enlargement of the candidate allocation class. PC investigates this enlargement rather than repeating a common-prefix scan.

The tested optimistic mechanism was: tune each genuine fibre separately to a small residual, then add the results. The competing mechanism was: saturation and the finite Euler factors impose a positive lower envelope on a nonempty interval of actual q, so local optimization cannot replace deliberate cross-fibre cancellation.

No extra donor, fractional coefficient, modified reference, or conjectural partner is admitted. The finite source is unchanged; only the partition of its already-existing owner cells varies.

### D. Exact Theorem Statements

For EVERY integer R>=8 define

~~~text
X=R^2-1, y=R-1, h=floor((R-1)/2), a=ceil(sqrt R),
Q={prime q:R<=q<2R}, m=#Q,
Zcut={integers z:a<=z<=h},
delta(s)=product_(prime r<=s)(1-1/r),
w_p=delta(p-1)/p, W=delta(h)-delta(y),
H=pi(h), x_q=X/q, r_q=fract(x_q).

N_p(t)=#{integers 2<=n<=t:leastPrime(n)=p},
T_q(z)=sum_(prime p<=z or R/2<=p<R)
                    [N_p(floor(x_q))-x_q*w_p].
~~~

The set Zcut is nonempty for R>=8. It is exactly the checkpoint's domain 2<=z<R/2, z^2>=R. All sums in this report are over the indicated genuine primes, with q=R included when prime. Each physical integer nq has n<R<=q; it cannot be assigned to two distinct Q fibres because qq'>=R^2>X.

The credited CF/AP/HM identity is

~~~text
T_q(z)=[delta(z)-W]x_q+pi(z)-H-1-r_q.             (PC.1)
~~~

Define finite minima, without any asymptotic assumption:

~~~text
v_R(q)=min_(z in Zcut) T_q(z),
e_R(q)=min_(z in Zcut) |T_q(z)|,
P_min(R)=sum_Q max(v_R(q),0),
A_1(R)=sum_Q e_R(q), A_2(R)=sum_Q e_R(q)^2.
~~~

**PC1. Prime-rank convexity and the exceptional zero.** List primes a<p_1<...<p_k<=h and regard a,p_1,...,p_k as the distinct prime-rank states. For every q in Q the successive increments are strictly increasing:

~~~text
T_q(p_j)-T_q(p_j-1)=1-x_q*w_(p_j),
1-x_q*w_(p_j) < 1-x_q*w_(p_(j+1)).               (PC.2)
~~~

A minimizing state is reached after exactly the negative increments; there are two adjacent minimizing states only if one increment vanishes. The first minimizing rank is nonincreasing as q increases. A prime increment vanishes if and only if

~~~text
(R,p_j,q)=(16,5,17).                              (PC.3)
~~~

At this exception T_17(4)=T_17(5)=T_17(6)=1450/1001. The last equality is a composite-cutoff plateau, not another prime increment. No uniqueness of an INTEGER cutoff inside a prime gap is asserted.

**PC2. Finite and uniform minimum laws.** For every q and every allowed z,

~~~text
T_q(z) > delta(y)*x_q-H-2.                        (PC.4)
~~~

Whenever T_q(h)>=0, the exact finite crossing bound is

~~~text
max(v_R(q),0) <= e_R(q) <= max(v_R(q),0)+1/2.      (PC.5)
~~~

The endpoint condition holds for ALL q in Q once R is sufficiently large, by the independent classical inputs below. Writing c=exp(-gamma), L=log R, the following uniform limits hold:

~~~text
sup_(q in Q) |(L/R)v_R(q)-(cR/q-1/2)| -> 0,
sup_(q in Q) |(L/R)e_R(q)-max(cR/q-1/2,0)| -> 0.  (PC.6)
~~~

In particular, for EVERY fixed lambda with 1<lambda<2c there is R_lambda such that for every R>=R_lambda, every q in Q with q<=lambda R, and EVERY z in Zcut,

~~~text
T_q(z) >= (1/2)(c/lambda-1/2) R/L > 0.            (PC.7)
~~~

The constants and threshold precede q,z. This excludes arbitrary per-fibre cutoff tuning on an entire genuine prime population, not just one common choice.

**PC3. Sharp optimized costs and greedy failure.** As R tends to infinity through integers,

~~~text
P_min(R) ~ A_1(R) ~ kappa_1 R^2/L^2,
A_2(R) ~ kappa_2 R^3/L^3,
kappa_1=integral_1^(2c)(c/u-1/2)du
       =c log(2c)-c+1/2>0,
kappa_2=integral_1^(2c)(c/u-1/2)^2 du
       =c^2-c log(2c)-1/4>0.                    (PC.8)
~~~

Since the finite choices are independent, A_1 is the MINIMUM of sum_Q |T_q(z_q)| over ALL assignments z_q in Zcut, and A_2 is the analogous minimum sum of squares.

For every assignment attaining each individual absolute minimum, put E_opt=sum_Q T_q(z_q). Once all endpoints T_q(h) are nonnegative,

~~~text
A_1(R)-m <= E_opt <= A_1(R).                     (PC.9)
~~~

Consequently, uniformly over all choices of minimizing cutoffs,

~~~text
E_opt ~ kappa_1 R^2/L^2.                        (PC.10)
~~~

For EVERY C>=0, all sufficiently large R and EVERY such greedy assignment have E_opt>C R log R. Moreover every arbitrary saturated assignment has sum |T_q|>=A_1 and sum T_q^2>=A_2; neither of these separate norms can uniformly satisfy the respective RH-sized budgets O(R log R), O(R^2 log^2 R).

This is a no-go for the stated LOCAL optimization/norm strategies, not a no-go for a small signed sum using nonoptimal rows. AP already supplies such a small proper-packet sum with a common cutoff.

**PC4. Forced negative mass for any affordable assignment.** For ANY saturated assignment, let

~~~text
E=sum_Q T_q(z_q),
P=sum_Q max(T_q(z_q),0), N=sum_Q max(-T_q(z_q),0).
~~~

Then, at every finite root,

~~~text
P>=P_min(R), E=P-N, N>=P_min(R)-|E|.             (PC.11)
~~~

Thus for a fixed C, any assignment with |E|<=C R log R must, eventually uniformly over all assignments, satisfy

~~~text
N >= (kappa_1/2) R^2/L^2.                       (PC.12)
~~~

Those negative rows cannot come from q<=lambda R for any fixed lambda<2c once R>=R_lambda. The exact signed aggregate square is P^2+N^2-2PN; the negative mixed term is essential, not replaceable by a sum of local squares.

### E. Mathematical Proofs

#### Source Reconstruction Before Optimization

For q in Q, floor(x_q)<R and floor(x_q)>=h. If z in Zcut, each composite cofactor n<R has a prime factor <sqrt R<=z. The unremoved cofactors after all owners <=z are exactly one and primes above z. Therefore

~~~text
sum_(p<=z)N_p(floor(x_q))
 =floor(x_q)-1-pi(floor(x_q))+pi(z).
~~~

An upper owner p>=R/2 cannot divide a composite cofactor n<R for R>=8. Its total count is pi(floor(x_q))-H. These actual prime-count terms cancel; their reference sums are 1-delta(z) and W. This proves (PC.1), independently reconstructing the credited identity with its original coefficients.

At an added prime a<p<=h, p^2>R>floor(x_q) and p<=floor(x_q). Consequently N_p(floor(x_q))=1: the one physical cofactor is p itself. It retains coefficient 1 and reference x_q*w_p. This proves the exact original-source adjunction rule (PC.2).

The full signed fractional representation is

~~~text
N_p(floor(x_q))-x_q*w_p
 =-sum_(d|P_(p-1))mu(d)fract(X/(p*q*d)).
~~~

The q is a physical mask, not a wheel prime. No mu(q*d) is inserted. All divisors are retained before Euler/floor cancellation, including p*q*d>X.

#### PC1: Convexity, Nested Minima, And Unique Flat Prime Step

For consecutive primes p<p' the original Euler product satisfies

~~~text
w_(p')/w_p=(p-1)/p'<1.
~~~

For nonconsecutive primes there are further positive factors below one, so strict decrease still holds. Since x_q>0, the prime increments 1-x_q*w_p strictly increase. This is discrete convexity in PRIME RANK. The negative increments form an initial segment and there is at most one zero increment, proving the minimizing-state statement.

As q increases, x_q decreases, so every increment increases. The number of negative increments cannot grow. This proves nested minimizing ranks without assuming that T_q itself is monotone in q; HM already refuted that different statement.

For the zero classification, put U=product_(prime r<p)(r-1), V=product_(prime r<p)r. Equality 1-x_q*w_p=0 is

~~~text
X*U=p*q*V.
~~~

Every prime factor of U is <p<R<=q. Thus q divides X=(R-1)(R+1). Since q>=R, it must equal R+1. Cancelling q gives (R-1)U=pV. Also p does not divide U, hence R-1=p*k for some positive integer k, and kU=V.

Here p>=5 because p>a>=3. If p>=7, U contains the factors 3-1=2 and 5-1=4, so 8 divides kU. But V is squarefree and contains just one factor 2, so 4 does not divide V: impossible. For p=5, U=2,V=6, hence k=3, R=16, q=17. These values satisfy all carrier conditions and give the displayed zero step and row value. This is a uniform arithmetic classification, not an extrapolation from the finite scan.

Nonzero rational increments do NOT by themselves give a scale-uniform lower bound: their denominators grow. PC2-PC3 supply their separate quantitative argument.

#### PC2: Uniform Optimization Without An RH-Strength Input

Because z<=h,

~~~text
delta(z)-W=delta(z)-delta(h)+delta(y)>=delta(y).
~~~

Insert pi(z)>=0 and 0<=r_q<1 in (PC.1) to obtain (PC.4). If v_R(q)>0, e_R(q)=v_R(q). If v_R(q)<=0<=T_q(h), take a minimizing state and proceed to h. Either a row is exactly zero or a first nonnegative prime step crosses zero. Its positive size is at most 1 by (PC.2). One of the two unchanged neighboring states has absolute value at most 1/2. This proves (PC.5). It is a local finite argument, not an assumption that every fibre has a sign crossing.

Only these established unconditional inputs are used: pi(t)~t/log t, from [NIST DLMF 27.12](https://dlmf.nist.gov/27.12), and delta(t)log t->c, stated in the primary paper [Diamond-Pintz, Mertens product formula](https://www.numdam.org/item/JTNB_2009__21_3_523_0/). No fine prime-gap theorem, independence, RH-sized error, or zero-density estimate is used. The deductions that follow are source-specific proofs in this report, not assertions quoted from those references.

The constant obeys 1/2<c<1. For example convex integral comparison gives gamma<=1-log(3/2), hence c>=3/(2e)>1/2 since e<3; gamma>0 gives c<1. Thus the interval (1,2c) is nonempty.

Let z_0=floor(R/L^2). For all sufficiently large R it belongs to Zcut: R/L^2 grows faster than sqrt R and slower than R/2. Also

~~~text
delta(y)L -> c, delta(h)L -> c,
delta(z_0)L -> c, W*L -> 0,
H*L/R -> 1/2, pi(z_0)L/R <= 1/L -> 0.
~~~

The last bound needs only pi(z_0)<=z_0. The third limit follows from log(z_0)/L->1 and the Mertens product limit; it is not a fixed-cutoff estimate applied outside its uniform range.

For every q simultaneously, x_q/R=R/q+O(R^-2), with 1/2<R/q<=1. The lower bound (PC.4) and upper comparison v_R(q)<=T_q(z_0) therefore sandwich (L/R)v_R(q) between cR/q-1/2 plus errors tending to zero INDEPENDENTLY of q. This proves the first uniform limit in (PC.6).

At z=h, T_q(h)=delta(y)x_q-1-r_q>=delta(y)X/(2R)-2, which tends to positive infinity uniformly over q. Thus (PC.5) applies simultaneously eventually. The positive-part map is 1-Lipschitz, and (L/R)/2->0; this proves the second limit. The same uniform lower bound proves (PC.7). No effective onset R_lambda is claimed.

#### PC3: Sharp Costs And The Signed Failure Of Greedy Optimization

PNT on the fixed interval [R,2R] gives, for any continuous g on [1,2],

~~~text
(L/R) sum_(q in Q)g(q/R) -> integral_1^2 g(u)du.
~~~

For precision, the distribution functions (L/R)#{q in Q:q/R<=u} converge uniformly to u-1 on [1,2], by the global PNT asymptotic on this compact proportional range. Step-function approximation then proves the displayed weighted limit. A possible prime at R contributes only L/R; 2R is composite. Neither endpoint is silently omitted.

Apply this to g(u)=max(c/u-1/2,0) and its square. The uniform error in (PC.6), boundedness of g, and m~R/L control the aggregate errors. Direct integration gives (PC.8). Both constants are strictly positive because their integrands are positive on the nonempty interval (1,2c). This proves the all-scale asymptotics, separately from the finite computations.

The independent finite choices imply that minimizing their sum of nonnegative costs is the same as summing their minima. This establishes the full variational scope over arbitrary assignments, not only one explicit cutoff rule.

For an absolute-minimizing choice, any negative row necessarily has v_R(q)<=0 and hence absolute value <=1/2 by (PC.5). Thus

~~~text
E_opt=A_1-2*sum_(negative chosen rows)e_R(q),
0<=2*sum_(negative chosen rows)e_R(q)<=m.
~~~

This is (PC.9). Since m=O(R/L)=o(R^2/L^2), it proves (PC.10). The ratio E_opt/(R L) tends to positive infinity, uniformly over minimizing choices.

The obstruction is robust: for any FIXED K>=0, if every chosen row satisfies |T_q(z_q)|<=e_R(q)+K, then eventually

~~~text
A_1-(1+2K)m <= sum_Q T_q(z_q) <= A_1+Km.
~~~

Rows whose v_R(q)>0 cannot be negative; other negative rows have magnitude <=1/2+K. Thus even uniformly bounded additive deviations from independent optimality have the same positive leading total. This is a proof-led corollary, not a separately preregistered numerical assertion.

#### PC4: An Inverse Restriction On A Small Selected Total

Every T_q(z_q)>=v_R(q), hence its positive part is at least max(v_R(q),0). Sum to get P>=P_min. Since E=P-N, one obtains N=P-E>=P_min-|E| exactly. By (PC.8), P_min/(R^2/L^2)->kappa_1>0; for fixed C the term C R L is negligible compared with R^2/L^2. Enlarging a threshold depending on C yields (PC.12). By (PC.7) none of that negative mass can come from the fixed lower interval q<=lambda R eventually.

This does not define an exceptional configuration merely as failure of the target. It identifies a specified compulsory positive prime population and a quantified negative population elsewhere that ANY affordable saturated assignment must retain.

### F. Structural Consequence

A fibre's owner-prefix response is not arbitrary: prime additions have ordered, strictly increasing costs and an almost unique minimizing prime rank. Prime factorization and even-factor multiplicity permit exactly one flat prime addition. Different q fibres can choose different cutoffs, but their uniform positive lower envelope near q=R cannot be eliminated within this class.

The consequence goes beyond HM's common-cutoff variance statement. The entire enlarged family of independently chosen cutoffs still has a sharp nonzero optimized L1/L2 cost. More importantly, greedy reduction of those local costs produces a large positive SIGNED proper-packet total. An affordable total must keep nonlocal negative contributions instead of minimizing them away.

The theorem does not say that every physical owner is positive, that all same-q transfers fail, or that every conceivable allocation must be saturated. Unsaturated cutoffs, another actual arithmetic map, and joint control with the outside mask are not ruled out.

### G. Original Source And Complete Signed Return

For an ORIGINAL unmasked least owner,

~~~text
B_R(p)=N_p(X)-X*w_p
      =-sum_(d|P_(p-1))mu(d)fract(X/(p*d)),
F_R=sum_(prime p<R)B_R(p).
~~~

Here the largest prime in a Boolean DIVISOR packet becomes the least prime of a PHYSICAL integer through inclusion-exclusion. They are not identified by an unsupported factor ordering. The unit divisor has fract(X)=0; the physical cofactor-one prime q is excluded from every N_p and subtracted exactly once.

Define V_Q=sum_Q x_q and rho_Q=sum_Q r_q. The full Q-mask is the credited CF total

~~~text
S_Q=delta(y)V_Q-m-rho_Q.
~~~

For ANY independent cutoff assignment let E=sum_Q T_q(z_q). The unselected owners are exactly z_q<p<=h, and each has the sole physical cofactor p. Therefore

~~~text
J=sum_Q [H-pi(z_q)-x_q*(delta(z_q)-delta(h))],
E+J=S_Q.
~~~

Each physical pq is present once, squareful cofactors remain in the selected saturated prefix, and the original Euler reference is partitioned rather than fitted. q=R, pq=X, d=X and every virtual divisor remain covered by the original source identities.

Let C_Q=F_R-S_Q-D_R. This contains ALL outside-Q physical sites, their exact reference and the full li anchor. The complete return is

~~~text
Z_R=E+J+C_Q,
Z_R^2=E^2+J^2+C_Q^2+2EJ+2E*C_Q+2J*C_Q,
E^2=sum_Q T_q^2+2*sum_(q<q')T_q*T_(q').          (RETURN)
~~~

All cross-family and cross-fibre terms are retained. This is not the differently normalized compressed #915 NNS statistic.

For the common AP cutoff, E is already O(R/log R). PC4 now proves that its large negative cross-fibre mass is unavoidable even in the more general independently chosen class. For greedy choices, PC3 proves E itself is too large; J+C_Q could still compensate it. No part of RETURN permits a claim that the full Z_R is large or small.

A bound J+C_Q=O(R log R) after choosing AP's already-paid E is TARGET_EQUIVALENT. Renaming that sum is not an independently proved supplier. PC pays no new part of the final RH bound.

### H. Falsification, Novelty And No-Circularity Review

The checkpoint was committed BEFORE arithmetic execution at 6cf1abc0324b471a70454f5d9b024919c14f0821, blob 5e668ceefc86642946545acdcaa696877dbde798. Immutable readback exactly matched the registered text.

Exact Python integers/Fraction tests covered EVERY R=8..128 and held-out roots 257,549,1024, every allowed integer cutoff and every q in Q:

| Check | Executed scope |
| --- | --- |
| Roots / fibres / integer cutoffs | 124 / 1,900 / 3,973 |
| Physical count versus saturated row | 144,283 exact identities |
| Prime increments and convexity/minimizing-rank tests | 30,634 increments; all exact assertions passed |
| Independent trial-factor reconstruction | 794 rows, R=8..32 |
| Independent complete divisor-row reconstruction | 85 rows, R=8..16 |
| Full arbitrary-reference signed return and all quadratic cross terms | 9 roots, R=8..16 |
| Empty/first-wheel and physical/virtual controls | R=2,3 and R=8..16 |

The test implementation independently constructs the physical least-factor counts. Its small-root second reconstruction uses trial division and the complete divisor cube; it does not infer correctness from agreement of two rearranged closed formulas. Both implementations are by this same author, not an independent Referee.

Decisive finite witnesses:

~~~text
R=8, q=13, Zcut={3}: T=-48/65.
Thus even existential per-fibre |T|<=1/2 is false.

R=10, q=11, Zcut={4}: T=37/35.
This also fails with a nonnegative final endpoint.
These are the smallest roots in the registered R>=8 domain
for the respective assertions.

R=13, q=13, z=5:
T(6)-2T(5)+T(4)=-9/65.
Convexity in INTEGER cutoff, rather than prime rank, is false.

R=16, q=17, added prime p=5:
zero increment; minimizing value 1450/1001.
~~~

All held-out cutoffs were tested, not only three representative cutoffs as in the different HM experiment. There were 78 compulsory positive fibres among 137 at R=1024; this is finite evidence, NOT a claim that the limiting fraction 2c-1 has been reached. No asymptotic onset, universal constant or limiting coefficient was fitted from the samples.

The unique zero-step classification and signed greedy corollary were proof-led extensions after the first registered run. The final program added their exact assertions on the SAME frozen domain and was rerun successfully; this is not described as a preregistered discovery. No failed assertion, altered source coefficient, or expanded supporting sweep was concealed.

Boundary checks retain the empty R=2 wheel, prime q=R, squareful cofactors, R=12's physical pq=X=143, R=14's divisor d=X=195, and every virtual divisor. The complete source uses the arbitrary reference 355/113 in exact tests; no uncertified numerical li value is used.

Main searches for "finiteWheel convex", "saturated cutoff", and "cofactor minimizer", together with relevant committed reports, found no matching current-source optimization theorem. Returned saturation/minimizer results concern other Mobius or Hecke carriers. The present claim is a source-specific extension of CF/AP/HM, NOT a literature-priority claim for convex sequences, finite optimization, PNT or Mertens. No exhaustive repository-wide novelty proof is asserted.

The asymptotic arguments are ordinary-PNT scale no-gos. They do not assume the desired O(R log R) estimate, and their positive constants do not certify a new global endpoint. PC4 is conditional only on its explicitly displayed finite selected-total test; the original global target is not assumed to imply that test.

### I. Conceptual Interpretation

A prime owner does not offer a free unit of cancellation. In the saturated region it adds one actual semiprime occurrence and subtracts a specific reciprocal-prime Euler allocation. The allocation decreases strictly with the owner prime, forcing convexity and a rigid minimum.

Giving different fibres independent choices does add freedom beyond a common prefix, but that freedom has a limit: fibres near the lower q wall retain a positive minimum. To cancel them, other fibres must intentionally carry substantial negative mass. A greedy local simplification removes precisely the negative mass that the affordable common packet needs.

This is information about the genuine full signed selected population, not an unsigned wheel-density inference or a graph analogy. It clarifies a forbidden local proof move while leaving the global original-source problem open.

### J. Competing Structural Hypotheses

| Mechanism | Disposition and exact reason |
| --- | --- |
| Independently minimize each fibre, then expect a small signed total | REFUTED at its stated saturated-cutoff scope by PC3, even allowing fixed additive near-optimality |
| Bound all separately optimized fibres by RH-sized L1/L2 budgets | REFUTED by the sharp positive constants in PC.8 |
| Preserve large positive/negative rows and prove a joint cross-mask relation | Still eligible; PC4 specifies unavoidable signs/masses, but no sufficient new transfer was proved |
| Exact/nearest-centre reflected product matching | Existing RF/NC subset results retained; no repeat scan or claim of missing partner coverage |
| Analytic HF full high-frequency estimate | Preserve its paper scope and complete-return obligations; PC supplies no automatic spectral bridge |

### K. Specialist Handoffs

**Coordinator:** PC3 rules out a genuinely larger local-optimization family than HM's common-cutoff norm. Add the sharp optimized signed no-go and PC4's compulsory negative mass to the owner consumer record. Do not count it as a new endpoint supplier or revive the already-refuted fixed-cutoff families.

**Owner:** Different z_q do not eliminate the need for cross-q cancellation. Any saturated assignment with affordable E must retain at least (kappa_1/2)R^2/log^2 R negative mass eventually. Near q=R the sign is forced positive regardless of cutoff. A proposed outside-mask transfer should preserve this signed mass and its Euler reference rather than first minimizing every row.

**Analytic:** PC uses neither HF nor an unproved spectral input. Its constants belong to the physical owner rows, not the nonconjugated frequency quadratic. Any use in HF requires an explicit source/weight bridge, including both mixed reference terms; none is asserted.

**Census:** No larger version of this scan is requested. A small independent reproduction of R=8,10,13,16 is sufficient for finite review. A useful NEW experiment needs a specified nonlocal map or a deliberately unsaturated cutoff class with original reference restored; freeze its constants, admission and complete return before execution.

**Referee:** Audit the quantifier change from common z to arbitrary z_q, the prime-rank rather than integer-coordinate convexity, exact (16,5,17) uniqueness, uniform minimum sandwich, positivity of both kappa constants, and the signed greedy inequality A_1-m<=E_opt<=A_1. Check that no premise in PC implies a global source estimate or treats q as a new Mobius factor.

**Lean Verification:** No immediate new branch/PR request before independent review and consumer triage. If useful after acceptance, PC1's finite prime-jump/zero classification is the compact structural candidate; PC2's finite half-unit crossing needs its endpoint condition. The PNT-based variational asymptotics are paper mathematics, not already formalized. Do not implement the full complement bound as a hypothesis and advertise its wrapper as an RH advance.

These are asynchronous handoffs in this report only. No agent was launched, scheduled or promised a background execution.

### L. First Independently Missing Theorem

No new smaller sufficient lemma for the complete RH estimate was obtained. The local strategy tested here is disproved at its actual hypotheses; the remaining requirement is a genuinely source-faithful nonlocal mechanism, not more precise independent cutoff optimization.

The first missing bridge for this lane is an actual once-only arithmetic operation connecting the compulsory positive q population to compensating original negative contributions while preserving the Euler reference and the full RETURN. PC4 constrains what such a mechanism must handle; it does not construct it or prove it exists. Naming J+C_Q and assuming its RH-size bound would simply restate the endpoint after AP's paid packet.

An unsaturated prefix is outside PC's no-go and would have to retain its surviving composite-cofactor correction; dropping that correction to reuse (PC.1) is invalid. No claim is made that this alternative succeeds.

### M. Continuity, Formal Evidence, And Resume Capsule

All November 9 role reports and the two available November 10 upstream reports were retrieved at the immutable intake snapshot. The latest relevant mathematical sections, source statements and referee verdicts were read. Today Owner HM and Analytic HF are AVAILABLE; Coordinator, Census, Referee and Lean are TODAY=PENDING / YESTERDAY=CARRY_FORWARD at that snapshot. Own prior RA/DG/RF claims retain their original IDs and status. Availability is not inferred from a schedule.

Consumed original claims: 20261109-owner-3/CF1-CF5; 20261109-referee-2/AP1-AP6, including its independent CF acceptance; 20261109-coordinator-2309-EST/CD1-CD4; 20261110-owner-1/HM1-HM5; 20261110-analytic-1/HF1-HF6; own RA/DG/RF; Census BL/NC; Lean's CF2 strengthening. This is intake, not blanket independent acceptance of HM/HF/CD/RF/NC. External handoff provenance and all role blob SHAs are preserved above.

Relevant formal evidence ACTUALLY rechecked this run:

- #1122 is merged. Source at tested head c53e9cf234500aea2605fd2557e638995f380407 has the identical blob ecb482e52deeee5e9b3853592a3ffdace662d2ff as current main. [Targeted job 128980092032](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42561949462/job/128980092032) was read: Lean 4.34.1, module compilation and both standard-axiom lists [propext, Classical.choice, Quot.sound]. It checked synthetic merge 1e3c182076a6e1a23ef132c41a78b0f26adab507 containing that head, not a newly run literal-main build.
- #1124 is merged; its original root-admission declarations were inspected. Its unchanged earlier accepted evidence is carried forward; no fresh #1124 compilation is claimed.
- #1125 is merged, but the fresh all-event query at proof head 538aa743a3e0de86b5ec44c9b4f159df3f5bd050 still returns twelve FAILED workflow records. No new successful dedicated proof execution was retrieved. Merge alone is not formal certification.
- #1126 is merged as current main. Its conditional amplification-consumer scope is carried from the verified Lean/Coordinator reports, not promoted to proof of its upgrade or zero-log hypotheses.
- #1127 remains the sole open non-draft PR at 866b3d2121309cdd854f9d64e2a6adbbc708ef9b. A fresh query returned thirteen successful check-runs. [Job 129590019152](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42743502306/job/129590019152) was read: literal checkout, Lean 4.34.1, both new modules compiled, source dependency closure=828 passed. Acceptance blob 94eecdbf8cea32bf80e7e0939e40c951bc72febd contains six executed standard-axiom guards. This supports its stated proper density/cofactor claims at the UNMERGED head, not PC or a global bound.

Execution: Python 3.12.13; no local Lean; no floating decisions. Final exact program SHA-256:
9a0904b870bc34001527802117b9fe2fb034794c25ae56dfac9e3af1c07b4205.
Syntax compilation and both arithmetic executions completed successfully. The complete final program and output are below. No expensive unregistered sweep occurred.

Direct Git transport returned CONNECT-tunnel HTTP 403, so authorized GitHub reads/writes used the working connector. An early oversized report batch was stopped and the necessary reports fetched separately; all listed continuity files were subsequently retrieved successfully. These technical limits did not prevent the stated proof or exact tests. No Lean source, central policy, other report, proof branch/PR, workflow, schedule, permissions or main was modified.

Resume: PC1-PC4 at PAPER_PROOF / SELF_AUDIT; PC5 exact finite evidence. Preserve the (16,5,17) exception, composite plateaus, endpoint condition in PC.5, and uniformity over independently varying cutoffs. Do not repeat the completed census, infer that pointwise nonzero increments have a uniform size, or replace the full RETURN by its diagonal. Highest-value next question: a concrete nonlocal, reference-preserving arithmetic operation beyond saturated per-fibre tuning.

Research complete at the stated scope. Publication is PENDING until the immutable commit/file readback receipt appended below.

### Reproducibility Appendix - PC5

Exact executed program, with the post-registration zero-step and greedy-bound assertions disclosed in H:

~~~python
"""Exact registered PC checks. No floating sign or asymptotic certification."""

from collections import Counter
from fractions import Fraction as F
from math import isqrt
import json


def sieve(n):
    least = list(range(n + 1))
    for p in range(2, isqrt(n) + 1):
        if least[p] == p:
            for k in range(p * p, n + 1, p):
                if least[k] == k:
                    least[k] = p
    primes = [p for p in range(2, n + 1) if least[p] == p]
    return least, primes


LP, PRIMES = sieve(2048)
DELTA = [F(1)] * 2049
PI = [0] * 2049
W = {}
for n in range(2, 2049):
    prime = LP[n] == n
    if prime:
        W[n] = DELTA[n - 1] / n
    DELTA[n] = DELTA[n - 1] * (F(n - 1, n) if prime else 1)
    PI[n] = PI[n - 1] + int(prime)


def trial_least(n):
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            return d
    return n


def faces(primes):
    terms = [(1, 1)]
    for p in primes:
        terms += [(d * p, -sign) for d, sign in terms]
    return terms


def frac(x):
    return x - x.numerator // x.denominator


counts = Counter()
first = {}
summaries = []
zero_jumps = []
roots = list(range(8, 129)) + [257, 549, 1024]
for R in roots:
    X, h, y = R * R - 1, (R - 1) // 2, R - 1
    a = isqrt(R) + int(isqrt(R) ** 2 < R)
    cutoffs = list(range(a, h + 1))
    Q = [q for q in PRIMES if R <= q < 2 * R]
    owners = [p for p in PRIMES if p < R]
    upper = [p for p in owners if 2 * p >= R]
    admissions = [p for p in owners if a < p <= h]
    states = [a] + admissions
    weights = {
        z: sum((W[p] for p in owners if p <= z or 2 * p >= R), F(0))
        for z in cutoffs
    }
    for z in cutoffs:
        assert weights[z] == 1 - DELTA[z] + DELTA[h] - DELTA[y]
    minima, optimal_abs, first_min_ranks = [], [], []
    positive_fibres, balanced_endpoint_rows = 0, 0
    for q in Q:
        x = F(X, q)
        t, r = X // q, F(X % q, q)
        physical = Counter(LP[n] for n in range(2, t + 1))
        assert all(p < R for p in physical)
        prefix = [0] * R
        for p in range(2, R):
            prefix[p] = prefix[p - 1] + physical[p]
        upper_count = sum(physical[p] for p in upper)
        rows = {}
        for z in cutoffs:
            direct = prefix[z] + upper_count - x * weights[z]
            formula = (DELTA[z] - DELTA[h] + DELTA[y]) * x
            formula += PI[z] - PI[h] - 1 - r
            assert direct == formula
            assert direct > DELTA[y] * x - PI[h] - 2
            rows[z] = direct
            counts['row_identities'] += 1
        values = [rows[z] for z in states]
        jumps = [1 - x * W[p] for p in admissions]
        for p, jump in zip(admissions, jumps):
            assert (jump == 0) == (R == 16 and q == 17 and p == 5)
            if jump == 0:
                zero_jumps.append({'R': R, 'q': q, 'p': p,
                                   'minimum': str(min(rows.values()))})
        assert all(values[j + 1] - values[j] == jumps[j] for j in range(len(jumps)))
        assert all(jumps[j] < jumps[j + 1] for j in range(len(jumps) - 1))
        for p in admissions:
            assert physical[p] == 1
        minrow, absrow = min(rows.values()), min(map(abs, rows.values()))
        ranks = [j for j, v in enumerate(values) if v == minrow]
        negative = sum(j < 0 for j in jumps)
        zeros = sum(j == 0 for j in jumps)
        assert ranks == list(range(negative, negative + zeros + 1))
        assert len(ranks) <= 2
        first_min_ranks.append(ranks[0])
        positive_fibres += minrow > 0
        if rows[h] >= 0:
            assert max(minrow, 0) <= absrow <= max(minrow, 0) + F(1, 2)
            minimizers = [v for v in rows.values() if abs(v) == absrow]
            assert all(absrow - 1 <= v <= absrow for v in minimizers)
            balanced_endpoint_rows += 1
            if absrow > F(1, 2) and 'endpoint_nonnegative_failure' not in first:
                first['endpoint_nonnegative_failure'] = {
                    'R': R, 'q': q, 'cutoffs': cutoffs,
                    'values': [str(rows[z]) for z in cutoffs],
                    'min_abs': str(absrow),
                }
        if absrow > F(1, 2) and 'independent_cutoff_failure' not in first:
            first['independent_cutoff_failure'] = {
                'R': R, 'q': q, 'cutoffs': cutoffs,
                'values': [str(rows[z]) for z in cutoffs],
                'min_abs': str(absrow),
            }
        for z in cutoffs[1:-1]:
            if rows[z + 1] - 2 * rows[z] + rows[z - 1] < 0:
                if 'integer_coordinate_convexity_failure' not in first:
                    first['integer_coordinate_convexity_failure'] = {
                        'R': R, 'q': q, 'z': z,
                        'second_difference': str(rows[z + 1] - 2 * rows[z] + rows[z - 1]),
                    }
        if R <= 32:
            independent = Counter(trial_least(n) for n in range(2, t + 1))
            assert independent == physical
            for z in cutoffs:
                selected = [p for p in owners if p <= z or 2 * p >= R]
                separate = sum((independent[p] - x * W[p] for p in selected), F(0))
                assert separate == rows[z]
                counts['trial_factor_rows'] += 1
        if R <= 16:
            for z in cutoffs:
                original = F(0)
                for p in owners:
                    if p <= z or 2 * p >= R:
                        for d, sign in faces([v for v in owners if v < p]):
                            original -= sign * frac(F(X, p * q * d))
                assert original == rows[z]
                counts['full_divisor_row_checks'] += 1
        assert rows[h] == DELTA[y] * x - 1 - r
        minima.append(minrow)
        optimal_abs.append(absrow)
        counts['fibres'] += 1
        counts['prime_jumps'] += len(jumps)
        counts['nonnegative_endpoint_rows'] += rows[h] >= 0
    assert all(first_min_ranks[j] >= first_min_ranks[j + 1] for j in range(len(Q) - 1))
    counts['roots'] += 1
    counts['integer_cutoffs'] += len(cutoffs)
    if R in (8, 10, 13, 16, 32, 64, 128, 257, 549, 1024):
        A1 = sum(optimal_abs, F(0))
        A2 = sum((v * v for v in optimal_abs), F(0))
        summaries.append({
            'R': R, 'fibres': len(Q), 'cutoffs': len(cutoffs),
            'compulsory_positive_fibres': positive_fibres,
            'endpoint_nonnegative_fibres': balanced_endpoint_rows,
            'A1_gt_R': A1 > R,
            'A1_gt_R_over_10': A1 > F(R, 10),
            'A2_gt_R': A2 > R,
        })


boundary = []
for R in [2, 3] + list(range(8, 17)):
    X, y = R * R - 1, R - 1
    owners = [p for p in PRIMES if p <= y]
    divisors = faces(owners)
    full = sum((sign * frac(F(X, d)) for d, sign in divisors), F(0))
    physical = sum((sign * frac(F(X, d)) for d, sign in divisors if d <= X), F(0))
    virtual = sum((sign * F(X, d) for d, sign in divisors if d > X), F(0))
    floors = sum(sign * (X // d) for d, sign in divisors)
    assert full == physical + virtual
    assert full - X * DELTA[y] == -floors
    actual_primes = sum(trial_least(n) == n for n in range(2, X + 1))
    L = F(355, 113)
    deterministic = X * DELTA[y] + PI[y] - 1 - L
    assert full - deterministic == L - actual_primes
    if R >= 8:
        h = (R - 1) // 2
        a = isqrt(R) + int(isqrt(R) ** 2 < R)
        Q = [q for q in PRIMES if R <= q < 2 * R]
        E, J, S = F(0), F(0), F(0)
        chosen = {}
        for q in Q:
            x = F(X, q)
            physical_count = Counter(trial_least(n) for n in range(2, X // q + 1))
            by_cut = {}
            for z in range(a, h + 1):
                by_cut[z] = sum((physical_count[p] - x * W[p]
                                 for p in owners if p <= z or 2 * p >= R), F(0))
            z = min(by_cut, key=lambda v: (abs(by_cut[v]), v))
            chosen[q] = by_cut[z]
            E += by_cut[z]
            J += sum((physical_count[p] - x * W[p]
                      for p in owners if z < p <= h), F(0))
            assert PI[h] - PI[z] - x * (DELTA[z] - DELTA[h]) == sum(
                (physical_count[p] - x * W[p] for p in owners if z < p <= h), F(0))
            S += DELTA[y] * x - 1 - frac(x)
        assert E + J == S
        C = full - S - deterministic
        Z = full - deterministic
        assert Z == E + J + C
        assert Z * Z == E * E + J * J + C * C + 2 * E * J + 2 * E * C + 2 * J * C
        vv = list(chosen.values())
        assert E * E == sum((v * v for v in vv), F(0)) + 2 * sum(
            (vv[i] * vv[j] for i in range(len(vv)) for j in range(i + 1, len(vv))), F(0))
        counts['complete_return_checks'] += 1
    boundary.append({'R': R, 'divisors': len(divisors), 'd_equals_X': any(d == X for d, _ in divisors),
                     'virtual_count': sum(d > X for d, _ in divisors)})


print(json.dumps({'counts': dict(counts), 'first_witnesses': first,
                  'zero_prime_jumps': zero_jumps,
                  'selected_root_summaries': summaries, 'boundary_checks': boundary}, indent=2))
~~~

Exact executed output:

~~~json
{
  "counts": {
    "row_identities": 144283,
    "trial_factor_rows": 794,
    "full_divisor_row_checks": 85,
    "fibres": 1900,
    "prime_jumps": 30634,
    "nonnegative_endpoint_rows": 1891,
    "roots": 124,
    "integer_cutoffs": 3973,
    "complete_return_checks": 9
  },
  "first_witnesses": {
    "independent_cutoff_failure": {
      "R": 8,
      "q": 13,
      "cutoffs": [
        3
      ],
      "values": [
        "-48/65"
      ],
      "min_abs": "48/65"
    },
    "endpoint_nonnegative_failure": {
      "R": 10,
      "q": 11,
      "cutoffs": [
        4
      ],
      "values": [
        "37/35"
      ],
      "min_abs": "37/35"
    },
    "integer_coordinate_convexity_failure": {
      "R": 13,
      "q": 13,
      "z": 5,
      "second_difference": "-9/65"
    }
  },
  "zero_prime_jumps": [
    {
      "R": 16,
      "q": 17,
      "p": 5,
      "minimum": "1450/1001"
    }
  ],
  "selected_root_summaries": [
    {
      "R": 8,
      "fibres": 2,
      "cutoffs": 1,
      "compulsory_positive_fibres": 0,
      "endpoint_nonnegative_fibres": 0,
      "A1_gt_R": false,
      "A1_gt_R_over_10": true,
      "A2_gt_R": false
    },
    {
      "R": 10,
      "fibres": 4,
      "cutoffs": 1,
      "compulsory_positive_fibres": 2,
      "endpoint_nonnegative_fibres": 2,
      "A1_gt_R": false,
      "A1_gt_R_over_10": true,
      "A2_gt_R": false
    },
    {
      "R": 13,
      "fibres": 4,
      "cutoffs": 3,
      "compulsory_positive_fibres": 1,
      "endpoint_nonnegative_fibres": 3,
      "A1_gt_R": false,
      "A1_gt_R_over_10": false,
      "A2_gt_R": false
    },
    {
      "R": 16,
      "fibres": 5,
      "cutoffs": 4,
      "compulsory_positive_fibres": 3,
      "endpoint_nonnegative_fibres": 4,
      "A1_gt_R": false,
      "A1_gt_R_over_10": true,
      "A2_gt_R": false
    },
    {
      "R": 32,
      "fibres": 7,
      "cutoffs": 10,
      "compulsory_positive_fibres": 5,
      "endpoint_nonnegative_fibres": 7,
      "A1_gt_R": false,
      "A1_gt_R_over_10": true,
      "A2_gt_R": false
    },
    {
      "R": 64,
      "fibres": 13,
      "cutoffs": 24,
      "compulsory_positive_fibres": 7,
      "endpoint_nonnegative_fibres": 13,
      "A1_gt_R": false,
      "A1_gt_R_over_10": true,
      "A2_gt_R": false
    },
    {
      "R": 128,
      "fibres": 23,
      "cutoffs": 52,
      "compulsory_positive_fibres": 15,
      "endpoint_nonnegative_fibres": 23,
      "A1_gt_R": false,
      "A1_gt_R_over_10": true,
      "A2_gt_R": true
    },
    {
      "R": 257,
      "fibres": 43,
      "cutoffs": 112,
      "compulsory_positive_fibres": 27,
      "endpoint_nonnegative_fibres": 43,
      "A1_gt_R": false,
      "A1_gt_R_over_10": true,
      "A2_gt_R": true
    },
    {
      "R": 549,
      "fibres": 83,
      "cutoffs": 251,
      "compulsory_positive_fibres": 49,
      "endpoint_nonnegative_fibres": 83,
      "A1_gt_R": false,
      "A1_gt_R_over_10": true,
      "A2_gt_R": true
    },
    {
      "R": 1024,
      "fibres": 137,
      "cutoffs": 480,
      "compulsory_positive_fibres": 78,
      "endpoint_nonnegative_fibres": 137,
      "A1_gt_R": true,
      "A1_gt_R_over_10": true,
      "A2_gt_R": true
    }
  ],
  "boundary_checks": [
    {
      "R": 2,
      "divisors": 1,
      "d_equals_X": false,
      "virtual_count": 0
    },
    {
      "R": 3,
      "divisors": 2,
      "d_equals_X": false,
      "virtual_count": 0
    },
    {
      "R": 8,
      "divisors": 16,
      "d_equals_X": false,
      "virtual_count": 3
    },
    {
      "R": 9,
      "divisors": 16,
      "d_equals_X": false,
      "virtual_count": 2
    },
    {
      "R": 10,
      "divisors": 16,
      "d_equals_X": false,
      "virtual_count": 2
    },
    {
      "R": 11,
      "divisors": 16,
      "d_equals_X": false,
      "virtual_count": 1
    },
    {
      "R": 12,
      "divisors": 32,
      "d_equals_X": false,
      "virtual_count": 10
    },
    {
      "R": 13,
      "divisors": 32,
      "d_equals_X": false,
      "virtual_count": 8
    },
    {
      "R": 14,
      "divisors": 64,
      "d_equals_X": true,
      "virtual_count": 30
    },
    {
      "R": 15,
      "divisors": 64,
      "d_equals_X": false,
      "virtual_count": 29
    },
    {
      "R": 16,
      "divisors": 64,
      "d_equals_X": false,
      "virtual_count": 28
    }
  ]
}
~~~

### Prepublication Freshness - 2026-11-10 02:33 EST

At 2026-11-10 07:33:03 UTC, main remained 7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9. The November 10 directory still contained only Owner, Analytic and this own checkpoint; their blobs match the intake ledger. Other upstream TODAY=PENDING is therefore still literal. The freshly fetched own blob is 5e668ceefc86642946545acdcaa696877dbde798 and matches the checkpoint byte-for-byte. The completed synthesis preserves it unchanged. All report code fences, required sections, embedded program bytes and program SHA were validated before publication.



### Verified Publication Receipt - 2026-11-10 02:34:18 EST

PUBLISHED and verified. Substantive commit 5be0963eab508ea3f891e628bef1b7baf2320dde on agent-reports created report blob bd77721bc2768c5bd6806852d922f422bcacd2f1. The report was re-fetched at that IMMUTABLE commit and matched all 53,992 prepared characters exactly; a fresh branch read also matched before this receipt was appended. The early checkpoint remained an unchanged prefix.

Execution=COMPLETE. PC1-PC4=PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. PC5=FINITE_COMPUTATION on the declared domain. NEW_VERIFIED_GLOBAL_ENDPOINT_GAIN=NONE. The complete finite-wheel RH bound remains OPEN.

This receipt records an already completed readback; it does not claim its own not-yet-known commit hash, independent review, new Lean certification, or a main merge. Its documentation-only append is separately re-fetched before the user-facing completion message.

A local append-prefix guard detected two displaced trailing blank lines; they were restored before any receipt write. No remote report content was lost or overwritten.





## Scheduled Cross-Route Checkpoint - 20261110-wheel-2/JC

### A. Structural Question And Current Status

IN_PROGRESS / NO_NEW_RESULT_YET. Test the complete historical Q_R against the actual CORR4 daughter/mixed expressions and the already-proved complete reciprocal-band telescope. The proposed recovery must preserve literal coefficients, both mixed orientations, squareful zeros, root-prime boundaries and all long-cofactor parents. No local positive fibre or negative daughter square is treated as a complete signed estimate.

### B. Authority And Continuity

Actual scheduled trigger: 2026-11-10 10:12:01 EST, America/New_York; platform RUN_ID_UNAVAILABLE. This is the second recorded Wheel invocation today. Main=655f897e274a8ba8a2fed80ecc1fc75a0d849174. cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1. AGENTS=c9c89f01b90b526de9f3e8ea92478e36504711b6; CURRENT_PROOF_CONTRACT=95566e37c8eaeb99ee680660df4f9d2e06ea5038; governing directive=e922d4ba9362a1ae196af8f6de88f7417f92087c.

Both November 9 and November 10 role reports were retrieved at agent-reports bb52e26c1dac8bd7222f74fd34969392ba1f6127. TODAY=AVAILABLE for all roles; YESTERDAY=CARRY_FORWARD. Read the relevant latest CD/CF/ZD/RF/NC/AP/Lean sections and today's UB/CR, BR, RD, PC, UC, LC, and repaired DG evidence. Analytic 20261110-analytic-2/RD's claimed candidate exponent is PAPER_PROOF / INDEPENDENT_REVIEW_PENDING, not a certified replacement baseline. The external inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry newer than October 18; its original root-boundary, physical-lift, and denominator cautions remain.

Open/draft PR collection is empty at intake. #1127 and #1128 are merged, superseding only earlier PR-state prose. #1115's actual new source is TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean (028d9f2bbfa1a8de1fe63e9bd368aca13aae6825), not the separate PrimeCombReciprocalBandCancellation module; credit Owner BR for identifying this attribution correction. Original Q_R endpoint theorem e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 and complete wheel ecb482e52deeee5e9b3853592a3ffdace662d2ff were read.

### C. Registered Investigation

Use X=R^2-1, Q_R=sum_(1<=a,b<R)mu(a)mu(b)floor(X/(ab))=2M(R-1)-M(X), and exact K_R=max_(0<=y<R)(M(y)-1)^2/(y+1). Read the original CORR4 source before proposing an identification. Candidate: the full mixed/daughter bookkeeping supplies a quantitative restriction not already equivalent to the original Q_R bound. Rival: the coefficient map has missing roots, squareful weights, or a complete same-order signed remainder.

First tests, after deriving a precise assertion: exhaustive small roots and original integer masks, plus targeted R=549 and R=5561 where relevant. Preserve top cofactor-one contributions, q=R, repeated factors, diagonal and both cross orientations. Finite survival will not establish uniformity. Do not rerun PC/UB local-cutoff scans, expand a wheel, or fabricate a proof route.

### D. Remaining Work And Permissions

Baseline exact theorem/dependency/CI receipt, four-way source map, signed-loss ledger, paid recovery test, proof/falsifier, and full return are PENDING. Canonical VF, complete wheel RH bound, finite A/C and RH remain OPEN. Own-report-only writes; no Lean edit, proof branch, PR, issue, merge, workflow, schedule change or agent launch. Direct git transport returned HTTP 403; the GitHub connector works. No local Lean execution.


## Square-Index Incidence And The Unpaid Upper Bands
### Final Research Synthesis - 20261110-wheel-2/JC

### A. Most Important Structural Finding

**The CORR4 daughter data is an exact nested sampling of completed reciprocal bands, but it does not include the upper eight bands of the complete historical source. Their interaction is neither automatically negative nor paid by twice the daughter energy. Both shortcuts fail on genuine Mobius coefficients at R=56.**

The bridge is coefficient-exact, not an analogy between two kinds of ownership. For each admitted odd prime q with q^2<R, its original daughter is

```text
M(floor((R^2-1)/q^2)) = M(R-1) + sum_(q^2<=z<R) t_R(z),
t_R(z)=M(floor((R^2-1)/z))-M(floor((R^2-1)/(z+1))).
```

Thus none of these daughters sees z=1,...,8, including the complete cofactor-one band. The already-proved band completion does not remove that sector. Its exact contribution after reassembling the scalar square contains its own square AND both cross orientations. The physical squarefree diagonal must still be subtracted.

At R=56, the omitted interaction before diagonal subtraction is 5312/105, while twice the entire daughter energy is 12. After subtracting the upper physical diagonal 1698 the contribution is NEGATIVE, -172978/105. Therefore these are decisive counterexamples to the two stated intermediate shortcuts, **not** counterexamples to the complete CORR4 inequality or RH.

| Claim | Classification and scope |
| --- | --- |
| 20261110-wheel-2/JC1 | Exact completed-band to original CORR4 daughter/Gram bridge; supporting PAPER_PROOF / IDENTITY_ONLY, using established source identities. |
| JC2 | Nested incidence kernel, exact coefficient support, and full upper/deep mixed reconstruction; supporting PAPER_PROOF / source-transfer obstruction. Not a new quantitative complete-source restriction. |
| JC3 | H_SIGN and H_CREDIT below are REFUTED by the actual R=56 source; sign reversal at R=60. |
| JC4 | Exact registered tests at 247 roots, 5,560 renewal checks, and separate trial-factor verification at 25 small roots; FINITE_COMPUTATION. |

New derivations and tests are SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. They do not pass the new-route/global-gain admission gate. **NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE.** No global arithmetic bound has been established.

### B. Current Authority And Baseline

Actual trigger: 2026-11-10 10:12:01 EST, America/New_York; platform RUN_ID_UNAVAILABLE. This is the SAME scheduled invocation as the JC checkpoint, not an additional launch. Main at intake is 655f897e274a8ba8a2fed80ecc1fc75a0d849174. A final freshness receipt is recorded below.

`cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. Older finite-wheel, cancellation-chain and HIGH acknowledgments retain source safeguards, not superseded task priority. The owned report's earlier PC work remains unchanged. Current instruction blobs: AGENTS c9c89f01b90b526de9f3e8ea92478e36504711b6; CURRENT_PROOF_CONTRACT 95566e37c8eaeb99ee680660df4f9d2e06ea5038; cross-route directive e922d4ba9362a1ae196af8f6de88f7417f92087c.

Canonical target remains VFCanonicalSquareVonKochStatement: one C>=0, uniform over integer R>=2, with abs(pi(R^2)-VF_can(R^2))<=C R log R. Its final riemannHypothesis_of_vfCanonicalSquare explicitly takes ClassicalVonKochRHCriterion and the arithmetic bound. Neither is supplied here. The exact wheel coordinate F_R-D_R=li(R^2-1)-pi(R^2-1) retains every virtual divisor until Euler compensation, the d=X boundary, and the fixed Li normalization. Its RH-sized bound is OPEN. The internal finite-AC/Mertens-energy-to-RH consumer is separate and conditional on its arithmetic input.

#### 1. BASELINE / DEPENDENCY RECEIPT

The strongest explicitly quantified applicable certified repository result checked is RHLean.Analysis.native_mertens_near_uniform_window_error_closed in research/oai_434/VF919WindowErrorClosure.lean:

```text
N_pack = ceil_nat(max(1,1/(6*explicitFineLength)))+2,
N_old  = ceil_nat(max(1,1/(3*explicitFineLength)))+2,
b_base = 7/8 - 7/(64*N_pack),
forall eps>0, exists C_eps>=0, forall integer n>=1:
  abs(M(n)) <= C_eps*n^(b_base+eps).
```

The constants precede n. This is MertensGrowthAtMost, not a no-loss bound. The old count and near-uniform count were read in their actual definitions. Since explicitFineLength>0, ceiling monotonicity gives N_pack<=N_old; consequently 7/(64*N_pack)>1/(48*N_old). This rechecks Coordinator CR1, not a new theorem or an identification of the counts.

Read the live error-closure proof, fixed-source/count construction, total-mass endpoint, native Hecke/zeta/Mertens adapter, growth predicate, and the hosted proof-value/dependency audit implementation. The inspected chain is original source construction and moments -> total-mass LOW and anchored HIGH/principal -> complete probe comparison -> smaller-positive-error closure for the same Hecke beta -> modulus-one Dirichlet/Hecke product -> actual zeta-zero boundary -> native Mertens converse. Each smaller error reconstructs its valid source; no fixed-source zero-error limit is assumed. The final declaration has no unproved arithmetic premise as an ordinary argument.

Verified [#1119 run 42552018910, job 128949473700](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700): completed/success, literal head 77ee815846d6d534c866f0752aa33b84c385610a; warning-fatal compilation, exact types and five PASS live dependency checks. Closure sizes: 35358, 35375, 35736, 35737, 35753. Allowed terminal axioms: propext, Classical.choice, Quot.sound. The audit traverses OAI/RHLean/private proof values and separately collects axioms transitively; it does not assert that this run independently reproved every external analytic lemma. A tree-blob comparison found NO changed pre-existing RHLean/ or research/oai_434/ source files between that tested head and current main; later files were added. This supports reuse, not a new main-head compilation.

Pins read from the hosted receipt and continuity: Lean 4.34.1 / compiler 5045d0056413266e57c625dcd7c365b10e377c52; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; PrimeNumberTheoremAnd c39a751132c88b6e8080b74c74023fd95b3d8be0; openai/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a; anchored generator source pin 9cbfce5295343bcb411e6d2cb159b59995cd985b. Imported analytic arguments remain part of this formal dependency receipt, not a newly independent human mathematical validation. No local Lean was executed.

Analytic's newer 20261110-analytic-2/RD candidate b_RD=7/8-1/(8*N_pack) is PAPER_PROOF / INDEPENDENT_REVIEW_PENDING. Its proposed gain is not used here or substituted for b_base. A future accepted improvement can be fed through the same existing band consumer, but that would not make the bridge itself a new global gain.

### C. Structural Mechanism Investigated

Resume Coordinator's 20261110-coordinator-0710-EST/M2 assignment: test the complete historical source against existing CORR4 mixed/daughter credit. This is a FINITE-AC/CORR4 comparison, not another local-cutoff scan. MU-LIFT is kept separate: endpoint identities do not by themselves give its whole-prefix subcritical recurrence.

The optimistic mechanism tested was that completed reciprocal bands allow the daughter square credit to pay the source without an additional upper/deep signed interaction. The rival is exact support mismatch: every low daughter starts at a squared odd-prime quotient index, while the full Q_R source includes all indices starting at one. We derive the exact remaining term before testing signs.

Credit #1115 for complete-parent renewal and band telescoping, the earlier common-clock CORR4 modules for the full weighted scalar square and mixed identity, and Owner BR for correcting #1115's attribution. PrimeCombReciprocalBandCancellation.lean is a separate source, not the file introduced by #1115. No established scalar identity is relabeled a new arithmetic bound.

### D. Exact Definitions And Statements

For EVERY integer R>=56 let

```text
X=R^2-1; m=M(R-1);
K_R=max_(0<=y<R) (M(y)-1)^2/(y+1);
Q_R=sum_(1<=a,b<R) mu(a)mu(b) floor(X/(ab))=2m-M(X);
O_R={odd primes q:q^2<R}; Y_q=floor(X/q^2);
t_z=M(floor(X/z))-M(floor(X/(z+1)))       (1<=z<R);
B_j=sum_(j<=z<R)t_z                       (1<=j<R);
U=sum_(q in O_R) M(Y_q)/q;
E=sum_(q in O_R) M(Y_q)^2;
d(n)=sum_(q in O_R, n<=Y_q)1/q;
G=M(X)-m=B_1=m-Q_R.
```

O_R is literally canonicalRoughLowQ2Owners: the odd primes below R minus the q^2>=R sector. It is NOT the mask of post-root primes. U is lowOwnerReciprocalMertensColumnReal and E is canonicalRoughLowQ2DaughterEnergy. Their signs and normalization are unchanged.

One original Euler occurrence is (a,b,k), with a,b<R and abk<=X, weight mu(a)mu(b). Aggregation by n=abk is a weighted projection, not a bijection: the compiled coefficient theorem sums its entire multiplicity to mu(n) below R and -mu(n) on R<=n<=X. The t_z intervals partition this latter physical integer population once. All squareful n retain mu(n)=0; they are not converted into new nonzero q^2 sites.

**JC1: exact square-index bridge.** For every q in O_R,

```text
Y_q>=R+1, B_(q^2)=M(Y_q)-m,
U=m*sum_q 1/q + sum_(1<=z<R) A(z)t_z,
E=#O_R*m^2 + 2m*sum_z C(z)t_z
  + sum_(1<=z,w<R) C(min(z,w))*t_z*t_w,
A(z)=sum_(q in O_R, q^2<=z)1/q,
C(z)=#{q in O_R:q^2<=z}.
```

The last sum is ORDERED and includes its diagonal and both cross orientations. It is the original daughter energy, not an extra reserve. In the binary incidence matrix I(q,z)=1_(q^2<=z), each row is nested and rank(I)=#O_R over the reals. This is a statement about the source map; it is not an arbitrary-sign substitute for the actual t_z.

**JC2: exact full upper/deep decomposition.** Set

```text
Y=floor(X/9), W=M(X)-M(Y)=sum_(1<=z<=8)t_z,
V=M(Y)-m=B_9, G=W+V,
D_top=sum_(Y<n<=X)mu(n)^2,
D_deep=sum_(R<=n<=Y)(1+2d(n))*mu(n)^2,
J=lowOwnerPrefixTailMixedRawCellMass R,
J_deep2=V^2+2UV-D_deep,
T=W^2+2W(V+U).
```

Then

```text
d(n)=0 for n>Y,
2J = J_deep2 + T - D_top,
2J-2E = [V^2+2UV-D_deep-2E] + [W^2+2W(V+U)-D_top].   (JC.1)
```

This is the complete original CORR4 mixed bill in literal reciprocal-band coefficients. The original physical diagonal difference is D_deep+D_top. No term with n=1, n=R, z=1, q^2=R, repeated factor, or both mixed orientations is silently discarded.

The incidence rows and the historical prefix have zero coefficient at every n>Y. Thus no linear combination of those COEFFICIENT FUNCTIONS reproduces the complete Euler tail coefficient there. This is a coefficientwise transfer obstruction, not a claim that the true arithmetic upper tail is freely variable after fixing all historical Mobius data. Indeed the original Newton identity reconstructs it exactly. At R=56 the actual prime n=349 has mu(349)=-1, Euler aggregated coefficient +1, and zero contribution to every daughter column and historical-prefix column. It is a literal witness against identifying these coefficient maps.

**JC3: the tested sign/credit rules.** On the above exact carrier, the two proposals were

```text
H_SIGN:   for all R>=56, T<=0;
H_CREDIT: for all R>=56, T<=2E.
```

Both are false. They are investigated hypotheses, not attributed assertions by another agent. Neither proposal includes D_top. No claim that T-D_top is positive is inferred from their failure.

### E. Proofs And Derivation

**Square-index incidence.** Since q^2<R, q^2<=R-1, whence Y_q>=floor((R^2-1)/(R-1))=R+1. The existing complete-band theorem at a=q^2,b=R-1 gives B_(q^2)=M(Y_q)-M(floor(X/R))=M(Y_q)-m. Its completion keeps ALL k=1,...,z descendants because sum_k M(floor(z/k))=1. The present use is an application of that theorem, not a new renewal result.

Substitute M(Y_q)=m+sum_(z>=q^2)t_z into U and E and interchange finite sums. A single t_z is replicated exactly once for each q with q^2<=z; an ordered pair (z,w) is replicated exactly once for each q with q^2<=min(z,w). This proves the displayed A and C coefficients, including multiplicity. Ordering the distinct primes and evaluating I on columns z=q^2 yields a triangular matrix with diagonal one, proving its row rank. All its columns z<9 vanish, since q>=3. This rank fact concerns formal coefficient data only and supplies no bound on the genuine Mobius vector.

**Sharp root boundary.** Conversely q^2>=R implies Y_q<=floor(X/R)=R-1; equality q^2=R is in the already-historical HIGH-owner sector. There is no daughter cutoff equal to R. For prime R the physical n=R contribution is in G and in every admitted low daughter, while it is excluded from m. q=R itself is not a low owner. These checks prevent swapping the root and square-owner conventions.

**Complete mixed reconstruction.** The native source weight is w(n)=1_(n>=R)+d(n), on 1<=n<=X, with sign mu(n). The reciprocal-prefix weight is d(n). Therefore its physical diagonal difference is

```text
sum_(n<=X) [(1_(n>=R)+d(n))^2-d(n)^2]*mu(n)^2
 =sum_(R<=n<=X)(1+2d(n))*mu(n)^2=D_deep+D_top.
```

The already-compiled corr4_mixed_tail_eq_actual_endpoint_gap gives
2J=G^2+2UG-(D_deep+D_top). Every low q is at least three, so Y_q<=Y, hence d vanishes above Y. Insert G=W+V and expand. Both WV and WU orientations produce the factor two in T. Subtract 2E exactly ONCE to obtain JC.1. This recovers every original term and uses no inequality.

**Genuine finite falsifiers.** R=56 has X=3135, O_R={3,5,7}, and

```text
M(55)=-2, M(3135)=6, M(348)=2,
(Y_3,M(Y_3))=(348,2), (Y_5,M(Y_5))=(125,-1),
(Y_7,M(Y_7))=(63,-1).
U=2/3-1/5-1/7=34/105; E=4+1+1=6;
W=4, V=4, T=16+8*(4+34/105)=5312/105;
T-2E=4052/105>0.
```

The top eight t_z are (9,3,-5,2,-1,4,-5,-3), summing to 4. In particular t_1=9 is present, not silently paid by daughter completion. The physical D_top=1698 gives T-D_top=-172978/105. The entire twice-mixed quantity is -68044/35, and 2J-2E=-68464/35. This example does NOT refute any complete source bound.

At R=60, W=-1, V=2, U=-46/105, E=18, giving T=-223/105<0. Thus the same genuine interaction has both signs. At R=56, the original floor sum independently gives Q_diag=4712, Q_cross=-2361, Q=Q_diag+2Q_cross=-10=2*(-2)-6. The large cancellation predates any proposed daughter allocation.

### F. Structural Consequence

The precise transfer is a NESTED square-index incidence map, not a disjoint allocation of all reciprocal parents. The first eight completed bands, physically n>floor(X/9), are absent from all low-daughter amplitudes but are present in the complete source. They reappear through W^2+2W(V+U) and their physical diagonal. Neither nesting, rank, proper-fibre positivity, nor a favorable daughter norm removes these terms.

The full low-daughter data also is not already paid by K_R: EVERY Y_q is >=R+1. The complementary q^2>=R daughters are the ones covered by history, as the existing tail-reduction theorem already proves. This distinction is not a new theorem; it is indispensable to the attempted recovery.

The support statement rules out an omitted-term coefficient map, not nonlinear arithmetic use of the historical prefix, not a different source-faithful transport, and not complete-source cancellation. JC1-JC2 expose where a valid quantitative argument must operate; they do not independently restrict the amplitude of W.

### G. Signed Relevance And Required Five-Stage Capsule

#### 2. FOUR-WAY SOURCE MAP

| Euler / finite AC | VF / prime discrepancy | NNS / OAI | Square blocks / CORR4 | Prime/Mobius coupling |
| --- | --- | --- | --- | --- |
| Q_R=sum mu(a)mu(b)floor(X/(ab)); strict historical a,b<R; no virtual integer triples abk>X. EXACT_IDENTITY to 2m-M(X) by eulerSelfDualBilinear_eq_two_mertens_sub_endpoint. Coefficient aggregation retains multiplicities. | Complete wheel F_R-D_R=li(X)-pi(X), X=R^2-1, all divisor and virtual terms compensated first. EXACT_IDENTITY on its own prime source, NOT equality with Q_R. | The native real common-clock square is (G+U)^2 with literal weighted Mobius sites. Its first-owner split is EXACT_IDENTITY. The OAI ideal/Hecke tuple Gram is a DIFFERENT source with complex phases, exclusions and normalizers. No direct coefficient isometry is asserted. | G=B_1=m-Q_R; each daughter is m+B_(q^2). JC1-JC2 are exact finite source adapters. M(X) is a full prefix, not a shell increment or sum of shell squares. Root scale R and integer scale X remain distinct. | Owner BR's complete weighted prime/floor-Li renewal includes all event descendants and sign defects. It does not identify prime-event coefficients with t_z. Direct OAI-moment-to-Q_R or wheel discrepancy recovery remains OPEN_BRIDGE. |
| Historical K_R is the actual shifted max over y<R, not 1. | Canonical VF/Li_2 has the proved bounded offset; principal-value li has its separate fixed offset. #915 clipped/history masks are not replaced by this scalar wheel. | The compiled analytic Hecke -> zeta -> Mertens route is a ONE_WAY_IMPLICATION, not a physical-occurrence bijection. OAI J=empty has one outer tuple and zero outer cross Gram. | U,E contain the true raw cutoffs floor(X/q^2); no nearest-square rounding, positive surrogate or Gaussian daughter is inserted. | Existing cofactor positivity and prime near-resonance apply to their own masks only; neither supplies the complete missing mixed term. |

#### 3. FIRST SIGNED LOSS

| Declaration / exact input | Loss and power/constant | Recovery tested and remaining bill |
| --- | --- | --- |
| eulerSelfDualBilinear / literal ordered floor sum | Triangle before pairing gives at most X*(1+log(R-1))^2, R-power 2 up to logs. It discards the real cancellation Q_diag+2Q_cross. At R=56 these are 4712 and -4722. | Pointwise Newton identity and exact complete-band renewal recover equality, not a smaller uniform bound. Full B_1 remains. |
| twoABCompleteReciprocalBand_norm_le_endpoints | Replaces the endpoint DIFFERENCE by two endpoint norms. Its existing growth consumer gives O_eps((X/a)^(b_base+eps)+(X/(b+1))^(b_base+eps)). | a comparable to R gives R^(b_base+eps), but a=1 and fixed a=9 retain R^(2b_base+2eps). Low q=3 starts at 9, not at a growing root-adjacent cutoff. |
| lowOwnerCriticalSynthesis_energy_le_compositeGap | Cauchy-Schwarz bounds U^2 by b_7 E, b_7=1565172113/7214407200. It loses signed daughter-pair information. | JC1 restores the entire C(min(z,w)) Gram, not a negative bound. The sharper existing frame is credited rather than replaced by an inferior 1/4 or 211/900 constant. |
| corr4_mixed_tail_eq_actual_endpoint_gap | No loss in the identity. The attempted loss is removing T, or asserting T<=2E, when converting complete source to daughter data. | H_SIGN and H_CREDIT fail at R=56. Restore JC.1, including D_top and both orientations. No failure of the restored inequality was observed on the registered roots. |
| Negative credit -2E in JC.1 | E<=E_bar implies -2E>=-2E_bar, NOT an upper bound for the mixed bill. | Cannot subtract the upper frame budget as if it were a guaranteed negative reserve, or spend E in both brackets. |
| Whole-prefix MU-LIFT return | Endpoint-only control omits all B<=x<B^2 and their signed floor overlap. | #1115 and JC1 at one square endpoint do not prove the subcritical all-prefix recurrence. That route remains separately OPEN. |

These source losses are not all binding steps of the strongest OAI theorem. The failed CORR4 recovery does not alter the independently established OAI baseline or certify/refute Analytic RD's proposed improvement to its binding principal loss.

#### 4. PAID RECOVERY TEST

Already-proved #1115 exactly recovers the complete parent packets; we apply it at the ACTUAL q^2 cuts and obtain JC1. Its existing consumer recovers the baseline power only, because q=3 is fixed. The CORR4 common-clock and first-owner theorems recover the discarded interaction exactly as JC.1; the published quantitative mixed-tail bound is an explicit OPEN premise. The existing composite-gap frame constrains U given E but supplies no bound on W.

#1127's positive cofactor fibres retain a different positive-survivor/Euler-reference source; there is no sign-preserving transfer to the t_z vector. #1128's genuine shared-prime Hermitian resonance is an obstruction to naive decorrelation, not a negative interaction theorem. Their actual merged sources were read, and their successful exact-head run metadata refreshed. #1122/#1124 remain wheel/virtual and root-admission identities and scoped costs, not the missing complete signed estimate. No prime density or ideal-phase assumption was imported.

#### 5. NET RESULT / ADMISSION VERDICT

NO_NEW_GLOBAL_GAIN. The new joint source adapter and the two finite falsifiers are useful supporting results, not a newly accepted RH route or a complete-source strengthening beyond known identities.

For a new power b_new>=1/2, the actual compiled consumer asks for ONE A>=0 uniform in R>=56 such that

```text
[V^2+2UV-D_deep-2E] + [W^2+2W(V+U)-D_top]
    <= A*R^(4*b_new).
```

This is precisely the existing Corr4PowerMixedTailBill after the exact bridge. Naming it is not proving it or making it smaller. Existing growth and triangle/frame inputs supply no new exponent below b_base. Their fixed q=3 return still has R-power 4*b_base, with all positive losses restored.

On the finite-AC alternative, a genuinely proved uniform abs(Q_R)<=C_eta R^(1+eta)*sqrt(K_R), with eta<b_base-1/2, could improve the exponent. Spend an input loss eps satisfying 0<eps<b_base-1/2-eta. The actual historical bound gives K_R=O_eps(R^(2*(b_base+eps)-1)), and the square endpoint then gives

```text
b_next=(2*b_base+1)/4 + eta/2 + eps/2 < b_base.
```

The between-square increment is O(sqrt(x)); since b_next>1/2 it is paid. This is the required exponent budget, not a proved supplier or an automatically renewable iteration. Replacing K_R by 1 only yields the baseline-based eta=2*b_base-1 plus loss, which is too large. Fixed-C finite-AC and RH remain open.

### H. Falsification, Novelty And Reproducibility

The preregistered source, two inequalities, rival mechanism, exact diagonal, root set and rejection rules were frozen before running. C++ integer arithmetic computed mu and M through X_5561=30,924,720 and the literal floor sum; Python Fraction performed every rational comparison. A separate trial-factorization algorithm recomputed the full source for R=56,...,80, including ordered Q, K_R, actual weighted sites, physical diagonal and selected pointwise Newton coefficients. This is same-session SELF_AUDIT, not independent agent acceptance.

- Registered roots: every R=56,...,300, plus held-out 549 and 5561, total 247.
- T was positive at 183 roots, negative at 60, zero at 4. First positive/credit failure in the declared range: 56; first negative: 60; first zero: 79.
- H_CREDIT failed at 131 roots. These are finite failures of that exact rule, not asymptotic frequency claims.
- T-D_top was NOT positive at any registered root. This observation does not prove its all-root sign and does not prove the complete mixed bill.
- 5,560 complete Mobius renewal checks and all registered band/daughter identities passed; 337 strict square-cutoff boundary checks passed.
- Root-prime, q^2=R, cofactor-one, squareful-zero, original ordered-pair, diagonal and both cross-orientation cases were retained.

| R | Q_R | K_R | W | V | E | Exact scope |
| --- | --- | --- | --- | --- | --- | --- |
| 56 | -10 | 3/2 | 4 | 4 | 6 | T=5312/105>2E; restored top contribution negative |
| 60 | -2 | 3/2 | -1 | 2 | 18 | T=-223/105<0 |
| 549 | -186 | 3/2 | 197 | -8 | 487 | T>2E; restored top contribution negative |
| 5561 | 2554 | 3/2 | -2137 | -412 | 196306 | T>2E; restored top contribution negative |

This is not another test of the already-refuted one-block BLOCK capture. The held-out roots test a newly specified complete-source decomposition and intermediate sign hypotheses. Mu values above the historical root are used for exact verification and counterexamples, NEVER as an independent all-scale estimate.

Repository novelty searches for twoABCompleteReciprocalBand with canonicalRough/lowOwner, and squareRootReplacementTailMoebiusCoefficient with rawQ2ChildCutoff, found no directly named joint adapter. This is not an exhaustive novelty claim. Inspection found that its scalar content follows from existing renewal, physical weighting, threshold-incidence, and mixed-remainder modules. The new contribution is the explicit source comparison and genuine falsifiers, NOT a newly discovered Mobius renewal or a new universal bound. Existing target-equivalence/no-go modules were checked; no desired bound is assumed.

Program SHA-256 receipts:

```text
jc-test-plan.md  1e12e9e807b8f2095fb059829f41873b3be5eb9925c196254dbebc68e4476b3b
jc_probe.cpp    2508e774e1ebbb70804e7fd94f811f50c11e21f8e3effac29d0a4d9298456a40
jc_verify.py    469fa107cd8ee10388da04b447397b88016035a42a8f05499a3821ca621f3a47
jc-results.json 6b37fefef5f35fefb7439d6d8cae273e261e92f69b2c630b9402fff8b6b8873a
```

The final source was compiled with g++ -std=c++17 -O2 -Wall -Wextra -Werror; Python 3.12.13 completed with every assertion passing. One initial version ran successfully; the final verification added explicit renewal and boundary/coefficient guards and was rerun to produce the frozen output. No local Lean, large unregistered sweep or floating-point sign decision occurred. Exact final source and output are included below.

### I. Interpretation

Completed reciprocal bands and q^2 daughters are genuinely compatible coordinates, but their compatibility has a precise coverage limit. The former cover every quotient index; the latter form nested samples beginning at nine. The missing upper sector carries an independent term in the reassembled algebra, not a sign inferred from daughter positivity or from an unsigned norm. Its arithmetic may still cancel against the deep source and diagonal. The investigation identifies that exact joint bill rather than declaring a broad impossibility result.

### J. Competing Hypotheses

Retire H_SIGN and H_CREDIT at their stated scope. Preserve the complete diagonal-restored possibility; it survived only the declared finite tests and has no proof here. Do not replace it with a universal sign conjecture merely to obtain a new label. A useful next mechanism must constrain the actual upper/deep covariance before the final norm, or exploit a separately proved source-compatible analytic estimate.

FINITE-AC remains the historical Q_R/K_R route. CORR4 remains the complete signed mixed-bill route, now with an explicit reciprocal-band bridge. MU-LIFT remains the all-prefix subcritical recurrence route; this run audited the endpoint mismatch but did not prove or meaningfully improve its distinct all-prefix estimate. No rolling coverage is fabricated by naming that route. Next rotation should give MU-LIFT a dedicated arithmetic attempt if no newer instruction supersedes it.

### K. Specialist Handoffs

**Coordinator:** record JC1-JC2 as supporting source adapters and JC3 as scoped falsifiers, not new-route admission. The paid q^2 columns miss z=1,...,8; the complete unrecovered bill is JC.1. The existing conditional CORR4 consumer is not a paid recovery theorem. Preserve Analytic RD's separate review-pending status.

**Owner:** no prime-event identification is needed for the Mobius-to-Mobius bridge. Retain BR's composite event defect and once-only multiplicity when comparing with Buchstab. Actual prime n=349 at R=56 is a compact witness against an omitted-upper-source daughter map; it is not a counterexample to BR or an alternative owner classification.

**Analytic:** any bound on U or on a completed fixed-index band leaves T and the deep mixed remainder. A proposed source estimate must enter JC.1 with both orientations and D_top. This report neither audits nor rejects RD's Hecke principal-response comparison; it supplies no extra gain for it.

**Census:** no larger scan is requested. Independently reproduce R=56 and 60, their actual daughter masks and diagonals. A later experiment needs a new quantified assertion on the diagonal-restored joint expression, not more confirmations of the two already-false shortcuts.

**Referee:** check the square threshold gap, exact C(min(z,w)) multiplicity, old versus new claims, and especially the distinction between positive T and negative T-D_top. Review the simple counterexamples and complete reconstruction before approving a bridge. No independent verdict has yet been received.

**Lean Verification:** NO_NEW_THEOREM_TO_FORMALIZE for a new endpoint. If an independently reviewed downstream task genuinely needs it, JC1 is a short exact adapter obtained from twoABCompleteReciprocalBand_eq_mertensDifference at a=q^2, b=R-1. Do not create a filler PR or encode the missing mixed bill as a proved arithmetic premise. Existing #1115/#1127/#1128 need no no-op rerun.

These are asynchronous report handoffs. No other agent was launched, messaged through a fabricated channel, rescheduled, or promised background work.

### L. First Independently Missing Theorem

No new smaller sufficient arithmetic bound was proved. For the investigated recovery, the exact first unpaid expression is JC.1 at a uniform power beating 4*b_base, or a comparably strong direct Q_R/K_R inequality. Both are OPEN. The display exposes the original source rather than evading it; treating it as an assumed supplier would be circular. The finite diagonal-restored sign observation is a possible falsifiable research question, not an established input or accepted route.

### M. Continuity, Formal Evidence And Resume Capsule

Intake report snapshot: bb52e26c1dac8bd7222f74fd34969392ba1f6127. TODAY=AVAILABLE for all seven roles; YESTERDAY=CARRY_FORWARD at the read scope. Both Eastern dates' relevant newest sections were actually read: yesterday CD/CF/ZD/RF/NC/AP/Lean, and today UB/CR, BR, RD, PC, UC, LC and repaired DG. All earlier claim IDs and review distinctions are preserved. In particular LC accepted HM1 and UC1-UC3 only at their stated scope; AP accepted CF1-CF4; repaired DG2 has its own #1128 evidence. UB, PC and RD author-level claims are not silently independently accepted here.

The external inbox has no newer entry than October 18. Its full latest handoff was retrieved (aeb5fa075701c9c0e38ddf02f6c2f571c13fdbc9); EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain their weighted, root-prime and denominator cautions. Historical routing/status prose does not override current main; no stale PR status is reused as live evidence.

Verified existing formal evidence, separate from JC's paper/computational status:

- #1119: exact-head success and transitive/source audit detailed in B; no changed pre-existing native/OAI source files at main.
- #1115: [run 42517562043, job 128843815559](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42517562043/job/128843815559), head 7256681db5adfc907426deaef676244aeb4384dd, completed/success; hosted log shows the actual band/consumer declarations, standard axiom lists and warning-fatal acceptance. The generic growth consumer requires its hgrowth argument, supplied only at the verified baseline above.
- #1127: run 42743502306 at 866b3d2121309cdd854f9d64e2a6adbbc708ef9b completed/success; merged. Its original proper-cofactor source was read; no new quantitative bridge to Q_R follows.
- #1128: run 42798625661 at d5b8003f6239611a457560b6fd16e29f16255e75 completed/success; merged. This replaces the earlier failed #1125 proof bytes, not its historical CI status.
- Open/draft PR collection was empty at intake. No PR, code, issue, workflow, policy, permission, schedule or main write was performed by this role.

Execution limitations: direct git clone returned CONNECT tunnel HTTP 403; the GitHub connector supplied working pinned reads and own-report writes. No external analytic theorem beyond the verified repository baseline is needed for JC1-JC4. No independent Referee execution or new Lean proof is claimed. Publication is not certified until immutable readback.

Resume from the actual square-index bridge, not saturated-cutoff optimization. Preserve R=56's full numbers, the q^2=R exclusion, all z<9 terms, shifted historical K_R and the diagonal distinction. Highest-value next question: an arithmetic restriction on the COMPLETE upper/deep/diagonal interaction that is not a renamed desired bound; otherwise advance MU-LIFT's distinct full-prefix recurrence rather than rerun these tests.

The early JC checkpoint commit e10ad61c95a6cab0223125c4d4fc369c7bf0ebb5, report blob 9c033d8d1a92e7a8891c10841353e30ee2babdb6, was read back byte-for-byte. The final publication receipt follows after the substantive report has actually been written and verified.

### N. Immutable Source And Continuity Ledger

Freshness rechecked at 2026-11-10 15:39:07 UTC / 10:39:07 EST: main remains 655f897e274a8ba8a2fed80ecc1fc75a0d849174; agent-reports is e10ad61c95a6cab0223125c4d4fc369c7bf0ebb5; the open/draft PR collection is empty. The report branch is still the own checkpoint atop the intake snapshot, so the other role reports listed below have not changed. This is a source/status refresh, not a new compilation.

All source blobs below were fetched at that pinned main and inspected at the relevant declaration or policy sections. File-level retrieval is not a claim to have independently reproved every declaration in the file.

| Main source | Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/AGENTS.md) | c9c89f01b90b526de9f3e8ea92478e36504711b6 |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/CURRENT_PROOF_CONTRACT.md) | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| [RHLean/Proof/RootSmoothCrossRegionGram.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/RHLean/Proof/RootSmoothCrossRegionGram.lean) | 8c439ea221749b0af23276bfd709ec3e019fcc1d |
| [RHLean/Proof/SquareRootAncestryRoot.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/RHLean/Proof/SquareRootAncestryRoot.lean) | 69668e5305c95ad7a4a9f88c74a8149298bab87b |
| [docs/COORDINATE_ATLAS.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/docs/COORDINATE_ATLAS.md) | cd0419d00a37739fe5a292f5cb738e33213949d5 |
| [docs/DYNAMIC_RESEARCH_AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/docs/DYNAMIC_RESEARCH_AGENTS.md) | 0f0b63a82380e18068ab7f3c317feafd66939290 |
| [docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md) | e922d4ba9362a1ae196af8f6de88f7417f92087c |
| [docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md) | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| [docs/search/coordinates/COORD-CORR4-PARENT.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/docs/search/coordinates/COORD-CORR4-PARENT.md) | 0d4304a44970c9c1d9c74b5ac5ca57f07fa4cff9 |
| [docs/search/coordinates/COORD-CORR4-REMAINDER.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/docs/search/coordinates/COORD-CORR4-REMAINDER.md) | c0e897ac4eb2e3b83b5e5f41e6654136bed0b89f |
| [research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean) | ebca096e83009a7df514d00b6a2696be86a94c55 |
| [research/CORR4_FRAME_ONLY_INVERSE_20261026.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/CORR4_FRAME_ONLY_INVERSE_20261026.lean) | fe318e29f348644bdd0896eba897a1d12b8d38ec |
| [research/CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026.lean) | a4abeb13653076bedd8e1173c933ee3324bfea26 |
| [research/CORR4_OAI_POWER_DETERMINISTIC_FRAME_20261025.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/CORR4_OAI_POWER_DETERMINISTIC_FRAME_20261025.lean) | ad6d4a0adddd3c730f64e61d22f80282a8e5bfbb |
| [research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean) | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a |
| [research/CORR4_OAI_RESTORED_PHYSICAL_KERNEL_20261024.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/CORR4_OAI_RESTORED_PHYSICAL_KERNEL_20261024.lean) | a71d24ee7660f425c0ae7d8918f30c1eea94f313 |
| [research/CompleteSquareRootWheelFractionalBoundary.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/CompleteSquareRootWheelFractionalBoundary.lean) | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| [research/DyadicPrimeNearResonance.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/DyadicPrimeNearResonance.lean) | f416e0149b73656e30a7f68a3934a937353d3f8d |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| [research/EULER_SELF_DUAL_POINTWISE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/EULER_SELF_DUAL_POINTWISE_20261027.lean) | c327c556f39ee7014fd774b24d0f95a1ece050e0 |
| [research/FiniteWheelCofactorPositivity.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/FiniteWheelCofactorPositivity.lean) | f83a3daefc2b9d603014af912ec82b4a7f52cfac |
| [research/GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/GLOBAL_RETURNED_CORE_POST789_CORRELATION_EQUIVALENCE.lean) | 05b45e726bba7d245ef868b44a2455bcdaf9d304 |
| [research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/GLOBAL_RETURNED_CORE_POST789_DIAGONAL_SUBTRACTED_CONTROL.lean) | ba95beda901719afaabca9011b8dbae6fc69662d |
| [research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean) | d17aeb639bb47d79333cf0d00760c2604feddfdf |
| [research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_FIRST_OWNER_ENERGY.lean) | ac8015a1dd87aea23d35d57f5102efd38f4a105b |
| [research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean) | 29bb263ddd07b12a2dd5ccf6a12aecaf627134d8 |
| [research/GLOBAL_RETURNED_CORE_THRESHOLD_INCIDENCE_KERNEL.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/GLOBAL_RETURNED_CORE_THRESHOLD_INCIDENCE_KERNEL.lean) | bb9f30058252e5dbb8ba43b048748fbb5b50ee72 |
| [research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean) | dbaf123113b544d0b19c7c3c6b92a1288a26cfb8 |
| [research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean) | f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8 |
| [research/MERTENS_EXPONENT_ENVELOPES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/MERTENS_EXPONENT_ENVELOPES.lean) | 655b896e8d5a41c9f8fc3c456eae3944a98bfefe |
| [research/TWOAB_OAI_COMPLETE_PACKET_ATTACK_20261108.md](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/TWOAB_OAI_COMPLETE_PACKET_ATTACK_20261108.md) | 3398233bd2ef291a2ff8f65e250e06939b028380 |
| [research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean) | 028d9f2bbfa1a8de1fe63e9bd368aca13aae6825 |
| [research/TWOAB_RENEWAL_OAI_CONSUMER_20261108.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/TWOAB_RENEWAL_OAI_CONSUMER_20261108.lean) | 4880969f71f4668b18a9e09fd6f4007b7e62a5d5 |
| [research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| [research/WEIGHTED_EULER_BOUNDARY_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/WEIGHTED_EULER_BOUNDARY_20261027.lean) | 41740a50510e781e94b95a6b60115ae21295aa60 |
| [research/oai_434/VF919ExplicitAmplificationBound.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919ExplicitAmplificationBound.lean) | f3cb6dbe1eb53c910c9b4b203d98ff849bd27dd3 |
| [research/oai_434/VF919ExplicitFixedSourceSlotCount.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |
| [research/oai_434/VF919ExplicitSquareBlockPacking.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | 32999039fdeea99c58a070c1c4ee9c140720dd44 |
| [research/oai_434/VF919NativeSevenEighthsReplay.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919NativeSevenEighthsReplay.lean) | 111c933a7ca15647105ce6a4d0f3cbfc3cde81f4 |
| [research/oai_434/VF919NativeStrictMertens.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919NativeStrictMertens.lean) | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| [research/oai_434/VF919TotalMassEndpoint.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919TotalMassEndpoint.lean) | 827bb952c4d4311d75fd03a2470799dc10b0f7e7 |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919WindowErrorClosure.lean) | f629db1b2b65d6ec042ac9432397d4b6316200c6 |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | 1f17f9401a63d16227db2e2aad020b9f74bc5f4e |

Both Eastern report dates were read at immutable report-branch snapshot bb52e26c1dac8bd7222f74fd34969392ba1f6127. The prior own November 10 SHA is the version before this invocation's append. Coordinator 00/90 mirror blobs agree on both dates.

| Report | November 9 blob | November 10 intake blob |
| --- | --- | --- |
| [00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/bb52e26c1dac8bd7222f74fd34969392ba1f6127/research/agent_reports/2026-11-10/00-coordinator-am.md) | 6fba43130391ad4a606aa3809c20f344d668c709 | 1cf71a74d0e80d5dc05ab1ef08f1ad6fcf134c9a |
| [10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/bb52e26c1dac8bd7222f74fd34969392ba1f6127/research/agent_reports/2026-11-10/10-owner-payment.md) | 643e8a004d9d8e0be102b03e2f79bb3b217ae916 | ece5b3cd8d25b45e64c48812c81d71f6eddf23a9 |
| [20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/bb52e26c1dac8bd7222f74fd34969392ba1f6127/research/agent_reports/2026-11-10/20-analytic-type-ii.md) | d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3 | a2675374a7160955917d42797eef5a3e2358056f |
| [30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/bb52e26c1dac8bd7222f74fd34969392ba1f6127/research/agent_reports/2026-11-10/30-finite-wheel.md) | 0624246d03b19cf76c01e186b7d868a248d896ef | 79ff39e0f79a30f4cf1657b22f96ebe49de4d717 |
| [40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/bb52e26c1dac8bd7222f74fd34969392ba1f6127/research/agent_reports/2026-11-10/40-prime-census.md) | 8c927cc6c323533ba1cfd369404b25aa4f9cef91 | 8a89d1a899850e39320a96bf35a6f221060fc8a7 |
| [50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/bb52e26c1dac8bd7222f74fd34969392ba1f6127/research/agent_reports/2026-11-10/50-adversarial-referee.md) | a5d0192eb31c0efb3767187a7752f1a0d07f8534 | ae7de1cb1900818b8844c2c3c7da597cc8f7eaa9 |
| [60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/bb52e26c1dac8bd7222f74fd34969392ba1f6127/research/agent_reports/2026-11-10/60-lean-verification.md) | 8b60c6136ac151774be2db0aee8f543f286b53aa | 0355c3203ede834e1abbe9bc2fc161bc7d7ece04 |

Upstream timestamp/claim receipts retained at their reported scope (not independent acceptance by this role): Coordinator UB/CR publication 2026-11-10 07:54:41 EST; Owner BR 08:43:47 EST; Analytic RD 09:49:11 EST; earlier own PC 02:34:18 EST; Census UC 03:45:53 EST; Referee LC 04:35:30 EST. Lean's latest synthesis was prepared 2026-11-10T10:30:27Z and records immutable substantive commit 7f7187352f5bb8d6202af358a7d50e7db921d2dd; its then-unmerged PR statuses are superseded here only by verified current PR metadata. Yesterday's final own RF readback was 2026-11-09 23:33:12 UTC; Owner CF 21:37:53 UTC; Analytic ZD 22:36:48 UTC; Census NC 2026-11-10 00:24:24 UTC; Referee AP 2026-11-10 01:33:06 UTC; Coordinator CD 2026-11-10 04:31:59 UTC. These UTC dates do not change their original Eastern report dates.

External inbox [EXTERNAL_HANDOFFS.md](https://github.com/OVVO-Financial/RH_Lean/blob/bb52e26c1dac8bd7222f74fd34969392ba1f6127/research/agent_reports/EXTERNAL_HANDOFFS.md) blob 038018145c0fddb2f6306c0712373adf9cd1ea52 and the full latest external handoff blob aeb5fa075701c9c0e38ddf02f6c2f571c13fdbc9 were retrieved. No later handoff was present. All source, claim and referee qualifications in M remain in force.

### O. Reproducible Registration, Programs And Output

The following are the exact local registration and final program/output bytes corresponding to the SHA-256 receipts in H. Run the two programs with assertions enabled; the executable uses approximately 0.5 GB of memory at the registered largest root. No Lean installation is required. The codes compute genuine integer Mobius data rather than surrogate signs.

```text
# JC Exact Test Registration

Registered 2026-11-10, after original-source derivation and before computation.

- Source: R>=56, X=R^2-1, m=M(R-1), t_z=M(X//z)-M(X//(z+1)); actual odd primes q with q*q<R.
- Exact bridge: B_j=sum(z=j..R-1)t_z, U=sum_q M(X//q^2)/q, E=sum_q M(X//q^2)^2, and each daughter equals m+B_(q^2).
- Set Y=X//9, W=M(X)-M(Y), V=M(Y)-m. Test the two deliberately optimistic hypotheses H_SIGN: W^2+2W(V+U)<=0 and H_CREDIT: W^2+2W(V+U)<=2E. These are tested proposals, not claims attributed to an upstream agent.
- Keep the physical diagonal: D_top=sum_(Y<n<=X)mu(n)^2; D_deep=sum_(R<=n<=Y)(1+2d(n))*mu(n)^2. The actual top contribution is W^2+2W(V+U)-D_top. A failure before diagonal subtraction is not a failure of the diagonal-restored claim.
- Test every integer R=56..300, plus held-out roots 549 and 5561. No constants will be fitted. Record both signs and exact first failures in the declared range.
- Independently use trial factorization for R=56..80 and selected boundary roots 9,10,25,26,49,50,56,57,73. Check squareful zeros, q*q=R, root-prime R, cofactor one, direct ordered Q, K_R, band partitions, and both Gram orientations.
- Novelty/scope: existing coefficient, band, common-clock, and mixed-tail identities are credited. This test can refute a proposed transfer, not prove a uniform bound or a new route.
```

#### Integer Source Program: jc_probe.cpp

```cpp
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>

int main() {
    std::vector<int> roots;
    for (int r = 56; r <= 300; ++r) roots.push_back(r);
    roots.push_back(549);
    roots.push_back(5561);
    const int limit = roots.back() * roots.back() - 1;
    std::vector<int> least(limit + 1), primes;
    std::vector<int8_t> mu(limit + 1);
    mu[1] = 1;
    for (int n = 2; n <= limit; ++n) {
        if (!least[n]) {
            least[n] = n;
            primes.push_back(n);
            mu[n] = -1;
        }
        for (int p : primes) {
            if (p > least[n] || int64_t(n) * p > limit) break;
            least[n * p] = p;
            mu[n * p] = (p == least[n]) ? 0 : -mu[n];
        }
    }
    std::vector<int> M(limit + 1), sf(limit + 1);
    for (int n = 1; n <= limit; ++n) {
        M[n] = M[n - 1] + mu[n];
        sf[n] = sf[n - 1] + mu[n] * mu[n];
    }
    for (int z = 1; z < roots.back(); ++z) {
        int renewal = 0;
        for (int k = 1; k <= z; ++k) renewal += M[z / k];
        assert(renewal == 1);
    }
    std::cout << "{\"limit\":" << limit << ",\"rows\":[";
    bool comma = false;
    for (int r : roots) {
        const int x = r * r - 1, y = x / 9, m = M[r - 1];
        int64_t diag = 0, cross = 0, kn = 0, kd = 1;
        int ky = 0;
        for (int a = 1; a < r; ++a) {
            diag += int64_t(mu[a]) * mu[a] * (x / (a * a));
            for (int b = a + 1; b < r; ++b)
                cross += int64_t(mu[a]) * mu[b] * (x / (a * b));
        }
        assert(diag + 2 * cross == 2 * m - M[x]);
        for (int n = 0; n < r; ++n) {
            const int64_t num = int64_t(M[n] - 1) * (M[n] - 1);
            if (num * kd > kn * (n + 1)) {
                kn = num; kd = n + 1; ky = n;
            }
        }
        std::vector<int> tail(r), bands(r + 1);
        for (int z = 1; z < r; ++z)
            tail[z] = M[x / z] - M[x / (z + 1)];
        for (int z = r - 1; z >= 1; --z)
            bands[z] = bands[z + 1] + tail[z];
        assert(bands[1] == M[x] - m);
        for (int j = 1; j < r; ++j)
            assert(bands[j] == M[x / j] - m);
        int witness = y + 1;
        while (least[witness] != witness) ++witness;
        if (comma) std::cout << ',';
        comma = true;
        std::cout << "{\"R\":" << r << ",\"m\":" << m
                  << ",\"MX\":" << M[x] << ",\"MY\":" << M[y]
                  << ",\"SFm\":" << sf[r - 1] << ",\"SFX\":" << sf[x]
                  << ",\"SFY\":" << sf[y] << ",\"Qdiag\":" << diag
                  << ",\"Qcross\":" << cross << ",\"K\":[" << kn << ',' << kd
                  << "],\"Karg\":" << ky << ",\"top_prime\":" << witness
                  << ",\"t1\":" << tail[1] << ",\"owners\":[";
        bool qc = false;
        for (int q : primes) {
            if (q >= r) break;
            const int cutoff = x / (q * q);
            assert((q * q < r && cutoff >= r + 1) ||
                   (q * q >= r && cutoff <= r - 1));
            if (q == 2 || q * q >= r) continue;
            assert(M[cutoff] == m + bands[q * q]);
            if (qc) std::cout << ',';
            qc = true;
            std::cout << '[' << q << ',' << cutoff << ',' << M[cutoff]
                      << ',' << sf[cutoff] << ']';
        }
        std::cout << "]}";
    }
    std::cout << "]}\n";
}
```

#### Exact Rational And Independent Trial Check: jc_verify.py

```python
import json
import math
import subprocess
import sys
from fractions import Fraction as F


def trial_mu(n):
    if n == 0:
        return 0
    sign, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


raw = json.loads(subprocess.check_output([sys.argv[1]], text=True))
records = []
first = {}
counts = {"T_positive": 0, "T_negative": 0, "T_zero": 0,
          "credit_fail": 0, "diagonal_restored_positive": 0}
for row in raw["rows"]:
    r = row["R"]
    x = r * r - 1
    m, mx, my = row["m"], row["MX"], row["MY"]
    w, v, g = mx - my, my - m, mx - m
    u = sum((F(mq, q) for q, yq, mq, sfq in row["owners"]), F(0))
    e = sum(mq * mq for q, yq, mq, sfq in row["owners"])
    dtop = row["SFX"] - row["SFY"]
    ddeep = row["SFY"] - row["SFm"] + 2 * sum(
        (F(sfq - row["SFm"], q) for q, yq, mq, sfq in row["owners"]), F(0))
    t = w * w + 2 * w * (v + u)
    deep = v * v + 2 * v * u - ddeep
    mixed = g * g + 2 * g * u - ddeep - dtop
    assert mixed == deep + t - dtop
    assert (g + u) ** 2 == u * u + mixed + ddeep + dtop
    assert row["Qdiag"] + 2 * row["Qcross"] == 2 * m - mx
    sign = "positive" if t > 0 else "negative" if t < 0 else "zero"
    counts["T_" + sign] += 1
    first.setdefault(sign, r)
    if t > 2 * e:
        counts["credit_fail"] += 1
        first.setdefault("credit_fail", r)
    if t > dtop:
        counts["diagonal_restored_positive"] += 1
        first.setdefault("diagonal_restored_positive", r)
    rec = {"R": r, "m": m, "MX": mx, "MY": my, "W": w, "V": v,
           "U": str(u), "E": e, "T": str(t), "T_minus_2E": str(t - 2 * e),
           "Dtop": dtop, "T_minus_Dtop": str(t - dtop),
           "twice_mixed": str(mixed), "mixed_minus_2E": str(mixed - 2 * e),
           "Q": 2 * m - mx, "Qdiag": row["Qdiag"],
           "Qcross": row["Qcross"], "K": str(F(*row["K"])),
           "Karg": row["Karg"], "top_prime": row["top_prime"]}
    if 56 <= r <= 80:
        mu = [trial_mu(n) for n in range(x + 1)]
        mt = [0]
        for a in mu[1:]:
            mt.append(mt[-1] + a)
        assert (m, mx, my) == (mt[r - 1], mt[x], mt[x // 9])
        assert F(*row["K"]) == max(F((mt[n] - 1) ** 2, n + 1) for n in range(r))
        direct_q = sum(mu[a] * mu[b] * (x // (a * b))
                       for a in range(1, r) for b in range(1, r))
        assert direct_q == rec["Q"]
        d = [sum((F(1, q) for q, yq, mq, sfq in row["owners"] if n <= yq), F(0))
             for n in range(x + 1)]
        assert sum(d[n] * mu[n] for n in range(1, x + 1)) == u
        assert sum((1 + 2 * d[n]) * mu[n] ** 2 for n in range(r, x + 1)) == ddeep + dtop
        assert all(d[n] == 0 for n in range(x // 9 + 1, x + 1))
        rec["top_eight_bands"] = [mt[x // z] - mt[x // (z + 1)] for z in range(1, 9)]
        rec["daughter_input"] = row["owners"]
        for n in {r, x, row["top_prime"], *(q * q for q, _, _, _ in row["owners"])}:
            coefficient = sum(mu[a] * mu[b]
                              for a in range(1, min(r, n + 1)) if n % a == 0
                              for b in range(1, min(r, n // a + 1)) if (n // a) % b == 0)
            assert coefficient == (mu[n] if n < r else -mu[n])
    records.append(rec)

# Independently verify the strict square threshold and squareful zero boundary.
boundary_checks = 0
for r in [9, 10, 25, 26, 49, 50, 56, 57, 73]:
    x = r * r - 1
    for q in range(2, r):
        yq = x // (q * q)
        assert yq >= r + 1 if q * q < r else yq <= r - 1
        boundary_checks += 1
    assert trial_mu(r * r) == 0

selected = {56, 57, 73, 80, 300, 549, 5561, *first.values()}
print(json.dumps({"limit": raw["limit"], "roots": len(records),
                  "first_in_declared_range": first, "counts": counts,
                  "independent_trial_roots": 25, "boundary_checks": boundary_checks,
                  "renewal_checks": 5560,
                  "selected_rows": [row for row in records if row["R"] in selected]}, indent=2))
```

#### Reproduction Commands

```sh
g++ -std=c++17 -O2 -Wall -Wextra -Werror jc_probe.cpp -o jc_probe
python jc_verify.py ./jc_probe > jc-results.json
sha256sum jc-test-plan.md jc_probe.cpp jc_verify.py jc-results.json
```

#### Frozen Exact Output: jc-results.json

```json
{
  "limit": 30924720,
  "roots": 247,
  "first_in_declared_range": {
    "positive": 56,
    "credit_fail": 56,
    "negative": 60,
    "zero": 79
  },
  "counts": {
    "T_positive": 183,
    "T_negative": 60,
    "T_zero": 4,
    "credit_fail": 131,
    "diagonal_restored_positive": 0
  },
  "independent_trial_roots": 25,
  "boundary_checks": 337,
  "renewal_checks": 5560,
  "selected_rows": [
    {
      "R": 56,
      "m": -2,
      "MX": 6,
      "MY": 2,
      "W": 4,
      "V": 4,
      "U": "34/105",
      "E": 6,
      "T": "5312/105",
      "T_minus_2E": "4052/105",
      "Dtop": 1698,
      "T_minus_Dtop": "-172978/105",
      "twice_mixed": "-68044/35",
      "mixed_minus_2E": "-68464/35",
      "Q": -10,
      "Qdiag": 4712,
      "Qcross": -2361,
      "K": "3/2",
      "Karg": 5,
      "top_prime": 349,
      "top_eight_bands": [
        9,
        3,
        -5,
        2,
        -1,
        4,
        -5,
        -3
      ],
      "daughter_input": [
        [
          3,
          348,
          2,
          212
        ],
        [
          5,
          125,
          -1,
          77
        ],
        [
          7,
          63,
          -1,
          39
        ]
      ]
    },
    {
      "R": 57,
      "m": -2,
      "MX": 17,
      "MY": -1,
      "W": 18,
      "V": 1,
      "U": "-71/105",
      "E": 3,
      "T": "11748/35",
      "T_minus_2E": "11538/35",
      "Dtop": 1758,
      "T_minus_Dtop": "-49782/35",
      "twice_mixed": "-61286/35",
      "mixed_minus_2E": "-61496/35",
      "Q": -21,
      "Qdiag": 4883,
      "Qcross": -2452,
      "K": "3/2",
      "Karg": 5,
      "top_prime": 367,
      "top_eight_bands": [
        29,
        -7,
        -5,
        6,
        -6,
        6,
        -5,
        0
      ],
      "daughter_input": [
        [
          3,
          360,
          -1,
          219
        ],
        [
          5,
          129,
          -1,
          79
        ],
        [
          7,
          66,
          -1,
          41
        ]
      ]
    },
    {
      "R": 60,
      "m": -1,
      "MX": 0,
      "MY": 1,
      "W": -1,
      "V": 2,
      "U": "-46/105",
      "E": 18,
      "T": "-223/105",
      "T_minus_2E": "-4003/105",
      "Dtop": 1949,
      "T_minus_Dtop": "-204868/105",
      "twice_mixed": "-243136/105",
      "mixed_minus_2E": "-246916/105",
      "Q": -2,
      "Qdiag": 5414,
      "Qcross": -2708,
      "K": "3/2",
      "Karg": 5,
      "top_prime": 401,
      "top_eight_bands": [
        6,
        -2,
        -5,
        4,
        -7,
        7,
        4,
        -8
      ],
      "daughter_input": [
        [
          3,
          399,
          1,
          243
        ],
        [
          5,
          143,
          -1,
          89
        ],
        [
          7,
          73,
          -4,
          46
        ]
      ]
    },
    {
      "R": 73,
      "m": -3,
      "MX": 1,
      "MY": 7,
      "W": -6,
      "V": 10,
      "U": "179/105",
      "E": 59,
      "T": "-3656/35",
      "T_minus_2E": "-7786/35",
      "Dtop": 2878,
      "T_minus_Dtop": "-104386/35",
      "twice_mixed": "-23910/7",
      "mixed_minus_2E": "-24736/7",
      "Q": -7,
      "Qdiag": 8035,
      "Qcross": -4021,
      "K": "3/2",
      "Karg": 5,
      "top_prime": 593,
      "top_eight_bands": [
        -9,
        16,
        -7,
        8,
        -6,
        3,
        8,
        -19
      ],
      "daughter_input": [
        [
          3,
          592,
          7,
          361
        ],
        [
          5,
          213,
          -1,
          131
        ],
        [
          7,
          108,
          -3,
          67
        ]
      ]
    },
    {
      "R": 79,
      "m": -3,
      "MX": -9,
      "MY": -9,
      "W": 0,
      "V": -6,
      "U": "-122/35",
      "E": 86,
      "T": "0",
      "T_minus_2E": "-172",
      "Dtop": 3372,
      "T_minus_Dtop": "-3372",
      "twice_mixed": "-416576/105",
      "mixed_minus_2E": "-434636/105",
      "Q": 3,
      "Qdiag": 9413,
      "Qcross": -4705,
      "K": "3/2",
      "Karg": 5,
      "top_prime": 701,
      "top_eight_bands": [
        -15,
        -2,
        12,
        -2,
        6,
        -7,
        0,
        8
      ],
      "daughter_input": [
        [
          3,
          693,
          -9,
          423
        ],
        [
          5,
          249,
          -1,
          153
        ],
        [
          7,
          127,
          -2,
          78
        ]
      ]
    },
    {
      "R": 80,
      "m": -4,
      "MX": -25,
      "MY": -5,
      "W": -20,
      "V": -1,
      "U": "-226/105",
      "E": 30,
      "T": "11048/21",
      "T_minus_2E": "9788/21",
      "Dtop": 3456,
      "T_minus_Dtop": "-61528/21",
      "twice_mixed": "-379852/105",
      "mixed_minus_2E": "-386152/105",
      "Q": 17,
      "Qdiag": 9653,
      "Qcross": -4818,
      "K": "3/2",
      "Karg": 5,
      "top_prime": 719,
      "top_eight_bands": [
        -36,
        9,
        9,
        -7,
        8,
        -9,
        0,
        6
      ],
      "daughter_input": [
        [
          3,
          711,
          -5,
          435
        ],
        [
          5,
          255,
          -1,
          157
        ],
        [
          7,
          130,
          -2,
          80
        ]
      ]
    },
    {
      "R": 300,
      "m": -5,
      "MX": 11,
      "MY": -23,
      "W": 34,
      "V": -18,
      "U": "-460631/51051",
      "E": 583,
      "T": "-2046728/3003",
      "T_minus_2E": "-5548226/3003",
      "Dtop": 48630,
      "T_minus_Dtop": "-148082618/3003",
      "twice_mixed": "-15222888448/255255",
      "mixed_minus_2E": "-15520515778/255255",
      "Q": -21,
      "Qdiag": 136513,
      "Qcross": -68267,
      "K": "3/2",
      "Karg": 5,
      "top_prime": 10007
    },
    {
      "R": 549,
      "m": 3,
      "MX": 192,
      "MY": -5,
      "W": 197,
      "V": -8,
      "U": "-95673143/111546435",
      "E": 487,
      "T": "3939716014453/111546435",
      "T_minus_2E": "3831069786763/111546435",
      "Dtop": 162875,
      "T_minus_Dtop": "-14228409586172/111546435",
      "twice_mixed": "-322902630744/1956955",
      "mixed_minus_2E": "-324808704914/1956955",
      "Q": -186,
      "Qdiag": 457582,
      "Qcross": -228884,
      "K": "3/2",
      "Karg": 5,
      "top_prime": 33493
    },
    {
      "R": 5561,
      "m": 5,
      "MX": -2544,
      "MY": -407,
      "W": -2137,
      "V": -412,
      "U": "-2468042808745921966683963490244/20364840299624512075310661735",
      "E": 196306,
      "T": "139410139240381211690531295859407751/20364840299624512075310661735",
      "T_minus_2E": "131414658560665032755619426334305931/20364840299624512075310661735",
      "Dtop": 16711107,
      "T_minus_Dtop": "-200908886044556069422777230634982894/20364840299624512075310661735",
      "twice_mixed": "-91935950308971150372533252405599636/6788280099874837358436887245",
      "mixed_minus_2E": "-94601110535543210017503875580633576/6788280099874837358436887245",
      "Q": 2554,
      "Qdiag": 46995004,
      "Qcross": -23496225,
      "K": "3/2",
      "Karg": 5,
      "top_prime": 3436127
    }
  ]
}
```



### Verified Publication Receipt - 20261110-wheel-2/JC

At 2026-11-10 15:41:11 UTC / 10:41:11 EST, substantive commit 704b64e64bafb09c7a01fc82bf668a4f1d5743a7, report blob e915faa73e5f39c757df1bfdebe6d8c54fc2906f, was re-fetched at that IMMUTABLE commit. All 122358 characters matched the intended report exactly; the previous 58509-character report is an unchanged prefix. Commit inspection confirmed one changed path, research/agent_reports/2026-11-10/30-finite-wheel.md, with 1005 additions and zero deletions. A fresh current-branch read also retained that full content before this receipt was appended.

SUBSTANTIVE_PUBLICATION=PUBLISHED_AND_READBACK_VERIFIED; EXECUTION=COMPLETE. JC1-JC2 remain supporting PAPER_PROOF / IDENTITY_ONLY / SELF_AUDIT; JC3 is exact falsification of H_SIGN and H_CREDIT only; JC4 is FINITE_COMPUTATION. INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED; NO_NEW_GLOBAL_GAIN / NO_NEW_ACCEPTED_ROUTE / VERIFIED_ETA=NONE. The diagonal-restored full source, uniform endpoint estimate and RH remain OPEN. The only remote changes were authorized own-report commits on agent-reports. No source file, other report, workflow, PR, main, permission or schedule was changed; no branch was created or deleted, and no agent or Lean process was launched. This receipt records completed verification and does not assert its own not-yet-known commit hash.


## Scheduled Completed-Defect Checkpoint - 20261110-wheel-3/RC

Actual scheduled trigger: 2026-11-10 18:06:01 EST, America/New_York. Platform run ID unavailable. This is a continuation of the existing daily report, preserving PC/JC and all earlier evidence. `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. `EXECUTION=IN_PROGRESS`; no new mathematical result is certified by this checkpoint.

Current main: f7947bee036c4dddb0c36fc9f53ab46b4fa90995, human merge of #1130. Authority blobs: AGENTS c9c89f01b90b526de9f3e8ea92478e36504711b6; contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038; cross-route directive e922d4ba9362a1ae196af8f6de88f7417f92087c. Open/draft PR collection was empty. Both November 10 and November 9 role reports and external inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 were retrieved. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD. Relevant latest handoffs include Coordinator MD, Analytic IR, Owner DR, own JC, Census UC, Referee SR and Lean RD. MD/IR are paper proposals, not replacements for the certified #1119 baseline. #1130 certifies a local response only.

Registered investigation: apply the already-proved Mobius renewal to the COMPLETE fixed-y descendant sum of Owner BR/DR's literal floor-Li lifting defect. Keep every (q,a,k) occurrence with q>y and qak<=X, including all parity sectors, cofactor one and both quadratic cross orientations. Test whether complete fixed-q fibres reduce to prime-factor-supported survivors and whether their physical-integer coefficients have a once-only radical description. This is distinct from DR's uncompleted defect and JC's squared-prime daughter sampling.

Proposed quantitative mechanism, NOT yet claimed proved: preserve the signed descendant completion before taking absolute values; then use event sparsity and a rad(d)-split to bound the entire completed defect by O(X loglog X/log X), without importing a Mertens power bound. Determine explicitly whether this changes the complete prime-side consumer or merely bounds an auxiliary quantity. No new global exponent or RH route is presumed.

Frozen falsification plan: exact discovery roots R=3..40, held-outs 47,64,97; X=R^2-1, y=R-1 throughout every descendant. Test original triple sums, completed per-event signs, physical radical coefficients, full lifted-innovation/defect return and complete squares. Test H_LOCAL (every completed physical coefficient is nonnegative) and H_TOTAL (the completed full defect is nonnegative), keeping these distinct. Use certified floor-Li floors for genuine-event witnesses, with a separately trial-factored reconstruction. Additional small general (y,X) cases will test strict versus nonstrict endpoints. Verify the proposed positive counting bound independently for integer cutoff choices. Finite success is not an all-scale proof.

Baseline dependency/log refresh, novelty search, proof, tests and publication remain PENDING. No local Lean, source modification, PR, merge, schedule change, agent launch or other-report write is authorized or performed. Only this owned report is changed remotely.


## Completed Defect Cancellation And A Radical Counting Bound
### Research Synthesis - 20261110-wheel-3/RC

### A. Most Important Structural Discovery

**Completing every reciprocal descendant BEFORE taking absolute values removes the harmonic loss in the floor-Li lifting defect.** At a fixed physical integer, the complete divisor cancellation leaves at most two contributions: its own floor-Li event and one event at its radical. The resulting coefficient is in {-1,0,1,2}, with a precisely classified negative sector. The full completed auxiliary source admits an elementary uniform bound of order X loglog X / log X, without a Mertens power theorem or prime-distribution premise.

More precisely, for integers y>=3 and y<X<(y+1)^2, put N=floor(X/(y+1)), L(n)=floor(Li_2(n)), lambda(q)=L(q)-L(q-1), and

```text
D_y(T)=sum_(y<q<=T)lambda(q)sum_(a<=T/q)[mu(a)+mu(aq)],
Dhat_y(X)=sum_(k=1..N)D_y(floor(X/k)).
```

The ENTIRE completed defect, including even-parity, odd-parity and squareful event q, satisfies

```text
|Dhat_y(X)| <= X*(10+3*log(log y))/log y + N + 1.       (RC.A)
```

The same bound controls the sum of the absolute values of the COMPLETED q-packets, and a stronger norm allowing any bounded physical-(q,n) mask as defined below. In particular, at y=R-1, X=R^2-1, R>=4, the right side is

```text
(R^2-1)*(10+3*log(log(R-1)))/log(R-1) + R.
```

This improves Owner DR4's stated descendant-triangle bound O_delta(X*(log R)^delta), for every fixed delta>0, and removes its use of a certified Mertens envelope. It is NOT an improvement of the canonical prime discrepancy or the global Mertens exponent. The original complete prime-side source still contains the lifted innovation and historical anchor; their exact reassembly is retained in G.

| Claim | Classification and actual contribution |
| --- | --- |
| 20261110-wheel-3/RC1 | Exact fixed-event completion and radical coefficient. IDENTITY_ONLY / supporting source adapter, derived from existing restricted-floor/renewal theorems and Owner DR1, not a new convolution law. |
| RC2 | Complete physical coefficient/sign classification, explicit sign-reversing involutions, and mask-invariance criterion. PAPER_PROOF / supporting arithmetic restriction on the completed auxiliary source. |
| RC3 | Explicit uniform counting bound (RC.A), including bounded (q,n)-masked completion. PAPER_PROOF / independent quantitative auxiliary result; no Mertens or PNT assumption. |
| RC4 | Exact full prime-side return and inverse-completion loss. IDENTITY_ONLY / PAPER_PROOF application; no complete endpoint gain. |
| RC5 | H_LOCAL refuted at R=13,n=156; descendant-mask transfer refuted at R=28,q=78,n=780; exact registered validation. FINITE_COMPUTATION. |

All new derivations are SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. No independent Referee verdict is manufactured. **NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE.** This is a successful supporting recovery, not a newly admitted RH route or a claim that the complete physical source meets the new-route admission criterion.

### B. Current Authoritative Objective

Actual configured trigger: 2026-11-10 18:06:01 EST, America/New_York. Platform RUN_ID_UNAVAILABLE. This is the same invocation as the RC checkpoint, not an additional launch. Main was pinned to **f7947bee036c4dddb0c36fc9f53ab46b4fa90995**. `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. The later main AGENTS priority supersedes the contract's older single-wheel task priority, not its mathematical safeguards or permissions.

The canonical `VFCanonicalSquareVonKochStatement` remains OPEN: one C>=0, chosen before integer R>=2, with |pi(R^2)-VF_can(R^2)|<=C R log R. The terminal `riemannHypothesis_of_vfCanonicalSquare` still takes both this arithmetic statement and `ClassicalVonKochRHCriterion`. Its exact VF/Li_2 offset must not be replaced by principal-value li without the fixed normalization correction.

The complete wheel remains F_R-D_R=li(R^2-1)-pi(R^2-1), retaining every virtual divisor until its Euler compensation. The historical finite-AC source remains Q_R=sum_(a,b<R)mu(a)mu(b)floor((R^2-1)/(ab))=2M(R-1)-M(R^2-1), with K_R=max_(0<=u<R)(M(u)-1)^2/(u+1). Neither K_R nor the actual source is replaced by a surrogate.

#### 1. BASELINE / DEPENDENCY RECEIPT

The strongest explicit certified applicable theorem inspected is `RHLean.Analysis.native_mertens_near_uniform_window_error_closed`, in `research/oai_434/VF919WindowErrorClosure.lean`:

```text
b_base=7/8-7/(64*N_pack),
forall eps>0, exists C_eps>=0, forall integers n>=1:
  |M(n)|<=C_eps*n^(b_base+eps).
```

Its type is `MertensGrowthAtMost`, not a no-loss boundary bound. Read the actual source/count definitions: N_pack=ceil_nat(max(1,1/(6*ell)))+2 and N_old=ceil_nat(max(1,1/(3*ell)))+2, with ell=explicitFineLength>0. Thus N_pack<=N_old and 7/(64*N_pack)>1/(48*N_old). This is a recheck of already-known Coordinator CR1, not a new comparison or an identification of the two counts.

Re-fetched the successful [#1119 exact-head run 42552018910](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910), head 77ee815846d6d534c866f0752aa33b84c385610a, and actual job 128949473700 logs. The selected warning-fatal theorem/type and live proof-value audits show five PASS closures of sizes 35358,35375,35736,35737,35753 and terminal axioms only propext, Classical.choice, Quot.sound. Read the audit implementation: it follows OAI/RHLean/private proof values and separately collects terminal axioms transitively. The chain includes original fixed-source construction/counts, total-mass LOW, anchored HIGH/principal, complete comparison, native Hecke/Dirichlet product, zeta-zero boundary and Mertens transfer. Smaller positive errors rebuild valid sources; no zero-error fixed-source limit is used.

Direct recursive-tree comparison found **912 unchanged pre-existing blobs** in the inspected scope RHLean/, research/oai_434/, scripts/lean/total_mass/ and scripts/lean/window_error_closure/ between the tested head and current main. This is reuse of exact-head evidence, not a new current-main compilation or an independent human reproof of every imported analytic lemma. The selected closure excludes sorryAx; dependency-wide absence of placeholders is not claimed.

Hosted pins: Lean 4.34.1, compiler 5045d0056413266e57c625dcd7c365b10e377c52; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; PrimeNumberTheoremAnd c39a751132c88b6e8080b74c74023fd95b3d8be0; openai/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a; anchored source pin 9cbfce5295343bcb411e6d2cb159b59995cd985b. The new RC theorem does not use this baseline as an arithmetic premise.

#1130 is merged, superseding Lean's earlier unmerged report status. Its actual local signed-remainder source was read, and run 42877550772 at head 4aa22782d10b3ad77dc970d6bb610eaab93a228c was verified successful. It proves local RD1 and its adapters, NOT the subsequent complete endpoint. Referee SR accepts Analytic RD1-RD5 on paper; Coordinator MD and Analytic IR remain unformalized paper proposals (MD has Analytic's scoped paper acceptance, not Referee certification). Their proposed new exponents are not silently substituted for b_base. Open/draft PR collection was empty at intake.

### C. Structural Mechanism Investigated

Owner DR1 expresses the uncompleted defect as a Mertens-weighted radical response; DR2 proves reinforcement within some uncompleted physical fibres; DR4 loses a harmonic factor when its bound is summed over descendants. The present question is whether that last loss is real or is caused by taking absolute values before the already-paid divisor cancellation.

The decisive different organization is to complete all (a,k) divisors of each fixed m=ak FIRST. The actual physical integer n=qak and event q are unchanged under a prime toggle. All non-smooth m cancel in that fibre. Unique factorization then makes the surviving nonunit label q equal to rad(n), leaving one radical ancestor per n. The counting proof uses this arithmetic condition; an arbitrary directed graph with the same local degree bound would not supply it.

This is a cross-route application of a finite-wheel restricted-floor theorem to the genuine floor-Li source, not an identification with an ideal Hecke polynomial. It also tests a MU-LIFT-style inverse renewal in F: the new forward bound does not give a subcritical historical-prefix recurrence. No old wheel census, prime near-resonance scan or R=549/5561 computation was rerun without a new hypothesis.

### D. Exact Definitions And Theorems

Let y>=3 and y<X<(y+1)^2 be integers. Li_2(u)=integral_2^u dt/log t, L(n)=floor(Li_2(n)), lambda(q)=L(q)-L(q-1), epsilon(q)=1_Prime(q)-lambda(q), N=floor(X/(y+1)). For T<=y all event sums below are zero. For T>y define

```text
I_y(T)=sum_(y<q<=T)epsilon(q)M(floor(T/q)),
J_y(T)=sum_(y<q<=T)epsilon(q)sum_(a<=T/q)mu(aq),
D_y(T)=sum_(y<q<=T)lambda(q)sum_(a<=T/q)[mu(a)+mu(aq)].
```

These are Owner BR/DR's original coefficients, not new event populations. q need not be prime. All q, a, k are positive integers; all upper products qak<=X are inclusive. q=y is excluded; q=y+1 is included. The same y is retained at every descendant T=floor(X/k). One occurrence is the triple (q,a,k), not merely its product n. Its coefficient is lambda(q)[mu(a)+mu(aq)]. Zero coefficients and repeated physical integers are accounted for before cancellation.

Write rad(1)=1 and rad(n)=product of the distinct primes dividing n. Define

```text
Psi_q(t)=#{1<=m<=t : every prime dividing m divides q},
C_q(X)=sum_(a*k<=floor(X/q))[mu(a)+mu(aq)],
Dhat_y(X)=sum_(k<=N)D_y(floor(X/k)).
```

The unit m=1 is always included in Psi. It is not a new prime occurrence.

**RC1: exact completion.** For every y<q<=X,

```text
C_q(X)=1+mu(q)*Psi_q(floor(X/q)),
Dhat_y(X)=sum_(y<q<=X)lambda(q)*C_q(X)
         =sum_(y<n<=X)h_y(n),
h_y(n)=lambda(n)+1_(rad(n)>y)*mu(rad(n))*lambda(rad(n)). (RC.1)
```

This is also obtained by completing DR.3/DR.4 with the existing unit renewal theorem. The radical coefficients were already exposed by DR1; the new scope is their complete unweighted physical return and the uniform estimate RC3. Do not count the radical reindexing itself twice as a discovery.

**RC2: signs and masks.** For all y<n<=X, -1<=h_y(n)<=2. If n is squarefree, h_y(n)=(1+mu(n))*lambda(n)>=0. If n is not squarefree,

```text
h_y(n)=-1 iff rad(n)>y, mu(rad(n))=-1,
                 lambda(rad(n))=1, lambda(n)=0.        (RC.2)
```

In the stated square range, a negative coefficient must have an odd squarefree COMPOSITE radical with at least three distinct prime factors; in particular n has at least four prime factors counted with multiplicity. A prime radical >y would force n>=rad(n)^2> X. This does not classify the uncompleted DR physical fibre or imply positivity of the full completed sum.

The completed q-packet has sign fixed by its parity: C_q<=0 if mu(q)=-1, C_q>=2 if mu(q)=+1, and C_q=1 if mu(q)=0. Every genuine prime q>y has C_q=0 because q^2>X. Thus the ENTIRE completed odd-parity event sector is nonpositive, without claiming the uncompleted odd sector has that sign.

For ANY real weights w(q,n) with |w(q,n)|<=1, define

```text
Dhat_w=sum_(q>y,a>=1,k>=1,qak<=X)
  lambda(q)[mu(a)+mu(aq)]w(q,qak).
```

Then the exact masked version is

```text
Dhat_w=sum_(q>y,m>=1,qm<=X)lambda(q)w(q,qm)
               [1_(m=1)+mu(q)*1_(rad(m)|q)].           (RC.3)
```

This permits arbitrary bounded event selectors and physical-(q,n) masks, including an arbitrary bounded physical-integer mask. It does NOT permit arbitrary dependence on a and k separately. No actual #915 clipping/ancestry mask is asserted to satisfy the required invariance without its source map.

**RC3: explicit uniform bound.** For every real H>=1,

```text
|Dhat_w| <= L(X)-L(y)
          +3X*(1+log H)/log y +6X/H +N.               (RC.4)
```

The same right side bounds sum_(q>y)lambda(q)|C_q(X)| and sum_(n>y)|h_y(n)|. Setting H=log y>=1 and using L(X)-L(y)<=X/log y+1 gives (RC.A). All constants precede y, X and the mask. The algebra and (RC.4) in fact hold for X>y>=3 without the square restriction; the prime-zero/sign-support statement and the root interpretation use that restriction.

### E. Proofs

**Completed fibre and an explicit involution.** The identity mu(aq)=mu(q)mu(a)1_(gcd(a,q)=1) is valid for all positive integers a,q. If q is squareful both sides vanish; if squarefree it follows from unique factorization.

At fixed m=ak, sum the first term mu(a) over a|m. If m>1 choose the least prime p|m and toggle the presence of p in the squarefree divisor a, changing k=m/a accordingly. This is a fixed-point-free involution of the nonzero signed atoms; it preserves q,m,n and reverses mu(a). Only m=1 survives, with value 1.

For the coprime term, if some prime p|m does not divide q, choose the least such p and apply the same toggle to the squarefree divisors a coprime to q. Coprimality, products and signs are preserved as required. If every prime of m divides q, the only surviving coprime squarefree divisor is a=1. Thus

```text
sum_(a|m)mu(a)=1_(m=1),
sum_(a|m,gcd(a,q)=1)mu(a)=1_(rad(m)|q).
```

This second identity is the already-proved `finiteWheelRoughMoebius_mul_zeta_apply` with P=q.primeFactors; its summatory version is `finiteWheelRestrictedFloorIdentity`. The first is the existing MobiusRenewalTelescope divisor identity. Their exact specialization proves RC1 and, since w(q,n) is constant on each orbit, RC.3. No primality-distribution or random-sign input enters.

For the second surviving channel, mu(q) nonzero means q is squarefree. If rad(m)|q then rad(qm)=q. Conversely n has exactly one such nonzero label, q=rad(n), m=n/q. This proves RC.1 with no duplicated radical ancestor. Each n also has the unit-channel label q=n,m=1. For squarefree n the two labels coincide and their coefficients are ADDED, not treated as two physical events. RC2 follows from lambda in {0,1}; this binary property is established for the present domain by the original floor-Li step theorem. The smaller q=3 finite regression is handled explicitly.

The graph with nonunit edges q->qm, q squarefree and rad(m)|q, is a disjoint family of stars: every child is squareful with unique parent rad(n), and no child can become a nonzero radical parent. Its edges represent surviving signed contributions, not additional copies of the original occurrence. This star description is a corollary of DR1's radical map, not a new independent degree theorem.

**Counting the complete survivor population.** Put

```text
E=L(X)-L(y),
T=sum_(y<q<=X,mu(q)!=0)lambda(q)*Psi_q(floor(X/q)).
```

RC.3 gives |Dhat_w|<=E+T, with the same upper bound for the completed packet and physical coefficient norms. Swap the positive q,m counts, writing d for m:

```text
T=sum_(d<=N) #{q : y<q<=X/d, q squarefree,
                   lambda(q)=1, rad(d)|q}.
```

This is genuine divisibility incidence. For rad(d)<=H, drop the divisibility/squarefree conditions and use deterministic event sparsity:

```text
#events in (y,U] <= (U-y)/log y+1 <= U/log y+1.
```

It follows directly from L(floor U)-L(y) and the integral of 1/log t on [y,U]. For rad(d)>H, drop event/squarefree conditions but retain divisibility, bounding the count by X/(d rad(d)). Therefore

```text
T <= X/log y * sum_(rad(d)<=H)1/d
       +N +X*sum_(rad(d)>H)1/(d rad(d)).                (RC.5)
```

The sums have been safely extended to all positive d. Exact factorization gives, for squarefree r,

```text
sum_(rad(d)=r)1/d = product_(p|r)1/(p-1)=1/phi(r).
```

No distribution of floor-Li events in residue classes has been assumed. To bound the remaining ordinary sums, let

```text
C0=sum_(r>=1)mu(r)^2/(r phi(r))
  =product_p(1+1/(p(p-1))) <= exp(1) <3.
```

All terms are nonnegative; finite Euler products and monotone convergence justify the identity. The inequality uses sum_p1/(p(p-1))<=sum_(n>=2)1/(n(n-1))=1. The elementary expansion n/phi(n)=sum_(d|n)mu(d)^2/phi(d) yields

```text
A(U):=sum_(1<=n<=U)n/phi(n) <= C0*U <3U.
```

Partial summation, including r=1 and the endpoint at H, now gives

```text
sum_(squarefree r<=H)1/phi(r) <= 3*(1+log H),
sum_(squarefree r>H)1/(r phi(r)) <= 6/H.               (RC.6)
```

For the second inequality, drop the nonpositive boundary -A(H)/H^2 and integrate 2A(u)/u^3 over [H,infinity). These formulas hold for real H>=1, including H=1. Combining RC.5-RC.6 proves RC.4 and (RC.A). Since y+1>sqrt X, N<sqrt X; at the square endpoint N=R-1. Also log y is comparable to log X uniformly in the square range, proving the claimed O(X loglog X/log X). The finitely many y=2 cases do not affect that asymptotic statement.

This is an elementary positive counting theorem AFTER an exact signed completion. It is not a sieve claim that survivors are primes, and not an independence or RH assumption.

### F. Structural Consequence And Inverse Test

The loss in DR's completed triangle estimate is avoidable: cancellation across ALL descendants leaves bounded coefficients, and the event/radical incidence gives the sharper full auxiliary bound. Same-n reinforcement in DR2 is not contradicted: DR2 sums (q,a) for an uncompleted T, whereas here k runs through its entire required range before grouping at n=qak.

The analogous inverse is NOT free. Extend D_y(T)=0 for T<=y. Ordinary Mobius inversion of the completion gives

```text
D_y(X)=sum_(k<=N)mu(k)*Dhat_y(floor(X/k)).              (RC.7)
```

This is an application of the same paid convolution algebra, not a new MU-LIFT theorem. If RC.A is inserted term by term, its linear-X cost is multiplied by sum_(k<=N)mu(k)^2/k. That factor cannot be replaced by a uniform constant in this absolute-value argument:

```text
(1/4)*H_N <= sum_(k<=N)mu(k)^2/k <= H_N,
H_N=sum_(k<=N)1/k.                                   (RC.8)
```

Elementary proof: every nonsquarefree integer is divisible by some d^2, d>=2, so the count of squarefree integers up to n is at least n*(1-sum_(d>=2)d^-2)>=n/4; use sum_(d>=2)d^-2<=1/4+integral_2^infinity u^-2 du=3/4. Discrete summation by parts gives the lower harmonic bound exactly. This is a standard squarefree counting consequence applied here, not a literature-priority claim.

Accordingly the forward improvement does not yield the whole-prefix subcritical MU-LIFT recurrence E(B^2)<=G(B)E(B)^r with fixed r<2 and subpower G. It gives no new dependence on E(B), and inverse triangle loses a logarithm. That rules out THIS norm-only transfer, not a genuine signed inversion theorem or MU-LIFT as a route. FINITE-AC/CORR4 remain at JC's earlier complete upper/deep/diagonal obligation. This invocation makes a substantive inverse-transfer attempt rather than labeling an endpoint identity as completed MU-LIFT coverage; a fresh whole-prefix arithmetic supplier is still needed.

### G. Signed Relevance And Five-Stage Return

#### 2. FOUR-WAY SOURCE MAP

| Euler / finite AC | VF / prime discrepancy | NNS / OAI | Square blocks / MU-LIFT | Prime-Mobius coupling |
| --- | --- | --- | --- | --- |
| Restricted-floor Mobius convolution with P=q.primeFactors gives Psi_q, EXACT_IDENTITY on the existing theorem's full integer divisor carrier. Complete finite-wheel physical/virtual compensation remains separate and unchanged. | I_y is the original cofactor-weighted prime-minus-floor-Li innovation. -I_y=J_y+D_y in the square range. Completion produces the actual primitive event discrepancy with its historical anchor, not a fitted reference. | RC.3 is an exact real signed occurrence sum, with arbitrary bounded (q,n)-invariant mask. Ideal Hecke phases, conductor, Gaussian and returned #915 masks have no identified coefficient map here: OPEN_BRIDGE. | RC applies throughout y<X<(y+1)^2 with the SAME y, hence includes every upper-prefix endpoint, but RC.7-RC.8 do not provide a subcritical amplitude recurrence. | mu(aq)=mu(q)mu(a)1_coprime is exact. Actual post-root primes have Psi_q=1. Composite events require the three defect sectors; they are not prime ancestry. |
| Historical Q_R=2M(R-1)-M(X) retains every ordered occurrence and shifted K_R. No equality between Q_R and Dhat is asserted. | F_R-D_R=li(X)-pi(X) is its own certified scalar identity; VF/Li_2 has a fixed offset. Root primes and qak=X stay admitted. | Complete scalar squares below retain both cross orientations; no sum of fibre squares replaces a square of the sum. | CORR4 q^2 daughters omit the JC upper bands; RC does not fill them or spend their negative credit. | At the coefficient level rad(n) is a unique ancestor only AFTER complete divisor cancellation. Original triple multiplicity is not silently erased before that proof. |

All event sums here use unit counting normalization. For nonunit masks, retain RC.3's exact invariant and sup-norm hypotheses. A historical occurrence cannot be spent independently for several descendants.

#### 3. FIRST SIGNED LOSS

| Source step | Discarded interaction and quantitative tax | Paid recovery and unpaid complement |
| --- | --- | --- |
| DR.15 followed by sum_k | Triangle before descendant completion replaces the signed sum by sum_k abs(D_y(X/k)), yielding O_delta(X*(log R)^delta). | Existing restricted-floor/renewal supplies RC1; RC3 replaces that bound by O(X loglog R/log R), without Mertens. This is an auxiliary improvement, not a binding improvement in the complete OAI endpoint. |
| Fixed (q,m) divisor fibre | Removing the opposite-sign partner destroys the exact 0 or 1 survivor coefficient. | Prime-toggle involutions prove RC.3 for invariant masks. The actual q=78,n=780 witness disproves arbitrary descendant-mask transfer. |
| Radical physical grouping | Treating every survivor as positive drops h=-1 terms. | RC2 retains them exactly; R=13,n=156 refutes H_LOCAL. Nonpositivity of the completed odd sector does not mean nonpositivity of every interaction with the positive sectors. |
| RC.5 positive count | Drops event-divisibility correlation and parity after complete local cancellation. | Explicit RC3 uniform bound is proved, but no RH-sized signed global estimate follows from this unsigned final majorant. |
| Inverse completion RC.7 | Absolute values discard the mu(k) signs and charge a harmonic factor. | RC.8 proves that the coefficient budget really grows; no subcritical whole-prefix consumer is obtained. |
| Original prime-side H+Jhat+Dhat | Separate estimates erase their common signed radical term and all mixed squares. | Exact reassembly below restores it; its remaining primitive prime discrepancy is still OPEN at RH scale. |

#### 4. PAID RECOVERY TEST

The recovery theorem actually used is `finiteWheelRestrictedFloorIdentity`, not positivity of a different cofactor source. With P=q.primeFactors its prime-support and coprimality hypotheses hold, and its floor cutoff is literally floor(X/q). `sum_mertensSummatory_div_eq_one` supplies the unit channel and agrees with completing DR1. These are genuine original-coefficient bridges.

#1115 completed reciprocal bands, #1122 virtual compensation, #1124 root admission, #1127 positive proper cofactor fibres and #1128 genuine shared-prime resonance were checked at source/continuity scope. They are not additional bounds on this event kernel. #1130's ideal-slot response and Analytic IR's proposed complete Mellin response also have no coefficientwise transfer to it. RC3 therefore uses no unsupported cross-route premise.

**Complete original consumer.** Let E=L(X)-L(y), Pi=pi(X)-pi(y) and

```text
Srad=sum_(y<q<=X)lambda(q)*mu(q)*Psi_q(floor(X/q)),
Jhat=sum_(k<=N)J_y(floor(X/k)),
Ihat=sum_(k<=N)I_y(floor(X/k)).
```

Exactly, in the stated square range,

```text
Dhat=E+Srad,
Jhat=-Pi-Srad,
Ihat=Pi-E,
Jhat+Dhat=-Ihat=E-Pi.                                (RC.9)
```

The actual prime terms in Jhat use mu(q)=-1 and Psi_q=1; every composite lambda term remains. Srad cancels ONCE between Jhat and Dhat. This explains why paying Dhat alone cannot establish a new prime error bound.

At X=R^2-1,y=R-1 put B(y)=pi(y)-L(y), r(X)=Li_2(X)-L(X), and c_li=li-Li_2, the fixed normalization constant. The original prime-side source is

```text
Z_R=H_R+Jhat+Dhat=li(X)-pi(X),
H_R=c_li+r(X)-B(y),
Z_R^2=H_R^2+Jhat^2+Dhat^2+2H_R*Jhat+2H_R*Dhat+2Jhat*Dhat.
```

If Dhat=P-Nminus with P>=0 the completed even/squareful total and Nminus>=0 the absolute completed odd total, its square is P^2+Nminus^2-2P*Nminus. That signed term is retained; no independent upper/lower estimate pays the other squares automatically.

#### 5. NET RESULT / ADMISSION VERDICT

The new bound is an independent uniform improvement for a COMPLETE AUXILIARY source, not for the complete canonical physical source. At root scale it is O(R^2 loglog R/log R), much larger than R log R. It supplies no b_new<b_base and no relative-to-K_R estimate. Restoring RC.9 recovers the original primitive prime discrepancy, not a smaller independently bounded remainder. **NO_NEW_GLOBAL_GAIN / NO_NEW_ACCEPTED_ROUTE.** No finite-A/C, CORR4, renewing MU-LIFT, canonical VF or RH conclusion is asserted.

### H. Falsification, Novelty And Reproducibility

The frozen primary test used every R=3..40 and held-outs 47,64,97, X=R^2-1,y=R-1. General endpoint checks used every y=3..12 and every integer y<X<(y+1)^2. Genuine floor-Li floors through 9408 were certified by outward integer enclosures; no floating tolerance decides a sign. The unchanged enclosure/sieve helpers are explicitly reused from Owner DR5 at blob 84afec90414b2394a61b51df46c07b6b540e5942, not presented as a new numerical method.

**H_LOCAL is false.** The first failure in the declared root domain is R=13,X=168,n=156, rad(n)=78=2*3*13. The exact floors are L(77)=23,L(78)=24,L(155)=L(156)=40, so lambda(78)=1,lambda(156)=0 and h_y(156)=-1. The original nonzero completed defect atom at this n is q=78,a=2,k=1 with coefficient -1; the unit a=1 contribution has coefficient zero. A separate trial-factor reconstruction and an independent monotone-rectangle integral enclosure with mesh 1/32 verify the witness and all four floors. This is same-author independent-method checking, not independent Referee acceptance.

**Arbitrary descendant-mask transfer is false.** At R=28,X=783,q=78,n=780, m=10, the pairs (a,k)=(1,10),(2,5),(5,2),(10,1) have coefficients 0,-1,0,+1. Their complete sum is zero, agreeing with rad(10) not dividing 78. Keeping only k=1 leaves +1. Thus a mask depending on k cannot be replaced by a (q,n)-constant mask. This is not alleged to be the actual #915 mask; it refutes that generic transfer rule only.

**Boundary test.** At y=2,X=9,q=3, outside the STRICT square domain, the completed prime packet is -1 rather than zero. The q^2=X occurrence is admitted in the sum. No proof silently extends the high-prime-zero statement across that boundary.

H_TOTAL (nonnegativity of the complete unmasked Dhat) had no counterexample on the declared roots. It is **not proved** or promoted to a conjectural supplier. It is different from RC2's proved sign of the completed odd sector and from DR's uncompleted total. No larger undirected sign scan is requested.

| R | Dhat | Odd sector | Even sector | Squareful sector | Jhat | Jhat+Dhat |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 14 | 56 | -1 | 44 | 13 | -52 | 4 |
| 22 | 99 | -11 | 78 | 32 | -94 | 5 |
| 40 | 265 | -53 | 226 | 92 | -258 | 7 |
| 47 | 353 | -78 | 308 | 123 | -344 | 9 |
| 64 | 592 | -135 | 513 | 214 | -583 | 9 |
| 97 | 1183 | -262 | 994 | 451 | -1170 | 13 |

Final checks include 73,928 per-event identities, 61,664 original triple occurrences, 36,824 physical coefficients, 720 general cutoffs, 4,560 exact counting comparisons, 1,823 invariant masked fibres, 256 totient/harmonic checks and 761 inverse completions. The defect-sector square and lifted-plus-defect square were checked with every cross term. The six-term historical-anchor square is retained symbolically in G. These are finite tests; the all-scale result is the separate proof in E.

**Actual failed check and repair.** A proof-led mask test initially proposed q=30,n=420 as a genuine event. Its arithmetic cancellation was correct but lambda(30)=0, so the source-admission assertion FAILED. That candidate was rejected, not reported as a genuine witness. The corrected q=78,n=780 example uses the already independently certified lambda(78)=1. The final corrected program passed. A first external-handoff fetch also used the wrong root-relative path and returned 404; the tree-resolved path research/agent_reports/external/... was retrieved successfully. Neither issue is hidden or upgraded into a mathematical result.

Scoped novelty searches included main code queries `radical floorLi`, `smooth moebius divisors`, `loglog totient`, the original source declarations, today/yesterday reports and prior no-go/context passages. This located `FiniteWheelRestrictedFloor.lean`, preventing a false claim of novelty for RC1. No inspected source/report supplied RC3's particular complete floor-Li rad(d)-split bound. This is not an exhaustive literature-priority claim. The elementary totient and squarefree estimates are standard arguments supplied in full, not new general number-theory theorems.

The only new local files are scratch/proof-report/test artifacts. Actual runtime returned Python 3.12.14; the environment's representative 3.12.13 description was not substituted for the observed version. No local Lean execution or new CI job occurred. Final code and output appear in the reproducibility appendix.

### I. Conceptual Interpretation

The genuine arithmetic restriction is stronger than a degree bound: a complete non-smooth divisor fibre has an explicit sign-reversing involution, while a surviving nonunit fibre has exactly one radical parent. This makes cancellation across descendants exact and leaves a countable arithmetic support with bounded physical coefficients. The quantitative gain comes from retaining both event sparsity and rad(d) divisibility, not from enlarging a wheel or inferring phase independence.

Completion is nevertheless not a free inversion. The same source retains a signed inverse and an independently unpaid full prime-side interaction. That distinction is why the auxiliary logarithmic improvement is useful supporting mathematics but not an endpoint breakthrough.

### J. Competing Structural Hypotheses

| Mechanism | Disposition |
| --- | --- |
| Complete same-event divisor pairing, with fixed y and invariant physical mask | PROVED ON PAPER; uses existing exact suppliers, with RC3's new quantitative application. |
| Every completed physical coefficient nonnegative | REFUTED at R=13,n=156. |
| Any descendant/history mask preserves the pairing | REFUTED generically by q=78,n=780; actual source masks require their own map. |
| Complete odd-parity sector nonpositive | PROVED for the completed source; do not transfer this sign to its uncompleted bracket. |
| Nonnegative total Dhat on all roots | UNRESOLVED; finite success is not an all-scale theorem or endpoint input. |
| Forward auxiliary bound implies a subcritical MU-LIFT recurrence | NOT ESTABLISHED; absolute inverse has the harmonic coefficient cost in RC8. Signed arithmetic inversion remains viable. |
| OAI complete-response proposals supply the actual event estimate | OPEN_BRIDGE; distinct coefficients, masks and consumers. No rerouting or false source equivalence is proposed. |

### K. Specialist Handoffs

**Coordinator:** RC3 improves the entire completed auxiliary defect bound and removes the Mertens-premise dependence, but fails the complete-source new-route admission gate. Preserve b_base and the separate MD/IR paper-review queue. Add the actual source -> descendant-triangle loss -> restricted-floor recovery -> unchanged prime-side consumer edge, not a new RH route.

**Owner Payment:** RC1 completes DR's radical response exactly; RC2 explains why DR2 reinforcement can coexist with completed cancellation. The uniform bound survives any bounded (q,n)-invariant mask, but not arbitrary a/k masks. The next useful source task is an exact occurrence-level test of that invariance for a genuinely proposed weighted carrier, retaining the original anchor and clips. Do not rename the generic q=78 mask as #915.

**Analytic Type II:** RC3 is an elementary deterministic event/divisibility estimate with no Hecke transfer. It removes the harmonic descendant triangle in the stated auxiliary source; the inverse and complete prime return remain separate. A sharper event/radical signed correlation would need a consumer beyond the already exact Srad cancellation. No stronger componentwise norm is made a compulsory test for MD/IR.

**Prime Census:** Independently reproduce R=13,n=156 and the q=78,n=780 mask example from the literal triple carrier, preserving q>y and qak<=X. No larger unchanged sign census is requested. A future test should register an actual non-invariant mask and measure its paired weight differences, not discard its unmatched orbit endpoints.

**Adversarial Referee:** Review RC3's dual count, real H cutoff, rad(d)-partition, totient tail boundary, uniform constants and distinction between complete auxiliary and complete canonical source. Check RC2's squareful/prime-radical restriction and the full RC9 square. Author tests are not acceptance. The first potential failure to seek is an omitted +1 event count or a mask not constant along the involution; both are explicitly charged here.

**Lean Verification:** After independent acceptance and an identified consumer need, reuse `finiteWheelRestrictedFloorIdentity` and `sum_mertensSummatory_div_eq_one`; do not duplicate their scalar identities. RC3's arithmetic counting inequality is not encoded as a desired bound. No endpoint theorem is ready to formalize from this run; no speculative branch or filler PR is requested. A necessary typed adapter, if selected, must state the fixed-y and (q,n)-mask invariance hypotheses explicitly.

These are written asynchronous handoffs in this owned report. No agent was launched, no report of another role was edited, and no execution is inferred from a schedule.

### L. First Independently Missing Theorem

No smaller independently sufficient RH theorem was established. On the unmasked prime-side route, the remaining complete estimate is exactly the anchored Jhat+Dhat quantity in RC9 at O(R log R); renaming it would be target-equivalent. On a weighted source, the first additional prerequisite is the literal original mask map and an independently justified bound for its paired weight-difference remainder. Neither is supplied by the generic mask theorem.

On the distinct MU-LIFT route, a uniform signed inverse/whole-prefix estimate with genuine subcritical dependence on E(B), all B<=X<B^2 and subpower loss remains open. The source-independent RC3 counting bound and its harmonic absolute inverse do not furnish it. The next high-value attempt is a concrete actual-weight invariant or signed inverse restriction, not another wheel expansion or repeat of accepted local falsifiers.

### M. Continuity, Resume Capsule And Publication

TODAY=AVAILABLE for all seven role files; YESTERDAY=CARRY_FORWARD at their actual verified scope. Relevant read handoffs: November 9 Coordinator CD/SA, Owner CF/CT, Analytic ZD, own RF/DG, Census NC, Referee AP and Lean cofactor/repair; November 10 Coordinator MD, Owner HM/BR/DR, Analytic RD/IR, own PC/JC, Census UC, Referee LC/SR and Lean RD. Original claim IDs and differing formal/paper statuses are retained. JC's R=56 upper-band failure and DR's actual q=78 admission remain prior evidence, not fresh discoveries here.

The external inbox has no entry newer than October 18. Its latest full handoff aeb5fa075701c9c0e38ddf02f6c2f571c13fdbc9 was retrieved after resolving its relative path. EXT-20261018-PNT-1..3, the split-prime root correction EXT-20261017-XCOORD-1 and original-denominator EXT-20261014-5 remain cautions at their recorded scope. Historical routing and old PR status in that inbox are not treated as current authority.

```text
RUN=20261110-wheel-3/RC; TRIGGER=2026-11-10 18:06:01 EST.
PLATFORM_RUN_ID=UNAVAILABLE.
ACK=CROSS_ROUTE_SIGNED_RECOVERY_V1.
MAIN=f7947bee036c4dddb0c36fc9f53ab46b4fa90995.
BASELINE=b_base=7/8-7/(64*N_pack), every positive loss.
RC1=SUPPORTING_IDENTITY; RC2-RC4=PAPER_PROOF/SELF_AUDIT.
RC5=FINITE_COMPUTATION; H_LOCAL=REFUTED; H_TOTAL=UNRESOLVED.
NEW_AUXILIARY_BOUND=O(X loglog X/log X), complete fixed-y defect.
NEW_GLOBAL_GAIN=NONE; NEW_ACCEPTED_ROUTE=NONE; VERIFIED_ETA=NONE.
MASK_GATE=constant on (q,n) divisor-toggle fibres; not arbitrary a/k.
NEXT=independent RC3 review; actual-weight map or signed inverse supplier.
RH / CANONICAL_VF / COMPLETE_WHEEL / FINITE_AC / MU_LIFT=OPEN.
NO_LOCAL_LEAN; NO_MAIN_PUSH; NO_PR; NO_MERGE; NO_AGENT_LAUNCH.
```

The early checkpoint was committed as 90ebf4f7c7fad76fc4a914356e092c7138e94234, blob 4e1d208f83787201bc3fdec1e2bad83119e75c57, and re-fetched at that immutable commit with exact equality. Earlier daily content was preserved. Publication of this substantive synthesis is confirmed only by the subsequent immutable readback receipt. Direct git network access returned proxy CONNECT 403; authenticated GitHub source/report access worked. All mathematical/test claims above are scoped independently of publication success.

### Source And Continuity Receipts

Preparation clock: **2026-11-10 23:32:47 UTC / 18:32:47 EST**. The prepublication authority refresh still returned main f7947bee036c4dddb0c36fc9f53ab46b4fa90995. The current report-tree refresh differed from intake only at this role's own checkpoint; all other November 9/10 reports and the external inbox were unchanged. Thus TODAY=AVAILABLE is based on fetched files, not expected schedules.

Retained safeguards: `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`, `high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1`, `chain_ack=CANCELLATION_CHAIN_REUSE_V1`. Current task precedence remains `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`.

**Paid supplier build evidence.** In addition to inspecting their complete proofs, fetched [#1130 hosted native-root job 130044785005](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42877550549/job/130044785005): it checks out refs/remotes/pull/1130/merge, runs `lake build RHLean`, passes the owned-warning gate and elaborated graph check, and reports successful completion of 9786 jobs. This is a synthetic-merge native-root build, NOT a dedicated RC test or a literal-head new theorem audit. The root RHLean.lean explicitly imports both FiniteWheelRestrictedFloor and MobiusRenewalTelescope; their blobs and the root are identical between PR head 4aa22782d10b3ad77dc970d6bb610eaab93a228c and current main. The proof bodies introduce no desired estimate. This receipt supports reuse of existing compiled algebra only. The separate #1119 exact-head dependency/axiom evidence in B supports the baseline; neither log certifies RC3.

Directly inspected #1115's actual `twoABCompleteReciprocalBand_eq_mertensDifference`: for R>=2, 1<=a<=b<R, the COMPLETE t_R(z)-weighted band is M(floor(X/a))-M(floor(X/(b+1))). Its parent coefficient is an actual complementary Mobius increment, not lambda(q) or epsilon(q). The shared renewal law does not equate the coefficients or pay the long-fibre complement. PrimeCombReciprocalBandCancellation is a separate existing file, not a #1115 modification. Also read `squareRootAmplificationZeroLog_eventually_native_envelope` with its explicit hzero and `all_exponents_of_contracting_upgrade` with its explicit upgrade; RC3 supplies neither premise.

Loss-ledger source anchors supplement G's signed inputs, taxes, consumers, masks, recovery and falsifiers:

| G loss entry | Literal location or declaration | Normalization, payment and remaining gate |
| --- | --- | --- |
| Descendant triangle | Owner 2026-11-10 report lines 2412 and 2431, DR.15 and its fixed-y return | Unit-weight q,a,k source. Old O_delta(X log^delta R); RC3 O(X loglog R/log R). Complete auxiliary gain, not a binding global gain. |
| Divisor fibre and mask removal | finiteWheelRoughMoebius_mul_zeta_apply; RC.3 and its proof E | Invariant w(q,n), absolute value at most 1. Cancellation paid by the existing identity; unmatched varying-mask remainder unpaid, q=78 witness retained. |
| Radical positive domination | Owner DR.4 at line 2286; RC.1-RC.2 | Original radical coefficient credited to DR; complete physical sum and signs as stated. H_LOCAL fails at n=156. |
| Positive incidence count | RC.5-RC.6, paper proof E | E+T, fixed constants 3 and 6, +N charged. No prime-in-progression premise; parity correlation discarded and still unpaid at RH scale. |
| Inverse triangle | RC.7-RC.8; MobiusRenewalTelescope's divisor identity | Same y at every descendant; coefficient cost between H_N/4 and H_N. No subcritical E(B) dependence or new finite-AC hypothesis obtained. |
| Full consumer separation | Owner fixed-y return lines 2423-2438; RC.9 and the six-term square G | Actual H_R, Jhat, Dhat and all mixed terms retained. Srad cancellation paid once; remaining O(R log R) primitive discrepancy is OPEN. |

**Immutable main file blobs (all actually retrieved):**

| Main path at f7947bee | Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/AGENTS.md) | c9c89f01b90b526de9f3e8ea92478e36504711b6 |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/CURRENT_PROOF_CONTRACT.md) | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| [docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md) | e922d4ba9362a1ae196af8f6de88f7417f92087c |
| [RHLean.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean.lean) | 94b15ac0b2fb9fa3df0ad0cf3bc2d55704199e6e |
| [lakefile.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/lakefile.lean) | 6ef95e9ebf184d5846fee88a9cdf2db3a38afc97 |
| [research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919WindowErrorClosure.lean) | f629db1b2b65d6ec042ac9432397d4b6316200c6 |
| [research/oai_434/VF919ExplicitSquareBlockPacking.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | 32999039fdeea99c58a070c1c4ee9c140720dd44 |
| [research/oai_434/VF919ExplicitFixedSourceSlotCount.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | 1f17f9401a63d16227db2e2aad020b9f74bc5f4e |
| [research/oai_434/VF919PrincipalSignedRemainder.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919PrincipalSignedRemainder.lean) | a41fee91754d5f6e5606f3f6f3dfe66031d81cbf |
| [RHLean/Analysis/FiniteWheelRestrictedFloor.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean/Analysis/FiniteWheelRestrictedFloor.lean) | 94c4d4420fc58cd87d92780c6265decd2cad7e66 |
| [RHLean/Analysis/MobiusRenewalTelescope.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean/Analysis/MobiusRenewalTelescope.lean) | 223013cd640148a1513ef9e836653aa86cf01cdb |
| [RHLean/Arithmetic/SignedBuchstabRecursion.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean/Arithmetic/SignedBuchstabRecursion.lean) | d9959a0c223d86f8b8f4ca53141bd9aae8665c2e |
| [research/VF_MID_FLOOR_LI_BUCHSTAB_EXACT_BRACKETS_20261022.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_MID_FLOOR_LI_BUCHSTAB_EXACT_BRACKETS_20261022.lean) | 918876c6ad7697388d565d39b15db5b8c3cc9952 |
| [research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean) | 9a9336dad72171b6d572a1c1ae88d1ae8b56b530 |
| [research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean) | 028d9f2bbfa1a8de1fe63e9bd368aca13aae6825 |
| [RHLean/Proof/PrimeCombReciprocalBandCancellation.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean/Proof/PrimeCombReciprocalBandCancellation.lean) | 7c2b4c8a55a1a2fe5bfa0dfe95996e416b0fd19f |
| [research/CompleteSquareRootWheelFractionalBoundary.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/CompleteSquareRootWheelFractionalBoundary.lean) | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| [research/CompleteWheelRootAdmission.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/CompleteWheelRootAdmission.lean) | a412632c1028d7728cd8d87ee6e5ac365377d338 |
| [research/FiniteWheelCofactorPositivity.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/FiniteWheelCofactorPositivity.lean) | f83a3daefc2b9d603014af912ec82b4a7f52cfac |
| [research/DyadicPrimeNearResonance.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/DyadicPrimeNearResonance.lean) | f416e0149b73656e30a7f68a3934a937353d3f8d |
| [RHLean/Proof/AmplificationExponentIteration.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean/Proof/AmplificationExponentIteration.lean) | d78be4509e5dcc35b833c3786258b94fc6e71915 |
| [RHLean/Proof/SquareRootAmplificationZeroLogConsumer.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/RHLean/Proof/SquareRootAmplificationZeroLogConsumer.lean) | b7e6b9170a22a77ac1be56c5d1da2956906e99c6 |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| [research/MERTENS_EXPONENT_ENVELOPES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/MERTENS_EXPONENT_ENVELOPES.lean) | 655b896e8d5a41c9f8fc3c456eae3944a98bfefe |

**Continuity blobs and original receipt times.** These are the prior authors' recorded verification times, not new independent validation of every computation. This execution fetched the blobs and read their relevant findings, failures, formal status and resume capsules. Yesterday's verified results are carried forward only at that scope. Coordinator 90-coordinator-pm.md has the same blob as its 00 mirror on each date.

| Report | Fetched blob | Original claims | Recorded verification / other labelled time | Carried scope and verdict |
| --- | --- | --- | --- | --- |
| 2026-11-09/00-coordinator-am.md | 6fba43130391ad4a606aa3809c20f344d668c709 | CD1-CD5 / SA | 2026-11-09 23:31:59 EST | Paper; fixed critical cutoff and complete-return warning |
| 2026-11-09/10-owner-payment.md | 643e8a004d9d8e0be102b03e2f79bb3b217ae916 | CF1-CF5 / CT | 2026-11-09 21:37:53 UTC | Paper; same-q reinforcement, complete proper cofactor scope |
| 2026-11-09/20-analytic-type-ii.md | d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3 | ZD1-ZD5 | 2026-11-09 17:36:48 EST | Paper; 17/12+eps proper-band cost, not a full endpoint |
| 2026-11-09/30-finite-wheel.md | 0624246d03b19cf76c01e186b7d868a248d896ef | RF1-RF / DG | 2026-11-09 23:33:12 UTC | Paper reflected matching; DG later compiled after repair |
| 2026-11-09/40-prime-census.md | 8c927cc6c323533ba1cfd369404b25aa4f9cef91 | NC / BL3 | 2026-11-10 00:24:24 UTC | Finite/paper collar and center reduction; no unmatched complement |
| 2026-11-09/50-adversarial-referee.md | a5d0192eb31c0efb3767187a7752f1a0d07f8534 | AP / DA E3 | 2026-11-09 20:33:06 EST | Scoped paper reviews; AP adaptive prefix is not a global bound |
| 2026-11-09/60-lean-verification.md | 8b60c6136ac151774be2db0aee8f543f286b53aa | Cofactor / near-resonance repair | 2026-11-10 02:42:54 UTC (readiness update) | Exact-head evidence retained; later human merges supersede old open statuses |
| 2026-11-10/00-coordinator-am.md | 14190fe06982de80c5904b156525e3cda15d8f03 | MD1-MD5 / CR1 | 2026-11-10 15:40:56 EST | MD self-audit, then Analytic scoped acceptance; not Referee or Lean certification |
| 2026-11-10/10-owner-payment.md | 84afec90414b2394a61b51df46c07b6b540e5942 | HM / BR1-BR / DR1-DR5 | 2026-11-10 16:43:55 EST | DR self-audit; q=78 nonexpansion falsifier, DR.4 radical source credited |
| 2026-11-10/20-analytic-type-ii.md | 7ed3a39bec4796f4173b692064af872ea8035048 | RD1-RD5 / IR | 2026-11-10 17:38:54 EST | RD independently accepted on paper; RD1 now compiled; IR not certified |
| 2026-11-10/30-finite-wheel.md | a6a05ab41daeeaf7b3d285833028075cf253d47c | PC / JC1-JC4 | 2026-11-10 15:41:11 UTC | JC R=56 T=5312/105 exceeds 2E12, but diagonal-restored total stays negative |
| 2026-11-10/40-prime-census.md | 8a89d1a899850e39320a96bf35a6f221060fc8a7 | UC | 2026-11-10 08:45:53 UTC | R=29 falsifies the unsaturated projected affine norm claim |
| 2026-11-10/50-adversarial-referee.md | 988a4a74e40a48d8d4c868c03263e66c129a6f1a | LC / SR1-SR5 | 2026-11-10 12:28:52 EST | RD1-RD5 ACCEPTED/PAPER_PROOF; SR extension SELF_AUDIT |
| 2026-11-10/60-lean-verification.md | d2f8fd346b7aaab57f3bd3676ed7b1d8c8abb3f8 | RD local proof / repair | 2026-11-10 13:14:01 EST (trigger; receipt untimed) | Local #1130 exact-head green; old UNMERGED is superseded by live merge |

External inbox blob: 038018145c0fddb2f6306c0712373adf9cd1ea52. Latest referenced full handoff: research/agent_reports/external/2026-10-18/pnt-first-signed-cofactor-seven-agent-handoff.md, blob aeb5fa075701c9c0e38ddf02f6c2f571c13fdbc9. Its historical claim IDs are retained in M; no later external result is invented.

### Reproducibility Appendix

Both exact Python files below are the executed final bytes. Standard library only; observed Python 3.12.14. `python -m py_compile rc_verify.py rc_li_helpers.py` passed; `python rc_verify.py` exited 0 with the JSON below. Helper attribution is preserved. The code does not execute Lean or prove the all-scale bound by finite enumeration.

| Artifact | SHA-256 |
| --- | --- |
| rc_li_helpers.py | 622fab0f55a5bd7e7fe0cd66ee05bf6ce4f3feb7eb80823feb0a80db9193e014 |
| rc_verify.py | 31e775d466b57d0d259346ad69126dfaa065373c7896dc815aeca2f02cfcf326 |
| rc-results.json | 53ce6aad7c4178befa012814cdfb8146c1b6663f0db3b0fd83fff2086b75dc36 |

#### rc_li_helpers.py

```python
# Reused unchanged arithmetic/enclosure helpers from Owner DR5, blob
# 84afec90414b2394a61b51df46c07b6b540e5942; not a new numerical method.
"""Exact floor-Li radical-response tests; research, not Lean certification."""

from functools import lru_cache
from math import gcd, isqrt
import json

S = 10**40


def ceildiv(a, b):
    return -(-a // b)


def log_unit(a, b):
    assert b <= a <= 2*b
    zn, zd = a-b, a+b
    pl, ph = S*zn//zd, ceildiv(S*zn, zd)
    zl, zh = S*zn*zn//(zd*zd), ceildiv(S*zn*zn, zd*zd)
    lo = hi = 0
    terms = 100
    for j in range(terms):
        lo += 2*pl//(2*j+1)
        hi += ceildiv(2*ph, 2*j+1)
        pl, ph = pl*zl//S, ceildiv(ph*zh, S)
    hi += ceildiv(2*ph*S, (2*terms+1)*(S-zh))
    return lo, hi


LOG2 = log_unit(2, 1)


@lru_cache(None)
def log_bounds(a, b=1):
    if a < b:
        lo, hi = log_bounds(b, a)
        return -hi, -lo
    k = 0
    while a >= 2*b:
        b *= 2
        k += 1
    lo, hi = log_unit(a, b)
    return lo+k*LOG2[0], hi+k*LOG2[1]


def ei_bounds(tl, th):
    lo = log_bounds(tl, S)[0]
    hi = log_bounds(th, S)[1]
    pl = ph = S
    terms = 180
    for k in range(1, terms+1):
        pl, ph = pl*tl//(S*k), ceildiv(ph*th, S*k)
        lo += pl//k
        hi += ceildiv(ph, k)
    nxt = ceildiv(ph*th, S*(terms+1))
    assert th < S*(terms+2)
    hi += ceildiv(nxt*S*(terms+2), (terms+1)*(S*(terms+2)-th))
    return lo, hi


EI2 = ei_bounds(*LOG2)


@lru_cache(None)
def li_bounds(n):
    assert n >= 2
    if n == 2:
        return (0, 0)
    lo, hi = ei_bounds(*log_bounds(n))
    return lo-EI2[1], hi-EI2[0]


@lru_cache(None)
def potential(n):
    lo, hi = li_bounds(n)
    assert lo//S == hi//S, (n, lo, hi)
    return lo//S


def arithmetic(N):
    mu, rad, spf = [1]*(N+1), [1]*(N+1), [0]*(N+1)
    mu[0] = 0
    rad[0] = 0
    for p in range(2, N+1):
        if not spf[p]:
            for n in range(p, N+1, p):
                mu[n] = -mu[n]
                rad[n] *= p
                if not spf[n]:
                    spf[n] = p
            for n in range(p*p, N+1, p*p):
                mu[n] = 0
    M, pi, E = [0]*(N+1), [0]*(N+1), [0]*(N+1)
    for n in range(1, N+1):
        M[n] = M[n-1]+mu[n]
        pi[n] = pi[n-1]+int(n >= 2 and spf[n] == n)
        E[n] = max(E[n-1], abs(M[n]))
    return mu, rad, spf, M, pi, E



```

#### rc_verify.py

```python
"""Completed floor-Li defect: exact incidence, signs, and counting checks."""

from collections import Counter
from fractions import Fraction as F
from math import gcd, isqrt
import json
import platform

from rc_li_helpers import S, arithmetic, log_bounds, potential


def trial(n):
    mu, radical, p, left = 1, 1, 2, n
    while p*p <= left:
        if left % p == 0:
            exponent = 0
            radical *= p
            while left % p == 0:
                left //= p
                exponent += 1
            mu = 0 if exponent >= 2 else -mu
        p += 1
    if left > 1:
        radical *= left
        mu = -mu
    return mu, radical


def smooth_count(q, t, rad):
    return sum(q % rad[d] == 0 for d in range(1, t+1))


def rectangle_floor(n):
    # An independent integral enclosure, not the Ei-series evaluation.
    scale = 10**24
    for mesh in (32, 128, 512):
        low = high = 0
        for j in range(2*mesh, n*mesh):
            _, log_right = log_bounds(j+1, mesh)
            log_left, _ = log_bounds(j, mesh)
            low += scale*S // (mesh*log_right)
            high += -((-scale*S) // (mesh*log_left))
        if low//scale == high//scale:
            return low//scale, mesh
    raise AssertionError(("unresolved rectangle floor", n))


def main():
    roots = list(range(3, 41))+[47, 64, 97]
    limit = max(roots)**2-1
    mu, rad, spf, M, pi, _ = arithmetic(limit)
    L = [0, 0]+[potential(n) for n in range(2, limit+1)]
    lam = [0, 0, 0]+[L[n]-L[n-1] for n in range(3, limit+1)]
    assert set(lam) <= {0, 1}
    first_negative_atom = first_negative_total = None
    rows, counts = [], Counter()

    def audit(y, X, physical=False):
        nonlocal first_negative_atom, first_negative_total
        N = X//(y+1)
        complete = odd = even = squareful = jcomplete = icomplete = 0
        abs_packet = smooth_mass = 0
        h_direct = [0]*(X+1)
        defects = [0]*(N+1)
        for q in range(y+1, X+1):
            t = X//q
            psi = smooth_count(q, t, rad)
            cop = sum(mu[a]*(t//a) for a in range(1, t+1) if gcd(a, q) == 1)
            assert cop == psi
            expected = 1+mu[q]*psi
            raw = sum((mu[a]+mu[q*a])*(t//a) for a in range(1, t+1))
            assert raw == expected
            assert (raw <= 0 if mu[q] == -1 else raw >= 1)
            if spf[q] == q:
                assert psi == 1 and raw == 0
            counts["event_row_identities"] += 1
            eps = int(spf[q] == q)-lam[q]
            jcomplete += eps*sum(mu[q*a]*(t//a) for a in range(1, t+1))
            icomplete += eps*sum(mu[a]*(t//a) for a in range(1, t+1))
            if not lam[q]:
                continue
            complete += raw
            abs_packet += abs(raw)
            if mu[q]:
                smooth_mass += psi
            if mu[q] == -1:
                odd += raw
            elif mu[q] == 1:
                even += raw
            else:
                squareful += raw
            for k in range(1, t+1):
                defects[k] += sum(mu[a]+mu[q*a] for a in range(1, t//k+1))
            if physical:
                for a in range(1, t+1):
                    v = mu[a]+mu[q*a]
                    for k in range(1, t//a+1):
                        h_direct[q*a*k] += v
                        counts["triple_occurrences"] += 1
        assert complete == sum(defects) == odd+even+squareful
        h = [0]*(X+1)
        for n in range(y+1, X+1):
            h[n] = lam[n]+(mu[rad[n]]*lam[rad[n]] if rad[n] > y else 0)
            assert -1 <= h[n] <= 2
            if rad[n] == n:
                assert h[n] == (1+mu[n])*lam[n] >= 0
            if h[n] < 0:
                q = rad[n]
                assert q > y and q < n and mu[q] == -1
                assert lam[q] == 1 and lam[n] == 0 and q != spf[q]
                if first_negative_atom is None and physical:
                    first_negative_atom = dict(R=y+1, X=X, n=n, q=q,
                                               h=h[n], floors={str(v): L[v] for v in [q-1,q,n-1,n]})
            if physical:
                assert h_direct[n] == h[n]
                counts["physical_coefficients"] += 1
        assert sum(h) == complete
        reconstructed_uncompleted = 0
        for k in range(1, N+1):
            partial = sum(h[:X//k+1])
            reconstructed_uncompleted += mu[k]*partial
        assert reconstructed_uncompleted == defects[1]
        counts["inverse_completions"] += 1
        if complete < 0 and first_negative_total is None and physical:
            first_negative_total = dict(R=y+1, X=X, complete=complete)
        Srad = sum(mu[rad[n]]*lam[rad[n]] for n in range(1, X+1) if rad[n] > y)
        events, primes = L[X]-L[y], pi[X]-pi[y]
        assert complete == events+Srad
        assert jcomplete == -primes-Srad
        assert jcomplete+complete == -icomplete == events-primes
        assert icomplete == (pi[X]-L[X])-(pi[y]-L[y])
        assert complete**2 == odd**2+even**2+squareful**2+2*odd*even+2*odd*squareful+2*even*squareful
        assert (jcomplete+complete)**2 == jcomplete**2+complete**2+2*jcomplete*complete
        assert abs_packet <= events+smooth_mass
        for H in (1, 2, 3, 5, 8, 16):
            small = sum(L[X//d]-L[y] for d in range(1, N+1) if rad[d] <= H)
            large = sum(X//(d*rad[d]) for d in range(1, N+1) if rad[d] > H)
            assert smooth_mass <= small+large
            if y >= 3:
                logh_low = F(log_bounds(H)[0], S)
                logy_high = F(log_bounds(y)[1], S)
                bound_low = 3*X*(1+logh_low)/logy_high+F(6*X, H)+N
                assert smooth_mass <= bound_low
                counts["counting_bounds"] += 1
        return dict(R=y+1, X=X, completed=complete, odd=odd, even=even,
                    squareful=squareful, abs_completed_packets=abs_packet,
                    descendant_abs=sum(map(abs, defects)), smooth_mass=smooth_mass,
                    events=events, primes=primes, lifted=jcomplete,
                    full_return=events-primes, coefficients=dict(sorted(Counter(h[y+1:]).items())))

    for R in roots:
        rows.append(audit(R-1, R*R-1, True))
    for y in range(3, 13):
        for X in range(y+1, (y+1)**2):
            audit(y, X)
            counts["general_cutoffs"] += 1

    # A different factorization algorithm reconstructs the smallest witness.
    witness = first_negative_atom
    assert witness is not None
    n, y = witness["n"], witness["R"]-1
    direct = 0
    for q in range(y+1, n+1):
        if n % q:
            continue
        m = n//q
        for a in range(1, m+1):
            if m % a == 0:
                direct += lam[q]*(trial(a)[0]+trial(a*q)[0])
    assert direct == witness["h"]
    independent_floors = {}
    for v in map(int, witness["floors"]):
        value, mesh = rectangle_floor(v)
        assert value == L[v]
        independent_floors[v] = dict(value=value, mesh=mesh)

    # Exact radical-partition and totient identities used in the uniform proof.
    phi = list(range(limit+1))
    for p in range(2, limit+1):
        if spf[p] == p:
            for n in range(p, limit+1, p):
                phi[n] -= phi[n]//p
    for n in range(1, 257):
        assert F(n, phi[n]) == sum((F(mu[d]**2, phi[d]) for d in range(1, n+1) if n%d == 0), F(0))
        assert sum(mu[k]**2 for k in range(1,n+1))*4 >= n
        assert sum((F(mu[k]**2,k) for k in range(1,n+1)), F(0))*4 >= sum((F(1,k) for k in range(1,n+1)), F(0))
        counts["totient_identities"] += 1

    # Proof-led extension: masks constant on each (q,n) fibre survive toggles.
    for R in (4, 7, 13, 21, 47):
        y, X = R-1, R*R-1
        direct = reconstructed = 0
        for q in range(y+1, X+1):
            if not lam[q]:
                continue
            for m in range(1, X//q+1):
                weight = ((q+q*m) % 3)-1
                coefficient = sum(mu[a]+mu[q*a] for a in range(1, m+1) if m%a == 0)
                residue = int(m == 1)+mu[q]*int(q % rad[m] == 0)
                assert coefficient == residue
                direct += weight*coefficient
                reconstructed += weight*residue
                counts["masked_fibres"] += 1
        assert direct == reconstructed
    assert lam[78] == 1
    mask_atoms = [(a, 10//a, mu[a]+mu[78*a]) for a in (1,2,5,10)]
    assert sum(v for a,k,v in mask_atoms) == 0
    assert sum(v for a,k,v in mask_atoms if k == 1) == 1
    assert lam[3] == 1
    assert sum((mu[a]+mu[3*a])*(3//a) for a in range(1,4)) == -1

    print(json.dumps(dict(status="PASS_EXACT_SELF_AUDIT", python=platform.python_version(),
                         roots=roots, Li_floor_limit=limit, counts=dict(counts),
                         first_H_LOCAL_failure=witness,
                         first_H_TOTAL_failure=first_negative_total,
                         independent_witness_floors=independent_floors,
                         descendant_mask_counterexample=dict(R=28,q=78,n=780,atoms=mask_atoms,unmasked=0,k1_only=1),
                         strict_wall_test=dict(y=2,X=9,q=3,completed_prime_packet=-1,outside_domain=True),
                         selected_rows=[r for r in rows if r["R"] in (3,6,8,14,16,22,30,40,47,64,97)],
                         no_global_bound_inferred=True), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
```

#### Exact Output

```json
{
  "Li_floor_limit": 9408,
  "counts": {
    "counting_bounds": 4560,
    "event_row_identities": 73928,
    "general_cutoffs": 720,
    "inverse_completions": 761,
    "masked_fibres": 1823,
    "physical_coefficients": 36824,
    "totient_identities": 256,
    "triple_occurrences": 61664
  },
  "descendant_mask_counterexample": {
    "R": 28,
    "atoms": [
      [
        1,
        10,
        0
      ],
      [
        2,
        5,
        -1
      ],
      [
        5,
        2,
        0
      ],
      [
        10,
        1,
        1
      ]
    ],
    "k1_only": 1,
    "n": 780,
    "q": 78,
    "unmasked": 0
  },
  "first_H_LOCAL_failure": {
    "R": 13,
    "X": 168,
    "floors": {
      "155": 40,
      "156": 40,
      "77": 23,
      "78": 24
    },
    "h": -1,
    "n": 156,
    "q": 78
  },
  "first_H_TOTAL_failure": null,
  "independent_witness_floors": {
    "77": {
      "mesh": 32,
      "value": 23
    },
    "78": {
      "mesh": 32,
      "value": 24
    },
    "155": {
      "mesh": 32,
      "value": 40
    },
    "156": {
      "mesh": 32,
      "value": 40
    }
  },
  "no_global_bound_inferred": true,
  "python": "3.12.14",
  "roots": [
    3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    12,
    13,
    14,
    15,
    16,
    17,
    18,
    19,
    20,
    21,
    22,
    23,
    24,
    25,
    26,
    27,
    28,
    29,
    30,
    31,
    32,
    33,
    34,
    35,
    36,
    37,
    38,
    39,
    40,
    47,
    64,
    97
  ],
  "selected_rows": [
    {
      "R": 3,
      "X": 8,
      "abs_completed_packets": 3,
      "coefficients": {
        "0": 4,
        "1": 1,
        "2": 1
      },
      "completed": 3,
      "descendant_abs": 3,
      "even": 2,
      "events": 4,
      "full_return": 1,
      "lifted": -2,
      "odd": 0,
      "primes": 3,
      "smooth_mass": 3,
      "squareful": 1
    },
    {
      "R": 6,
      "X": 35,
      "abs_completed_packets": 18,
      "coefficients": {
        "0": 19,
        "1": 4,
        "2": 7
      },
      "completed": 18,
      "descendant_abs": 18,
      "even": 14,
      "events": 11,
      "full_return": 3,
      "lifted": -15,
      "odd": 0,
      "primes": 8,
      "smooth_mass": 11,
      "squareful": 4
    },
    {
      "R": 8,
      "X": 63,
      "abs_completed_packets": 23,
      "coefficients": {
        "0": 40,
        "1": 9,
        "2": 7
      },
      "completed": 23,
      "descendant_abs": 23,
      "even": 17,
      "events": 17,
      "full_return": 3,
      "lifted": -20,
      "odd": 0,
      "primes": 14,
      "smooth_mass": 16,
      "squareful": 6
    },
    {
      "R": 14,
      "X": 195,
      "abs_completed_packets": 58,
      "coefficients": {
        "-1": 1,
        "0": 142,
        "1": 21,
        "2": 18
      },
      "completed": 56,
      "descendant_abs": 68,
      "even": 44,
      "events": 42,
      "full_return": 4,
      "lifted": -52,
      "odd": -1,
      "primes": 38,
      "smooth_mass": 42,
      "squareful": 13
    },
    {
      "R": 16,
      "X": 255,
      "abs_completed_packets": 71,
      "coefficients": {
        "-1": 3,
        "0": 190,
        "1": 26,
        "2": 21
      },
      "completed": 65,
      "descendant_abs": 65,
      "even": 50,
      "events": 52,
      "full_return": 4,
      "lifted": -61,
      "odd": -3,
      "primes": 48,
      "smooth_mass": 47,
      "squareful": 18
    },
    {
      "R": 22,
      "X": 483,
      "abs_completed_packets": 121,
      "coefficients": {
        "-1": 10,
        "0": 376,
        "1": 43,
        "2": 33
      },
      "completed": 99,
      "descendant_abs": 131,
      "even": 78,
      "events": 89,
      "full_return": 5,
      "lifted": -94,
      "odd": -11,
      "primes": 84,
      "smooth_mass": 84,
      "squareful": 32
    },
    {
      "R": 30,
      "X": 899,
      "abs_completed_packets": 229,
      "coefficients": {
        "-1": 23,
        "0": 711,
        "1": 74,
        "2": 62
      },
      "completed": 175,
      "descendant_abs": 217,
      "even": 148,
      "events": 150,
      "full_return": 6,
      "lifted": -169,
      "odd": -27,
      "primes": 144,
      "smooth_mass": 159,
      "squareful": 54
    },
    {
      "R": 40,
      "X": 1599,
      "abs_completed_packets": 371,
      "coefficients": {
        "-1": 48,
        "0": 1293,
        "1": 125,
        "2": 94
      },
      "completed": 265,
      "descendant_abs": 327,
      "even": 226,
      "events": 246,
      "full_return": 7,
      "lifted": -258,
      "odd": -53,
      "primes": 239,
      "smooth_mass": 263,
      "squareful": 92
    },
    {
      "R": 47,
      "X": 2208,
      "abs_completed_packets": 509,
      "coefficients": {
        "-1": 70,
        "0": 1798,
        "1": 165,
        "2": 129
      },
      "completed": 353,
      "descendant_abs": 447,
      "even": 308,
      "events": 324,
      "full_return": 9,
      "lifted": -344,
      "odd": -78,
      "primes": 315,
      "smooth_mass": 355,
      "squareful": 123
    },
    {
      "R": 64,
      "X": 4095,
      "abs_completed_packets": 862,
      "coefficients": {
        "-1": 119,
        "0": 3413,
        "1": 289,
        "2": 211
      },
      "completed": 592,
      "descendant_abs": 808,
      "even": 513,
      "events": 555,
      "full_return": 9,
      "lifted": -583,
      "odd": -135,
      "primes": 546,
      "smooth_mass": 607,
      "squareful": 214
    },
    {
      "R": 97,
      "X": 9408,
      "abs_completed_packets": 1707,
      "coefficients": {
        "-1": 233,
        "0": 8072,
        "1": 598,
        "2": 409
      },
      "completed": 1183,
      "descendant_abs": 1645,
      "even": 994,
      "events": 1152,
      "full_return": 13,
      "lifted": -1170,
      "odd": -262,
      "primes": 1139,
      "smooth_mass": 1207,
      "squareful": 451
    }
  ],
  "status": "PASS_EXACT_SELF_AUDIT",
  "strict_wall_test": {
    "X": 9,
    "completed_prime_packet": -1,
    "outside_domain": true,
    "q": 3,
    "y": 2
  }
}
```



### Verified Publication Receipt - 20261110-wheel-3/RC

Verified **2026-11-10 23:34:46 UTC / 18:34:46 EST**. Substantive research was published at [commit 4769b57101fbc0821dbc43110e837b05b7442302](https://github.com/OVVO-Financial/RH_Lean/commit/4769b57101fbc0821dbc43110e837b05b7442302), report blob **3fa7b1c60fbba5dc6ada22ae3961d059f3474e9d**. Immutable-commit readback matched all **195962 characters** exactly and preserved the previous **126792-character** report as an unchanged prefix. Commit inspection confirmed exactly this authorized report path, **1177 additions and zero deletions**. A fresh current-branch fetch retained the synthesis before this receipt. Final main recheck remained f7947bee036c4dddb0c36fc9f53ab46b4fa90995.

The new synthesis passed A-M/five-stage coverage, balanced-fence/table checks and byte-for-byte comparison of both embedded executed programs. Its prepublication text SHA-256 is **8625207aa69e57c5d28b38eefa89f76109a471b028614fb6bd296f9ded02deb3**. The final exact test run exited 0 with PASS_EXACT_SELF_AUDIT; no computation is left running.

EXECUTION=COMPLETE; SUBSTANTIVE_PUBLICATION=PUBLISHED_READBACK_VERIFIED. RC1 remains a supporting identity derived from credited existing theorems; RC2-RC4 remain paper/self-audited at their stated scopes, with independent review and formalization pending; RC5 is exact finite evidence. The complete auxiliary improvement does not change the global exponent, b_base, canonical VF or RH status: **NO_NEW_GLOBAL_GAIN / NO_NEW_ACCEPTED_ROUTE / VERIFIED_ETA=NONE**. Only this owned report was modified remotely. No Lean execution, main/source/other-report edit, PR, merge, agent launch, permission or schedule change occurred.

This receipt records the already verified substantive commit. Its own update is re-fetched at its returned immutable commit before user-facing completion; no future commit hash is guessed here.
