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



