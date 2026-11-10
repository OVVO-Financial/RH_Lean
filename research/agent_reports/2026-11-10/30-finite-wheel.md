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
