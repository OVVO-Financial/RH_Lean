# RH | Adversarial Referee - 2026-11-10

## Early Checkpoint - 20261110-referee-1/LC

Status: IN_PROGRESS / PARTIAL. Scheduled invocation: 2026-11-10 04:13:01 EST. Actual runtime timestamps are recorded separately; no extra agent or schedule is launched.
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.

### A. Selected Investigation
Independently review 20261110-census-1/UC1-UC3: exact surviving-composite correction, the claimed smallest R=29 projected-energy counterexample, and the fixed/small-wheel curvature asymptotic. Compare its scope with Owner HM and Wheel PC, whose saturation hypotheses must not be dropped. Original research question: does fitting finitely many logarithmic reciprocal modes repair this transverse obstruction, including independently selected small cutoffs in different genuine prime fibres? No new conclusion is claimed at checkpoint.

### B. Authority
main=7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9.
AGENTS blob=6695522a45d67fd1e80a7cff1f98d909405036e2.
CURRENT_PROOF_CONTRACT blob=95566e37c8eaeb99ee680660df4f9d2e06ea5038.
Finite-wheel directive blob=e505f35522b675c6b5b263eac73618d717346973.
CompleteSquareRootWheelFractionalBoundary.lean blob=ecb482e52deeee5e9b3853592a3ffdace662d2ff.

For X=R^2-1, y=R-1, retain F=sum_(d|P_y)mu(d)fract(X/d), D=X delta(y)+pi(y)-1-li(X), Z=F-D=li(X)-pi(X). The ONE-C uniform |Z|<=C R log R bound remains OPEN. All virtual Euler compensation, physical d=X, cofactor one, root primes and signed mixed terms remain.

### C. Continuity And Scope
Reports snapshot=2667ebfd1e949864e609cbf8333b9b6d50f8353c.
Today Owner HM, Analytic HF, Wheel PC and Census UC are available and retrieved; Coordinator and Lean TODAY=PENDING, YESTERDAY=CARRY_FORWARD. Yesterday's seven roles and identical coordinator mirror blobs are available; relevant final handoffs and own AP/DA evidence are being read. External inbox blob=038018145c0fddb2f6306c0712373adf9cd1ea52 has only historical October entries; no new November external claim.
Only open PR at intake: #1127, non-draft, head 866b3d2121309cdd854f9d64e2a6adbbc708ef9b, not merged. Its sharp-density/positivity claims require actual source and exact-head CI inspection before certification is repeated.
No blanket acceptance of HF, PC or CD is implied by retrieval. Unchanged prior reviews keep their old scopes.

### D-O. Pending Work And Limitations
PENDING: independent rational witness and small-domain minimality checks, classical-source verification, complete proof and quantifier audit, finite-dimensional repair investigation, exact CI/source evidence, final report/readback.
No local Lean execution; no Lean or shared-file edits are authorized. Direct git clone returned CONNECT tunnel failed, response 403; GitHub connector reads work. Only this role's dated report will be written.


## Fixed Reference Spaces Cannot Remove All Prime Curvature
### Final Research Synthesis - 20261110-referee-1/LC

### A. Most Important Mathematical Finding

**The small-wheel transverse obstruction survives every FIXED finite-dimensional continuous reference space, not just the constant/reciprocal fit.** It also survives allowing a different small cutoff in every genuine prime fibre. For a fixed reference space V containing 1 and 1/u, let j>=1 be the first integer for which g_j(u)=(log u)^j/u is not in V. The minimum squared residual on the actual primes q in [R,2R) satisfies

```text
min_(v in V) sum_q |T_q(z_q)-v(q/R)|^2
  ~ kappa_V R^3/(log R)^(2j+3),   kappa_V>0,
```

uniformly over all cutoff assignments with a common small-wheel cap specified in E. Fitted coefficients may depend arbitrarily on R and the data. Consequently no fixed such space makes this residual O(m), or even O(R^2 log^2 R), where m is the number of genuine prime fibres. This is a source-specific infinite-family no-go for these **auxiliary norm bounds**, not a no-go for signed cancellation, moving reference spaces, growing dimension, intermediate/large wheels, or RH.

Independently, Census UC1-UC3 survive review. Its smallest affine-energy failure R=29,z=2, and both optimization witnesses, were reproduced by newly written exact code. The rough-composite vector and its negative mixed term are essential. HM's genuinely saturated theorem is not refuted.

PR #1127's sharper density and R>=47 positivity claims also survive independent mathematical review and have verified exact-head Lean evidence. An additional finite certificate closes the remaining interval: the optimal eventual strict-positivity thresholds are **R>=19 for all integer masks R<=q<2R**, and **R>=18 for prime masks**. Those two lower thresholds are new paper/computational results, NOT Lean-certified.

New LC claims are PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED, with executed finite certificates separately identified. NEW_VERIFIED_GLOBAL_ENDPOINT_GAIN=NONE. The complete centered bound and RH remain OPEN.

### B. Current Authoritative Objective

Scheduled trigger: 2026-11-10 04:13:01 EST, America/New_York, UTC-05:00. RUN_ID_UNAVAILABLE. This is one actual scheduled invocation, not a new launch. Intake main is **7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9**. Acknowledgment: `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`.

For every integer R>=2, preserve

```text
X=R^2-1, y=R-1, P_y=product_(prime p<=y)p,
delta(y)=product_(prime p<=y)(1-1/p),
F_R=sum_(d|P_y)mu(d)fract(X/d),
D_R=X delta(y)+pi(y)-1-li(X),
Z_R=F_R-D_R=li(X)-pi(X).
OPEN: exists ONE C>=0, forall R>=2, |Z_R|<=C R log R.
```

The source is `research/CompleteSquareRootWheelFractionalBoundary.lean`, whose arbitrary-reference identity is `finiteWheel_squareFractional_centered_eq_reference_sub_pi`. It proves an equality, not the bound. Every virtual d>X cancels against its own Euler term BEFORE truncation; d=X stays. Principal-value li is not silently replaced by Li_2. The canonical `riemannHypothesis_of_vfCanonicalSquare` still explicitly takes `ClassicalVonKochRHCriterion` and the unproved arithmetic tracking statement.

The current priority supersedes old frozen-root/HIGH task selection, not their valid results. The proof DAG and atlas were consulted as navigation; their older routing language was not treated as live authority. No new Mertens exponent, finite A, or zero-log premise is asserted. The latest #1126 declarations retain their explicit `upgrade` and `hzero` hypotheses.

### C. Highest-Risk Mechanisms And Selection

Selected review: **20261110-census-1/UC1-UC3**, requested in today's Census handoff. It tests the loss of HM/PC saturation when composite cofactors survive. The original investigation asks whether adding more fitted smooth directions actually repairs the resulting norm failure. A secondary proof-led check concerns the new #1127 sharpening of previously accepted CF2.

Continuity was retrieved at agent-reports snapshot **2667ebfd1e949864e609cbf8333b9b6d50f8353c**. Today Owner HM, Analytic HF, Wheel PC and Census UC were available. Coordinator and Lean: **TODAY=PENDING; YESTERDAY=CARRY_FORWARD**. Yesterday's seven roles were retrieved; the coordinator mirror blobs agree. Relevant late handoffs read were Coordinator CD, Owner CF, Analytic ZD, Wheel RF, Census NC, own AP/DA, and Lean's #1127 synthesis. External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 contains only the historical October entries; no new November external input was found.

Prior CF/AP source reviews remain reusable on unchanged source bytes. They are not rerun as discoveries. HF's proposed 71/52+epsilon high-frequency bound, CD's second-order critical cutoffs, RF/NC matching, and PC's full optimization theorem were read for context but are **NOT blanket-accepted** by this report. They retain their previous review statuses. The present no-go neither uses nor refutes HF's distinct spectral carrier.

### D. Claims Reviewed And Verdicts

| Original claim | Verdict | Exact scope and evidence |
| --- | --- | --- |
| 20261110-census-1/UC1 | ACCEPT | Exact original-row correction by all rough composite cofactors; complete mixed term and sharper saturation criterion. PAPER_PROOF, independently reconstructed. |
| UC2a / UC2b / UC2c | ACCEPT | Exact counterexamples to the specified extensions, with minimality independently checked in the stated R>=8 domain. First failures R=8,10,29 respectively. |
| UC3 | ACCEPT_WITH_SCOPE | PAPER_PROOF for fixed z and the stated growing COMMON cutoff condition. Uniform PNT expansion and empirical projection argument are valid. No unrestricted-z theorem or effective onset follows. |
| UC4 | LIMITED_REPRODUCTION | This run checked 1,074 cutoff states and 12,446 rows, not the author's entire 870,319-row campaign or numerical li table. |
| 20261110-owner-1/HM1 | ACCEPT_WITH_SCOPE | Saturated affine-row identity and transverse <=m/4 bound. UC's composite correction is required outside saturation. Other HM assertions are not collectively promoted. |
| #1127 finiteWheel_density_sq_lower / density_lower / coefficient_sharp | ACCEPT | The coefficient 3 is sharp at z=3; elementary induction is valid. PROVED_IN_LEAN at the inspected unmerged head, independently reviewed here. |
| #1127 cofactor source identities / positivity | ACCEPT_WITH_SCOPE | Complete nonunit source, all integer q in [R,2R), strict positivity for R>=47; no PNT or full discrepancy bound. Exact-head proof evidence verified. |
| Extrapolation: finitely many fixed continuous reference modes restore O(m) residual energy for small wheels | REJECT | New LC2 theorem gives a genuine-prime infinite-family obstruction. This extrapolation is investigated here, not falsely attributed to UC/HM. |
| 20261110-referee-1/LC1-LC4 | SELF_AUDIT | New results below; independently executing reviewer and Lean verification remain pending. |

Actual review method: the source and submitted statements were read, the proofs reconstructed, and a separate exact implementation executed. This is independent execution, not blind review or a claim of statistical independence between models.

### E. Independent Reconstruction And The New Theorem

#### Exact Carrier And Accepted UC1

Fix R>=8, X=R^2-1, h=floor((R-1)/2), and

```text
Q_R={prime q:R<=q<2R}, m=#Q_R,
x_q=X/q, t_q=floor(x_q), r_q=fract(x_q),
H=pi(h), W=delta(h)-delta(R-1),
w_p=delta(p-1)/p,
N_p(t)=#{2<=n<=t: leastPrime(n)=p},
T_q(z)=sum_(prime p<=z or R/2<=p<R)[N_p(t_q)-x_q w_p],
2<=z<=h,
C_q(z)=#{composite n<=t_q: leastPrime(n)>z}.
```

Since t_q>=h and t_q<R, the lower-owner count is
`t_q-1-pi(t_q)+pi(z)-C_q(z)`. The upper-owner count is `pi(t_q)-H`, because an upper owner cannot divide a composite cofactor below R. The reference sums are `1-delta(z)` and W. Therefore

```text
T_q(z)=[delta(z)-W]x_q+pi(z)-H-1-r_q-C_q(z).    (LC.1)
```

All physical cofactor multiplicities, including squares and higher powers, are present. C_q(z)=0 exactly when the square of the first prime greater than z exceeds t_q: any rough composite has at least two such factors, and that prime square is itself a witness otherwise. Geometric z^2>=R is sufficient, not necessary.

Let Phi(t,z) count positive integers <=t surviving all primes <=z, INCLUDING the unit. The alternate exact form is

```text
epsilon_q(z)=t_q-Phi(t_q,z)-x_q[1-delta(z)],
T_q(z)=pi(t_q)-H-W x_q+epsilon_q(z),
|epsilon_q(z)| <= 2^pi(z)+1.                    (LC.2)
```

The last inequality follows from the existing Lean prefix-face discrepancy bound and 0<=x_q-t_q<1. It does not replace the source by random signs or by a prime density. For z=2, epsilon_q=-fract(X/(2q)).

#### LC1. A Finite Uniform Stability Bound, Including Different Cutoffs

Let V be any finite-dimensional real space of continuous functions on [1,2] containing 1 and u^(-1). For each R, let V_R be their vectors sampled at q/R, and use ordinary unweighted Euclidean distance on those genuine primes. Give each q its own integer cutoff 2<=z_q<=z_max<=h, and set B_R=2^pi(z_max)+1. Because H+W x_q is EXACTLY in V_R, (LC.2) and the Lipschitz property of distance to a subspace give

```text
|dist_2((T_q(z_q)),V_R)-dist_2((pi(t_q)),V_R)|
   <= sqrt(m) B_R.                              (LC.3)
```

No common-cutoff assumption is used. This is an all-finite-R statement, with constant one. It is a comparison, not an assertion that either distance is small. It remains valid if B_R is replaced by any independently proved uniform bound for the exact epsilon vector.

#### LC2. Fixed Continuous Finite-Rank Obstruction

**Complete quantifiers.** Fix once and for all a finite-dimensional V as in LC1. Put g_n(u)=(log u)^n/u. Let

```text
j=j(V)=min{n>=1:g_n not in V},
kappa_V=min_(v in V) integral_1^2 |g_j(u)-v(u)|^2 du.
```

The integer j exists: g_0,g_1,... are linearly independent, whereas V is finite-dimensional. Moreover kappa_V>0: a finite-dimensional subspace is closed in L2, and continuous functions equal almost everywhere are equal everywhere.

Let z_max(R) be ANY sequence of integers with 2<=z_max(R)<=h eventually, such that

```text
[2^pi(z_max(R))+1] (log R)^(j+1) / R -> 0.      (SMALL)
```

Then, as R tends to infinity through integers,

```text
sup_(all assignments 2<=z_q<=z_max(R))
 | ((log R)^(2j+3)/R^3)
       min_(v in V) sum_(q in Q_R)|T_q(z_q)-v(q/R)|^2
       - kappa_V | -> 0.                        (LC.4)
```

The minimizer's coefficients are unrestricted and may depend on R, all primes, and every cutoff. Only the function space V is fixed. No unknown RH-scale input is assumed.

**Independent classical input.** Johnston-Yang, Corollary 1.3, gives the unconditional prime-counting error
`|pi(x)-li(x)|<=9.59 x(log x)^0.515 exp(-0.8274 sqrt(log x))` for x>=2. The actual v2 PDF was retrieved and the theorem checked. It implies an error O_A(x/log^A x) for every fixed A. [Primary paper](https://arxiv.org/pdf/2204.01980). The associated fixed-order expansion is also recorded in [NIST DLMF 27.12.4](https://dlmf.nist.gov/27.12#E4). Neither input is RH; no fine interval equidistribution or independence is used. The following deductions are this report's proof, not a result attributed to those references.

**Proof, step 1: finite-order expansion, uniform over actual fibres.** Write L=log R, u=q/R in [1,2], s=log u. Integration by parts for li, followed by the stated PNT error, gives for each fixed j

```text
pi(t_q) = R sum_(n=0..j) P_n(log u)/(u L^(n+1))
          + O_j(R/L^(j+2)),
P_n(s)=n! sum_(r=0..n) s^r/r!.                 (LC.5)
```

The error is uniform in q. Here pi(t_q)=pi(x_q) exactly and x_q=(R/u)(1-R^-2); the relative endpoint shift changes the smooth expansion by an absorbed O(1) amount. No unjustified equality pi(x_q)=pi(R/u) is needed. The polynomial formula follows by expanding the finitely many powers (L-s)^(-a); its leading coefficient is ONE.

By definition of j, every g_n with n<j lies in V. Thus all terms before order L^(-j-1), and all lower-degree terms at that order, lie in V_R. Combining (LC.2), (LC.5), and (SMALL), one can write

```text
(T_q(z_q)) = v_R + [R/L^(j+1)] [ (g_j(q/R)) + e_R ],
v_R in V_R,
sup_(all assignments) ||e_R||_infinity
 <= O_j(1/L)+B_R L^(j+1)/R -> 0.                (LC.6)
```

The original W,H remain in v_R exactly; no reference mass has been discarded.

**Proof, step 2: the moving prime sample does not invalidate projection.** Ordinary PNT yields weak convergence of finite measures

```text
mu_R=(L/R) sum_(q in Q_R) point_mass_(q/R)
   -> Lebesgue measure on [1,2].
```

For a continuous basis f_1,...,f_d of V, every Gram entry integral f_i f_k dmu_R, every cross entry integral f_i g_j dmu_R, and integral g_j^2 dmu_R converges. The limiting Gram matrix is positive definite, since the basis is independent as continuous functions. Its inverse therefore converges, and the empirical minimum squared distance tends to kappa_V. Small perturbations e_R have small empirical L2 norm uniformly in assignments, because mu_R([1,2]) tends to 1. Distance to a subspace is 1-Lipschitz. Applying this to (LC.6) proves (LC.4), with normalization
`[R/L^(j+1)]^2 [R/L]=R^3/L^(2j+3)`.

**Scope of the infinite-family obstruction.** For this fixed V and admissible cap there is one R_0 such that, for EVERY R>=R_0 and EVERY assignment,

```text
minimum residual energy >= (kappa_V/2) R^3/L^(2j+3).
```

Its ratio to m is asymptotic to kappa_V R^2/L^(2j+2), tending to infinity. Its ratio to R^2 L^2 also tends to infinity. Hence the specified uniform norm bounds fail on genuine primes, for every sufficiently large root, not merely on a synthetic vector or sparse subsequence.

V, j, and its constants must be fixed before R. The theorem does NOT license j=j(R), a moving basis such as li(R/u), discontinuous prime-indicator bases, or arbitrary cutoffs outside (SMALL). Continuity is an essential hypothesis for the prime-sampling argument. A norm obstruction does not forbid keeping the residual in a signed joint estimate.

#### LC3. The Logarithmic Hierarchy And A Surviving Exact Repair

For V_k=span{1,g_0,...,g_k}, k>=0 FIXED, linear independence of the exponential and polynomials after writing u=exp(s) shows j(V_k)=k+1. Thus

```text
minimum residual energy ~ kappa_k R^3/L^(2k+5),
kappa_k=dist_L2[1,2](g_(k+1),V_k)^2>0,
B_R L^(k+2)/R -> 0.                            (LC.7)
```

k=0 recovers UC3; LC2 additionally permits arbitrary fixed continuous reference spaces and per-fibre cutoff choices. For k=1, adding precisely the missing log(u)/u mode only changes the loss from L^5 to L^7. Every fixed k still fails both norm budgets above. All fixed finite wheels satisfy (SMALL) for every fixed V. Also, for any FIXED 0<a<1/log 2, the cap `z_max=floor(a log R loglog R)` eventually satisfies (SMALL), by ordinary PNT applied at that explicitly growing argument. No endpoint assertion at a=1/log 2 is made.

As a check on UC3's constant, with ell=log 2,

```text
G=[[1,ell],[ell,1/2]], b=[ell^2/2,(1-ell)/2],
kappa_0=1-ell-ell^2/2-b^T G^(-1)b>0.
```

The proof of positivity is functional independence, not floating cancellation. Ninety-digit Decimal moment calculations give diagnostic values 0.00015704636990096... for k=0 and 0.00000215664952146... for k=1, with positive smaller values through k=4. These are NOT interval certificates or evidence of an asymptotic onset.

A valid replacement retains the ENTIRE smooth profile, not a finite Taylor truncation. Define Delta(t)=pi(t)-li(t), with the same principal-value convention. Then exactly

```text
T_q(z_q)-[li(x_q)-H-W x_q] = Delta(x_q)+epsilon_q(z_q).
```

The removed smooth vector must be restored in the total source. A deterministic bound on the new residual is `sqrt(m)[max_Q |Delta(x_q)|+B_R]`. Classical PNT makes its smooth-error component smaller than every fixed logarithmic truncation asymptotically, but the supplied bound is still not an RH-scale full-return estimate. This identifies what survives, without assuming that the remaining prime error cancels with the complement.

### F. Exact Counterexamples And Sharp Positivity

#### Independent UC2 Certificates

For R=29,z=2, X=840,

```text
Q=(29,31,37,41,43,47,53),
t=(28,27,22,20,19,17,15),
C(2)=(5,5,3,2,2,2,2).
```

The rough composites are 9,15,21,25,27. Projection onto span{1,1/q} may be computed from the simpler exact vector `pi(t_q)-fract(840/(2q))`, since its difference from T is in the removed space. A new rational normal-equation calculation returned

```text
E_perp=13204382152870676585/7298618577576669768
      =7/4+431799642111504491/7298618577576669768 >7/4.
||r_perp||^2=3659936844782588825/7298618577576669768,
||C_perp||^2=1202843690975460748/912327322197083721,
2<r_perp,C_perp>=-9788027464449778/912327322197083721.
```

The three final terms sum exactly to E_perp. The negative mixed term was not omitted. Exhaustive exact checks of every integer cutoff and every R=8..28 found no violation, confirming the claimed smallest root in the stated domain. This is the BEST fitted affine error, so it also defeats imposing a particular reciprocal coefficient outside saturation.

The two distinct optimization failures were also independently recovered: at R=8,q=11 the unrestricted signed minimum is -51/110 at z=2, below the saturated -23/55; at R=10,q=11 the unrestricted absolute minimum is 39/70 at z=2, below 37/35 at z=4. The former has C=0 and exposes the merely sufficient geometric saturation bound; the latter includes the square cofactor 9. These do not refute PC on its actual domain.

#### LC4. Optimal Eventual Positivity Thresholds

Write the #1127 full nonunit source as

```text
S(R,q)=sum_(d|P_(R-1),d!=1)mu(d)fract(X/(qd))
      =delta(R-1) X/q-1-fract(X/q).
```

The source identity needs only integers R>=2 and R<=q<2R, not primality of q. Independently reviewed #1127 proves S>0 for R>=47. Its density induction is elementary: at a prime p>=5 the predecessor p-1 is composite, so the previous invariant at p-2 is multiplied by `(p-1)^2/[p(p-2)]>1`; composite steps only increase 3z delta(z)^2. z=2,3 are exact bases, and z=3 proves sharpness of 3. The inequality `R^2-48(R-1)=(R-47)(R-1)+1>0`, together with X/q>R/2, yields the stated positivity. Thus the paper proof independently confirms the actual Lean scope.

The remaining finite interval was checked twice, by trial-factor/Fraction code and by an independent sieve with integer numerators. If delta(R-1)=A/B (not necessarily reduced) and t=floor(X/q), the exact numerator is

```text
B q S(R,q)=B q(t-1)-(B-A)X.                    (LC.8)
```

Both implementations agree, and the integer verifier proves the finite certificates

```text
forall 19<=R<=46, forall integer R<=q<2R:
  S(R,q)>=16832/629629>0,
forall 18<=R<=46, forall prime R<=q<2R:
  S(R,q)>=16832/629629>0.
```

The common minimum is attained at R=19,q=37. Combined with the analytic R>=47 proof, these are ALL-ROOT strict-positivity theorems starting at 19 and 18 respectively. The thresholds are optimal because

```text
S(18,33)=-691/33033<0,
S(17,29)=-760/29029<0, with 29 prime.
```

These results are PAPER_PROOF_WITH_EXECUTED_FINITE_CERTIFICATE, SELF_AUDIT, NOT_FORMALIZED. They sharpen a proper-source sign statement, not a global upper bound. This secondary finite study was proof-led after inspecting #1127, not part of the original UC preregistration. No claim that #1127 was wrong or asserted an optimal threshold is made.

### G. Original-Carrier And Covariance Audit

The individual owner bridge is

```text
N_p(t_q)-x_q w_p
 =-sum_(e|P_(p-1))mu(e)fract(X/(pqe)).
```

The sign is mu(e), not mu(qe). q is a genuine physical mask, not a new wheel coordinate. Since n<R<=q and nq<=X, no integer can belong to two Q fibres: qq'>=R^2>X. Squareful cofactors are retained; the unit cofactor is excluded from owners and restored exactly once per q. All reference allocations are the original x_q w_p, including virtual divisor compensation. No post-root sign distribution is assumed as an independent saving.

For arbitrary per-fibre cutoffs define E=sum_q T_q(z_q), the complete masked total S_Q=delta(y)sum_q x_q-m-sum_q r_q, the unselected same-mask remainder J=S_Q-E, and G_R=F_R-S_Q-D_R. Then

```text
Z_R=E+J+G_R,
Z_R^2=E^2+J^2+G_R^2+2EJ+2EG_R+2JG_R,
E^2=sum_q T_q^2+2sum_(q<q')T_q T_q'.
```

All these squares were checked for small full-cube roots using arbitrary rational reference 355/113, permitted by the original source theorem. No occurrence is reused within the root; no cross-root donor allocation is claimed.

Crucially, because V contains the constant function, every best-fit residual is orthogonal to constants and its signed sum is ZERO. Large residual energy is therefore perfectly compatible with exact cancellation of that residual's scalar sum. LC2 rules out the specified separate norm bounds, not the original scalar objective or methods preserving its signed interactions. The fitted reference must itself remain in the returned scalar expression.

### H. Quantifier And No-Circularity Audit

UC3 uses a fixed cutoff or the displayed slow-growth condition; it does not assert uniformity over all z<=h. LC2 makes the enlarged quantifiers explicit: fixed continuous V, fixed first missing degree j, then an admissible cap sequence, then all sufficiently large R and ALL per-fibre choices. Its error is uniform in those choices. Fitted coefficients may vary; the basis and dimension may not. No numerical onset, uniform-in-V constant, or growing-j conclusion is claimed.

The source equality to pi-li remains TARGET_EQUIVALENT at the desired full scale. LC1-LC4 do not imply the canonical target, nor is the target assumed in their proofs. They use finite arithmetic and unconditional classical PNT. No reverse implication from RH is needed or asserted; these are independent proper-source theorems. Replacing the final J+G_R obligation after an already-paid E by an unproved target-size bound would merely rename the unresolved target.

The finite threshold improvement uses a genuine universal R>=47 theorem plus an exhausted finite remainder, not extrapolation from samples. Conversely, the 12,446-row checks do not establish LC2's asymptotic; its proof is the expansion and sampling argument in E.

### I. Strongest Surviving Repair

Retain UC1's exact C_q vector outside saturation. For small wheels, retain the complete nonlinear li(x_q) profile or keep the residual in an explicitly signed interaction. Adding any fixed finite collection of continuous modes cannot produce the proposed small separate residual norm; allowing a scale-dependent reference is a mathematically different case, not disproved here.

The finite LC1 distance comparison is a usable stable lemma. It permits any independently established sharper bound for the actual wheel discrepancy epsilon, rather than artificially restricting to the crude face count. Such an improvement must be proved on the genuine carrier. There is no need to assume arbitrary-vector smallness or to rule out joint compensation.

### J. Competing Proof-Strategy Assessment

| Mechanism | Disposition after this review |
| --- | --- |
| Saturated adaptive AP/HM packets | RETAIN at their accepted scopes. Unsaturated counterexamples do not apply; their complete complement is still unpaid. |
| Fixed finite-dimensional small-wheel residual norms | REJECT the O(m) and O(R^2 log^2 R) strengthenings under LC2's hypotheses. The obstruction is now all fixed continuous reference spaces, not only two modes. |
| Moving nonlinear reference / genuine signed compensation | NOT REFUTED. Exact li restoration exposes the true prime discrepancy; an independent quantitative joint estimate is still missing. |
| All-prefix extension of PC's eventual optimum | UNRESOLVED. UC's intermediate growing cutoffs are not covered by LC2 or by saturated PC; no conclusion from held-out signs. |
| Analytic HF and reflected/nearest-centre matching | Separate carriers, unchanged statuses. LC does not supply their missing spectral or unmatched-source return. |
| #1127 complete-fibre positivity | ACCEPT at tested unmerged head; LC4 improves the threshold on paper only. Neither result pays the full centered error. |

No campaign amendment, source edit or human merge is requested. This is a mathematical narrowing of specified auxiliary claims, not a rejection of the whole finite-wheel program.

### K. Original Research And Executed Verification

The principal original result is LC2: arbitrary fixed continuous reference spaces and independently selected small cutoffs, with the first omitted logarithmic mode determining the exact loss. LC3 gives its explicit hierarchy and a source-preserving nonlinear repair. LC4 gives optimal eventual positivity thresholds through a separate finite certificate.

The exact scan was declared in the local checklist before execution, not separately preregistered as a GitHub experiment: R=8..64, all integer 2<=z<=h; held-out roots 67,101,137. Actual total: **1,074 cutoff states and 12,446 exact source rows**. Trial primality/least-factor counting, full counts versus the corrected source formula, rational normal equations, sharper saturation, all mixed terms, and the finite epsilon bound passed. The maximum E_perp/(m/4) within R=8..64 was at R=62,z=2, exactly
`7292435845866738048605923044821818435869437/5323604900557074165224370138966022421127540`.

Full divisor cubes were checked only for R=2..16. They include the empty R=2 wheel; prime roots; at R=8, physical fraction 3/5 plus virtual -6/5 equals -3/5; at R=14, d=X=195 has coefficient -1 and remains in the floor sum. Larger asymptotic claims never require exponential cube enumeration.

The secondary integer-sieve verifier independently checks every q for 2<=R<47, all exact positivity thresholds, and the coefficient-polynomial identity through n=8. Ninety-digit moment displays are diagnostics only. No li numerical table or floating sign certificate is used in any refutation.

Runtime observed: Python **3.12.14**. The environment description's 3.12.13 is not substituted for the observed value. Both scripts completed, and syntax compilation passed. A final rerun after adding the complete E/J/G square checks also passed. The exact executed source is embedded below; final SHA-256 values are

```text
referee_lc_check.py
0e12d95141d267c832dea9651a87403cbc1b64add1e0b3609c07cbef04ff6fe5
referee_lc_certificate.py
e30dd75109f5ffaf2f002096313c6b51efcfdbafbff9589a51b9cb5aec1af6a3
```

No local Lean ran. Direct git clone failed with `CONNECT tunnel failed, response 403`; source and publication used the functioning GitHub connector. No mathematical assertion failed in the executed scripts. No sub-agents, schedules, branches, PRs, issues, shared policies or other reports were changed.

### L. Formalization Guidance And Verified GitHub Evidence

**#1122:** merged, head c53e9cf234500aea2605fd2557e638995f380407, merge 8c9e54ec3dffbe8c0a4136e835814a0c041054a1. Historical targeted [job 128980092032](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42561949462/job/128980092032) actually compiled the complete-wheel source under Lean 4.34.1 and printed standard terminal axioms `[propext, Classical.choice, Quot.sound]`. It checked synthetic merge 1e3c182076a6e1a23ef132c41a78b0f26adab507, not today's main. Fetching the tested source returned the identical current blob ecb482e52deeee5e9b3853592a3ffdace662d2ff. This is reusable historical evidence, not a new current-main build.

**#1125:** merged, head 538aa743a3e0de86b5ec44c9b4f159df3f5bd050, merge e7ffe4e01fd049dfe6f47af86a9984bc0b843576. Final refresh confirms all 12 returned literal-head workflows FAILED; the dedicated near-resonance run 42674337064 has ZERO jobs. Carry forward AP's `MERGED_SOURCE / FORMAL_CERTIFICATION_NOT_VERIFIED` caveat. This invocation found no new successful dedicated proof evidence and does not use #1125 as a certified dependency. A failed run with no jobs is not evidence of a compiler error or a refutation of the paper theorem; merge alone is also not proof certification.

**#1126:** merged, head e8969ad76d4c5694273cefc934316fc528c56648, merge/current main 7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9. The 16 returned PR-triggered workflow records are successful. The actual source types were read: the contracting-upgrade theorem assumes `upgrade`; native envelopes assume `SquareRootAmplificationZeroLogGrowthStatement`. Neither premise is proved by that consumer. This review does not infer arithmetic closure from workflow status.

**#1127:** only open PR at intake, non-draft, **UNMERGED**, head 866b3d2121309cdd854f9d64e2a6adbbc708ef9b. All 12 returned head-associated workflows succeeded. [Dedicated run 42743502306](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42743502306) reports that exact head and success; [job 129590019152](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42743502306/job/129590019152) logs its exact checkout, both new modules compiled, exact public types, guarded standard axioms and live source-dependency audit `closure=828`. The acceptance source contains six guarded axiom lists and the actual proof dependency requirements. It is formal proof of the stated R>=47 theorem, not LC4's thresholds. Runner action-runtime deprecation warnings are distinct from Lean's warning-fatal gate.

Two compact review-ready finite candidates, only if useful to the current consumer: UC1 plus the R=29 rational counterexample; and LC4's finite interval certificates extending the already-proved positivity theorem. LC2 is not a small new Lean task and remains paper-only. Do not create a filler conditional RH wrapper, modify #1122's exact identities, or label a Decimal moment diagnostic kernel-certified. Human review/merge remains mandatory.

### M. Specialist Handoffs

**Proof Architect:** record UC1-UC3 independently accepted at their stated scope. LC2 is a new fixed-continuous-reference norm no-go, not a global obstruction. Keep HF's independent review separate and do not promote the target-equivalent complement as a paid input.

**Owner Payment:** HM1 survives with actual saturation. For a new outside-mask response, retain C_q and either the full smooth curvature or a quantitatively controlled signed compensation. A finite list of fitted modes cannot have the forbidden norm budget in the small-wheel regime.

**Analytic Type II:** independently review LC2's arbitrary-V empirical Gram passage and uniform per-fibre perturbation. The available strong PNT suffices; no zero-boundary improvement is used. This is not a statement about HF's nonconjugated frequency product.

**Finite Wheel:** PC's intermediate/all-prefix extension remains open. (SMALL) cannot be stretched to z near sqrt R. LC1 permits replacement of the face-count error only by an independently justified actual-prefix error theorem.

**Prime Census:** R=29 and all three mixed-energy rationals independently match. Do not repeat the large UC scan. A future experiment should target a precisely proposed intermediate-cutoff theorem or moving-reference consumer, not reconfirm the same failure.

**Lean Verification:** #1127's sharper constant and sufficient threshold receive independent acceptance here. LC4's optimal 19/18 thresholds have full finite numerator certificates but no Lean proof. UC1/R29 is a separate compact falsifier candidate. Keep at most the useful implementation work, not both automatically.

### N. First Independently Missing Mathematical Ingredient

There is still no proved source-preserving quantitative interaction between the selected fibre packet, its unselected same-mask remainder, and the outside-mask/li reference that pays the original complete Z_R. This run does NOT establish a strictly weaker sufficient global lemma. Naming `|E+J+G_R|<=C R log R` merely restates the target.

For the proposed repair, the concrete first unsupported move is a quantitative cancellation/transport theorem for the retained `Delta(x_q)+epsilon_q` vector together with the restored smooth profile and the exact J/G_R source. LC2 explains why replacing that move by a fixed finite-dimensional separate norm is impossible in its domain. It does not prove or assume a suitable signed transport exists.

### O. Resume Capsule And Publication Discipline

```text
RUN=20261110-referee-1/LC; trigger=SCHEDULED; RUN_ID_UNAVAILABLE.
MAIN=7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9.
ACK=FINITE_WHEEL_CENTERED_RH_V1.
PRIOR=20261109-referee-2/AP, source unchanged, no global closure.
ACCEPTED=UC1-UC3 at exact scope; UC2 smallest witnesses reproduced; HM1;
         #1127 density coefficient 3 and R>=47 source positivity.
NEW_SELF_AUDIT=LC1 finite perturbation; LC2 fixed continuous reference no-go;
              LC3 log hierarchy/nonlinear repair; LC4 sharp 19/18 thresholds.
EXACT=R29/z2 projected excess; R18/q33 and R17/q29 negativity.
FORMAL=existing #1122 identity; #1127 exact unmerged head only.
NOT_PROVED=full centered bound; RH; unrestricted-cutoff optimization;
           growing-dimensional repair; new Mertens/zero-boundary exponent.
NEXT=independent LC2 review or a genuinely new source-preserving signed
     response for the nonlinear remainder; do not repeat fixed-rank scans.
```

The early checkpoint was published at commit 7b0dc795583b7bab0f11d4bc92c6a502390c6c04, read back byte-identically at blob 26f5b297c1f9cb32ecca12d5e6c521c0b2dab51f. The final synthesis is complete mathematically, but publication is claimed only after its own immutable readback. Source/continuity ledgers and exact executed programs follow. No local scratch file is treated as a published report.

### Prepublication Freshness - 2026-11-10 04:33 EST

At 2026-11-10 09:33:20 UTC, main remained 7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9; the four upstream November 10 report blobs were unchanged. Coordinator and Lean were still absent today. The own report was still the verified early checkpoint, with no conflicting continuation. #1127 remained open, non-draft and unmerged at 866b3d2121309cdd854f9d64e2a6adbbc708ef9b. No source changed that would invalidate the selected review. Publication and its receipt are the only remaining actions.


### Immutable Source Ledger

All main rows below are pinned to 7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9; PR rows are pinned to #1127 head 866b3d2121309cdd854f9d64e2a6adbbc708ef9b.

| Path | Blob SHA |
| --- | --- |
| AGENTS.md | 6695522a45d67fd1e80a7cff1f98d909405036e2 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_SEVEN_AGENT_FINITE_WHEEL_BOUNDARY_20261108.md | e505f35522b675c6b5b263eac73618d717346973 |
| docs/DYNAMIC_RESEARCH_AGENTS.md | e8d913ff9663bb5163eaf0eddca9f76e0508a7ef |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| RHLean/Proof/AmplificationExponentIteration.lean | d78be4509e5dcc35b833c3786258b94fc6e71915 |
| RHLean/Proof/SquareRootAmplificationZeroLogConsumer.lean | b7e6b9170a22a77ac1be56c5d1da2956906e99c6 |
| docs/PROOF_DEPENDENCY_DAG.md | eee764cefe70035a9f6c7df26ad787fbfd0fb233 |
| docs/COORDINATE_ATLAS.md | cd0419d00a37739fe5a292f5cb738e33213949d5 |
| research/FiniteWheelCofactorPositivity.lean (#1127) | f83a3daefc2b9d603014af912ec82b4a7f52cfac |
| research/FiniteWheelCofactorPositivityAcceptance.lean (#1127) | 94eecdbf8cea32bf80e7e0939e40c951bc72febd |
| .github/workflows/finite-wheel-cofactor-positivity.yml (#1127) | ec1a1898542d36944db9492064865ce43c56123f |

### Two-Day Continuity Ledger

The following immutable report blobs were retrieved at branch snapshot 2667ebfd1e949864e609cbf8333b9b6d50f8353c. Relevant sections are identified in C; retrieval does not mean blanket acceptance or complete rerunning of each author's computations.

| Dated report | Blob SHA |
| --- | --- |
| [2026-11-09/00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-09/00-coordinator-am.md) | 6fba43130391ad4a606aa3809c20f344d668c709 |
| [2026-11-09/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-09/10-owner-payment.md) | 643e8a004d9d8e0be102b03e2f79bb3b217ae916 |
| [2026-11-09/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-09/20-analytic-type-ii.md) | d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3 |
| [2026-11-09/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-09/30-finite-wheel.md) | 0624246d03b19cf76c01e186b7d868a248d896ef |
| [2026-11-09/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-09/40-prime-census.md) | 8c927cc6c323533ba1cfd369404b25aa4f9cef91 |
| [2026-11-09/50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-09/50-adversarial-referee.md) | a5d0192eb31c0efb3767187a7752f1a0d07f8534 |
| [2026-11-09/60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-09/60-lean-verification.md) | 8b60c6136ac151774be2db0aee8f543f286b53aa |
| [2026-11-09/90-coordinator-pm.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-09/90-coordinator-pm.md) | 6fba43130391ad4a606aa3809c20f344d668c709 |
| [2026-11-10/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-10/10-owner-payment.md) | 2bed3da8ed4ddd49c0708378a1c3da5b4883cb54 |
| [2026-11-10/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-10/20-analytic-type-ii.md) | d8337353a94b465f53a0c6a65ad46aac1dc1927e |
| [2026-11-10/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-10/30-finite-wheel.md) | 79ff39e0f79a30f4cf1657b22f96ebe49de4d717 |
| [2026-11-10/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/2667ebfd1e949864e609cbf8333b9b6d50f8353c/research/agent_reports/2026-11-10/40-prime-census.md) | 8a89d1a899850e39320a96bf35a6f221060fc8a7 |

EXTERNAL_HANDOFFS.md: 038018145c0fddb2f6306c0712373adf9cd1ea52. No new external entry.

### Exact Executed Programs

These are scratch reproducers preserved in this owned report, not new repository source files. They require only Python's standard library. Command forms: `python referee_lc_check.py`, `python referee_lc_certificate.py`, and `python -m py_compile referee_lc_check.py referee_lc_certificate.py`. No network or Lean execution is performed.

#### referee_lc_check.py

```python
"""Independent exact checks of the admitted cofactor source; no Lean execution."""

from fractions import Fraction as F
from math import isqrt
import hashlib
import json
import platform


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def least(n):
    return next(d for d in range(2, n + 1) if n % d == 0)


def density(z):
    out = F(1)
    for p in range(2, z + 1):
        if prime(p):
            out *= F(p - 1, p)
    return out


def countpi(n):
    return sum(prime(p) for p in range(2, n + 1))


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), F(0))


def perpendicular(qs, v):
    xs = [F(1, q) for q in qs]
    m, sx, sx2 = len(qs), sum(xs), dot(xs, xs)
    sv, sxv = sum(v), dot(xs, v)
    det = m * sx2 - sx * sx
    assert det > 0
    a, b = (sx2 * sv - sx * sxv) / det, (m * sxv - sx * sv) / det
    out = [y - a - b * x for x, y in zip(xs, v)]
    assert sum(out) == 0 and dot(out, xs) == 0
    return out


def source_rows(R):
    X, h = R * R - 1, (R - 1) // 2
    qs = [q for q in range(R, 2 * R) if prime(q)]
    ps = [p for p in range(2, R) if prime(p)]
    w = {p: density(p - 1) / p for p in ps}
    H, W = countpi(h), density(h) - density(R - 1)
    xs = [F(X, q) for q in qs]
    ts = [X // q for q in qs]
    rs = [x - t for x, t in zip(xs, ts)]
    factors = {n: least(n) for n in range(2, R)}
    rows = {}
    corrections = {}
    for z in range(2, h + 1):
        chosen = [p for p in ps if p <= z or 2 * p >= R]
        total = []
        cs = []
        for x, t, r in zip(xs, ts, rs):
            actual = sum(sum(factors[n] == p for n in range(2, t + 1)) for p in chosen)
            row = actual - x * sum((w[p] for p in chosen), F(0))
            C = sum(not prime(n) and factors[n] > z for n in range(2, t + 1))
            expected = (density(z) - W) * x + countpi(z) - H - 1 - r - C
            assert row == expected
            Phi = sum(all(n % p for p in ps if p <= z) for n in range(1, t + 1))
            epsilon = t - Phi - x * (1 - density(z))
            assert abs(epsilon) <= 2 ** countpi(z) + 1
            assert row == countpi(t) - H - W * x + epsilon
            nextprime = next(p for p in range(z + 1, 2 * R) if prime(p))
            assert (C == 0) == (nextprime * nextprime > t)
            total.append(row)
            cs.append(F(C))
        rows[z], corrections[z] = total, cs
    return qs, xs, ts, rs, rows, corrections


def full_cube(R):
    X, y = R * R - 1, R - 1
    ds = [(1, 1)]
    for p in range(2, y + 1):
        if prime(p):
            ds += [(d * p, -sgn) for d, sgn in list(ds)]
    frac = sum((sgn * (F(X, d) - X // d) for d, sgn in ds), F(0))
    phys = sum((sgn * (F(X, d) - X // d) for d, sgn in ds if d <= X), F(0))
    virtual = sum((sgn * F(X, d) for d, sgn in ds if d > X), F(0))
    floor = sum(sgn * (X // d) for d, sgn in ds)
    assert frac == phys + virtual
    assert frac - X * density(y) == -floor
    assert floor == 1 + countpi(X) - countpi(y)
    L = F(355, 113)
    D = X * density(y) + countpi(y) - 1 - L
    assert frac - D == L - countpi(X)
    if R >= 8:
        qs, xs, ts, rs, rows, _ = source_rows(R)
        S = density(y) * sum(xs) - len(qs) - sum(rs)
        G = frac - S - D
        for z in [2, (R - 1) // 2]:
            E = sum(rows[z])
            J = S - E
            assert E + J + G == frac - D
            assert (frac - D) ** 2 == E * E + J * J + G * G + 2 * E * J + 2 * E * G + 2 * J * G
            assert E * E == dot(rows[z], rows[z]) + 2 * sum(rows[z][i] * rows[z][j] for i in range(len(qs)) for j in range(i + 1, len(qs)))
    return {"R": R, "F": str(frac), "physical": str(phys), "virtual": str(virtual), "d_eq_X": [(d, s) for d, s in ds if d == X]}


def main():
    first_energy = first_signed = first_abs = None
    largest = (F(0), None, None)
    roots = list(range(8, 65))
    heldout = [67, 101, 137]
    states = rowcount = 0
    witness = {}
    for R in roots + heldout:
        qs, xs, ts, rs, rows, cs = source_rows(R)
        m = len(qs)
        sat = [z for z in rows if z * z >= R]
        for i, q in enumerate(qs):
            signed_all = min((rows[z][i], z) for z in rows)
            signed_sat = min((rows[z][i], z) for z in sat)
            abs_all = min((abs(rows[z][i]), z) for z in rows)
            abs_sat = min((abs(rows[z][i]), z) for z in sat)
            if R in roots and first_signed is None and signed_all[0] < signed_sat[0]:
                first_signed = (R, q, str(signed_all[0]), signed_all[1], str(signed_sat[0]), signed_sat[1])
            if R in roots and first_abs is None and abs_all[0] < abs_sat[0]:
                first_abs = (R, q, str(abs_all[0]), abs_all[1], str(abs_sat[0]), abs_sat[1])
        for z, v in rows.items():
            states += 1
            rowcount += m
            perp = perpendicular(qs, v)
            energy = dot(perp, perp)
            if R in roots and energy > F(m, 4):
                if first_energy is None:
                    first_energy = (R, z, str(energy), str(energy - F(m, 4)))
                if energy / F(m, 4) > largest[0]:
                    largest = energy / F(m, 4), R, z
            if z in sat:
                assert energy <= F(m, 4)
            rp = perpendicular(qs, rs)
            cp = perpendicular(qs, cs[z])
            assert all(a == -b - c for a, b, c in zip(perp, rp, cp))
            assert energy == dot(rp, rp) + dot(cp, cp) + 2 * dot(rp, cp)
            if R == 29 and z == 2:
                simple = [F(countpi(t)) - (F(R * R - 1, 2 * q) - ((R * R - 1) // (2 * q))) for q, t in zip(qs, ts)]
                assert perpendicular(qs, simple) == perp
                witness = {"Q": qs, "t": ts, "C": [str(c) for c in cs[z]], "E": str(energy), "rounding": str(dot(rp, rp)), "composites": str(dot(cp, cp)), "mixed": str(2 * dot(rp, cp))}
    # General sharp density invariant and the finite, previously untested region.
    fail_integer = []
    fail_prime = []
    for z in range(2, 200):
        assert 3 * z * density(z) ** 2 >= 1
    assert 3 * 3 * density(3) ** 2 == 1
    for R in range(2, 47):
        for q in range(R, 2 * R):
            x = F(R * R - 1, q)
            s = density(R - 1) * x - 1 - (x - x.numerator // x.denominator)
            if s <= 0:
                fail_integer.append((R, q, str(s)))
                if prime(q):
                    fail_prime.append((R, q, str(s)))
    result = {"runtime": platform.python_version(), "roots": [8, 64], "heldout": heldout, "states": states, "rows": rowcount, "first_energy": first_energy, "first_signed": first_signed, "first_abs": first_abs, "max_ratio_R8_64": [str(largest[0]), largest[1], largest[2]], "R29": witness, "cubes": [full_cube(R) for R in range(2, 17)], "last_nonpositive_integer_R_lt_47": fail_integer[-1], "last_nonpositive_prime_R_lt_47": fail_prime[-1]}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
```

#### referee_lc_certificate.py

```python
"""Second implementation: integer positivity certificates and moment diagnostics."""

from decimal import Decimal, localcontext
from fractions import Fraction
from math import comb, factorial, isqrt
import json


def sieve(n):
    flags = [True] * (n + 1)
    flags[0] = flags[1] = False
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            for d in range(p * p, n + 1, p):
                flags[d] = False
    return flags


def solve(A, b):
    rows = [list(a) + [v] for a, v in zip(A, b)]
    n = len(b)
    for j in range(n):
        p = max(range(j, n), key=lambda i: abs(rows[i][j]))
        rows[j], rows[p] = rows[p], rows[j]
        divisor = rows[j][j]
        rows[j] = [v / divisor for v in rows[j]]
        for i in range(n):
            if i != j:
                c = rows[i][j]
                rows[i] = [v - c * w for v, w in zip(rows[i], rows[j])]
    return [row[-1] for row in rows]


flags = sieve(100)
mins_integer, mins_prime = [], []
last_integer = last_prime = None
for R in range(2, 47):
    A = B = 1
    for p in range(2, R):
        if flags[p]:
            A *= p - 1
            B *= p
    X = R * R - 1
    allq, primeq = [], []
    for q in range(R, 2 * R):
        t = X // q
        # The exact fibre value is N/(B*q), without any rational rounding.
        N = B * q * (t - 1) - (B - A) * X
        value = Fraction(N, B * q)
        allq.append((value, q))
        if flags[q]:
            primeq.append((value, q))
        if N <= 0:
            last_integer = [R, q, str(value)]
            if flags[q]:
                last_prime = [R, q, str(value)]
    vi, qi = min(allq)
    vp, qp = min(primeq)
    if R >= 19:
        assert vi > 0
        mins_integer.append([R, qi, str(vi)])
    if R >= 18:
        assert vp > 0
        mins_prime.append([R, qp, str(vp)])
assert last_integer == [18, 33, "-691/33033"]
assert last_prime == [17, 29, "-760/29029"]
assert min(Fraction(row[2]) for row in mins_integer) == Fraction(16832, 629629)
assert min(Fraction(row[2]) for row in mins_prime) == Fraction(16832, 629629)

# Verify the coefficient-polynomial identity without a numerical asymptotic fit.
for j in range(9):
    for power in range(j + 1):
        assert factorial(j - power) * comb(j, j - power) == factorial(j) // factorial(power)

diagnostic = []
with localcontext() as ctx:
    ctx.prec = 90
    ell = Decimal(2).ln()

    def J(n):
        return Decimal(factorial(n)) * (1 - sum((ell ** j / Decimal(factorial(j)) for j in range(n + 1)), Decimal(0)) / 2)

    for k in range(5):
        # Basis: 1, 1/u, log(u)/u, ..., log(u)^k/u, in Lebesgue L2[1,2].
        dim = k + 2
        G = [[Decimal(0)] * dim for _ in range(dim)]
        G[0][0] = Decimal(1)
        for i in range(k + 1):
            G[0][i + 1] = G[i + 1][0] = ell ** (i + 1) / (i + 1)
            for j in range(k + 1):
                G[i + 1][j + 1] = J(i + j)
        b = [ell ** (k + 2) / (k + 2)] + [J(k + 1 + i) for i in range(k + 1)]
        coeff = solve(G, b)
        kap = J(2 * k + 2) - sum((v * c for v, c in zip(b, coeff)), Decimal(0))
        diagnostic.append({"k": k, "kappa_diagnostic": str(kap), "energy_log_power": 2 * k + 5})

print(json.dumps({"last_nonpositive_allq": last_integer, "last_nonpositive_primeq": last_prime, "positive_allq_minima_R19_to_46": mins_integer, "positive_primeq_minima_R18_to_46": mins_prime, "polynomial_orders_checked": 9, "moment_diagnostics_not_certified": diagnostic}, indent=2))
```
