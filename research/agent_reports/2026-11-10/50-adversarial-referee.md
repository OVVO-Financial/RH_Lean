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


### Verified Publication Receipt - 2026-11-10 04:35:30 EST

Execution status: COMPLETE / PUBLISHED. Final synthesis and both exact executed programs were committed at **aac2ecf05e10ac304057706e9079a7ec7a07de9b**, then fetched at that immutable commit and compared byte-for-byte successfully. Verified report blob: **16c64c8655a9ff26587d45e85de058db6b748f01**; 52,350 characters. The original early-checkpoint prefix remains unchanged. This receipt is appended only after that successful readback.

Mathematical status remains separate: UC1-UC3 and the specified #1127 statements have independent acceptance at their stated scopes; LC1-LC4 remain this invocation's SELF_AUDIT paper results with the finite certificates explicitly identified. No new LC theorem is Lean-certified. #1127 is unmerged; #1125's missing proof-head certification caveat is retained. Complete finite-wheel bound and RH remain OPEN. No unrelated repository or agent configuration was changed.


## Scheduled Cross-Route Review Checkpoint - 20261110-referee-2/SR

Trigger: scheduled 2026-11-10 12:03:01 EST, America/New_York. Platform run ID unavailable. This is a continuation of today's owned report, not a replacement of LC or its publication receipts. Execution: IN_PROGRESS / PARTIAL. No new result or final verdict is asserted at checkpoint.

`cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`; retain `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`, `high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1`, and `chain_ack=CANCELLATION_CHAIN_REUSE_V1` as source safeguards. Live main is 655f897e274a8ba8a2fed80ecc1fc75a0d849174; AGENTS blob c9c89f01b90b526de9f3e8ea92478e36504711b6; proof contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038; cross-route directive e922d4ba9362a1ae196af8f6de88f7417f92087c. The newer main AGENTS task priority controls the older finite-wheel priority text in CURRENT_PROOF_CONTRACT, without changing the canonical OPEN VF/RH objective.

Both November 9 and November 10 reports were retrieved at agent-reports commit 387018549541511992183afd4f09955c1e421231. TODAY=AVAILABLE for every role; YESTERDAY=CARRY_FORWARD. The latest Analytic RD and Wheel JC continuations are present. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no entry newer than October 18; its carrier/denominator safeguards are retained. No open or draft PR existed at intake. Merge and exact-head CI evidence is being independently checked; report descriptions are not substituted for those checks.

Highest-risk selected claim: 20261110-analytic-2/RD1-RD5, a proposed complete global exponent improvement by retaining a signed principal response. Review order: actual source algebra and normalizer; same-signal Mellin delay and uniform absorption; full anchored six-component return and all parameter/height gates; beta/zeta/Mertens consumer and positive-loss spend. Coordinator CR1/CR2 are relevant baseline/hypothesis checks. UB, BR, JC and earlier HF remain separately scoped and are not blanket-accepted. Prior LC/AP judgments are carried forward where dependencies are unchanged.

Registered independent investigation: determine whether the signed response inversion is genuinely uniform for outer-scale moving pools, and derive the strongest corrected invertibility statement and sharp failure boundary. Use exact rational/complex arithmetic for the local principal identities and finite products; no finite test will certify a global exponent. If RD's complete return has an unverified gate, identify its first exact declaration/hypothesis rather than inventing a counterexample to a different carrier.

Pending: baseline dependency/CI receipt, source/loss/recovery/consumer map, independent reconstruction and adversarial tests, A-O final synthesis, publication verification. Only this owned report may be changed remotely. No Lean execution, source edit, feature branch, PR, other-agent launch, merge, workflow or schedule mutation is authorized or performed. Direct git transport returned HTTP 403; connector reads work. No unexecuted work is claimed.


## Signed Response Survives Independent Review; A Stronger Full-Reserve Paper Boundary

### Final Research Synthesis - 20261110-referee-2/SR

Same actual scheduled invocation as the checkpoint: 2026-11-10 12:03:01 EST, America/New_York. Platform RUN_ID_UNAVAILABLE. Earlier LC results, corrections and publication receipts are preserved. The new governing acknowledgment is `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. This continuation does not claim another agent was launched.

### A. Most Important Mathematical Finding

**ACCEPT 20261110-analytic-2/RD1-RD5 as PAPER_PROOF at the submitted scope.** The original principal slot really contains the signed correction `-eta(p) Q_p^(-s)`. After the original finite-product normalizer this has a PLUS sign, and its Mellin return is a smaller-scale value of the SAME fixed corrected Hecke signal. The compact-supremum inversion is noncircular. Reassembling the raw anchored tails, principal remainder, supported floor and supported nonfloor rows pays the complete return. The old theorem requiring actual beta>=7/8 is not being applied below its domain.

The accepted paper endpoint is

```text
b_RD = 7/8 - 1/(8 N_pack),
forall eps>0 exists C_eps>=0 forall n>=1:
  |M(n)| <= C_eps n^(b_RD+eps).
```

**Original investigation gives a stronger paper candidate without a stronger local estimate:** spend the already-proved `11m/8` remainder reserve instead of only `m`, where `m=actualSlotMinimum D`. The complete return below works for physical tilt `h=11m/8-e`, with a fresh source at every positive `e<=min(e_old,m/64)`. Closing only the numerical beta inequality gives

```text
SR3: beta <= 7/8 - (11/8)m,
SR4: b_SR = 7/8 - 11/(64 N_pack),
     forall eps>0 exists C_eps>=0 forall n>=1:
       |M(n)| <= C_eps n^(b_SR+eps).
```

SR3-SR4 are **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. They are not independently accepted by their own author. The certified baseline remains `b_base=7/8-7/(64 N_pack)`. The original RD endpoint is now independently paper-accepted, not Lean-certified. `VERIFIED_ETA=NONE`; no new certified route, RH result, finite A/C, or complete wheel bound is announced. This separation is material, not merely a publication label.

### B. Current Authoritative Objective And Baseline / Dependency Receipt

Authority: main `655f897e274a8ba8a2fed80ecc1fc75a0d849174`; main tree `a4889160114bebe7f7e3bf240122db7dffe44c2f`. AGENTS blob `c9c89f01b90b526de9f3e8ea92478e36504711b6`; CURRENT_PROOF_CONTRACT blob `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; cross-route directive blob `e922d4ba9362a1ae196af8f6de88f7417f92087c`. The newer AGENTS directive supersedes the older contract's task-priority sentence, not any theorem or integrity safeguard. Retain finite-wheel, complete-HIGH and cancellation-chain acknowledgments as source safeguards.

Canonical arithmetic objective remains OPEN:

```text
exists C>=0 forall integer R>=2:
  |pi(R^2)-VF_can(R^2)| <= C R log R.
```

The complete wheel specialization uses `X=R^2-1`, `y=R-1`, all divisors of the primorial through y, and `F_R-D_R=li(X)-pi(X)`. The source theorem is actually stronger as an IDENTITY: its reference `L` is an arbitrary real number. Substituting `L=li(X)` supplies no estimate. The actual-prime VF-to-RH theorem still takes BOTH the arithmetic bound and `ClassicalVonKochRHCriterion`. The internal Mertens-energy-to-RH route has a different, still-unpaid arithmetic premise.

The strongest explicit formal Mertens boundary reviewed here is [native_mertens_near_uniform_window_error_closed](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919WindowErrorClosure.lean#L128). Its type is `MertensGrowthAtMost b_base`, hence EVERY positive exponent loss is retained. It has no ordinary arithmetic hypothesis. The exact definition in `MERTENS_EXPONENT_ENVELOPES.lean:29` is `forall eps>0, MertensPowerBound(b_base+eps)`, not a no-loss boundary power.

Coordinator CR1 is independently accepted: the actual definitions are

```text
L=explicitFineLength>0,
N_pack=ceil_nat(max(1,1/(6L)))+2,
N_old =ceil_nat(max(1,1/(3L)))+2.
```

Thus `N_pack<=N_old` by monotonicity, and `7/(64N_pack)>1/(48N_old)`. The same comparison beats #1116's `5/(96N_old)`. No identification of the two counts, optimization of their size, or new exponent is hidden in this baseline comparison.

The inspected dependency chain is: actual fixed fine source and certified moments -> total-mass LOW -> generated, additive 7/8-anchored raw HIGH/principal leaves -> complete signal comparison -> actual Hecke beta -> modulus-one Dirichlet/Hecke product -> actual zeta rightmost-zero coordinate -> genuine Mertens converse. The native moment supplier explicitly requires `51/100<=beta<=7/8+Delta`; its use below is confined to a contradiction range where those conditions follow. The marked-NNS interface's `PositiveFineSourceInput` is not counted as an independently proved premise for arbitrary profiles.

PR #1119 is merged, head `77ee815846d6d534c866f0752aa33b84c385610a`. [Run 42552018910, job 128949473700](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700) was independently retrieved: completed/success, pull_request event, attempt 1, exact head. All 14 attached check-runs succeeded. The job prints the exact five endpoint types, standard terminal axioms only, and live dependency traversals of sizes 35358, 35375, 35736, 35737, 35753. Its audit traverses proof values in OAI/RHLean/private namespaces; `Lean.collectAxioms` separately checks transitive terminal axioms. It is not a human rereading of every imported analytic proof.

Eighty source/audit paths under `research/oai_434`, the window-error and anchored audit directories, and the dedicated workflow were compared against that tested tree; all are unchanged on main. Pins read from the proof job and source: Lean 4.34.1, compiler `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; PrimeNumberTheoremAnd `c39a751132c88b6e8080b74c74023fd95b3d8be0`; openai/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. Anchored generation reads RH_Lean pin `9cbfce5295343bcb411e6d2cb159b59995cd985b`. Its added declarations use the separately proved beta<=7/8; they do not redefine beta.

**Warning-scope correction:** the log does contain dependency-build warnings that `PrimeNumberTheoremAnd/Wiener.lean:325,344` uses `sorry`, as well as package worktree warnings. Do not describe the entire log or imported repository as warning/placeholder-free. The selected endpoint's subsequent warning-fatal compilation and transitive axiom audit pass with only `propext`, `Classical.choice`, `Quot.sound`, excluding those placeholder axioms from the audited theorem. This is a scoped certification receipt, not a claim those unrelated declarations are proved. No local Lean execution occurred.

### C. Highest-Risk Mechanism And Selection

RD is selected ahead of UB/HF/BR/JC because it claims a complete new global exponent, not a proper-source restriction. The essential risk is not the elementary finite-product identity: it is whether the SAME signal, masks, weights, principal normalizer, moving row labels and height budgets survive the complete return. A large formal dependency chain cannot substitute for checking the newly proposed assembly.

The relevant original loss is upstream `principal_slot_error`: an absolute bound of order `Q^(-7/8)` hides a structured signed leading correction. Restoring only its sign without its exact dilation would be insufficient. The recovery uses already-proved residue and signal identities plus a genuinely new local estimate and an elementary inversion argument.

### D. Claims Reviewed And Verdicts

| Claim | Independent verdict | Evidence / exact limitation |
| --- | --- | --- |
| 20261110-analytic-2/RD1 | ACCEPT | PAPER_PROOF; literal normalized principal slot, Q>=480, norm(A)<=1, norm(eta)=1, Re(s)>=7/8; constant 12 and all denominator conditions verified. |
| RD2 | ACCEPT | PAPER_PROOF; fixed finite slot family, nonnegative normalized weights; PLUS linear term and every degree>=2 product retained. No uniformity in arbitrary growing N. |
| RD3 | ACCEPT | PAPER_PROOF; exact same-mask Mellin dilation with outer weights frozen; locally bounded signal, theta>0, fixed N,m>0, and eventually 1<=Z/Q<=Z. |
| RD4 | ACCEPT | PAPER_PROOF; six complete bills verified from raw anchored leaves, with exact heightCost=2*tau<=t and independently requested floor saving m. No reuse of the incompatible bundled HIGH window. |
| RD5 | ACCEPT | PAPER_PROOF; actual beta and finite-deletion argument, then existing zeta/Mertens adapter; all positive final losses retained. NOT_PROVED_IN_LEAN. |
| 20261110-coordinator-0710-EST/CR1 | ACCEPT | Actual N_pack/N_old comparison above; supports baseline selection only. |
| CR2 | ACCEPT | Old actual-beta HIGH cannot be applied below beta>=7/8. RD avoids, rather than falsifies, this objection. |
| 20261110-referee-2/SR1-SR4 | SELF_AUDIT | New results below, independent review pending. SR1 is an abstract inversion theorem, SR2 local sharpness, SR3-SR4 a complete paper extension. |
| SR5 | FINITE_COMPUTATION | Newly executed exact checks; not an infinite proof or Lean certificate. |

UB1-UB3, BR, JC, HF and ZD are read as relevant continuity, but are NOT collectively reviewed or accepted in this continuation. Earlier independent AP/DA/LC verdicts remain at their original scopes where their source bytes are unchanged. This run does not repeat their large arithmetic scans.

### E. Independent Reconstruction Of RD

#### E1. Literal local algebra and a uniform remainder

Take `q=1/Q`, `z=Q^(-s)`, `D=eta*z`, `R=A*Q^3*z^6`, `B=1/D`, `K=(1-q)D`, `V=W=q`. These are the ACTUAL residue substitutions `w=1,z_residue=1/6`; the factor `Q-1` in coordK must not be removed. The definitions in upstream `Detector/Euler.lean`, `Detector/Local.lean`, and `PrincipalSlotEstimate.lean` give

```text
P=(1+q)(R-D)/(1-R),
U=1-qR-(1-q)D,
continuedCorrection=(1-q^2)U/((1-R)(1-D)),
principalSlot=(1-q)(BR-1)/U-q.
```

For `a=Re(s)>=7/8`, `|D|=Q^(-a)<=1/20`, `|R|<=Q^(3-6a)<=q^2`, and `|U|>=1-1/20-480^(-3)>1/2`. Thus every division above is legitimate, including correction and D. Direct subtraction gives

```text
principalSlot+1+D =
 [(1-q)BR-q(1-q)R+(2q-q^2)D-qRD-(1-q)D^2]/U.
```

Its norm is at most

```text
2[Q^(3-5a)+Q^(2-6a)+2Q^(-1-a)+Q^(2-7a)+Q^(-2a)]
 <=12Q^(-11/8).
```

This is a uniform proof in Im(s), not a real-line extrapolation. The executed tests evaluate the original nested definitions independently before comparing this simplified expression.

#### E2. Complete product and original normalization

For slot j, let `alpha_jp=w(Q_p/Z^ell_j)Q_p^(-5/6)/M_j`, with M_j the positive sum of the original weights, and set `d_j=sum alpha_jp eta(p)Q_p^(-s)` and `e_j=sum alpha_jp E_p(s)`. The original scalar includes `(-1)^N product M_j`, so

```text
slotRatio=product_j(1+d_j-e_j)=1+sum_j d_j+R_Z.
```

If `m=min ell_j>0`, `V=sum_j|d_j-e_j|<=13N Z^(-7m/8)`. Eventually V<=1. The exact subset expansion bounds every degree>=2 term by `exp(V)V^2/2`. Consequently

```text
|R_Z| <= K_N Z^(-11m/8),
K_N=12N+(169 exp(1)/2)N^2.
```

This pays mixed products rather than asserting they cancel. Constants and thresholds may depend on the FIXED N, not Z. The factor 2 in the upper pool cutoff affects the eventual threshold `Q<=Z`, not the lower-bound exponent.

#### E3. Same signal, same exclusion set, outer weights frozen

Choose fixed positive e, reconstruct F with `FirstTail(4e)`, and take `a=7/8+e`. The existing beta<=7/8 licenses the contour. Let `c=-11/16-8h`, `chi=eta.excludePrimes F.S`, `H=sourceCorrection eta F.S`, and `f=HeckeSignal.signal chi H c`. The variable-x double-residue identity gives the exact integrand `Z^(s+c) exp((s-5/6)^2) H(s)/L_chi(s)` times slotRatio. The c shift follows from `x_phys/3-5/6+1/36` with `x_phys=17/48-24h`.

The Gaussian, bounded H and the established polynomial reciprocal bound give absolute integrability. A finite sum can therefore pass through the integral. Crucially,

```text
Z^(s+c) Q^(-s)=Q^c (Z/Q)^(s+c),
T_Z f=sum_j sum_p alpha_jp(Z) eta(p) Q_p^c f(Z/Q_p).
```

The inner value uses the SAME F.S and H; it is not a new normalized probe at Z/Q. Replacing alpha(Z) by alpha(Z/Q) is unjustified. Every fixed character has an eventual pool coprimality threshold, and every ell_j<1 implies `1<=Z/Q_p<=Z` eventually. Character-dependent thresholds are allowed by the downstream zero contradiction.

The full normalized principal residue is `f+T f+O(Z^(7/8+c+e-11m/8))`. There is no additional inverse-normalizer loss on this term: the exact normalized identity has already divided by that normalizer. Principal w/z remainders and physical tails separately pay their inverse-normalizer loss nu.

#### E4. Noncircular inversion

For any theta>0, define on a compact prefix

```text
B_X=sup_(1<=x<=X) |f(x)| x^(-theta-c).
```

It is finite from the existing signal continuity theorem. If `|f(Z)+T_Z f|<=C Z^(theta+c)` eventually, then

```text
|T_Z f| Z^(-theta-c)
 <=B_X sum_j sum_p alpha_jp(Z) Q_p^(-theta)
 <=B_X N Z^(-theta m).
```

Choose Z0 so that the last coefficient is at most 1/2. Taking the compact supremum yields `B_X<=max(B_init,C+B_X/2)`, hence `B_X<=max(B_init,2C)` independently of X. No target growth assumption enters this argument. Complex phases and correlations require no randomness.

#### E5. Exact complete return, including the strengthened parameter range

The following proves RD4 at h=m and is also the full-return input for SR3. Fix `Delta=10^(-6)`, cap the existing HighData allowances, then replace e by any positive `e<=min(e_old,m/64)` and reconstruct source/counts. Geometry, N and m are unchanged. Here `epsilon` denotes the separate detector field D.ε, `eps` denotes D.eps, and e denotes D.e; they are not interchangeable. The proved `high_data_small_errors` and the capped construction supply `epsilon<=t/2000`, `e<=t/2000`, and `(N+8)eps<=t`. Use

```text
0<h<=11m/8, h+e<=11m/8,
nu=dyadCost=t/8, zeta=mesh=margin=loss=t,
R_source=t, dmin=1/200, dmax=7/8, mu_margin=2t,
logCost=momentCost=t, heightCost=2*tau<=t,
nonfloorSaving=49/881280, largeTailSaving=1.
```

Choose tau from the existing source-height construction. It pays `C(1+Z^(2tau))^J` into `C'Z^t`, using `2tau(1+J)<=t`, and retains `4tau<(1/200)cost`, `tau<(1/200)/2`, and `tau(2+4eps)<t`. The uniform native moments are supplied at external real part 17/50, not at the principal residue's 1/6. This is a carrier distinction, not a suppressed cost.

First use `canonical_probe_exists_ray_cube_tilted_anchored` for the COMPLETE raw probe minus its principal row and central cube. Then use `physical_principal_residue_remainder_tilted_anchored`, the same normalizer, and E3. Split the central cube by `finiteCentralCubeRows_supported_split`: supported floor, supported nonfloor, and exactly vanishing zero-calibration rows. Use `actual_floor_rows_saving_tilted` with its FREE `saving=h`, and `actual_nonfloor_rows_saving_tilted` with the fixed saving above. In the floor row condition choose `d=7/8`, `v=13/16+t`; `13/16+3t<7/8` pays the required conductor margin. The common canonical idx/grid labels supply the floor and nonfloor detector hypotheses, including all original dyadic rows.

The six exponents after normalization are:

| Complete component | Exponent | Condition to be <=3/16-9h |
| --- | --- | --- |
| Small physical tails | 7/8+c-63/800+8e+nu | h+8e+nu<=63/800 |
| Large physical tails | -1-8h+nu | h+nu<=19/16 |
| Principal w/z remainders | 7/8+c-17/48000+nu | h+nu<=17/48000 |
| Retained-response remainder | 7/8+c+e-11m/8 | h+e<=11m/8 |
| Supported floor | 3/16-h-8h | equality |
| Supported nonfloor | 3/16+Delta-49/881280-8h+nu+dyadCost | Delta+h+t/4<=49/881280 |

These are statements about the same full source, not six unrelated probes. With `t<=10^(-8)`, `m<=t/200`, `h<=11t/1600`, `e<=t/2000`, and `(N+8)eps<=t`, every condition has slack except the permitted equality in the response and floor bills. Further input budgets are

```text
24h<=33t/200<t; h<1/960;
18t+49/881280<49/440640;
2t+26e+(N+8)eps+t+t/6+nu+h<7/1200;
159 epsilon+9t<1/32; 13/16+3t<7/8.
```

The independent rational check below verifies the affine worst-case endpoints; monotonicity in these nonnegative variables justifies their use as universal bounds. The stored HighData.sigma is NOT raised to h. In particular its old `sigma+e<=(7/8)ellMin` window is not invoked. This is exactly why Coordinator CR2 remains true while RD succeeds.

Under the temporary range `51/100<=actual beta<=7/8` we obtain, for every fixed eta,

```text
J_eta-(I+T)f_eta=O(Z^(3/16-9h)),
J_eta=O_omega(Z^(3/16-9h+omega)) for every omega>0,
f_eta=O_omega(Z^(7/8-h+c+omega)).
```

The middle statement is the already-proved total-mass LOW theorem, with `h<1/960`. The last follows from E4 with `theta=7/8-h+omega>0`.

#### E6. Actual beta and genuine Mertens return

Set `g=7/8-h>21/25`. If beta>g, the existing upper bound ensures the temporary range needed for moments. Choose `omega=(beta-g)/2`, so `0<omega<h` and `g+omega=beta-omega`. The primitive-zero-near-beta theorem supplies a nonpole zero with real part greater than g+omega. The existing finite-deletion theorem preserves it in chi. Apply `nonzero_of_probe_bounds_variable_boundary` with `J=f`, analytic boundary 21/25, theta=g, beta_reference=7/8, sigma=h, and c as above. Its error is zero and its maximum boundary is g+omega. The original correction is within 1/2 of one and cannot cancel the zero. Contradiction.

Therefore `beta<=7/8-h`. For h=m this proves RD5. The actual modulus-one product and Mertens converse then give the submitted b_RD. Spending `1/(128N_pack)` yields the fixed-power RD gain of the same amount below b_base. The finite initial integer range is included by the existing MertensGrowthAtMost consumer, not by endpoint-only interpolation.

### F. New Counterexamples And Sharp Scope

**SR1: weighted response inversion and its sharp endpoint.** Let f:[1,infinity)->C be locally bounded, c and theta real, and at every sufficiently large Z let

```text
T_Z f=sum_i b_i(Z) Q_i(Z)^c f(Z/Q_i(Z)),
1<=Q_i(Z)<=Z,
k_theta(Z)=sum_i |b_i(Z)| Q_i(Z)^(-theta)<=kappa<1.
```

The sums are finite; their sizes, phases and locations may vary. If `|f+Tf|<=C Z^(theta+c)` eventually, then

```text
|f(x)| <= max(B_init,C/(1-kappa)) x^(theta+c)  (x>=1).
```

Proof: use the compact-prefix B_X argument in E4 with kappa in place of 1/2. Local boundedness, not an assumed global norm, supplies finite B_X. Conversely a global bound for f gives the corresponding response bound by `1+kappa`. Thus this operator rephrasing ALONE is not a new arithmetic estimate; the independently supplied complete response bound in E5 is indispensable. Fixed N is a sufficient source condition, not necessary: the exact weighted row mass k_theta is the right criterion. For RD, `k_theta<=NZ^(-theta m)->0` is supplied by actual pool geometry.

The restriction cannot be dropped indiscriminately. Fix `0<m<1`, c real, one model slot `Q(Z)=Z^m`, coefficient `b=-1`, and

```text
f(x)=x^c log(1+log x).
f(Z)+T_Z f=Z^c log[(1+log Z)/(1+(1-m)log Z)].
```

The bracketed logarithm is between 0 and `-log(1-m)`. Thus the response is O(Z^c), but f is NOT O(Z^c). This is a counterexample to the abstract theta=0 strengthening, satisfying its local boundedness, unit phase, one-slot and delay-domain hypotheses. It is MODEL_ONLY, not a genuine Hecke-phase or Mobius counterexample, and it does not refute RD3, whose theta is positive.

Even theta>0 does not justify arbitrary slot proliferation. With `N(Z)=floor(Z^(theta*m))` identical negative model slots and `f(x)=x^(theta+c)log(1+log x)`, the response divided by Z^(theta+c) is the bounded preceding logarithmic difference plus at most `Z^(-theta*m)log(1+(1-m)log Z)`. The target f bound still fails, while k_theta approaches one. This refutes only the unrestricted growing-N extension of the abstract lemma; it is not admitted as the repository's fixed distinct-slot physical source.

**SR2: the local 11/8 remainder exponent is sharp for the stated coefficient class.** Set `Q=n^8`, `s=7/8`, `eta=A=1`, with integer n>=3. These satisfy EVERY hypothesis of RD1. Then `q=n^(-8)`, `D=n^(-7)`, `R=n^(-18)`, `BR=n^(-11)`, U->1, and E1 gives

```text
n^11 (principalSlot+1+D) -> 1.
```

Indeed the cleared numerator after multiplication by n^11 is

```text
(1-n^-8)-n^-15(1-n^-8)+2n^-4-n^-12-n^-22-(1-n^-8)n^-3,
```

and the denominator is `1-n^-26-(1-n^-8)n^-7`. This is an exact rational infinite family, not a fitted numerical trend. Consequently no uniform `o(Q^(-11/8))` replacement is possible in RD1's full stated A/eta class. Before removing -D, the raw error remains of order Q^(-7/8), so simply changing the old absolute-error exponent is false.

This does NOT prove that the genuine arithmetic remainder cannot enjoy further cancellation, nor that the full endpoint below is optimal. A new signed expansion retaining BR, or another valid joint-source argument, could pass this particular first-order barrier. A=1 is an allowed local coefficient, not an asserted realization at every genuine ideal prime.

### G. Original-Carrier Audit And Four-Way Source Map

Selected physical source: the COMPLETE fixed-source compensated OAI probe. All entries below preserve original normalizers and state the actual bridge, not an asserted equality of error terms.

| Euler / finite AC | VF / actual prime discrepancy | NNS / OAI | Square blocks / native prefix | Prime-Mobius coupling |
| --- | --- | --- | --- | --- |
| `X_R=R^2-1`, `Q_R=sum_(1<=a,b<R)mu(a)mu(b)floor(X_R/(ab))=2M(R-1)-M(X_R)`, strict historical `K_R=max_(0<=y<R)(M(y)-1)^2/(y+1)`. EXACT_IDENTITY at `eulerSelfDualBilinear_eq_two_mertens_sub_endpoint`; finite-C bound OPEN. | `F_R-D_R=L-pi(X_R)` for arbitrary real L; specialize L=li(X_R). Complete physical and virtual divisor compensation, unit survivor and root-prime admission retained. EXACT_IDENTITY, not a bound. VF/Li normalization has its fixed O(1) and classical-interface conditions. | Actual Hecke-ideal pools outside fixed F.S; compensated atoms, original alpha(Z), Gaussian and principal scalar. Signed LOW Gram EXACT_IDENTITY; no negative sign is assumed. The binding restored multiplier is internal to this source. | `M(X_R)` is a full integer prefix; shell increments and sum-of-shell-squares are not substitutes. OAI real scale Z is not identified with R or R^2. The verified beta -> zeta -> all-integer Mertens chain is ONE_WAY_IMPLICATION. | No coefficientwise equality between rational mu and ideal Hecke phases is proved or used. Owner BR's prime/floor-Li divisor renewal has different admitted events and weights. Direct marked-moment-to-wheel or arbitrary-NNS-to-Q_R recovery remains OPEN_BRIDGE. |

RD/SR do not discard diagonal, principal, mixed, conductor, remote-height or zero-calibration terms. E2 explicitly retains all finite-product interactions. E5 uses exact supported-row splitting before bounds. The final Mertens signed-pair consumer, if invoked, must retain the true squarefree diagonal; this report does not replace a square-of-sum by a sum-of-squares or spend negative covariance twice.

### H. Quantifier And No-Circularity Audit

The hierarchy is fixed Delta and geometry -> chosen positive e -> fresh source F/counts -> chosen physical h and admissible tau -> each character eta -> eventual real Z. All source constants are chosen before Z. Heights are uniformly supplied and then paid; character-dependent constants are allowed. Distinct fixed ell_j make eventual pools disjoint; no growing N is silently introduced. The actual source correction remains fixed within every individual inversion argument.

The response norm and signal norm are quantitatively equivalent under SR1's independent row-contraction condition. Therefore ASSUMING the required response estimate would merely move the unresolved quantitative claim. Here it is DERIVED: the signed local correction, exact residue identity, already-paid total-mass LOW and all six raw-return bills supply it. No norm boundedness, admissibility property, or endpoint inequality is introduced as a new premise.

Forward implication is explicit: complete response estimate -> signal bound -> actual Hecke beta -> genuine Mertens exponent. Reverse implication from the canonical VF/RH objective to this all-character Hecke beta assertion is NOT established and must not be invented; a zeta theorem is not automatically a theorem for every Hecke character. The final Mertens bound at an exponent above 1/2 is weaker in its required numerical boundary than the RH-scale Mertens conclusion and does not finish RH. No TARGET_EQUIVALENT classification is applied to this complete proof. The canonical centered wheel bound and its mere coordinate renamings remain target-equivalent, separately OPEN.

Positive losses are spent, never suppressed. Closing e in SR3 changes finite source data and its constants. It closes only a scalar inequality for the SAME beta, exactly as in the already-accepted #1119 error-closure principle. It does not establish an e=0 source, a common source mask for every e, a uniform limit of Euler products, or a no-loss Mertens power at b_SR.

### I. Constructive Extension: The Full First-Order Reserve

**SR3, complete paper proof.** Fix any original `HighData(10^(-6))` geometry D0 satisfying the explicit fine-source hypothesis `forall i:Fin D0.N, D0.ell i<=detectorMesh(10^(-6),D0.t)/200`, with `m=actualSlotMinimum D0>0`. Apply cappedHighData once; this changes allowances but not geometry. For every `0<e<=min(e_capped,m/64)`, apply withSmallerError and construct a new F/counts. Put

```text
h=(11/8)m-e.
```

Then `87m/64<=h<11m/8`, and `h+e=11m/8`. All conditions in E5 hold, so E6 gives `beta<=7/8-(11/8)m+e`. If `beta>7/8-(11/8)m`, choose e no larger than half that fixed positive gap, as well as e_capped and m/64. This contradicts the preceding inequality. Therefore

```text
forall fine D0: beta<=7/8-(11/8)actualSlotMinimum D0.
```

This extension uses no stronger local cancellation, no new LOW theorem, and no extension below the proved physical contour. It is the complete numerical optimization of the conservative reserve already provided by RD1-RD3 and the free floor-saving parameter. The principal response and floor bills can be equal to the target exponent; no strict exponent slack is needed there because the later Mertens/signal argument retains every positive omega.

**SR4, explicit fixed geometry and positive-loss spend.** Instantiate the already-proved near-uniform family, with `m>=1/(8N_pack)`, and use the native Mertens adapter:

```text
b_SR=7/8-11/(64N_pack),
b_RD=7/8-8/(64N_pack),
b_base=7/8-7/(64N_pack).

b_base-b_SR=1/(16N_pack)>0.
eta_fixed=1/(32N_pack)>0.
b_SR+eta_fixed=b_base-eta_fixed.

exists C>=0 forall integer n>=1:
  |M(n)|<=C n^(b_base-eta_fixed).
```

The original all-positive-loss conclusion at b_SR precedes this fixed-power consequence. No numerical decimal approximation to the enormous fixed slot count is needed. SR3/SR4 are author-checked complete PAPER_PROOF candidates, not independent self-acceptance and not a replacement of the certified main theorem. Their exact h-dependent six-bill assembly is the next independent review target.

### J. Competing Mechanisms And Paid Recovery Test

| Already-proved candidate | Compatibility test | Result |
| --- | --- | --- |
| Signed LOW tuple Gram / Co-Div | Exact original atoms, Hermitian orientations and compensation. At J=empty there is only one outer tuple. | Recovers an identity, not an extra binding gain; no outer-pair saving in that case. |
| Marked `1+t/2` source moment | Requires PositiveFineSourceInput, actual Batch/profile, external real part 17/50, capacity and height factor. | Valid native row supplier in E5; cannot be substituted as an estimate for an arbitrary residue profile at w=1,z=1/6. |
| Exact principal residue / signal / normalizer | SAME H, chi, outer weights and Gaussian; verified variable-x exponent. | Successful paid identity recovery. New local estimate and inversion make it quantitatively useful. |
| #1119 complete endpoint | Source-by-source positive-error closure and existing beta<=7/8. | Legitimate baseline/contour input, not RD's desired conclusion assumed in advance. |
| #1115 bands, #1122/#1124 wheel/root, #1127 fibres, #1128 resonance | Genuine integer/prime sources differ from ideal residue coefficients and normalization. | No coefficient-preserving transfer found; no saving borrowed. Proper-source positivity/resonance do not bound full wheel error. |
| CORR4 / finite-AC / MU-LIFT / NYMAN | Preserve complete mixed tails, K_R, all-prefix recurrence or full-basis/tail conditions respectively. | Remain independent protected routes; RD is not a compulsory replacement or an automatic recovery theorem on them. |

The first chronological LOW triangle and the binding principal-window loss are DIFFERENT. A useful loss ledger for the selected chain is:

| Source / location | Signed input, discarded information and cost | Consumer / recovery / remaining test |
| --- | --- | --- |
| upstream `Detector/LowTupleGram.lean:74`, source adapter `VF919OriginalLowTupleSignedGram.lean:91` | norm_sum_le loses the original tuple off-diagonal orientations. | Already represented exactly; no new sign bound supplied. J=empty falsifies an outer-pair-only saving claim. |
| upstream `PrincipalSlotEstimate.principal_slot_error` | Absorbing -D into the norm costs Q^(-7/8), hence old window `Z^(7/8+c+e-7m/8)`. | E1 restores -D with residual Q^(-11/8). Raw faster-bound strengthening fails by SR2. |
| `PrincipalSignalComparison.slotRatio_error` | Unsigned product envelope hides linear signed terms and all product interactions. | E2 retains sum d_j, pays all higher subsets at K_N Z^(-11m/8). Fixed N is essential unless SR1's stronger weighted criterion is checked. |
| `slotResidue_bound_of_reciprocal_bound` | A norm inside the integral erases the relation to the same f(Z/Q). | E3 exact dilation and E4 inversion; changing masks or inner weights would break the bridge. |
| `VF919TiltedHighCentral.lean:233,524` | Positive moment/row/dyadic bounds have explicit floor/nonfloor losses. | Every source, height and h-dependent bill is paid in E5. No conditional interface is promoted. |
| `VF919TiltedHighTails.lean:645`, principal remainder and native Mertens adapter | Raw tails, normalization and final positive losses remain. | Six-bill assembly plus genuine all-integer adapter, not a proper-band endpoint extrapolation. |

Disposition: continue formalization of independently accepted RD; independently review SR3 before extending its consumer. Keep all nine route families. The earlier finite-wheel restrictions remain useful at their actual scope; none is contradicted by a new internal OAI signed response.

### K. Original Research And Executed Verification

SR1 is the weighted-mass extension of the delay inversion, with exact theta=0 and critical growing-N countermodels. SR2 is an exact infinite-family sharpness obstruction for the submitted local coefficient class. SR3-SR4 carry the previously unused remainder reserve through every complete-source cost and numerical error closure. These are substantive derivations beyond routine handoff labeling.

**SR5 exact execution:** a newly written Python standard-library program, not the author's program, evaluated the literal nested markedFactor, continuedCorrection, compensatedReplacement and principalSlot in Gaussian rational arithmetic. It checked 5,760 legal local inputs, including Q=480 and real parts 7/8, 1, 9/8, 5/4 with complex unit phases; 108 weighted products with 1-6 slots, disjoint chosen Q values and positive weights; the exact complete subset remainder; 11 universal affine budget bounds; and all six final exponent comparisons. Zero failures. The eighth-power comparison certifies the fractional Q^(-11/8) bound exactly, without floating-point cancellation. Product tests use exp(1)<3 to produce a rational majorant; the universal paper constant remains the one in E2.

At the worst-case box `t=10^(-8),m=t/200,e=min(t/2000,m/64),h=11m/8-e`, the six target-minus-bill exponent gaps are

```text
20159999661/256000000000,
1519999998313/1280000000000,
1359994939/3840000000000,
0,
0,
96232913801/1762560000000000.
```

These are checks of monotone rational inequalities whose all-parameter proof is given in E5, not numerical evidence extrapolated to arbitrary sources. Sharpness family n=3 gives exactly `n^11 E=313763342121/317587968001`; the limiting proof is the explicit rational formula in F, not the sample values.

Reproducer SHA-256: `335ce5b48f63c4f07526a4793ccfa0ddd628141440fe83987dd4930c0afd94b8`. Complete executed code is embedded below. The local terminal session finished with exit code 0. A preliminary import check found sympy unavailable; it was not installed or used. No native evaluation, unbounded computation, primality assertion about model Q values, or Lean certification is attributed to these tests.

### L. Formalization Guidance And Current GitHub Evidence

Independent mathematical acceptance is available for RD1-RD5 only at PAPER_PROOF scope. The necessary implementation order is original principal-slot signed remainder, complete normalized finite-product expansion, exact same-signal Mellin response, local-boundedness inversion, raw anchored six-bill assembly, then the existing beta/zeta/Mertens consumer. Do not introduce the response estimate as an assumed premise of a purported unconditional endpoint. The intermediate general inversion can be formulated with SR1's weighted mass, but SR1/SR3 still require independent review as newly authored work.

For SR3 the useful source theorem is the h-parametric complete response estimate in E5 with `0<h<=11m/8` and `h+e<=11m/8`. Its source definition, original masks, and all high-data restrictions must appear in the proof. After independent acceptance, numerical closure in e is permitted by fresh-source reconstruction, not a zero-error limit. No duplicate algebra PR or no-op CI is requested.

Live merge/status evidence, independently fetched rather than inherited from stale reports:

| PR | Current state / exact tested head | Latest attached check-runs |
| --- | --- | --- |
| #1119 | MERGED 2026-11-09T04:57:27Z; head 77ee815846d6d534c866f0752aa33b84c385610a | 14/14 success; dedicated logs/types/axioms inspected in B. |
| #1126 | MERGED 2026-11-10T02:10:09Z; head e8969ad76d4c5694273cefc934316fc528c56648 | 17/17 success; conditional amplification remains conditional. No new audit of every theorem in this PR is claimed. |
| #1127 | MERGED 2026-11-10T10:38:28Z; head 866b3d2121309cdd854f9d64e2a6adbbc708ef9b | 13/13 success; earlier independent cofactor review reused, not rerun. |
| #1128 | MERGED 2026-11-10T10:40:04Z; head d5b8003f6239611a457560b6fd16e29f16255e75 | 12/12 success; repaired near-resonance theorem is now on main. |
| #1129 | MERGED 2026-11-10T12:11:24Z; head 45b0fbdc564c7cd063e2de2cc98c0051ee02457e | Governing policy merge; not a mathematical theorem. |

No open/draft PR existed at intake. No workflow was rerun, branch created, source changed, PR submitted/merged, or other agent launched. New RD/SR has NO exact-head Lean proof run to cite. Formal source receipts for the paid leaves are not certification of the newly assembled endpoint.

### M. Specialist Handoffs

- **Coordinator:** RD1-RD5 now have an independently executing Referee's ACCEPT/PAPER_PROOF verdict. Preserve certified b_base until exact-head formal verification. Review SR3's h-dependent complete return and fresh-e closure separately; proposed b_SR is below both RD and b_base, with eta_fixed=1/(32N_pack). Do not promote the author's SELF_AUDIT.
- **Analytic:** The submitted signed local algebra, normalized PLUS response, frozen weights and six-bill argument survived. Check the SR3 extension at h=11m/8-e, especially free floor saving, source-height substitution and positive-error closure. A new source estimate is not required for that candidate; an independently verified full assembly is.
- **Owner:** No prime/floor-Li event is relabeled as a Hecke phase. BR's composite admission and multiplicity defects remain relevant to any later cross-carrier transfer. RD's source is internally preserved, not an authorization to remove BR corrections.
- **Wheel:** JC's missing upper-band interaction is not paid by RD by analogy. A new transfer would need the exact original coefficients and diagonal-restored complete source. Keep FINITE-AC/CORR4/MU-LIFT independent.
- **Census:** Large-root scans are not the next validation gate for this analytic theorem. The full exact local/product reproducer is below; a distinct implementation can check it, but no finite sample establishes the beta endpoint. Preserve actual arithmetic tests on separate source hypotheses.
- **Lean Verification:** Implement independently accepted RD only with the original definitions and complete return, warning-fatal exact-head checks, exact types and terminal/dependency audit. Do not assume or silently strengthen SR3 until independently reviewed. No immediate theorem count or PR is required in place of a valid source proof.

### N. First Independently Missing Ingredient

For RD's claimed finite gain, no additional arithmetic hypothesis remains in the reviewed paper derivation; the next gap is formal implementation/verification of its new full normalized response comparison and consumer. This is different from saying the result is already kernel-certified.

For the stronger SR3-SR4 candidate, the first outstanding obligation is an independently executing review of E5/I at h=11m/8-e, followed by formal verification if accepted. The theta=0 countermodel and SR2 local sharpness identify boundaries of the method, not unresolved assumptions in its stated positive-theta range.

For canonical RH, a complete square-root-scale arithmetic estimate or another independently sufficient theorem remains OPEN. Neither the small improvement above nor an arbitrary iteration of it reaches that target. No renewed bound at a lower contour, new character-range extension, or repeated automatic improvement is proved here.

### O. Next-Run Resume Capsule And Publication Discipline

```text
RUN=20261110-referee-2/SR; trigger=SCHEDULED 12:03:01 EST; platform ID unavailable.
MAIN=655f897e274a8ba8a2fed80ecc1fc75a0d849174.
ACK=CROSS_ROUTE_SIGNED_RECOVERY_V1.
INTAKE_REPORTS=387018549541511992183afd4f09955c1e421231.
ACCEPT=20261110-analytic-2/RD1-RD5 PAPER_PROOF; Coordinator CR1/CR2 exact scope.
NEW_SELF_AUDIT=SR1 weighted inversion/sharp abstract endpoint;
              SR2 local rational sharpness;
              SR3 full 11m/8-e tilt reserve and positive-error closure;
              SR4 b_SR=7/8-11/(64N_pack); SR5 exact finite checks.
CERTIFIED_BASELINE=b_base=7/8-7/(64N_pack), unchanged.
PAPER_ACCEPTED_BOUNDARY=b_RD=7/8-1/(8N_pack).
SELF_AUDITED_BOUNDARY=b_SR; proposed fixed gain=1/(32N_pack).
VERIFIED_ETA=NONE; NEW_LEAN_THEOREM=NONE; RH=OPEN.
NEXT=independent SR3 h-parametric return review; accepted RD formalization.
DO_NOT=repeat unchanged fibre scans, equate Hecke with mu coefficients,
       claim a uniform e->0 source limit, or replace a positive loss by zero.
```

The early checkpoint was committed at `19918ef43181585fdf1a631311a660cb3591fb44` and read back byte-identically at blob `4879af75c69059592be5485e0d7f8512743cf9c0`. Final publication is claimed only after its own immutable readback. This report's only remote write target is the owned daily file on agent-reports. Direct git transport failed with CONNECT HTTP 403; the GitHub connector supplied pinned source reads and authorized writes. No credentials, private scratch notes, other report edits or local Lean runs are part of the output.

### Appendix 1. Immutable Material Source Ledger

Main source below is pinned to [655f897e274a8ba8a2fed80ecc1fc75a0d849174](https://github.com/OVVO-Financial/RH_Lean/tree/655f897e274a8ba8a2fed80ecc1fc75a0d849174). These are blob SHAs, not theorem certification labels. Exact declarations and material proof steps were inspected; unchanged prior evidence is reused only at its previously established scope.

| Main path | Blob SHA |
| --- | --- |
| `AGENTS.md` | `c9c89f01b90b526de9f3e8ea92478e36504711b6` |
| `CURRENT_PROOF_CONTRACT.md` | `95566e37c8eaeb99ee680660df4f9d2e06ea5038` |
| `docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md` | `e922d4ba9362a1ae196af8f6de88f7417f92087c` |
| `docs/PROOF_DEPENDENCY_DAG.md` | `eee764cefe70035a9f6c7df26ad787fbfd0fb233` |
| `docs/COORDINATE_ATLAS.md` | `cd0419d00a37739fe5a292f5cb738e33213949d5` |
| `research/oai_434/VF919WindowErrorClosure.lean` | `f629db1b2b65d6ec042ac9432397d4b6316200c6` |
| `research/oai_434/VF919TotalMassEndpoint.lean` | `827bb952c4d4311d75fd03a2470799dc10b0f7e7` |
| `research/oai_434/VF919NativeStrictMertens.lean` | `b33a4883e1ddb0551b0f11f062bce46680d87450` |
| `research/oai_434/VF919ExplicitSquareBlockPacking.lean` | `32999039fdeea99c58a070c1c4ee9c140720dd44` |
| `research/oai_434/VF919ExplicitFixedSourceSlotCount.lean` | `bad5aab0a60e96d19e7c9550cd7c0a072288bc0f` |
| `research/oai_434/VF919WindowSaturatedLowPrincipal.lean` | `b7b05069ea013d83b2acaa76a8ea2ed932568930` |
| `research/oai_434/VF919TiltedHighCentral.lean` | `6f75563d84161a023e4750df69ad0def460c0513` |
| `research/oai_434/VF919TiltedHighAssembly.lean` | `883141e0af896d4132bfc4ffa076e2d265ece5c9` |
| `research/oai_434/VF919TiltedHighTransport.lean` | `50c46fb1c5629865c3b7a6546ed3d9418fff1391` |
| `research/oai_434/VF919TiltedHighPrincipal.lean` | `e123ffa5903a62f6249aafef7a093dc6a7e3eb09` |
| `research/oai_434/VF919TiltedHighTails.lean` | `6ae8ea83aca3d3f8ba8d65d42f2a6a4428e6b84f` |
| `research/oai_434/VF919NativeSourceMoments.lean` | `4e5326b983f5110f7138d222f7b1be71c5694dfc` |
| `research/oai_434/VF919FiniteSlotReflectedGain.lean` | `a5545b5a00958b69f6fbfd79fc555a0476aa6487` |
| `research/oai_434/VF919NativeSevenEighthsReplay.lean` | `111c933a7ca15647105ce6a4d0f3cbfc3cde81f4` |
| `research/oai_434/VF919OriginalLowTupleSignedGram.lean` | `dd2fde01ae6e2446da4e69b30f6fc80fcadb858d` |
| `research/oai_434/VF919OriginalMarkedSharpenedSignedNNS.lean` | `1ead3888a1f59cacc71f482f6d4ce9c9ad31903a` |
| `research/oai_434/VF919OriginalOnePrimePowerGain.lean` | `492cd5d4a459c9665df07e5f77653be5261591a0` |
| `scripts/lean/slot_anchored/prepare_anchored.py` | `0bac9047afaa8e9ddc5ac246be2d0fe7d6efa725` |
| `scripts/lean/window_error_closure/WindowErrorClosureAudit.lean` | `1f17f9401a63d16227db2e2aad020b9f74bc5f4e` |
| `.github/workflows/vf919-window-saturated-low-principal.yml` | `bf53637ed649b2c8c7517ad3b81c33620f3bffa9` |
| `research/MERTENS_EXPONENT_ENVELOPES.lean` | `655b896e8d5a41c9f8fc3c456eae3944a98bfefe` |
| `research/MERTENS_CONVERSE_IDENTIFICATION.lean` | `768c8255850bf4074aff265c3fe17a1f5c43979b` |
| `research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean` | `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73` |
| `research/CompleteSquareRootWheelFractionalBoundary.lean` | `ecb482e52deeee5e9b3853592a3ffdace662d2ff` |
| `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean` | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |
| `research/FiniteWheelCofactorPositivity.lean` | `f83a3daefc2b9d603014af912ec82b4a7f52cfac` |
| `research/DyadicPrimeNearResonance.lean` | `f416e0149b73656e30a7f68a3934a937353d3f8d` |

The original OAI sources are pinned to [openai/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL). Paths below are relative to `lean/OAI/NumberTheory/DirichletL/`.

| Original upstream path | Blob SHA |
| --- | --- |
| `PrincipalSlotEstimate.lean` | `f9250c7c4464f374902bbb39ebbb3487d96bea1f` |
| `PrincipalSignalComparison.lean` | `bd252b01e2784f9ec32fe9c1e0380c4b221adc23` |
| `Detector/Local.lean` | `599ab7884122342f9d200a81119ea5a410114e0a` |
| `Detector/Euler.lean` | `ce1309a4da0b0b3ccd703946aef504b96f95e6f5` |
| `Detector/EulerCoordinates.lean` | `75a2a5a3801939489102d6e7cce2ef1cab479057` |
| `Detector/PrincipalResidueActual.lean` | `2f336d8cfb0e6ec157ad1d43099372eb61961381` |
| `Detector/PrincipalNormalizer.lean` | `890de70fac5b637af0cb803f3d8c691df6c668b2` |
| `Hecke/Signal.lean` | `9b0f1f6ff5f74c77fee06327c4936c2a9e180df5` |
| `Hecke/SignalBounds.lean` | `8b0f3faf87c2649dfccfc7c6eb4349259ff34d7e` |
| `ParametersHighData.lean` | `c565dc0a72c7da9a2706cdd835e69a39e8c0dc14` |
| `Detector/LowTupleGram.lean` | `710598c8bef4d1a1ec98aa7e68b00369962c3d17` |

### Appendix 2. Today / Yesterday Continuity And Freshness

All relevant November 10 reports are `TODAY=AVAILABLE`; November 9 is `YESTERDAY=CARRY_FORWARD`. The immutable intake is [agent-reports 387018549541511992183afd4f09955c1e421231](https://github.com/OVVO-Financial/RH_Lean/tree/387018549541511992183afd4f09955c1e421231/research/agent_reports). Availability is verified from actual files, not scheduled execution. Both coordinator mirrors are byte-identical for each date.

| Role file | November 10 blob | November 9 blob |
| --- | --- | --- |
| `00-coordinator-am.md` | `1cf71a74d0e80d5dc05ab1ef08f1ad6fcf134c9a` | `6fba43130391ad4a606aa3809c20f344d668c709` |
| `10-owner-payment.md` | `ece5b3cd8d25b45e64c48812c81d71f6eddf23a9` | `643e8a004d9d8e0be102b03e2f79bb3b217ae916` |
| `20-analytic-type-ii.md` | `a2675374a7160955917d42797eef5a3e2358056f` | `d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3` |
| `30-finite-wheel.md` | `a6a05ab41daeeaf7b3d285833028075cf253d47c` | `0624246d03b19cf76c01e186b7d868a248d896ef` |
| `40-prime-census.md` | `8a89d1a899850e39320a96bf35a6f221060fc8a7` | `8c927cc6c323533ba1cfd369404b25aa4f9cef91` |
| `50-adversarial-referee.md` | `ae7de1cb1900818b8844c2c3c7da597cc8f7eaa9` | `a5d0192eb31c0efb3767187a7752f1a0d07f8534` |
| `60-lean-verification.md` | `0355c3203ede834e1abbe9bc2fc161bc7d7ece04` | `8b60c6136ac151774be2db0aee8f543f286b53aa` |

Relevant newest handoffs actually consumed: `20261110-coordinator-0710-EST/UB` and CR1/CR2; `20261110-owner-2/BR1-BR6`; `20261110-analytic-2/RD1-RD5` and earlier HF; `20261110-wheel-2/JC`; `20261110-census-1/UC`; own `20261110-referee-1/LC`; and `20261110-lean-1` repairing `20261109-wheel-2/DG2`. Relevant prior-day CD/CF/ZD/RF/NC/AP/DA/Lean results retain their claim IDs and original review statuses. LC's HM1/UC1-UC3 acceptance and AP's CF1-CF4 acceptance are continuity, not fresh execution in this run. BR's composite admission defect, JC's missing upper bands and exact R=56 intermediate counterexamples, and UC's unsaturated-cofactor warning do not become complete-source bounds here.

`research/agent_reports/EXTERNAL_HANDOFFS.md` remains blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and the original #915 anchor/mask/denominator safeguards remain in scope. No external theorem was imported without its source hypotheses; this run's new proofs use the pinned original analytic leaves and elementary exact algebra.

**Prepublication freshness, 2026-11-10 12:24:48 EST:** main is unchanged; the open/draft PR list is empty. The refreshed agent-reports tree is `19918ef43181585fdf1a631311a660cb3591fb44`. Against the complete intake tree, the ONLY changed report file is this own checkpoint, at blob `4879af75c69059592be5485e0d7f8512743cf9c0`. Every other handoff and the external inbox are byte-unchanged. No new source or handoff therefore invalidates the review. The current own blob will be checked again immediately before its append.

Five-stage completion receipt: B = certified baseline and dependency audit; G = typed four-way source map; J = signed-loss inventory; E/J = already-proved recovery identity with masks plus newly proved arithmetic/analytic lemmas; A/I/N = net exponent, review/formalization separation and exact remaining obligation. Admission is PAPER_ACCEPTED for RD, SELF_AUDIT_PENDING for SR, not a new certified route.

### Appendix 3. Complete Independently Executed Reproducer

Run with Python 3 using only the standard library. The file bytes inside the following code block, including its final newline, have SHA-256 `335ce5b48f63c4f07526a4793ccfa0ddd628141440fe83987dd4930c0afd94b8`. The code does not modify repository source or run Lean. The original arithmetic class for the local tests is stated in E1/F; the chosen Q values are not falsely labeled genuine primes.

```python
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations, product
import json


@dataclass(frozen=True)
class G:
    re: F = F(0)
    im: F = F(0)

    def __add__(self, other):
        other = promote(other)
        return G(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.re, -self.im)

    def __sub__(self, other):
        return self + -promote(other)

    def __rsub__(self, other):
        return promote(other) + -self

    def __mul__(self, other):
        other = promote(other)
        return G(self.re * other.re - self.im * other.im,
                 self.re * other.im + self.im * other.re)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = promote(other)
        den = other.norm2()
        assert den > 0
        return self * G(other.re / den, -other.im / den)

    def __rtruediv__(self, other):
        return promote(other) / self

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out = G(F(1))
        for _ in range(n):
            out *= self
        return out

    def norm2(self):
        return self.re ** 2 + self.im ** 2


def promote(x):
    return x if isinstance(x, G) else G(F(x))


def slot_original(Q, z, eta, A):
    # z = Q^(-s); evaluate the original nested definitions, not the new ratio.
    q = F(1, Q)
    D = eta * z
    R = A * Q ** 3 * z ** 6
    K = (1 - q) * D
    P = ((R * (1 - q) - K * q) / (1 - q) - D + q * R) / (1 - R)
    correction = (1 - q * q + (1 - q) ** 2 * P) / (1 - D)
    replacement = (((1 / D) - q) * (1 - q) ** 2 * P - q * (1 - q * q)) / (1 - D)
    return replacement / correction, P, correction, D, R


phases = [G(F(1)), G(F(-1)), G(F(0), F(1)), G(F(0), F(-1)),
          G(F(3, 5), F(4, 5)), G(F(5, 13), F(-12, 13))]
amplitudes = phases + [G(), G(F(1, 2), F(1, 3))]
cases = [(n ** 8, G(F(1, n ** k)) * phase)
         for n, k, phase in product([3, 4, 7, 11], [7, 8, 9, 10], phases)]
cases += [(Q, G(F(1, Q)) * phase) for Q, phase in product([480, 481, 509, 1024], phases)]
checked = 0
for (Q, z), eta, A in product(cases, phases, amplitudes):
    slot, P, correction, D, R = slot_original(Q, z, eta, A)
    q = F(1, Q)
    U = 1 - q * R - (1 - q) * D
    assert P == (1 + q) * (R - D) / (1 - R)
    assert correction == (1 - q * q) * U / ((1 - R) * (1 - D))
    assert slot == (1 - q) * (R / D - 1) / U - q
    numerator = ((1 - q) * R / D - q * (1 - q) * R
                 + (2 * q - q * q) * D - q * R * D - (1 - q) * D ** 2)
    E = slot + 1 + D
    assert E == numerator / U
    assert U.norm2() >= F(1, 4)
    # Eighth powers certify the fractional-power inequality exactly.
    assert E.norm2() ** 4 * Q ** 11 <= 12 ** 8
    checked += 1

products_checked = 0
for n, N, offset in product([3, 4, 7], range(1, 7), range(6)):
    ratio = G(F(1))
    ds, es, us = [], [], []
    for j in range(N):
        terms = []
        for v, weight in [(0, F(1, 3)), (1, F(2, 3))]:
            root = n + 2 * j + v
            Q = root ** 8
            eta = phases[(j + v + offset) % len(phases)]
            A = amplitudes[(2 * j + v + offset) % len(amplitudes)]
            slot, _, _, D, _ = slot_original(Q, G(F(1, root ** 7)), eta, A)
            terms.append((weight, slot, D, slot + 1 + D))
        normalized = -sum((w * slot for w, slot, _, _ in terms), G())
        d = sum((w * D for w, _, D, _ in terms), G())
        e = sum((w * E for w, _, _, E in terms), G())
        assert normalized == 1 + d - e
        ratio *= normalized
        ds.append(d)
        es.append(e)
        us.append(d - e)
    higher = G()
    for size in range(2, N + 1):
        for indices in combinations(range(N), size):
            term = G(F(1))
            for j in indices:
                term *= us[j]
            higher += term
    residual = ratio - 1 - sum(ds, G())
    assert residual == higher - sum(es, G())
    assert 13 * N * F(1, n ** 7) <= 1
    # exp(1)<3 gives a rational majorant of the submitted constant.
    K = 12 * N + F(507, 2) * N * N
    assert residual.norm2() <= (K * F(1, n ** 11)) ** 2
    products_checked += 1

t = F(1, 10 ** 8)
m = t / 200
e = min(t / 2000, m / 64)
hcap = F(11, 8) * m
nu = t / 8
s0 = F(49, 881280)
budgets = {
    'tilt_tail': t - 24 * hcap,
    'physical_tilt': F(1, 960) - hcap,
    'small_tail': F(63, 800) - hcap - 8 * (t / 2000) - nu,
    'large_tail': F(19, 16) - hcap - nu,
    'principal_remainder': F(17, 48000) - hcap - nu,
    'nonfloor_target': s0 - F(1, 10 ** 6) - hcap - t / 4,
    'nonfloor_source': F(49, 440640) - 18 * t - s0,
    'floor_source': F(7, 1200) - (2 * t + 26 * (t / 2000) + t + t + t / 6 + nu + hcap),
    'conductor': F(7, 8) - (F(13, 16) + 3 * t),
    'count': F(1, 32) - (F(159, 2000) + 9) * t,
    'analytic_boundary': F(7, 8) - hcap - F(21, 25),
}
assert all(v > 0 for v in budgets.values())
h = hcap - e
c = -F(11, 16) - 8 * h
target = F(7, 8) - h + c
powers = [F(7, 8) + c - F(63, 800) + 8 * e + nu,
          -1 - 8 * h + nu,
          F(7, 8) + c - F(17, 48000) + nu,
          F(7, 8) + c + e - F(11, 8) * m,
          F(3, 16) - h - 8 * h,
          F(3, 16) + F(1, 10 ** 6) - s0 - 8 * h + 2 * nu]
assert target == F(3, 16) - 9 * h
assert all(p <= target for p in powers)
assert powers[3] == powers[4] == target

sharpness = []
for n in [3, 4, 8, 16, 32]:
    slot, _, _, D, _ = slot_original(n ** 8, G(F(1, n ** 7)), G(F(1)), G(F(1)))
    scaled = (slot + 1 + D) * n ** 11
    assert scaled.im == 0
    sharpness.append({'n': n, 'scaled_remainder_exact': str(scaled.re)})

N = 17  # A symbolic coefficient check at a finite placeholder N, not N_pack.
bbase = F(7, 8) - F(7, 64 * N)
brd = F(7, 8) - F(1, 8 * N)
bsr = F(7, 8) - F(11, 64 * N)
eta = F(1, 32 * N)
assert bsr + eta == bbase - eta
assert bsr < brd < bbase

print(json.dumps({'local_exact_cases': checked, 'weighted_product_cases': products_checked,
                  'failures': 0, 'budget_margins': {k: str(v) for k, v in budgets.items()},
                  'six_power_gaps': [str(target - p) for p in powers],
                  'sharpness_samples': sharpness}, indent=2))
```

Recorded terminal summary: `local_exact_cases=5760`, `weighted_product_cases=108`, `failures=0`; eleven strictly positive rational budget margins; six nonnegative target gaps, with equality only in the retained-response remainder and supported floor rows. The process completed with exit code 0.



### Verified Publication Receipt - 20261110-referee-2/SR

At 2026-11-10 12:28:52 EST (17:28:52 UTC), the complete substantive continuation was verified at immutable [commit af8d304f19985eadb8c7a2683a5a029dcd905daa](https://github.com/OVVO-Financial/RH_Lean/commit/af8d304f19985eadb8c7a2683a5a029dcd905daa), report blob `dd285b1fd74ccf7a8710e99b04e088e2e983561e`. The GitHub file read matched all submitted content exactly, preserved the earlier daily report and checkpoint as an unchanged prefix, and the commit's changed-file list contained only this authorized report.

The new continuation passed A-O/five-stage coverage, code-fence and exact embedded-code checks. Its prepublication text SHA-256 is `50964255802c6e3fee31b220df9ff61cf35adbcf592effbf42b44929d93147ae`; the executed program SHA remains `335ce5b48f63c4f07526a4793ccfa0ddd628141440fe83987dd4930c0afd94b8`. Mathematical checks completed with zero failures and no running computation session. No local Lean build or unauthorized remote mutation occurred.

`RUN_STATUS=COMPLETE`; `SUBSTANTIVE_REPORT=PUBLISHED_READBACK_VERIFIED`. RD1-RD5 are independently ACCEPTED/PAPER_PROOF; SR1-SR4 remain SELF_AUDIT/INDEPENDENT_REVIEW_PENDING; SR5 is exact finite verification. Formal implementation of the new RD/SR arguments remains pending, `VERIFIED_ETA=NONE`, certified main baseline unchanged, canonical RH objective OPEN. The next run should refresh actual main and review new source or objections, not repeat the unchanged arithmetic scans.


## Scheduled Independent Infinite-Response Review Checkpoint - 20261110-referee-3/IRR

Actual scheduled trigger: 2026-11-10 20:13:01 EST (America/New_York). Platform run ID unavailable. This is a new timestamped continuation of the same owned daily report. All earlier LC/SR statements, counterexamples, corrections and receipts are retained.

`cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. Intake main is `f7947bee036c4dddb0c36fc9f53ab46b4fa90995`, including human-merged #1130. Governing AGENTS blob `c9c89f01b90b526de9f3e8ea92478e36504711b6`; contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; cross-route directive `e922d4ba9362a1ae196af8f6de88f7417f92087c`.

Report intake branch snapshot: `2fa72294667a400570c057ee15b70db21d30406f`. All seven roles have reports for both November 10 and November 9; no scheduled completion is inferred. Today is AVAILABLE; yesterday is CARRY_FORWARD only at verified unchanged scope. External inbox remains `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than October 18. Open/draft PR discovery returned an empty list. Direct git transport failed with CONNECT HTTP 403; the authenticated connector supplies source reads and own-report writes. No local Lean execution or unauthorized source/branch/issue change is planned.

Highest-risk review selection: `20261110-analytic-3/IR1-IR5` and the related `20261110-coordinator-1513-EST/MD1-MD5`, especially complete-source convergence, below-one signal arguments, fixed masks and weights, free physical tilt, exact positive-loss spending and the final Mertens consumer. #1130 is a merged local supplier, not a certified global IR/MD theorem. Earlier independent RD acceptance is reusable only where actual dependencies are unchanged.

Original investigation registered: derive a sharp inversion obstruction or corrected principle for the complete rational response, distinguishing a synthetic kernel countermodel from genuine prime arithmetic; optionally test the new GC5 complete gcd-group inequality with an independent exact implementation if it provides a decisive bounded-cost falsifier. The canonical VF/RH target, finite A/C and complete wheel estimate remain OPEN. No new result or acceptance is asserted at this checkpoint.

Execution: IN_PROGRESS. Substantive verdicts, source/type/dependency receipts, exact reproducer, complete-return audit and A-O continuation are pending. Publication is claimed only after immutable readback.


---

# Independent Complete-Response Review And Multi-Slot Obstruction

## 20261110-referee-3/IRR

Scheduled trigger: 2026-11-10 20:13:01 EST, America/New_York. Platform run ID unavailable. This is a continuation of the November 10 owned Referee report, preserving LC/SR and all earlier evidence. `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`; the finite-wheel, complete-HIGH and cancellation-chain safeguards remain in force.

### A. Most Important Mathematical Finding

**ACCEPT `20261110-analytic-3/IR1-IR4` and `20261110-coordinator-1513-EST/MD1-MD5` as PAPER_PROOF at their stated fixed-source scopes.** Independent reconstruction finds no unpaid arithmetic hypothesis in the complete-return argument. In particular, the infinite response's inner arguments below one are legitimate: the ORIGINAL signal is defined on every positive argument, and its already-proved rapid decay at zero supplies the missing bound. The finite MD construction is a valid alternative that avoids those arguments. This acceptance is not Lean certification.

The strongest newly accepted paper endpoint is

```text
b_IR = 7/8 - 1/2400000000,
forall eps>0 exists C_eps>=0 forall integers n>=1:
  |M(n)| <= C_eps n^(b_IR+eps).
```

With the actual certified baseline `b_base=7/8-7/(64*N_pack)`, spending a positive loss gives the accepted paper fixed improvement

```text
eta_IR = 737/3840000000000 > 0,
exists C>=0 forall integers n>=1:
  |M(n)| <= C n^(b_base-eta_IR).
```

**Original adversarial result:** critical inversion at theta=3/5 fails much more strongly than the one-slot logarithmic example. For EVERY fixed N>=2 and positive slot lengths summing to 1/6, the complete coherent-phase model suppresses every continuous cutoff mode `x^(3/5+c) P(log x)`, where P is a nonzero polynomial of degree less than N with P(0)=0. Its full response is `o(x^(3/5+c))`, although the signal is not `O(x^(3/5+c))`. The theorem retains all within-slot powers, all mixed-slot terms, arbitrary normalized positive pool weights and the original window scales. It can use distinct arbitrarily fine slot lengths. This is a **model-only no-go for universal critical inversion**, not a genuine-prime counterexample, not a refutation of IR's strict theta>3/5 theorem, and not an obstruction to its accepted endpoint near 7/8.

The complete gcd-source conjecture GC5 was independently tested at every integer 2<=R<=2000: no failure. The previously reported R=15,17,549 witnesses were reproduced exactly. This is finite evidence only.

`NEW_LEAN_ENDPOINT=NONE; VERIFIED_ETA=NONE; CERTIFIED_BASELINE=UNCHANGED; RH=OPEN.`

### B. Current Authoritative Objective

Main is `f7947bee036c4dddb0c36fc9f53ab46b4fa90995`, the human merge of #1130. AGENTS blob `c9c89f01b90b526de9f3e8ea92478e36504711b6`; CURRENT_PROOF_CONTRACT blob `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; cross-route directive blob `e922d4ba9362a1ae196af8f6de88f7417f92087c`. The newer AGENTS directive governs task selection, not a change to any arithmetic theorem.

The canonical OPEN statement is one C>=0 before every integer R>=2, with `|pi(R^2)-VF_can(R^2)|<=C R log R`. The actual [terminal VF consumer](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean#L191) still takes `ClassicalVonKochRHCriterion` as well as the arithmetic premise. The distinct finite-AC/Mertens-energy chain does not supply its own missing uniform input. The full wheel identity retains arbitrary reference L and all virtual divisors; setting L=li(R^2-1) is not an estimate.

#### 1. BASELINE / DEPENDENCY RECEIPT

The exact current [native_mertens_near_uniform_window_error_closed](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919WindowErrorClosure.lean#L128) has no desired-bound argument. Its type is `MertensGrowthAtMost b_base`, whose original definition is EVERY positive exponent loss, not a bound with zero loss. For L=`explicitFineLength`>0,

```text
N_pack = ceil_nat(max(1,1/(6L)))+2,
N_old  = ceil_nat(max(1,1/(3L)))+2.
```

Thus N_pack<=N_old, and the #1119 explicit boundary is stronger than the older `7/8-1/(48N_old)`. This is reused CR1, not new progress or an identification of counts. The more general fine-source family remains available; no optimization over every possible source record is claimed.

The audited chain is fixed source and native moments -> complete compensated LOW and anchored HIGH/principal -> actual Hecke beta -> exact modulus-one Hecke/Dirichlet product -> actual zeta boundary -> native Mertens converse. The auxiliary positive moment hypotheses are discharged by `native_uniform_fixed_source_moments` in its actual domain `51/100<=beta<=7/8+Delta`; they are not assumed for arbitrary profiles. IR uses that domain only in the contradiction branch beta>7/8-h. The final global source is rational Mobius, not a renaming of ideal-character coefficients.

Independent hosted checks in this invocation:

| Item | Verified evidence |
| --- | --- |
| #1119 | MERGED; tested head `77ee815846d6d534c866f0752aa33b84c385610a`; [run 42552018910/job 128949473700](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700) successful; 14/14 check-runs successful. |
| #1119 dependency audit | Actual log has five PASS closures of sizes 35358,35375,35736,35737,35753, and only propext, Classical.choice, Quot.sound. Read the audit implementation and exact endpoint statement. |
| Baseline preservation | Compared all 911 preexisting blobs under RHLean/, research/oai_434/, and slot_anchored/window_error_closure audit directories against that tested tree: none changed at current main. Not a fresh whole-main compilation. |
| #1130 | MERGED; tested head `4aa22782d10b3ad77dc970d6bb610eaab93a228c`; [run 42877550772/job 130044786387](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42877550772/job/130044786387) successful; 13/13 check-runs successful. |
| #1130 dependency audit | Actual log has four quantitative PASS closures 628,984,653,657, standard terminal axioms only. This proves RD1 and its actual/weighted adapters, NOT the complete RD, MD or IR endpoint. |

The audit follows live OAI/RHLean/private proof values and separately uses Lean.collectAxioms transitively. This is scoped formal evidence, not an independent reproof of every imported analytic theorem. The baseline dependency build includes historical Wiener.lean `sorry` warnings; they do not occur in the selected endpoint's audited axiom closure. Do not call the entire imported repository placeholder-free.

Pins: Lean 4.34.1/compiler `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; PrimeNumberTheoremAnd `c39a751132c88b6e8080b74c74023fd95b3d8be0`; upstream `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`; anchored generator source `9cbfce5295343bcb411e6d2cb159b59995cd985b`. Existing compile pins and unchanged audited sources are reused. No local Lean execution occurred.

All seven roles' November 9/10 reports were retrieved at `agent-reports@2fa72294667a400570c057ee15b70db21d30406f`, and relevant latest sections read. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD at unchanged verified scope, not an assertion of every upstream claim's truth. Coordinator mirrors have identical blobs. External inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than October 18; historical source/cutoff/normalization cautions remain, but those routing notices are superseded. Original AP/LC/SR verdicts are retained. CD/CF/ZD/RF/NC and current DR/RC/JC are continuity inputs, not collectively newly accepted by this run.

### C. Highest-Risk Proof Mechanisms

IR/MD are selected because they claim a COMPLETE global improvement. The main risks are whether countably many returned terms use the same signal and exclusions, whether inner arguments below one are legal, whether the proposed physical tilt violates source hypotheses, and whether constants precede Z and n. All were checked against original declarations rather than a green badge or another author's self-audit.

The independent question is whether IR's strict critical threshold is merely a loose triangle estimate. Section F shows a real universal-inversion obstruction even with the complete multi-slot geometry. It does not reject source-specific arithmetic restrictions capable of excluding that model.

### D. Claims Reviewed And Verdicts

| Original claim | Referee verdict | Evidence level / exact scope |
| --- | --- | --- |
| `20261110-analytic-3/IR1` | ACCEPT | PAPER_PROOF: complete labelled expansion and absolute theta-mass for every fixed theta>3/5, fixed N and positive minimum length; all phases/mixed terms retained. |
| IR2 | ACCEPT | PAPER_PROOF: original normalized residue equals f+K_Z f for all sufficiently large real Z; right contour shift and countable interchange justified; same fixed source below one. Not implemented in Lean. |
| IR3 | ACCEPT | PAPER_PROOF / CONDITIONAL: noncircular inversion from an independently supplied response bound; by itself a two-way growth reformulation. |
| IR4 | ACCEPT | PAPER_PROOF: full physical return for every fixed 0<h<t/24, numerical closure only in h, exact native Mertens adapter and positive-loss comparison. Not PROVED_IN_LEAN. |
| IR5 | ACCEPT | PAPER_PROOF: coherent one-slot model at theta=3/5; not asserted to be a genuine prime-ideal occurrence or actual Hecke signal. |
| `20261110-coordinator-1513-EST/MD1-MD5` | ACCEPT | PAPER_PROOF: finite total-degree truncation, all mixed terms, strict delay cutoff, same-source compact inversion and complete endpoint at h=t/100. |
| #1130 / RD1 adapters | ACCEPT | PROVED_IN_LEAN_ON_MAIN at their local scope; exact original Q-1, actual unit hypothesis, positive outer weights and negative-normalizer sign retained. |
| `20261110-census-2/GC1-GC2` | ACCEPT | REFUTED auxiliary sign rules; independent exact witnesses and exhaustive minimality check through their first failures. |
| GC3 coarsening identity | ACCEPT | PAPER_PROOF algebra, retaining both orientations. Does not supply GC5's sign. |
| GC5 | UNRESOLVED | CONJECTURE; independent finite checks through 2000 found no counterexample. No all-scale proof. |
| New `20261110-referee-3/IRR2` | SELF_AUDIT | PAPER_PROOF below; complete multi-slot critical near-kernel. Independent review pending. |
| New IRR3/IRR4 | Executed evidence | FINITE_COMPUTATION: response/budget and complete gcd-source tests, respectively. |

There is no newly rejected submitted theorem in IR/MD. The rejected assertion is the expressly stronger universal critical-inversion extension, whose hypotheses are stated in F. Prior SR3/SR4 is not newly self-certified by its author; the accepted IR proof independently supersedes its proposed numerical strength.

### E. Independent Mathematical Reconstruction

#### E1. Exact source and complete coefficient mass

Fix a valid fine source before scale: N>=1, distinct ell_j>0, sum ell_j=1/6, m=min ell_j>0. At every sufficiently large Z the original finite ideal pools have `Z^ell_j<=Q_jp<=2Z^ell_j`, positive total weight M_j and normalized nonnegative weights `alpha_jp=w_jp/M_j`, sum_p alpha_jp=1. Take the genuine A=`actualAPhase`, eta_p=`idealCoeff`, so |A|<=1 and |eta_p|=1 after the actual coprimality threshold. The raw local statement also holds for arbitrary coefficients satisfying those inequalities.

With q=1/Q and z=Q^(-s), define D=eta_p*z, R=A Q^3 z^6, G=qR, W=conj(eta_p)R/z and Hloc=G+(1-q)D. Original `principalSlot`, not a surrogate, gives

```text
S_Q(s)=-principalSlot(Q,A,eta_p,s)
      =q+(1-q)(1-W)/(1-Hloc).
```

This was rederived from the nested marked/correction/replacement expressions and #1130's exact Q-1 identity. The negative original normalizer is essential. On Re(s)>=7/8, `|Hloc|<=Q^(-13/4)+Q^(-7/8)<1/2` for Q>=480. Thus all original divisions and the geometric series are legal uniformly in height.

For r,b>=0, d in {0,1}, excluding (0,0,0),

```text
v=6r+b+5d, u=2r+3d,
c_rbd=(-1)^d binom(r+b,r)(1-q)^(b+1)
       A^(r+d) eta_p^(b-d) Q^u,
S_Q(s)=1+sum' c_rbd (Q^v)^(-s).
```

At any fixed theta>3/5 put `g=Q^(2-6theta)`, `d0=(1-q)Q^(-theta)`, `w=Q^(3-5theta)`, r0=g+d0. The binomial geometric sum gives

```text
sum' |c_rbd| Q^(-theta v)
 <= (1-q)(r0+w)/(1-r0) = L_theta(Q),
tail after r+b<=K <= (1-q)(1+w) r0^(K+1)/(1-r0).
```

The inequality becomes equality for the unmerged labelled absolute sum when |A|=1. Original pool averaging and the complete N-fold convolution give

```text
P_Z(s)=product_j sum_p alpha_jp S_Qjp(s)
      =1+sum_i B_i(Z) T_i(Z)^(-s),
kappa_theta(Z)=sum_i |B_i| T_i^(-theta)
 <= product_j(1+sum_p alpha_jp L_theta(Q_jp))-1
 <= exp(6N Z^(-delta_theta*m))-1 -> 0,
delta_theta=min(theta,5theta-3)>0.
```

This retains every nonempty slot subset, within-slot power and cross product. Coincident delays may remain separately labelled. Cardinality of a moving pool does not multiply a bound because its original normalized positive weights sum to one. Constants and thresholds need not be uniform in moving N or m; neither is allowed to move here.

#### E2. All-positive-argument return and inversion

Fix `chi=eta.excludePrimes F.S`, H0=`sourceCorrection eta F.S`, c=-11/16-8h and f=`HeckeSignal.signal chi H0 c`. The [exact variable-x normalizer](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919FiniteSlotReflectedGain.lean#L846) gives the normalized residue integrand

```text
Z^(s+c) exp((s-5/6)^2) H0(s)/L(chi,s) P_Z(s).
```

Choose a=7/8+e with e>0. The certified beta<=7/8 puts this line strictly to the right of all relevant zeros. Use the original raw-quotient/analytic-reciprocal a.e. identity first; isolated exceptional points are not silently equated pointwise. The actual `polynomial_reciprocal_bound` bounds the analytic reciprocal by `C(1+|Im s|^2)` uniformly on Re(s)>=a. H0 is analytic and bounded, and P_Z is a finite product of bounded holomorphic rational factors there. For fixed Z, horizontal sides of a Cauchy rectangle between a and 2 are bounded by `C_Z(1+H^2)exp(-H^2)` and vanish. The shift is therefore valid without a uniform-in-Z contour constant.

On Re(s)=2, the entire coefficient series is absolutely summable with its T^-2 weight. Tonelli domination permits interchanging the series with the Gaussian integral. Since `Z^(s+c)T^-s=T^c(Z/T)^(s+c)`, the original [signal_eq_contour](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Hecke/Signal.lean#L53), which requires only x>0, proves

```text
normalized double residue = f(Z)+K_Z f,
K_Z f=sum_i B_i(Z) T_i(Z)^c f(Z/T_i(Z)).
```

The same exclusions, H0, c and outer alpha(Z) are used for every term. No alpha(Z/T), new source or new physical probe is inserted. No claim T_i<=Z is needed.

The original [signal_bound_at_zero](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Hecke/Signal.lean#L146) and continuity give finiteness of

```text
B_X=sup_(0<x<=X) |f(x)|/x^(theta+c)
```

for each finite X: choose B=max(2,theta) in the small-x theorem. If `|f(Z)+K_Z f|<=C Z^(theta+c)` eventually, choose Z0 with kappa_theta<=1/2. Every delayed argument is positive and <=Z. Taking suprema gives `B_X<=max(B_initial,C+B_X/2)`, hence `B_X<=max(B_initial,2C)` uniformly in X. This is not a hidden global boundedness assumption. The reverse growth implication follows from the same weighted mass and local control; IR3 alone is a CONDITIONAL equivalence. Its antecedent is supplied next.

#### E3. Complete physical return and uniformity

Use Delta=10^-6, t=D.t<=10^-8, cap the original detector parameter so `(N+8)eps<=t`, and retain e,epsilon<=t/2000. Choose valid source/count data before eta and Z. Fix ANY 0<h<t/24. Keep the stored D.sigma unchanged. Set

```text
g=7/8-h, c=-11/16-8h, nu=dyadCost=t/8,
zeta=mesh=margin=loss=R_source=t,
dmin=1/200, dmax=7/8, mu_margin=2t,
logCost=momentCost=t, s0=49/881280.
```

The original fine-data budgets supply all slot, detector, phase and exclusion conditions. `native_uniform_fixed_source_moments` supplies a height exponent J BEFORE eta, in the contradiction branch beta>g>51/100. Choose tau>0 after J and before Z, small enough that `2tau(1+J)<=t`, `4tau<dmin*cost`, `tau<dmin/2`, and `tau(2+4eps)<t`. Then the true source height `(1+Z^(2tau))^J` is paid at the permitted polynomial cost. The moment profile is 17/50, not the principal-residue profile 1/6.

The pinned anchored generator preserves actual beta and uses its independently certified upper bound only to license reference contours. Use its RAW canonical-probe and principal-remainder leaves; do not invoke the bundled theorem with D.sigma's window restriction. The central split retains calibration zeros, all supported floor rows, all supported nonfloor rows and their original common labels.

| Complete bill | Normalized exponent | Remaining condition for <=g+c=3/16-9h |
| --- | --- | --- |
| Small tails | 7/8+c-63/800+8e+nu | h+8e+nu<=63/800 |
| Large tails | -1-8h+nu | h+nu<=19/16 |
| Principal w/z remainders | 7/8+c-17/48000+nu | h+nu<=17/48000 |
| Principal rational response | EXACT f+K_Z f | No remainder; no extra inverse-normalizer tax |
| Entire floor population | 3/16-h-8h | Free RAW saving=h; floor budget below |
| Entire nonfloor population | 3/16+Delta-s0-8h+nu+dyadCost | Delta+h+t/4<=s0 |

Read the actual floor-row theorem: saving is a free parameter subject to
`2zeta+26e+(N+8)eps+loss+mesh/6+nu+saving<=7/1200`. It does not impose saving<=m or saving<=D.sigma. The original nonfloor final cost is bounded by

```text
(13/16)(159epsilon+9t)+2t+3t+26e+t+t+t/6+3t < 18t.
```

Together with `18t+s0<49/440640`, `159epsilon+9t<1/32`, `13/16+3t<7/8`, and h<1/960, all source and return inequalities have positive margins at the worst closed-box endpoint t=10^-8,h=t/24,e=epsilon=t/2000. Each relevant expression is affine with nonnegative cost coefficients; monotonicity pays the whole interior. The STRICT gate `24h<t` is imposed separately, never asserted at equality. Twelve exact rational margin checks are recorded below.

Consequently `J-(I+K)f=O(Z^(g+c))` for the SAME `J=F.tiltedProbe h eta`. The already-proved `SourceData.tiltedProbe_low_total_mass` gives J=O(Z^(g+c+omega)) for every omega>0. Section E2 with theta=g+omega>3/5 yields f=O(Z^(g+c+omega)). This closes the entire response, not a proper band.

If beta>g, choose omega=(beta-g)/2 and an actual primitive nonpole zero with real part >g+omega. Finite prime deletion preserves this zero. The same correction is analytic and within 1/2 of one on Re(s)>21/25. In `nonzero_of_probe_bounds_variable_boundary`, put J=f, analytic boundary 21/25, theta=g, reference beta=7/8, sigma=h and error identically zero. Its maximum crossing is g+omega, giving the required contradiction. No favorable sign, random phase or hypothetical arithmetic norm is added.

Thus beta<=7/8-h for every fixed 0<h<t/24. Closing ONLY this numerical inequality gives beta<=7/8-t/24. There is no limiting h=t/24 physical source, no uniformity of analytic constants in h, and no zero-error limit. The actual modulus-one product and native Mertens converse then give the every-positive-loss b_IR bound.

Finally L<=t/200 implies `7/(64N_pack)<=21t/6400`, hence
`t/24-7/(64N_pack)>=737t/19200`. Spend epsilon=eta_IR=737t/38400, rather than dropping epsilon. This proves the stated fixed comparison at t=10^-8 on paper. It does not establish a repeatable bootstrap.

### F. New Counterexamples And No-Go Results

#### IRR2: Polynomial near-kernel for the COMPLETE critical multi-slot model

**Precise excluded statement.** The implication `f+K_Z f=O(Z^(3/5+c)) => f=O(Z^(3/5+c))` is FALSE for all continuous rapidly-zero-at-origin f and all complete rational response families with the above fixed slot geometry, nonnegative normalized pool weights and locally admissible phase bounds. It remains false if the antecedent is strengthened to little-o. This is a universal model theorem; no claim is made that the counterexample f is a Hecke signal.

Fix N>=2, any positive distinct ell_j with sum 1/6, m=min ell_j>0, and any fixed c. For each large Z choose nonempty finite pools `Q_jp in [Z^ell_j,2Z^ell_j]` with any normalized nonnegative weights. In the MODEL take A=eta_p=1 in every slot. This is legal for the abstract local coefficient bounds. The theorem accommodates the actual fine length constraints, but does not assert that an arbitrary such phase assignment is arithmetically realized.

Let theta0=3/5. Write W=Q^(3-5s) and retain the exact rational factor. In the labelled absolute theta0 norm,

```text
S_Q = (1-W)+E_Q,
E_Q = qW+(1-q)(1-W)Hloc/(1-Hloc),
||E_Q||_(theta0) <= q+2(1-q)r/(1-r) = O(Q^(-3/5)),
r=Q^(-8/5)+(1-q)Q^(-3/5).
```

This is the FULL geometric remainder, not a truncation. Pool averaging preserves the bound. The weighted norm of each `(1-W)` factor is at most two. Finite product telescoping therefore gives

```text
||P_Z - product_j average_p(1-W_jp)||_(theta0)
 <= product_j(2+delta_j)-2^N = O_(N,ell)(Z^(-3m/5)),
delta_j=sup_p ||E_Qjp||_(theta0).
```

Choose any nonzero polynomial P with P(0)=0 and degree k<N, and define

```text
f(x)=0                         for 0<x<=1,
f(x)=x^(theta0+c) P(log x)      for x>1.
```

This f is continuous on (0,infinity), is zero near the origin, and is not O(x^(theta0+c)). For the pure-W product, EVERY subset delay satisfies
`T_S=product_(j in S)Q_j^5 <=2^(5N)Z^(5/6)<Z` eventually. Thus all pure-product inner arguments exceed one. At a fixed pool tuple its normalized action is exactly

```text
sum_(S subset {1,...,N}) (-1)^|S|
  P(log Z - 5 sum_(j in S)log Q_j) = 0.
```

Proof: each difference operator `P(u)->P(u)-P(u-a)` lowers polynomial degree by at least one. N commuting differences annihilate any degree k<N polynomial. This argument holds for each tuple separately, so arbitrary original positive pool averaging preserves exact cancellation. It does not assume that the moving-delay operators compose as scale-independent operators.

For every remaining delay T>=1, the normalized delayed value is bounded by `C_P(1+log Z)^k`; when Z/T<=1 it is zero. Absolute summability of the complete theta0-labelled series and the preceding product remainder imply

```text
|f(Z)+K_Z f|
 <= C_(P,N,ell) Z^(theta0+c-3m/5)(1+log Z)^k
  = o(Z^(theta0+c)).
```

This is an infinite-family obstruction with ALL geometric powers and mixed slots restored. It extends IR5's one-slot log-log mode to an (N-1)-dimensional polynomial family matching arbitrary fixed fine slot geometry. No infinite census or numerical trend is used in the proof.

**Surviving theorem:** IR3 is valid at EVERY fixed theta>3/5. At the critical endpoint, a future inverse theorem needs additional source-specific conditions that actually exclude or control these modes; deleting them by definition would not prove an estimate for the original signal. No conclusion about impossibility of RH, all analytic methods, or actual arithmetic cancellation follows. The present physical h<t/24 and correction-domain gates are separate limits of this implementation, not universal no-go barriers.

### G. Original-Carrier And Covariance Audit

#### 2. FOUR-WAY SOURCE MAP

The selected complete source is the actual fixed-source tilted OAI probe. The four columns below are typed bridges and barriers, NOT four equal formulas.

| Field | Euler / finite AC | VF / actual prime | NNS / OAI | Square blocks / native prefix |
| --- | --- | --- | --- | --- |
| Exact source | X=R^2-1; Q_R=sum_(1<=a,b<R)mu(a)mu(b)floor(X/(ab)); strict-history K_R | Complete wheel F_R-D_R=li(X)-pi(X), all physical/virtual divisors; separate clipped #915 returned packets | J=F.tiltedProbe h eta, literal ideal tuples, source exclusions, original W0/W1 and principal normalizer | Actual M(n), including M(R^2-1), not a shell increment |
| Certified map | `eulerSelfDualBilinear_eq_two_mertens_sub_endpoint`: Q_R=2M(R-1)-M(X) | `finiteWheel_squareFractional_centered_eq_reference_sub_pi`; actual VF/Li equivalence has its own normalization | Exact LOW signed Gram and principal residue normalization; complex-to-real isometry preserves both orientations | `native_mertens_growth_at_hecke_beta`, through actual L-product and native converse |
| This review's edge | ONE_WAY consequence of the accepted all-prefix paper estimate; no new control relative to sqrt(K_R) | OPEN_BRIDGE to RH-scale discrepancy; prime error is not equal to M or an ideal coefficient | EXACT_IDENTITY and PAPER_PROOF complete-response estimate on original masks; no arbitrary-profile moment substitution | ONE_WAY analytic consequence at every integer prefix, all positive losses retained |
| Barrier / restoration | Both pair orientations and full floors retained; no historical denominator discarded | Chronology, ownership, clipping and Euler virtual compensation cannot be inferred from the OAI norm | Principal 1/6 profile differs from marked 17/50 input; full residual/LOW/HIGH reassembly required | Square-of-sum includes diagonal and all signed cross pairs; sum-of-squares is not an equivalent source |

#### IRR4: Independent genuine-source gcd checks

Define `C_R(g)=sum_(1<=a,b<R, gcd(a,b)=g)mu(a)mu(b)floor((R^2-1)/(ab))`, Q=sum_g C_R(g), A=C_R(1), B=sum_(g>=2)C_R(g). The exact coarsening identity is

```text
Q^2-sum_g C_R(g)^2
 = 2AB + (B^2-sum_(g>=2)C_R(g)^2).
```

Consequently a favorable fine cross term does not imply favorable binary covariance. Independent exact output:

| R | Q | C(1) | C(2) | B | 2AB | Q^2-sum_g C(g)^2 |
| --- | --- | --- | --- | --- | --- | --- |
| 15 | -7 | -12 | -6 | 5 | -120 | -174 |
| 17 | 5 | 4 | -6 | 1 | 8 | -148 |
| 549 | -186 | -28 | 70 | -158 | 8848 | -178880 |

At R=17 the missing within-shared contribution is -156; at R=549 it is -187728. H_POS first fails at R=15, and H_SPLIT first fails at R=17, verified by exhaustive roots from 2. The new universal conjecture GC5, `Q^2<=sum_g C_R(g)^2`, has NO failure on 2..2000. This does not prove GC5, bound its right side at the required scale, or test a claim involving K_R. The experiment did not compute K_R because that variable does not enter GC5. No denominator-normalized finite-AC conclusion is asserted.

### H. Quantifier And Circularity Audit

Fix N, ell, e, source exclusions, source/count data and h before Z. Character-dependent eventual thresholds and constants are permitted, but the signal for a fixed character cannot change with each delay. The final Mertens constant depends on its chosen positive loss and precedes ALL integers n. Tiny fixed exponents permit enormous thresholds; no computational practicality is claimed.

IR3 and MD3 alone are conditional growth equivalences. The new information is the full coefficient-mass estimate plus the separately paid physical comparison, not the new operator's name. IR4 is not TARGET_EQUIVALENT to RH and does not renew itself at a new contour. The baseline is not used circularly: its already-proved beta<=7/8 licenses a stronger contradiction argument at g<7/8, using RAW suppliers whose hypotheses were inspected. No theorem requiring actual beta>=7/8 is reused below its domain.

The h endpoint is numerical closure of a family of independently proved inequalities. It is not an interchange of limits with countable sums or moving sources. Every-positive-loss growth is converted to a fixed power only by explicit epsilon spending. The count comparison uses real inequalities between N_pack and N_old rather than interchangeable symbols.

### I. Constructive Repairs And Implementation Choice

No correction to IR1-IR4's submitted mathematical conclusion was needed. Two safeguards should remain explicit in implementation: shift the COMPLETE principal integrand right before the countable exchange; use all-positive-argument rapid decay in the compact supremum. Calling the existing x>=1 left-shift theorem at x<1 would be an invalid proof even though the corrected argument is valid.

There is a finite alternative at the SAME accepted ceiling. For any 0<h<t/24 and e<=t/2000, choose rho=t/12. Then `h+e<rho<11/40`. MD's finite truncation with `(7/8)(K+1)m>=rho` and total weighted-degree cutoff lambda<rho keeps every term needed for accuracy. Its support cone `u<=3v/5` implies delta<40rho/11<1, so every retained delay is eventually <=Z. This finite response plus E3's same RAW return proves the same interior h estimates, then the same numerical endpoint. It avoids the new countable contour step without weakening the accepted endpoint.

This is an explicit implementation specialization of the already-discussed MD retuning, not a second independent global mechanism or a new arithmetic theorem. The finite K may be extremely large but is fixed before Z; Lean should prove the parametric finite theorem, not enumerate its terms.

### J. Competing Strategy Assessment

#### 3. FIRST SIGNED LOSS

| Declaration / step | Exact discarded information and tax | Paid recovery / remaining bill / first falsifier |
| --- | --- | --- |
| upstream principal_slot_error and PrincipalSignalComparison.slotRatio_error | Replacing original S_Q by 1 loses +D, -W and every higher/mixed returned term; old principal tax e-(7/8)m | #1130 recovers only first response; MD/IR now recover full needed response. An omitted W term or changed normalizer sign immediately breaks local algebra. |
| original normalized residue | Taking a norm inside the integral forgets that Q^-s is a dilation of the SAME signal | Exact variable-x normalizer and signal contour/rapid-zero theorems pay this transfer. Changed alpha(Z/T) or exclusions reject the bridge. |
| LOW tuple norm_sum_le | Signed Hermitian off-diagonals discarded before norms | Existing exact LOW Gram restores them but supplies no sign. J=empty has one outer tuple. This is not the source of the accepted IR recovery. |
| raw central row and tail bounds | Norms, bin counts, dyadic and height factors remain | Existing native moments, supported split and raw anchored leaves pay the complete E3 ledger. A missing floor/nonfloor/tail population rejects the global gain. |
| complete rational gcd groups | Coarsening loses internal shared-sector interactions | Exact coarsening identity; R=17/549 refute sign preservation. GC5 remains unproved and has no independently proved norm consumer at the target scale. |

#### 4. PAID RECOVERY TEST

The actual recovery uses original local rational algebra, #1130's retained-response source, the exact normalizer, original Hecke signal contour and rapid-zero estimates, total-mass LOW, native moments, raw supported-row bounds and raw anchored tails. These are source-compatible. #1115 completed reciprocal bands, #1127 proper-fibre positivity, #1128 dyadic resonance and Owner/Wheel DR/RC identities do not provide a coefficientwise map to this ideal-labelled principal response. No fictitious cross-route equality was used.

Keep all nine authorized routes. Prioritize formal verification of the accepted complete OAI return while leaving VF-LOW/SAT/JOH and FINITE-AC/CORR4/MU-LIFT independently active. CODIV gets only the genuine complete signed-energy consequence of a Mertens estimate; NYMAN does not inherit the Hecke signal's pointwise rapid-zero condition. No alternative route is retired merely because its current result is a proper-source theorem.

#### 5. NET RESULT / ADMISSION VERDICT

`ACCEPTED_NEW_GLOBAL_GAIN_ON_PAPER` within the existing OAI route; `FORMAL_ENDPOINT_PENDING`; `VERIFIED_ETA=NONE`. The paper candidate satisfies the numerical global-gain form of the admission test after all costs are paid, but the repository's certified baseline and open statuses must NOT be changed until exact-head formal verification. IRR2 is a substantial method-specific obstruction, not a new accepted RH route or a genuine-prime no-go. GC5's finite survival is not route admission.

### K. Original Research And Executed Verification

New IRR2 is the independent multi-slot polynomial near-kernel theorem in F, beyond review of submitted IR5. It explains why a whole family of apparent critical response bounds can coexist with larger signals, even after all cross products and tiny slot lengths are retained.

IRR3 used newly written exact Gaussian-rational arithmetic, not the upstream submitted checker. It evaluated the literal nested marked/correction/replacement formulas on 240 legal Q/phase inputs; independently reconstructed 960 finite geometric expansions and their exact tails; tested 24 COMPLETE multi-slot critical responses using two, three and four DISTINCT lengths and all degrees 1<=k<N; and verified twelve complete-return margins with rational arithmetic. Total 1,236 checks, zero failures. For critical tests, terms whose inner argument is <=1 vanish exactly by the test function, so the finite coefficient sum evaluates the ENTIRE countable response, not an arbitrarily truncated approximation. Toy Q values are not asserted to be genuine prime norms or actual detector slots.

IRR4 is a separately written C++ exact sieve and ordered-pair/gcd grouping for all 1,999 roots 2..2000. Every complete Q also matched `2M(R-1)-M(R^2-1)`. Pair orientation and diagonal multiplicity are explicit; all quantities used for squares have 128-bit accumulation. This is one independent implementation with a distinct endpoint-identity consistency check, not a claim of two independent primality implementations. It found zero GC5 failures and reproduced the stated minimal sign witnesses.

Reproducer SHA256 values: Python `7da4964ae8ee2e9beadc7047b2fc4d04a02217d672d0479183ac3de681c81f54`; C++ `8c6c1f6e214895a38d5aa58005a78b12c80f0154adc933193f955c214e4e9784`. Both processes finished successfully. Full code and recorded output are appended. Floating displays are diagnostic only; all acceptance assertions use exact integers/fractions. No finite test is substituted for a universal proof.

### L. Formalization Guidance

Independent acceptance is now available for the complete MD and IR paper claims, not only RD1. Lean Verification can implement the finite parametric MD path at rho=t/12 and free 0<h<t/24, or the complete IR countable path, while retaining source, type, import, public-export, dependency and terminal-axiom checks. The finite path minimizes new countable-analysis infrastructure. Neither may introduce its final response bound as an assumed desired-bound premise.

Suggested necessary order: exact original complete product coefficients and weighted cutoff; same-signal dilation with frozen masks; compact-prefix inversion; raw full-source h-parametric return; actual beta contradiction; positive-loss native Mertens consumer; numerical endpoint closure. Reuse #1130. No duplicate local-algebra-only PR is requested in place of the endpoint.

IRR2 is new SELF_AUDIT and requires independent review before being used as accepted formalization input. A suitable theorem is the N-fold finite-difference annihilation plus the complete labelled remainder estimate, clearly on a model carrier. Do not encode it as an obstruction to an actual Hecke signal. Do not formalize GC5 as true from the finite scan.

### M. Specialist Handoffs

- Coordinator: MD1-MD5 and IR1-IR4 now have an independent Referee ACCEPT/PAPER_PROOF verdict. Keep certified b_base unchanged. Treat finite/infinite constructions as implementations of one mechanism, with the common physical return still requiring Lean verification.
- Analytic: preserve all-positive-argument rapid decay and the complete right shift. Independently review IRR2, especially tuplewise finite differences with moving pools and the O(Z^(-3m/5)) full remainder; no need to assume arithmetic realization of coherent phases.
- Owner: DR remains continuity, not newly blanket-accepted. No prime/floor-Li event has been reclassified as a Hecke phase. The accepted principal response does not pay the complete weighted Buchstab/first-bad source by analogy.
- Wheel: RC/JC remain separate auxiliary/source claims. Do not infer that a proper-fibre sign or completed-defect bound transfers to Q_R's gcd groups; the exact R=15/17 witnesses survive.
- Census: GC1-GC3 have the scoped acceptance above; GC5 survives independently through 2000 but is still CONJECTURE. A next useful test should target predicted exceptional configurations, not simply label this finite scan a theorem. Keep K_R in any proposed finite-AC consumer.
- Lean Verification: complete MD/IR paper acceptance is ready. A fixed rho=t/12 finite formulation realizes the stronger h<t/24 range without below-one arguments; implement only with actual original coefficients and all raw return hypotheses. The first true remaining gap for this paper gain is formal verification, not a newly postulated arithmetic estimate.

### N. First Independently Missing Ingredient

For the accepted finite improvement, the missing item is a kernel-verified COMPLETE product/dilation/inversion/physical-return theorem and its native Mertens consumer. No additional arithmetic hypothesis was left unpaid in the reviewed paper argument. Failure of implementation to instantiate one of the displayed original-source hypotheses must reopen the corresponding paper verdict, rather than be hidden by a new assumption.

For canonical RH, a square-root-scale complete source estimate or another independently sufficient arithmetic theorem remains OPEN. The fixed h gate, correction domain and critical response threshold are not a renewal theorem. For GC5 the first missing theorem is its all-root sign itself, followed by an independently useful norm bound; neither is provided here.

### O. Next-Run Resume Capsule

```text
RUN=20261110-referee-3/IRR; trigger=SCHEDULED 20:13:01 EST.
MAIN=f7947bee036c4dddb0c36fc9f53ab46b4fa90995.
ACK=CROSS_ROUTE_SIGNED_RECOVERY_V1.
INTAKE_REPORTS=2fa72294667a400570c057ee15b70db21d30406f.
ACCEPT=20261110-analytic-3/IR1-IR5 PAPER_PROOF at exact scopes;
       20261110-coordinator-1513-EST/MD1-MD5 PAPER_PROOF;
       GC1-GC3 exact sign/algebra scopes.
NEW_SELF_AUDIT=IRR2 complete multi-slot critical polynomial near-kernel.
EXECUTED=IRR3 1236 exact response/budget checks; IRR4 1999 roots.
GC5=UNRESOLVED; no failure through 2000.
CERTIFIED_BASELINE=7/8-7/(64*N_pack), unchanged.
PAPER_ACCEPTED_BOUNDARY=7/8-1/2400000000, every positive loss.
PAPER_FIXED_GAIN=737/3840000000000 relative to b_base.
NEW_LEAN_ENDPOINT=NONE; VERIFIED_ETA=NONE; RH/FINITE_AC/WHEEL_RH=OPEN.
NEXT=accepted full-return formalization; independent review of IRR2;
     do not repeat unchanged baseline scans or promote model modes to primes.
```

Checkpoint publication was committed at `9b3104dbedb1418e9f33f4e5a5b92b74ab17d24e`, blob `6ac92ef6450b4ae47629d3636229bbf13ea0b319`, and read back identically. Final research execution is complete; final publication is recorded only after immutable commit/readback. Direct git transport failed with CONNECT HTTP 403, so authenticated connector reads and own-report writes were used. No local Lean, main push, proof feature branch, PR/issue change, merge, auto-merge, workflow rerun, schedule change or agent launch occurred.


## Material Source And Continuity Ledger

All main entries below are pinned to `f7947bee036c4dddb0c36fc9f53ab46b4fa90995`; each listed hash is its actual Git blob SHA, not a report's inferred source identifier. The source-map declarations are read at their stated conditional scope. Main dependency DAG prose still mentioning old PR states is not used as current status authority.

| Main source | Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/AGENTS.md) | `c9c89f01b90b526de9f3e8ea92478e36504711b6` |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/CURRENT_PROOF_CONTRACT.md) | `95566e37c8eaeb99ee680660df4f9d2e06ea5038` |
| [docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md) | `e922d4ba9362a1ae196af8f6de88f7417f92087c` |
| [docs/COORDINATE_ATLAS.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/COORDINATE_ATLAS.md) | `cd0419d00a37739fe5a292f5cb738e33213949d5` |
| [docs/PROOF_DEPENDENCY_DAG.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/PROOF_DEPENDENCY_DAG.md) | `eee764cefe70035a9f6c7df26ad787fbfd0fb233` |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919WindowErrorClosure.lean) | `f629db1b2b65d6ec042ac9432397d4b6316200c6` |
| [research/oai_434/VF919PrincipalSignedRemainder.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919PrincipalSignedRemainder.lean) | `a41fee91754d5f6e5606f3f6f3dfe66031d81cbf` |
| [research/oai_434/VF919ExplicitSquareBlockPacking.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | `32999039fdeea99c58a070c1c4ee9c140720dd44` |
| [research/oai_434/VF919ExplicitFixedSourceSlotCount.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) | `bad5aab0a60e96d19e7c9550cd7c0a072288bc0f` |
| [research/oai_434/VF919TotalMassEndpoint.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919TotalMassEndpoint.lean) | `827bb952c4d4311d75fd03a2470799dc10b0f7e7` |
| [research/oai_434/VF919TotalMassLowPhysical.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919TotalMassLowPhysical.lean) | `3fa845ae607f64137e01e0e2ff201d244885cfea` |
| [research/oai_434/VF919TiltedHighCentral.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919TiltedHighCentral.lean) | `6f75563d84161a023e4750df69ad0def460c0513` |
| [research/oai_434/VF919TiltedHighPrincipal.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919TiltedHighPrincipal.lean) | `e123ffa5903a62f6249aafef7a093dc6a7e3eb09` |
| [research/oai_434/VF919TiltedHighTails.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919TiltedHighTails.lean) | `6ae8ea83aca3d3f8ba8d65d42f2a6a4428e6b84f` |
| [research/oai_434/VF919TiltedHighTransport.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919TiltedHighTransport.lean) | `50c46fb1c5629865c3b7a6546ed3d9418fff1391` |
| [research/oai_434/VF919TiltedHighAssembly.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919TiltedHighAssembly.lean) | `883141e0af896d4132bfc4ffa076e2d265ece5c9` |
| [research/oai_434/VF919NativeSourceMoments.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919NativeSourceMoments.lean) | `4e5326b983f5110f7138d222f7b1be71c5694dfc` |
| [research/oai_434/VF919NativeStrictMertens.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919NativeStrictMertens.lean) | `b33a4883e1ddb0551b0f11f062bce46680d87450` |
| [research/oai_434/VF919SlotAnchoredEndpoint.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919SlotAnchoredEndpoint.lean) | `b6cce722add0fc0473238523919d021b19db7a83` |
| [research/oai_434/VF919FiniteSlotReflectedGain.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919FiniteSlotReflectedGain.lean) | `a5545b5a00958b69f6fbfd79fc555a0476aa6487` |
| [research/oai_434/VF919NativeSevenEighthsReplay.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919NativeSevenEighthsReplay.lean) | `111c933a7ca15647105ce6a4d0f3cbfc3cde81f4` |
| [research/oai_434/VF919OriginalLowTupleSignedGram.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919OriginalLowTupleSignedGram.lean) | `dd2fde01ae6e2446da4e69b30f6fc80fcadb858d` |
| [research/MERTENS_EXPONENT_ENVELOPES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/MERTENS_EXPONENT_ENVELOPES.lean) | `655b896e8d5a41c9f8fc3c456eae3944a98bfefe` |
| [scripts/lean/slot_anchored/prepare_anchored.py](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/scripts/lean/slot_anchored/prepare_anchored.py) | `0bac9047afaa8e9ddc5ac246be2d0fe7d6efa725` |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | `1f17f9401a63d16227db2e2aad020b9f74bc5f4e` |
| [scripts/lean/principal_signed_remainder/Audit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/scripts/lean/principal_signed_remainder/Audit.lean) | `e30dd1e3a36b049cbf93359a7a39857651171715` |
| [.github/workflows/vf919-principal-signed-remainder.yml](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/.github/workflows/vf919-principal-signed-remainder.yml) | `5cd287ebc659ae1e61381270a13628c7e04e2d6a` |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73` |
| [research/CompleteSquareRootWheelFractionalBoundary.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/CompleteSquareRootWheelFractionalBoundary.lean) | `ecb482e52deeee5e9b3853592a3ffdace662d2ff` |
| [research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |

Upstream source is pinned to `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`. Source inspections here support the quoted original hypotheses; hosted baseline audit evidence, not a local build, supplies the compiled dependency receipt.

| Upstream source | Blob SHA |
| --- | --- |
| [Hecke/Signal.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Hecke/Signal.lean) | `9b0f1f6ff5f74c77fee06327c4936c2a9e180df5` |
| [Hecke/SignalBounds.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Hecke/SignalBounds.lean) | `8b0f3faf87c2649dfccfc7c6eb4349259ff34d7e` |
| [Hecke/ReciprocalGrowth.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Hecke/ReciprocalGrowth.lean) | `d518b9ef91a66af6c0a14711c329d0c5dd83e7ab` |
| [PrincipalSignalComparison.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/PrincipalSignalComparison.lean) | `bd252b01e2784f9ec32fe9c1e0380c4b221adc23` |
| [PrincipalSlotEstimate.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/PrincipalSlotEstimate.lean) | `f9250c7c4464f374902bbb39ebbb3487d96bea1f` |
| [Detector/PrincipalResidueActual.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/PrincipalResidueActual.lean) | `2f336d8cfb0e6ec157ad1d43099372eb61961381` |
| [Detector/PrincipalNormalizer.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/PrincipalNormalizer.lean) | `890de70fac5b637af0cb803f3d8c691df6c668b2` |

Reports retrieved at the immutable intake commit `2fa72294667a400570c057ee15b70db21d30406f`. The following are the original intake blobs, before this run's checkpoint and append. The 00/01 Coordinator mirrors share their same day's content. Retrieved does not mean every historical claim was independently re-audited.

| Date / role | Blob SHA |
| --- | --- |
| [2026-11-09 / 00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-09/00-coordinator-am.md) | `6fba43130391ad4a606aa3809c20f344d668c709` |
| [2026-11-09 / 10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-09/10-owner-payment.md) | `643e8a004d9d8e0be102b03e2f79bb3b217ae916` |
| [2026-11-09 / 20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-09/20-analytic-type-ii.md) | `d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3` |
| [2026-11-09 / 30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-09/30-finite-wheel.md) | `0624246d03b19cf76c01e186b7d868a248d896ef` |
| [2026-11-09 / 40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-09/40-prime-census.md) | `8c927cc6c323533ba1cfd369404b25aa4f9cef91` |
| [2026-11-09 / 50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-09/50-adversarial-referee.md) | `a5d0192eb31c0efb3767187a7752f1a0d07f8534` |
| [2026-11-09 / 60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-09/60-lean-verification.md) | `8b60c6136ac151774be2db0aee8f543f286b53aa` |
| [2026-11-10 / 00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-10/00-coordinator-am.md) | `14190fe06982de80c5904b156525e3cda15d8f03` |
| [2026-11-10 / 10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-10/10-owner-payment.md) | `84afec90414b2394a61b51df46c07b6b540e5942` |
| [2026-11-10 / 20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-10/20-analytic-type-ii.md) | `7ed3a39bec4796f4173b692064af872ea8035048` |
| [2026-11-10 / 30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-10/30-finite-wheel.md) | `62406503a1ddbbf9330abcdc4cf761f7fbf05795` |
| [2026-11-10 / 40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-10/40-prime-census.md) | `a3cfa56072f3893dbf92a18956e1794236bde057` |
| [2026-11-10 / 50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-10/50-adversarial-referee.md) | `988a4a74e40a48d8d4c868c03263e66c129a6f1a` |
| [2026-11-10 / 60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/2026-11-10/60-lean-verification.md) | `d2f8fd346b7aaab57f3bd3676ed7b1d8c8abb3f8` |

[External handoffs](https://github.com/OVVO-Financial/RH_Lean/blob/2fa72294667a400570c057ee15b70db21d30406f/research/agent_reports/EXTERNAL_HANDOFFS.md): blob `038018145c0fddb2f6306c0712373adf9cd1ea52`; no entry after October 18. Prior scopes are preserved, not silently reclassified.

Final prepublication refresh at 2026-11-10 20:35 EST: main remains `f7947bee036c4dddb0c36fc9f53ab46b4fa90995`; agent-reports is exactly this run's checkpoint `9b3104dbedb1418e9f33f4e5a5b92b74ab17d24e`, so no other report or inbox changed since intake. Open/draft PR collection is empty. #1126/#1127/#1128 metadata independently confirms MERGED; no unrelated workflow is used to certify the new paper endpoint.

## Reproduction Appendix

Run the following Python with the standard library. It uses exact rational complex arithmetic; JSON decimal displays are diagnostic only. The count 1,236 is 240 local cases + 960 complete-tail checks + 24 critical multi-slot tests + 12 numerical budget margins.

### Exact Response And Budget Checker

```python
from fractions import Fraction as F
from itertools import product
from math import comb
import json


class G:
    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)
    def __add__(self, x):
        x = x if isinstance(x, G) else G(x)
        return G(self.a + x.a, self.b + x.b)
    __radd__ = __add__
    def __neg__(self):
        return G(-self.a, -self.b)
    def __sub__(self, x):
        return self + -as_g(x)
    def __rsub__(self, x):
        return as_g(x) + -self
    def __mul__(self, x):
        x = as_g(x)
        return G(self.a*x.a-self.b*x.b, self.a*x.b+self.b*x.a)
    __rmul__ = __mul__
    def norm2(self):
        return self.a*self.a+self.b*self.b
    def __truediv__(self, x):
        x = as_g(x)
        return self*G(x.a/x.norm2(), -x.b/x.norm2())
    def __rtruediv__(self, x):
        return as_g(x)/self
    def __pow__(self, n):
        v = G(1)
        for _ in range(n):
            v = v*self
        return v
    def __eq__(self, x):
        x = as_g(x)
        return self.a == x.a and self.b == x.b


def as_g(x):
    return x if isinstance(x, G) else G(x)


def mul_truncated(a, b, stop):
    out = [F(0)]*stop
    for i, v in enumerate(a):
        for j, w in enumerate(b[:stop-i]):
            out[i+j] += v*w
    return out


phases = [G(1), G(-1), G(0, 1), G(F(3, 5), F(4, 5))]
local_count = tail_count = 0
for n, eta, phase, A in product([3, 4, 6], phases, phases, [G(0)]+phases):
    Q, z = n**8, phase*F(1, n**7)
    q = F(1, Q)
    D, R = eta*z, A*Q**3*z**6
    B, K, V, W0 = 1/D, (1-q)*D, G(q), G(q)
    marked = ((R*(1-q)-K*V)/(1-V)-D+W0*R)/(1-R)
    correction = (1-V*W0+(1-V)*(1-W0)*marked)/(1-D)
    replacement = ((B-q)*(1-V)*(1-W0)*marked-q*(1-V*W0))/(1-D)
    symbol = -replacement/correction
    H, W = q*R+(1-q)*D, B*R
    assert symbol == q+(1-q)*(1-W)/(1-H)
    assert (symbol-(1+D)).norm2() <= F(144, n**22)
    local_count += 1
    for cut in [0, 1, 2, 4]:
        literal = q+(1-q)*(1-W)*sum((H**k for k in range(cut+1)), G())
        expanded = G(1)
        for r in range(cut+1):
            for b in range(cut-r+1):
                for d in [0, 1]:
                    if r+b+d == 0:
                        continue
                    coef = (-1)**d*comb(r+b, r)*(1-q)**(b+1)
                    eta_power = eta**b if d == 0 else eta**b/eta
                    expanded += coef*A**(r+d)*eta_power*Q**(2*r+3*d)*z**(6*r+b+5*d)
        assert literal == expanded
        assert symbol-literal == (1-q)*(1-W)*H**(cut+1)/(1-H)
        majorant_h = F(1, n**26)+(1-q)*F(1, n**7)
        majorant_w = F(1, n**11)
        majorant_tail = (1-q)*(1+majorant_w)*majorant_h**(cut+1)/(1-majorant_h)
        assert (symbol-literal).norm2() <= majorant_tail**2
        tail_count += 1

# At theta=3/5, choose Q_j=B^(5e_j), Z=B^(30 sum e_j).
# The rational generating function below retains every delay that can see x>1.
critical_count = 0
samples = []
for weights in [(1, 2), (1, 2, 3), (1, 2, 3, 4)]:
    N, E = len(weights), sum(weights)
    stop = 6*E
    for base in [3, 5, 11, 31]:
        complete = [F(1)]+[F(0)]*(stop-1)
        ideal = [F(1)]+[F(0)]*(stop-1)
        absolute_product = F(1)
        for e in weights:
            q = F(1, base**(5*e))
            d = (1-q)*F(1, base**(3*e))
            g = F(1, base**(8*e))
            inv = [F(0)]*stop
            inv[0] = 1
            for j in range(1, stop):
                inv[j] = (d*inv[j-e] if j >= e else 0)+(g*inv[j-6*e] if j >= 6*e else 0)
            slot = [(1-q)*(inv[j]-(inv[j-5*e] if j >= 5*e else 0)) for j in range(stop)]
            slot[0] += q
            complete = mul_truncated(complete, slot, stop)
            pure = [F(0)]*stop
            pure[0], pure[5*e] = 1, -1
            ideal = mul_truncated(ideal, pure, stop)
            r = d+g
            delta = q+2*(1-q)*r/(1-r)
            absolute_product *= 2+delta
        error_mass = absolute_product-2**N
        for degree in range(1, N):
            test = [(30*E-5*j)**degree for j in range(stop)]
            pure_response = sum(a*b for a, b in zip(ideal, test))
            full_response = sum(a*b for a, b in zip(complete, test))
            assert pure_response == 0
            assert abs(full_response) <= (30*E)**degree*error_mass
            critical_count += 1
            if weights == (1, 2) and base in [3, 11, 31]:
                samples.append({'weights': weights, 'base': base,
                                'response_over_log_base': float(full_response),
                                'majorant': float((30*E)**degree*error_mass)})

t = F(1, 10**8)
h, e, nu, s0 = t/24, t/2000, t/8, F(49, 881280)
nonfloor_cost = F(13, 16)*(159*e+9*t)+2*t+3*t+26*e+t+t+t/6+3*t
margins = {
    'small_tail': F(63, 800)-h-8*e-nu,
    'large_tail': F(19, 16)-h-nu,
    'principal': F(17, 48000)-h-nu,
    'nonfloor': s0-F(1, 10**6)-h-t/4,
    'floor': F(7, 1200)-(2*t+26*e+t+t+t/6+nu+h),
    'count': F(1, 32)-(159*e+9*t),
    'height_paid_nonfloor': F(49, 440640)-nonfloor_cost-s0,
    'coarse_nonfloor_cost': 18*t-nonfloor_cost,
    'conductor': F(7, 8)-F(13, 16)-3*t,
    'low_tilt': F(1, 960)-h,
    'correction_domain': F(7, 8)-h-F(21, 25),
    'response_domain': F(7, 8)-h-F(3, 5),
}
assert all(v > 0 for v in margins.values())
assert 24*h == t  # Only the nonphysical closed-box endpoint is tested here.
assert t/24-F(21, 6400)*t == F(737, 19200)*t
assert F(737, 38400)*t == F(737, 3840000000000)
print(json.dumps({'local_cases': local_count, 'full_tail_cases': tail_count,
                  'complete_critical_tests': critical_count, 'budget_tests': len(margins),
                  'critical_samples_diagnostic_only': samples,
                  'budget_margins_exact': {k: str(v) for k, v in margins.items()},
                  'status': 'PASS'}, indent=2))
```

Executed output, exit 0:

```json
{
  "local_cases": 240,
  "full_tail_cases": 960,
  "complete_critical_tests": 24,
  "budget_tests": 12,
  "critical_samples_diagnostic_only": [
    {
      "weights": [
        1,
        2
      ],
      "base": 3,
      "response_over_log_base": 0.20903856979536073,
      "majorant": 15.04754133422371
    },
    {
      "weights": [
        1,
        2
      ],
      "base": 11,
      "response_over_log_base": 0.00031053192228277225,
      "majorant": 0.27199604051603443
    },
    {
      "weights": [
        1,
        2
      ],
      "base": 31,
      "response_over_log_base": 1.7464892508679497e-06,
      "majorant": 0.01209128466673755
    }
  ],
  "budget_margins_exact": {
    "small_tail": "369140617/4687500000",
    "large_tail": "712499999/600000000",
    "principal": "70833/200000000",
    "nonfloor": "60145187/1101600000000",
    "floor": "583328987/100000000000",
    "count": "6249981841/200000000000",
    "height_paid_nonfloor": "244226378909/4406400000000000",
    "coarse_nonfloor_cost": "42551/9600000000000",
    "conductor": "6249997/100000000",
    "low_tilt": "833333/800000000",
    "correction_domain": "83999999/2400000000",
    "response_domain": "659999999/2400000000"
  },
  "status": "PASS"
}
```

### Genuine Gcd-Source Checker

Compile with `g++ -O3 -std=c++17 gcd_source_audit.cpp -o gcd_source_audit`, then execute `./gcd_source_audit`. Both commands completed successfully. The ordered pair sum is computed by doubling off-diagonal unordered pairs, retaining each diagonal once. The complete range fits the displayed integer types; quadratic accumulation uses 128 bits.

```cpp
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

int main() {
    const int limit = 2000, maxn = limit*limit;
    std::vector<int> mu(maxn+1, 1), prime;
    std::vector<bool> composite(maxn+1, false);
    mu[0] = 0;
    for (int n=2; n<=maxn; ++n) {
        if (!composite[n]) { prime.push_back(n); mu[n] = -1; }
        for (int p: prime) {
            if (std::int64_t(n)*p > maxn) break;
            composite[n*p] = true;
            if (n%p == 0) { mu[n*p] = 0; break; }
            mu[n*p] = -mu[n];
        }
    }
    std::vector<int> mertens(maxn+1);
    for (int n=1; n<=maxn; ++n) mertens[n] = mertens[n-1]+mu[n];
    std::vector<std::uint16_t> gcd(limit*limit);
    for (int a=1; a<limit; ++a)
        for (int b=a; b<limit; ++b) gcd[a*limit+b] = std::gcd(a,b);
    int failures = 0, first_positive_rule = 0, first_binary_rule = 0;
    for (int R=2; R<=limit; ++R) {
        const int X = R*R-1;
        std::vector<std::int64_t> C(R, 0);
        for (int a=1; a<R; ++a) if (mu[a])
            for (int b=a; b<R; ++b) if (mu[b])
                C[gcd[a*limit+b]] += std::int64_t(mu[a]*mu[b])*(a==b?1:2)*(X/(a*b));
        const auto Q = std::accumulate(C.begin(), C.end(), std::int64_t(0));
        if (Q != 2*mertens[R-1]-mertens[X]) return 2;
        __int128 diagonal = 0;
        for (int g=1; g<R; ++g) diagonal += __int128(C[g])*C[g];
        if (!first_positive_rule)
            for (int g=2; g<R; ++g) if (C[g]<0) { first_positive_rule=R; break; }
        const auto binary = 2*C[1]*(Q-C[1]);
        if (!first_binary_rule && binary>0) first_binary_rule=R;
        if (__int128(Q)*Q > diagonal) {
            ++failures;
            std::cout << "GC5_FAIL R=" << R << " Q=" << Q
                      << " fine_diagonal=" << std::int64_t(diagonal) << '\n';
        }
        if (R==15 || R==17 || R==549) {
            std::cout << "WITNESS R=" << R << " Q=" << Q << " C1=" << C[1]
                      << " C2=" << C[2] << " shared=" << Q-C[1]
                      << " binary_cross=" << binary
                      << " fine_cross=" << std::int64_t(__int128(Q)*Q-diagonal) << '\n';
        }
    }
    std::cout << "ROOTS=1999 IDENTITY_FAILURES=0 GC5_FAILURES=" << failures
              << " FIRST_H_POS=" << first_positive_rule
              << " FIRST_H_SPLIT=" << first_binary_rule << '\n';
}
```

Executed output, exit 0:

```text
WITNESS R=15 Q=-7 C1=-12 C2=-6 shared=5 binary_cross=-120 fine_cross=-174
WITNESS R=17 Q=5 C1=4 C2=-6 shared=1 binary_cross=8 fine_cross=-148
WITNESS R=549 Q=-186 C1=-28 C2=70 shared=-158 binary_cross=8848 fine_cross=-178880
ROOTS=1999 IDENTITY_FAILURES=0 GC5_FAILURES=0 FIRST_H_POS=15 FIRST_H_SPLIT=17
```



## Verified Publication Receipt

STATUS=COMPLETED for this scheduled research execution, 2026-11-10 20:37 EST.

- Substantive final report committed to the owned daily path on agent-reports at `ce3f4087703d1ea869af4564481110d6ff62d8d5`, blob `8a3a2b0c1b72f3ced544198632efcb320cabdcd3`.
- Immutable re-fetch matched all 178,488 characters exactly and retained the previous 115,329-character report/checkpoint as an unchanged byte prefix (all content is UTF-8; comparison used the complete decoded text).
- Early checkpoint `9b3104dbedb1418e9f33f4e5a5b92b74ab17d24e` was likewise read back before substantive work continued.
- This receipt records the already verified substantive commit; it does not claim its own future commit hash in advance.
- Publication is not formal mathematical certification. Accepted MD/IR results remain PAPER_PROOF; new IRR2 remains PAPER_PROOF/SELF_AUDIT pending independent review; IRR3/IRR4 remain FINITE_COMPUTATION. `VERIFIED_ETA=NONE`; canonical RH, finite AC and wheel-RH estimates remain OPEN.
