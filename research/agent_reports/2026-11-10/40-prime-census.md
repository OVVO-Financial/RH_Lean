# RH | Prime Census Laboratory - 2026-11-10

## Early Preregistration - 20261110-census-1/UC

Execution: IN_PROGRESS. Trigger: scheduled 2026-11-10 03:11:02 EST; America/New_York. RUN_ID_UNAVAILABLE. Registration timestamp: 2026-11-10 08:20:08 UTC. No experiment in this run has yet executed.

finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.
Main source commit: 7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9.
Reporting intake head: a75d50bba39133dc7351d4e6463d0e4cc945dc5b.
AGENTS blob 6695522a45d67fd1e80a7cff1f98d909405036e2; proof-contract blob 95566e37c8eaeb99ee680660df4f9d2e06ea5038; current directive e505f35522b675c6b5b263eac73618d717346973; complete-wheel source ecb482e52deeee5e9b3853592a3ffdace662d2ff; prefix source c499ca7bd7d90fb32f9cd99d652961ea023bed58.

### Current Objective

For integer R>=2, X=R^2-1, y=R-1, F_R=sum_(d|P_y)mu(d)fract(X/d), D_R=X*delta(y)+pi(y)-1-li(X). The certified identity F_R-D_R=li(X)-pi(X) does not prove the OPEN uniform bound |F_R-D_R|<=C R log R. The canonical VFCanonicalSquareVonKochStatement and its explicit ClassicalVonKochRHCriterion interface remain unchanged. Virtual divisors cancel termwise against Euler mass before physical truncation; d=X and q=R when prime remain admitted.

### Continuity

Today Owner HM (blob 2bed3da8ed4ddd49c0708378a1c3da5b4883cb54), Analytic HF (d8337353a94b465f53a0c6a65ad46aac1dc1927e), and Wheel PC (79ff39e0f79a30f4cf1657b22f96ebe49de4d717) are AVAILABLE and retrieved. Coordinator, Referee and Lean TODAY=PENDING. YESTERDAY=CARRY_FORWARD for all seven roles at their actual evidence scopes. Own prior NC pairing work is not rerun. HM's common saturated-cutoff reciprocal profile and PC's independently optimized saturated fibres leave UNSATURATED prefixes expressly outside their scope. This is the changed hypothesis, not a larger repeat of those scans.

November 9 report blobs: Coordinator 6fba43130391ad4a606aa3809c20f344d668c709 (AM/PM identical), Owner 643e8a004d9d8e0be102b03e2f79bb3b217ae916, Analytic d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3, Wheel 0624246d03b19cf76c01e186b7d868a248d896ef, Census 8c927cc6c323533ba1cfd369404b25aa4f9cef91, Referee a5d0192eb31c0efb3767187a7752f1a0d07f8534, Lean 8b60c6136ac151774be2db0aee8f543f286b53aa. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no newer current-campaign handoff; its source, first-bad and target-equivalence safeguards remain applicable.

Only open PR at intake: #1127, non-draft, head 866b3d2121309cdd854f9d64e2a6adbbc708ef9b. Main includes merges #1125 and #1126; no new formal certification is inferred from merge status. This experiment does not need #1127 or its sharper density threshold.

### Exact Registered Experiment

For R>=8 set h=floor((R-1)/2), Q={prime q:R<=q<2R}, x_q=X/q, t_q=floor(x_q), r_q=fract(x_q), w_p=delta(p-1)/p, W=delta(h)-delta(R-1). Preserve the actual row

T_q(z)=sum_(prime p<=z or R/2<=p<R) [N_p(t_q)-x_q*w_p],
N_p(t)=#{2<=a<=t:leastPrime(a)=p}.

Extend ONLY the tested choice range to every integer 2<=z<=h; do not assume z^2>=R. Count all surviving composite cofactors C_q(z)=#{2<=a<=t_q: a composite, leastPrime(a)>z}, including squares. Test the proposed corrected reconstruction
T_q(z)=[delta(z)-W]x_q+pi(z)-pi(h)-1-r_q-C_q(z).

Competing hypotheses and rejection conditions:
1. Saturated minimization is already globally optimal among all prefix cutoffs. Refute if a genuine unsaturated row has signed minimum or absolute minimum strictly below its saturated optimum, where saturation means ceil(sqrt R)<=z<=h. Report these as TWO distinct claims.
2. HM's transverse estimate remains valid without saturation. Let P be exact orthogonal projection onto span{1,(x_q)}. Test ||(I-P)T(z)||^2<=#Q/4. One strict exact rational violation refutes this extension, not HM under its stated hypotheses.
3. Surviving rough composites, rather than freely adjustable prime signs, are the missing variable. Trace any failure to the vector C_q(z), retain its mixed term with r_q, and discriminate bounded rounding from deterministic non-affine prime-count curvature. Further conjectures must be registered before held-out testing.

Discovery roots: every R=8..256, all cutoffs 2..h. Held-out roots, fixed now: 263,389,521,1031,1543,2053,4099,8191. No threshold or constant will be fitted to maxima. Stop scaling once a decisive falsifier and structural explanation are independently checked.

Use a least-factor sieve plus exact integer/Fraction arithmetic; independently reconstruct small witnesses and at least selected held-out data using trial factorization or a structurally distinct compiled integer implementation. Check small complete divisor cubes R=2,3,8..16, physical/virtual reunification, q=R, squareful cofactors and d=X. Larger roots use the certified compensated physical floor form and symbolic virtual reciprocal correction, not the exponential complete cube. High-precision li-based normalized discrepancy is diagnostic only, not an interval certificate or an all-scale bound. Restore the full selected/unselected/outside-mask source and all cross terms before interpreting any global consequence.

### Next Action And Scope

Implement the registered exact experiment, inspect smallest failures and strongest held-out exceptions, and develop a precise corrected theorem or scoped impossibility result. New proofs will be PAPER_PROOF / self-audit pending independent review; exact checks FINITE_COMPUTATION; specific false extensions REFUTED. No Lean source or other agent report will change. No local Lean, PR/branch/issue/workflow mutation, merge, schedule change, or agent launch is authorized or planned.

## Surviving Cofactors Break The Transverse Bound - 20261110-census-1/UC

### A. Most Important Mathematical Discovery

**The saturation hypothesis is essential. Once composite cofactors survive a smaller owner cutoff, the source acquires an additional transverse component. It is not just bounded fractional rounding.** The best possible affine fit in the constant and reciprocal-prime directions already violates the proposed m/4 energy bound at R=29, z=2. The exact excess is positive, and an independently reconstructed implementation agrees.

The mechanism also has an all-scale explanation. For every FIXED small cutoff z, the projected energy has the paper asymptotic

```text
||(I-Pi_R)T_R(z)||^2 ~ kappa * R^3/(log R)^5,
kappa = min_(alpha,beta in Real)
          integral_1^2 [(log u)/u-alpha-beta/u]^2 du > 0.
```

Here Pi_R is Euclidean orthogonal projection onto span{1,(1/q)} over the genuine primes q in [R,2R). The additional mode is the curvature (log u)/u, u=q/R. It follows from the classical prime-counting expansion after the first two affine terms are removed. It is not a model of independent signs, a new zero-free region, or an RH-strength input.

| Claim | Result | Evidence |
| --- | --- | --- |
| 20261110-census-1/UC1 | Exact unsaturated correction by every surviving rough composite, with all mixed terms retained | PAPER_PROOF; independently checked finite reconstruction |
| UC2 | Three explicit counterexamples to extending the saturated results outside their hypotheses | REFUTED extensions; exact finite certificates |
| UC3 | Positive fixed-cutoff transverse-curvature asymptotic, also for a specified slowly growing wheel | PAPER_PROOF; SELF_AUDIT; independent mathematical review pending |
| UC4 | 870,319 exact source rows, independent trial-factor audit, complete source and numerical diagnostics | FINITE_COMPUTATION; finite scope only |

HM and PC under their actual saturation hypotheses are NOT refuted. NEW_GLOBAL_ENDPOINT_GAIN=NONE. The complete finite-wheel bound and RH remain open. UC3 is not formalized and has not received an independently executing Referee's acceptance.

### B. Current Authoritative Objective

Main was refreshed at the start: `7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9`. The governing acknowledgment is `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`. The original current target remains

```text
X=R^2-1, y=R-1, P_y=product_(prime p<=y)p,
delta(y)=product_(prime p<=y)(1-1/p),
F_R=sum_(d|P_y)mu(d)*fract(X/d),
D_R=X*delta(y)+pi(y)-1-li(X),
Z_R=F_R-D_R=li(X)-pi(X).

OPEN: exists ONE C>=0, forall integer R>=2, |Z_R|<=C R log R.
```

The canonical `VFCanonicalSquareVonKochStatement` is unchanged. Its terminal `riemannHypothesis_of_vfCanonicalSquare` still explicitly takes `ClassicalVonKochRHCriterion`; this run does not supply that interface or its arithmetic premise. No historical K_R, Mertens budget, or original #915 NNS covariance is replaced by the present Euclidean fibre statistic.

Material source blobs actually retrieved:

| Path | Blob |
| --- | --- |
| AGENTS.md | 6695522a45d67fd1e80a7cff1f98d909405036e2 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_SEVEN_AGENT_FINITE_WHEEL_BOUNDARY_20261108.md | e505f35522b675c6b5b263eac73618d717346973 |
| docs/DYNAMIC_RESEARCH_AGENTS.md | e8d913ff9663bb5163eaf0eddca9f76e0508a7ef |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| research/CompleteWheelRootAdmission.lean | a412632c1028d7728cd8d87ee6e5ac365377d338 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

The first source defines `finiteWheelFract` and `finiteWheelSquareDeterministic`, and proves `finiteWheel_squareFractional_centered_eq_reference_sub_pi` for an arbitrary real reference. The prefix source defines the actual positive survivor count and finite Euler product. Its existing `abs_vfMidPrefixWheelCounting_sub_density_mul_le` supplies the complete-face bound used in UC3. These statements were inspected, not inferred from report prose.

Historical #1122 job 128980092032 was read. It compiled the complete-wheel module with Lean 4.34.1 and printed the two relevant terminal axiom lists `[propext, Classical.choice, Quot.sound]`. Its checkout was synthetic merge `1e3c182076a6e1a23ef132c41a78b0f26adab507`, containing proof head `c53e9cf234500aea2605fd2557e638995f380407`, NOT today's main. Re-fetching the module at that tested merge returned the identical current source blob. This supports reuse of the existing identity evidence; it is not a new current-main build or certification of UC.

Only #1127 was open at intake, non-draft at `866b3d2121309cdd854f9d64e2a6adbbc708ef9b`. Main's recent accepted changes include #1125 and the #1126 conditional amplification consumers. Their merge metadata does not prove their premises. The present work needs neither #1127's positivity strengthening nor a new formal claim about #1125. No local Lean was run.

### C. Competing Hypotheses

The existing HM/PC work is credited, not reproduced as novelty. HM restricts a COMMON saturated cutoff to an affine reciprocal-prime family; PC allows DIFFERENT saturated cutoffs and proves a nonzero optimized cost. Both explicitly leave smaller cutoffs outside their theorems.

The preregistered extensions were distinct:

1. For each R,q, minimizing the signed row over all 2<=z<=h gives the same answer as restricting to ceil(sqrt R)<=z<=h.
2. The analogous equality holds for the absolute row minimum.
3. For all 2<=z<=h, even the BEST constant/reciprocal fit leaves squared residual at most m/4.

An exact strict inequality refutes the corresponding extension. A surviving composite vector, rather than newly independent signs, was the competing explanation. The curvature law was formulated AFTER discovery but BEFORE the registered held-out run; the preserved registration below makes that timing explicit. Its proof is independent of the finite samples.

### D. Experimental Design And Exact Carrier

For integer R>=8 put

```text
X=R^2-1, h=floor((R-1)/2), a=ceil(sqrt R),
Q={prime q:R<=q<2R}, m=#Q,
x_q=X/q, t_q=floor(x_q), r_q=fract(x_q),
w_p=delta(p-1)/p, W=delta(h)-delta(R-1), H=pi(h),
N_p(t)=#{integers 2<=n<=t: leastPrime(n)=p},
T_q(z)=sum_(prime p<=z or R/2<=p<R)[N_p(t_q)-x_q*w_p].
```

The new range is ALL integers 2<=z<=h. Physical cofactors include squares and higher prime multiplicities. Each admitted integer n*q has n<R<=q, so it belongs to at most one Q-fibre; the unit cofactor n=1 is excluded from N_p and must not be silently charged as a composite. q=R is included when prime. The q mask is not an added wheel prime: the original signed divisor packet uses mu(d), not mu(q*d).

Define the new observed variable

```text
C_q(z)=#{composite n<=t_q: leastPrime(n)>z}.
```

Discovery covered every R=8..256. The predeclared held-out roots were 263,389,521,1031,1543,2053,4099,8191. Every integer cutoff is represented exactly: the row is constant between consecutive prime cutoffs, and the geometric saturation boundary and terminal state were explicitly included. No random seeds, probabilistic primality, floating sign decisions or fitted constants were used.

Primary method: least-prime-factor sieve, integer common denominators for all Euler references, and an integer Gram determinant for projection. Independent method: trial factorization, direct physical owner counts, rational normal equations, and complete divisor enumeration at small roots. Both are this author's implementations, NOT separate specialist review. Agreement concerns actual computations and algorithms, not claimed statistical independence.

### E. Executed Results

The final exact runs returned:

```text
Discovery: 249 roots, 137647 prime-cutoff source states.
Held-out: 8 roots, 732672 source states.
Independent trial-factor audit: 257 roots, 870319 state ledgers MATCH.
Small full divisor/source/return audits: R=2,3,8,9,10,11,12,13,14,15,16 PASS.
Additional physical-floor reconstructions: R=263,521,1031 PASS.
Python syntax checks: PASS.
```

Discovery had 104 roots with a strict signed-minimum improvement, 234 with an absolute-minimum improvement, and 148 with a projected-energy violation. All eight held-out roots had absolute-minimum improvements and projected-energy violations. NONE had a signed-minimum improvement. These are different optimization questions; the latter negative result is not an all-scale optimality theorem.

Let E_perp=||(I-Pi_R)T(z)||^2. Displayed decimals below are rounded views of exact rational computations; every threshold decision was exact.

| R | m | z giving largest tested E_perp | E_perp/(m/4) there | E_perp at z=2 |
| --- | --- | --- | --- | --- |
| 263 | 44 | 2 | 1.557620 | 17.133816 |
| 389 | 61 | 5 | 1.607641 | 20.824443 |
| 521 | 78 | 2 | 1.639736 | 31.974859 |
| 1031 | 138 | 2 | 4.203319 | 145.014520 |
| 1543 | 199 | 2 | 5.849047 | 290.990064 |
| 2053 | 256 | 3 | 7.252358 | 453.622595 |
| 4099 | 464 | 7 | 12.835376 | 1394.886406 |
| 8191 | 873 | 61 | 23.474163 | 3431.185885 |

The discovery maximum ratio was approximately 2.943237 at R=163,z=3. A larger search is not needed to refute the universal extension.

At R=263,521,1031, independent summation over EVERY nonzero physical squarefree divisor with greatest prime factor <=R-1 gave respectively 6815,23664,82859 for the complete signed floor total. Their physical nonzero divisor counts were 10109,40729,162729. Each total equals 1+pi(X)-pi(R-1), checked against a separate prime sieve. The symbolic virtual reciprocal contribution remains

```text
X*[delta(R-1)-sum_(d<=X, d|P_(R-1))mu(d)/d].
```

It cancels termwise in F-X*delta, not by deleting the virtual terms from F. At R=8, physical fractional mass 3/5 plus virtual correction -6/5 is the full F=-3/5. At R=14, d=X=195 has mu(d)=-1 and contributes -1 to the signed floor sum, despite fractional part zero.

The requested normalized full discrepancy was also monitored, separately as NON-CERTIFIED 80/160-decimal diagnostics. Exact endpoint prime counts were sieved up to 67,092,480; no bound is inferred from these values.

| R | Exact pi(R^2-1) | Approximate abs(li(X)-pi(X))/(R log R) |
| --- | --- | --- |
| 29 | 146 | 0.083548756 |
| 263 | 6869 | 0.028439609 |
| 521 | 23760 | 0.016329046 |
| 1031 | 83030 | 0.020214698 |
| 2053 | 297297 | 0.010295776 |
| 4099 | 1079376 | 0.009485611 |
| 8191 | 3956871 | 0.007714978 |

All tested normalized values agreed across precision levels to better than 1e-70. This is a stability check, not validated interval arithmetic. Principal-value li was used, with its Euler-gamma constant retained; Li_2 was not silently substituted.

### F. Exceptional Cases And Minimal Certificates

**UC2a, signed minimum:** R=8, q=11, unrestricted z=2 gives -51/110, below the saturated minimum -23/55 at z=3. This is the first root in the stated R>=8 domain. Importantly C_q(2)=0: this failure reflects an unnecessarily restrictive geometric cutoff, NOT a surviving composite.

**UC2b, absolute minimum:** R=10, q=11, t_q=9. The unrestricted minimum is 39/70 at z=2, versus 37/35 at the only saturated state z=4. Here the omitted cofactor is genuinely squareful: C_q(2)=1, represented by n=9. The selected owners {2,5,7} have counts 4,1,1 and exact weights 1/2,1/15,4/105, so their rows sum to

```text
6 - 9*(1/2+1/15+4/105) = 39/70.
```

Adding owner 3 contributes 2-9/6=1/2, giving 37/35. This keeps both physical cofactors 3 and 9, with their correct multiplicity. The displayed final calculation, not an unsigned ancestry count, is the certificate.

**UC2c, weakest projected extension:** the smallest violation for R>=8, 2<=z<=h is R=29,z=2. Its hand-auditable carrier is

```text
X=840; Q=(29,31,37,41,43,47,53); m=7;
t=(28,27,22,20,19,17,15);
C(2)=(5,5,3,2,2,2,2).
```

The rough composites below 28 are 9,15,21,25,27, including BOTH squares and the cube 27. For z=2 there is also an especially simple exact representation:

```text
T_q(2)=pi(t_q)-H-x_q*W-fract(X/(2q)).
```

The reference H+x_q*W lies entirely in the projected-out space. Projection of the seven entries pi(t_q)-fract(X/(2q)) yields

```text
E_perp = 13204382152870676585 / 7298618577576669768
       = 7/4 + 431799642111504491 / 7298618577576669768
       > 7/4.
```

This refutes even the version allowing the BEST fitted reciprocal slope, not merely the prescribed HM coefficient. It does not assert that R=29 is the first failure of a DIFFERENT fixed-slope formula.

For a forensic decomposition put r_perp=(I-Pi)r and C_perp=(I-Pi)C. Independent rational normal equations give

```text
||r_perp||^2 = 3659936844782588825 / 7298618577576669768,
||C_perp||^2 = 1202843690975460748 / 912327322197083721,
2<r_perp,C_perp> = -9788027464449778 / 912327322197083721.
```

Their sum is exactly E_perp. The negative mixed term is retained; it is insufficient to restore m/4. Ordinary rounding alone still satisfies its bound.

### G. Hidden Variable And Corrected Saturation

UC1 holds for EVERY R>=8 and EVERY 2<=z<=h:

```text
T_q(z)=[delta(z)-W]x_q+pi(z)-H-1-r_q-C_q(z).       (UC.1)
```

Proof: of the t_q-1 integers from 2 to t_q, the ones not removed by owners <=z consist precisely of primes greater than z and the C_q(z) rough composites. Thus the lower-owner count is t_q-1-pi(t_q)+pi(z)-C_q(z). The upper-owner count is pi(t_q)-H, since two upper-size prime factors would exceed t_q<R. Their reference masses are 1-delta(z) and W. Adding the counts and subtracting the references gives (UC.1).

Consequently the exact projected source is

```text
(I-Pi_R)T(z)=-(I-Pi_R)[r+C(z)],
E_perp=||r_perp||^2+||C_perp||^2+2<r_perp,C_perp>. (UC.2)
```

There is a sharper interpretation of the geometric saturation requirement. For each q, C_q(z)=0 exactly when the square of the smallest prime greater than z exceeds t_q. Indeed, the smallest possible rough composite is that prime squared. For simultaneous saturation replace t_q by max_Q t_q. This elementary criterion can admit states with z^2<R. It explains the R=8 signed witness and why some held-out absolute-minimum improvements still have C=0. For example R=263,q=461,z=13 has t_q=150 and no surviving rough composite. Therefore NOT EVERY optimization improvement is evidence for an extra transverse mode.

This exact carrier criterion is a proof-led interpretation, not a newly preregistered held-out discovery. UC2c and the R=10 squareful witness genuinely involve surviving composites. No claim is made that all unrestricted optimizers use them.

### H. Mathematical Interpretation

Saturated rows remove all composite cofactors, allowing their prime-count terms to cancel exactly. Removing that hypothesis reintroduces a deterministic arithmetic vector C_q(z). For fixed small wheels, its projected part contains prime-count curvature. Fitting only constant and reciprocal directions cannot turn that curvature into bounded rounding.

This is a source-specific obstruction to promoting HM's transverse estimate to arbitrary smaller cutoffs. It does NOT rule out all unsaturated signed mechanisms, cross-fibre cancellation, or cancellation with the complete outside-mask source. It also does not turn the tiny finite improvements of absolute minima into an asymptotic escape from PC.

### I. UC3: Precise Paper Theorem And Proof

**Theorem, paper/self-audit scope.** For every FIXED integer z>=2, as R tends to infinity through integers large enough that z<=h,

```text
E_perp(R,z) / [R^3/(log R)^5] -> kappa > 0.
```

The same conclusion holds for ANY sequence of integer cutoffs 2<=z_R<=h satisfying

```text
2^pi(z_R) * (log R)^2 / R -> 0.                    (UC.3)
```

The fixed-z statement was registered before held-out execution. The growing-wheel version is a subsequent proof-led corollary with its precise uniformity condition, not an empirically fitted generalization. No onset or universal bound for unrestricted z_R is claimed.

**Independent input.** The classical PNT error is available, for example in Johnston-Yang, Corollary 1.3: an unconditional bound of the form x*(log x)^0.515*exp(-0.8274*sqrt(log x)) times a fixed constant. It is more than sufficient for pi(x)=x/log x+x/log^2 x+O(x/log^3 x). The primary paper was retrieved at https://arxiv.org/pdf/2204.01980; the standard expansion is also recorded at https://dlmf.nist.gov/27.12#E4. This is a classical input, not a new theorem claimed here. The paper's inaccessible v3 HTML URL was not used as evidence; its available v2 PDF was read.

**Step 1: retain the fixed-wheel error exactly.** Let Phi(t,z) be the positive survivor count from the original prefix module, and define

```text
epsilon_q(z)=t_q-Phi(t_q,z)-x_q*(1-delta(z)).
T_q(z)=pi(t_q)-H-x_q*W+epsilon_q(z).              (UC.4)
```

The existing complete-face bound |Phi(t,z)-delta(z)*t|<=2^pi(z), and 0<=x_q-t_q<1, imply

```text
max_Q |epsilon_q(z)| <= 2^pi(z)+1.
```

The unit is counted in Phi. No squarefree-only physical cofactor substitution occurs. For z=2 this specializes to epsilon_q=-fract(X/(2q)).

**Step 2: isolate the new mode.** Write L=log R, u=q/R in [1,2). Uniformly over that interval, x_q=R/u+O(1/R). Since pi(t_q)=pi(x_q), the classical expansion gives

```text
pi(t_q)= (R/L+R/L^2)/u + (R/L^2)*(log u)/u
         + O(R/L^3),                             (UC.5)
```

with ONE error constant independent of the sampled prime q. This follows by expanding 1/(L-log u) on the fixed compact interval. The floor contributes no extra prime count because pi(t_q)=pi(x_q) exactly. Under (UC.3), epsilon_q=o(R/L^2) uniformly. Projection removes H, x_q*W and the first term of (UC.5) EXACTLY, because span{1,x_q}=span{1,1/u}.

**Step 3: pass through the actual prime sampling measure.** Ordinary PNT gives m~R/L and, for continuous f on [1,2],

```text
(L/R)*sum_(q in Q)f(q/R) -> integral_1^2 f(u)du.
```

This follows from uniform prime-count asymptotics on a fixed proportional interval and step-function approximation; no independence of upper and lower primes is assumed. Apply it to 1,1/u,1/u^2,g,g/u,g^2, where g=(log u)/u. The empirical two-by-two Gram matrix converges to

```text
G = [[1, ell], [ell, 1/2]],  ell=log 2,
det G=1/2-ell^2>0.
```

Its inverse therefore converges. The uniform remainder in Step 2 is small in the SAME empirical norm, and orthogonal projection is a contraction. This proves the claimed energy limit, including the mixed terms between main profile and remainder.

**Step 4: strict positivity and explicit constant.** Put b=(ell^2/2,(1-ell)/2). Direct integration gives

```text
kappa = 1-ell-ell^2/2 - b^T G^(-1)b.
```

It is strictly positive because g is not in span{1,1/u}: otherwise log u would be affine in u on [1,2], contradicting its nonzero second derivative. Numerical display only: kappa is approximately 0.00015704636990096183474361712955391435. A separate Simpson quadrature of the squared residual agrees; positivity rests on the analytic argument, not numerical cancellation.

Thus E_perp/m~kappa*R^2/L^4 tends to infinity. **No fixed multiple of m can uniformly replace the transverse energy in this small-wheel regime.** This strengthens the single finite counterexample without assuming an RH-scale prime estimate.

The held-out scaled z=2 energies E_perp*L^5/R^3 were approximately 0.00505944 at R=263 and 0.000370893 at R=8191. The latter is still about 2.36 times the limiting coefficient. These data do not verify an asymptotic onset or a monotone rate. The theorem is supported by its displayed argument, not extrapolation from those values. Independent specialist review is still required.

### J. Full Return And Proof Impact

The investigated rows are a proper source, not the full centered error. For the original owners put

```text
B_R(p)=N_p(X)-X*w_p,
F_R=sum_(p<R, p prime)B_R(p),
b_Q(p)=sum_Q[N_p(t_q)-x_q*w_p],
S_Q=sum_(p<R)b_Q(p)=delta(y)*sum_Q x_q-m-sum_Q r_q,
E_z=sum_Q T_q(z), J_z=S_Q-E_z,
G_R=F_R-S_Q-D_R.

Z_R=E_z+J_z+G_R,
Z_R^2=E_z^2+J_z^2+G_R^2+2E_zJ_z+2E_zG_R+2J_zG_R.
E_z^2=sum_Q T_q(z)^2+2sum_(q<q')T_q(z)T_q'(z).
```

The original source B_R(p) also equals the complete signed fractional divisor packet. Its Euler mass is unchanged. G_R includes the actual outside-Q source and the entire deterministic centering. Physical q-fibres are disjoint because qq'>=R^2>X; neither a historical contribution nor a physical integer is multiplied by its descendant count.

These full identities and their complete squares were checked at the small-cube roots with arbitrary rational reference 355/113; the source theorem permits any real reference, so this validates the algebra without pretending li is rational. At larger roots the separate complete signed floor totals were also reconstructed.

For an arbitrary smaller cutoff E_z is NOT claimed paid by AP's saturated adaptive argument. UC3 neither bounds the constant/reciprocal modes nor pays J_z or G_R. A proof of the full bound on their unchanged signed sum remains the original RH-strength problem. No smaller sufficient RH lemma, exponent improvement, finite-A estimate, or first-bad refutation is claimed.

The useful new requirement is concrete: an unsaturated response must retain C_q(z) and its projection. In the small-wheel regime, any proposed bounded-transverse mechanism must also account for the nonzero logarithmic curvature, or exhibit a genuine signed cancellation that annihilates it with a quantified complement. Naming the complement and assuming its target-sized bound is not such a theorem.

### K. Falsification, Reproducibility And Limitations

The full cutoff domain, rivals, held-out roots, rejection rules and source-integrity checks were committed BEFORE execution at `8753a61190d7f3bae6f362612dea44403818cc02`; immutable readback matched blob `3850201a9e82ce928bbe452a22cfc2f0f84c738e`. The fixed-cutoff curvature registration preceded the held-out command at 2026-11-10 08:24:57 UTC. No post-hoc constant was used to decide a counterexample.

Final runtime was **Python 3.12.14**, observed directly; the environment description's 3.12.13 was not used as execution evidence. All final programs use only the Python standard library. No C++ execution is claimed. Algorithms are deterministic: Eratosthenes and least-factor sieves on explicit finite ranges, trial factorization, arbitrary-size integer/Fraction arithmetic, and normal equations/determinants. Complete-cube enumeration is limited to small roots; higher roots do not enumerate an exponential wheel.

The main probe took 0.599 seconds on its final discovery rerun and 20.863 seconds on held-out roots; independent verification completed in 14.399 seconds; source/Decimal diagnostics completed in 1.914 seconds. These are the programs' observed elapsed times, not hardware-normalized benchmarks. The discovery rerun checked that the final display-only abbreviation for very large rationals left all results unchanged. Its earlier source hash was 9f045a2cfa7c11b53b915bde3abc57f8b8cdb2ebf0ddde05256f02790d8809d4.

Two earlier independent-verifier attempts were intentionally interrupted while redundant full rational residual vectors made the large roots slow. No failed mathematical assertion occurred. The completed version first removes the EXACT reciprocal reference and uses rational normal-equation moments; all 870,319 integer source ledgers and the projected checks still ran. The source diagnostic first failed before computation because mpmath was unavailable; installation was blocked by HTTP 403. It was replaced by standard-library Decimal, an Euler-Maclaurin Euler-gamma evaluation and the convergent Ei series for li. The final implementation and executed bytes are included below. Numerical values are explicitly non-certified.

A generic GitHub job-metadata read could not be parsed as JSON; no success state was invented from that call. The actual historical compilation log and tested source blob were available and inspected as recorded in B. This does not affect the exact computations or paper proofs.

Final executed script SHA-256 values:

```text
uc_probe.py
6a64c09b8c52cc59175094442d486658263c6608d54a0e06bc4fcdfec475c2b6
uc_independent.py
8a631cee2f3c912b49c086c8319344419b7070e3bc3196b10ea2043a65ca5d85
uc_source_diagnostics.py
f114637e938fa3e1fcba8fb47ef3dd0eb26120069c5e36883ca78c2f83e77b91
```

Commands, after placing the embedded scripts in the indicated scratch directory:

```bash
python /workspace/uc_probe.py --phase discovery --output /workspace/uc_discovery.json
python /workspace/uc_probe.py --phase held-out --output /workspace/uc_heldout.json
python /workspace/uc_independent.py
python /workspace/uc_source_diagnostics.py
python -m py_compile /workspace/uc_probe.py /workspace/uc_independent.py /workspace/uc_source_diagnostics.py
```

Exact physical prime counts and rational signs are finite arithmetic results. Decimal li values, quadrature, scaled displays and empirical onset assessments are not certified finite inequalities. UC3 is PAPER_PROOF, not PROVED_IN_LEAN. No independently reviewed acceptance is invented.

### L. Specialist Handoffs

**Proof Architect:** add UC2 as a precise guard against dropping saturation from HM/PC. UC3 explains why the extended transverse norm cannot have O(m) cost even for a fixed wheel. The full return stays unchanged and unpaid; this is no reason to abandon HF, RF, NC or other genuine signed approaches.

**Owner Payment:** inspect UC.1/UC.2 and the sharper actual-saturation criterion. The first optimization failure R=8 is NOT a rough-composite example; R=10 and R=29 are. A proposed outside-mask map using HM's transverse bound must either prove C=0 on its own admitted carrier or transport the entire extra vector and its reference.

**Analytic Type II:** the fixed-small-wheel response has a deterministic (log u)/u mode after constant and reciprocal projection. Verify UC3's uniform PNT expansion and prime-sampled Gram limit. It is a proper-source logarithmic-scale obstruction, not the high-frequency H_R from HF and not an automatic transfer to its signed spectral term.

**Finite Wheel:** unrestricted signed and absolute minima behave differently. No signed improvement occurred at the eight held-out roots, while every root had an absolute improvement. Do not extend PC's asymptotic variational theorem to ALL prefixes solely from those data; some new cutoffs are already actually saturated even though z^2<R.

**Adversarial Referee:** independently reconstruct R=29 using pi(t)-fract(X/(2q)), audit all three exact Gram contributions, and review UC3's empirical-projection passage and slowly growing wheel condition. Check the distinction between an optimal fitted slope and HM's fixed slope. These are new requests, not an assertion that review happened.

**Lean Verification:** after independent acceptance and only if useful to a live consumer, the finite unsaturated correction and the R=29 rational counterexample are compact candidates. Do not duplicate the existing complete-wheel identities, formalize an assumed RH-strength estimate, or label the asymptotic proved in Lean. No new PR is requested without that review gate.

### M. Ranked Experimental Portfolio

| Rank | Exact hypothesis or mechanism | Evidence and counterevidence | Independent ingredient / next theorem | Disposition |
| --- | --- | --- | --- | --- |
| 1 | Unsaturated rows require the full projected rough-composite correction; fixed small wheels have UC3 curvature | UC.1 exact on all tested rows; R=29 refutes bounded rounding; classical proof gives kappa>0 | Independent review of UC3; then an actual response/complement map that retains or cancels its logarithmic mode | RETAIN, scoped structural input |
| 2 | Saturated signed minimizers remain eventually optimal among ALL prefixes | False as an all-R assertion at R=8 and also genuinely rough cases such as R=29; no held-out signed improvements | A uniform genuine rough-survivor comparison, potentially using Buchstab information; no such theorem proved here | CONJECTURE only for an explicitly eventual reformulation; do not assign a fitted onset |
| 3 | Arbitrary small-cutoff transverse energy is <=m/4 or O(m) | Exact counterexample plus positive paper asymptotic | No new ingredient rescues this unchanged statement; growing z outside UC.3 is a different question | REJECT the stated extension |

The precise unproved rank-2 conjecture is: there exists R_0 such that for every integer R>=R_0 and every q in Q_R, min_(2<=z<=h)T_q(z)=min_(ceil(sqrt R)<=z<=h)T_q(z). No R_0 is proposed from data. Its proof would extend the signed-minimum part of PC to all prefixes, not prove the complete discrepancy bound.

No new numerical campaign is needed merely to confirm these counterexamples. No optimum universal constant or empirical growth exponent is inferred.

### N. Resume Capsule And Publication Discipline

```text
RUN=20261110-census-1/UC; RUN_ID_UNAVAILABLE.
TRIGGER=2026-11-10 03:11:02 EST, scheduled.
MAIN=7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9.
ACK=FINITE_WHEEL_CENTERED_RH_V1.
OWN_PREVIOUS=20261109-census-3/NC; report blob 8c927cc6c323533ba1cfd369404b25aa4f9cef91.
TODAY_READ=Owner HM, Analytic HF, Wheel PC.
TODAY_PENDING_AT_INTAKE=Coordinator, Referee, Lean.
YESTERDAY=CARRY_FORWARD; all seven actual report blobs are in the checkpoint.
EXTERNAL=038018145c0fddb2f6306c0712373adf9cd1ea52; no newer campaign input.
FINISHED=249 discovery roots + 8 fixed held-out roots; 870319 exact row states;
         independent trial-factor/rational audit and full source checks.
COUNTEREXAMPLES=signed optimum R8/q11/z2; absolute optimum R10/q11/z2;
                best-affine transverse bound R29/z2.
NEW_PAPER=rough-composite correction; fixed/small-wheel curvature law UC3.
NOT_PROVED=arbitrary-cutoff all-scale optimization; full centered error; RH.
NEXT=independent review of UC3 and construction of an actual reference-preserving
     response that accounts for C_q(z) and the logarithmic mode. Do not assume it exists.
NO_SOURCE_EDIT; NO_LOCAL_LEAN; NO_MAIN_PUSH; NO_PR_OR_BRANCH_WRITE;
NO_MERGE; NO_OTHER_REPORT_EDIT; NO_SCHEDULE_CHANGE; NO_AGENT_LAUNCH.
```

Publication is claimed only after the final append is committed and read back at its immutable commit. The early checkpoint remains an unchanged prefix. The complete executed programs and retained preregistration follow so that a later run need not reconstruct this work from narrative alone.


### Prepublication Freshness - 2026-11-10 03:41:40 EST

Main remains 7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9. Today's Owner, Analytic and Wheel blobs match the intake ledger exactly. Coordinator, Referee and Lean remain TODAY=PENDING; no execution is inferred from their schedules. #1127 remains the sole open PR at the same non-draft head. The current owned report was freshly fetched before this append and its early checkpoint is preserved as an exact prefix. All needed computation sessions have completed; publication will be verified at the immutable resulting commit.


## Preserved Held-Out Registration

# UC Held-Out Registration

Discovery is complete on R=8..256. It found the first tested-domain signed-minimum failure at (R,q,z)=(8,11,2), absolute-minimum failure at (10,11,2), and transverse-energy failure at (29,2). No held-out root has yet run.

Fixed hypotheses for held-out testing remain those in the published checkpoint. No fitted constants or changed cutoffs are introduced. The newly derived explanation to investigate is a fixed-cutoff curvature law, distinct from a claim of uniform optimality:

For each FIXED integer z>=2, as integer R tends to infinity, with Q_R the genuine primes in [R,2R) and P_R the Euclidean projection onto span{1,(1/q)},

||(I-P_R)T_R(z)||^2 ~ kappa R^3/(log R)^5,
kappa = min_(a,b in Real) integral_1^2 [(log u)/u-a-b/u]^2 du > 0.

This is a proof-led candidate using the classical PNT error, NOT an inference from the R<=256 data. It would refute every fixed O(#Q_R) transverse-energy budget without saturation. It says nothing about arbitrary growing z_R or the full centered discrepancy. The finite normalized energy need not already approximate kappa at the registered held-out roots.

Tests: execute the previously registered roots 263,389,521,1031,1543,2053,4099,8191 without editing the claims; independently verify the first witness, projection identity and complete-source reconstruction. The exact correction is -(I-P_R)(r_q+C_q(z)), including its mixed term. At fixed z, the original low-wheel counting error is bounded by its fixed complete face count; the remaining non-affine part is pi(floor(X/q)). This supports an analytic curvature derivation, not a random-sign interpretation.

This local registration is made before the held-out command and will be included in the final immutable report with observed command time. The only program change since discovery abbreviates enormous rationals in display; integer decisions and root lists are unchanged.


## Exact Executed Programs

### uc_probe.py

```python
"""Exact owner-prefix experiment. All assertions use integer/rational arithmetic."""

import argparse
from bisect import bisect_right
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt, prod
from pathlib import Path
import json
import platform
import time


HELD = [263, 389, 521, 1031, 1543, 2053, 4099, 8191]


def show_rational(x):
    if max(x.numerator.bit_length(), x.denominator.bit_length()) < 3000:
        return str(x)
    return {"approximation_only": float(x), "numerator_bits": x.numerator.bit_length(),
            "denominator_bits": x.denominator.bit_length()}


def least_factors(n):
    lp = list(range(n + 1))
    for p in range(2, isqrt(n) + 1):
        if lp[p] == p:
            for k in range(p * p, n + 1, p):
                if lp[k] == k:
                    lp[k] = p
    return lp


def projection_data(qs, X, ys):
    # Common integer coordinates avoid floating projection or ill-conditioned fits.
    m = len(qs)
    L = prod(qs)
    v = [L // q for q in qs]
    sy = sum(ys)
    sv = sum(v)
    dx = m * sum(k * k for k in v) - sv * sv
    dy = m * sum(k * k for k in ys) - sy * sy
    dxy = m * sum(k * j for k, j in zip(v, ys)) - sv * sy
    if dx == 0:
        return 0, 1
    return dy * dx - dxy * dxy, m * L * L * dx


def root_probe(R, lp, detail=False):
    X, h = R * R - 1, (R - 1) // 2
    a = isqrt(R - 1) + 1
    ps = [p for p in range(2, R) if lp[p] == p]
    qs = [q for q in range(R, 2 * R) if lp[q] == q]
    states = sorted({2, a, h} | {p for p in ps if p <= h})
    P = prod(ps)
    delta = {1: P}
    D = P
    for p in ps:
        assert D % p == 0
        D = D // p * (p - 1)
        delta[p] = D

    def density_num(z):
        j = bisect_right(ps, z)
        return delta[ps[j - 1]] if j else P

    W = density_num(h) - D
    H = bisect_right(ps, h)
    L = prod(qs)
    y_vectors = {z: [] for z in states if z <= a}
    first_signed = None
    first_abs = None
    records = []
    digest = sha256()
    row_checks = 0
    rough_occurrences = 0
    all_abs, sat_abs = F(0), F(0)
    for q in qs:
        t, rnum = divmod(X, q)
        hist = [0] * R
        comps = []
        for n in range(2, t + 1):
            hist[lp[n]] += 1
            if lp[n] != n:
                comps.append(lp[n])
        comps.sort()
        prefix = []
        s = 0
        for k in hist:
            s += k
            prefix.append(s)
        upper = sum(hist[p] for p in ps if 2 * p >= R)
        assert upper == bisect_right(ps, t) - H
        values = []
        for z in states:
            count = upper + prefix[z]
            num = q * P * count - X * (P - density_num(z) + W)
            C = len(comps) - bisect_right(comps, z)
            # Independent composite enumeration supplies the unsaturated correction.
            corrected = X * (density_num(z) - W) + q * P * (
                bisect_right(ps, z) - H - 1 - C
            ) - rnum * P
            assert num == corrected
            if z >= a:
                assert C == 0
            if z <= a:
                y_vectors[z].append((rnum + q * C) * (L // q))
            values.append((z, num, C))
            digest.update(f"{R},{q},{z},{count},{C};".encode())
            row_checks += 1
            rough_occurrences += C
        sat = [v for v in values if v[0] >= a]
        umin = min(values, key=lambda v: (v[1], v[0]))
        smin = min(sat, key=lambda v: (v[1], v[0]))
        uabs = min(values, key=lambda v: (abs(v[1]), v[0]))
        sabs = min(sat, key=lambda v: (abs(v[1]), v[0]))
        all_abs += F(abs(uabs[1]), q * P)
        sat_abs += F(abs(sabs[1]), q * P)
        for kind, left, right in [("signed", umin, smin), ("absolute", uabs, sabs)]:
            fail = left[1] < right[1] if kind == "signed" else abs(left[1]) < abs(right[1])
            if fail:
                rec = {"R": R, "q": q, "all_z": left[0], "sat_z": right[0],
                       "all_T": show_rational(F(left[1], q * P)), "sat_T": show_rational(F(right[1], q * P)),
                       "rough_count": left[2], "t": t}
                if kind == "signed" and first_signed is None:
                    first_signed = rec
                if kind == "absolute" and first_abs is None:
                    first_abs = rec
        if detail:
            records.append({"q": q, "t": t, "states": [[z, str(F(n, q * P)), c] for z, n, c in values]})

    transverse = []
    worst = (0, 1, 2)
    for z, yy in y_vectors.items():
        n, d = projection_data(qs, X, yy)
        assert n >= 0
        if z == a:
            assert 4 * n <= len(qs) * d
        if n * worst[1] > worst[0] * d:
            worst = (n, d, z)
        transverse.append((z, n, d))
    failures = [(z, n, d) for z, n, d in transverse if 4 * n > len(qs) * d]
    first_transverse = None
    if failures:
        z, n, d = failures[0]
        first_transverse = {"R": R, "z": z, "m": len(qs), "energy": show_rational(F(n, d)),
                            "bound": str(F(len(qs), 4)), "Q": qs}
    zn, zd = next((n, d) for z, n, d in transverse if z == 2)
    row = {"R": R, "m": len(qs), "states": len(states), "row_checks": row_checks,
           "signed_improvement": first_signed, "abs_improvement": first_abs,
           "transverse_failure": first_transverse,
           "max_transverse_z": worst[2], "max_transverse_over_bound": float(F(4 * worst[0], len(qs) * worst[1])),
           "z2_energy": float(F(zn, zd)), "z2_over_bound": float(F(4 * zn, len(qs) * zd)),
           "all_abs_sum": float(all_abs), "sat_abs_sum": float(sat_abs),
           "integer_ledger_sha256": digest.hexdigest()}
    if detail:
        row["records"] = records
        row["transverse"] = [[z, str(F(n, d))] for z, n, d in transverse]
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", choices=["discovery", "held-out", "witness"], required=True)
    parser.add_argument("--root", type=int)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    roots = list(range(8, 257)) if args.phase == "discovery" else HELD
    if args.phase == "witness":
        roots = [args.root]
    start = time.perf_counter()
    lp = least_factors(2 * max(roots))
    rows = [root_probe(R, lp, args.phase == "witness") for R in roots]
    summary = {"status": "PASS_EXACT", "phase": args.phase, "python": platform.python_version(),
               "root_count": len(rows), "rows_checked": sum(r["row_checks"] for r in rows),
               "first_signed_improvement": next((r["signed_improvement"] for r in rows if r["signed_improvement"]), None),
               "first_abs_improvement": next((r["abs_improvement"] for r in rows if r["abs_improvement"]), None),
               "first_transverse_failure": next((r["transverse_failure"] for r in rows if r["transverse_failure"]), None),
               "roots_with_signed_improvement": sum(r["signed_improvement"] is not None for r in rows),
               "roots_with_abs_improvement": sum(r["abs_improvement"] is not None for r in rows),
               "roots_with_transverse_failure": sum(r["transverse_failure"] is not None for r in rows),
               "worst_transverse": max(rows, key=lambda r: r["max_transverse_over_bound"]),
               "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
               "elapsed_seconds": time.perf_counter() - start}
    Path(args.output).write_text(json.dumps({"summary": summary, "rows": rows}, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
```

### uc_independent.py

```python
"""Trial-factor, Fraction normal-equation and full-divisor independent audit."""

from bisect import bisect_right
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations
from math import isqrt
from pathlib import Path
import json
import platform
import time


def factors(n):
    out = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            out.append(d)
            n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def prime(n):
    return n >= 2 and factors(n) == [n]


def fract(x):
    return x - x.numerator // x.denominator


def orthogonal(vector, x):
    m = len(vector)
    sx, sy = sum(x), sum(vector)
    xx, xy = sum(t * t for t in x), sum(t * u for t, u in zip(x, vector))
    det = m * xx - sx * sx
    if det == 0:
        return [v - sy / m for v in vector]
    alpha, beta = (sy * xx - xy * sx) / det, (m * xy - sx * sy) / det
    residual = [v - alpha - beta * u for v, u in zip(vector, x)]
    assert sum(residual) == sum(v * u for v, u in zip(residual, x)) == 0
    return residual


def cube(ps):
    out = [(1, 1)]
    for p in ps:
        out += [(p * d, -mu) for d, mu in out[:]]
    return out


def audit_root(R, expected, full_rows):
    X, h, a = R * R - 1, (R - 1) // 2, isqrt(R - 1) + 1
    fs = [factors(n) for n in range(2 * R)]
    ps = [n for n in range(2, R) if fs[n] == [n]]
    qs = [n for n in range(R, 2 * R) if fs[n] == [n]]
    states = sorted({2, a, h} | {p for p in ps if p <= h})
    weights, density = {}, Q(1)
    for p in ps:
        weights[p] = density / p
        density *= Q(p - 1, p)
    digest = sha256()
    vectors = {z: [] for z in states if full_rows or z <= a}
    rough_vectors = {z: [] for z in vectors}
    selected_weights = {z: sum(weights[p] for p in ps if p <= z or 2*p >= R)
                        for z in vectors}
    xs = [Q(X, q) for q in qs]
    for q in qs:
        t = X // q
        owners = sorted(fs[n][0] for n in range(2, t + 1))
        composites = sorted(fs[n][0] for n in range(2, t + 1) if len(fs[n]) > 1)
        upper = sum(2 * p >= R for p in owners)
        for z in states:
            count = upper + bisect_right(owners, z)
            c = len(composites) - bisect_right(composites, z)
            digest.update(f"{R},{q},{z},{count},{c};".encode())
            if z in vectors:
                w = selected_weights[z]
                # The reference is proportional to x, so projection removes it exactly.
                vectors[z].append(count)
                rough_vectors[z].append(Q(c) + fract(Q(X, q)))
                if R <= 16:
                    via_faces = -sum((mu * fract(Q(X, p * q * d))
                                      for p in ps if p <= z or 2 * p >= R
                                      for d, mu in cube([r for r in ps if r < p])), Q(0))
                    assert count - Q(X, q) * w == via_faces
    assert digest.hexdigest() == expected["integer_ledger_sha256"]
    first_bad = None
    energies = {}
    sx, xx = sum(xs), sum(x*x for x in xs)
    det = len(qs)*xx-sx*sx
    for z, vec in vectors.items():
        assert all(v+u-x == bisect_right(ps,z)-bisect_right(ps,h)-1
                   for v,u,x in zip(vec,rough_vectors[z],xs))
        sy, yy = sum(vec), sum(v*v for v in vec)
        xy = sum(v*x for v,x in zip(vec,xs))
        alpha, beta = (sy*xx-xy*sx)/det, (len(qs)*xy-sx*sy)/det
        E = yy-alpha*sy-beta*xy
        energies[z] = E
        if E > Q(len(qs), 4) and first_bad is None:
            first_bad = z
        if z >= a:
            assert E <= Q(len(qs), 4)
    expected_bad = expected["transverse_failure"]
    assert first_bad == (None if expected_bad is None else expected_bad["z"])
    if full_rows:
        for i, q in enumerate(qs):
            allvals = [(z, vectors[z][i]-xs[i]*selected_weights[z]) for z in states]
            satvals = [(z, v) for z, v in allvals if z >= a]
            if R == 8 and q == 11:
                assert min(v for z, v in allvals) == Q(-51, 110)
                assert min(v for z, v in satvals) == Q(-23, 55)
            if R == 10 and q == 11:
                assert min(abs(v) for z, v in allvals) == Q(39, 70)
                assert min(abs(v) for z, v in satvals) == Q(37, 35)
    result = {"R": R, "ledger_match": True, "first_bad_z": first_bad}
    if R == 29:
        z = 2
        rr = [fract(x) for x in xs]
        cc = [v - r for v, r in zip(rough_vectors[z], rr)]
        pr, pc = orthogonal(rr, xs), orthogonal(cc, xs)
        er, ec = sum(v*v for v in pr), sum(v*v for v in pc)
        cross = 2 * sum(v*w for v, w in zip(pr, pc))
        assert er + ec + cross == energies[z]
        assert energies[z] == Q(13204382152870676585, 7298618577576669768)
        result.update({"Q": qs, "t": [X//q for q in qs], "C": list(map(int, cc)),
                       "rounding_energy": str(er), "rough_energy": str(ec),
                       "doubled_cross": str(cross), "total_energy": str(energies[z]),
                       "excess_over_m4": str(energies[z]-Q(len(qs),4))})
    return result


def complete_source(R):
    X, y, h = R * R - 1, R - 1, (R - 1) // 2
    ps = [p for p in range(2, R) if prime(p)]
    faces = cube(ps)
    density = sum((Q(mu, d) for d, mu in faces), Q(0))
    physical = sum((mu * fract(Q(X, d)) for d, mu in faces if d <= X), Q(0))
    virtual = X * sum((Q(mu, d) for d, mu in faces if d > X), Q(0))
    F = physical + virtual
    physical_floor = sum(mu * (X // d) for d, mu in faces if d <= X)
    prime_X = sum(prime(n) for n in range(2, X + 1))
    assert F - X * density == -physical_floor
    assert physical_floor == 1 + prime_X - len(ps)
    qs = [q for q in range(R, 2 * R) if prime(q)]
    weights, de = {}, Q(1)
    for p in ps:
        weights[p] = de / p
        de *= Q(p - 1, p)
    owner = {p: sum(factors(n)[0] == p for n in range(2, X + 1)) - X * weights[p]
             for p in ps}
    assert sum(owner.values()) == F
    if R >= 8:
        mask = {p: sum(sum(factors(a)[0] == p for a in range(2, X // q + 1))
                           - Q(X, q) * weights[p] for q in qs) for p in ps}
        E = sum(mask[p] for p in ps if p <= 2 or 2*p >= R)
        J = sum(mask.values()) - E
        ref = Q(355, 113)
        D = X * density + len(ps) - 1 - ref
        C = sum(owner[p] - mask[p] for p in ps) - D
        total = F - D
        assert E + J + C == total == ref - prime_X
        assert total**2 == E**2 + J**2 + C**2 + 2*(E*J + E*C + J*C)
    return {"R": R, "physical": str(physical), "virtual": str(virtual), "full_F": str(F),
            "physical_floor": physical_floor, "d_equals_X": [(d, mu) for d, mu in faces if d == X]}


def main():
    start = time.perf_counter()
    discovery = json.loads(Path("/workspace/uc_discovery.json").read_text())
    held = json.loads(Path("/workspace/uc_heldout.json").read_text())
    selected = discovery["rows"] + held["rows"]
    results = [audit_root(r["R"], r, r["R"] <= 64) for r in selected]
    cubes = [complete_source(R) for R in [2, 3] + list(range(8, 17))]
    out = {"status": "PASS_INDEPENDENT_TRIAL_FACTOR_AND_NORMAL_EQUATIONS", "python": platform.python_version(),
           "roots": len(results), "integer_ledger_rows": sum(r["row_checks"] for r in selected),
           "first_transverse_failure": next(r for r in results if r["first_bad_z"] is not None),
           "complete_source": cubes, "elapsed_seconds": time.perf_counter()-start,
           "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest()}
    Path("/workspace/uc_independent.json").write_text(json.dumps(out, indent=2)+"\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
```

### uc_source_diagnostics.py

```python
"""Full physical source checks and explicitly non-certified li diagnostics."""

from array import array
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt
from pathlib import Path
import json
import platform
import time
from decimal import Decimal as D, localcontext


ROOTS = [2, 3, 8, 10, 29, 263, 389, 521, 1031, 1543, 2053, 4099, 8191]


def eratosthenes(n):
    flags = bytearray(b"\x01") * (n + 1)
    flags[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            flags[p*p:n+1:p] = b"\x00" * ((n - p*p) // p + 1)
    return flags


def physical_floor(R, flags):
    X, y = R*R-1, R-1
    mu = array("b", [1]) * (X + 1)
    gp = array("I", [0]) * (X + 1)
    mu[0] = 0
    for p in range(2, X + 1):
        if flags[p]:
            for n in range(p, X + 1, p):
                mu[n] = -mu[n]
                gp[n] = p
            if p*p <= X:
                for n in range(p*p, X + 1, p*p):
                    mu[n] = 0
    total = sum(mu[d] * (X // d) for d in range(1, X + 1) if gp[d] <= y)
    direct_count = 1 + sum(flags[:X+1]) - sum(flags[:R])
    assert total == direct_count
    # Every omitted virtual term is X*mu(d)/d and cancels against itself.
    return {"R": R, "X": X, "physical_floor": total,
            "direct_survivor_count": direct_count,
            "physical_nonzero_divisors": sum(mu[d] != 0 and gp[d] <= y for d in range(1, X+1)),
            "virtual_compensation": "X*(delta(R-1)-sum_physical mu(d)/d); retained symbolically"}


def gamma_decimal(precision):
    # Euler--Maclaurin with exact Bernoulli numbers; output remains non-certified.
    count, n = max(24, precision // 3), 1000
    a, bernoulli = [], []
    for m in range(2 * count + 1):
        a.append(F(1, m + 1))
        for j in range(m, 0, -1):
            a[j - 1] = j * (a[j - 1] - a[j])
        bernoulli.append(a[0])
    with localcontext() as ctx:
        ctx.prec = precision + 20
        g = sum((D(1)/k for k in range(1, n+1)), D(0)) - D(n).ln() - D(1)/(2*n)
        for k in range(1, count+1):
            b = bernoulli[2*k]
            g += D(b.numerator)/D(b.denominator)/(2*k*D(n)**(2*k))
        return +g


def li_decimal(x, precision, gamma):
    with localcontext() as ctx:
        ctx.prec = precision + 20
        z = D(x).ln()
        term, total, k = z, z, 1
        while True:
            k += 1
            term *= z/k
            increment = term/k
            total += increment
            if abs(increment) < D(10)**(-precision-10):
                break
        return +(gamma+z.ln()+total)


def curvature_constant():
    ell = D(2).ln()
    b1, b2 = ell**2/2, (1-ell)/2
    det = D(1)/2-ell**2
    alpha, beta = (b1/2-ell*b2)/det, (b2-ell*b1)/det
    closed = 1-ell-ell**2/2-b1*alpha-b2*beta
    approximations = []
    with localcontext() as ctx:
        ctx.prec = 40
        for count in [1024, 2048]:
            step = D(1)/count
            total = D(0)
            for j in range(count+1):
                u = 1+j*step
                value = (u.ln()/u-alpha-beta/u)**2
                weight = 1 if j in [0, count] else (4 if j % 2 else 2)
                total += weight*value
            approximations.append(total*step/3)
    return closed, approximations, [alpha, beta]


def main():
    start = time.perf_counter()
    flags = eratosthenes(max(ROOTS)**2-1)
    assert sum(flags[:101]) == 25
    assert sum(flags[:1000001]) == 78498
    exact = [physical_floor(R, flags) for R in [263, 521, 1031]]
    rows = []
    gammas = {p: gamma_decimal(p) for p in [80, 160]}
    for R in ROOTS:
        X = R*R-1
        piX = sum(flags[:X+1])
        values = []
        for prec in [80, 160]:
            with localcontext() as ctx:
                ctx.prec = prec
                values.append(+(abs(li_decimal(X, prec, gammas[prec])-piX)/(R*D(R).ln())))
        with localcontext() as ctx:
            ctx.prec = 160
            diff = abs(values[0]-values[1])
            assert diff < D("1e-70")
            rows.append({"R": R, "X": X, "pi_X": piX,
                         "normalized_abs_li_minus_pi": format(values[1], ".28g"),
                         "precision_difference": format(diff, ".4g")})
    with localcontext() as ctx:
        ctx.prec = 160
        k, quadrature, coefficients = curvature_constant()
        assert abs(k - quadrature[-1]) < D("1e-12")
        curvature = {"kappa": format(k, ".60g"), "independent_simpson": [format(v, ".30g") for v in quadrature],
                     "affine_coefficients": [format(v, ".40g") for v in coefficients]}
    held = json.loads(Path("/workspace/uc_heldout.json").read_text())
    with localcontext() as ctx:
        ctx.prec = 80
        for row in held["rows"]:
            R = row["R"]
            row["scaled_z2_energy_display_only"] = float(D(str(row["z2_energy"]))*D(R).ln()**5/R**3)
        scaling = [{k: r[k] for k in ["R", "z2_energy", "scaled_z2_energy_display_only"]} for r in held["rows"]]
    out = {"status": "PASS_EXACT_SOURCE_AND_NONCERTIFIED_HIGH_PRECISION_DIAGNOSTICS",
           "python": platform.python_version(), "transcendentals": "stdlib Decimal, 80 and 160 decimal digits",
           "source_checks": exact, "li_diagnostics": rows, "curvature": curvature,
           "scaling_diagnostics": scaling, "elapsed_seconds": time.perf_counter()-start,
           "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
           "limitations": "Transcendentals and quadrature are approximations, not interval certificates or proof of onset."}
    Path("/workspace/uc_source_diagnostics.json").write_text(json.dumps(out, indent=2)+"\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
```

## Recorded Output

### Primary Summary

```json
{
  "status": "PASS_EXACT",
  "discovery_roots": 249,
  "discovery_rows": 137647,
  "held_out_roots": 8,
  "held_out_rows": 732672,
  "first_signed": {
    "R": 8,
    "q": 11,
    "all_z": 2,
    "sat_z": 3,
    "all_T": "-51/110",
    "sat_T": "-23/55",
    "rough_count": 0,
    "t": 5
  },
  "first_absolute": {
    "R": 10,
    "q": 11,
    "all_z": 2,
    "sat_z": 4,
    "all_T": "39/70",
    "sat_T": "37/35",
    "rough_count": 1,
    "t": 9
  },
  "first_transverse": {
    "R": 29,
    "z": 2,
    "m": 7,
    "energy": "13204382152870676585/7298618577576669768",
    "bound": "7/4",
    "Q": [
      29,
      31,
      37,
      41,
      43,
      47,
      53
    ]
  },
  "held_out": [
    {
      "R": 263,
      "m": 44,
      "signed_improvement": false,
      "absolute_improvement": true,
      "transverse_failure": true,
      "max_transverse_z": 2,
      "max_transverse_over_bound": 1.5576196378797287,
      "z2_energy": 17.133816016677013,
      "all_abs_sum": 177.22382466457358,
      "sat_abs_sum": 177.61645405756852,
      "integer_ledger_sha256": "cf6ae290a51b0516146a22b88be18e66beba0389e221a9669920f40c8b2652ec"
    },
    {
      "R": 389,
      "m": 61,
      "signed_improvement": false,
      "absolute_improvement": true,
      "transverse_failure": true,
      "max_transverse_z": 5,
      "max_transverse_over_bound": 1.6076405848089816,
      "z2_energy": 20.82444315933759,
      "all_abs_sum": 311.1557083299049,
      "sat_abs_sum": 312.06926065042694,
      "integer_ledger_sha256": "72ec2ba8f74f920a161d9dc8d52a3195b2a9ffa248bbd0fe4e052aa611cf7b52"
    },
    {
      "R": 521,
      "m": 78,
      "signed_improvement": false,
      "absolute_improvement": true,
      "transverse_failure": true,
      "max_transverse_z": 2,
      "max_transverse_over_bound": 1.6397363654011465,
      "z2_energy": 31.974859125322354,
      "all_abs_sum": 516.5001523840625,
      "sat_abs_sum": 516.9792408212161,
      "integer_ledger_sha256": "acd151552b7a50926417769da97fa30986a34d84201b8bbfb1d7c548423f7113"
    },
    {
      "R": 1031,
      "m": 138,
      "signed_improvement": false,
      "absolute_improvement": true,
      "transverse_failure": true,
      "max_transverse_z": 2,
      "max_transverse_over_bound": 4.203319424169158,
      "z2_energy": 145.01452013383596,
      "all_abs_sum": 1465.7273392933105,
      "sat_abs_sum": 1466.7265201345995,
      "integer_ledger_sha256": "a8dce5ba2a02843ad4ebb6ba4ddd75daafe4bbbec3951732db1e4f840866e7a7"
    },
    {
      "R": 1543,
      "m": 199,
      "signed_improvement": false,
      "absolute_improvement": true,
      "transverse_failure": true,
      "max_transverse_z": 2,
      "max_transverse_over_bound": 5.849046513412018,
      "z2_energy": 290.9900640422479,
      "all_abs_sum": 2749.169270979352,
      "sat_abs_sum": 2749.9470998861098,
      "integer_ledger_sha256": "0f949889a50473690d2e9a3de93681c574709fd898294c659716854ea10334b2"
    },
    {
      "R": 2053,
      "m": 256,
      "signed_improvement": false,
      "absolute_improvement": true,
      "transverse_failure": true,
      "max_transverse_z": 3,
      "max_transverse_over_bound": 7.252358404524603,
      "z2_energy": 453.62259510524245,
      "all_abs_sum": 4404.439211588812,
      "sat_abs_sum": 4406.6574142272275,
      "integer_ledger_sha256": "744ed2f6a4b4943422fefdcf6a5347c0a51a6eebb1fe6b61986adf99f44aa5b6"
    },
    {
      "R": 4099,
      "m": 464,
      "signed_improvement": false,
      "absolute_improvement": true,
      "transverse_failure": true,
      "max_transverse_z": 7,
      "max_transverse_over_bound": 12.835375913721693,
      "z2_energy": 1394.8864059521393,
      "all_abs_sum": 13030.933022272695,
      "sat_abs_sum": 13032.507956167548,
      "integer_ledger_sha256": "a68bd95d93a9dcd3d9acbbb65f7d9c4a52c1d1b4fe37434472b42659c1bc27c0"
    },
    {
      "R": 8191,
      "m": 873,
      "signed_improvement": false,
      "absolute_improvement": true,
      "transverse_failure": true,
      "max_transverse_z": 61,
      "max_transverse_over_bound": 23.474163108228524,
      "z2_energy": 3431.185884792155,
      "all_abs_sum": 40527.65314122991,
      "sat_abs_sum": 40530.400289916375,
      "integer_ledger_sha256": "63cd8d7d8afc615f523b28e64339be1450afe5b4b7067fe94af684d850ad973c"
    }
  ]
}
```

### Independent Audit

```json
{
  "status": "PASS_INDEPENDENT_TRIAL_FACTOR_AND_NORMAL_EQUATIONS",
  "python": "3.12.14",
  "roots": 257,
  "integer_ledger_rows": 870319,
  "first_transverse_failure": {
    "R": 29,
    "ledger_match": true,
    "first_bad_z": 2,
    "Q": [
      29,
      31,
      37,
      41,
      43,
      47,
      53
    ],
    "t": [
      28,
      27,
      22,
      20,
      19,
      17,
      15
    ],
    "C": [
      5,
      5,
      3,
      2,
      2,
      2,
      2
    ],
    "rounding_energy": "3659936844782588825/7298618577576669768",
    "rough_energy": "1202843690975460748/912327322197083721",
    "doubled_cross": "-9788027464449778/912327322197083721",
    "total_energy": "13204382152870676585/7298618577576669768",
    "excess_over_m4": "431799642111504491/7298618577576669768"
  },
  "complete_source": [
    {
      "R": 2,
      "physical": "0",
      "virtual": "0",
      "full_F": "0",
      "physical_floor": 3,
      "d_equals_X": []
    },
    {
      "R": 3,
      "physical": "0",
      "virtual": "0",
      "full_F": "0",
      "physical_floor": 4,
      "d_equals_X": []
    },
    {
      "R": 8,
      "physical": "3/5",
      "virtual": "-6/5",
      "full_F": "-3/5",
      "physical_floor": 15,
      "d_equals_X": []
    },
    {
      "R": 9,
      "physical": "-1/3",
      "virtual": "-8/21",
      "full_F": "-5/7",
      "physical_floor": 19,
      "d_equals_X": []
    },
    {
      "R": 10,
      "physical": "11/10",
      "virtual": "-33/70",
      "full_F": "22/35",
      "physical_floor": 22,
      "d_equals_X": []
    },
    {
      "R": 11,
      "physical": "-1/7",
      "virtual": "4/7",
      "full_F": "3/7",
      "physical_floor": 27,
      "d_equals_X": []
    },
    {
      "R": 12,
      "physical": "29/35",
      "virtual": "-39/35",
      "full_F": "-2/7",
      "physical_floor": 30,
      "d_equals_X": []
    },
    {
      "R": 13,
      "physical": "-49/55",
      "virtual": "4/5",
      "full_F": "-1/11",
      "physical_floor": 35,
      "d_equals_X": []
    },
    {
      "R": 14,
      "physical": "-227/154",
      "virtual": "-19/154",
      "full_F": "-123/77",
      "physical_floor": 39,
      "d_equals_X": [
        [
          195,
          -1
        ]
      ]
    },
    {
      "R": 15,
      "physical": "839/715",
      "virtual": "-864/715",
      "full_F": "-5/143",
      "physical_floor": 43,
      "d_equals_X": []
    },
    {
      "R": 16,
      "physical": "183/1001",
      "virtual": "-272/1001",
      "full_F": "-89/1001",
      "physical_floor": 49,
      "d_equals_X": []
    }
  ],
  "elapsed_seconds": 14.398886880999953,
  "source_sha256": "8a631cee2f3c912b49c086c8319344419b7070e3bc3196b10ea2043a65ca5d85"
}
```

### Full Source And Numerical Diagnostics

```json
{
  "status": "PASS_EXACT_SOURCE_AND_NONCERTIFIED_HIGH_PRECISION_DIAGNOSTICS",
  "python": "3.12.14",
  "transcendentals": "stdlib Decimal, 80 and 160 decimal digits",
  "source_checks": [
    {
      "R": 263,
      "X": 69168,
      "physical_floor": 6815,
      "direct_survivor_count": 6815,
      "physical_nonzero_divisors": 10109,
      "virtual_compensation": "X*(delta(R-1)-sum_physical mu(d)/d); retained symbolically"
    },
    {
      "R": 521,
      "X": 271440,
      "physical_floor": 23664,
      "direct_survivor_count": 23664,
      "physical_nonzero_divisors": 40729,
      "virtual_compensation": "X*(delta(R-1)-sum_physical mu(d)/d); retained symbolically"
    },
    {
      "R": 1031,
      "X": 1062960,
      "physical_floor": 82859,
      "direct_survivor_count": 82859,
      "physical_nonzero_divisors": 162729,
      "virtual_compensation": "X*(delta(R-1)-sum_physical mu(d)/d); retained symbolically"
    }
  ],
  "li_diagnostics": [
    {
      "R": 2,
      "X": 3,
      "pi_X": 2,
      "normalized_abs_li_minus_pi": "0.1180042271361762922589595050",
      "precision_difference": "2.154e-81"
    },
    {
      "R": 3,
      "X": 8,
      "pi_X": 4,
      "normalized_abs_li_minus_pi": "0.3803945251328117228495933725",
      "precision_difference": "2.109e-80"
    },
    {
      "R": 8,
      "X": 63,
      "pi_X": 18,
      "normalized_abs_li_minus_pi": "0.2220406221738623096224103165",
      "precision_difference": "3.876e-81"
    },
    {
      "R": 10,
      "X": 99,
      "pi_X": 25,
      "normalized_abs_li_minus_pi": "0.2131846271028431671866340391",
      "precision_difference": "7.986e-82"
    },
    {
      "R": 29,
      "X": 840,
      "pi_X": 146,
      "normalized_abs_li_minus_pi": "0.08354875596199834073841249331",
      "precision_difference": "9.508e-82"
    },
    {
      "R": 263,
      "X": 69168,
      "pi_X": 6869,
      "normalized_abs_li_minus_pi": "0.02843960945447054620234023205",
      "precision_difference": "1.375e-81"
    },
    {
      "R": 389,
      "X": 151320,
      "pi_X": 13960,
      "normalized_abs_li_minus_pi": "0.01886540892921978137252352342",
      "precision_difference": "1.055e-83"
    },
    {
      "R": 521,
      "X": 271440,
      "pi_X": 23760,
      "normalized_abs_li_minus_pi": "0.01632904602294280224616998519",
      "precision_difference": "5.655e-82"
    },
    {
      "R": 1031,
      "X": 1062960,
      "pi_X": 83030,
      "normalized_abs_li_minus_pi": "0.02021469796622517461236916644",
      "precision_difference": "3.049e-82"
    },
    {
      "R": 1543,
      "X": 2380848,
      "pi_X": 174979,
      "normalized_abs_li_minus_pi": "0.01452895239119058792266343969",
      "precision_difference": "2.609e-82"
    },
    {
      "R": 2053,
      "X": 4214808,
      "pi_X": 297297,
      "normalized_abs_li_minus_pi": "0.01029577558685325819822974735",
      "precision_difference": "3.326e-82"
    },
    {
      "R": 4099,
      "X": 16801800,
      "pi_X": 1079376,
      "normalized_abs_li_minus_pi": "0.009485610588011593936523394390",
      "precision_difference": "1.656e-82"
    },
    {
      "R": 8191,
      "X": 67092480,
      "pi_X": 3956871,
      "normalized_abs_li_minus_pi": "0.007714977615442630796777351477",
      "precision_difference": "6.613e-83"
    }
  ],
  "curvature": {
    "kappa": "0.000157046369900961834743617129553914350539339485096831982288609",
    "independent_simpson": [
      "0.000157046369920116352506835009475",
      "0.000157046369902159001728294957203"
    ],
    "affine_coefficients": [
      "0.7042604983229081130799663851199474950574",
      "-0.6694595381444770106657414840028042485433"
    ]
  },
  "scaling_diagnostics": [
    {
      "R": 263,
      "z2_energy": 17.133816016677013,
      "scaled_z2_energy_display_only": 0.005059439647322869
    },
    {
      "R": 389,
      "z2_energy": 20.82444315933759,
      "scaled_z2_energy_display_only": 0.0026684532725598994
    },
    {
      "R": 521,
      "z2_energy": 31.974859125322354,
      "scaled_z2_energy_display_only": 0.00216616935366944
    },
    {
      "R": 1031,
      "z2_energy": 145.01452013383596,
      "scaled_z2_energy_display_only": 0.0021276295240388655
    },
    {
      "R": 1543,
      "z2_energy": 290.9900640422479,
      "scaled_z2_energy_display_only": 0.0016892721469447512
    },
    {
      "R": 2053,
      "z2_energy": 453.62259510524245,
      "scaled_z2_energy_display_only": 0.0013530470840718229
    },
    {
      "R": 4099,
      "z2_energy": 1394.8864059521393,
      "scaled_z2_energy_display_only": 0.0008067328713691123
    },
    {
      "R": 8191,
      "z2_energy": 3431.185884792155,
      "scaled_z2_energy_display_only": 0.0003708925559020739
    }
  ],
  "elapsed_seconds": 1.9137790359998235,
  "source_sha256": "f114637e938fa3e1fcba8fb47ef3dd0eb26120069c5e36883ca78c2f83e77b91",
  "limitations": "Transcendentals and quadrature are approximations, not interval certificates or proof of onset."
}
```


## Verified Publication Receipt - 20261110-census-1/UC

At 2026-11-10 08:45:53 UTC, substantive commit `8cc9788cee79c34a1c83f45af4e87ae654abb78b`, report blob `8c093df87db4e787c230faf5a289a2df591182fb`, was re-fetched at that IMMUTABLE commit and all 71,860 characters matched the intended report exactly. Commit inspection confirmed exactly one changed path, `research/agent_reports/2026-11-10/40-prime-census.md`, with 1,460 additions and zero deletions. The early preregistration checkpoint is an unchanged prefix.

Execution=COMPLETE. Substantive publication=PUBLISHED_AND_READBACK_VERIFIED. UC2 retains its exact REFUTED-extension scope, UC4 is FINITE_COMPUTATION, and UC1/UC3 paper arguments remain SELF_AUDIT with INDEPENDENT_REVIEW_PENDING and no new Lean certification. The full uniform finite-wheel estimate, canonical endpoint and RH remain OPEN.

The report includes all three final executed programs, their observed hashes, exact witnesses, complete-source tests, numerical precision limits and the next-run capsule. No other report, source, policy, branch, PR, issue, workflow, merge, permission or schedule was changed; no agent was launched. All required computation sessions have finished. This receipt records already completed verification, not a prospective promise; its own append is separately read back before the final user response.


## Scheduled Preregistration - 20261110-census-2/GC

Recorded 2026-11-11 00:05:48 UTC; trigger 2026-11-10 19:00:01 EST; RUN_ID_UNAVAILABLE.
Execution=IN_PROGRESS. cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1.
Main=f7947bee036c4dddb0c36fc9f53ab46b4fa90995; AGENTS blob=c9c89f01b90b526de9f3e8ea92478e36504711b6; contract blob=95566e37c8eaeb99ee680660df4f9d2e06ea5038; policy=e922d4ba9362a1ae196af8f6de88f7417f92087c.
All seven November 10 and November 9 reports and the external inbox were retrieved at report head e715cfda8aa5e6cb42501fb155592545b9d260af. TODAY=AVAILABLE; YESTERDAY=CARRY_FORWARD. Current open/draft PR enumeration is empty. #1130 is merged, superseding its earlier report state. No old UC table is being repeated.

### Mathematical Question And Frozen Tests

For X=R^2-1, Q_R=sum_(1<=a,b<R)mu(a)mu(b)floor(X/(ab)), define C_R(g) by the SAME ordered pairs restricted to gcd(a,b)=g. Every diagonal, both off-diagonal orientations, squarefree zero, and inclusive floor endpoint remains. Thus Q_R=sum_g C_R(g). Define D_G=sum_g C_R(g)^2 and O_G=Q_R^2-D_G. This is a scalar grouping of the original bilinear source, NOT the #915 zero-target NNS normalization and NOT the lcm-divisor Gram.

Registered auxiliary hypotheses, not assertions by another specialist:

1. H_POS: C_R(g)>=0 for every g>=2. This tests whether positive shared-factor fibres survive the true historical cutoff and coprime complement.
2. H_CROSS: O_G<=0 at every R>=2. Equivalently, |Q_R|^2<=sum_g C_R(g)^2. This tests whether all shared-gcd grouping interactions can be discarded in the favorable direction.
3. H_SPLIT: C_R(1)*sum_(g>=2)C_R(g)<=0. This weaker two-sector sign test distinguishes internal shared-sector interactions from the full cross Gram.

Rival explanation: parity/coprimality restrictions induce coherent positive or negative groups, and the sign may reverse under grouping; no cofactor-positivity theorem automatically controls the global interaction. Rejection criterion is ONE exact strict failure on the stated complete source. Record smallest failures in the exhaustive domain and largest finite margins; a surviving bound remains CONJECTURE, not a theorem.

Discovery roots: every integer 2<=R<=256. Held-out, fixed before execution: 257,263,511,512,513,549,1023,1024,1025,2047,2048,2049,4095,4096,4097,5561. Near-dyadic roots test arithmetic boundaries, not an unverified claim that every listed root is prime-resonant. Stop after this finite set unless a specific discrepancy needs localization.

At every root retain exact K_R=max_(0<=u<R)(M(u)-1)^2/(u+1), its earliest maximizer, Q_R^2/(R^2*K_R), and (M(X)-1)^2/(R^2*K_R). Independently compare Q_R with 2M(R-1)-M(X). Exact integer/rational arithmetic only for decisions; no fitted constants or random controls. An independent factorization/Dirichlet recurrence will check important results against a sieve/pair implementation. Code and execution evidence will follow.

### Authority, Paid Recovery And Pending Work

Original definitions read in EULER_FRACTIONAL_COUPLED_20261027.lean (e6c4b1690e497760d366e36b28a1f7aa60e19f85), EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean (e97561ef330a9996fd807d8910369f0698147b01), and the square-root amplification consumer. Latest #1119 native_mertens_near_uniform_window_error_closed source f629db1b2b65d6ec042ac9432397d4b6316200c6 and actual successful audit log 128949473700 were read; exact dependency freshness/comparison remains to finish. No new baseline or global gain is asserted.

The paid recovery candidates are exact divisor/floor and cofactor decompositions, not a hidden sign estimate. The test asks whether their true masks justify a favorable COMPLETE grouping inequality. Even a positive finite result would leave a uniform D_G bound relative to K_R unpaid. Owner DR/Wheel RC complete auxiliary defect work and Analytic IR/Coordinator MD paper endpoint proposals remain distinct carriers/statuses.

Next: execute the frozen tests, independently reconstruct any failure, map the precise lost interaction, and append checked findings without changing this registration or earlier daily evidence. No Lean execution, source modification, agent launch, schedule change, or new proof route is authorized or claimed.


## Shared-GCD Cancellation Is Not Preserved By Coarsening - 20261110-census-2/GC

### A. Most Important Mathematical Discovery

**On the complete historical Mobius floor source, fine gcd groups can compensate while the coprime and noncoprime totals reinforce.** At R=17 the complete source has C(1)=4 and sum_(g>=2)C(g)=1. Their doubled cross term is +8, yet the cross term between all individual gcd groups is -148. The missing -156 is exactly the interaction INSIDE the noncoprime sector. At the required held-out R=549 the same reversal occurs: the binary cross term is +8848 while the fine cross term is -178880.

Separately, the assertion that every shared-gcd group is nonnegative first fails at R=15, g=2, with C(2)=-6. Sharing a prime does not preserve a positivity theorem from a different cofactor carrier. These are refutations of the explicitly registered auxiliary rules, not of any canonical, first-bad, CORR4 or certified cofactor theorem.

| Stable claim | Evidence classification | Scope |
| --- | --- | --- |
| 20261110-census-2/GC1 | REFUTED | H_POS: all shared-gcd groups nonnegative; smallest failure R=15, g=2. |
| GC2 | REFUTED | H_SPLIT: coprime/noncoprime totals always oppose; smallest failure R=17. Exact fine-to-coarse sign reversals at R=17 and 549. |
| GC3 | PAPER_PROOF | Elementary pair-product/squarepart sign classification and exact coarsening formula; supporting explanation, not a new global bound. SELF_AUDIT; not formalized. |
| GC4 | FINITE_COMPUTATION | Two independent reconstructions agree at all 271 registered roots. Full Q, strict-history K, squares and all gcd groups retained. |
| GC5 | CONJECTURE | H_CROSS: Q_R^2<=sum_g C_R(g)^2 for every integer R>=2. Survived the registered finite set only. |

NET RESULT: **NO_NEW_GLOBAL_GAIN / NO_NEW_ACCEPTED_ROUTE / VERIFIED_ETA=NONE.** A finite sign conjecture plus an unproved norm bound is not admitted as a new proof route.

### B. Current Authoritative Objective

Actual scheduled trigger: 2026-11-10 19:00:01 EST, America/New_York. Run label 20261110-census-2/GC; platform RUN_ID_UNAVAILABLE. The complete preregistration was published and read back before any experiment: commit e3bcc5a3f02cf290f65adc01786b970fdaa6a2a2, blob a6957f29c50ebf54a408726863e95b608a8a4ffc. Original registration and all earlier daily evidence are preserved.

`cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. Source main is **f7947bee036c4dddb0c36fc9f53ab46b4fa90995**, fetched at invocation start. AGENTS c9c89f01b90b526de9f3e8ea92478e36504711b6 takes priority over the contract's older task-selection sentence; contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038 leaves the mathematical target unchanged. The governing cross-route directive is e922d4ba9362a1ae196af8f6de88f7417f92087c.

The canonical OPEN goal remains `VFCanonicalSquareVonKochStatement`: one C>=0 before all integers R>=2 such that |pi(R^2)-VF_can(R^2)|<=C R log R. Its VF consumer explicitly also takes `ClassicalVonKochRHCriterion`. The complete wheel source F_R-D_R=li(R^2-1)-pi(R^2-1) remains OPEN at the same scale, with every virtual divisor retained until exact Euler compensation. Neither is identified with the Q_R below.

#### 1. BASELINE / DEPENDENCY RECEIPT

The strongest applicable certified explicit baseline located is `RHLean.Analysis.native_mertens_near_uniform_window_error_closed`:

```text
b_base=7/8-7/(64*N_pack),
forall epsilon>0, exists C_epsilon>=0, forall integer n>=1,
  |M(n)|<=C_epsilon*n^(b_base+epsilon).
```

The exact source declaration has no desired-bound argument. Its proof goes through the native Hecke boundary, original source construction, complete total-mass probe, anchored HIGH, modulus-one Hecke/Dirichlet product, native zero-boundary and Mertens converse. Positive losses have NOT been deleted. A fixed power requires explicitly spending a positive epsilon.

Inspected definitions give N_pack=ceil_nat(max(1,1/(6L)))+2 and N_old=ceil_nat(max(1,1/(3L)))+2, with the SAME positive `explicitFineLength` L. Thus N_pack<=N_old by monotonicity of max and ceiling, and 7/(64*N_pack)>1/(48*N_old). This is a valid comparison, not an identification of counts. It establishes the stated #1119 baseline as stronger than #1108's cited explicit boundary.

Actual hosted run [42552018910](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910), head 77ee815846d6d534c866f0752aa33b84c385610a, is completed/success. Its fetched job 128949473700 prints the five live proof-value closures, sizes 35358,35375,35736,35737,35753, and only propext, Classical.choice, Quot.sound. The audit source was read: it checks required live source dependencies, separately collects terminal axioms transitively, and checks the native arithmetic transfers. Repository-tree comparison found **988 pre-existing blobs unchanged** across RHLean, research/oai_434, relevant scripts/lean and workflow/toolchain selectors between that tested head and current main. This is reuse of exact-head evidence, not a new build at main.

Observed compiler: Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52. Observed pinned OpenAI upstream: 1581d4cbdd69a0faf34b2089614fe2a814316a6a; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. This invocation audited the source interfaces and existing hosted evidence, not an independent mathematical reproof of the upstream analytic corpus. No imported classical premise is silently equated with an arithmetic estimate.

#1130 is actually MERGED at current main; its earlier Lean-report UNMERGED label is stale. Run 42877550772 at exact head 4aa22782d10b3ad77dc970d6bb610eaab93a228c is completed/success. Inspected `principal_slot_signed_error` assumes Q>=480, norm(A)<=1, norm(eta)=1, Re(s)>=7/8 and proves a retained local signed remainder <=12 Q^(-11/8). It is not the complete paper endpoint. Referee-accepted RD, Referee's SR, Coordinator MD, and Analytic IR retain their different paper/review statuses; none replaces b_base here. The newer IR proposal remains independently unreviewed and unformalized in the retrieved handoff.

### C. Competing Hypotheses

All three tests were registered before execution on the genuine COMPLETE historical source:

```text
H_POS:   forall R>=2, forall 2<=g<R, C_R(g)>=0.
H_CROSS: forall R>=2, Q_R^2-sum_(g<R)C_R(g)^2<=0.
H_SPLIT: forall R>=2, C_R(1)*sum_(2<=g<R)C_R(g)<=0.
```

H_POS tests a proposed positivity transfer, H_CROSS tests the full inter-group interaction, and H_SPLIT tests the coarser two-sector mechanism. They are not interchangeable. The rival mechanism predicts mixed signs from the coprimality-restricted squarefree kernel and a possible sign change on coarsening. One exact strict failure rejects the corresponding universal assertion. No fitted constants, target-presupposing exceptional condition, randomized arithmetic, or retroactive hypothesis change was used.

This resumes the cross-route loss-recovery objective without repeating UC's unchanged transverse-energy tables, NC's reflected-prime tests, DR's event nonexpansion scan, or JC's daughter-band tests. It does not claim that another specialist asserted H_POS/H_SPLIT: these are the laboratory's explicitly proposed transfer tests.

### D. Experimental Design And Exact Carrier

For integer R>=2, X=R^2-1 and genuine Mobius coefficients, define

```text
A_R(a,b)=mu(a)mu(b)*floor(X/(ab)),       1<=a,b<R,
C_R(g)=sum_(gcd(a,b)=g) A_R(a,b),       1<=g<R,
Q_R=sum_g C_R(g)=2M(R-1)-M(X),
D_G(R)=sum_g C_R(g)^2,
O_G(R)=Q_R^2-D_G(R),
K_R=max_(0<=u<R) (M(u)-1)^2/(u+1).
```

Every ordered pair, diagonal, both strict orientations, integer floor, and squarefree-zero coefficient is retained. A floor equals the count of all k>=1 with abk<=X; distinct (a,b,k) labels are not silently deduplicated. Only zero-weight pairs are omitted computationally. The unit is present. The historical condition is STRICT a,b<R, and K includes u=0, forcing K>=1. K is not replaced by 1 in any reported ratio.

The gcd-square O_G is a scalar square-of-sum decomposition of Q_R, not an assertion that the floor kernel is positive semidefinite. It is NOT the lcm kernel floor(X/lcm(a,b)), empirical mean-centered covariance, or #915 zero-target NNS statistic. Relative to the original Mobius coefficients, Q is bilinear and its square is quartic; these orders are not confused.

Discovery: every R=2..256, 255 roots. Held-out, fixed in advance: 257,263,511,512,513,549,1023,1024,1025,2047,2048,2049,4095,4096,4097,5561, 16 roots. No additional roots were searched after seeing the result. The prime-resonance check below only annotates this same held-out set.

Primary C++: deterministic linear least-prime-factor/Mobius sieve through X_max=30,924,720, direct upper-triangle pair enumeration with exact multiplicity 1 or 2, gcd grouping, independent endpoint sums from the full sieve. Complexity O(X_max+sum R^2 log R) conservatively, storage O(X_max). Actual 38,417,708 nonzero ORDERED pair occurrences were reconstructed across the 271 roots.

Independent Python: trial-factor Mobius below max R, fixed-g construction using primitive coprime u,v with gcd(uv,g)=1, and the separate divisor recurrence M(n)=1-sum_(l=2..n)M(floor(n/l)), evaluated in constant-quotient blocks. It did NOT reuse the sieve's coefficient table or endpoint array. Every gcd vector, Q, D_G, O_G, K and earliest K maximizer matched. Trial primality is exhaustive to the integer square root in its documented small domain; no probable-prime claim is used.

Both implementations are by this author in this invocation. Algorithmic independence is not independent specialist acceptance or statistical independence.

### E. Executed Results

```text
Primary: PASS, 271 roots, 30,924,720 sieve limit, 38,417,708 pair occurrences.
Independent: PASS_INDEPENDENT_EXACT, all 271 full gcd ledgers identical.
Endpoint identity failures: 0. Historical-envelope mismatches: 0.
H_POS failures: 258 roots, including all 16 held-out roots.
H_SPLIT failures: 17,31,32,511,513,549; three held-out failures.
H_CROSS failures: 0; equality only at R=2,3 in the tested set.
Pair-product classification: 15,028 distinct pair-products, every R=2..64, PASS.
Held-out near-resonance admission checks: 16/16 exact witnesses, PASS.
Python syntax checks and warning-fatal C++ compilation: PASS.
```

For all listed roots R>=6, K_R=3/2, attained first at u=5. The programs actually checked the full historical maximum at EVERY root; this statement is finite, not a claim that K stays 3/2 forever.

| R | Q_R | C_R(1) | Sum g>=2 | D_G | O_G | Q_R^2/(R^2 K_R) |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| 15 | -7 | -12 | 5 | 223 | -174 | 98/675 |
| 17 | 5 | 4 | 1 | 173 | -148 | 50/867 |
| 47 | -12 | 34 | -46 | 6010 | -5866 | 96/2209 |
| 66 | 10 | 151 | -141 | 45696 | -45596 | 50/3267 |
| 257 | -6 | 210 | -216 | 76480 | -76444 | 24/66049 |
| 549 | -186 | -28 | -158 | 213476 | -178880 | 7688/100467 |
| 1024 | -265 | -645 | 380 | 2373931 | -2303706 | 70225/1572864 |
| 4096 | -249 | -4921 | 4672 | 63425699 | -63363698 | 20667/8388608 |
| 5561 | 2554 | -298 | 2852 | 19073482 | -12550566 | 13045832/92774163 |

Endpoint controls: R=549 has M(548)=3, M(301400)=192, and shifted endpoint ratio 72962/904203. R=5561 has M(5560)=5, M(30924720)=-2544, and shifted endpoint ratio 12954050/92774163. Thus the large latter Q is not an endpoint or shift convention error.

Extremes in the REGISTERED set: max_(R>=4) Q_R^2/D_G=3261458/9536741 at R=5561; max D_G/(R^2 K_R)=7616/1089 at R=66. The latter is nearly 7, but no constant 7 is fitted or proposed. The full Q ratio's maximum including degenerate roots is 9/4 at R=2; the shifted endpoint ratio's maximum is 1 there. Do not confuse these two normalizations.

### F. Exceptional Cases And Minimal Certificates

**GC1, smallest H_POS failure.** At R=15, g=2, the only nonzero squarefree a,b divisible by 2 are 2,6,10,14. Within gcd=2 the unequal pairs are all allowed, while only (2,2) remains on the diagonal. Hence

```text
C_15(2)=56-2*(18+11+8)+2*(3+2+1)=-6.
```

Both independent exhaustive scans certify no earlier root fails H_POS. The failure is not confined to roots below #1127's threshold: at R=47, C_47(2)=-58. This still does NOT refute #1127, whose fractional finite-wheel cofactor expression, mask and q range are different.

**GC2, smallest H_SPLIT failure.** At R=17 the complete nonzero gcd ledger is

```text
g:     1   2   3   5   6   7  10  11  13  14  15
C(g):  4  -6  -6  -3   8   1   2   2   1   1   1
```

Every omitted g has value zero. The sum is Q=5. The binary diagonal is 4^2+1^2=17, so its cross term is 25-17=+8. The fine diagonal is 173, so its cross term is 25-173=-148. The shared-sector diagonal is 157 and its internal cross term is 1-157=-156. Exactly -148=-156+8.

**All interactions restored, not just a favorable pair:**

| R | Original ordered-pair atom square sum | Within-gcd cross | Fine inter-gcd cross | Recombined Q^2 |
| --- | ---: | ---: | ---: | ---: |
| 15 | 108713 | -108490 | -174 | 49 |
| 17 | 181511 | -181338 | -148 | 25 |
| 549 | 209519833116 | -209519619640 | -178880 | 34596 |
| 5561 | 2208675199789504 | -2208675180716022 | -12550566 | 6522916 |

The first column treats the floor as the original pair weight; it is not the unit triple-occurrence diagonal. The original full weighted sum is preserved by either representation, but their diagonals differ, so they are explicitly distinguished.

At R=549 the shared-sector internal cross is -187728 and the binary cross is +8848. At R=5561 these are -10850774 and -1699792 respectively. Their sums reproduce the fine cross in both cases. This shows why negative local credit cannot be counted again after a group has been compressed.

### G. Hidden Variables And Arithmetic Classification

**GC3, supporting factorization lemma.** For a nonzero original pair let d=ab. Because a,b are squarefree, d is cube-free and has the unique form d=g^2*t, where g=gcd(a,b), g and t are squarefree, gcd(g,t)=1. Its sign is mu(a)mu(b)=mu(t), independent of the parity of g. Conversely a=g*u, b=g*v with uv=t, gcd(u,v)=1 and gcd(uv,g)=1 reconstructs every pair once.

Put N_g=floor((R-1)/g) and r_N(t)=#{u|t:1<=u<=N,1<=t/u<=N}. Then for squarefree g,

```text
C_R(g)=sum_(t<=N_g^2, t squarefree, gcd(t,g)=1)
          mu(t)*r_(N_g)(t)*floor((R^2-1)/(g^2*t)).
```

For nonsquarefree g the value is zero. At a fixed PAIR-PRODUCT d all admitted pairs therefore reinforce; cancellation in C(g) occurs between different squarefree kernels t. This is elementary unique factorization applied to the original masks, not a claimed new multiplicative theorem. The 15,028 exact pair-product checks independently match this formula to the original pair ledger.

Important distinction: d=ab is not the full physical integer n=abk counted by the floor. Different triples with the same n need NOT have the same g or sign. No once-only physical occurrence assertion is inferred from the pair-product classification.

A simple corrected positivity statement does survive on paper: if g is squarefree and every prime <=N_g divides g, then the only squarefree u<=N_g coprime to g is 1, so C_R(g)=floor(X/g^2)>0. In particular this holds for squarefree R/2<=g<R. The small-prime complement and squarefree-kernel parity, not merely the existence of a shared prime, control the sign. This proper-sector fact cannot imply H_POS for the omitted g.

**Exact coarsening law.** For any partition of the g labels into blocks B,

```text
O_coarse=O_fine-2*sum_B sum_(g<h in B) C(g)C(h).
```

It follows by expanding the block squares. If a block has negative internal interaction, coarsening moves that credit into its diagonal and can make the remaining cross positive. R=17 is a full-source arithmetic witness. The algebra is generic and credited as such; its application and exact minimal witnesses are this run's result.

### H. Mathematical Interpretation And Required Source Map

#### 2. FOUR-WAY SOURCE MAP

| Euler / finite AC | VF / actual primes | NNS / OAI | Square blocks |
| --- | --- | --- | --- |
| Original eulerFloorBilinearQ, X=R^2-1, strict a,b<R, unit and all ordered pairs. EXACT_IDENTITY to eulerSelfDualBilinear and 2M(R-1)-M(X). K_R is the literal lower critical envelope. | Complete finiteWheelFract minus finiteWheelSquareDeterministic equals li(X)-pi(X), with physical and virtual divisor compensation. This is its own EXACT_IDENTITY, NOT_EQUIVALENT to Q as a scalar formula. No bound transfer from gcd groups is proved. | O_G is the real scalar expansion of Q^2. No source-weight/mask-preserving map to original ideal-labelled LOW tuples, the Hecke principal response, or clipped #915 returned cells is available: OPEN_BRIDGE. An isometric rewriting supplies no sign gain. | Q returns to the COMPLETE prefix M(X), not one shell. `groupedSquareBlocks_sum` preserves a full prefix as exact shell reassembly; an isolated shell norm or sum of shell squares is NOT_EQUIVALENT to it. |

Prime/Mobius coupling: actual large-prime cofactor positivity in #1127 includes a finite Euler reference, erased unit, and its own q in [R,2R). C_R(g) instead has two historical mu factors, gcd= g, and product floor. Ideal Hecke phases are not rational mu coefficients. The native all-prefix Mertens theorem reaches Q through its exact endpoint identity as a ONE_WAY size consequence, not a coefficientwise prime/Hecke identification.

All weights here are integers/rationals; no logarithm or Li value was numerically substituted. A completed floor-Li radical defect from DR/RC is a different source. Their exact compensation and masks do not imply an inequality for C_R(g).

### I. Proposed Theorem And Falsification Status

GC5 is precisely the preregistered H_CROSS, with genuine mu and original floors:

```text
CONJECTURE: forall integer R>=2,
  (sum_(1<=a,b<R) mu(a)mu(b)floor((R^2-1)/(ab)))^2
    <= sum_(1<=g<R)
         (sum_(1<=a,b<R,gcd(a,b)=g)
            mu(a)mu(b)floor((R^2-1)/(ab)))^2.
```

There is no adjustable constant, no first-bad hypothesis, no empirical mean subtraction, and no claim that individual C(g) are positive. Finite evidence: all 255 discovery roots and all 16 predeclared held-outs, including genuine near-resonant configurations; equality R=2,3 and strict inequality for every tested R>=4. The strongest tested nondegenerate Q^2/D_G is at R=5561 as recorded above. The available proof is NONE; the all-scale status remains CONJECTURE. H_SPLIT cannot be used as its proof, since it is false.

Even a proof would leave `exists B>=0 forall R>=2: D_G(R)<=B R^2 K_R` unpaid. This second statement is not adopted as an independently supported theorem or asserted from the finite maximum. It may be much stronger than necessary. First test the sign conjecture decisively before investing in this norm; do not manufacture a new route from two open statements.

### J. Proof Impact And Loss-Recovery Audit

#### 3. FIRST SIGNED LOSS

| Exact location / input | Loss and discarded interaction | Quantitative tax / consumer | Recovery and remaining bill |
| --- | --- | --- | --- |
| eulerFloorBilinearQ in EULER_FRACTIONAL_COUPLED_20261027.lean | Replacing signed pair atoms by absolute values erases both within- and between-gcd interactions. | Elementary unsigned budget is <=X*(sum_(a<R)1/a)^2, order R^2 log^2 R; finite-C asks order R sqrt(K_R). | GC restores every signed group and cross exactly; no uniform estimate is supplied. |
| Proposed gcd split Q=sum_g C(g) | Triangle loses all O_G; dropping O_G in the favorable direction requires H_CROSS, not an identity. | Finite differences are explicit in F; no all-scale power improvement. | H_CROSS survives only finite testing. A uniform D_G bound remains OPEN. |
| Coarsening g>=2 into one block | Negative internal shared-sector cross is absorbed into the coarse square. | R=17 moves -156 and leaves +8; R=549 moves -187728 and leaves +8848. | Exact coarsening formula recovers accounting; H_SPLIT is REFUTED. Negative credit cannot be spent twice. |
| Attempt to apply #1127 positivity | Replaces the proper fractional wheel mask/reference by a distinct historical product/gcd kernel. | No valid output constant or exponent. | OPEN_BRIDGE; C_47(2)=-58 disproves a blanket positivity conclusion on this new carrier. #1127 itself remains valid. |
| Native baseline to historical Q | Triangle in Q=2M(R-1)-M(X) retains only a coarse power. | O_epsilon(R^(2*b_base+epsilon)); using K>=1 would discard actual feedback. | Nothing here recovers the required historical-normalized saving. |

#### 4. PAID RECOVERY TEST

Read and reuse `eulerSelfDualBilinear_eq_two_mertens_sub_endpoint`, its actual Newton coefficient reconstruction and complete divisor-antidiagonal Fubini. These theorems justify the tested source and its endpoint checks, not a sign assertion. `eulerFractionBilinearQ_eq_diagonal_add_twice_off` supplies full signed fractional accounting on its original carrier; it does not imply the separate gcd-square inequality.

#1127 cofactor positivity and #1128 shared-prime resonance are proper-source results. The former has a different mask/kernel; the latter limits naive phase decorrelation, not this rational gcd Gram. #1130's local signed principal remainder and DR/RC's radical completion were checked as potential recoveries but have no original-coefficient transfer to the proposed H_CROSS or D_G bound. Marking that transfer OPEN is essential.

The actual terminal consumer is already available: `EulerSelfDualFiniteCStatement` gives one C before R and every valid K; `squareRootEndpointAmplification_of_eulerFiniteC` returns A=(C+3)^2; `riemannHypothesis_of_eulerSelfDualFiniteC` consumes the internal Mertens-energy chain. If both H_CROSS and an independently proved uniform D_G<=B R^2 K_R held, they would give C=sqrt(B), then that existing chain. **Neither premise is proved here.** Writing this conditional consumer is not new arithmetic progress or an RH proof.

#### 5. NET RESULT / ADMISSION VERDICT

The exact counterexamples retire the two proposed sign shortcuts. The refined finite survival is a falsifiable research candidate. The elementary factorization/coarsening formulas explain the result, but do not meet the directive's threshold for a newly accepted route or a new global exponent. Canonical VF, complete wheel, finite A/C, zero-log amplification, complete CORR4 and RH remain OPEN.

### K. Falsification, Numerical Control And Reproducibility

All hypothesis decisions, floors, signs, gcds, primality, envelope comparisons, certificates and reported ratios use exact integers/rationals. There is no floating-point mathematical sign or inequality claim. Elapsed times alone use ordinary clocks. C++ uses 64-bit integer arithmetic; the independent group-square and cross calculations use Python integers, and all agree. NumPy integer products and row sums stay within 64-bit at the stated finite domain. No numerical enclosure for li, log or a zeta zero was needed.

The small certificates are independently hand-checkable. At R=15, 56-74+12=-6. At R=17, the displayed vector sums to 5 and its squares to 173. Finer masks and the complete source are retained; these witnesses satisfy the registered all-root hypotheses, not a fully specified first-bad predicate.

Actual environment: Linux x86_64; Python **3.12.14** (observed, overriding the environment description's 3.12.13), NumPy 2.3.5; g++ 13.3.0. Primary measured compute/serialization time 0.898468 seconds; final independent verification 3.5820056889999705 seconds. No benchmark claim is made from these short timings. The second verifier run added explicit independently computed D_G/O_G checks; it was verification of unchanged hypotheses, not a new search or cherry-picked result.

Commands actually executed:

```bash
g++ -O2 -std=c++17 -Wall -Wextra -Werror gc_probe.cpp -o gc_probe
./gc_probe gc_primary.json
python gc_verify.py gc_primary.json gc_verified.json
python gc_certificates.py
python -m py_compile gc_verify.py gc_certificates.py
```

| Executed file | SHA-256 |
| --- | --- |
| gc_probe.cpp | 6c5c1889cee009b4548459f81bb1a718db530ee84079f51d7dc32c7bbee1e8d1 |
| gc_verify.py | c81e81c2ad689a5b43a049f2c9ec6220a7e0b98fcf95a127085c9648b0da7784 |
| gc_certificates.py | 47a02b4ce70d8f1b9b17d1a3783c3a3547f4ff1ce760fc666dd5aace7d0b868f |
| gc_primary.json | 8cb6188b24040d340bebb632a9ebc000611fbb6e92eaa5c14e9005d0c15c93eb |
| gc_verified.json | d5b945cd730a5a7faa361ee417c6e8c29c75e721bef5c7cacec26adb93110b8d |
| gc_certificates.json | a8ebc027901abb71c2ea16aa9f66e509035bc3a477abee065b1be338f31299b9 |

Output hashes containing elapsed time may change on rerun; source hashes and exact arithmetic records are reproducible. Complete programs and the verified/certificate outputs are embedded below. The primary output can be regenerated, including every full gcd vector.

To satisfy the near-resonance regression without inventing a phase identification, exact trial-prime witnesses were found for all 16 held-out roots using the INSPECTED #1128 predicates: p in [R/2,R), q in [R,2R), r in [2R,4R), r=4p+-1, pq<=R^2-1 and qr<=4R^2-1. Example R=549: (p,q,r)=(277,557,1109); R=5561: (2803,5563,11213). The exact positive relative ratio errors are 300569/333952031 and 10305437/115575989683, each <=1/R. The existing theorem then bounds the corresponding logarithmic phase difference; no logarithm was approximated. This merely confirms the registered roots include genuine near-resonant geometry; it does not map those different prime atoms into C_R(g) or claim causation.

### L. Specialist Handoffs And Research Continuity

**Proof Architect:** GC1/GC2 eliminate positivity-by-shared-factor and binary anti-alignment as unconditional recovery steps on the literal Q carrier. GC5 is a small precisely scoped conjecture, not a new route. Do not replace the independently progressing OAI MD/IR work with it. The first complete-source unpaid item remains a uniform original signed estimate, not new bookkeeping.

**Owner Payment:** DR's same-product reinforcement has an analogous but distinct pair-product explanation here. Retain the distinction between d=ab and n=abk. A #915 or floor-Li mask may change every grouping; no source admission has been inferred from divisibility. GC2 is an explicit warning against spending an internal cross term after compressing its sector.

**Analytic Type II:** There is no transfer of marked ideal moments or the #1130 principal response to the gcd ledger without a coefficient map. Continue the actual complete MD/IR return review independently. For the native source, a claimed Gram saving must state whether its diagonal is pair-weighted, unit-triple-weighted, fine-gcd, or coarse-sector.

**Finite Wheel:** Referee-check GC3 and test whether H_CROSS has a genuine arithmetic proof or counterexample. #1127 positivity does not apply; R=47 gives a source-specific check within its numerical root range. Neither the high-g positive sector nor existing daughter-visible bands covers the whole ledger. RC3's auxiliary completion bound remains a separate supporting result.

**Adversarial Referee:** Independently check the R=15 and R=17 certificates and the exact pair-to-gcd carrier before adopting any conjecture. The highest-risk inference is treating a negative fine cross as evidence for negative binary cross. Finite equality and source identities should be accepted only at their stated scope. All new paper arguments remain self-audited, not independently accepted.

**Lean Verification:** No new global theorem is supplied. A small exact counterexample or the generic coarsening adapter may be useful only if it prevents a live invalid transfer; do not create a filler proof task. GC5 is a conjecture, never a formalization premise disguised as a fact. Reuse existing endpoint/Fubini/Gram theorems.

TODAY=AVAILABLE for all seven roles at immutable intake agent-reports e715cfda8aa5e6cb42501fb155592545b9d260af; YESTERDAY=CARRY_FORWARD for November 9. Read relevant findings, current review states and resume points. Earlier report descriptions of #1127/#1130 as unmerged are superseded by live main/PR evidence.

| Role | November 9 carried finding | November 10 consumed finding |
| --- | --- | --- |
| Coordinator | CD fixed-cutoff failures and prime-rank restriction; proper packet only. | CR source audit and MD complete Mellin-symbol proposal; distinguish its paper acceptance from Lean. |
| Owner | CF large-prime cofactor positivity and same-q reinforcement; later formalized only at its true scope. | BR true event admission; DR radical response, physical-fibre reinforcement, and scoped contraction failures. |
| Analytic | ZD proper-band zero-density transfer; no full endpoint gain. | RD paper acceptance and IR infinite-response proposal; IR not a new certified baseline. |
| Wheel | RF exact reflected-prime shared-factor classification and bounded proper band. | JC omitted upper bands; RC complete auxiliary defect and remaining inverse/prime-side costs. |
| Census | NC nearest-centre sign failures and controlled subset, not full source. | UC unsaturated transverse failures; no unchanged tables rerun. |
| Referee | AP valid adaptive prefix and failures of overbroad fixed-prefix claims. | LC scopes UC; SR accepts RD on paper and separately proposes its own extension. |
| Lean | #1127 cofactor proof evidence, now merged. | #1130 local signed remainder, now merged; endpoint assembly not yet certified. |

External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry after October 18. EXT-20261018-PNT-1 and the earlier #915 source/denominator warnings remain applicable; they neither supply a gcd sign rule nor authorize source changes. Scheduled execution of another role is never inferred merely from a filename or timetable.

### M. Ranked Experimental Hypothesis Portfolio

| Rank / disposition | Exact hypothesis and motivation | Evidence and counterevidence | Independent ingredient / required theorem / next discriminator |
| --- | --- | --- | --- |
| 1 / CONTINUE cautiously | GC5 H_CROSS on all R, motivated by full inter-gcd cancellation. | 271 finite roots survive; no proof; no surrogate-coefficient claim. H_SPLIT fails and cannot establish it. | Need an actual Mobius/coprime-kernel restriction forcing total inter-gcd cross <=0. Next test is targeted at large Q^2/D_G, not another routine prime census. |
| 2 / REJECT as stated | H_POS and H_SPLIT unconditional positivity/anti-alignment transfer. | Exact smallest failures R=15 and 17; held-out failures persist. | Corrected high-g positivity is only a proper sector. Any repair must specify new hypotheses and restore the complement. |
| 3 / SUSPEND as a proposed route | A uniform D_G<=B R^2 K_R would combine with GC5 into finite C. | Only finite ratios known; observed maximum 7616/1089 is not an all-scale constant. | No independent uniform norm supplier is available. Do not spend a run fitting B or counting this open reformulation as a new mechanism. |

The portfolio does not replace the team's independent VF, CODIV, OAI-NNS, FINITE-AC, CORR4, MU-LIFT or NYMAN routes. No unrelated route coverage is fabricated.

### N. Next-Run Resume Capsule

```text
RUN=20261110-census-2/GC; TRIGGER=scheduled 19:00:01 EST; RUN_ID_UNAVAILABLE.
AUTHORITY=main f7947bee036c4dddb0c36fc9f53ab46b4fa90995.
ACK=CROSS_ROUTE_SIGNED_RECOVERY_V1.
REGISTERED_DOMAIN=R=2..256 plus the 16 explicitly listed held-outs.
EXACT_MAX_INTEGER=30,924,720; ALL_ROOTS_VERIFIED=271.
NEW_COUNTEREXAMPLES=H_POS at (R,g)=(15,2), C=-6;
                    H_SPLIT at R=17, C1=4, Crest=1.
GROUPING_REVERSAL=R17: fine cross -148, binary cross +8, internal -156.
REQUIRED_REGRESSIONS=R549 and R5561 complete source/K/squares PASS.
SURVIVING_CONJECTURE=H_CROSS, finite evidence only.
PAID_INPUT=actual eulerSelfDual endpoint identity, original signed Gram algebra.
UNPAID=all-scale H_CROSS and independent D_G historical-normalized control.
BASELINE=#1119 exact-head evidence reused; no new global exponent.
NEXT_EXPERIMENT=after fresh authority/handoff intake, preregister a targeted
  falsification window around the largest observed Q^2/D_G excursion R=5561;
  compare nearby untested roots and the gcd groups responsible, with exact K.
  Do not rerun the 271 unchanged roots except for changed definitions/verification.
REVIEW=SELF_AUDIT, independent specialist review pending; NO_LOCAL_LEAN.
PUBLICATION=verify immutable commit/readback separately; no success presumed.
```

The next test must freeze a finite window and failure rule before execution; its purpose is to attack GC5, not to fit a universal constant. All computation sessions for this invocation finished. No source, instruction, other report, issue, branch, PR, workflow, merge, schedule or permission was modified, and no agent was launched.


### Material Source Receipts - GC

All following files were fetched at main f7947bee036c4dddb0c36fc9f53ab46b4fa90995 during this invocation. Line locations are best recovered from the immutable linked source, not a moving branch.

| Path | Blob SHA |
| --- | --- |
| AGENTS.md | c9c89f01b90b526de9f3e8ea92478e36504711b6 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md | e922d4ba9362a1ae196af8f6de88f7417f92087c |
| docs/COORDINATE_ATLAS.md | cd0419d00a37739fe5a292f5cb738e33213949d5 |
| docs/PROOF_DEPENDENCY_DAG.md | eee764cefe70035a9f6c7df26ad787fbfd0fb233 |
| research/EULER_FRACTIONAL_COUPLED_20261027.lean | e6c4b1690e497760d366e36b28a1f7aa60e19f85 |
| research/EULER_SELF_DUAL_POINTWISE_20261027.lean | c327c556f39ee7014fd774b24d0f95a1ece050e0 |
| research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean | e97561ef330a9996fd807d8910369f0698147b01 |
| research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| RHLean/Proof/SquareRootLegalAncestryGramReduction.lean | 1270d4d91c53b50b110d10014f223f427fb7a575 |
| RHLean/Proof/SquareRootMertensEndpointAmplification.lean | 7793d7bfd842348facf62a7ad856bc802ffcd15c |
| RHLean/Proof/SquareRootAmplificationClosure.lean | 8949e3925695353635f67b2b611a9c21bacbd9ea |
| research/oai_434/VF919WindowErrorClosure.lean | f629db1b2b65d6ec042ac9432397d4b6316200c6 |
| research/oai_434/VF919ExplicitFixedSourceSlotCount.lean | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |
| research/oai_434/VF919ExplicitSquareBlockPacking.lean | 32999039fdeea99c58a070c1c4ee9c140720dd44 |
| scripts/lean/window_error_closure/WindowErrorClosureAudit.lean | 1f17f9401a63d16227db2e2aad020b9f74bc5f4e |
| research/oai_434/VF919PrincipalSignedRemainder.lean | a41fee91754d5f6e5606f3f6f3dfe66031d81cbf |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/FiniteWheelCofactorPositivity.lean | f83a3daefc2b9d603014af912ec82b4a7f52cfac |
| research/DyadicPrimeNearResonance.lean | f416e0149b73656e30a7f68a3934a937353d3f8d |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

Report intake commit: e715cfda8aa5e6cb42501fb155592545b9d260af. Coordinator 00/90 paths had identical blobs on each date. All seven role reports were retrieved in full, then the relevant findings, claims, acceptance states, and resume sections were read.

| Date | Role report | Blob SHA |
| --- | --- | --- |
| 2026-11-09 | 00-coordinator-am.md | 6fba43130391ad4a606aa3809c20f344d668c709 |
| 2026-11-09 | 10-owner-payment.md | 643e8a004d9d8e0be102b03e2f79bb3b217ae916 |
| 2026-11-09 | 20-analytic-type-ii.md | d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3 |
| 2026-11-09 | 30-finite-wheel.md | 0624246d03b19cf76c01e186b7d868a248d896ef |
| 2026-11-09 | 40-prime-census.md | 8c927cc6c323533ba1cfd369404b25aa4f9cef91 |
| 2026-11-09 | 50-adversarial-referee.md | a5d0192eb31c0efb3767187a7752f1a0d07f8534 |
| 2026-11-09 | 60-lean-verification.md | 8b60c6136ac151774be2db0aee8f543f286b53aa |
| 2026-11-10 | 00-coordinator-am.md | 14190fe06982de80c5904b156525e3cda15d8f03 |
| 2026-11-10 | 10-owner-payment.md | 84afec90414b2394a61b51df46c07b6b540e5942 |
| 2026-11-10 | 20-analytic-type-ii.md | 7ed3a39bec4796f4173b692064af872ea8035048 |
| 2026-11-10 | 30-finite-wheel.md | 62406503a1ddbbf9330abcdc4cf761f7fbf05795 |
| 2026-11-10 | 40-prime-census.md | 8a89d1a899850e39320a96bf35a6f221060fc8a7 |
| 2026-11-10 | 50-adversarial-referee.md | 988a4a74e40a48d8d4c868c03263e66c129a6f1a |
| 2026-11-10 | 60-lean-verification.md | d2f8fd346b7aaab57f3bd3676ed7b1d8c8abb3f8 |


### Exact Executed Programs - GC

These are the final executed source bytes. Extract each named block into its stated filename in one directory and execute the commands in K. No unstated remote data is needed.

#### gc_probe.cpp

```cpp
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <vector>

using I = long long;

int main(int argc, char** argv) {
    if (argc != 2) return 2;
    const auto start = std::chrono::steady_clock::now();
    std::vector<int> roots;
    for (int r = 2; r <= 256; ++r) roots.push_back(r);
    for (int r : {257,263,511,512,513,549,1023,1024,1025,2047,2048,
                  2049,4095,4096,4097,5561}) roots.push_back(r);
    std::sort(roots.begin(), roots.end());
    const int limit = roots.back() * roots.back() - 1;
    std::vector<int> least(limit + 1), primes;
    std::vector<int8_t> mu(limit + 1);
    mu[1] = 1;
    for (int n = 2; n <= limit; ++n) {
        if (!least[n]) { least[n] = n; primes.push_back(n); mu[n] = -1; }
        for (int p : primes) {
            if (I(n) * p > limit) break;
            least[n*p] = p;
            if (n % p == 0) { mu[n*p] = 0; break; }
            mu[n*p] = -mu[n];
        }
    }
    std::vector<I> history(roots.back()), endpoint(roots.size());
    I mertens = 0;
    size_t cursor = 0;
    for (int n = 1; n <= limit; ++n) {
        mertens += mu[n];
        if (n < int(history.size())) history[n] = mertens;
        if (cursor < roots.size() && n == roots[cursor]*roots[cursor]-1)
            endpoint[cursor++] = mertens;
    }
    std::ofstream out(argv[1]);
    out << "{\"limit\":" << limit << ",\"rows\":[";
    I pair_count = 0;
    for (size_t j = 0; j < roots.size(); ++j) {
        const int r = roots[j];
        const I x = I(r)*r-1;
        std::vector<I> groups(r);
        I atom_diagonal = 0;
        for (int a = 1; a < r; ++a) if (mu[a]) {
            for (int b = a; b < r; ++b) if (mu[b]) {
                const I atom = I(mu[a])*mu[b]*(x/(I(a)*b));
                const int multiplicity = a == b ? 1 : 2;
                groups[std::gcd(a,b)] += multiplicity*atom;
                atom_diagonal += multiplicity*atom*atom;
                pair_count += multiplicity;
            }
        }
        I q = 0, energy = 0;
        for (I v : groups) { q += v; energy += v*v; }
        if (q != 2*history[r-1]-endpoint[j]) return 3;
        I kn = 1, kd = 1, ku = 0;
        for (int u = 1; u < r; ++u) {
            const I numerator = (history[u]-1)*(history[u]-1);
            if (numerator*kd > kn*(u+1)) { kn = numerator; kd = u+1; ku = u; }
        }
        const I divisor = std::gcd(kn,kd); kn /= divisor; kd /= divisor;
        if (j) out << ',';
        out << "{\"R\":" << r << ",\"X\":" << x << ",\"Q\":" << q
            << ",\"M_history\":" << history[r-1] << ",\"M_endpoint\":" << endpoint[j]
            << ",\"K_num\":" << kn << ",\"K_den\":" << kd << ",\"K_at\":" << ku
            << ",\"group_energy\":" << energy << ",\"cross\":" << q*q-energy
            << ",\"atom_diagonal\":" << atom_diagonal << ",\"groups\":[";
        bool first = true;
        for (int g=1; g<r; ++g) if (groups[g]) {
            if (!first) out << ',';
            first = false;
            out << '[' << g << ',' << groups[g] << ']';
        }
        out << "]}";
    }
    const double seconds = std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    out << "],\"ordered_nonzero_pairs\":" << pair_count << ",\"elapsed_seconds\":" << seconds << "}\n";
    std::cout << "PASS roots=" << roots.size() << " limit=" << limit
              << " pairs=" << pair_count << " seconds=" << seconds << '\n';
}
```

#### gc_verify.py

```python
import argparse
from fractions import Fraction
from functools import cache
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path
import platform
import time

import numpy as np


def trial_mu(n):
    parity = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            parity = -parity
            if n % p == 0:
                return 0
        p += 1
    return -parity if n > 1 else parity


@cache
def mertens(n):
    if n == 0:
        return 0
    total, left = 1, 2
    while left <= n:
        quotient = n // left
        right = n // quotient
        total -= (right-left+1) * mertens(quotient)
        left = right + 1
    return total


def independent_groups(r, mu):
    # Primitive coprime pairs are built at fixed gcd; no pair-gcd ledger is reused.
    x = r*r-1
    result = {}
    for g in range(1, r):
        if not mu[g]:
            continue
        u = np.array([n for n in range(1, (r-1)//g+1)
                      if mu[n] and gcd(n,g) == 1], dtype=np.int64)
        signs = mu[u]
        total = 0
        for index, a in enumerate(u):
            mask = np.gcd(a, u) == 1
            total += int(np.sum(signs[index] * signs[mask] * (x // (g*g*a*u[mask])),
                                dtype=np.int64))
        if total:
            result[g] = total
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('input')
    parser.add_argument('output')
    args = parser.parse_args()
    start = time.perf_counter()
    raw = json.loads(Path(args.input).read_text())
    rows = raw['rows']
    mu = np.array([0]+[trial_mu(n) for n in range(1, max(x['R'] for x in rows))],
                  dtype=np.int64)
    history = np.cumsum(mu)
    failures = {'H_POS': [], 'H_CROSS': [], 'H_SPLIT': []}
    records = []
    for row in rows:
        r = row['R']
        groups = independent_groups(r, mu)
        assert groups == dict(row['groups']), (r, groups, row['groups'])
        q = sum(groups.values())
        assert row['group_energy'] == sum(value*value for value in groups.values())
        assert row['cross'] == q*q-row['group_energy']
        end = mertens(r*r-1)
        assert end == row['M_endpoint'] and q == 2*int(history[r-1])-end
        kval = max(Fraction((int(history[u])-1)**2, u+1) for u in range(r))
        assert kval == Fraction(row['K_num'], row['K_den'])
        assert next(u for u in range(r) if Fraction((int(history[u])-1)**2,u+1)==kval)==row['K_at']
        c1 = groups.get(1,0)
        rest = q-c1
        neg = [[g,c] for g,c in groups.items() if g>=2 and c<0]
        if neg: failures['H_POS'].append({'R':r,'negative_groups':neg})
        if row['cross']>0: failures['H_CROSS'].append({'R':r,'cross':row['cross']})
        if c1*rest>0: failures['H_SPLIT'].append({'R':r,'C1':c1,'rest':rest})
        records.append({'R':r,'Q':q,'C1':c1,'rest':rest,'group_energy':row['group_energy'],
                        'cross':row['cross'],'K':str(kval),'K_at':row['K_at'],
                        'M_history':row['M_history'],'M_endpoint':end,
                        'Q_ratio':str(Fraction(q*q,r*r)/kval),
                        'endpoint_ratio':str(Fraction((end-1)**2,r*r)/kval),
                        'negative_group_count':len(neg)})
    summary = {'status':'PASS_INDEPENDENT_EXACT','roots':len(rows),
               'python':platform.python_version(),'numpy':np.__version__,
               'recurrence_cache':str(mertens.cache_info()),
               'failures':{k:{'count':len(v),'first':v[0] if v else None,
                              'held_out_count':sum(x['R']>256 for x in v)} for k,v in failures.items()},
               'largest_cross':max(records,key=lambda x:x['cross']),
               'largest_Q_ratio':max(records,key=lambda x:Fraction(x['Q_ratio'])),
               'largest_endpoint_ratio':max(records,key=lambda x:Fraction(x['endpoint_ratio'])),
               'held_out': [x for x in records if x['R']>256],
               'first_failures_detail': [row for row in rows if row['R'] in
                                        {v[0]['R'] for v in failures.values() if v}],
               'elapsed_seconds':time.perf_counter()-start,
               'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(args.output).write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__ == '__main__':
    main()
```

#### gc_certificates.py

```python
from collections import defaultdict
from fractions import Fraction
from math import gcd, isqrt
from pathlib import Path
import json

from gc_verify import trial_mu


def prime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n)+1))


rows = json.loads(Path('gc_primary.json').read_text())['rows']
selected = [x for x in rows if x['R'] >= 4]
ratio = lambda row: Fraction(row['Q']**2, row['group_energy'])
energy_ratio = lambda row: Fraction(row['group_energy']*row['K_den'],
                                   row['R']**2*row['K_num'])
certificates = []
for r in (15,17,549,5561):
    row = next(x for x in rows if x['R']==r)
    groups = dict(row['groups'])
    c1, total = groups.get(1,0), row['Q']
    shared = total-c1
    shared_diagonal = row['group_energy']-c1*c1
    shared_cross = shared*shared-shared_diagonal
    binary_cross = 2*c1*shared
    assert shared_cross+binary_cross==row['cross']
    assert row['atom_diagonal']+(row['group_energy']-row['atom_diagonal'])+row['cross']==total*total
    cert = {'R':r,'C1':c1,'shared_sum':shared,
            'shared_group_diagonal':shared_diagonal,
            'shared_cross':shared_cross,'binary_cross':binary_cross,
            'fine_cross':row['cross'], 'fine_diagonal':row['group_energy'],
            'atom_diagonal':row['atom_diagonal'],
            'within_gcd_cross':row['group_energy']-row['atom_diagonal'],
            'Q_squared':total*total,'Q2_over_DG':str(ratio(row)),
            'DG_over_R2K':str(energy_ratio(row))}
    if r==15:
        # Multiply after taking the integer floor, including negative weights.
        cert['g2_ordered_atoms'] = [[a,b,trial_mu(a)*trial_mu(b)*((r*r-1)//(a*b))]
              for a in range(1,r) for b in range(1,r)
              if gcd(a,b)==2 and trial_mu(a)*trial_mu(b)]
        assert sum(x[2] for x in cert['g2_ordered_atoms'])==-6
    certificates.append(cert)

product_checks = 0
for r in range(2,65):
    x = r*r-1
    signs = defaultdict(set)
    counts = defaultdict(int)
    for a in range(1,r):
        for b in range(1,r):
            s = trial_mu(a)*trial_mu(b)
            if s:
                signs[a*b].add(s)
                counts[a*b] += 1
    rebuilt = defaultdict(int)
    for product, ss in signs.items():
        assert len(ss)==1
        g = max(d for d in range(1,isqrt(product)+1) if product % (d*d)==0)
        t = product//(g*g)
        assert trial_mu(g)!=0 and trial_mu(t)!=0 and gcd(g,t)==1
        assert ss=={trial_mu(t)}
        n = (r-1)//g
        count = sum(t % u==0 and t//u<=n for u in range(1,n+1))
        assert count==counts[product]
        rebuilt[g] += trial_mu(t)*count*(x//product)
        product_checks += 1
    assert {g:v for g,v in rebuilt.items() if v}==dict(next(z for z in rows if z['R']==r)['groups'])

resonance = []
for row in rows:
    R = row['R']
    if R<=256: continue
    X,Y = R*R-1,4*R*R-1
    witness = None
    for p in range((R+1)//2,R):
        if not prime(p): continue
        for rr in (4*p-1,4*p+1):
            if not (2*R<=rr<4*R and prime(rr)): continue
            for q in range(R,min(2*R-1,X//p,Y//rr)+1):
                if prime(q):
                    error = Fraction(abs(X*rr-Y*p),Y*p)
                    assert error and error<=Fraction(1,R)
                    witness={'R':R,'p':p,'q':q,'r':rr,'pq':p*q,'qr':q*rr,
                             'relative_phase_ratio_error':str(error)}
                    break
            if witness: break
        if witness: break
    resonance.append(witness or {'R':R,'witness':None})

result={'certificates':certificates,'pair_product_checks':product_checks,
        'pair_product_scope':'Every R=2..64, all nonzero original pairs; pair product is NOT final triple product.',
        'all_nontrivial_cross_max':max(row['cross'] for row in selected),
        'largest_nontrivial_Q2_over_DG':{'R':max(selected,key=ratio)['R'],
                                       'ratio':str(max(map(ratio,selected)))},
        'largest_DG_over_R2K':{'R':max(rows,key=energy_ratio)['R'],
                              'ratio':str(max(map(energy_ratio,rows)))},
        'H_SPLIT_failing_roots':[row['R'] for row in rows
             if dict(row['groups']).get(1,0)*(row['Q']-dict(row['groups']).get(1,0))>0],
        'resonance':resonance,'status':'PASS_EXACT_CERTIFICATES'}
Path('gc_certificates.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
```

### Recorded Exact Outputs - GC

#### gc_verified.json

```json
{
  "status": "PASS_INDEPENDENT_EXACT",
  "roots": 271,
  "python": "3.12.14",
  "numpy": "2.3.5",
  "recurrence_cache": "CacheInfo(hits=4632122, misses=17869, maxsize=None, currsize=17869)",
  "failures": {
    "H_POS": {
      "count": 258,
      "first": {
        "R": 15,
        "negative_groups": [
          [
            2,
            -6
          ]
        ]
      },
      "held_out_count": 16
    },
    "H_CROSS": {
      "count": 0,
      "first": null,
      "held_out_count": 0
    },
    "H_SPLIT": {
      "count": 6,
      "first": {
        "R": 17,
        "C1": 4,
        "rest": 1
      },
      "held_out_count": 3
    }
  },
  "largest_cross": {
    "R": 2,
    "Q": 3,
    "C1": 3,
    "rest": 0,
    "group_energy": 9,
    "cross": 0,
    "K": "1",
    "K_at": 0,
    "M_history": 1,
    "M_endpoint": -1,
    "Q_ratio": "9/4",
    "endpoint_ratio": "1",
    "negative_group_count": 0
  },
  "largest_Q_ratio": {
    "R": 2,
    "Q": 3,
    "C1": 3,
    "rest": 0,
    "group_energy": 9,
    "cross": 0,
    "K": "1",
    "K_at": 0,
    "M_history": 1,
    "M_endpoint": -1,
    "Q_ratio": "9/4",
    "endpoint_ratio": "1",
    "negative_group_count": 0
  },
  "largest_endpoint_ratio": {
    "R": 2,
    "Q": 3,
    "C1": 3,
    "rest": 0,
    "group_energy": 9,
    "cross": 0,
    "K": "1",
    "K_at": 0,
    "M_history": 1,
    "M_endpoint": -1,
    "Q_ratio": "9/4",
    "endpoint_ratio": "1",
    "negative_group_count": 0
  },
  "held_out": [
    {
      "R": 257,
      "Q": -6,
      "C1": 210,
      "rest": -216,
      "group_energy": 76480,
      "cross": -76444,
      "K": "3/2",
      "K_at": 5,
      "M_history": -1,
      "M_endpoint": 4,
      "Q_ratio": "24/66049",
      "endpoint_ratio": "6/66049",
      "negative_group_count": 37
    },
    {
      "R": 263,
      "Q": -66,
      "C1": 134,
      "rest": -200,
      "group_energy": 58928,
      "cross": -54572,
      "K": "3/2",
      "K_at": 5,
      "M_history": -1,
      "M_endpoint": 64,
      "Q_ratio": "2904/69169",
      "endpoint_ratio": "2646/69169",
      "negative_group_count": 33
    },
    {
      "R": 511,
      "Q": -30,
      "C1": -4,
      "rest": -26,
      "group_energy": 213948,
      "cross": -213048,
      "K": "3/2",
      "K_at": 5,
      "M_history": -5,
      "M_endpoint": 20,
      "Q_ratio": "600/261121",
      "endpoint_ratio": "722/783363",
      "negative_group_count": 61
    },
    {
      "R": 512,
      "Q": -32,
      "C1": 21,
      "rest": -53,
      "group_energy": 208112,
      "cross": -207088,
      "K": "3/2",
      "K_at": 5,
      "M_history": -4,
      "M_endpoint": 24,
      "Q_ratio": "1/384",
      "endpoint_ratio": "529/393216",
      "negative_group_count": 61
    },
    {
      "R": 513,
      "Q": -46,
      "C1": -10,
      "rest": -36,
      "group_energy": 219130,
      "cross": -217014,
      "K": "3/2",
      "K_at": 5,
      "M_history": -4,
      "M_endpoint": 38,
      "Q_ratio": "4232/789507",
      "endpoint_ratio": "2738/789507",
      "negative_group_count": 61
    },
    {
      "R": 549,
      "Q": -186,
      "C1": -28,
      "rest": -158,
      "group_energy": 213476,
      "cross": -178880,
      "K": "3/2",
      "K_at": 5,
      "M_history": 3,
      "M_endpoint": 192,
      "Q_ratio": "7688/100467",
      "endpoint_ratio": "72962/904203",
      "negative_group_count": 69
    },
    {
      "R": 1023,
      "Q": -289,
      "C1": -646,
      "rest": 357,
      "group_energy": 2334167,
      "cross": -2250646,
      "K": "3/2",
      "K_at": 5,
      "M_history": -3,
      "M_endpoint": 283,
      "Q_ratio": "167042/3139587",
      "endpoint_ratio": "17672/348843",
      "negative_group_count": 124
    },
    {
      "R": 1024,
      "Q": -265,
      "C1": -645,
      "rest": 380,
      "group_energy": 2373931,
      "cross": -2303706,
      "K": "3/2",
      "K_at": 5,
      "M_history": -4,
      "M_endpoint": 257,
      "Q_ratio": "70225/1572864",
      "endpoint_ratio": "1/24",
      "negative_group_count": 124
    },
    {
      "R": 1025,
      "Q": -296,
      "C1": -672,
      "rest": 376,
      "group_energy": 2390558,
      "cross": -2302942,
      "K": "3/2",
      "K_at": 5,
      "M_history": -4,
      "M_endpoint": 288,
      "Q_ratio": "175232/3151875",
      "endpoint_ratio": "98/1875",
      "negative_group_count": 124
    },
    {
      "R": 2047,
      "Q": -176,
      "C1": -694,
      "rest": 518,
      "group_energy": 4986104,
      "cross": -4955128,
      "K": "3/2",
      "K_at": 5,
      "M_history": 6,
      "M_endpoint": 188,
      "Q_ratio": "61952/12570627",
      "endpoint_ratio": "69938/12570627",
      "negative_group_count": 255
    },
    {
      "R": 2048,
      "Q": -214,
      "C1": -691,
      "rest": 477,
      "group_energy": 4894358,
      "cross": -4848562,
      "K": "3/2",
      "K_at": 5,
      "M_history": 7,
      "M_endpoint": 228,
      "Q_ratio": "11449/1572864",
      "endpoint_ratio": "51529/6291456",
      "negative_group_count": 254
    },
    {
      "R": 2049,
      "Q": -249,
      "C1": -706,
      "rest": 457,
      "group_energy": 4857571,
      "cross": -4795570,
      "K": "3/2",
      "K_at": 5,
      "M_history": 7,
      "M_endpoint": 263,
      "Q_ratio": "13778/1399467",
      "endpoint_ratio": "137288/12595203",
      "negative_group_count": 254
    },
    {
      "R": 4095,
      "Q": -308,
      "C1": -4982,
      "rest": 4674,
      "group_energy": 63898372,
      "cross": -63803508,
      "K": "3/2",
      "K_at": 5,
      "M_history": -19,
      "M_endpoint": 270,
      "Q_ratio": "3872/1026675",
      "endpoint_ratio": "144722/50307075",
      "negative_group_count": 517
    },
    {
      "R": 4096,
      "Q": -249,
      "C1": -4921,
      "rest": 4672,
      "group_energy": 63425699,
      "cross": -63363698,
      "K": "3/2",
      "K_at": 5,
      "M_history": -19,
      "M_endpoint": 211,
      "Q_ratio": "20667/8388608",
      "endpoint_ratio": "3675/2097152",
      "negative_group_count": 517
    },
    {
      "R": 4097,
      "Q": -367,
      "C1": -5042,
      "rest": 4675,
      "group_energy": 64839075,
      "cross": -64704386,
      "K": "3/2",
      "K_at": 5,
      "M_history": -19,
      "M_endpoint": 329,
      "Q_ratio": "269378/50356227",
      "endpoint_ratio": "215168/50356227",
      "negative_group_count": 516
    },
    {
      "R": 5561,
      "Q": 2554,
      "C1": -298,
      "rest": 2852,
      "group_energy": 19073482,
      "cross": -12550566,
      "K": "3/2",
      "K_at": 5,
      "M_history": 5,
      "M_endpoint": -2544,
      "Q_ratio": "13045832/92774163",
      "endpoint_ratio": "12954050/92774163",
      "negative_group_count": 700
    }
  ],
  "first_failures_detail": [
    {
      "R": 15,
      "X": 224,
      "Q": -7,
      "M_history": -2,
      "M_endpoint": 3,
      "K_num": 3,
      "K_den": 2,
      "K_at": 5,
      "group_energy": 223,
      "cross": -174,
      "atom_diagonal": 108713,
      "groups": [
        [
          1,
          -12
        ],
        [
          2,
          -6
        ],
        [
          6,
          6
        ],
        [
          10,
          2
        ],
        [
          11,
          1
        ],
        [
          13,
          1
        ],
        [
          14,
          1
        ]
      ]
    },
    {
      "R": 17,
      "X": 288,
      "Q": 5,
      "M_history": -1,
      "M_endpoint": -7,
      "K_num": 3,
      "K_den": 2,
      "K_at": 5,
      "group_energy": 173,
      "cross": -148,
      "atom_diagonal": 181511,
      "groups": [
        [
          1,
          4
        ],
        [
          2,
          -6
        ],
        [
          3,
          -6
        ],
        [
          5,
          -3
        ],
        [
          6,
          8
        ],
        [
          7,
          1
        ],
        [
          10,
          2
        ],
        [
          11,
          2
        ],
        [
          13,
          1
        ],
        [
          14,
          1
        ],
        [
          15,
          1
        ]
      ]
    }
  ],
  "elapsed_seconds": 3.5820056889999705,
  "source_sha256": "c81e81c2ad689a5b43a049f2c9ec6220a7e0b98fcf95a127085c9648b0da7784"
}
```

#### gc_certificates.json

```json
{
  "certificates": [
    {
      "R": 15,
      "C1": -12,
      "shared_sum": 5,
      "shared_group_diagonal": 79,
      "shared_cross": -54,
      "binary_cross": -120,
      "fine_cross": -174,
      "fine_diagonal": 223,
      "atom_diagonal": 108713,
      "within_gcd_cross": -108490,
      "Q_squared": 49,
      "Q2_over_DG": "49/223",
      "DG_over_R2K": "446/675",
      "g2_ordered_atoms": [
        [
          2,
          2,
          56
        ],
        [
          2,
          6,
          -18
        ],
        [
          2,
          10,
          -11
        ],
        [
          2,
          14,
          -8
        ],
        [
          6,
          2,
          -18
        ],
        [
          6,
          10,
          3
        ],
        [
          6,
          14,
          2
        ],
        [
          10,
          2,
          -11
        ],
        [
          10,
          6,
          3
        ],
        [
          10,
          14,
          1
        ],
        [
          14,
          2,
          -8
        ],
        [
          14,
          6,
          2
        ],
        [
          14,
          10,
          1
        ]
      ]
    },
    {
      "R": 17,
      "C1": 4,
      "shared_sum": 1,
      "shared_group_diagonal": 157,
      "shared_cross": -156,
      "binary_cross": 8,
      "fine_cross": -148,
      "fine_diagonal": 173,
      "atom_diagonal": 181511,
      "within_gcd_cross": -181338,
      "Q_squared": 25,
      "Q2_over_DG": "25/173",
      "DG_over_R2K": "346/867"
    },
    {
      "R": 549,
      "C1": -28,
      "shared_sum": -158,
      "shared_group_diagonal": 212692,
      "shared_cross": -187728,
      "binary_cross": 8848,
      "fine_cross": -178880,
      "fine_diagonal": 213476,
      "atom_diagonal": 209519833116,
      "within_gcd_cross": -209519619640,
      "Q_squared": 34596,
      "Q2_over_DG": "8649/53369",
      "DG_over_R2K": "426952/904203"
    },
    {
      "R": 5561,
      "C1": -298,
      "shared_sum": 2852,
      "shared_group_diagonal": 18984678,
      "shared_cross": -10850774,
      "binary_cross": -1699792,
      "fine_cross": -12550566,
      "fine_diagonal": 19073482,
      "atom_diagonal": 2208675199789504,
      "within_gcd_cross": -2208675180716022,
      "Q_squared": 6522916,
      "Q2_over_DG": "3261458/9536741",
      "DG_over_R2K": "38146964/92774163"
    }
  ],
  "pair_product_checks": 15028,
  "pair_product_scope": "Every R=2..64, all nonzero original pairs; pair product is NOT final triple product.",
  "all_nontrivial_cross_max": -34,
  "largest_nontrivial_Q2_over_DG": {
    "R": 5561,
    "ratio": "3261458/9536741"
  },
  "largest_DG_over_R2K": {
    "R": 66,
    "ratio": "7616/1089"
  },
  "H_SPLIT_failing_roots": [
    17,
    31,
    32,
    511,
    513,
    549
  ],
  "resonance": [
    {
      "R": 257,
      "p": 131,
      "q": 257,
      "r": 523,
      "pq": 33667,
      "qr": 134411,
      "relative_phase_ratio_error": "22147/11536515"
    },
    {
      "R": 263,
      "p": 137,
      "q": 263,
      "r": 547,
      "pq": 36031,
      "qr": 143861,
      "relative_phase_ratio_error": "23193/12634825"
    },
    {
      "R": 511,
      "p": 263,
      "q": 521,
      "r": 1051,
      "pq": 137023,
      "qr": 547571,
      "relative_phase_ratio_error": "87303/91566343"
    },
    {
      "R": 512,
      "p": 263,
      "q": 521,
      "r": 1051,
      "pq": 137023,
      "qr": 547571,
      "relative_phase_ratio_error": "87644/91925075"
    },
    {
      "R": 513,
      "p": 263,
      "q": 521,
      "r": 1051,
      "pq": 137023,
      "qr": 547571,
      "relative_phase_ratio_error": "263957/276853525"
    },
    {
      "R": 549,
      "p": 277,
      "q": 557,
      "r": 1109,
      "pq": 154289,
      "qr": 617713,
      "relative_phase_ratio_error": "300569/333952031"
    },
    {
      "R": 1023,
      "p": 521,
      "q": 1031,
      "r": 2083,
      "pq": 537151,
      "qr": 2147573,
      "relative_phase_ratio_error": "1048091/2180965915"
    },
    {
      "R": 1024,
      "p": 521,
      "q": 1031,
      "r": 2083,
      "pq": 537151,
      "qr": 2147573,
      "relative_phase_ratio_error": "350046/728410621"
    },
    {
      "R": 1025,
      "p": 521,
      "q": 1031,
      "r": 2083,
      "pq": 537151,
      "qr": 2147573,
      "relative_phase_ratio_error": "350729/729833993"
    },
    {
      "R": 2047,
      "p": 1033,
      "q": 2053,
      "r": 4133,
      "pq": 2120749,
      "qr": 8485049,
      "relative_phase_ratio_error": "1395703/5771314185"
    },
    {
      "R": 2048,
      "p": 1033,
      "q": 2053,
      "r": 4133,
      "pq": 2120749,
      "qr": 8485049,
      "relative_phase_ratio_error": "1397068/5776954365"
    },
    {
      "R": 2049,
      "p": 1033,
      "q": 2053,
      "r": 4133,
      "pq": 2120749,
      "qr": 8485049,
      "relative_phase_ratio_error": "4195301/17347791899"
    },
    {
      "R": 4095,
      "p": 2111,
      "q": 4099,
      "r": 8443,
      "pq": 8652989,
      "qr": 34607857,
      "relative_phase_ratio_error": "16775357/141597644989"
    },
    {
      "R": 4096,
      "p": 2111,
      "q": 4099,
      "r": 8443,
      "pq": 8652989,
      "qr": 34607857,
      "relative_phase_ratio_error": "5594516/47222269931"
    },
    {
      "R": 4097,
      "p": 2111,
      "q": 4099,
      "r": 8443,
      "pq": 8652989,
      "qr": 34607857,
      "relative_phase_ratio_error": "5597247/47245330495"
    },
    {
      "R": 5561,
      "p": 2803,
      "q": 5563,
      "r": 11213,
      "pq": 15593089,
      "qr": 62377919,
      "relative_phase_ratio_error": "10305437/115575989683"
    }
  ],
  "status": "PASS_EXACT_CERTIFICATES"
}
```


### Prepublication Freshness - GC

At 2026-11-11 00:18:50 UTC, main remained f7947bee036c4dddb0c36fc9f53ab46b4fa90995; open/draft PR enumeration remained empty; all six other November 10 role report blobs were unchanged from intake. The nine numerical summary rows were rechecked against the exact output, all ten Markdown tables were validated, A-N and all five required capsule stages are present, and code fences are balanced. Earlier report content and preregistration are exact preserved prefixes. Research execution is COMPLETE at the stated finite scope; publication is verified only after immutable readback below.
