# RH | Adversarial Referee - 2026-11-11

## Early Checkpoint - 20261111-referee-1/NP

Execution: IN_PROGRESS / PARTIAL. Scheduled trigger: 2026-11-11 04:13:01 EST, America/New_York. Platform run ID unavailable. No new theorem is claimed at this checkpoint.

cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1.
Main: f7947bee036c4dddb0c36fc9f53ab46b4fa90995.
AGENTS: c9c89f01b90b526de9f3e8ea92478e36504711b6.
CURRENT_PROOF_CONTRACT: 95566e37c8eaeb99ee680660df4f9d2e06ea5038.
Cross-route directive: e922d4ba9362a1ae196af8f6de88f7417f92087c.
Intake agent-reports: 702daede309826ef9106c80ac1397ed20526550f.

### A. Selected Independent Review

Today Wheel 20261111-wheel-1/GD1-GD4 asserts a complete gcd-norm/Mertens exponent equivalence without GC5. Analytic 20261111-analytic-1/NT2-NT3 asserts that vanishing full-period Nyman variance prevents full Hilbert approximation, and solves the mean-centered covariance minimizer. Reconstruct these claims from the genuine coefficients, full cutoffs and explicit constants. Review the changed finite FFR implementation only at its new scope; do not repeat yesterday's unchanged IR/MD endpoint audit.

Original research question: does actual Nyman density force the periodic variance to diverge, rather than merely remain positive? Investigate the prime-indexed coefficient functionals in the exact Jordan-totient covariance norm. No divergence theorem is assumed; fixed-head coefficient recovery, all prime cross terms and uniform operator constants must be proved.

### B. Authority, Continuity And Baseline

Canonical actual-prime VF square von Koch bound, complete centered wheel RH bound, finite A/C and RH remain OPEN. Certified baseline intake is b_cert=7/8-7/(64*N_pack), with every positive exponent loss. Prior Referee IRR acceptance of IR/MD is PAPER_PROOF, not a compiled endpoint. Original declarations and hosted dependency receipts are being refreshed; no new baseline audit completion is yet claimed.

November 10 reports retrieved for all seven roles. November 11 Owner MC, Analytic NT, Wheel GD and Census DZ are AVAILABLE. Coordinator and Lean are TODAY=PENDING; YESTERDAY=CARRY_FORWARD. The own November 11 report did not exist at intake. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no new entry after October 18. Preserve prior IRR/SR verdicts and the distinction between model obstructions and actual-prime claims.

Only open PR observed: #1131, non-draft, head 621f48b34b5ace39c05aba33ff33b6d014544b4d; finite complete principal-product approximation, not the full endpoint. Main #1130 is merged. Fresh relevant CI evidence remains to be inspected.

### C. Preregistered Checks And Limits

Before numerical work: test genuine Nyman residue/Jordan covariance and multiples inversion on all N=2..24 with deterministic signed rational vectors and the stated covariance minimizer. Test exact recovery of c_n from the first n residuals, prime-functional Gram identities and uniform bounds, and finite complete-error lower bounds; finite tests will not certify an infinite limit. Independently check GD's strict rectangular hyperbola wall and complete gcd reconstruction on a bounded small domain with exact arithmetic, including the equality-wall negative control. Do not extend the unchanged GC5/H_Z scans merely to rediscover their finite survival.

Pending: mathematical verdicts, exact computations, source/CI verification, formalization guidance, report validation and final publication. Direct git transport failed with CONNECT 403; authenticated connector reads and own-report writes remain available. No local Lean, source/main/other-report change, branch/PR creation, merge, agent launch, workflow rerun, schedule or permission change is authorized or performed.

---

## Bounded Periodic Variance Cannot Approximate The Full Nyman Target

### Final Research Synthesis - 20261111-referee-1/NP

Synthesis timestamp: 2026-11-11 04:38 EST (America/New_York). Research execution finished; publication is verified in the appended receipt, once present.

This is the continuation of the scheduled 04:13:01 EST invocation, not a second run. `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. Prior checkpoint and inherited verdicts are preserved. New findings below are paper mathematics unless explicitly stated otherwise.

### A. Most Important Mathematical Finding

**Every successful full Nyman approximation sequence must have periodic variance tending to infinity.** This strengthens today's Analytic NT2 conclusion, which only excluded variance tending to zero. It does not exclude the full-basis Nyman route: a growing variance can coexist with a small weighted tail, and the middle region remains essential.

For arbitrary finite real coefficients on ALL original moduli 2,...,N, let

```text
F(m)=sum_(k=2..N)c_k (m mod k)/k,
r(m)=1-F(m),
E=D_N(c)^2=sum_(m>=1) r(m)^2/[m(m+1)],
V=(1/12)sum_(k,l=2..N)c_k c_l (gcd(k,l)^2-1)/(kl).
```

The new prime-coefficient inequality and complete-error consequences are

```text
sum_(p prime)c_p^2 <= 12*zeta(2)*(1+sum_p p^-2)*V <= 48V,
|c_p-1| <= 2p sqrt(E) for EVERY prime p, with c_p=0 for p>N,
V >= pi(1/(4 sqrt(E)))/192,                         E>0,
E_j -> 0  implies  V_j -> infinity.
```

Here pi on a real argument counts primes at or below its floor. No conjecture, Mertens bound, model coefficient substitution, PNT, or RH premise is used. All composite and squareful basis coordinates remain available. The primes are a diagnostic subset of coefficients, NOT a prime-only basis restriction.

The proof reconstructs an exact infinite Gram matrix for prime coefficient functionals, including its positive off-diagonal terms. It therefore does not incorrectly infer a global signed bound from individual coefficient inequalities. For an exact head F(m)=1 on 1<=m<=H, it gives V>=pi(H)/48, independently of how the high coefficients were corrected.

New claims `20261111-referee-1/NP1-NP3`: **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. NP4 is exact finite verification. This is proposed as a substantial complete-NYMAN-source restriction under admission test 2, not self-certified as an accepted new proof route. No external-literature priority is claimed.

Independent review also returns **ACCEPT/PAPER_PROOF** for `20261111-wheel-1/GD1-GD4`, **ACCEPT/PAPER_PROOF** for `20261111-analytic-1/NT2-NT3`, and **ACCEPT/PAPER_PROOF** for Coordinator `20261110-coordinator-2309-EST/FFR1-FFR4` as a finite implementation of the already accepted IR endpoint. FFR is not another numerical improvement. **NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE; RH=OPEN.**

### B. Current Authoritative Objective

Source main: **f7947bee036c4dddb0c36fc9f53ab46b4fa90995**, human merge of #1130. Authority: AGENTS `c9c89f01b90b526de9f3e8ea92478e36504711b6`, proof contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`, cross-route directive `e922d4ba9362a1ae196af8f6de88f7417f92087c`. The later AGENTS cross-route priority supersedes the older contract's single-wheel task selection, not mathematical hypotheses or safeguards.

The canonical OPEN objective remains one constant C>=0 before every integer R>=2 with |pi(R^2)-VF_can(R^2)|<=C R log R. The live terminal `riemannHypothesis_of_vfCanonicalSquare` explicitly takes both that arithmetic statement and `ClassicalVonKochRHCriterion`. The separate internal finite-C -> finite-A -> Mertens energy -> RH consumer still takes the unpaid finite-C arithmetic premise. A new identity does not discharge it.

#### 1. BASELINE / DEPENDENCY RECEIPT

The strongest explicit applicable compiled comparator verified here is

```text
RHLean.Analysis.native_mertens_near_uniform_window_error_closed
  : MertensGrowthAtMost(b_cert),
b_cert=7/8-7/(64*N_pack).

MertensGrowthAtMost(b): forall eps>0 exists C_eps>=0 forall n>=1,
  |M(n)| <= C_eps*n^(b+eps).
```

Read the actual endpoint, original growth definition, source count definitions, native moment supplier, native Hecke-to-zeta/Mertens transfer, and live dependency-audit implementation. For the SAME positive explicitFineLength L, N_pack=ceil_nat(max(1,1/(6L)))+2 and N_old=ceil_nat(max(1,1/(3L)))+2. Hence N_pack<=N_old and 7/(64N_pack)>1/(48N_old), also >5/(96N_old). These are compared counts, not identical symbols. No optimization over all fine-source records is asserted, and no zero-loss bound at b_cert follows.

The inspected chain is actual fixed source/native moments -> total-mass LOW and complete anchored HIGH/principal -> actual Hecke zero supremum -> modulus-one L-product -> native Mertens converse. `native_uniform_fixed_source_moments` has actual hypotheses 51/100<=beta<=7/8+Delta, fixed fine geometry and count data, with J before the character and C,Z0 before tau,height,scale. It is not a free arbitrary-profile bound. Its use in the previously accepted IR contradiction branch remains within that range.

| Item | Actual hosted/source evidence refreshed this run |
| --- | --- |
| #1119 | MERGED, tested head 77ee815846d6d534c866f0752aa33b84c385610a; all 14 checks successful. Dedicated run 42552018910, job 128949473700 inspected. |
| #1119 root audit | Five actual PASS proof-value closures 35358,35375,35736,35737,35753; only propext, Classical.choice, Quot.sound. The audit traverses OAI/RHLean/private proof values and separately collects terminal axioms. |
| Source preservation | Compared 911 pre-existing blobs under RHLean/, research/oai_434/, scripts/lean/slot_anchored/ and scripts/lean/window_error_closure/ at the tested tree and current main: ZERO changed. This reuses scoped evidence; it is not a fresh whole-main build. |
| #1130 | MERGED at current main; tested head 4aa22782d10b3ad77dc970d6bb610eaab93a228c, 13/13 checks successful. Run 42877550772/job 130044786387: four standard-axiom closures 628,984,653,657. Local signed-remainder scope only. |
| #1131 | Sole open PR, non-draft/unmerged, head 621f48b34b5ace39c05aba33ff33b6d014544b4d; 13/13 checks successful. Run 42947849721/job 130284860499: six standard-axiom closures 618,647,660,730,735,197. Full finite-product approximation only, not contour/inversion/endpoint. |

Pins retained from actual hosted evidence: Lean 4.34.1/compiler 5045d0056413266e57c625dcd7c365b10e377c52; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; openai/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a; prior verified PNT+ c39a751132c88b6e8080b74c74023fd95b3d8be0 and anchored source 9cbfce5295343bcb411e6d2cb159b59995cd985b. Historical Wiener placeholder warnings remain outside the selected audited root closures. No claim that every imported declaration is placeholder-free or independently re-proved is made. No local Lean ran.

The stronger accepted paper endpoint `b_IR=7/8-1/2400000000`, with every positive loss and spent fixed comparison `eta_IR=737/3840000000000`, retains yesterday's independent Referee IRR acceptance. It remains PAPER, not a new compiled baseline. Source hashes are unchanged, so this run audits only FFR's changed finite implementation, not the entire unchanged IR proof again.

#### Two-Day Continuity

Intake reporting head 702daede309826ef9106c80ac1397ed20526550f. All November 10 role reports and the available November 11 reports were retrieved; latest relevant proofs, results and resume sections were read. Today Owner MC, Analytic NT, Wheel GD and Census DZ are AVAILABLE. Coordinator and Lean: **TODAY=PENDING; YESTERDAY=CARRY_FORWARD**. Own today's report was absent before this run. Coordinator's November 10 mirrors have identical blobs. Do not infer unobserved executions.

External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no entry after October 18. Relevant EXT-20261018-PNT-1 cofactor/cutoff restrictions and EXT-20261014-5 original-denominator/all-root versus first-bad distinction remain safeguards. Their historical routing does not override current main. Prior SR/IRR, RC/DR/GC scopes are preserved, not repeatedly audited or silently promoted.

### C. Highest-Risk Proof Mechanisms

The highest-risk changed inference is replacing the COMPLETE Nyman weighted approximation norm by a favorable full-period covariance. NT2 already rejects a vanishing-covariance premise; NP below rejects every uniformly bounded-covariance version. This is a method-specific no-go, not a refutation of the full Hilbert method or its classical criterion.

Wheel GD asks whether a complete gcd diagonal is an independently weaker exponent target. Its two-way transfer is valid, but reveals target-equivalent strength. Proving the norm independently would still be progress; assuming the norm merely renames the same arithmetic difficulty. Neither GC5 nor today's stronger H_Z is needed for the exponent consumer.

The principal-response risk is a different one: deleting below-one delayed arguments or treating a finite polynomial approximation as the full endpoint. FFR keeps those terms and uses the original signal's already-proved small-argument bound. No such pointwise bound transfers to the Nyman step function.

### D. Claims Reviewed And Verdicts

| Original claim ID | Verdict | Evidence and exact accepted scope |
| --- | --- | --- |
| 20261111-analytic-1/NT1 | ACCEPT | IDENTITY_ONLY/PAPER algebra: original covariance diagonalization and finite multiples inversion. Existing periodic covariance and Jordan diagonalization are credited. |
| NT2 | ACCEPT | PAPER_PROOF: uniform full-error lower bound, V->0 obstruction and positive variance floor. No mean-centering assumption. Strengthened, not refuted, by NP. |
| NT3 | ACCEPT | PAPER_PROOF: unique mean-centered covariance optimizer, V=Theta(1/N), full squared error 1+O(log^3(N)/N). Not the full Hilbert minimizer. |
| 20261111-wheel-1/GD1 | ACCEPT | PAPER_PROOF/supporting IDENTITY_ONLY: full smooth-divisor rectangular reconstruction with strict wall. |
| GD2 | ACCEPT | PAPER_PROOF: uniform complete gcd coefficient/norm/tail transfers for each fixed c>1/2, assuming the stated actual Mertens power. Constants need not stay bounded as c decreases to 1/2. |
| GD3 | ACCEPT | PAPER_PROOF/TARGET_EQUIVALENT at exponent level for 1/2<=b<=1; no GC5 premise and no zero-loss boundary inference. |
| GD4 | ACCEPT | PAPER_PROOF/CONDITIONAL: historical N_eta consumer and all-positive-loss equivalence. Fixed eta=0 converse is not proved. |
| 20261111-census-1/DZ2b,DZ2c | ACCEPT | Exact R=7 refutation of the claimed favorable divisor-weighting explanation; complete overlap identity. Independently reproduced below. |
| DZ1/DZ3 H_Z and GC5 | UNRESOLVED | H_Z and GC5 remain CONJECTURE. The upstream larger finite domain was not rerun; this run tests reconstruction, not a new sign-scan campaign. |
| 20261110-coordinator-2309-EST/FFR1-FFR4 | ACCEPT | PAPER_PROOF: finite all-delay return and inversion on the same fixed actual source; same already accepted IR endpoint, not a new exponent. |
| #1131 finite product statements | ACCEPT AT DECLARED SCOPE | PROVED_IN_LEAN_AT_PR_HEAD, green/unmerged; not main and not the complete endpoint. |
| 20261111-owner-1/MC | CONTINUITY, NOT NEWLY REFEREED | Read literal-mask derivation and Census's independent certificates. Preserve their auxiliary mask-transfer scope; no complete #915 coefficient embedding is claimed here. |
| New NP1-NP3 | SELF_AUDIT | Complete paper proofs below; independent review pending, no self-issued independent ACCEPT. |
| New NP4 | EXECUTED | Exact finite tests with complete declared domains and source-faithful controls; no infinite inference from tests. |

### E. Independent Mathematical Reconstruction

#### E1. Accepted NT2 And NT3

For q_d=sum_(d|k,2<=k<=N)c_k/k and J2(d)=d^2 product_(p|d)(1-p^-2), the full covariance is V=(1/12)sum_(d=2..N)J2(d)q_d^2. This follows from exact CRT residue averaging: conditional on a shared residue modulo gcd(k,l), the remaining two residue coordinates run over a Cartesian product. It is exact counting, not a stochastic independence assumption. Expanding gcd(k,l)^2-1=sum_(d|k,d|l,d>=2)J2(d) gives the displayed norm with every cross term.

Finite multiples inversion gives c_k=k sum_(j<=N/k)mu(j)q_(kj), q_1=-sum_(d=2..N)mu(d)q_d, and sum c_k(1-1/k)=sum phi(d)q_d. Since J2(d)>=d^2/zeta(2), weighted Cauchy-Schwarz bounds |c_k|,|q_1| by 7 sqrt(V). The exact floor return F(m)=m q_1-sum_(2<=k<=m)c_k floor(m/k) therefore gives |F(m)|<=7 sqrt(V)m H_m, with high coefficients still present through q_1.

Keeping the first M nonnegative weighted residual squares and using (1-F)^2>=1-2|F| proves EXACTLY NT2:

```text
E >= 1-1/(M+1)-7 sqrt(V)[H_(M+1)^2-H_(M+1)^(2)].
```

First take liminf at fixed M, then M->infinity; no uniform-limit substitution is needed. The first-cell positive variance floor in NT2 is also correct, using sum_(d>=2)mu(d)^2/J2(d)=zeta(2)-1. Its necessary-condition status is retained.

Under mean centering, sum phi(d)q_d=2. Put S_N=sum_(d=2..N)phi(d)^2/J2(d). Strict positive quadratic minimization gives

```text
q_d*=2phi(d)/(S_N J2(d)),
c_k*=(2k/S_N)sum_(j<=N/k)mu(j)phi(kj)/J2(kj),
min V=1/(3S_N),
V(q)=1/(3S_N)+(1/12)sum J2(d)(q_d-q_d*)^2.
```

The cross term vanishes by the SAME mean constraint. The elementary estimate phi(n)^2/J2(n)>=1-sum_(p|n)2/(p+1), together with sum_p2/[p(p+1)]<=9/10 (exclude n=4 from the full telescoping integer sum), gives N/20<=S_N<=N-1 for N>=20. Thus V(q*)=Theta(1/N) with uniform constants.

The crucial full-tail audit succeeds: B_N=sum|c_k*|<=2 zeta(2)N/S_N is bounded, |q_1*|<=2H_N/S_N and |F*(m)|<=2H_N mH_m/S_N for m<=N. Hence

```text
|E(c*)-1| <= (2+B_N)H_N/S_N [H_(N+1)^2-H_(N+1)^(2)]
              +(2B_N+B_N^2)/(N+1)
           = O(log^3(N)/N).
```

This includes all m>N through their exact total weight 1/(N+1). It proves NT3's full limit, not merely the behavior of a proper tail.

#### E2. Accepted GD1-GD4

Fix R>=2, N=R-1, X=R^2-1 and the genuine mu. Let C_R(g) be the sum of mu(a)mu(b)floor(X/(ab)) over ALL ordered 1<=a,b<=N with gcd(a,b)=g; S_R(d) is the corresponding sum with d|a,b. Define D_G=sum_g C_R(g)^2. The original endpoint Q_R=sum_g C_R(g)=2M(N)-M(X) was checked in main.

For A,B<=T<(A+1)(B+1), complete Mobius inversion minus the two outer strips gives the rectangular identity Q_(A,B)(T)=M(A)+M(B)-M(T). The overlap is empty ONLY under the strict wall. At A=B=1,T=4 the literal value is 4, while the no-corner expression is 3, so equality at the wall is not permitted.

For B_d=floor(N/d), h,k supported on primes dividing d with h,k<=B_d, and A_h=floor(B_d/h), T=floor(X/(d^2hk)),

```text
S_R(d)=mu(d)^2 sum_(h,k)[M(A_h)+M(A_k)-M(T)],
C_R(g)=sum_(k<=N/g)mu(k)S_R(gk).
```

This follows from mu(du)=mu(d)mu(u)1_(gcd(u,d)=1) and the finite smooth-divisor convolution. In every resulting rectangle, max(A_h,A_k)<=T and d^2hk(A_h+1)(A_k+1)>=R^2>X, so the original wall survives, including divisibility boundary cases. Squareful labels have their actual zero factor. This is not an arbitrary-coefficient identity or a matching allocation.

If |M(n)|<=A n^c for every n>=1, with FIXED c>1/2, set w_c(p)=(1-p^-c)^-2 and W_c(d)=product_(p|d)w_c(p). Then

```text
|S_R(d)| <= 3A X^c mu(d)^2 W_c(d)/d^(2c),
|C_R(g)| <= 3A Z_c X^c mu(g)^2 W_c(g)/g^(2c),
Z_c=product_p(1+w_c(p)/p^(2c)) < infinity.
```

Nonzero gk requires squarefree coprime g,k, justifying multiplicativity of W_c. Squaring gives D_G<=9A^2 Z_c^2 Y_c X^(2c), with Y_c=product_p(1+w_c(p)^2/p^(4c)). Expanding W_c(n) as a nonnegative divisor convolution gives sum_(n<=t)W_c(n)<=E_c t, E_c=product_p(1+(w_c(p)-1)/p)<infinity. Partial summation gives GD2's full tail constant 2c E_c/(2c-1), and its squared analogue 4c E_c,2/(4c-1), where E_c,2=product_p(1+(w_c(p)^2-1)/p)<infinity. The constants are independent of R and the gcd label; convergence fails at the relevant c=1/2 endpoint for Z_c, which is never used.

Under D_G(R)<=B R^(4b), 1/2<=b<c<=1, split the EXACT Q into g<=G and g>G. The head costs sqrt(G)sqrt(D_G); the complete tail costs O_c,A(R^(2c)G^(1-2c)). With alpha=4(c-b)/(4c-1) and G=R^alpha,

```text
MertensPowerBound(c) AND D_G(R)=O(R^(4b))
  ==> MertensPowerBound(b+(c-b)/(4c-1)).
```

Both exponents match, 0<alpha<1, and the endpoint-to-all-prefix O(sqrt(n)) interpolation is paid. No favorable cross sign is assumed. Iterating at a FIXED b'>b reaches any prescribed b+eps in finitely many steps. It follows that MertensGrowthAtMost(b) is equivalent to every-positive-loss D_G(R)=O_eps(R^(4b+eps)), for 1/2<=b<=1. Constants may grow with the finite iteration count; no uniform limiting constant or no-loss theorem is claimed.

For the ORIGINAL K_R=max_(0<=u<R)(M(u)-1)^2/(u+1), a power c>=1/2 gives K_R<=(A+1)^2 R^(2c-1), including u=0. Thus the OPEN N_eta premise D_G<=B R^(2+2eta)K_R gives the growth update (2c+1)/4+eta/2 and, by finite iterations, MertensGrowthAtMost(1/2+eta). Every-positive-eta N_eta is target-equivalent to the critical Mertens growth statement; fixed eta=0 is proved sufficient only. GD is a useful exact difficulty audit, not evidence for its own norm premise.

#### E3. Accepted Finite FFR Implementation

For fixed actual source and fixed number n of slots, retain the actual normalized positive pool weights, |A|<=1, |eta|=1, and Q>=max(480,Z^m), with m>0 chosen BEFORE Z. A fixed pool prefactor is absorbed by reducing m and increasing the threshold, not by assuming it is at least one. The original negative-normalized symbol is

```text
q=Q^-1, D=eta Q^-s, G=A Q^(2-6s),
W=A conjugate(eta)Q^(3-5s), H=G+(1-q)D,
S=q+(1-q)(1-W)/(1-H),
S_K=q+(1-q)(1-W)sum_(j=0..K)H^j.
```

For every fixed theta>3/5, the nonconstant theta-weighted coefficient mass is at most (1-q)(r+w)/(1-r), where r=Q^(2-6theta)+(1-q)Q^-theta and w=Q^(3-5theta). This holds uniformly in K. The COMPLETE weighted product therefore has mass at most exp(6n Z^(-m min(theta,5theta-3)))-1. All mixed monomials remain.

Choose finite K ONCE with (7/8)m(K+1)>=2. The actual #1131 theorem supplies product error <=n*5^n*4*2^(K+1)Z^-2. Shift the WHOLE original principal integrand to Re(s)=2, where the actual zero bound, analytic correction, polynomial reciprocal growth and Gaussian decay license the shift. Use the raw quotient equality only almost everywhere. Then finite expansion and the original signal_eq_contour give

```text
principal_normalized(Z)=f(Z)+sum_i B_i T_i^c f(Z/T_i)+E_K(Z),
|E_K(Z)|<=C_(n,K)*endpointConstant(2)*Z^c.
```

T_i>Z terms are legal and retained: signal_eq_contour requires x>0, not x>=1. The actual signal_bound_at_zero and continuity bound the compact-prefix weighted supremum on ALL 0<x<=X. The small coefficient mass then gives noncircular inversion by B_X<=max(B_initial,C+B_X/2). This inverse statement alone is a growth equivalence, not new arithmetic.

The extra error Z^c is below Z^(g+c) since g=7/8-h>0. All remaining raw physical-return inequalities, profiles, height choices, floor/nonfloor populations, principal tails and the strict gate 24h<t are exactly the previously accepted IR4 obligations at unchanged source. Hence FFR gives the SAME paper endpoint; no new global gain or repeated baseline audit is counted. It is a valid simplification for Lean implementation, not a license to drop below-one arguments, reset the pools at Z/T, identify Mobius signs with Hecke phases, or assume an unproved response bound.

### F. New Complete-Source Obstruction: NP1-NP3

#### NP1. Exact Prime-Functional Gram And Uniform Bessel Bound

Fix any finite N>=2 and ANY real vector c_2,...,c_N. Set c_k=0 for k>N and q_d=0 for d>N. Let J2 and q be as above, and x_d=sqrt(J2(d))q_d for d>=2. Then ||x||_2^2=12V. For each prime p define on integers d>=2

```text
v_p(d)=p*mu(d/p)/sqrt(J2(d)) if p|d, and 0 otherwise.
```

Finite multiples inversion gives c_p=<x,v_p>, including p>N. Every v_p is square summable. The absolutely convergent squarefree Euler product is

```text
sum_(h>=1)mu(h)^2/J2(h)
  = product_p(1+1/(p^2-1))=zeta(2).
```

Absolute convergence follows already from J2(h)>=h^2/zeta(2). This is the elementary Euler product at 2, not a conditional Mobius rearrangement or a prime-distribution theorem.

For distinct primes p,q, nonzero mu(d/p)mu(d/q) forces d=pq h with h squarefree and coprime to pq. The product is then mu(h)^2, so the off-diagonal is POSITIVE, not silently zero. Direct summation gives

```text
<v_p,v_q> = zeta(2)/(pq),                  p != q.
```

For p=q, split d=p h and d=p^2 h with h squarefree and p-free. Since J2(p^2)=p^2(p^2-1),

```text
<v_p,v_p>
 = [p^2/(p^2-1)+1/(p^2-1)]
       *zeta(2)*(1-p^-2)
 = zeta(2)*(1+p^-2).
```

Thus for EVERY finite prime set P and real z_p,

```text
||sum_(p in P)z_p v_p||_2^2
 = zeta(2)[sum z_p^2+(sum z_p/p)^2]
 <= zeta(2)(1+sum_(p in P)p^-2) sum z_p^2.
```

Taking z_p=c_p and using Cauchy-Schwarz against x proves

```text
sum_(p in P)c_p^2
 <= 12*zeta(2)(1+sum_(p in P)p^-2)*V.                (NP.1)
```

All support is finite on x, while the explicit Gram suppliers are square summable; the passage to all primes uses monotone nonnegative sums only. Put P2=sum_p p^-2 and L=12*zeta(2)(1+P2). Since zeta(2)<2 and P2<=zeta(2)-1<1, L<48. Hence sum_p c_p^2<=L V<=48V. No cross term in the original covariance has been discarded. The coarser numerical constant is intentionally not optimized.

#### NP2. Full Approximation Forces Divergent Periodic Variance

The original floor identity gives, for EVERY integer n>=1,

```text
F(n)-F(n-1)=q_1-sum_(k|n,k>=2)c_k,
F(0)=0, r(0)=1.
```

At a prime p this is exactly

```text
c_p=1-r(1)+r(p)-r(p-1).                            (NP.2)
```

This coefficient recovery is inherited finite Mobius algebra, already present in the repository's October 15 Nyman note; the new contribution is its JOINT use with NP.1, not a claim to have discovered the increment identity.

For p>=3 the squared weighted dual norm of the three residual coordinates is 2+p(p+1)+p(p-1)=2p^2+2<=4p^2. At p=2 the r(1) terms coincide and the correct norm is 4*2+6=14<=16. Therefore, with the COMPLETE original weighted error E,

```text
|c_p-1|<=2p sqrt(E)                                (NP.3)
```

for every prime p, including absent coefficients p>N. This checks the small-prime multiplicity that a naive three-independent-coordinate argument would miss.

If E_j->0 along ANY sequence of finite full-basis vectors, c_p^(j)->1 for each fixed prime. For any finite prime set P, NP.1 gives liminf_j V_j>=|P|/L. Infinitely many primes and arbitrary finite |P| imply V_j->infinity. The prime set is fixed BEFORE the limit; there is no unproved uniform coefficient convergence over a growing range.

More quantitatively, if 0<E and p<=1/(4 sqrt(E)), then c_p>=1/2. Applying NP.1 gives

```text
V >= pi(1/(4 sqrt(E)))/(4L)
  >= pi(1/(4 sqrt(E)))/192.                         (NP.4)
```

E cannot be zero for a finite vector: at any positive multiple of lcm(2,...,N), F=0 and the residual has positive weight. This is a genuine full-source no-go for all uniformly bounded-V approximation schemes. It does NOT refute density with V growing, an RH-equivalent density statement, the unchanged large-sieve tail estimate, or the actual-prime/VF objective.

#### NP3. Exact-Head Cost And Uniform Separation Of Bounded-Variance Classes

If F(m)=1 for every 1<=m<=H, then NP.2 forces c_p=1 for p<=H. Thus

```text
V>=pi(H)/L>=pi(H)/48.                              (NP.5)
```

In particular the compiled flat-taper exact-head theorem, with its literal reciprocal-moment condition and low correction zero, cannot be combined with a coefficient-uniform bounded periodic-variance supplier as H grows. This charges a previously unquantified cost of the actual complete approximant; it is not a bound on an artificially isolated correction.

For a fixed B>=0, choose ANY integer H>=2 with pi(H)>48B. From NP.3 and the Euclidean triangle inequality on primes p<=H,

```text
sqrt(pi(H)) <= sqrt(48V)+2sqrt(E)*sqrt(sum_(p<=H)p^2).
```

Consequently EVERY finite vector with V<=B satisfies the explicit positive full-error floor

```text
E >= [sqrt(pi(H))-sqrt(48B)]^2 / [4 sum_(p<=H)p^2] > 0.  (NP.6)
```

H depends only on B, not N or the coefficients. Euclid's theorem suffices to choose H; no asymptotic for primes is needed. This is stronger than just excluding V->0, yet does not impose a false no-go on schemes with growing V.

### G. Original-Carrier And Covariance Audit

The selected new result is on the exact Nyman basis in main: nymanResidue k m=(m%k)/k, nymanResidual=1-sum c_k nymanResidue, nymanWeight m=1/[m(m+1)]. On 1/(m+1)<x<=1/m, the centered integer-dilation basis {1/(kx)}-{1/x}/k is exactly (m mod k)/k. Thus E is the COMPLETE L2(0,1) error, not a reference covariance or pointwise proxy. Every prime, composite, squareful modulus and every weighted cell is retained. Full periodic V is an auxiliary statistic, connected to E only by the newly proved inequalities.

The [primary integer-dilation criterion](https://arxiv.org/html/math/0202141v2), Theorem 1.1, was checked for context. Its RH equivalence is an external classical interface, not newly formalized or required by NP. The obstruction itself uses elementary finite inversion, an absolutely convergent Euler product and Hilbert inequalities. No literature-priority claim is made.

#### 2. FOUR-WAY SOURCE MAP

| Euler / finite AC | VF / actual-prime source | NNS / OAI | Square blocks / native HIGH | Typed boundary to the present source |
| --- | --- | --- | --- | --- |
| X=R^2-1; complete ordered Q_R=sum mu(a)mu(b)floor(X/(ab)), 1<=a,b<R, genuine floor multiplicities and unit. K_R is the strict shifted historical maximum. | Complete F_R=sum_(d divides primorial(R-1))mu(d)fract(X/d); deterministic D_R=X product_(p<R)(1-1/p)+pi(R-1)-1-li(X). All virtual d>X remain until Euler compensation. | Original complex ideal LOW tuples, calibrated masks, conductor/exclusions, weights, Gaussian and normalizer; exact signed Gram preserves both orientations. FFR uses the distinct actual principal product. | Complete M(X), not a single shell; canonical fixed-Lambda LOW/HIGH retains historical, mixed and high terms. | Q_R=2M(R-1)-M(X): EXACT_IDENTITY in endpoint gate. F_R-D_R=li(X)-pi(X): EXACT_IDENTITY in complete-wheel theorem. Neither equals Nyman V or E. |
| GD1 restores each common-divisor source and each gcd group exactly; GD3 is a PAPER exponent-level BOUND_EQUIVALENCE, not pointwise isometry. | Original #915 chronology, clipped returned cells, weights, squareful residual and anchors are additional restrictions. Owner MC tests a literal mask pulled back to an auxiliary completion, not a full #915 occurrence equality. | Hecke-to-native-Mertens is ONE_WAY_IMPLICATION through the actual zero inclusion/converse. There is NO coefficient map replacing ideal phases with rational Mobius. | GD's square-endpoint-to-all-prefix O(sqrt(n)) bill is explicit. CORR4 daughters and reciprocal top bands keep their distinct mixed bills. | Prime-to-Mobius Buchstab is a cofactor-weighted coupling, not equal errors. Direct isometry/size transfer from Nyman to these sources is OPEN_BRIDGE; the classical density consumer is separate. |
| Nyman q_d also uses divisibility, but q is a transform of arbitrary approximant coefficients c, not S_R(d) or C_R(g). | No actual prime indicator is replaced by Li density or by a Nyman coefficient. | A real/complex norm representation supplies no cancellation by itself. The principal signal's rapid decay is NOT a Nyman step-function property. | No sum-of-squares is substituted for a square-of-sum. | Nyman F<->q is finite invertible algebra; V is its exact periodic covariance norm; E is a different complete weighted norm. NP gives necessary inequalities, NOT equivalence or sufficiency. |

### H. Quantifier And Circularity Audit

NP holds for EVERY N>=2 and EVERY finite real coefficient vector, without mean centering. The constant L, and the coarse constant 48, precede all N. For NP2, fix a finite prime set before passing to a density limit; enlarge that set afterward. Equation (NP.4) provides a separate uniform growing-range statement, justified directly by the quantitative coordinate bound. No impossible interchange of these limits is used.

The NP necessary condition V->infinity is NOT target-equivalent and does not imply density. For example c_2=j, all other coefficients zero, gives V=j^2/16->infinity, while the m=1 residual contribution alone is (1-j/2)^2/2->infinity. Thus divergent V is compatible with both failure and hypothetical success. The surviving target remains E->0, not a renamed covariance condition.

GD3 IS target-equivalent at its stated exponent, not a universal zero-loss norm comparison. GD4's N_eta family for every positive eta is RH-strength on the actual Mertens carrier; its single eta=0 converse is not asserted. Constants may depend on c, eta and a finite iteration count, never the running arithmetic scale. K_R is not replaced by 1 to manufacture the forward gain.

FFR3 alone is an equivalence of signal growth under independently verified response coefficients. FFR4's useful content comes from the unchanged paid physical return, not from assuming that equivalence's antecedent. Its constants and finite order precede Z, all pools stay frozen at the outer Z, and the strict h<t/24 gate is not evaluated at equality. The boundary is numerical closure, not a limit of uniformly bounded physical sources.

### I. Constructive Repairs And Paid Recovery Test

#### 3. FIRST SIGNED LOSS

| Declaration or step | Exact input / discarded information / tax | Consumer, paid recovery and remaining bill | First falsifier |
| --- | --- | --- | --- |
| Nyman replacement of full E by periodic V | Drops the original nonuniform weights, fixed head and middle; no valid universal small-error transfer follows. | Exact covariance and multiples inversion are paid. NP adds prime-functional Gram control and shows bounded V is incompatible with E->0. Full weighted head/middle/tail estimate is still required. | Zero vector: V=0,E=1. Mean-centered optimizer: V->0,E->1. NP excludes even bounded nonzero V. |
| Nyman coefficientwise CS without aggregation | Individual abs(c_p) bounds cannot be summed with a constant independent of the number of primes. | NP's exact Gram is zeta(2)(I+u u^T), INCLUDING positive cross terms. This gives the uniform aggregate constant L. | At p=2,3 the infinite cross Gram is zeta(2)/6, not zero. |
| Euler Q=sum_g C(g) -> unstructured head CS | Costs sqrt(number of groups), losing signed inter-gcd interactions. | GD2 recovers a complete arithmetic tail from actual Mobius factorization; balanced head/tail gives GD3 equivalence, not a new exponent. Independent improved norm input remains open. | Strict rectangle equality wall A=B=1,T=4; R=7 divisor overlap adds +10 to the ordinary cross term. |
| Original principalSlot -> 1 | Discards signed D, W and mixed/higher returned terms; old minimum-slot error remains binding. | #1130 and #1131 plus exact source normalizer and original signal contour/zero bound recover finite FFR response. Full endpoint formalization remains. | Removing T>Z changes the response despite identical above-one data; no such deletion occurs in FFR. |
| Completion before actual #915 mask | Moving f(qa) to f(qak) changes source admission and signed multiplicity. | RC completion only licenses fibre-invariant masks; MC gives a separate commutator. It is not paid by a Hecke or Nyman theorem. | Upstream literal r=10, p=3 row gives +4w(1-w) or -4w^2 against zero completed row; not independently recomputed in this invocation. |

#### 4. PAID RECOVERY TEST

The new Nyman recovery uses the already available original residue/floor identity, complete covariance and multiples transform. The missing interaction is supplied by the NEW exact prime-functional Gram, not by an assumption that V is bounded or that primes decorrelate. The Gram's positive rank-one part is fully charged. The existing compiled `nyman_flat_exact_head` supplies a real consumer for (NP.5): any admissible flat-taper exact head incurs a growing complete covariance cost.

The corrected research direction is not to minimize V alone or impose a fixed covariance cap. Allow V to grow and prove a complete weighted norm estimate. An already reviewed tail majorant of the form V[1/(T+1)+N^2/((T+1)(T+2))] remains usable when its normalization pays that growth; it is not proved useless by NP. This run does NOT infer that this upper majorant is a necessary lower cost, nor that choosing T alone pays the middle or correction terms.

For Euler, GD demonstrates that the source does have nontrivial arithmetic tail restrictions, but they preserve the input exponent. GC5/H_Z may encode useful pointwise structure; neither can be used as the source of its own norm estimate. For OAI, select one finite FFR implementation and preserve all original return hypotheses rather than build duplicate identity-only routes.

### J. Competing Proof-Strategy Assessment

NYMAN: **REVISE bounded-variance or covariance-minimization strategies; CONTINUE the full weighted Hilbert route with growing variance.** NP is a complete-source necessary restriction, not an RH refutation. Exact-head corrections now have an explicit covariance bill. CODIV's original Mertens quadratic source is not identified with this covariance.

FINITE-AC/CORR4/MU-LIFT: **ACCEPT GD's exponent equivalence and tail transfer; do not call the norm independently easier without new arithmetic.** Preserve strict history K_R, all top bands and both mixed orientations. The norm estimate itself remains a legitimate target to prove, not a circular theorem merely because it is equivalent.

OAI-NNS: **CONTINUE the independently accepted FFR/IR endpoint implementation.** FFR is a simpler realization of the same mechanism, not a tenth route. Actual #1131 is a useful necessary finite-product theorem, still unmerged and not the global endpoint.

VF-LOW/SAT/JOH: **CONTINUE original-mask commutator and weighted history transport.** MC must not be upgraded from auxiliary mask-transfer failure into a refutation of a conditional first-bad strategy. No route is retired based on an unrelated carrier, and all nine authorized route families remain available.

#### 5. NET RESULT / ADMISSION VERDICT

`NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE.` NP1-NP3 are a new self-audited PAPER restriction on the complete Nyman physical approximation source, submitted for independent admission-test-2 review. GD/NT/FFR receive scoped independent paper acceptance. No new Mertens exponent, finite A/C, canonical VF bound or RH theorem is asserted. The accepted older IR paper comparator and compiled b_cert are kept separate.

### K. Original Adversarial Research And Executed Checks

The independent investigation began with the question whether NT2's positive variance floor was the strongest necessary condition. A direct attempt to invert the entire infinite divisibility transform was insufficient: the full divisor transform does not have the needed uniform bound from individual estimates. Restricting the COEFFICIENT FUNCTIONALS to primes, while retaining the ENTIRE original basis, exposes the exact bounded Gram zeta(2)(I+u u^T). Combining it with full-error coefficient recovery yields NP1-NP3. This is not a generic signed-vector example imposed on a multiplicative theorem.

NP4 used a newly written exact Python Fraction checker, not the submitted upstream programs. Frozen Nyman domain: all N=2..24, six deterministic coefficient vectors per N including the literal mean-centered optimizer; every prime up to 2N for coordinate recovery; literal full periods for N<=8; eight exact-head constructions with H in {2,3,5,8,16,32,64,128}. Growing covariance is not inferred from these samples; it is proved above.

Exact completed counts: 801 prime Gram entries, 23 rational positive-semidefinite matrix certificates, 1,656 multiples inversions, 138 complete variance/prime bounds, 3,450 full coefficient recoveries, 1,218 prime-head recovery/error checks, 552 NT2 full-head lower bounds, 42 literal full-period variances, 23 NT3 optimizer/stability checks, and eight exact-head variance checks. No floating eigenvalues or near-zero sign decisions are used. The zeta(2) upper bound for the finite matrix certificates is the rational sum_(n<=64)n^-2+1/64.

GD review tests: ALL valid positive A,B<=T<(A+1)(B+1) with T<=40, totaling 20,899 rectangles; the equality-wall negative control; every root 2<=R<=64 with 2,016 complete common-divisor and 2,016 gcd-inverse checks; 80 exact rational exponent iterations. This small-domain run is an independent reconstruction test, not an enlarged GC5 scan. A focused added check of DZ's complete overlap identity passed at all 63 roots.

At R=7 the independently computed complete vector is (-6,4,1,0,1,1), Q=1, D_G=55, D_S=32. The ordinary doubled cross term is -54; divisor-weighted cross is -44; diagonal multiplicity costs +21; hence D_S-D_G=-23=21-44. The +10 worsening confirms DZ2b without refuting H_Z. At R=3, D_S=8>D_G=4 remains the excluded boundary, not a counterexample to H_Z's R>=4 statement.

The verifier first passed the registered NP/GD domain; it was then extended ONLY with the focused DZ overlap check and rerun successfully. Both completed versions had zero failures. The final executed program and output are embedded below; their SHA-256 hashes are recorded in the appendix. No local Lean, large prime sweep or unfinished computation remains.

### L. Formalization Guidance

Independently ACCEPTED supporting candidates are NT2-NT3 and GD1-GD4, with their actual hypotheses. GD3 is useful chiefly as a no-circularity/source-tail theorem; do not prioritize a new conditional wrapper in place of the independent norm. FFR1-FFR4 now have Referee acceptance, so the existing #1131 finite approximation may feed the complete original contour, all-positive-argument inversion, raw physical return and native endpoint. Do not assume a response bound to finish the endpoint.

New NP1-NP3 require independent review before they are treated as accepted implementation input. A focused finite statement is `sum_(p<=H, prime)c_p^2 <= 48*V_N(c)` for arbitrary original finite real coefficients, plus the exact prime residual recovery including p=2. The infinite Gram calculation above is a paper proof supplier; a Lean implementation may use a finite dominated Gram bound instead if all constants and mixed terms are preserved. Then the original complete-error lower bound or exact-head variance growth is the substantive consumer.

No Lean source or feature branch was edited by this role. The accepted paper theorem is not labeled PROVED_IN_LEAN merely because its source definitions or a related PR compile.

### M. Specialist Handoffs

- Coordinator: register GD3 as independently accepted exponent equivalence, not an easier missing norm. FFR1-FFR4 are independently accepted as an implementation simplification of the existing IR paper boundary. NP proposes a stronger full-source restriction, pending someone else's review. Keep b_cert unchanged.
- Analytic: independently review NP's prime Gram, especially the p^2 contribution on the diagonal, positive off-diagonal zeta(2)/(pq), and p=2 dual norm 14. Replace only bounded-V suppliers, not the full Nyman route. NT2-NT3 are accepted at their stated scope.
- Wheel: GD1-GD4 are accepted on paper. Keep all c>1/2 constants and finite-iteration loss spending; do not evaluate Z_c at c=1/2 or infer pointwise D_G<=C Q^2. A genuinely independent improved complete norm remains the needed arithmetic.
- Census: preserve H_Z/GC5 as conjectures. R=7's +10 and the full overlap identity are independently reproduced. A useful changed test is NP's exact-head bound on actual full-basis/flat-taper coefficients, with complete E certificates, not an unchanged larger sign scan.
- Owner: MC's original-mask caution remains; no Nyman/Hecke recovery has been claimed for it. Any completion estimate still needs the actual coefficient/occurrence bridge and its full commutator, historical anchor, squareful and cross-row bills.
- Lean Verification: reuse #1131 and implement one accepted complete finite FFR return if feasible. For NP, obtain independent mathematical review first; do not convert a self-audit into Referee independence. GD and NT are supporting accepted options, not mandates to increase theorem count.

### N. First Independently Missing Mathematical Ingredient

For the existing accepted OAI paper gain: the missing item remains kernel-verified COMPLETE response/contour/inversion/raw-return assembly and its actual Mertens consumer. FFR supplies a narrower implementation, not a new arithmetic premise.

For NYMAN: an independently proved complete E_N(c_N)->0 (or a justified weighted-exponent analogue) with the original full head, middle, tail and correction. NP requires V_N(c_N)->infinity for any successful sequence; it does not supply the missing error estimate or require a specific rate for the true tail.

For GD: an independent estimate on D_G of improved exponent, or on the actual K_R-normalized complete source. Its every-positive-loss exponent is already equivalent to Mertens growth, and neither sign conjecture nor identity alone pays it. Canonical RH remains OPEN across the portfolio.

### O. Next-Run Resume Capsule

```text
RUN=20261111-referee-1/NP; scheduled trigger 04:13:01 EST.
MAIN=f7947bee036c4dddb0c36fc9f53ab46b4fa90995.
ACK=CROSS_ROUTE_SIGNED_RECOVERY_V1.
INTAKE_REPORTS=702daede309826ef9106c80ac1397ed20526550f.
NEW_SELF_AUDIT=NP1 prime-functional Gram and uniform Bessel bound;
  NP2 full Nyman density forces V->infinity;
  NP3 exact-head growing variance and bounded-V positive error floor.
ACCEPT=20261111-analytic-1/NT1-NT3; 20261111-wheel-1/GD1-GD4;
  20261110-coordinator-2309-EST/FFR1-FFR4, all at paper scopes.
REPRODUCED=20261111-census-1/DZ2b,DZ2c R=7 / complete overlap.
GC5,H_Z=UNRESOLVED CONJECTURES; no large repeated scan.
COMPILED=b_cert=7/8-7/(64*N_pack), unchanged.
PAPER_ACCEPTED=b_IR=7/8-1/2400000000, unchanged from IRR.
PR1131=green non-draft UNMERGED, head 621f48b34b5ace39c05aba33ff33b6d014544b4d.
NEXT=independent review of NP and complete finite FFR implementation;
  no repeat of unchanged baseline or old sign scans without new hypotheses.
NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE; RH=OPEN.
```

Checkpoint commit cabd68f8d4d7ab10c4fc572d72baeceb39562452, blob 1260f3dc3683d8c1feb831a3a03d0151d7aede4f, was read back exactly. Final research execution is finished; final publication is claimed only after immutable readback below. Tool limitation: direct git transport returned CONNECT 403; connector retrieval and own-report publication work. No main, Lean, other report, issue, proof branch, PR, workflow, schedule, permission or agent-launch modification occurred.

## Material Evidence And Reproduction Appendices

### Source And Handoff Ledger

Final authority refresh at 2026-11-11 09:35:22 UTC (04:35:22 EST) found main unchanged at f7947bee036c4dddb0c36fc9f53ab46b4fa90995; agent-reports remained at the verified checkpoint cabd68f8d4d7ab10c4fc572d72baeceb39562452, whose parent is the intake snapshot 702daede309826ef9106c80ac1397ed20526550f. Therefore no new upstream handoff was silently missed. Coordinator and Lean remain TODAY=PENDING / YESTERDAY=CARRY_FORWARD. The only open PR is still non-draft #1131 at the same tested head.

Material source files fetched and inspected at current main (scope of reuse and exact hosted checks is stated in Section B):

| Main source, pinned to actual commit | Git blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/AGENTS.md) | `c9c89f01b90b526de9f3e8ea92478e36504711b6` |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/CURRENT_PROOF_CONTRACT.md) | `95566e37c8eaeb99ee680660df4f9d2e06ea5038` |
| [docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md) | `e922d4ba9362a1ae196af8f6de88f7417f92087c` |
| [research/NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean) | `2da630c1d5fb9302e2097ec1e170cf41c2b40609` |
| [research/NYMAN_FLAT_TAPER_RETURN_20261104.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/NYMAN_FLAT_TAPER_RETURN_20261104.lean) | `2d23721027ecc44e85b7add02fc632b482f03352` |
| [research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md) | `b2775c892edffe920a101651eef6f3581c73c9d4` |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919WindowErrorClosure.lean) | `f629db1b2b65d6ec042ac9432397d4b6316200c6` |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | `1f17f9401a63d16227db2e2aad020b9f74bc5f4e` |
| [research/oai_434/VF919ExplicitSquareBlockPacking.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | `32999039fdeea99c58a070c1c4ee9c140720dd44` |
| [research/oai_434/VF919ExplicitFixedSourceSlotCount.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) | `bad5aab0a60e96d19e7c9550cd7c0a072288bc0f` |
| [research/oai_434/VF919ExplicitSlotTotalMass.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919ExplicitSlotTotalMass.lean) | `71c5b7b5b8032ca3558467126fdf97d3caf1a7df` |
| [research/oai_434/VF919NativeStrictMertens.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919NativeStrictMertens.lean) | `b33a4883e1ddb0551b0f11f062bce46680d87450` |
| [research/oai_434/VF919NativeSevenEighthsReplay.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919NativeSevenEighthsReplay.lean) | `111c933a7ca15647105ce6a4d0f3cbfc3cde81f4` |
| [research/MERTENS_EXPONENT_ENVELOPES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/MERTENS_EXPONENT_ENVELOPES.lean) | `655b896e8d5a41c9f8fc3c456eae3944a98bfefe` |
| [research/oai_434/VF919FiniteSlotReflectedGain.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919FiniteSlotReflectedGain.lean) | `a5545b5a00958b69f6fbfd79fc555a0476aa6487` |
| [research/EULER_SELF_DUAL_POINTWISE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_SELF_DUAL_POINTWISE_20261027.lean) | `c327c556f39ee7014fd774b24d0f95a1ece050e0` |
| [research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean) | `e97561ef330a9996fd807d8910369f0698147b01` |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73` |
| [research/EULER_HYBRID_TRIANGULAR_GRAM_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/EULER_HYBRID_TRIANGULAR_GRAM_20261027.lean) | `02fbe396b7e40fe4ac8c832970abafef31f67788` |
| [research/CompleteSquareRootWheelFractionalBoundary.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/CompleteSquareRootWheelFractionalBoundary.lean) | `ecb482e52deeee5e9b3853592a3ffdace662d2ff` |
| [research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |
| [docs/PROOF_DEPENDENCY_DAG.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/PROOF_DEPENDENCY_DAG.md) | `eee764cefe70035a9f6c7df26ad787fbfd0fb233` |
| [docs/COORDINATE_ATLAS.md](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/docs/COORDINATE_ATLAS.md) | `cd0419d00a37739fe5a292f5cb738e33213949d5` |

Separate source scopes:

| Source | Ref / blob / evidence scope |
| --- | --- |
| [PR #1131 finite response](https://github.com/OVVO-Financial/RH_Lean/blob/621f48b34b5ace39c05aba33ff33b6d014544b4d/research/oai_434/VF919PrincipalFiniteResponse.lean) | PR HEAD 621f48b34b5ace39c05aba33ff33b6d014544b4d; blob `8c7f21b34402758b18ce42f4484f518c4090c105`; fetched original theorem and actual hosted job. NOT main. |
| [Upstream Signal.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Hecke/Signal.lean) | Pinned upstream 1581d4cbdd69a0faf34b2089614fe2a814316a6a; blob `9b0f1f6ff5f74c77fee06327c4936c2a9e180df5`; all-positive-argument contour and small-argument theorem hypotheses inspected. |
| [Main signed remainder](https://github.com/OVVO-Financial/RH_Lean/blob/f7947bee036c4dddb0c36fc9f53ab46b4fa90995/research/oai_434/VF919PrincipalSignedRemainder.lean) | Blob `a41fee91754d5f6e5606f3f6f3dfe66031d81cbf`; tree unchanged and exact-head #1130 log refreshed, prior independent SR paper audit reused. No claim of a new line-by-line rereview of the unchanged module. |
| [External handoffs](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/EXTERNAL_HANDOFFS.md) | Blob `038018145c0fddb2f6306c0712373adf9cd1ea52`; available relevant entries read. |

Two-day reports, all pinned to the intake reporting snapshot rather than a moving branch. The Coordinator PM mirror has exactly the fetched AM blob, so the same verified bytes supply both:

| Original report | Git blob SHA |
| --- | --- |
| [2026-11-10/00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-10/00-coordinator-am.md) | `4d55b2893f974656c6aa14e48b243827fa8308f8` |
| [2026-11-10/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-10/10-owner-payment.md) | `84afec90414b2394a61b51df46c07b6b540e5942` |
| [2026-11-10/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-10/20-analytic-type-ii.md) | `7ed3a39bec4796f4173b692064af872ea8035048` |
| [2026-11-10/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-10/30-finite-wheel.md) | `62406503a1ddbbf9330abcdc4cf761f7fbf05795` |
| [2026-11-10/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-10/40-prime-census.md) | `a3cfa56072f3893dbf92a18956e1794236bde057` |
| [2026-11-10/50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-10/50-adversarial-referee.md) | `6529562a5bb21fa192fddadaa91a758b9d125c29` |
| [2026-11-10/60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-10/60-lean-verification.md) | `682b334b8f37fa4bfe2d552a1142d852a0db2afd` |
| [2026-11-10/90-coordinator-pm.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-10/90-coordinator-pm.md) | `4d55b2893f974656c6aa14e48b243827fa8308f8` |
| [2026-11-11/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-11/10-owner-payment.md) | `e60f67d2192932715895f9e9b72a6fe773d4a68d` |
| [2026-11-11/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-11/20-analytic-type-ii.md) | `eab26782cdd44e705e007185d6c7321d9300ca61` |
| [2026-11-11/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-11/30-finite-wheel.md) | `dbf68d8f8b1737b4b585811dae014329614ec595` |
| [2026-11-11/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/702daede309826ef9106c80ac1397ed20526550f/research/agent_reports/2026-11-11/40-prime-census.md) | `49c1c48f672cf96c93909bd2b412d95bb3587d62` |

Hosted evidence inspected directly: [#1119 dependency job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700), [#1130 signed-remainder job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42877550772/job/130044786387), and [#1131 complete finite-product job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42947849721/job/130284860499). These are scope-specific proof receipts, not claims of a new full-main build or of the full paper endpoint being formalized.

### Exact Independent Reproducer

Run with Python 3.12 and its standard library: `python referee_np_checks.py`. The program uses exact integers and fractions throughout. The source domains are declared in Section K and in the loops below. Assertions test finite identities and necessary inequalities, not the infinite density theorem.

Executed program SHA-256: `0e8dba09788feed5cd04e27875b44e22a22551f92f6fe310361e5d2183240bbd`.
Exact output SHA-256: `91f5a039a3c935df1d93f10eaabc7031d3fe7c3ebfd203cf8c57eb608d6daf51`.

```python
"""Exact independent checks for 20261111-referee-1/NP; no Lean execution."""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, isqrt, lcm
import json


@lru_cache(None)
def factor(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            out.append((p, e))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def mu(n):
    fs = factor(n)
    return 0 if any(e > 1 for _, e in fs) else (-1) ** len(fs)


def phi(n):
    value = n
    for p, _ in factor(n):
        value = value // p * (p - 1)
    return value


def jordan(n):
    value = n * n
    for p, _ in factor(n):
        value = value // (p * p) * (p * p - 1)
    return value


def prime(n):
    return n >= 2 and factor(n) == ((n, 1),)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def psd(matrix):
    # Exact symmetric elimination; no floating eigenvalue decisions.
    a = [row[:] for row in matrix]
    for i in range(len(a)):
        pivot = a[i][i]
        assert pivot >= 0
        if pivot == 0:
            assert all(a[i][j] == 0 for j in range(i + 1, len(a)))
            continue
        for j in range(i + 1, len(a)):
            for k in range(j, len(a)):
                a[j][k] -= a[j][i] * a[i][k] / pivot
                a[k][j] = a[j][k]


count = Counter()
optimizer_rows = []
zeta_upper = sum((F(1, n * n) for n in range(1, 65)), F(0)) + F(1, 64)
assert zeta_upper < 2

for N in range(2, 25):
    S = sum((F(phi(d) ** 2, jordan(d)) for d in range(2, N + 1)), F(0))
    optimum = {k: F(2 * k, 1) / S * sum(
        (F(mu(j) * phi(k * j), jordan(k * j)) for j in range(1, N // k + 1)), F(0))
        for k in range(2, N + 1)}
    vectors = [
        {k: F(0) for k in range(2, N + 1)},
        {k: F(-mu(k)) for k in range(2, N + 1)},
        {k: F((-1) ** k, k) for k in range(2, N + 1)},
        {k: F(k % 5 - 2, k + 1) for k in range(2, N + 1)},
        {k: F((k * (k - 1)) % 7 - 3, 3) for k in range(2, N + 1)},
        optimum,
    ]
    primes = [p for p in range(2, N + 1) if prime(p)]
    gram = [[sum((F(p * q * mu(d // p) * mu(d // q), jordan(d))
                  for d in range(2, N + 1) if d % p == d % q == 0), F(0))
             for q in primes] for p in primes]
    for i, p in enumerate(primes):
        tp = lambda b: sum((F(mu(h) ** 2, jordan(h))
                            for h in range(1, b + 1) if h % p), F(0))
        assert gram[i][i] == F(p * p, p * p - 1) * tp(N // p) + F(1, p * p - 1) * tp(N // (p * p))
        for j, q in enumerate(primes):
            if i != j:
                tail = sum((F(mu(h) ** 2, jordan(h)) for h in range(1, N // (p * q) + 1)
                            if gcd(h, p * q) == 1), F(0))
                assert gram[i][j] == F(p * q, (p * p - 1) * (q * q - 1)) * tail
            count['prime_gram_entries'] += 1
    psd([[zeta_upper * (int(i == j) + F(1, p * q)) - gram[i][j]
          for j, q in enumerate(primes)] for i, p in enumerate(primes)])
    count['rational_gram_psd'] += 1

    for c in vectors:
        q = {d: sum((c[k] / k for k in range(2, N + 1) if k % d == 0), F(0))
             for d in range(1, N + 1)}
        V = sum((F(jordan(d), 12) * q[d] ** 2 for d in range(2, N + 1)), F(0))
        direct = sum((F(gcd(k, ell) ** 2 - 1, 12 * k * ell) * c[k] * c[ell]
                      for k in c for ell in c), F(0))
        assert direct == V >= 0
        assert q[1] == -sum((mu(d) * q[d] for d in range(2, N + 1)), F(0))
        for k in c:
            assert c[k] == k * sum((mu(j) * q[k * j] for j in range(1, N // k + 1)), F(0))
            assert c[k] ** 2 <= 48 * V
            count['multiples_inverse'] += 1
        prime_square = sum((c[p] ** 2 for p in primes), F(0))
        assert prime_square <= 12 * zeta_upper * (1 + sum((F(1, p * p) for p in primes), F(0))) * V
        assert prime_square <= 48 * V
        count['variance_and_prime_bound'] += 1
        residual = {m: 1 - sum((c[k] * F(m % k, k) for k in c), F(0))
                    for m in range(0, 2 * N + 1)}
        for n in range(2, 2 * N + 1):
            recovered = sum((mu(n // d) * (residual[d] - residual[d - 1])
                             for d in divisors(n)), F(0))
            assert recovered == c.get(n, F(0))
            count['full_coefficient_recovery'] += 1
        for p in range(2, 2 * N + 1):
            if prime(p):
                assert c.get(p, F(0)) == 1 - residual[1] + residual[p] - residual[p - 1]
                head = sum((residual[m] ** 2 / (m * (m + 1)) for m in range(1, p + 1)), F(0))
                assert (c.get(p, F(0)) - 1) ** 2 <= 4 * p * p * head
                count['prime_head_recovery_and_error'] += 1
        for M in (1, 2, N, 2 * N):
            head = sum((residual[m] ** 2 / (m * (m + 1)) for m in range(1, M + 1)), F(0))
            harmonic = F(0)
            bill = F(0)
            for m in range(1, M + 1):
                harmonic += F(1, m)
                bill += harmonic / (m + 1)
            gap = 1 - F(1, M + 1) - head
            if gap > 0:
                assert gap * gap <= 196 * V * bill * bill
            count['NT2_complete_head_lower_bound'] += 1
        if N <= 8:
            period = lcm(*range(2, N + 1))
            mean = sum((c[k] * F(k - 1, 2 * k) for k in c), F(0))
            periodic = sum(((sum((c[k] * F(m % k, k) for k in c), F(0)) - mean) ** 2
                            for m in range(period)), F(0)) / period
            assert periodic == V
            count['literal_full_period_variance'] += 1
        if c == optimum:
            assert sum((c[k] * F(k - 1, 2 * k) for k in c), F(0)) == 1
            assert V == 1 / (3 * S)
            h = {d: F((-1) ** d, d + 1) for d in range(2, N + 1)}
            defect = sum((phi(d) * h[d] for d in h), F(0))
            h[2] -= defect / phi(2)
            perturbed = sum((F(jordan(d), 12) * (q[d] + h[d]) ** 2 for d in h), F(0))
            correction = sum((F(jordan(d), 12) * h[d] ** 2 for d in h), F(0))
            assert perturbed == V + correction
            count['NT3_optimizer_and_stability'] += 1
            if N in (2, 4, 8, 16, 24):
                optimizer_rows.append({'N': N, 'V': str(V), 'q1': str(q[1])})

head_rows = []
for H in (2, 3, 5, 8, 16, 32, 64, 128):
    N = next(p for p in range(H + 1, 2 * H + 3) if prime(p))
    c = {k: F(-mu(k)) if k <= H else F(0) for k in range(2, N + 1)}
    c[N] = N * (1 - sum((c[k] / k for k in c), F(0)))
    for m in range(1, H + 1):
        assert sum((c[k] * F(m % k, k) for k in c), F(0)) == 1
    q = {d: sum((c[k] / k for k in c if k % d == 0), F(0)) for d in range(2, N + 1)}
    V = sum((F(jordan(d), 12) * q[d] ** 2 for d in q), F(0))
    prime_count = sum(prime(p) for p in range(2, H + 1))
    assert V >= F(prime_count, 48)
    head_rows.append({'H': H, 'N': N, 'prime_count': prime_count, 'V': str(V)})
    count['exact_head_variance_obstruction'] += 1


@lru_cache(None)
def M(n):
    return sum(mu(k) for k in range(1, n + 1))


for T in range(1, 41):
    for A in range(1, T + 1):
        for B in range(1, T + 1):
            if T >= (A + 1) * (B + 1):
                continue
            value = sum(mu(a) * mu(b) * (T // (a * b))
                        for a in range(1, A + 1) for b in range(1, B + 1))
            assert value == M(A) + M(B) - M(T)
            count['GD_strict_rectangles'] += 1
assert 4 != 2 * M(1) - M(4)
count['GD_equality_wall_negative_control'] += 1
gcd_rows = []
for R in range(2, 65):
    X, N = R * R - 1, R - 1
    C = [0] * R
    S = [0] * R
    for a in range(1, R):
        for b in range(1, R):
            C[gcd(a, b)] += mu(a) * mu(b) * (X // (a * b))
    for d in range(1, R):
        B = N // d
        smooth = [h for h in range(1, B + 1) if all(d % p == 0 for p, _ in factor(h))]
        S[d] = mu(d) ** 2 * sum(M(B // h) + M(B // k) - M(X // (d * d * h * k))
                                for h in smooth for k in smooth)
        assert S[d] == sum(C[g] for g in range(d, R, d))
        assert all(max(B // h, B // k) <= X // (d * d * h * k) < (B // h + 1) * (B // k + 1)
                   for h in smooth for k in smooth)
        count['GD_common_divisor_reconstruction'] += 1
    for g in range(1, R):
        assert C[g] == sum(mu(k) * S[g * k] for k in range(1, N // g + 1))
        count['GD_gcd_inverse'] += 1
    assert sum(C) == 2 * M(N) - M(X)
    if R in (3, 7, 15, 17, 64):
        gcd_rows.append({'R': R, 'Q': sum(C), 'DG': sum(x * x for x in C),
                         'DS': sum(x * x for x in S)})
    ordinary = 2 * sum(C[g] * C[h] for g in range(1, R) for h in range(g + 1, R))
    weighted = 2 * sum(len(divisors(gcd(g, h))) * C[g] * C[h]
                       for g in range(1, R) for h in range(g + 1, R))
    cost = sum((len(divisors(g)) - 1) * C[g] ** 2 for g in range(1, R))
    assert sum(x * x for x in S) - sum(x * x for x in C) == cost + weighted
    if R == 7:
        assert weighted - ordinary == 10
        gcd_rows[-1].update({'C': C[1:], 'ordinary_cross': ordinary,
                             'divisor_weighted_cross': weighted, 'overlap_cost': cost})
    count['DZ_complete_overlap_identity'] += 1
for b in (F(1, 2), F(3, 5), F(3, 4), F(7, 8)):
    c = F(1)
    for j in range(1, 21):
        alpha = 4 * (c - b) / (4 * c - 1)
        nxt = b + (c - b) / (4 * c - 1)
        assert 0 < alpha < 1 and b < nxt < c
        assert 2 * b + alpha / 2 == 2 * c + alpha * (1 - 2 * c) == 2 * nxt
        if b == F(1, 2):
            assert nxt == F(1, 2) + F(1, 4 * j + 2)
        c = nxt
        count['GD_exact_exponent_iterations'] += 1

print(json.dumps({'status': 'PASS_EXACT', 'counts': dict(count),
                  'optimizer_rows': optimizer_rows, 'exact_head_rows': head_rows,
                  'gcd_rows': gcd_rows, 'zeta2_rational_upper': str(zeta_upper)}, indent=2))
```

Completed output:

```json
{
  "status": "PASS_EXACT",
  "counts": {
    "prime_gram_entries": 801,
    "rational_gram_psd": 23,
    "multiples_inverse": 1656,
    "variance_and_prime_bound": 138,
    "full_coefficient_recovery": 3450,
    "prime_head_recovery_and_error": 1218,
    "NT2_complete_head_lower_bound": 552,
    "literal_full_period_variance": 42,
    "NT3_optimizer_and_stability": 23,
    "exact_head_variance_obstruction": 8,
    "GD_strict_rectangles": 20899,
    "GD_equality_wall_negative_control": 1,
    "GD_common_divisor_reconstruction": 2016,
    "GD_gcd_inverse": 2016,
    "DZ_complete_overlap_identity": 63,
    "GD_exact_exponent_iterations": 80
  },
  "optimizer_rows": [
    {
      "N": 2,
      "V": "1",
      "q1": "2"
    },
    {
      "N": 4,
      "V": "2/7",
      "q1": "1"
    },
    {
      "N": 8,
      "V": "4/37",
      "q1": "19/37"
    },
    {
      "N": 16,
      "V": "42/829",
      "q1": "407/1658"
    },
    {
      "N": 24,
      "V": "840/26443",
      "q1": "9029/52886"
    }
  ],
  "exact_head_rows": [
    {
      "H": 2,
      "N": 3,
      "prime_count": 1,
      "V": "11/48"
    },
    {
      "H": 3,
      "N": 5,
      "prime_count": 2,
      "V": "83/432"
    },
    {
      "H": 5,
      "N": 7,
      "prime_count": 3,
      "V": "2387/10800"
    },
    {
      "H": 8,
      "N": 11,
      "prime_count": 4,
      "V": "4997/18900"
    },
    {
      "H": 16,
      "N": 17,
      "prime_count": 6,
      "V": "23093341/42942900"
    },
    {
      "H": 32,
      "N": 37,
      "prime_count": 11,
      "V": "23530491162073950529249/17877560089415923296400"
    },
    {
      "H": 64,
      "N": 67,
      "prime_count": 18,
      "V": "43877961205494817927648838988914888078062775429/23582681831845173638840234679615572143919816400"
    },
    {
      "H": 128,
      "N": 131,
      "prime_count": 31,
      "V": "1698995200532897418571189326785474296735139378927925342144860146069973866938912503440594850488646/483480752893102257691652042292290499537041657420379329900316931005209078735766325073857304104587"
    }
  ],
  "gcd_rows": [
    {
      "R": 3,
      "Q": 2,
      "DG": 4,
      "DS": 8
    },
    {
      "R": 7,
      "Q": 1,
      "DG": 55,
      "DS": 32,
      "C": [
        -6,
        4,
        1,
        0,
        1,
        1
      ],
      "ordinary_cross": -54,
      "divisor_weighted_cross": -44,
      "overlap_cost": 21
    },
    {
      "R": 15,
      "Q": -7,
      "DG": 223,
      "DS": 142
    },
    {
      "R": 17,
      "Q": 5,
      "DG": 173,
      "DS": 138
    },
    {
      "R": 64,
      "Q": 17,
      "DG": 36839,
      "DS": 3673
    }
  ],
  "zeta2_rational_upper": "41806991420017334818304786694254270947722161043649859/25413727004476294175336659010085214676345183380992000"
}
```

## Verified Publication Receipt

Execution status: COMPLETED. Publication status: PUBLISHED_VERIFIED.

At 2026-11-11 09:39:40 UTC (04:39:40 EST), the complete substantive report was retrieved at immutable commit [699de1abd45c69c0b4b579e30ca0bff686d13337](https://github.com/OVVO-Financial/RH_Lean/commit/699de1abd45c69c0b4b579e30ca0bff686d13337) and matched the submitted 70,947 ASCII bytes exactly. Git blob: `ae59d62ffe23770a5460dfe1ff3559d09813e8a8`. SHA-256 of that substantive report, before this receipt: `4e1568d27319ce7393072ffd91433fc320983f9635341cbc546a5640165b3b83`.

The actual commit diff contains exactly the owned daily `50-adversarial-referee.md` path, with 900 additions and ZERO deletions. The original checkpoint is preserved byte-for-byte. This receipt records that already verified publication, not a prediction of its own subsequent commit. Mathematical status is unchanged: NP1-NP3 PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING; NP4 FINITE_COMPUTATION; no new certified global exponent and RH remains OPEN.
