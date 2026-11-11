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


## Scheduled Continuation Checkpoint - 20261111-referee-2/HR

Status: IN_PROGRESS / PARTIAL. Actual scheduled trigger: 2026-11-11 12:03:01 EST (America/New_York). Platform RUN_ID_UNAVAILABLE; HR is a research label. Checkpoint runtime: 2026-11-11 17:07:00 UTC.

cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1. Preserve all earlier same-day NP claims, reviews, computations and receipts without alteration.

### A. Selected Investigation
Independently review 20261111-wheel-2/PD1-PD4 and 20261111-census-2/UM1,UM4,UM5: the complete historical/powerful gcd decomposition, strict-history norm, exact R=115 nonunit-response failure, and the radical contraction form. Seek a rigorous growing-family obstruction to proofs based only on sparse radical support, and a corrected interaction criterion. Do not attribute an arbitrary-coefficient obstruction to genuine Mertens values. H_ROB/H_PRE/H_Z/GC5 remain unproved; no new sign scan is registered beyond exact source verification and the R=115 minimum certificate.

### B. Authority And Continuity
main=dda92f9ce59627b4c1f1317082f728648d330a0a; AGENTS blob=c9c89f01b90b526de9f3e8ea92478e36504711b6; CURRENT_PROOF_CONTRACT blob=95566e37c8eaeb99ee680660df4f9d2e06ea5038; cross-route directive blob=e922d4ba9362a1ae196af8f6de88f7417f92087c.
Reports intake=1855dcff615963978e73bddf4779e9630420a549. All seven roles are TODAY=AVAILABLE; relevant November 10 work is YESTERDAY=CARRY_FORWARD. Both coordinator mirrors have matching blobs on both dates. All reports were retrieved; relevant latest proofs and resume sections are being read, not collectively accepted. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no new entry after October 18.
Latest handoffs: Coordinator FL; Owner FA; Analytic DM; Wheel PD; Census UM; own NP; Lean FFR mass. #1131 is now main according to the main merge record; exact head, CI, source and transitive-baseline evidence are PENDING independent refresh. The open/draft PR collection was empty at intake.

### C. Preregistered Checks And Scope
Use newly written exact integer/rational code to enumerate the genuine gcd floor pairs and reconstruct every historical/powerful component for R=2..128 and R=549; verify the first H_F failure over every R=4..115, complete unit/historical restoration, and strict rectangle endpoints. Test proof-led abstract squarefree-divisor families separately with explicit MODEL-ONLY labels; no genuine coefficient freedom is assumed. Any larger test requires a changed mathematical discriminator. No computation result is claimed yet.

### D-O. Remaining Work And Limitations
PENDING: mathematical proof audit; original-source and baseline/CI refresh; exact checks; strongest surviving statement; five-stage capsule and A-O synthesis; final publication/readback. No local Lean execution and no source/PR/policy changes. Direct git clone failed with CONNECT tunnel 403; authorized GitHub connector reads work. Only this owned daily report will be written remotely.


## Shared-Prime Interactions, Not Sparse Support, Govern Response Contraction

### Final Research Synthesis - 20261111-referee-2/HR

Scheduled trigger: 2026-11-11 12:03:01 EST, America/New_York. Platform RUN_ID_UNAVAILABLE. This is an appended continuation, not a replacement of today's NP report. `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. Research is complete; final publication is established only by the later immutable readback receipt.

### A. Most Important Mathematical Finding

**ACCEPT Wheel PD1-PD4 at their exact paper scopes and Census UM1/UM5; independently verify UM4's smallest genuine counterexample R=115.** The nonunit powerful response has squared norm 404, while its common-divisor transform has squared norm 599. Its gap is -195. The COMPLETE genuine source still has positive gap 18,331 after the historical and endpoint terms are restored. This refutes the stated auxiliary H_F, not H_ROB, H_Z, finite A/C, or RH.

**New supporting theorem HR1:** negative nonunit gap requires a sufficiently negative SHARED-PRIME interaction. Pairwise-coprime nonunit squarefree radical supports always have nonnegative gap, even when their radicals are composite and their real coefficients have arbitrary signs. This strictly extends UM5's prime-only repair. In the actual R=115 witness the exact nonnegative reserve is 477 and the shared-prime bill is -672, explaining the -195 without discarding coprime cross terms.

**New method-specific no-go HR2:** admissible powerful support and zero scalar column totals give neither a uniform upper nor a positive uniform lower comparison between response energy and radical-coefficient energy. On a k-prime divisor family the all-positive coefficients have energy 2^k-1 but response energy exactly 2. Another explicit sign choice has response energy 5^k-2^(k+1)+1. These are infinite MODEL families respecting the literal divisor incidence and cutoff, NOT genuine Mertens assignments. They rule out support-only norm arguments, not an arithmetic theorem exploiting the dependent Mertens coefficients or historical interactions.

HR1-HR2 are PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. HR3 is the executed exact audit. No new global exponent, accepted new RH route, or Lean endpoint is asserted. `NO_NEW_GLOBAL_GAIN; VERIFIED_ETA=NONE; RH=OPEN`.

### B. Current Authoritative Objective

Main is **dda92f9ce59627b4c1f1317082f728648d330a0a**. AGENTS blob `c9c89f01b90b526de9f3e8ea92478e36504711b6`, proof contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`, and governing cross-route directive `e922d4ba9362a1ae196af8f6de88f7417f92087c` were fetched from that commit. The newer cross-route priority supersedes dated single-route task selection, not valid statements or source safeguards.

The canonical OPEN statement remains one C>=0, before every integer R>=2, such that |pi(R^2)-vfCanonical(R^2)|<=C R log R. `riemannHypothesis_of_vfCanonicalSquare` still takes BOTH `ClassicalVonKochRHCriterion` and the arithmetic tracking premise. The separate internally proved Mertens-energy consumer does not pay its own arithmetic premise. The complete wheel identity is F_R-D_R=li(R^2-1)-pi(R^2-1), with all virtual divisors restored; it is not an equality with the bilinear Mobius source below.

#### 1. BASELINE / DEPENDENCY RECEIPT

The strongest explicit fixed-family COMPILED comparator inspected remains

```text
native_mertens_near_uniform_window_error_closed
  : MertensGrowthAtMost(b_Lean),
b_Lean=7/8-7/(64*N_pack).
MertensGrowthAtMost(b):
  forall eps>0 exists C_eps>=0 forall integers n>=1,
    |M(n)|<=C_eps*n^(b+eps).
```

The source declaration has no desired-growth antecedent. Its original-source construction, counts, native moments, complete total-mass LOW/anchored HIGH/principal comparison, Hecke zero supremum, modulus-one L-product and native Mertens converse are the audited dependency chain. The moment supplier retains 51/100<=beta<=7/8+Delta, fixed fine geometry, J before the character, and C,Z0 before height and scale. It is not an arbitrary-profile theorem.

For the SAME independently fixed positive explicitFineLength L, the actual definitions read here are N_pack=ceil_nat(max(1,1/(6L)))+2 and N_old=ceil_nat(max(1,1/(3L)))+2. Thus N_pack<=N_old and 7/(64N_pack)>1/(48N_old). No identification of the counts, optimization over all sources, or zero-loss bound is asserted.

Fresh evidence: #1119 is merged; head `77ee815846d6d534c866f0752aa33b84c385610a` has 14/14 successful checks. The actual [dependency/axiom job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700) and its implementation were read. The five selected proof-value closures have sizes 35358,35375,35736,35737,35753, with only propext, Classical.choice, Quot.sound. A fresh tree comparison found **zero changes among 911 preexisting relevant source/audit blobs** between the tested head and current main. This legitimately reuses scoped certification; it is not a fresh main build, an independent reproving of every analytic dependency, or a claim that every historical imported module is placeholder-free.

Pins verified in the hosted logs: Lean 4.34.1/compiler `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; openai/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. The warning-fatal target commands and actual selected-root axiom results were inspected, not inferred from a green badge. Historical upstream/package warnings are not represented as clean whole-repository compilation.

The stronger accepted PAPER boundary b_IR=7/8-1/2400000000, with every positive loss and prior independently accepted fixed comparison eta_IR=737/3840000000000, is carried forward from IRR/FFR. The proof bytes and dependencies are available and unchanged. It is not promoted to the compiled comparator. Today's result improves neither that paper boundary nor b_Lean.

### C. Highest-Risk Mechanisms And Continuity

Reports were retrieved at `agent-reports@1855dcff615963978e73bddf4779e9630420a549`. All seven roles are TODAY=AVAILABLE. Relevant November 10 results are YESTERDAY=CARRY_FORWARD. Both coordinator mirrors have matching blobs on each date. Read the relevant latest findings, proofs for selected claims, handoffs and resume sections: Coordinator FFR/FL, Owner DR/MC/FA, Analytic IR/NT/DM, Wheel RC/GD/PD, Census GC/DZ/UM, own IRR/NP, and Lean finite-response/mass. These are provenance records, not collective acceptance.

The new PD/UM source and explicit R=115 request take priority in this continuation because they test a newly proposed explanation for complete gcd contraction. Coordinator FL1-FL5 and Analytic DM1-DM4 remain **PENDING separate independent review**. Their claims are not accepted, rejected or declared superseded merely because their headlines were read. Owner FA is likewise continuity, not a new verdict here. Earlier NP/GD/NT/FFR decisions are retained at their unchanged scopes.

External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no post-October-18 entry. Its cofactor/cutoff safeguards and unconditional-all-root versus conditional-first-bad distinctions remain applicable; its historical routing does not override main.

### D. Claims Reviewed

| Original claim | Verdict | Evidence and exact scope |
| --- | --- | --- |
| 20261111-wheel-2/PD1 | ACCEPT | PAPER_PROOF / supporting identity: complete historical/powerful split, ordered multiplicity, sparse support, distinct quotient sites and formal-coordinate rank. The rank is not freedom of genuine Mertens data. |
| PD2 | ACCEPT | PAPER_PROOF: uniform strict-history norm and COMPLETE high-gcd tail with the stated convergent absolute constants. No global Mertens estimate is assumed. |
| PD3 | ACCEPT_WITH_SCOPE | PAPER_PROOF: exact full Gram and sparse inverse inequality. The positive-weight parameter c must remain >1/2; the resulting witness is not excluded. |
| PD4 | ACCEPT_WITH_SCOPE | CONDITIONAL and TARGET_EQUIVALENT family audit. Fixed eta=0 is sufficient; no fixed zero-loss converse is asserted. The premise is unpaid. |
| PD5 | LIMITED_REPRODUCTION | 128 roots independently checked here, not the author's entire campaign or its R=5561 computation. |
| 20261111-census-2/UM1 | ACCEPT | PAPER_PROOF / identity: affine endpoint separation and quarter-horizon representation, with later M values dependent on genuine history. |
| UM4 / H_F | ACCEPT THE REFUTATION | Exact finite counterexample and minimality for the asserted R>=4 domain independently reproduced. H_F itself is REJECTED. |
| UM5 | ACCEPT | PAPER_PROOF: prime-only gap is a square; first arbitrary-coefficient indefinite support at R=37. Actual R=37 is not a counterexample. |
| UM2 | LIMITED_REPRODUCTION | Complete reconstruction on the declared 128-root domain; no claim to have repeated all 527 roots. |
| UM3 / H_PRE, H_ROB; H_Z; GC5 | UNRESOLVED | CONJECTURE. Finite agreement is not an all-scale proof. H_ROB is a stronger robustness condition, not automatically equivalent to H_Z. |
| #1131 complete finite response/mass | ACCEPT AT DECLARED SCOPE | PROVED_IN_LEAN_ON_MAIN with exact-head evidence and identical main/head tree. Not the complete Mellin/inversion/endpoint return. |
| 20261111-referee-2/HR1-HR2 | SELF_AUDIT | New supporting paper results below; no self-issued independent acceptance. |
| HR3 | EXECUTED | Exact original-source verification and explicitly separated model checks. |

### E. Independent Mathematical Reconstruction

#### Exact Original Carrier And PD1

For EVERY integer R>=2 set N=R-1, X=R^2-1, M(0)=0, M(t)=sum_(1<=n<=t)mu(n), and

```text
K_R=max_(0<=t<R) (M(t)-1)^2/(t+1),
C_g=sum_(1<=a,b<=N, gcd(a,b)=g)mu(a)mu(b)floor(X/(ab)),
S_d=sum_(d|g) C_g,  D_G=sum_g C_g^2,
Q=sum_g C_g=S_1=2M(N)-M(X).
```

The source counts ALL ordered triples (a,b,k), abk<=X, with genuine mu(a)mu(b). Equal products do not identify occurrences. This matches `eulerSelfDualFloor`, `eulerSelfDualBilinear`, their convolution bridge and `eulerSelfDualBilinear_eq_two_mertens_sub_endpoint` in the fetched original source. The historical envelope includes t=0 and its shift by 1, exactly as `LowerMertensCriticalEnvelope` requires.

For d<=N put B_d=floor(N/d), let H_d contain all positive d-smooth h<=B_d, A_h=floor(B_d/h), and T_dhk=floor(X/(d^2hk)). Define

```text
U_d=mu(d)^2 sum_(h,k in H_d)
      [M(A_h)+M(A_k)-1_(T_dhk<R)M(T_dhk)],
H_g=sum_(j<=N/g)mu(j)U_(gj).
```

For a powerful integer q (including 1), put d(q)=rad(q), a(q)=product_(p^e||q)(e-1), with a(1)=1. Let

```text
v_d(g)=1_(g|d)mu(d/g),
A_d=sum_(q<=N powerful, rad(q)=d) a(q)M(floor(X/q)),
E=sum_d A_d v_d.
```

Then PD1 asserts C=H-E, sum H=2M(N), sum E=M(X), E_g=0 for g^2>N, and #powerful(q<=N)<=3sqrt(N). Its response rank on FORMAL quotient coordinates is #{squarefree d:d^2<=N}.

Independent proof: mu(du)=mu(d)mu(u)1_(gcd(u,d)=1), and the compiled rough-Mobius/smooth-indicator convolution invert the coprimality restriction. Each resulting complete rectangle has max(A_h,A_k)<=T_dhk and
d^2hk(A_h+1)(A_k+1)>=R^2>X. The strict rectangular identity is therefore applicable. At (A,B,T)=(1,1,4) it would fail, so equality at the wall is not admitted. Next T_dhk>=R iff d^2hk<=N. In that range every ordered splitting of hk is admitted: neither factor exceeds B_d. Grouping q=d^2hk gives exactly the powerful multiplicity a(q). Multiples inversion now proves C=H-E.

The sum of v_d is zero except at d=1. Its support and triangular diagonal prove the asserted scalar totals, support and formal rank. Every powerful q has a unique representation a^2 b^3 with squarefree b, giving the bound 3sqrt(N). Also floor(X/q)>R for q<=N, and consecutive such quotient arguments differ by more than one before flooring. No independent unknown data have been added to the original source.

#### PD2: Historical Norm And Complete Tail

Write w(p)=(1-p^(-1/2))^-2, W(n)=product_(p|n)w(p), and define absolute constants

```text
E0=product_p(1+(w(p)-1)/p),
E2=product_p(1+(w(p)^2-1)/p),
Y =product_p(1+w(p)^2/p^2),
L_R=1+log N, C_H=9 E0 sqrt(Y).
```

The exact accepted bounds, with constants before every scale, are

```text
|H_g|<=9 E0 R sqrt(K_R)L_R mu(g)^2 W(g)/g,
||H||_2<=C_H R sqrt(K_R)L_R,
sum_(G<g<=N)C_g^2
 <=162 E0^2 E2 R^2 K_R L_R^2/G,
for every real G>=max(1,sqrt(N)).
```

Proof audit: K_R>=1 follows from t=0. For 1<=t<R, |M(t)|<=3sqrt(K_R t). The historical mask in U is applied BEFORE this estimate, giving |U_d|<=9R sqrt(K_R)mu(d)^2 W(d)/d. The finite-prime smooth geometric series pays W(d), even for growing d. Expand W(n)=sum_(e|n)h(e), h>=0, to obtain sum_(j<=N)W(j)/j<=E0 L_R. Nonzero inversion terms have squarefree coprime g,j, so W(gj)=W(g)W(j). This proves the pointwise and squared-norm bounds. The analogous expansion for W^2 yields sum_(n<=t)W(n)^2<=E2 t and sum_(n>G)W(n)^2/n^2<=2E2/G. Since E_g=0 above sqrt(N), the tail concerns actual C, not only H.

Convergence is uniform: w(p)-1=O(p^-1/2), so E0 and E2 have summable O(p^-3/2) local increments; Y has O(p^-2). This is an independently paid supporting estimate. It does not pay small-gcd E or the full D_G.

#### PD3-PD4: Inverse And No-Circularity

For squarefree d,e, <v_d,v_e>=mu(d)mu(e)2^omega(gcd(d,e)), where omega counts DISTINCT prime factors. Thus

```text
||E||^2=sum_(d,e)mu(d)mu(e)2^omega(gcd(d,e)) A_d A_e,
D_G=||H||^2+||E||^2-2<H,E>.
```

For any FIXED c>1/2 set
Lambda_c=product_p(1+sqrt(2)*p^(-2c)/(1-p^-c)^2)-1 and B_H=C_H R sqrt(K_R)L_R. If sqrt(D_G)>B_H+|M(X)|, then some powerful 4<=q<=N satisfies

```text
q^c |M(floor(X/q))|
 >= [sqrt(D_G)-B_H-|M(X)|]/Lambda_c.
```

This is exactly the weighted triangle on all NONUNIT columns, using ||v_d||=2^(omega(d)/2). Its Euler product converges for c>1/2, not at the asserted boundary c=1/2. It locates a necessary witness at an index between R+1 and floor(X/4); it does not exclude that witness or prove an endpoint.

For fixed 0<=eta<1/2, PD4's hypothetical ONE B before all R with ||E||<=B R^(1+eta)sqrt(K_R) implies MertensGrowthAtMost(1/2+eta), via accepted GD4. For eta>0 the historical logarithm is absorbed into R^eta; for eta=0 one must use each positive auxiliary loss, not claim a zero-loss bound for C. Conversely the critical Mertens growth statement supplies PD's estimate for EVERY positive eta via GD and the historical bound. This is a valid TARGET_EQUIVALENT family audit, not independent proof of its premise.

### F. Exact Counterexample And New No-Go

#### UM4: Genuine R=115, With Every Complement Restored

Here X=13224, M(114)=-6, M(X)=-9. Remove only the unit: A'=A-M(X)e_1, F=E-M(X)e_1. Their nonzero entries are

```text
(d,A'_d)=(2,-20),(3,-4),(5,-1),(6,-13),(7,-2),(10,-3),
(g,F_g)=(1,11),(2,-4),(3,9),(5,2),(6,-13),(7,-2),(10,-3).
sum F=0; ||F||^2=404; ||A'||^2=599; D_F=-195.
```

A newly written exact checker independently verifies EVERY R=4..115, so 115 is the smallest failure in the actual domain, not only the first root in a sparse sample. At R=37 the support permits a negative abstract form, but the genuine gap is +681.

Put Z=H-F, T_d=sum_(d|g)Z_g, B=sum_(g>=2)C_g and m=M(X). The accepted UM1 identity and complete restoration give

```text
D_H=||H||^2-||U||^2=18750,
J=-2(<H,F>-<U,A'>)=-1970,
Delta_0=||Z||^2-||T||^2=D_H+D_F+J=16585,
Delta=||C||^2-||S||^2=Delta_0+2mB=18331,
B=-97; 2mB=1746; H_ROB margin=16585-1746=14839.
```

Thus the historical mixed term is itself unfavorable here. Calling it automatic negative payment would also be wrong. At R=549 the independent check gives D_F=-1402, J=-50196, Delta_0=203220 and complete Delta=142548. R=5561 was not rerun; its upstream record remains finite continuity evidence only.

#### HR1: Exact Shared-Prime Bill And A Broader Valid Repair

Let D be ANY finite set of distinct nonunit squarefree integers, A_d ANY real numbers, and F=sum_(d in D)A_d v_d on the union of their divisor sets. Define b_d=mu(d)A_d and tau(d)=2^omega(d). The exact identity is

```text
||F||^2-sum_d A_d^2 = P(A)+Omega(A),
P(A)=(sum_d b_d)^2+sum_d (tau(d)-2)A_d^2 >=0,
Omega(A)=2sum_(d<e)(tau(gcd(d,e))-1)b_d b_e.
```

Proof: the full Gram is sum_(d,e)tau(gcd(d,e))b_d b_e. Split each off-diagonal factor as 1+(tau(gcd)-1), combine the 1's with a single diagonal copy into (sum b)^2, and subtract the original coefficient norm. The remaining diagonal coefficient is tau(d)-2>=0. No coprime cross term has been deleted; it is included in the square.

Consequences, all with complete quantifiers inherited from this finite statement:

- Pairwise-coprime nonunit squarefree supports have Omega=0 and therefore D_F>=0 for ALL real coefficients. Composite radicals are allowed. This strengthens the prime-only theorem.
- The same conclusion holds whenever all nonzero b_d have one sign, without a coprimality hypothesis. A common sign of A_d alone does NOT imply this parity-aligned condition.
- A negative gap requires Omega<-P. In particular at least one active pair shares a prime and has mu(d)mu(e)A_dA_e<0. Mere composite support or mere overlap is insufficient.

At the GENUINE R=115 coefficients, (sum b)^2=121, the remaining diagonal is 356, and the only nonzero shared-prime terms are

| Pair (d,e) | Exact contribution to Omega |
| --- | ---: |
| (2,6) | -520 |
| (2,10) | -120 |
| (3,6) | -104 |
| (5,10) | -6 |
| (6,10) | +78 |
| Total | -672 |

Hence 477-672=-195. This is a coefficient-sensitive discriminator on the actual proper response. It does not bound Omega+J on the complete source or show the corresponding bad configuration is arithmetically impossible.

#### HR2: Growing Divisor Families Defeat Every Support-Only Two-Sided Constant

Choose k distinct primes, their squarefree product D, and ANY R>=D^2+1. Every q=d^2 for d|D is an admitted powerful denominator with a(q)=1. Work on the admitted nonunit radical columns d|D,d>1, setting all other formal response coefficients to zero.

First set A_d=1 for every d>1 dividing D. For g|D,
sum_(g|d|D)mu(d/g)=1_(g=D), so removing d=1 gives

```text
F=e_D-e_1,
||A||^2=2^k-1, ||F||^2=2,
D_F=3-2^k.
```

The ratio ||F||^2/||A||^2 tends to zero and the negative gap is unbounded. All A_d have the same sign; multiplying them all by -1 preserves the example. This is stronger than an isolated indefinite 2-by-2 minor.

Second set A_d=mu(d) on the same support. The full divisor sum at g is mu(g)2^(k-omega(g)); after removal of the unit, F_1=2^k-1. Counting subsets gives

```text
||A||^2=2^k-1,
||F||^2=5^k-2^(k+1)+1,
||F||^2/||A||^2 -> infinity.
```

Both families have sum F=0. Thus no constants 0<c<=C<infinity, independent of support size/root, can give c||A||^2<=||F||^2<=C||A||^2 using only this exact support/incidence information. The first family already refutes a uniform positive lower comparison under common-sign A.

**Critical scope:** the quotient sites are distinct, so these assignments are legitimate FORMAL-coordinate configurations, realizable by assigning values at those sites and zero at the others. They are NOT asserted to extend to the genuine Mertens function or the original historical mu prefix. The forbidden class is coefficient-blind/support-only comparison, not PD.OPEN, H_ROB or every signed arithmetic argument. No infinite family of genuine R with D_F<0 is claimed. No external theorem is required for the finite divisor algebra or its infinite-k consequence.

### G. Original-Carrier And Covariance Audit

All original mu signs, ordered floor multiplicities, squareful zeros, strict a,b<R, X=R^2-1, unit q=1, historical mask T<R and both cross orientations survive. Powerful q is an auxiliary denominator, not an owner tag. The later M values are exact DEPENDENT coordinates of a source already determined below R; admitting them as independent bounds would change the problem.

#### 2. FOUR-WAY SOURCE MAP

| Field | Euler / finite AC | VF / actual primes | NNS / OAI | Square blocks |
| --- | --- | --- | --- | --- |
| Original object | Q_R, complete C and S, historical K_R and powerful response above | Complete wheel F_R-D_R=li(X)-pi(X); separately the weighted/clipped #915 history/current source | Original ideal-labelled compensated LOW polynomial and Hermitian Gram, with character, profile, height, exclusions and principal normalizer | Full M(X_R), not a shell increment |
| Valid relation | EXACT_IDENTITY: original floor/convolution/endpoint declarations; PD/UM are now accepted PAPER bridges for each coefficient | NOT_EQUIVALENT to Q_R. Exact wheel identity retains virtual d>X Euler compensation. Actual prime/Mobius transport is cofactor-weighted, not equality of errors | ONE_WAY global consequence through native Hecke-to-zeta/Mertens transfer. OPEN_BRIDGE for a coefficient map from these rational radical vectors | EXACT_IDENTITY Q_R=2M(R-1)-M(X_R); GD's complete tail and square-to-prefix interpolation supply its conditional consumer |
| Source/scale safeguards | X=R^2-1, q<=R-1, a(q), all g, zero/shift in K_R; no rescaling | Original prime membership, VF seat weights, historical anchor, admission and clipping cannot be replaced by the unmasked divisor map | J means UNSELECTED slots; J=empty has one outer tuple. A real/complex norm identity supplies no new arithmetic cancellation | Q_R^2=D_G+2sum_(g<h)C_gC_h; neither D_G nor sum of shell squares is the full square |
| Unpaid interaction | Small-gcd H/E and shared-prime overlap; no independent PD.OPEN bound | Complete discrepancy and original #915 payment | Binding same-source LOW/principal return, not paid by HR1's finite real-vector identity | Historical-normalized full norm and all-prefix endpoint gain remain unproved |

The fetched atlas/DAG are navigation only. Existing reciprocal-band telescopes and cofactor-positivity theorems do not act on this simultaneous powerful/radical mask. In particular a prime-square amplitude coincidence with a CORR4 daughter is not a full CORR4 coefficient or mixed-tail transfer; all other powers, multi-prime denominators, the unit and history remain.

### H. Quantifier And Circularity Audit

PD2 is unconditional on the native history and has absolute constants; it is not uniform smallness of E. PD3 has a fixed c>1/2 and c-dependent finite Lambda_c; its endpoint c=1/2 is not available. PD4's positive-loss family is critical-growth-equivalent, while its zero-loss member is only shown sufficient. No target has been assumed as a new supplier.

UM1 follows by writing C=Z-m e_1, S=T-m e_1: the m^2 terms cancel exactly, leaving Delta=Delta_0+2mB. Nonunit q>=4 makes Z expressible through indices at most max(R-1,floor(X/4)), but those values are dependent coordinates, not an independently free quarter-horizon input.

H_ROB, Delta_0>=2|mB| for every R>=4, implies H_Z and then Q^2<=D_G. It is equivalent at a fixed Z to requiring nonnegative gap for BOTH endpoint choices m and -m. The second choice is counterfactual in general. No reverse implication from the genuine H_Z or the canonical objective was established, so H_ROB is NOT labelled TARGET_EQUIVALENT. Even H_ROB alone pays no magnitude bound for D_G. Changing only the endpoint in a model cannot refute a genuine-arithmetic conjecture.

HR2 is universal in k and legal root size, but only in its stated formal coefficient class. Its no-go does not transfer to genuine mu without an additional realizability theorem. HR1's pairwise-coprime theorem is a sufficient structural statement, not a hypothesis inserted into the full arithmetic source to hide R=115.

### I. Constructive Repairs And Paid Recovery Test

#### 3. FIRST SIGNED LOSS

| Step / declaration | Exact loss and quantitative tax | Consumer and remaining bill |
| --- | --- | --- |
| Original eulerSelfDualBilinear -> absolute pair count | Erases mu(a)mu(b) before interaction; naive O(R^2 log^2 R) scale | Existing convolution/endpoint identity reconstructs signs, but supplies no smaller bound |
| PD historical U bound -> divisor inversion triangle | Drops signs within each historical rectangle and across mu(j); pays 9, E0, sqrt(Y), and 1+log N | This is independently paid on H and the COMPLETE high-gcd tail; small-gcd E and -2<H,E> remain |
| Nonunit radical response -> presumed contraction or independent diagonal payment | Drops full off-diagonal Gram or substitutes a norm comparison with no uniform constant | R=115 refutes H_F. HR1 keeps coprime interactions in a square and isolates the exact shared-prime bill; HR2 excludes a support-only substitute |
| C=H-E -> separate squares | Discards -2<H,E>, or J after unit separation | At R=115 J=-1970. Full Delta needs D_H+P+Omega+J+2mB; no term is paid twice |
| Q=sum C -> Cauchy over all labels | A factor sqrt(R), potentially a quarter-power tax at integer scale | Accepted GD instead uses a short head and complete tail. Its conditional exponent consumer does not assume H_Z/GC5 |
| OAI LOW norm_sum_le after exact signed Gram | Loses Hermitian off-diagonals on a different ideal/profile carrier | Native marked moments and principal mass retain their actual hypotheses; no coefficient transfer from HR1 or PD has been proved |

#### 4. PAID RECOVERY TEST

The compiled rough/smooth convolution and self-dual Newton endpoint are a successful identity recovery on the genuine source. PD2 then supplies NEW independent historical control, accepted here. This is meaningful supporting mathematics, not a complete endpoint gain.

The existing OAI endpoint can be applied to M(floor(X/q)) only with its actual positive-loss exponent; it does not generate a second gain by reusing that conclusion in an exact representation. Completed reciprocal bands have different masks. Positive cofactor fibres, virtual-wheel compensation and near-resonance do not supply the missing shared-radical/history estimate. The NNS signed Gram recovers both orientations but does not prove their sign.

The surviving exact full ledger is

```text
Delta = D_H + P(A') + Omega(A') + J + 2M(X)B.
```

It is an IDENTITY, not a new bound. A useful next arithmetic result must control the actual Omega+J jointly, or another complete source expression, using the true dependent coefficients. Pairwise-coprime components are paid at the proper-response level; their shared-prime crossings and the unit/history return are not.

### J. Competing Strategy Assessment

#### 5. NET RESULT / ADMISSION VERDICT

No numerical global improvement and no new admitted RH route. Accept PD's strict-history localization as a supporting quantitative theorem; retain FINITE-AC/CORR4/MU-LIFT without claiming sparse support alone implies smallness. Retire H_F and coefficient-blind two-sided radical norm comparisons. Retain H_ROB/H_Z/GC5 as conjectures, not as a replacement for magnitude control.

The accepted OAI IR/FFR all-delay return remains the distinct formalization path toward the already accepted paper endpoint. #1131 pays its finite-response/mass supplier, not the unfinished same-signal analytic return. NYMAN's FL/DM review remains a separate useful pending task; this run does not revive the already excluded bounded-variance route. Owner FA's marked proper-source result is neither contradicted nor newly approved here. All nine protected routes retain their actual source obligations.

### K. Original Research And Executed Verification

HR1 derives a finer shared-prime criterion than prime/composite grouping. HR2 gives two explicit growing norm-distortion families rather than extrapolating a single matrix minor. The two-day reports were searched for these specific formulas; no matching formulation was found. No external-literature priority or exhaustive repository novelty is claimed. Standard Mobius inversion, Gram expansion and elementary divisor combinatorics are credited, not renamed as new discoveries.

HR3: a new Python 3 standard-library checker used a sign/square sieve for mu through 301400, direct enumeration of every ordered pair, literal smooth rectangles, independent powerful regrouping, and a separately seeded quotient-block Mertens recursion. Trial-factorization mu below the seed was checked against the sieve. No upstream program or emitted coefficient vector was reused as the implementation.

| Executed check | Count / result |
| --- | ---: |
| Roots R=2..128 plus R=549 | 128 |
| Literal ordered pairs, including zero-weight pairs | 991184 |
| Strict smooth rectangles | 23980 |
| Powerful denominator occurrences across roots | 1337 |
| Independently recomputed Mertens query checks, with repeats | 1465 |
| Complete vector/gap restorations | 128 |
| Exact divisor-cube model families, k=1..10, two signs | 20 |
| Pairwise-coprime repairs, three supports and four coefficient choices | 12 |
| Source, endpoint, Gram, mask or arithmetic mismatches | 0 |

The fixed supports include (6,35,143), demonstrating that the repair genuinely permits composite radicals. All sign decisions are integer/rational. The program was executed once for results and once unchanged to capture its archival output; these are not two independent experiments. Syntax checking passed. No computation session is left running. The R=115 minimum is exhaustive in its stated lower domain; the global conjectures are NOT tested exhaustively beyond 128. No new R=5561 calculation or Lean execution is claimed.

Program SHA256: `915364e149e38593bf388bcacfade299ff3e6b79928abe645e5a1736d1e5ce6b`.
Output SHA256: `24d23a9afec16883708423814759a2409b812274da0212f38f1898fb8d726977`.
The complete executed source and output are appended below for reproducibility.

### L. Formalization Guidance And GitHub Evidence

PD1-PD4 and UM1/UM5 now have this independent ACCEPT at their stated paper scopes. PD2 is the useful independent quantitative supplier; PD4 is a conditional/equivalence result, not a new arithmetic premise. H_F must not be implemented as a theorem. HR1-HR2 need an independently executing reviewer before being treated as independently accepted new results. Their algebra alone is not grounds for a filler PR or for preempting the accepted full OAI return.

#1131 actually merged at 2026-11-11T12:46:15Z. Tested head `f3f1da37c3e2fff9374eb5e99eca0da94c1efc29` and current main have the SAME tree `17225275af9120da64ccbd3f16eca465a557d6d6`. All 13 attached checks are successful. The actual [dedicated job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43006238259/job/130474300634) checked out that literal head and compiled with warnings fatal. Six old finite-response and eight new mass/delay closures passed with only the standard three axioms; the new closure sizes are 422,533,182,841,230,223,101,85.

The original `principal_product_response_terms_mass` was read, not inferred from the title. It assumes nonnegative normalized weights, positive slot mass, Q>=P>=1, ||A||,||eta||<=1, theta>=3/5 and P^(2-6theta)+P^-theta<=1/2. Its bound is (1+2*(P^(2-6theta)+P^-theta+P^(3-5theta)))^N-1, independent of finite order K. Vanishing requires fixed N and STRICT theta>3/5. The separate original-error bridge requires ||eta||=1, P>=480 and Re(s)>=7/8, and retains the negative principal normalizer. No delayed T>Z atom may be dropped. None of these declarations proves the full same-signal contour return or b_IR.

Open/draft PR collection at intake was empty. No CI was triggered or rerun. Direct git clone failed with CONNECT 403; authorized connector source/report/CI reads succeeded. Only this own report is written remotely. No main, Lean, shared policy, another report, PR, issue, workflow, merge, permission, schedule or agent launch was changed, and no branch was created.

### M. Specialist Handoffs

- Proof Architect: PD2 is independently accepted supporting control; HR1-HR2 are new self-audited scope-specific results. Do not promote proper-response contraction into complete source payment. FL/DM reviews remain pending, explicitly preserved rather than silently dropped.
- Owner: distinguish the rational powerful-radical overlap here from prime/floor-Li event ancestry and the literal #915 marked masks. Your FA bound is not a bound on Omega or J without an exact occurrence/weight map.
- Analytic: preserve the accepted FFR return sequence and DM's pending review status. An existing Mertens power controls quotient samples at that SAME power; it does not pay a new joint shared-radical/history saving.
- Wheel: PD1-PD4 survive review. Replace a generic composite-radical explanation by HR1's exact reserve and shared-prime bill. Seek a genuine relation between A_d and H_g BEFORE triangle, not a coefficient-free contraction.
- Census: do not enlarge H_Z/H_ROB scans without a changed discriminator. A useful new candidate must control the actual shared-prime bill together with J and 2M(X)B. The R=115 edge contributions above are exact fixtures; R=549 is independently rechecked here.
- Lean Verification: #1131 is merged and green; do not rebuild it merely for activity. Continue the independently accepted all-delay same-signal return. PD2 is an optional supporting source lemma if its consumer needs it; HR1-HR2 require separate review and are not a new endpoint.

### N. First Independently Missing Mathematical Ingredient

For the selected FINITE-AC path, the exact historical normalization target remains ONE B before all R in ||C_R||<=B R^(1+eta)sqrt(K_R), at an eta giving a genuine improvement over the applicable global comparator. PD.OPEN is sufficient but its all-positive-loss family is RH-strength; assuming it merely renames the endpoint. PD2 pays H, not E or their cancellation.

The next source-specific question is whether an independently provable relation between the genuine shared-prime correlations Omega(A') and historical interaction J restricts the COMPLETE ledger strongly enough to improve that magnitude consumer. HR1 identifies its exact arithmetic terms; HR2 shows why support alone cannot do it. Neither an exclusion theorem nor the required magnitude estimate has been proved here. H_ROB is a stronger sign conjecture, not a paid magnitude supplier.

The separate OAI formal gap remains the accepted full original all-delay residue/contour identity, finite-interval inversion and complete endpoint assembly. This report does not replace it by a new assumed response bound.

### O. Next-Run Resume Capsule

```text
RUN=20261111-referee-2/HR; actual trigger=12:03:01 EST.
MAIN=dda92f9ce59627b4c1f1317082f728648d330a0a.
ACK=CROSS_ROUTE_SIGNED_RECOVERY_V1.
INTAKE_REPORTS=1855dcff615963978e73bddf4779e9630420a549.
CHECKPOINT=8c37e325b36c605957b0e829541c6588f903f2cf,
  blob=413749324711f69c9042254a47d94e965991dcb5, exact readback verified.
ACCEPT_ON_PAPER=20261111-wheel-2/PD1-PD4; census-2/UM1,UM5.
REFUTED=H_F; smallest genuine R115, 404-599=-195.
RESTORED_R115=DH18750 + DF(-195) + J(-1970) + unit1746 =18331.
NEW_SELF_AUDIT=HR1 shared-prime reserve/bill and coprime repair;
  HR2 growing support-only norm-distortion families, MODEL-ONLY.
EXECUTED=HR3, 128 roots, 991184 direct pairs, 23980 rectangles.
OPEN=H_ROB,H_PRE,H_Z,GC5,PD.OPEN, complete magnitude gain and RH.
PENDING_SEPARATE_REVIEW=Coordinator FL1-FL5; Analytic DM1-DM4; Owner FA.
FORMAL=#1131 merged, 13/13 checks; #1119 14/14, 911 unchanged blobs.
COMPILED_BOUNDARY=7/8-7/(64*N_pack); accepted paper IR boundary separate.
NEW_GLOBAL_GAIN=NONE; VERIFIED_ETA=NONE.
NEXT=review FL/DM on their exact complete source, or a NEW genuine
  shared-prime/history relation; do not rerun unchanged sign scans.
```

All earlier report bytes and material correction history are preserved. Final report publication is verified separately below, never inferred from successful computation or preparation.

## HR Material Evidence And Reproduction

### Original Source Receipts

All files below were fetched at main `dda92f9ce59627b4c1f1317082f728648d330a0a`; the table records actual returned Git blob SHAs.

| Source | Blob SHA |
| --- | --- |
| [AGENTS.md](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/AGENTS.md) | `c9c89f01b90b526de9f3e8ea92478e36504711b6` |
| [CURRENT_PROOF_CONTRACT.md](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/CURRENT_PROOF_CONTRACT.md) | `95566e37c8eaeb99ee680660df4f9d2e06ea5038` |
| [research/EULER_HYBRID_ABEL_GRAM_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/EULER_HYBRID_ABEL_GRAM_20261027.lean) | `2a94dd8fd56fc03e95f732fb44b778a8d4f83e26` |
| [research/EULER_SELF_DUAL_POINTWISE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/EULER_SELF_DUAL_POINTWISE_20261027.lean) | `c327c556f39ee7014fd774b24d0f95a1ece050e0` |
| [research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean) | `e97561ef330a9996fd807d8910369f0698147b01` |
| [research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean) | `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73` |
| [RHLean/Analysis/FiniteWheelRestrictedFloor.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/RHLean/Analysis/FiniteWheelRestrictedFloor.lean) | `94c4d4420fc58cd87d92780c6265decd2cad7e66` |
| [RHLean/Proof/SquareRootLegalAncestryGramReduction.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/RHLean/Proof/SquareRootLegalAncestryGramReduction.lean) | `1270d4d91c53b50b110d10014f223f427fb7a575` |
| [research/CompleteSquareRootWheelFractionalBoundary.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/CompleteSquareRootWheelFractionalBoundary.lean) | `ecb482e52deeee5e9b3853592a3ffdace662d2ff` |
| [research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` |
| [research/MERTENS_EXPONENT_ENVELOPES.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/MERTENS_EXPONENT_ENVELOPES.lean) | `655b896e8d5a41c9f8fc3c456eae3944a98bfefe` |
| [research/oai_434/VF919WindowErrorClosure.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919WindowErrorClosure.lean) | `f629db1b2b65d6ec042ac9432397d4b6316200c6` |
| [research/oai_434/VF919NativeStrictMertens.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919NativeStrictMertens.lean) | `b33a4883e1ddb0551b0f11f062bce46680d87450` |
| [research/oai_434/VF919NativeSevenEighthsReplay.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919NativeSevenEighthsReplay.lean) | `111c933a7ca15647105ce6a4d0f3cbfc3cde81f4` |
| [research/oai_434/VF919ExplicitSquareBlockPacking.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919ExplicitSquareBlockPacking.lean) | `32999039fdeea99c58a070c1c4ee9c140720dd44` |
| [research/oai_434/VF919ExplicitFixedSourceSlotCount.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919ExplicitFixedSourceSlotCount.lean) | `bad5aab0a60e96d19e7c9550cd7c0a072288bc0f` |
| [research/oai_434/VF919PrincipalResponseMass.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919PrincipalResponseMass.lean) | `5f7e812108ff7eff4a60da7055c2dd5f852c4941` |
| [research/oai_434/VF919OriginalLowTupleSignedGram.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/research/oai_434/VF919OriginalLowTupleSignedGram.lean) | `dd2fde01ae6e2446da4e69b30f6fc80fcadb858d` |
| [scripts/lean/window_error_closure/WindowErrorClosureAudit.lean](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/scripts/lean/window_error_closure/WindowErrorClosureAudit.lean) | `1f17f9401a63d16227db2e2aad020b9f74bc5f4e` |
| [docs/COORDINATE_ATLAS.md](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/docs/COORDINATE_ATLAS.md) | `cd0419d00a37739fe5a292f5cb738e33213949d5` |
| [docs/PROOF_DEPENDENCY_DAG.md](https://github.com/OVVO-Financial/RH_Lean/blob/dda92f9ce59627b4c1f1317082f728648d330a0a/docs/PROOF_DEPENDENCY_DAG.md) | `eee764cefe70035a9f6c7df26ad787fbfd0fb233` |

### Two-Day Handoff Receipts

Pinned reporting snapshot: `1855dcff615963978e73bddf4779e9630420a549`. Equal coordinator mirror blobs were verified from both directory listings; the AM bytes supply the identical PM content.

| Report | Blob SHA |
| --- | --- |
| [2026-11-10/00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-10/00-coordinator-am.md) | `4d55b2893f974656c6aa14e48b243827fa8308f8` |
| [2026-11-10/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-10/10-owner-payment.md) | `84afec90414b2394a61b51df46c07b6b540e5942` |
| [2026-11-10/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-10/20-analytic-type-ii.md) | `7ed3a39bec4796f4173b692064af872ea8035048` |
| [2026-11-10/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-10/30-finite-wheel.md) | `62406503a1ddbbf9330abcdc4cf761f7fbf05795` |
| [2026-11-10/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-10/40-prime-census.md) | `a3cfa56072f3893dbf92a18956e1794236bde057` |
| [2026-11-10/50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-10/50-adversarial-referee.md) | `6529562a5bb21fa192fddadaa91a758b9d125c29` |
| [2026-11-10/60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-10/60-lean-verification.md) | `682b334b8f37fa4bfe2d552a1142d852a0db2afd` |
| [2026-11-10/90-coordinator-pm.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-10/90-coordinator-pm.md) | `4d55b2893f974656c6aa14e48b243827fa8308f8` |
| [2026-11-11/00-coordinator-am.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-11/00-coordinator-am.md) | `106f6d88708a7545caab43c56ae1bbb915fd97f2` |
| [2026-11-11/10-owner-payment.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-11/10-owner-payment.md) | `accf2930372234b58e98e8e43e88aeb845b56e9b` |
| [2026-11-11/20-analytic-type-ii.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-11/20-analytic-type-ii.md) | `0309d49557af30da43a07d72dce93c93c1811157` |
| [2026-11-11/30-finite-wheel.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-11/30-finite-wheel.md) | `c9989449a814a1a7ee799791c73450872f4c7d3c` |
| [2026-11-11/40-prime-census.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-11/40-prime-census.md) | `a85bc7dc8b49952d37f1a4cb6a0a8eb307d3f352` |
| [2026-11-11/50-adversarial-referee.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-11/50-adversarial-referee.md) | `214e99d8d6133e720f9645dd650a57b01a8c05cf` |
| [2026-11-11/60-lean-verification.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-11/60-lean-verification.md) | `c86b058b6387de7348b123b22b8f5b8772d5ae9a` |
| [2026-11-11/90-coordinator-pm.md](https://github.com/OVVO-Financial/RH_Lean/blob/1855dcff615963978e73bddf4779e9630420a549/research/agent_reports/2026-11-11/90-coordinator-pm.md) | `106f6d88708a7545caab43c56ae1bbb915fd97f2` |

External inbox: `038018145c0fddb2f6306c0712373adf9cd1ea52`; no entry after October 18. This table is retrieval/provenance evidence, not collective mathematical acceptance.

### Complete Executed Reproducer

Python 3 standard library; run `python hr_checks.py`. The code is reproduced verbatim. It proves the stated finite certificates, not H_ROB or an infinite genuine-Mertens assertion.

```python
"""Independent exact audit of PD/UM and proof-led radical overlap families."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import gcd, isqrt, prod
import json


@lru_cache(None)
def factors(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            exponent = 0
            while n % p == 0:
                n //= p
                exponent += 1
            out.append((p, exponent))
        p += 1
    if n > 1:
        out.append((n, 1))
    return tuple(out)


def mobius(n):
    f = factors(n)
    return 0 if any(e > 1 for _, e in f) else (-1) ** len(f)


def divisors(n):
    result = [1]
    for p, e in factors(n):
        result = [d * p ** j for d in result for j in range(e + 1)]
    return sorted(result)


def transform(v):
    n = len(v) - 1
    return [0] + [sum(v[g] for g in range(d, n + 1, d)) for d in range(1, n + 1)]


def inverse(v):
    n = len(v) - 1
    return [0] + [sum(mobius(k) * v[g * k] for k in range(1, n // g + 1))
                  for g in range(1, n + 1)]


def norm(v):
    return sum(x * x for x in v)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


roots = list(range(2, 129)) + [549]
limit = max(roots) ** 2 - 1
mu = [1] * (limit + 1)
mu[0] = 0
prime_flags = bytearray(b'\x01') * (limit + 1)
prime_flags[0:2] = b'\x00\x00'
for p in range(2, limit + 1):
    if prime_flags[p]:
        for n in range(p, limit + 1, p):
            mu[n] = -mu[n]
        for n in range(p * p, limit + 1, p):
            prime_flags[n] = 0
        for n in range(p * p, limit + 1, p * p):
            mu[n] = 0
M = [0] * (limit + 1)
for n in range(1, limit + 1):
    M[n] = M[n - 1] + mu[n]
seed = [0]
for n in range(1, 129):
    seed.append(seed[-1] + mobius(n))
assert seed == M[:129]


@lru_cache(None)
def recursive_M(n):
    if n < len(seed):
        return seed[n]
    total = 1
    left = 2
    while left <= n:
        quotient = n // left
        right = n // quotient
        total -= (right - left + 1) * recursive_M(quotient)
        left = right + 1
    return total


counts = Counter()
failures = []
witnesses = []
overlap_terms_115 = []
for R in roots:
    N, X = R - 1, R * R - 1
    C = [0] * R
    for a in range(1, R):
        assert mu[a] == mobius(a)
        for b in range(1, R):
            C[gcd(a, b)] += mu[a] * mu[b] * (X // (a * b))
            counts['ordered_pairs'] += 1
    S = transform(C)
    U, A = [0] * R, [0] * R
    rectangle_future = [0] * R
    sites = {X, N}
    for d in range(1, R):
        if not mu[d]:
            continue
        bound = N // d
        smooth = [h for h in range(1, bound + 1)
                  if all(d % p == 0 for p, _ in factors(h))]
        reconstruction = 0
        for h in smooth:
            for k in smooth:
                a, b = bound // h, bound // k
                q, t = d * d * h * k, X // (d * d * h * k)
                assert max(a, b) <= t < (a + 1) * (b + 1)
                assert (t >= R) == (q <= N)
                reconstruction += M[a] + M[b] - M[t]
                U[d] += M[a] + M[b] - (M[t] if t < R else 0)
                rectangle_future[d] += M[t] if t >= R else 0
                counts['strict_rectangles'] += 1
        assert reconstruction == S[d]
    for q in range(1, R):
        f = factors(q)
        if all(e >= 2 for _, e in f):
            d = prod(p for p, _ in f)
            multiplicity = prod(e - 1 for _, e in f)
            A[d] += multiplicity * M[X // q]
            sites.add(X // q)
            assert X // q > R
            counts['powerful_denominators'] += 1
    assert A == rectangle_future
    for t in sites:
        assert recursive_M(t) == M[t]
        counts['independent_M_sites_with_repeats'] += 1
    H, E = inverse(U), inverse(A)
    assert [H[g] - E[g] for g in range(R)] == C
    assert transform(H) == U and transform(E) == A
    assert sum(H) == 2 * M[N] and sum(E) == M[X]
    assert sum(C) == 2 * M[N] - M[X]
    assert all(E[g] == 0 for g in range(1, R) if g * g > N)
    F, Ap = E[:], A[:]
    F[1] -= M[X]
    Ap[1] -= M[X]
    assert sum(F) == 0 and transform(F) == Ap
    Z = [H[g] - F[g] for g in range(R)]
    T = transform(Z)
    B = sum(C[2:])
    DH, DF = norm(H) - norm(U), norm(F) - norm(Ap)
    J = -2 * (dot(H, F) - dot(U, Ap))
    D0, D = norm(Z) - norm(T), norm(C) - norm(S)
    assert D0 == DH + DF + J
    assert D == D0 + 2 * M[X] * B
    assert D0 == B * B - 4 * M[N] * B + norm(C[2:]) - norm(S[2:])
    active = [d for d in range(2, R) if Ap[d]]
    signed_sum = sum(mu[d] * Ap[d] for d in active)
    reserve = signed_sum ** 2 + sum((2 ** len(factors(d)) - 2) * Ap[d] ** 2 for d in active)
    overlap = 0
    for d, e in combinations(active, 2):
        term = 2 * (2 ** len(factors(gcd(d, e))) - 1) * mu[d] * mu[e] * Ap[d] * Ap[e]
        overlap += term
        if R == 115 and term:
            overlap_terms_115.append([d, e, term])
    assert DF == reserve + overlap
    assert DF >= 0 or any(gcd(d, e) > 1 and mu[d] * mu[e] * Ap[d] * Ap[e] < 0
                          for d, e in combinations(active, 2))
    counts['complete_vector_and_gap_checks'] += 1
    if DF < 0:
        failures.append(R)
    if R in (3, 21, 37, 115, 128, 549):
        K = max(Fraction((M[u] - 1) ** 2, u + 1) for u in range(R))
        witnesses.append({'R': R, 'M_X': M[X], 'M_N': M[N], 'K': str(K),
                          'B': B, 'DG': norm(C), 'DS': norm(S), 'DH': DH,
                          'DF': DF, 'J': J, 'Delta0': D0, 'Delta': D,
                          'robust_margin': D0 - 2 * abs(M[X] * B),
                          'reserve': reserve, 'shared_prime_bill': overlap})
    if R == 115:
        assert [(d, Ap[d]) for d in active] == [(2, -20), (3, -4), (5, -1), (6, -13), (7, -2), (10, -3)]
        assert norm(F) == 404 and norm(Ap) == 599
        assert (DH, J, D0, D, reserve, overlap) == (18750, -1970, 16585, 18331, 477, -672)
        assert [F[g] for g in (1, 2, 3, 5, 6, 7, 10)] == [11, -4, 9, 2, -13, -2, -3]
assert failures[0] == 115
assert 4 != 2 * M[1] - M[4]
assert 1 * 3 - (-2) ** 2 == -1

# Boolean divisors are an exact combinatorial model of squarefree divisors.
# These assigned coefficients are not claimed to be genuine Mertens values.
cube_rows = []
for k in range(1, 11):
    size = 1 << k
    total_square = []
    for mode in ('constant', 'parity'):
        coeff = [0] + [1 if mode == 'constant' else (-1) ** d.bit_count()
                       for d in range(1, size)]
        out = [sum((-1) ** ((d ^ g).bit_count()) * coeff[d]
                   for d in range(size) if d & g == g)
               for g in range(size)]
        assert sum(out) == 0
        if mode == 'constant':
            assert out == [-1] + [0] * (size - 2) + [1]
            assert norm(out) == 2
        else:
            assert norm(out) == 5 ** k - 2 ** (k + 1) + 1
        assert norm(coeff) == 2 ** k - 1
        total_square.append(norm(out))
        counts['model_cube_families'] += 1
    cube_rows.append({'prime_count': k, 'coefficient_energy': size - 1,
                      'constant_response_energy': total_square[0],
                      'parity_response_energy': total_square[1]})

for support in ([2, 3, 5], [6, 35, 143], [2, 15, 77]):
    assert all(gcd(d, e) == 1 for d, e in combinations(support, 2))
    for c in ([1, 1, 1], [2, -3, 5], [-7, 0, 4], [0, 0, 0]):
        energy = sum(mobius(d) * mobius(e) * 2 ** len(factors(gcd(d, e))) * c[i] * c[j]
                     for i, d in enumerate(support) for j, e in enumerate(support))
        gap = energy - norm(c)
        expected = sum(mobius(d) * c[i] for i, d in enumerate(support)) ** 2
        expected += sum((2 ** len(factors(d)) - 2) * c[i] ** 2 for i, d in enumerate(support))
        assert gap == expected >= 0
        counts['pairwise_coprime_repairs'] += 1

print(json.dumps({'status': 'PASS_EXACT', 'roots': len(roots), 'max_root': max(roots),
                  'counts': dict(counts), 'first_genuine_nonunit_failure': failures[0],
                  'witnesses': witnesses, 'R115_shared_prime_terms': overlap_terms_115,
                  'model_only_cubes': cube_rows}, indent=2))
```

### Recorded Exact Output

```json
{
  "status": "PASS_EXACT",
  "roots": 128,
  "max_root": 549,
  "counts": {
    "ordered_pairs": 991184,
    "strict_rectangles": 23980,
    "powerful_denominators": 1337,
    "independent_M_sites_with_repeats": 1465,
    "complete_vector_and_gap_checks": 128,
    "model_cube_families": 20,
    "pairwise_coprime_repairs": 12
  },
  "first_genuine_nonunit_failure": 115,
  "witnesses": [
    {
      "R": 3,
      "M_X": -2,
      "M_N": 0,
      "K": "1",
      "B": 2,
      "DG": 4,
      "DS": 8,
      "DH": 4,
      "DF": 0,
      "J": 0,
      "Delta0": 4,
      "Delta": -4,
      "robust_margin": -4,
      "reserve": 0,
      "shared_prime_bill": 0
    },
    {
      "R": 21,
      "M_X": -7,
      "M_N": -3,
      "K": "3/2",
      "B": 5,
      "DG": 357,
      "DS": 338,
      "DH": 494,
      "DF": 225,
      "J": -630,
      "Delta0": 89,
      "Delta": 19,
      "robust_margin": 19,
      "reserve": 225,
      "shared_prime_bill": 0
    },
    {
      "R": 37,
      "M_X": 7,
      "M_N": -1,
      "K": "3/2",
      "B": -41,
      "DG": 4631,
      "DS": 840,
      "DH": 8934,
      "DF": 681,
      "J": -5250,
      "Delta0": 4365,
      "Delta": 3791,
      "robust_margin": 3791,
      "reserve": 731,
      "shared_prime_bill": -50
    },
    {
      "R": 115,
      "M_X": -9,
      "M_N": -6,
      "K": "3/2",
      "B": -97,
      "DG": 21411,
      "DS": 3080,
      "DH": 18750,
      "DF": -195,
      "J": -1970,
      "Delta0": 16585,
      "Delta": 18331,
      "robust_margin": 14839,
      "reserve": 477,
      "shared_prime_bill": -672
    },
    {
      "R": 128,
      "M_X": -32,
      "M_N": -2,
      "K": "3/2",
      "B": -153,
      "DG": 56804,
      "DS": 6339,
      "DH": 78234,
      "DF": 4927,
      "J": -42488,
      "Delta0": 40673,
      "Delta": 50465,
      "robust_margin": 30881,
      "reserve": 5043,
      "shared_prime_bill": -116
    },
    {
      "R": 549,
      "M_X": 192,
      "M_N": 3,
      "K": "3/2",
      "B": -158,
      "DG": 213476,
      "DS": 70928,
      "DH": 254818,
      "DF": -1402,
      "J": -50196,
      "Delta0": 203220,
      "Delta": 142548,
      "robust_margin": 142548,
      "reserve": 9316,
      "shared_prime_bill": -10718
    }
  ],
  "R115_shared_prime_terms": [
    [
      2,
      6,
      -520
    ],
    [
      2,
      10,
      -120
    ],
    [
      3,
      6,
      -104
    ],
    [
      5,
      10,
      -6
    ],
    [
      6,
      10,
      78
    ]
  ],
  "model_only_cubes": [
    {
      "prime_count": 1,
      "coefficient_energy": 1,
      "constant_response_energy": 2,
      "parity_response_energy": 2
    },
    {
      "prime_count": 2,
      "coefficient_energy": 3,
      "constant_response_energy": 2,
      "parity_response_energy": 18
    },
    {
      "prime_count": 3,
      "coefficient_energy": 7,
      "constant_response_energy": 2,
      "parity_response_energy": 110
    },
    {
      "prime_count": 4,
      "coefficient_energy": 15,
      "constant_response_energy": 2,
      "parity_response_energy": 594
    },
    {
      "prime_count": 5,
      "coefficient_energy": 31,
      "constant_response_energy": 2,
      "parity_response_energy": 3062
    },
    {
      "prime_count": 6,
      "coefficient_energy": 63,
      "constant_response_energy": 2,
      "parity_response_energy": 15498
    },
    {
      "prime_count": 7,
      "coefficient_energy": 127,
      "constant_response_energy": 2,
      "parity_response_energy": 77870
    },
    {
      "prime_count": 8,
      "coefficient_energy": 255,
      "constant_response_energy": 2,
      "parity_response_energy": 390114
    },
    {
      "prime_count": 9,
      "coefficient_energy": 511,
      "constant_response_energy": 2,
      "parity_response_energy": 1952102
    },
    {
      "prime_count": 10,
      "coefficient_energy": 1023,
      "constant_response_energy": 2,
      "parity_response_energy": 9763578
    }
  ]
}
```


### Prepublication Freshness - 2026-11-11 17:25:24 UTC

Immediately before publication, the live main HEAD remained `dda92f9ce59627b4c1f1317082f728648d330a0a` with tree `17225275af9120da64ccbd3f16eca465a557d6d6`. The `agent-reports` HEAD was the verified own checkpoint `8c37e325b36c605957b0e829541c6588f903f2cf`; thus no report handoff changed after intake except that checkpoint. The refreshed open-PR collection was empty, including drafts. The current owned report blob `413749324711f69c9042254a47d94e965991dcb5` was read again and matched the checkpoint content exactly. Original pre-run report bytes remain a prefix of the publication. Exact-head CI results are the scoped completed evidence recorded above, not a newly launched main build.


### Verified Publication Receipt - 2026-11-11 17:26:32 UTC

`STATUS=COMPLETE_AND_PUBLISHED` for the selected HR investigation; separately identified FL/DM/FA review tasks remain PENDING.

The substantive append was committed as [`0edeef389b5acb05de22381221b598b70fdcad3a`](https://github.com/OVVO-Financial/RH_Lean/commit/0edeef389b5acb05de22381221b598b70fdcad3a), report blob `23004f5bc81b5250029a2f3ed3bbf60ef21b34f1`. An immutable fetch of that commit returned the entire submitted report exactly, including the complete reproducer and output. The commit API independently confirmed exactly ONE changed file, this authorized report, with 889 additions and ZERO deletions. The original pre-run report remains a byte-for-byte prefix; the early checkpoint also remains intact. This receipt records a verified earlier publication, not an unverified promise about its own eventual commit.

Main freshness and empty open/draft PR collection were checked at 17:25:24 UTC. No source or workflow was modified, no CI was launched, and no local Lean build was attempted. HR1-HR2 remain PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING; HR3 is executed exact finite verification, not Lean certification. `NO_NEW_GLOBAL_GAIN; VERIFIED_ETA=NONE; RH=OPEN`.
