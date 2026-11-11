# RH | Finite Wheel & Incidence - 2026-11-11

## Early Checkpoint - 20261111-wheel-1/GD

### A. Structural Question

No new theorem is certified at this checkpoint. The selected investigation is Coordinator M2: whether the complete gcd diagonal of the genuine historical Mobius floor source supplies independent arithmetic information. A candidate reconstruction expands each divisibility-restricted pair sum into rectangular self-dual Mobius sums by finite-prime smooth divisors. The intended test is whether this preserves a global Mertens exponent in both directions, without assuming Census GC5's unproved sign rule. Exact cutoffs, quantitative constants, converse iteration, and novelty remain under review.

### B. Authority And Continuity

Actual configured trigger: 2026-11-11 02:05:01 EST, America/New_York. Platform run ID unavailable. Source main: f7947bee036c4dddb0c36fc9f53ab46b4fa90995. AGENTS blob c9c89f01b90b526de9f3e8ea92478e36504711b6; CURRENT_PROOF_CONTRACT blob 95566e37c8eaeb99ee680660df4f9d2e06ea5038; governing cross-route directive blob e922d4ba9362a1ae196af8f6de88f7417f92087c. cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1.

Canonical VF, complete centered wheel, finite A/C, and RH remain OPEN. The compiled comparator is the every-positive-loss boundary 7/8-7/(64*N_pack), not a zero-loss power bound. The actual declaration and audit implementation have been inspected; hosted evidence refresh is PENDING. Accepted paper IR/MD and the newer FFR alternative are not substituted for a compiled endpoint.

November 11 Owner MC and Analytic NT are AVAILABLE. Coordinator, Census, Referee, and Lean are TODAY=PENDING; their verified November 10 reports are YESTERDAY=CARRY_FORWARD. Yesterday's own RC/JC, Census GC, Coordinator FFR/M2, Referee IRR, Owner DR, Analytic IR, and Lean #1131 continuity were read at their relevant claims. External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 has no new entry after October 18. Preserve the original claim IDs and scopes.

The source is X=R^2-1, a,b<R, Q_R=sum mu(a)mu(b)floor(X/(ab)), C_R(g) the gcd=g sub-sum, and D_G(R)=sum_g C_R(g)^2. All ordered pairs, the unit, squarefree zeros, both off-diagonal orientations, and the complete upper bands remain. K_R is the original shifted historical maximum, not replaced by 1 in the proposed criterion. GC5 is CONJECTURE; R=15/17/549 sign/coarsening witnesses remain valid. Owner's current-mask commutator cannot be replaced by the unmasked RC completion.

### C. Registered Test And Remaining Work

Test exact rectangular identity Q_(A,B)(T)=M(A)+M(B)-M(T) only when A,B<=T and (A+1)(B+1)>T. Test the smooth-divisor reconstruction of every complete common-divisor sum and invert to every gcd group, including nonsquarefree labels. Use all small roots 2..80 and held-outs 127,256,549,5561, plus independent direct reconstruction of small and selected held-out cases. Test exact square-wall equality and a deliberate relaxed-cutoff negative control. This is a changed structural identity test, not an extension of the unchanged GC5 scan. No floating sign decisions or infinite inference from finite evidence.

Execution: IN_PROGRESS. Evidence: NO_NEW_RESULT at this checkpoint; proof and tests PENDING. No global gain, new accepted route, or Lean certification is claimed. Only this owned daily report is authorized for remote writing.

## Complete Gcd Norm Has Exactly The Mertens Growth Exponent

### Final Research Synthesis - 20261111-wheel-1/GD

### A. Most Important Structural Discovery

**The complete gcd diagonal is not an independently easier exponent target. Its every-positive-loss power bound is equivalent to the corresponding genuine Mertens growth bound, WITHOUT assuming GC5.** For every real b with 1/2<=b<=1,

```text
MertensGrowthAtMost(b)
  iff
forall epsilon>0 exists B_epsilon>=0 forall integers R>=2:
  D_G(R) <= B_epsilon R^(4b+epsilon),

D_G(R)=sum_(1<=g<R) C_R(g)^2,
C_R(g)=sum_(1<=a,b<R, gcd(a,b)=g) mu(a)mu(b)floor((R^2-1)/(ab)).
```

The reverse direction does not discard a positive cross term or assume `Q_R^2<=D_G(R)`. A new uniform arithmetic reconstruction first controls the complete large-gcd tail from any already-valid Mertens power. A head/tail comparison then improves that power, and a finite number of valid iterations reaches any prescribed positive loss. Constants need not remain uniform as the exponent approaches 1/2.

This answers Coordinator M2's independence question and removes GC5 as a necessary gate for an exponent-level consumer. In particular the still-OPEN historical norm hypothesis

```text
N_eta: exists B>=0 forall R>=2:
  D_G(R) <= B R^(2+2eta) K_R
```

would imply `MertensGrowthAtMost(1/2+eta)` for every fixed 0<=eta<1/2. This is a CONDITIONAL consequence, not a proof of N_eta. The family N_eta for EVERY eta>0 is target-equivalent to the RH-strength Mertens growth statement. The single fixed-constant eta=0 criterion is only shown sufficient; no converse at zero loss is asserted.

| Claim | Result and scope | Evidence |
| --- | --- | --- |
| 20261111-wheel-1/GD1 | Exact smooth-divisor rectangular reconstruction of every common-divisor sum and every gcd group, with strict square wall | PAPER_PROOF / supporting IDENTITY_ONLY; existing inversion and hyperbola principles credited |
| GD2 | Uniform complete gcd norm and large-gcd tail from any actual Mertens power c>1/2; constants uniform in R and gcd label | PAPER_PROOF / supporting quantitative transfer; unconditional after substitution of an established Mertens bound |
| GD3 | Bidirectional exponent equivalence for the COMPLETE gcd diagonal; no GC5 premise | PAPER_PROOF / TARGET_EQUIVALENCE at exponent level |
| GD4 | Historical K_R norm consumer and all-positive-loss target-equivalence audit | PAPER_PROOF / CONDITIONAL consumer; its new arithmetic premise remains OPEN |
| GD5 | Two independent exact reconstructions, full registered roots, strict-wall negative control, rational exponent checks | FINITE_COMPUTATION |

All new paper claims are **SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. Algorithmic independence below is not independent specialist acceptance. **NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE.** The main quantitative exponent and canonical objective have not improved. No external-literature novelty is claimed.

### B. Current Authoritative Objective

The early checkpoint's source and trigger remain unchanged. The later `main:AGENTS.md` cross-route policy supersedes the proof contract's older single-wheel task-selection sentence, not its valid theorems, masks, or open obligations. Acknowledgment: `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`.

The canonical arithmetic objective is still one C>=0 chosen before all R>=2 with

```text
|pi(R^2)-VF_can(R^2)| <= C R log R.
```

The exact complete wheel is `F_R-D_R=li(R^2-1)-pi(R^2-1)`; the wheel's D_R is NOT this report's D_G. All virtual divisors survive until their termwise Euler compensation. The scalar historical source Q_R is different from the prime discrepancy, from the OAI ideal-labelled probe, and from the clipped weighted #915 source.

#### 1. BASELINE / DEPENDENCY RECEIPT

The strongest applicable explicit compiled comparator verified here is

```text
RHLean.Analysis.native_mertens_near_uniform_window_error_closed
  : MertensGrowthAtMost (b_cert),
b_cert=7/8-7/(64*N_pack).
```

`MertensGrowthAtMost` quantifies EVERY positive epsilon before an all-prefix constant. It is not a fixed power bound at b_cert. The actual source definitions give, for the same positive `explicitFineLength=L`,

```text
N_pack=ceil_nat(max(1,1/(6L)))+2,
N_old =ceil_nat(max(1,1/(3L)))+2.
```

Consequently N_pack<=N_old and `7/(64*N_pack)>1/(48*N_old)`. The counts are not identified. This comparison is inherited verified arithmetic, not GD's new result. The more general fine-source family is retained; an optimization over every admissible source record is not claimed.

Directly inspected the endpoint declaration/proof, actual count definitions, native Hecke-to-zeta/Mertens transfer, growth definition, and live audit implementation. Re-fetched successful hosted run **42552018910**, tested head **77ee815846d6d534c866f0752aa33b84c385610a**, and job **128949473700**. Its actual log reports five live proof-value closures of sizes **35358,35375,35736,35737,35753**, each with only `propext, Classical.choice, Quot.sound`. The checker traverses OAI/RHLean/private proof values and independently collects terminal axioms; required fixed-source construction, native moments, full LOW/HIGH/principal comparison, exact Hecke/Dirichlet product, and arithmetic transfers are checked. Compared **911** pre-existing blobs under RHLean/, research/oai_434/, and the slot_anchored/window_error_closure audit directories against current main: **zero changed**.

This reuses verified exact-head evidence across unchanged sources. It is neither a new main-head compilation nor an independent reproof of every imported analytic lemma. Historical Wiener placeholder warnings in the dependency build are not upgraded to an axiom of the selected endpoint: its audited closure has only the three standard axioms. No whole-upstream placeholder-free claim is made.

Pins carried by the verified hosted evidence: Lean 4.34.1/compiler `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; PrimeNumberTheoremAnd `c39a751132c88b6e8080b74c74023fd95b3d8be0`; openai/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`; anchored source `9cbfce5295343bcb411e6d2cb159b59995cd985b`.

Stronger retrieved PAPER_PROOF: Analytic `20261110-analytic-3/IR1-IR4`, accepted by Referee `20261110-referee-3/IRR`, proposes `b_IR=7/8-1/2400000000` with every positive loss and the stated fixed comparison `eta_IR=737/3840000000000`. This run preserves that accepted-paper status; it does not independently re-audit the entire analytic argument or substitute it for a compiled endpoint. Coordinator FFR1-FFR4 now have today's Analytic paper acceptance, distinct from a Referee verdict. The sole open PR observed is **#1131**, non-draft/unmerged at **621f48b34b5ace39c05aba33ff33b6d014544b4d**; its complete finite-product approximation is not the full IR/FFR endpoint. #1130 is actually merged at current main.

GD1-GD4 need only elementary exact Mobius inversion and, where explicitly stated, a genuine global Mertens power. They do not depend on accepting the newer paper OAI improvement. The actual-prime von Koch consumer retains its explicit classical criterion; the internal Mertens-energy-to-RH consumer is a different established implication with an unpaid arithmetic premise.

### C. Structural Mechanism Investigated

The assigned question is about the COMPLETE literal gcd diagonal, not a new finite wheel or an extension of the unchanged GC5 sign scan. Two things must not be confused:

1. Compressing actual pair atoms into gcd groups preserves Q exactly but changes the diagonal of its square.
2. Bounding all those group squares independently might look weaker than bounding Q, but genuine Mobius factorization can force them to have the same asymptotic growth difficulty.

The mechanism uses the **divisibility sums** S_R(d), where both historical indices are multiples of d, rather than immediately taking gcd=g. For squarefree d, deleting its prime factors from the Mobius coefficients is exactly a convolution with d-smooth integers. Each resulting rectangle still lies below its own strict hyperbola wall. This makes every S_R(d) a signed sum of THREE genuine Mertens values. Divisor inversion restores every C_R(g).

The smooth labels can grow with d and R. Uniformity is established using convergent Euler products, not an unsupported fixed-wheel constant. This arithmetic reconstruction fails for arbitrary coefficient vectors with small prefix sums: it uses the genuine convolution inverse mu*zeta=1 and genuine prime-factor coprimality.

### D. Exact Definitions And Theorems

Throughout R>=2 is an integer, N=R-1, X=R^2-1, mu is the genuine integer Mobius function, and M(t)=sum_(1<=n<=t)mu(n) for integer t>=0. All product cutoffs are inclusive. Historical a,b are strictly less than R. A physical floor occurrence is an ordered triple (a,b,k) with 1<=a,b<=N, k>=1, abk<=X, coefficient mu(a)mu(b). Equal products do not identify different occurrences.

```text
Q_R=sum_(a,b<=N)mu(a)mu(b)floor(X/(ab)),
C_R(g)=sum_(a,b<=N,gcd(a,b)=g)mu(a)mu(b)floor(X/(ab)),
S_R(d)=sum_(a,b<=N,d|a,d|b)mu(a)mu(b)floor(X/(ab)),
D_G(R)=sum_(g=1..N)C_R(g)^2,
K_R=max_(0<=u<R) (M(u)-1)^2/(u+1).
```

S_R(d) and C_R(d) are zero for nonsquarefree d. Let H_d(B)={h:1<=h<=B and every prime factor of h divides d}; H_1(B)={1}. The unit is included. Put B_d=floor(N/d), A_h=floor(B_d/h), and T_(d,h,k)=floor(X/(d^2 h k)).

**GD1, exact reconstruction.** For every 1<=d<R,

```text
S_R(d)=mu(d)^2 sum_(h,k in H_d(B_d))
          [M(A_h)+M(A_k)-M(T_(d,h,k))],                 (GD.1)

C_R(g)=sum_(1<=k<=N/g)mu(k)S_R(gk),                  (GD.2)
Q_R=sum_g C_R(g)=S_R(1)=2M(N)-M(X).                  (GD.3)
```

The labels h,k in GD.1 are auxiliary convolution labels; they are not new physical prime occurrences or multiple independent uses of one historical supply. Their exact signed coefficients reconstruct the original sum before any inequality. No matching claim is made.

**GD2, complete-source transfer.** Fix c>1/2 and A>=0 such that |M(n)|<=A n^c for EVERY integer n>=1. Define fixed positive constants

```text
w_c(p)=(1-p^(-c))^(-2),
W_c(d)=product_(p|d) w_c(p),
Z_c=product_p (1+w_c(p)/p^(2c)),
Y_c=product_p (1+w_c(p)^2/p^(4c)),
E_c=product_p (1+(w_c(p)-1)/p),
E_c,2=product_p (1+(w_c(p)^2-1)/p).
```

All four infinite products converge for fixed c>1/2. Every constant below is chosen before R, g, and G. For every R>=2 and 1<=g<R,

```text
|C_R(g)| <= 3 A Z_c X^c mu(g)^2 W_c(g)/g^(2c),       (GD.4)
D_G(R) <= 9 A^2 Z_c^2 Y_c X^(2c).                   (GD.5)
```

For every real G>=1 the COMPLETE tails satisfy

```text
sum_(G<g<R)|C_R(g)|
  <= 3 A Z_c [2c E_c/(2c-1)] X^c G^(1-2c),          (GD.6)

sum_(G<g<R) C_R(g)^2
  <= 9 A^2 Z_c^2 [4c E_c,2/(4c-1)] X^(2c)G^(1-4c). (GD.7)
```

There is no g-dependent hidden constant. This is a substantive arithmetic restriction on the full gcd coefficient vector, but after using the existing Mertens input it carries the same global exponent, not a new one.

**GD3, converse and exponent equivalence.** Suppose 1/2<=b<c<=1, |M(n)|<=A n^c for all n>=1, and D_G(R)<=B R^(4b) for all R>=2. Then a constant A' depending only on A,B,b,c exists with

```text
|M(n)| <= A' n^(b+(c-b)/(4c-1)) for all n>=1.        (GD.8)
```

Consequently for 1/2<=b<=1,

```text
MertensGrowthAtMost(b)
 iff [forall epsilon>0 exists B_epsilon>=0 forall R>=2:
        D_G(R)<=B_epsilon R^(4b+epsilon)].             (GD.9)
```

Neither GD.8 nor GD.9 assumes GC5, a favorable sign for any C_R(g), phase independence, or a fixed sign of the total gcd cross interaction.

**GD4, the actual historical denominator.** For fixed 0<=eta<1/2, N_eta as stated in A implies MertensGrowthAtMost(1/2+eta). More specifically, if c>=1/2+eta and c<=1,

```text
MertensGrowthAtMost(c) AND N_eta
  ==> MertensGrowthAtMost((2c+1)/4+eta/2).             (GD.10)
```

Iteration yields the displayed limit exponent with positive losses retained. For any eta<b_cert-1/2, a proof of N_eta would therefore beat b_cert. N_eta is NOT proved by GD2 at that range. The input's constants must precede all R.

### E. Mathematical Proof

#### Exact Arithmetic Reconstruction

For positive integers A_0,B_0,T with A_0,B_0<=T and T<(A_0+1)(B_0+1),

```text
sum_(a<=A_0,b<=B_0)mu(a)mu(b)floor(T/(ab))
  =M(A_0)+M(B_0)-M(T).                               (GD.11)
```

Indeed the unrestricted double sum through T is M(T), since mu*mu*zeta=mu. The omitted a>A_0 strip is M(T)-M(A_0): for each a, the complete b sum is sum_(b<=T/a)mu(b)floor((T/a)/b)=1. The analogous b strip is M(T)-M(B_0). Their overlap is empty by the STRICT wall. Subtract both strips. This is the ordinary exact Mobius/hyperbola principle, credited to the existing renewal and signed-hyperbola infrastructure, not a new cancellation theorem by itself. At equality a nonempty signed corner must be restored.

For all d,u>=1, unique factorization gives

```text
mu(du)=mu(d) mu(u) 1_(gcd(u,d)=1),
mu(u)1_(gcd(u,d)=1)
  =sum_(h|u, every prime of h divides d)mu(u/h).       (GD.12)
```

For p|d, the local divisor sum is 1 on exponent zero and zero on every positive exponent; for p not dividing d it is the usual Mobius value. Thus GD.12 is valid also when d or u is squareful. It is the convolution inverse form of the already-compiled finite-wheel rough-Mobius/smooth-indicator identity.

Write a=du,b=dv in S_R(d), then substitute GD.12 for u,v and reindex u=hi,v=kj. This yields rectangles i<=floor(B_d/h), j<=floor(B_d/k), with floor weight floor(T_(d,h,k)/(ij)). Each original coefficient is restored exactly; both orientations remain.

For h,k<=B_d, X>d^2 B_d^2, so T_(d,h,k)>=A_h and >=A_k. Also

```text
h(A_h+1)>=B_d+1, k(A_k+1)>=B_d+1,
d(B_d+1)>=R,
d^2 h k(A_h+1)(A_k+1)>=R^2>X.
```

Therefore T_(d,h,k)<(A_h+1)(A_k+1) with no discarded corner, including when d divides R or h divides B_d+1. Apply GD.11 to get GD.1. Finally S_R(d)=sum_(d|g)C_R(g); finite divisor inversion gives GD.2. At d=1 the only smooth pair is (1,1), giving GD.3, in agreement with the existing compiled original-source endpoint theorem.

#### Uniform Norm And Tail

Since A_h,A_k<=T_(d,h,k), every summand in GD.1 has absolute value at most 3A T_(d,h,k)^c. Thus

```text
|S_R(d)| <= 3A X^c mu(d)^2 d^(-2c)
              [sum_(h in H_d(B_d))h^(-c)]^2
           <=3A X^c mu(d)^2 d^(-2c) W_c(d).           (GD.13)
```

The finite-prime geometric product is exact when the nonnegative smooth sum is extended to infinity. It remains legitimate when d grows.

If S_R(gk) is nonzero then g,k are squarefree and coprime. Therefore W_c(gk)=W_c(g)W_c(k). Take absolute values in GD.2 and extend the nonnegative squarefree k sum to infinity. Its Euler product is Z_c. This proves GD.4, and squaring/summing over squarefree g gives GD.5 with Y_c. For large p, w_c(p)=1+O_c(p^(-c)), so convergence follows by comparison with sum n^(-2c) and sum n^(-4c), respectively. Small primes cause only fixed finite factors.

For the tail estimates, put h_c(d)=0 unless d is squarefree and h_c(d)=product_(p|d)(w_c(p)-1) otherwise. These are nonnegative and W_c(n)=sum_(d|n)h_c(d). Hence for every real t>=1,

```text
sum_(n<=t)W_c(n) <= t sum_d h_c(d)/d = E_c t.
```

E_c converges because its local increment is O_c(p^(-1-c)). Partial summation, retaining and then dropping only the NONPOSITIVE lower boundary, gives

```text
sum_(n>G) W_c(n)n^(-s) <= [s E_c/(s-1)]G^(1-s), s>1.
```

Use s=2c in GD.4 to prove GD.6. The identical argument for W_c(n)^2, whose local increment is w_c(p)^2-1, proves GD.7 with s=4c. This uses no prime-distribution theorem and no unsigned wheel-survivor substitution for Mobius signs.

#### Converse Without GC5

For every G in [1,R), split the EXACT sum Q_R=sum_g C_R(g). Cauchy-Schwarz is used only on its at-most-G head, while GD.6 controls the full tail:

```text
|Q_R| <= sqrt(G) sqrt(D_G(R))
            + L_c A R^(2c) G^(1-2c),                (GD.14)
L_c=3 Z_c*2c E_c/(2c-1).
```

Both terms and their costs are retained. Choose G=R^alpha with

```text
alpha=4(c-b)/(4c-1),
0<alpha<1,
2b+alpha/2=2c+alpha(1-2c)
          =2[b+(c-b)/(4c-1)].
```

Real G is allowed since the head has floor(G)<=G indices; there is no rounding loss. GD.14 proves the stated square-endpoint exponent. GD.3 adds 2M(R-1), whose R-power c<=1 is no larger than that exponent. For a general n, choose R=floor(sqrt(n+1)); then R^2-1<=n<(R+1)^2-1 and the difference from the lower endpoint contains at most 2R Mobius terms. This O(sqrt(n)) interpolation is paid because the new exponent is at least 1/2. Finitely many n<3 are absorbed into A'. This proves GD.8 for ALL prefixes, not just a square subsequence.

For the forward arrow of GD.9, apply GD.5 with c=b+epsilon/4. For the reverse at b<1, fix any target loss delta>0 and choose b' strictly between b and min(1,b+delta). The assumed norm bound gives a fixed D_G(R)<=B R^(4b'). Start with the genuine trivial Mertens power c_0=1 and repeatedly apply GD.8 at b'. Then

```text
c_(j+1)=b'+(c_j-b')/(4c_j-1),
0<c_(j+1)-b' <= (c_j-b')/(4b'-1).
```

The last contraction factor is strictly less than one. After finitely many steps c_j<b+delta, giving the required power bound. Constants may grow with j and delta but remain uniform in n. The case b=1 follows from the trivial power and GD.5. For b=1/2, the same proof uses b'>1/2; it never evaluates the divergent product Z_(1/2). As an additional check, under the stronger fixed norm D_G=O(R^2), starting c_0=1 gives exactly c_j=1/2+1/(4j+2).

This is not circular: only the assumed norm bound and a PREVIOUSLY proved Mertens power are used at each finite step. The improved power is obtained from the complete source with every tail charged. No supremum over an unbounded unknown function is assumed finite.

#### Historical K_R And The Conditional Consumer

If |M(n)|<=A n^c with c>=1/2, then

```text
K_R <= (A+1)^2 R^(2c-1).                             (GD.15)
```

For u>=1 use |M(u)-1|<=A u^c+1<=(A+1)u^c and divide by u+1. The u=0 term is exactly 1 and is covered. This is an upper bound derived from a genuine all-prefix estimate, not the information-losing replacement K_R=1. In particular all actual historical sites and the shift by 1 are retained.

N_eta and GD.15 give D_G(R)<=B(A+1)^2 R^(1+2c+2eta). At the every-positive-loss level this is precisely the right side of GD.9 with b=(2c+1)/4+eta/2. Its converse proves GD.10. Starting from MertensGrowthAtMost(1), the resulting exponents are

```text
c_j=1/2+eta+(1/2-eta)2^(-j).
```

They approach 1/2+eta. For each requested positive final loss use a FINITE j, then spend a smaller positive loss in that already-proved growth statement. No uniform-in-j constant is needed. Thus N_eta is sufficient independently of GC5.

Conversely, MertensGrowthAtMost(1/2) implies D_G(R)<=B_eta R^(2+2eta) by GD.9 for every eta>0; since the ORIGINAL K_R>=1 this implies N_eta. This proves the all-positive-loss equivalence, not a zero-loss converse. At eta=0, the internal Mertens-energy-to-RH consumer can be used after obtaining all positive losses; no new classical prime-discrepancy premise is imported.

### F. Structural Consequence

The full gcd vector cannot behave like arbitrary R unrelated signed coordinates: once a genuine Mertens power is known, its large-gcd amplitude and energy have summable tails GD.6-GD.7, uniformly over the growing gcd labels. This derives from prime exclusion plus exact rectangular support, not a maximum-degree bound or a drawing of incidence edges.

It also prevents the norm from being promoted as an easier independent estimate merely because the empirical cross term is negative. Its exponent is exactly the Mertens exponent in GD.9. GC5 remains an interesting stronger POINTWISE sign conjecture, but its truth is unnecessary for the exponent consumer and is not established here. D_G itself is quartic in the original Mobius coefficients; the historical Q_R is bilinear.

This does not say that every fixed g already has the full difficulty, that D_G and Q_R^2 are pointwise comparable, or that every successful proof of D_G is circular. A genuinely independent proof of a better norm bound would be valid global progress. The new equivalence says where that proof must supply genuinely new arithmetic.

### G. Signed And Quantitative Relevance

#### 2. FOUR-WAY SOURCE MAP

| Euler / finite AC | VF / actual primes | NNS / OAI | Square blocks / CORR4 | Prime-side coupling |
| --- | --- | --- | --- | --- |
| Literal Q_R and C_R(g), complete ordered pairs at X=R^2-1; GD.1-GD.3 are paper EXACT_IDENTITIES built from compiled inversion. The original endpoint Q_R=2M(R-1)-M(X) is compiled. K_R is the strict shifted historical maximum. | Complete finiteWheelFract minus finiteWheelSquareDeterministic equals li(X)-pi(X), with every virtual d>X compensated first. This is its own EXACT_IDENTITY, NOT an equality with Q_R or D_G. | Q_R^2=D_G+2sum_(g<h)C_R(g)C_R(h) is exact scalar algebra. A direct source-weight/mask map to original complex ideal LOW atoms or clipped #915 cells is OPEN_BRIDGE. No isometry or triangle estimate is called cancellation. | The native output is the COMPLETE Mertens prefix. GD.8 explicitly pays between-square interpolation. CORR4's q^2 daughters have their own cutoffs and full mixed bill; no upper band is removed by GD.1. | Prime/floor-Li Buchstab is an existing cofactor-weighted bilinear coupling, not equality of errors. Current Owner MC shows the actual current mask does not commute with the unmasked completion. |
| GD.9 is a NEW PAPER exponent-level BOUND_EQUIVALENCE with Mertens growth, not pointwise equality of norms. | Canonical VF/Li_2 has its fixed bounded offset; principal-value li has a separate normalization. No new prime-discrepancy constant is obtained. | The native Hecke-to-zeta-to-Mertens theorem is a ONE_WAY size input; no rational-Mobius/Hecke-phase identification is used. | Full reciprocal bands telescope to exact endpoint differences. Fixed lower bands retain the large endpoint and are not paid merely by root history. | Proper-source positivity and near-resonance retain their exact source scopes. |

#### 3. FIRST SIGNED LOSS

| Exact source / location | Loss and discarded interaction | Before / after cost | Recovery and complement |
| --- | --- | --- | --- |
| eulerFloorBilinearQ, research/EULER_FRACTIONAL_COUPLED_20261027.lean:41 | Atomwise absolute values erase all within-gcd and between-gcd cancellation. | Elementary R^2 log^2 R amplitude; desired finite-C scale R sqrt(K_R). | GD.1 first performs exact Mobius inversion. It is not an estimate of the RH-strength amplitude. |
| Proposed Q_R=sum_g C_R(g) | Full Cauchy-Schwarz gives sqrt(R) sqrt(D_G); pretending GC5 is paid would remove that factor without proof. | A direct full Cauchy bound loses 1/4 in the integer-scale exponent. | GD.6 plus the finite head comparison yields GD.8, then GD.9, with no favorable-sign premise. |
| GD.1 -> GD.13 | Triangle on THREE actual Mertens values and on smooth labels discards their joint signs. | Factor 3 and the explicit W_c(d), followed by convergent Z_c,Y_c; SAME power c. | Existing Mertens input fully pays this transfer, but no exponent saving. This is the first remaining loss a new norm argument would have to improve independently. |
| CORR4 mixed-tail gate / prior JC.1 | Dropping W^2+2W(V+U)-D_top would erase complete upper-band and mixed terms. | Prior R=56 witness T=5312/105 shows isolated positive credit is real; full diagonal still matters. | GD does not pay or remove this separate source. All of JC's complements remain in its own consumer. |

The exact identity Q_R^2=D_G+O_G remains in force. GD never replaces Q_R^2 by D_G. Any signs within a common-divisor or smooth-label sum are preserved until the stated, fully charged inequality.

#### 4. PAID RECOVERY TEST

Already-proved `finiteWheelRoughMoebius_mul_zeta_apply` and `finiteWheelRestrictedFloorIdentity` supply the genuine finite-prime/smooth convolution used in GD.12. They are used on their literal original coefficients, not as positivity of C_R(g). Existing Newton and signed-hyperbola theorems supply the rectangular support mechanism. Their exact specialization is the valid recovery in GD.1.

The complete reciprocal-band theorem `twoABCompleteReciprocalBand_eq_mertensDifference` and its Mertens-growth consumer were read. They do not alone retain the simultaneous gcd restrictions; GD.1 explicitly restores them through the smooth labels. #1127's `finiteWheel_cofactor_pos` has an erased-unit fractional cofactor source with q in [R,2R), whereas C_R(g) has two historical Mobius coefficients and a product floor. The R=15,g=2 negative group already rejects that positivity transfer. #1128 near-resonance rejects automatic phase decorrelation, not GD's deterministic inversion.

The current root-admission and complete virtual-compensation modules were inspected as proper-source identities. No direct quantitative bridge from those prime-side facts to N_eta was found. Owner MC's mask correction, OAI outer Gram losses, and CORR4's complete upper mixed bill remain separate unpaid objects. The accepted principal-product PR/paper advances do not by name control this diagonal; only their eventual genuine Mertens consequence can enter GD2.

#### 5. NET RESULT / ADMISSION VERDICT

Substituting the certified baseline into GD2 proves, ON PAPER as a new consequence,

```text
forall epsilon>0 exists B_epsilon forall R>=2:
  D_G(R) <= B_epsilon R^(4*b_cert+epsilon).
```

It also proves the complete gcd-tail bounds at every fixed c>b_cert. Running GD3 back recovers exactly the same exponent. There is no net gain. GD4 shows how a genuinely better N_eta would be consumed without GC5, but does not prove it. These are supporting transfer and target-equivalence results, not a new admitted route or a filler formalization request.

### H. Falsification, Novelty And Reproducibility

**Preregistered changed test:** exact smooth-divisor reconstruction of the COMPLETE common-divisor and gcd ledgers. The early checkpoint was committed at `755092f947d342a1e284fc9f63c8095c2cdc58db`, blob `f4cd44cd7a83a8fbd267b03cd06ea290417669b7`, then read back exactly before execution. The experiment did not extend GC5's unchanged sign scan.

Primary C++20, compiled with `-O2 -Wall -Wextra -Werror`, checked every R=2..80 and held-outs 127,256,549,5561. A deterministic Mobius sieve through **30,924,720** and direct ordered-pair gcd enumeration were compared against every transformed group. Results: **83 roots, 9,649 common-divisor groups, 9,649 gcd groups, 34,305 smooth rectangles, 11,627,095 nonzero ordered coefficient pairs; zero mismatches.** Each coefficient pair retains its full floor multiplicity; this pair count is not a count of expanded triples. Separately checked **6,878** valid rectangular identities and **144** exact wall cases. The auxiliary c=1 bound `|S_R(d)| phi(d)^2<=3X` also passed for every squarefree d.

An independent Python program uses trial factorization, direct divisor masks, and the quotient-block recurrence `M(t)=1-sum_(j=2..t)M(floor(t/j))`, not the C++ sieve or its endpoint table. It reconstructs every transformed gcd vector at roots 2..40 and the same four held-outs, with additional direct ordered-pair comparisons through R=549. R=5561 uses the independent transform/recurrence; the C++ program supplies its full direct enumeration. The final compact verifier also passed **192 exact rational exponent checks**. An earlier version with 240 such checks completed successfully; only redundant self-K recurrence iterations were reduced in the final reproducible version, with all registered arithmetic roots unchanged. No failed mathematical assertion was removed.

| R | Q_R | D_G(R) | Actual K_R | M(R-1) | M(X) |
| --- | ---: | ---: | --- | ---: | ---: |
| 15 | -7 | 223 | 3/2 | -2 | 3 |
| 17 | 5 | 173 | 3/2 | -1 | -7 |
| 56 | -10 | 12810 | 3/2 | -2 | 6 |
| 549 | -186 | 213476 | 3/2 | 3 | 192 |
| 5561 | 2554 | 19073482 | 3/2 | 5 | -2544 |

These reproduce earlier GC values where overlapping; they are not newly discovered sign data. Every historical maximum was actually computed in the primary verifier. K_R=3/2 on these rows is finite evidence, not an all-scale assertion.

**Strict-wall negative control:** A_0=B_0=1,T=4 gives literal rectangular Q=4, but M(1)+M(1)-M(4)=3. The missing corner (2,2) contributes +1. At equality T=(A_0+1)(B_0+1), the defect is exactly mu(A_0+1)mu(B_0+1). GD.1 proves the strict inequality; it does not assume it from an approximate square root.

**No-circularity checks:** GD2 assumes a stated actual global power. GD3 starts from the independently known trivial power and uses a NEWLY assumed norm only in its converse theorem. Every finite iteration has a completed input theorem; no uniform constants at c=1/2, zero-loss endpoint, unknown global supremum, prime independence, positivity of gcd groups, or GC5 sign is assumed. GD4 states N_eta as an open premise. A norm theorem equivalent to the target is not counted as an independent supplier.

**Novelty search:** searched current main for gcd/diagonal, rectangular Mobius, smooth/self-dual, and MertensGrowthAtMost/gcd combinations; inspected the coordinate atlas, original self-dual pointwise/finite-C/endpoint modules, signed hyperbola, finite-wheel rough/smooth inversion, asymmetric-corner source and reciprocal-band consumer. No matching complete gcd-norm exponent equivalence or uniform growing-gcd tail transfer was found in that search or the recent reports/open PR. Search indexing and finite inspection are not proof of universal absence. The elementary convolution, Mobius inversion, rectangular hyperbola, and generic Cauchy/partial-summation principles are explicitly credited as existing tools, not claimed inventions. GD2-GD4's literal combined source and consumer are the candidate repository novelty.

### I. Conceptual Interpretation

The gcd labels are not an arbitrary partition of a sign sequence. Genuine prime-factor exclusion turns each label into a smooth-divisor family of exactly supported self-dual rectangles. The family has a summable arithmetic tail whenever any exponent above one half is available. That tail is the missing ingredient in reversing a norm estimate without a favorable-sign rule.

Thus the observation that fine gcd groups often compensate is not the only possible consumer. The complete diagonal already encodes the same exponent-level obstruction as M itself. This makes the research question sharper: an independent estimate must improve the signed arithmetic in the reconstructed rectangles, not merely rename their sum of squares.

### J. Competing Structural Hypotheses

- Retain GD.1-GD.7 for independent review as a uniform growing-label transfer. They are more informative than a fixed-g bound because the Euler-product constants are explicit and scale-independent.
- Keep GC5 unresolved as a pointwise statement. Do not prioritize further unchanged sign scans as a prerequisite for the exponent-level route; GD3 no longer needs them.
- Do not infer N_eta with eta<b_cert-1/2 by feeding the present baseline into GD2. The recovered diagonal exponent is 4*b_cert, so that shortcut has no new saving.
- A genuine stronger joint estimate on the complete smooth-rectangle response is admissible, but it must retain historical terms, all h,k, squarefree zero cases, and every cross interaction required by D_G. No such estimate is established here.
- Continue the protected independent routes. This invocation is a substantive FINITE-AC audit using MU-LIFT/rectangular inversion; the preceding own JC invocation covered CORR4 and its complete upper mixed bill. No route is retired or made the sole program.

### K. Specialist Handoffs

**Coordinator:** M2 now has a precise paper answer: GD.9 is exponent-equivalent and GD.10 consumes a historical norm without GC5. Record this as a supporting uniform transfer/target audit, not a new global gain. Do not count an all-epsilon diagonal estimate as an independently weaker RH supplier. Keep the accepted analytic paper endpoint and its unfinished formal return separate.

**Referee:** Independently check GD.1's strict wall after BOTH smooth substitutions; growth of W_c(g) and all Euler-product constants; the full tail in GD.14; square-prefix interpolation; every-positive-loss quantifiers; and GD.10's shifted K_R. First falsifier is the exact equality-wall (1,1,4), then R=15,17,56,549,5561. Return claim-specific ACCEPT/REVISE/REJECT. The author has not supplied that independent verdict.

**Lean Verification:** No source edit is requested before independent acceptance. If strategically useful, the minimal coherent supplier is GD.1 plus its uniform original-coefficient bound; reuse mu*zeta and existing hyperbola/rough-wheel theorems. GD3 needs real tail bounds and finite exponent iteration, not a new axiom or an assumed diagonal gain. Existing #1131 work is not superseded. No need for a filler identity-only PR.

**Analytic:** Check whether a genuinely stronger complete signed estimate can enter before GD.13's three-value triangle, with an actual quantified exponent return. Merely applying the strongest existing Mertens power recovers itself. The real/complex or Hecke transfer cannot be invented; this is a rational-integer source. Today's NT remains a separate NYMAN result pending its own review.

**Owner:** The smooth-divisor rectangles operate on the complete historical pair source, not the current #915 mask. MC's commutator witnesses therefore remain intact. Any weighted/clipped analogue needs a separate coefficient identity with all induced mask corrections, not a declaration that GD.1 survives unchanged.

**Census:** Reuse the exact GD programs and existing GC data. The changed question is GD.1 and the literal uniform tail, not another scan of GC5. If an independently proposed numerical tail constant is supplied, preregister it before testing. Do not fit a missing all-scale N_eta from these rows. Both mandatory held-outs have already been included here.

### L. First Independently Missing Theorem

After independent review of GD, the outstanding arithmetic claim in this lane is still a genuine source estimate, for example

```text
for some fixed 0<=eta<b_cert-1/2:
  exists B>=0 forall integers R>=2,
    sum_(g<R) [sum_(a,b<R,gcd(a,b)=g)
      mu(a)mu(b)floor((R^2-1)/(ab))]^2
      <= B R^(2+2eta) K_R.
```

This is not proved, not certified easier, and not justified by GC5. Its exact consumer is GD.10 and finite exponent iteration. The all-positive-loss RH-strength family is target-equivalent; the fixed eta=0 criterion may be stronger than the every-positive-loss endpoint. An independently better Mertens/source estimate would instead enter GD2 as an already-earned input, not become a second independent gain.

### M. Next-Run Resume Capsule

Main: f7947bee036c4dddb0c36fc9f53ab46b4fa90995. Selected route FINITE-AC; secondary exact MU-LIFT rectangular reconstruction; prior CORR4 upper-band protection retained. Cross-route acknowledgment recorded. GD1-GD4 are PAPER_PROOF/SELF_AUDIT, independent review and formalization PENDING. GD5 is exact finite verification. GC5 remains CONJECTURE; no sign claim was resolved. Canonical VF, finite A/C, original #915 payment, and RH remain OPEN. Certified b_cert unchanged; NO_NEW_GLOBAL_GAIN / NO_NEW_ACCEPTED_ROUTE / VERIFIED_ETA=NONE.

Resume from GD.1-GD.10 rather than recomputing accepted wheel counts, near-resonance, RC radical completion, or unchanged GC sign data. Highest-value next question: can a genuinely new original signed restriction improve the complete smooth-rectangle response before GD.13, or does a proposed simplification merely assume the improved norm? Require an exact full return and first falsifier.

Execution limitations: direct git network access was unavailable (CONNECT tunnel 403), so authoritative sources and publication used the configured GitHub connector. One guessed nonexistent source path returned 404 and was corrected to the actual `research/MERTENS_EXPONENT_ENVELOPES.lean`; no missing source was inferred. No local Lean was run. No source/main/other-report edit, proof branch, PR, workflow launch, merge, agent launch, schedule change, or permission change occurred. Only the owned dated report is authorized remotely. The complete executed reproducibility sources and outputs follow; scratch files are not separate deliverables.

Substantive publication is READBACK_PENDING until the final receipt. The verified early checkpoint is preserved verbatim above.


## Source And Continuity Ledger

### Pinned Main Sources

All following source blobs were retrieved at main `f7947bee036c4dddb0c36fc9f53ab46b4fa90995`. File paths are repository-relative. These hashes establish source identity, not a new compilation of this paper argument.

| Source path | Git blob SHA |
| --- | --- |
| AGENTS.md | c9c89f01b90b526de9f3e8ea92478e36504711b6 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md | e922d4ba9362a1ae196af8f6de88f7417f92087c |
| research/EULER_FRACTIONAL_COUPLED_20261027.lean | e6c4b1690e497760d366e36b28a1f7aa60e19f85 |
| research/EULER_SELF_DUAL_POINTWISE_20261027.lean | c327c556f39ee7014fd774b24d0f95a1ece050e0 |
| research/EULER_SELF_DUAL_FINITE_C_BRIDGE_20261027.lean | e97561ef330a9996fd807d8910369f0698147b01 |
| research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| research/EULER_ASYMMETRIC_CORNER_SIGNED_GRAM_20261028.md | 388ea4b896ea4ffe0054fec9a9149d5c617037c0 |
| research/MERTENS_SIGNED_HYPERBOLA.lean | d199571f19346797229a25b0fa53c6e80499999f |
| RHLean/Analysis/FiniteWheelRestrictedFloor.lean | 94c4d4420fc58cd87d92780c6265decd2cad7e66 |
| RHLean/Analysis/FiniteWheelReciprocalMertensImprovement.lean | 0bc7468b6ad40ed6b32b7d1950b6e73192ae8c36 |
| research/MERTENS_EXPONENT_ENVELOPES.lean | 655b896e8d5a41c9f8fc3c456eae3944a98bfefe |
| research/MERTENS_CONVERSE_IDENTIFICATION.lean | 768c8255850bf4074aff265c3fe17a1f5c43979b |
| RHLean/Proof/SquareRootLegalAncestryGramReduction.lean | 1270d4d91c53b50b110d10014f223f427fb7a575 |
| RHLean/Analysis/MertensPowerGrowth.lean | ae855e8212fa8f12bc225a4d60af004ebd002f7d |
| research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean | 028d9f2bbfa1a8de1fe63e9bd368aca13aae6825 |
| research/TWOAB_RENEWAL_OAI_CONSUMER_20261108.lean | 4880969f71f4668b18a9e09fd6f4007b7e62a5d5 |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/CompleteWheelRootAdmission.lean | a412632c1028d7728cd8d87ee6e5ac365377d338 |
| research/FiniteWheelCofactorPositivity.lean | f83a3daefc2b9d603014af912ec82b4a7f52cfac |
| research/DyadicPrimeNearResonance.lean | f416e0149b73656e30a7f68a3934a937353d3f8d |
| research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a |
| research/oai_434/VF919WindowErrorClosure.lean | f629db1b2b65d6ec042ac9432397d4b6316200c6 |
| research/oai_434/VF919ExplicitSquareBlockPacking.lean | 32999039fdeea99c58a070c1c4ee9c140720dd44 |
| research/oai_434/VF919ExplicitFixedSourceSlotCount.lean | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |
| research/oai_434/VF919ExplicitSlotTotalMass.lean | 71c5b7b5b8032ca3558467126fdf97d3caf1a7df |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| scripts/lean/window_error_closure/WindowErrorClosureAudit.lean | 1f17f9401a63d16227db2e2aad020b9f74bc5f4e |
| docs/COORDINATE_ATLAS.md | cd0419d00a37739fe5a292f5cb738e33213949d5 |

### Two-Date Research Continuity

The following are the CURRENT fetched report blobs, which can differ from the substantive blobs named in their later receipts. Receipt times below are the reports' recorded verification times, not new specialist executions inferred from schedules. Their relevant statements and evidence were read; author publication verification is not mathematical acceptance. Both Coordinator mirrors were read and matched. Today's missing roles remain `TODAY=PENDING; YESTERDAY=CARRY_FORWARD`.

| Dated report | Current blob SHA | Relevant original claims and retained scope | Latest recorded receipt |
| --- | --- | --- | --- |
| 2026-11-10/00-coordinator-am.md | 4d55b2893f974656c6aa14e48b243827fa8308f8 | 20261110-coordinator-2309-EST/FFR1-FFR4; M2 full gcd-norm assignment; latest source/return audit. FFR now has today's Analytic paper review, not a new compiled endpoint. | 2026-11-11 04:36:23 UTC; substantive ce6a9344d7f86add41d7defd2a645e31bb8ae70d |
| 2026-11-10/10-owner-payment.md | 84afec90414b2394a61b51df46c07b6b540e5942 | 20261110-owner-3/DR1-DR5; same-fibre reinforcement, failed q=78 contraction, complete unmasked logarithmic estimate from existing Mertens input; SELF_AUDIT. | 2026-11-10 16:43:55 EST; substantive a565c31085995987d38f2e46b6d6224fe21e18eb |
| 2026-11-10/20-analytic-type-ii.md | 7ed3a39bec4796f4173b692064af872ea8035048 | 20261110-analytic-3/IR1-IR4; independently accepted ON PAPER by Referee IRR, endpoint NOT_FORMALIZED. Older RD response-only limitation retained. | 2026-11-10 22:38:54 UTC; substantive 494509e00315ca7616ce235594ea098d14fc52dc |
| 2026-11-10/30-finite-wheel.md | 62406503a1ddbbf9330abcdc4cf761f7fbf05795 | 20261110-wheel-3/RC1-RC5 radical completion and log estimate; 20261110-wheel-2/JC retains all upper CORR4 mixed bands. No current-mask commutation asserted. | 2026-11-10 23:34:46 UTC; substantive 4769b57101fbc0821dbc43110e837b05b7442302 |
| 2026-11-10/40-prime-census.md | a3cfa56072f3893dbf92a18956e1794236bde057 | 20261110-census-2/GC1-GC2 REFUTED sign/coarsening rules; GC3 exact reconstruction; GC4 finite evidence; GC5 Q^2<=D_G CONJECTURE only. | 2026-11-11 00:19:48 UTC; substantive d48d9ca10f0afdddef44c39c992b6aad0fec055e |
| 2026-11-10/50-adversarial-referee.md | 6529562a5bb21fa192fddadaa91a758b9d125c29 | 20261110-referee-3/IRR accepts IR/MD ON PAPER; GC1/GC2 witnesses accepted, GC5 independently tested R=2..2000 but UNPROVED; coherent response no-go is model-scoped. | 2026-11-10 20:37 EST; substantive ce3f4087703d1ea869af4564481110d6ff62d8d5 |
| 2026-11-10/60-lean-verification.md | 682b334b8f37fa4bfe2d552a1142d852a0db2afd | 20261110-lean-3/MD: #1131 finite complete-product approximation tested at PR head; full accepted endpoint NOT_FORMALIZED. | No explicit time in latest receipt; substantive 55f669489a46b1660b5fc85dfbc774f714c8639a |
| 2026-11-11/10-owner-payment.md | e60f67d2192932715895f9e9b72a6fe773d4a68d | 20261111-owner-1/MC1-MC4 current-mask commutator; r=10, p=3, b=101 gives +4w(1-w), b=115 gives -4w^2 while completion is zero; PAPER/SELF_AUDIT. | 2026-11-11 00:35 EST; substantive 5543e710336330468efff4a6fdb929087ef5965a |
| 2026-11-11/20-analytic-type-ii.md | eab26782cdd44e705e007185d6c7321d9300ca61 | 20261111-analytic-1/NT2-NT3: vanishing Nyman full-period variance forces full norm liminf>=1; optimizer full norm tends to 1; independent review PENDING. Separate scoped FFR/IRR2 reviews. | 2026-11-11 01:44 EST; substantive 6f7f7ad0afe9740e35cefce6b541944bf9ccffb1 |

The November 10 Coordinator PM mirror has the same blob `4d55b2893f974656c6aa14e48b243827fa8308f8`. Today's own early checkpoint is `755092f947d342a1e284fc9f63c8095c2cdc58db`, blob `f4cd44cd7a83a8fbd267b03cd06ea290417669b7`, independently fetched after creation. No new paper GD verdict exists yet.

External inbox `research/agent_reports/EXTERNAL_HANDOFFS.md` was retrieved from agent-reports at blob `038018145c0fddb2f6306c0712373adf9cd1ea52`. Its newest entries are still October 18: no new external mathematical evidence was admitted. Retain `EXT-20261018-PNT-1`'s cofactor-weighted prime/floor coupling and `EXT-20261014-5`'s all-R limsup versus first-bad-denominator distinction. Historical routing language in that inbox cannot supersede current main policy.

At **2026-11-11 07:33:18 UTC / 02:33:18 EST**, the final branch and today-directory refresh confirmed unchanged main, unchanged Owner/Analytic blobs, only those two reports plus this role's checkpoint for November 11, and only non-draft open #1131 at unchanged `621f48b34b5ace39c05aba33ff33b6d014544b4d`. Its check-run collection was directly inspected earlier in this execution: **13/13 success**, not a merged endpoint. Recent merged #1122/#1124 complete-wheel/root-admission, #1126 reciprocal-band iteration, #1127 cofactor positivity, #1128 near-resonance repair, #1129 cross-route instructions and #1130 instruction follow-up were discovered and their relevant source scopes inspected. Current #1131 is not counted among them.

### Reproducibility Contract

The programs below are the exact final executed sources. They use integer or rational arithmetic for every identity/sign/exponent check. The primary sieve table and the independent quotient-block Mertens recurrence share the mathematical definition but no computed table. No infinite inequality is inferred from these finite runs. All proof of the uniform constants and exponent transfer is in E.

File SHA-256 values:

- `gcd_diagonal_check.cpp`: `e5305a61d09d9949b1db1524fe4cf41527531ae1a0d3ba11109aef8b50d6394d`.
- `gcd_diagonal_independent.py`: `46e828d0706adab59f815548ef72102590511e76742420f49a07b53f64a8d9fe`.

Reproduction commands in a directory containing the two literal source blocks:

```bash
g++ -std=c++20 -O2 -Wall -Wextra -Werror gcd_diagonal_check.cpp -o gcd_diagonal_check
./gcd_diagonal_check
python -m py_compile gcd_diagonal_independent.py
python gcd_diagonal_independent.py
```

### Primary Exact Verifier

```cpp
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using i64 = std::int64_t;

int main() {
    std::vector<int> roots;
    for (int r = 2; r <= 80; ++r) roots.push_back(r);
    for (int r : {127, 256, 549, 5561}) roots.push_back(r);
    const int limit = roots.back() * roots.back() - 1;
    std::vector<std::int8_t> mu(limit + 1, 0);
    std::vector<bool> composite(limit + 1, false);
    std::vector<int> primes;
    mu[1] = 1;
    for (int n = 2; n <= limit; ++n) {
        if (!composite[n]) { primes.push_back(n); mu[n] = -1; }
        for (int p : primes) {
            if (static_cast<i64>(n) * p > limit) break;
            composite[n * p] = true;
            if (n % p == 0) { mu[n * p] = 0; break; }
            mu[n * p] = static_cast<std::int8_t>(-mu[n]);
        }
    }
    std::vector<int> mertens(limit + 1, 0);
    for (int n = 1; n <= limit; ++n) mertens[n] = mertens[n-1] + mu[n];
    i64 rectangles = 0, boundary_cases = 0, common_groups = 0;
    i64 smooth_rectangles = 0, gcd_groups = 0, ordered_pairs = 0;
    for (int a = 1; a <= 12; ++a) {
        for (int b = 1; b <= 12; ++b) {
            for (int t = std::max(a, b); t <= (a+1)*(b+1); ++t) {
                i64 direct = 0;
                for (int i = 1; i <= a; ++i)
                    for (int j = 1; j <= b; ++j)
                        direct += mu[i] * mu[j] * (t / (i*j));
                const i64 base = mertens[a] + mertens[b] - mertens[t];
                if (t < (a+1)*(b+1)) { assert(direct == base); ++rectangles; }
                else { assert(direct-base == mu[a+1]*mu[b+1]); ++boundary_cases; }
            }
        }
    }
    assert(4 != mertens[1] + mertens[1] - mertens[4]);
    std::cout << "R,Q,D,K_num,K_den,M_history,M_endpoint,transform_terms\n";
    for (int r : roots) {
        const int x = r*r-1;
        std::vector<i64> c(r, 0), s(r, 0), rebuilt(r, 0);
        for (int a = 1; a < r; ++a) {
            if (!mu[a]) continue;
            for (int b = a; b < r; ++b) {
                if (!mu[b]) continue;
                const int mult = a == b ? 1 : 2;
                c[std::gcd(a,b)] += static_cast<i64>(mult) * mu[a]*mu[b] * (x/(a*b));
                ordered_pairs += mult;
            }
        }
        i64 row_terms = 0;
        for (int d = 1; d < r; ++d) {
            for (int g = d; g < r; g += d) s[d] += c[g];
            if (!mu[d]) { assert(s[d] == 0); ++common_groups; continue; }
            int rest = d, phi = d;
            std::vector<int> pf;
            for (int p : primes) {
                if (static_cast<i64>(p)*p > rest) break;
                if (rest % p == 0) {
                    pf.push_back(p); phi = phi/p*(p-1);
                    while (rest % p == 0) rest /= p;
                }
            }
            if (rest > 1) { pf.push_back(rest); phi = phi/rest*(rest-1); }
            const int bound = (r-1)/d;
            std::vector<int> smooth{1};
            for (int p : pf) {
                const auto old = smooth;
                for (int h : old)
                    for (i64 v = static_cast<i64>(h)*p; v <= bound; v *= p)
                        smooth.push_back(static_cast<int>(v));
            }
            std::sort(smooth.begin(), smooth.end());
            assert(std::adjacent_find(smooth.begin(), smooth.end()) == smooth.end());
            i64 value = 0;
            for (int h : smooth) {
                for (int k : smooth) {
                    const int a = bound/h, b = bound/k;
                    const int t = static_cast<int>(x/(static_cast<i64>(d)*d*h*k));
                    assert(1 <= a && a <= t && 1 <= b && b <= t);
                    assert(t < static_cast<i64>(a+1)*(b+1));
                    value += mertens[a] + mertens[b] - mertens[t];
                    ++smooth_rectangles; ++row_terms;
                }
            }
            assert(value == s[d]);
            assert(std::abs(value)*static_cast<i64>(phi)*phi <= 3LL*x);
            ++common_groups;
        }
        for (int g = 1; g < r; ++g) {
            for (int k = 1; g*k < r; ++k) rebuilt[g] += mu[k]*s[g*k];
            assert(rebuilt[g] == c[g]);
            ++gcd_groups;
        }
        const i64 q = std::accumulate(c.begin(), c.end(), i64{0});
        i64 diagonal = 0;
        for (i64 v : c) diagonal += v*v;
        assert(q == 2LL*mertens[r-1]-mertens[x]);
        i64 kn = 1, kd = 1;
        for (int u = 0; u < r; ++u) {
            const i64 n = static_cast<i64>(mertens[u]-1)*(mertens[u]-1), d = u+1;
            if (n*kd > kn*d) { kn = n; kd = d; }
        }
        const i64 divisor = std::gcd(kn,kd); kn /= divisor; kd /= divisor;
        if (r <= 6 || r == 15 || r == 17 || r == 56 || r > 80)
            std::cout << r << ',' << q << ',' << diagonal << ',' << kn << ',' << kd
                      << ',' << mertens[r-1] << ',' << mertens[x] << ',' << row_terms << '\n';
    }
    std::cout << "PASS_EXACT_SOURCE roots=" << roots.size() << " limit=" << limit
              << " rectangles=" << rectangles << " boundary_cases=" << boundary_cases
              << " common_groups=" << common_groups << " gcd_groups=" << gcd_groups
              << " smooth_rectangles=" << smooth_rectangles
              << " ordered_pairs=" << ordered_pairs << '\n';
}
```

Executed output, exit 0:

```text
R,Q,D,K_num,K_den,M_history,M_endpoint,transform_terms
2,3,9,1,1,1,-1,1
3,2,4,1,1,0,-2,2
4,-1,35,1,1,-1,-1,3
5,0,104,1,1,-1,-2,6
6,-3,299,3,2,-2,-1,7
15,-7,223,3,2,-2,3,24
17,5,173,3,2,-1,-7,32
56,-10,12810,3,2,-2,6,147
127,33,61309,3,2,-1,-35,370
256,-16,68992,3,2,-1,14,831
549,-186,213476,3,2,3,192,1934
5561,2554,19073482,3,2,5,-2544,23316
PASS_EXACT_SOURCE roots=83 limit=30924720 rectangles=6878 boundary_cases=144 common_groups=9649 gcd_groups=9649 smooth_rectangles=34305 ordered_pairs=11627095
```

### Independent Exact Verifier

```python
"""Trial-factor and divisor-recurrence checks, independent of the C++ sieve."""

from functools import lru_cache
from fractions import Fraction as F
from math import gcd
import json


@lru_cache(None)
def factors(n):
    out = []
    p = 2
    while p*p <= n:
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


@lru_cache(None)
def mu(n):
    ff = factors(n)
    return 0 if any(e > 1 for _, e in ff) else (-1)**len(ff)


@lru_cache(None)
def mertens(n):
    if n == 0:
        return 0
    result, left = 1, 2
    while left <= n:
        q = n//left
        right = n//q
        result -= (right-left+1)*mertens(q)
        left = right+1
    return result


def smooth_list(d, bound):
    return [h for h in range(1, bound+1)
            if all(d % p == 0 for p, _ in factors(h))]


def check(r, direct):
    x = r*r-1
    s = [0]*r
    for d in range(1, r):
        if not mu(d):
            continue
        b = (r-1)//d
        hs = smooth_list(d, b)
        s[d] = sum(mertens(b//h)+mertens(b//k)-mertens(x//(d*d*h*k))
                   for h in hs for k in hs)
        if direct:
            original = sum(mu(a)*mu(bb)*(x//(a*bb))
                           for a in range(d,r,d) for bb in range(d,r,d))
            assert s[d] == original
    c = [0] + [sum(mu(k)*s[g*k] for k in range(1,(r-1)//g+1))
                 for g in range(1,r)]
    if direct:
        exact = [0]*r
        for a in range(1,r):
            for b in range(1,r):
                exact[gcd(a,b)] += mu(a)*mu(b)*(x//(a*b))
        assert c == exact
    assert sum(c) == 2*mertens(r-1)-mertens(x)
    return [r, sum(c), sum(v*v for v in c)]


small = [check(r, True) for r in range(2,41)]
held = [check(r, r <= 549) for r in (127,256,549,5561)]
count = 0
for b in (F(1,2), F(3,5), F(3,4), F(7,8)):
    c = F(1)
    for j in range(1,41):
        alpha = 4*(c-b)/(4*c-1)
        new = b+(c-b)/(4*c-1)
        assert 0 < alpha < 1
        assert 2*b+alpha/2 == 2*c+alpha*(1-2*c) == 2*new
        assert b < new < c
        if b == F(1,2):
            assert new == F(1,2)+F(1,4*j+2)
        c = new
        count += 1
for eta in (F(0),F(1,16),F(1,8),F(1,4)):
    c = F(1)
    for _ in range(8):
        b = (1+2*c+2*eta)/4
        new = b+(c-b)/(4*c-1)
        assert new == c-(2*c-1)*(c-F(1,2)-eta)/(4*c-1)
        assert F(1,2)+eta < new < c
        c = new
        count += 1
print(json.dumps({"status":"PASS_INDEPENDENT_EXACT", "small_roots":len(small),
                  "held_out":held, "rational_exponent_checks":count,
                  "M_cache":mertens.cache_info()._asdict(),
                  "square_wall_negative_control":{"A":1,"B":1,"T":4,
                       "literal_Q":4,"incorrect_no_corner":3}}, indent=2))
```

Executed output, exit 0:

```json
{
  "status": "PASS_INDEPENDENT_EXACT",
  "small_roots": 39,
  "held_out": [
    [
      127,
      33,
      61309
    ],
    [
      256,
      -16,
      68992
    ],
    [
      549,
      -186,
      213476
    ],
    [
      5561,
      2554,
      19073482
    ]
  ],
  "rational_exponent_checks": 192,
  "M_cache": {
    "hits": 2254895,
    "misses": 11166,
    "maxsize": null,
    "currsize": 11166
  },
  "square_wall_negative_control": {
    "A": 1,
    "B": 1,
    "T": 4,
    "literal_Q": 4,
    "incorrect_no_corner": 3
  }
}
```


## Verified Publication Receipt - 20261111-wheel-1/GD

Verified **2026-11-11 07:36:36 UTC / 02:36:36 EST**. The complete substantive report was committed on agent-reports at [a32bc3548eeb0daa7bd616380309f244bd71f78b](https://github.com/OVVO-Financial/RH_Lean/commit/a32bc3548eeb0daa7bd616380309f244bd71f78b), blob `47415e8f8a0ecfaeeb0e755994556222849cb9f2`. Immutable-commit readback matched all **58,254 bytes** exactly, including the full **3,358-byte** early checkpoint as an unchanged prefix. Commit inspection confirmed exactly the owned November 11 Finite Wheel report: **791 additions, zero deletions**, no other file changed.

Prepublication report SHA-256: `f923088f4baeb2aa2401a1d139b3d2be33eddf7228052e257abd3256db23602b`. Validation passed A-M and all five cross-route stages, ASCII/Markdown structure, **62 balanced fence markers**, **six consistent tables**, exact byte equality of both embedded executed programs and outputs, both program hashes, arithmetic summary rows and preserved checkpoint. Both exact checkers completed successfully; no computation or Lean process remains running.

`EXECUTION=COMPLETE; SUBSTANTIVE_PUBLICATION=PUBLISHED_READBACK_VERIFIED.` This closes earlier execution/publication-pending wording only. GD1-GD4 remain **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**, with the conditional and target-equivalent scopes stated above. GD5 remains exact finite evidence. No new norm inequality is proved; GC5 stays CONJECTURE; **NO_NEW_GLOBAL_GAIN / NO_NEW_ACCEPTED_ROUTE / VERIFIED_ETA=NONE**. Certified baseline and canonical VF/finite A-C/RH status are unchanged and OPEN.

Only this role's owned daily report was modified remotely. No Lean execution, source/main/other-report edit, proof branch or PR creation, workflow launch, merge, agent launch, schedule change or permission change occurred. The receipt is appended against a fresh current blob and its returned immutable commit is checked before final delivery; it references the already-verified substantive commit instead of guessing its own future SHA.





## Scheduled Continuation Checkpoint - 20261111-wheel-2/PD

IN_PROGRESS. Actual scheduled trigger: 2026-11-11 10:12:01 EST; platform run ID unavailable. America/New_York report date 2026-11-11. Main retrieved as dda92f9ce59627b4c1f1317082f728648d330a0a; AGENTS blob c9c89f01b90b526de9f3e8ea92478e36504711b6; contract blob 95566e37c8eaeb99ee680660df4f9d2e06ea5038; policy blob e922d4ba9362a1ae196af8f6de88f7417f92087c. cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1.

Resuming GD1-GD4 and Coordinator 20261111-coordinator-0710-EST/M2. GD's exponent equivalence has today's Referee paper acceptance; it is not a new norm bound. Both calendar dates' seven report files and external inbox were retrieved; all today's roles are present. New Owner FA and Analytic DM entries will be consumed at their stated scopes. #1131 is now on main; its finite complete response is not the full accepted paper endpoint. No open PR was returned by the initial search; metadata/CI verification continues.

Candidate PD: split every GD smooth rectangle into its strictly historical Mertens terms and its T>=R terms. Test whether the latter are exactly supported on q=d^2*t<=R-1 with t d-smooth, hence powerful q, and whether their divisor-incidence columns have zero total for q>1. Retain the full historical vector, every mixed term, and q=1 endpoint. Attempt a uniform historical-vector norm bound using the genuine K_R and an explicit inverse restriction before claiming a new mechanism. This is a proposed derivation, not yet a verified theorem or global gain.

Registered changed experiment, before execution: all R=2..100 plus 127,256,549,5561; literal ordered pairs and gcd groups versus the historical/powerful decomposition, including diagonal multiplicity, strict cutoffs, complete cross energy and column Gram. Independently trial-factor small cases. Negative controls: equality wall (1,1,4); nonzero Gram of radicals 2 and 3; clipping a divisor-incidence column destroys its zero total. Reuse the published GC/GD endpoint values only as regressions, not new sign evidence. Do not rerun unchanged GC5/H_Z sweeps. No fitted global constant, no independence assumption, no new source or Lean edits.

Expected disposition is either a complete proved structural supplier with an independently justified exclusion, or a supporting identity/inverse restriction with its first missing arithmetic estimate exposed. NO_NEW_GLOBAL_GAIN at this checkpoint. Only this owned report may be changed remotely; proof branches, PRs, merges, other reports and schedules remain untouched.


## Powerful Denominators Localize The Unpaid Gcd Response

### Final Research Synthesis - 20261111-wheel-2/PD

### A. Most Important Structural Discovery

**Every part of the complete gcd vector not controlled directly by the strict historical envelope is supported on gcd labels g^2<R. It is an exact signed response of M(floor((R^2-1)/q)) over POWERFUL denominators q<R, with explicitly determined multiplicities and cross interactions.** Here powerful means that each prime exponent is at least two; the unit is included.

There is an absolute constant C_H, independent of R and of any assumed Mertens growth exponent, and an explicit vector H_R using only M(t), t<R, such that

```text
C_R = H_R - E_R,
||H_R||_2 <= C_H R sqrt(K_R) (1+log(R-1)),
E_R(g)=0 whenever g^2>R-1.

E_R(g)=sum_(q<=R-1 powerful, g|rad(q))
          a(q) mu(rad(q)/g) M(floor((R^2-1)/q)),
a(q)=product_(p^e || q)(e-1), a(1)=1.
```

The nonunit columns sum to zero EXACTLY across the complete gcd carrier, but are NOT mutually orthogonal. For squarefree radicals d,e their Gram entry is

```text
<v_d,v_e>=mu(d)mu(e) 2^omega(gcd(d,e)),
v_d(g)=1_(g|d)mu(d/g).
```

In particular coprime radicals 2 and 3 have Gram entry +1. Genuine coefficients at R=10 give positive nonunit cross energy +24; at R=40 it is -56. The complete historical/future mixed contribution is also not sign-definite. Thus neither zero column totals nor coprime support justifies deleting the interactions.

| Claim | Classification and scope |
| --- | --- |
| 20261111-wheel-2/PD1 | PAPER_PROOF: exact historical/powerful split of every original gcd coefficient; sparse support, distinct quotient sites, rank and complete scalar conservation. Supporting representation, derived from accepted GD1 and existing rough/smooth inversion. |
| PD2 | PAPER_PROOF: uniform strict-history norm and complete large-gcd tail bound, with absolute convergent-product constants. New supporting quantitative restriction; no global Mertens power assumption. |
| PD3 | PAPER_PROOF: full radical Gram and quantified sparse inverse restriction; explicit mixed terms retained. No independent exclusion of its exceptional configuration. |
| PD4 | CONDITIONAL / TARGET-EQUIVALENCE AUDIT: precise historical-normalized consumer for the powerful response; the all-positive-loss family is still RH-strength, not an easier paid supplier. |
| PD5 | FINITE_COMPUTATION and narrowly REFUTED shortcuts: two different exact reconstructions; actual positive/negative cross terms; boundary and mask controls. |

All new PD paper arguments are SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. No literature-priority claim is made. **NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE.** The genuinely new payment is the whole historical vector and its large-gcd tail, not the small-gcd powerful response or the canonical endpoint.

### B. Current Authoritative Objective

Actual invocation: configured schedule, 2026-11-11 10:12:01 EST, America/New_York. Platform RUN_ID_UNAVAILABLE; PD is a research label. Main: `dda92f9ce59627b4c1f1317082f728648d330a0a`. AGENTS, contract and cross-route directive blobs are the unchanged hashes recorded in the verified checkpoint. The later AGENTS cross-route directive supersedes the contract's older single-wheel task selection, not its theorem types or safeguards. `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`; earlier finite-wheel, complete-HIGH and cancellation-chain acknowledgments remain subject to that priority override.

Canonical OPEN statement: one C>=0, chosen before every integer R>=2, bounds |pi(R^2)-VF_can(R^2)| by C R log R. Its terminal theorem still explicitly takes `ClassicalVonKochRHCriterion`. The separate internal Mertens-energy-to-RH consumer has an unpaid arithmetic premise. The complete centered wheel F_R-D_R=li(R^2-1)-pi(R^2-1) retains all virtual divisors until their exact Euler compensation. None of these quantities is renamed as the gcd norm below.

#### 1. BASELINE / DEPENDENCY RECEIPT

Directly inspected the current declaration and proof of

```text
RHLean.Analysis.native_mertens_near_uniform_window_error_closed
  : MertensGrowthAtMost(b_base),
b_base=7/8-7/(64*N_pack).

MertensGrowthAtMost(b):
  forall eps>0 exists C_eps>=0 forall integers n>=1,
  |M(n)|<=C_eps*n^(b+eps).
```

This is the strongest explicit fixed-family compiled comparator verified here, not a no-loss bound and not an optimization over all source geometries. Actual source definitions at the SAME positive fine length L give N_pack=ceil_nat(max(1,1/(6L)))+2 and N_old=ceil_nat(max(1,1/(3L)))+2. Hence N_pack<=N_old and 7/(64N_pack)>1/(48N_old); the counts are not identified.

Fresh #1119 check collection: 14/14 success at `77ee815846d6d534c866f0752aa33b84c385610a`. Read actual [proof/type/dependency log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700), endpoint, native Hecke-to-zeta/Mertens transfer, and live audit implementation. Five relevant closures of sizes 35358,35375,35736,35737,35753 end only in propext, Classical.choice, Quot.sound. The audit checks fixed-source construction/counts, native total-mass probe, anchored HIGH and complete Hecke comparison; the arithmetic roots additionally require the exact modulus-one L-product and native converse. Compared all 911 pre-existing relevant source/audit blobs at the tested head with current main: ZERO changed. This reuses scoped exact-head certification; it is not a fresh full-main Lean run, an independent reproving of every imported analytic lemma, or a claim that all historical upstream modules are placeholder-free. Unrelated historical Wiener warnings are outside the audited selected closures.

Verified log pins: Lean 4.34.1/compiler `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; openai/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. Preserve the existing pinned analytic assumptions and every positive exponent loss.

#1131 is now MERGED, at 2026-11-11T12:46:15Z, to the current main. Its exact tested head `f3f1da37c3e2fff9374eb5e99eca0da94c1efc29` has 13/13 successful checks. The actual [dedicated proof job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/43006238259/job/130474300634) reports six finite-response and eight mass/delay roots with only the standard axioms. Its complete finite expansion and order-independent coefficient mass do not yet constitute the all-delay same-signal Mellin return or improved global endpoint. The accepted PAPER IR/FFR boundary 7/8-1/2400000000 therefore remains distinct from b_base. No open/draft PR appeared in either the initial search or the subsequent recent-PR collection; merged #1115/#1122/#1124/#1126/#1127/#1128/#1129/#1130/#1131 were discovered and relevant scopes inspected.

### C. Structural Mechanism Investigated

Resume, not restart: GD1-GD4 have independent ACCEPT/PAPER_PROOF in today's Referee NP report. Coordinator 20261111-coordinator-0710-EST assigns Wheel the exact question of what a bad complete gcd norm forces BEFORE GD.13's three-Mertens-value triangle. Today's Census H_Z and yesterday's GC5 remain conjectures; neither is used.

Split GD's rectangles at the ACTUAL historical threshold T<R, without bounding their three terms together. Two entries are always historical. Only the third can lie beyond history. Its denominator d^2*h*k is powerful because h and k contain only primes dividing the squarefree d. Conversely every powerful denominator has one such radical d, and its remaining factor has exactly a(q) ordered splittings. Divisor inversion dictates its complete signed incidence column.

This uses genuine prime factorization. It does not posit independent future Mobius data: the original Q_R and all C_R(g) already depend only on mu(n), n<R. The displayed later Mertens values are DEPENDENT exact coordinates reconstructed by the existing Newton arithmetic. Computing them in a finite verifier is not admitting them as an independent supplier for an unknown bound.

### D. Exact Theorem Statements

Fix an integer R>=2, N=R-1, X=R^2-1. Define genuine M(0)=0, M(t)=sum_(1<=n<=t)mu(n), and retain the exact shifted envelope K_R=max_(0<=t<R)(M(t)-1)^2/(t+1). A physical floor occurrence is an ORDERED triple (a,b,k), 1<=a,b<R, k>=1, abk<=X, with weight mu(a)mu(b). Distinct triples with equal product are not identified.

```text
C_R(g)=sum_(a,b<=N, gcd(a,b)=g)mu(a)mu(b)floor(X/(ab)),
S_R(d)=sum_(a,b<=N, d|a,d|b)mu(a)mu(b)floor(X/(ab)),
D_G(R)=sum_(g=1..N)C_R(g)^2, Q_R=sum_g C_R(g).
```

For 1<=d<=N let B_d=floor(N/d), H_d={h<=B_d: every prime of h divides d}, A_h=floor(B_d/h), and T_dhk=floor(X/(d^2*h*k)). Units belong to H_d. Define

```text
U_R(d)=mu(d)^2 sum_(h,k in H_d)
       [M(A_h)+M(A_k)-1_(T_dhk<R) M(T_dhk)],
H_R(g)=sum_(k<=N/g)mu(k) U_R(gk).

P_N={q:1<=q<=N, each nonzero prime exponent in q is >=2},
d(q)=rad(q), a(q)=product_(p^e||q)(e-1),
v_d(g)=1_(g|d)mu(d/g), for squarefree d,
A_R(d)=sum_(q in P_N, d(q)=d) a(q) M(floor(X/q)),
E_R=sum_(q in P_N) a(q)M(floor(X/q))v_{d(q)}
   =sum_(d squarefree, d^2<=N) A_R(d)v_d.
```

The subscript d(q) selects a whole incidence vector. All sums are finite; q is an AUXILIARY denominator, not a prime-owner label or a new physical occurrence.

**PD1.** For every such R, the exact vector identity C_R=H_R-E_R holds. Moreover:

```text
sum_g H_R(g)=2M(N), sum_g E_R(g)=M(X),
sum_g v_d(g)=1_(d=1),
E_R(g)=0 for g^2>N,
#{q in P_N}<=3sqrt(N).
```

All quotient sites floor(X/q), q in P_N, are distinct and >R. As a linear map on FORMAL independent quotient coordinates, the response has rank #{squarefree d:d^2<=N}; this is not a statement that genuine arithmetic values can vary independently.

**PD2.** Put, for primes p,

```text
w(p)=(1-p^(-1/2))^(-2), W(n)=product_(p|n)w(p),
E0=product_p(1+(w(p)-1)/p),
E2=product_p(1+(w(p)^2-1)/p),
Y =product_p(1+w(p)^2/p^2), L_R=1+log N.
```

These are finite positive ABSOLUTE constants. Uniformly in R>=2 and 1<=g<=N,

```text
|H_R(g)|<=9 E0 R sqrt(K_R) L_R mu(g)^2 W(g)/g,
||H_R||_2<=C_H R sqrt(K_R)L_R, C_H=9 E0 sqrt(Y).       (PD.1)
```

For every real G>=max(1,sqrt(N)), the COMPLETE original high-gcd tail satisfies

```text
sum_(G<g<=N)C_R(g)^2
  <=162 E0^2 E2 R^2 K_R L_R^2/G.                     (PD.2)
```

No Mertens power, prime-distribution estimate, finite wheel independence, or conjectural norm contraction is assumed. The constants may be very large; no optimized numerical constant is claimed.

**PD3.** With all d,e squarefree and <=sqrt(N),

```text
||E_R||_2^2 = sum_(d,e) mu(d)mu(e)2^omega(gcd(d,e)) A_R(d)A_R(e),
D_G = ||H_R||_2^2 + ||E_R||_2^2 - 2<H_R,E_R>.       (PD.3)
```

Fix ANY real c>1/2, independently of R, and set

```text
Lambda_c=product_p(1+sqrt(2)*p^(-2c)/(1-p^(-c))^2)-1 >0,
B_H(R)=C_H R sqrt(K_R)L_R.
```

If sqrt(D_G(R))>B_H(R)+|M(X)|, then there is a powerful q with 4<=q<=N such that

```text
q^c |M(floor(X/q))|
 >= [sqrt(D_G(R))-B_H(R)-|M(X)|]/Lambda_c.            (PD.4)
```

The witness site lies in [R+1,floor(X/4)]. c is a freely chosen weight parameter, NOT an assumed exponent bound. This is a precise sparse inverse restriction, not proof that its conclusion is impossible.

**PD4.** For fixed 0<=eta<1/2, the open hypothesis

```text
exists B>=0 forall R>=2:
  ||E_R||_2<=B R^(1+eta)sqrt(K_R)                    (PD.OPEN)
```

would imply MertensGrowthAtMost(1/2+eta), using GD4 and PD.1 with the logarithmic loss properly charged. The family PD.OPEN for EVERY eta>0 is equivalent to MertensGrowthAtMost(1/2); no converse at the fixed zero-loss eta=0 is asserted. It is therefore not an independently easier RH supplier.

### E. Mathematical Proof

#### Exact Split And Multiplicity

Accepted GD1, independently rechecked here, gives

```text
S_R(d)=mu(d)^2 sum_(h,k in H_d)[M(A_h)+M(A_k)-M(T_dhk)],
C_R(g)=sum_(k<=N/g)mu(k)S_R(gk).
```

Its arithmetic input is mu(u)1_(gcd(u,d)=1)=sum_(h|u, h d-smooth)mu(u/h), the inverse form of the compiled rough-Mobius/smooth-indicator convolution. Reindexing both ordered historical indices preserves all floor multiplicities. The exact rectangular identity requires A_h,A_k<=T_dhk<(A_h+1)(A_k+1). Its strict upper wall follows from d(B_d+1)>=R and h(A_h+1),k(A_k+1)>=B_d+1. No equality corner is discarded.

For the third term, with positive integer q=d^2*h*k,

```text
T_dhk>=R iff q<=floor(X/R)=R-1=N.
```

In this range hk<=N/d^2<=B_d. Consequently EVERY factorization hk=t of an eligible t is admitted in H_d x H_d; no partial-divisor mask remains. If mu(d)^2=1, q=d^2*t has radical exactly d and each prime exponent at least two. Conversely a powerful q has the unique d=rad(q), t=q/d^2. The number of ordered (h,k) with hk=t is tau(t)=product_(p^e||q)(e-1)=a(q). This proves that the excluded third-term sum is exactly A_R(d), and divisor inversion gives C=H-E. If d is squareful, both common-divisor and reconstructed terms vanish, as genuine Mobius coefficients require.

For squarefree d, sum_(g|d)mu(d/g)=1 if d=1 and zero otherwise. At d=1, H_1={1}, U_R(1)=2M(N), A_R(1)=M(X). Summing the inverted vectors proves all scalar conservation statements, including the existing Q_R=2M(N)-M(X). This conservation does not discard the complete quadratic interactions.

Since d^2<=q<=N, every future column is supported on g<=d<=sqrt(N). Every powerful q has the unique form a^2*b^3 with squarefree b, by separating even exponents from odd exponents >=3. Thus #P_N<=sqrt(N)sum_(b>=1)b^(-3/2)<=3sqrt(N), using the elementary integral bound for the last series. If q<=N, floor(X/q)>=X/N=R+1. For consecutive positive q<=N, X/q-X/(q+1)=X/[q(q+1)]>1; hence all sampled floor quotients are distinct. The rank assertion follows by selecting q=d^2: the matrix v_d(g), over squarefree d,g<=sqrt(N) in increasing order, is triangular with diagonal one.

#### Historical Norm And Tail

K_R>=1 from its t=0 term. For 1<=t<R, its actual shifted definition gives

```text
|M(t)|<=1+sqrt(K_R(t+1))<=3sqrt(K_R*t).
```

All A_h,A_k are historical and <=T_dhk. The third term in U is admitted only when it is historical. Therefore, retaining its mask before taking absolute values,

```text
|U_R(d)|
 <=9sqrt(K_R) mu(d)^2 sum_(h,k in H_d)sqrt(T_dhk)
 <=9R sqrt(K_R) mu(d)^2 W(d)/d.                    (PD.5)
```

The second inequality uses sqrt(T)<=R/(d sqrt(hk)) and the exact finite-prime geometric majorant sum_(h d-smooth)h^(-1/2)=product_(p|d)(1-p^(-1/2))^(-1). It is valid for growing d. No global Z_(1/2) from GD2 is used; that divergent endpoint product must not be substituted here.

Define h(n)=0 off squarefree n, and h(n)=product_(p|n)(w(p)-1) otherwise. Then W(n)=sum_(d|n)h(d), h>=0, and sum_d h(d)/d=E0. Hence

```text
sum_(k<=N)W(k)/k
 =sum_(d<=N)h(d)/d sum_(j<=N/d)1/j
 <=E0(1+log N).
```

When U(gk) is nonzero, g,k are squarefree and coprime, so W(gk)=W(g)W(k). Apply (PD.5) to divisor inversion and the preceding finite harmonic bound to prove the pointwise PD2 estimate. Squaring and summing over squarefree g gives Y and proves PD.1.

For the tail, W(n)^2 has the identical nonnegative divisor expansion with local factors w(p)^2-1. Thus sum_(n<=t)W(n)^2<=E2*t. Partial summation, dropping only its nonpositive lower endpoint, yields sum_(n>G)W(n)^2/n^2<=2E2/G for G>=1. If G>=sqrt(N), E_R(g)=0 for every g>G, so C_R(g)=H_R(g) EXACTLY there. This proves PD.2 on the complete tail.

Convergence is elementary: w(p)=1+O(p^(-1/2)), so E0 and E2 have summable O(p^(-3/2)) local increments; Y has O(p^(-2)) increments. Small primes contribute finite fixed factors. Constants are selected before every scale. For an intentionally crude explicit check, w(p)<=12 and w(p)-1<=24/sqrt(p), giving E0<=exp(48), Y<=exp(144) and C_H<=9exp(120). This is not a fitted constant or an optimized estimate.

#### Complete Gram And Inverse Restriction

For squarefree d and g|d, mu(d/g)=mu(d)mu(g). Hence the column inner product is mu(d)mu(e) times the number of common divisors, namely 2^omega(gcd(d,e)). Expanding E and then C=H-E proves PD.3 with both orientations and the entire mixed term.

Remove the unit mode: F_R=E_R-M(X)v_1. Its sum is zero, not its norm. Since ||v_d||_2=2^(omega(d)/2), triangle gives

```text
||F_R||_2
 <=max_(q in P_N,q>1)[q^c|M(floor(X/q))|]
    *sum_(q in P_N,q>1)a(q)2^(omega(rad q)/2)/q^c
 <=Lambda_c max_(q in P_N,q>1)[q^c|M(floor(X/q))|].
```

The infinite positive sum factors with local series sqrt(2)sum_(e>=2)(e-1)p^(-ec)=sqrt(2)p^(-2c)/(1-p^(-c))^2. It converges for c>1/2 without assuming anything about M. Meanwhile ||F||>=||C||-||H||-|M(X)|. If the numerator is positive, F is nonzero and the finite maximizing set is nonempty; R>=5 automatically. This proves PD.4. No sign alignment, independent samples, or favorable Gram sign is inferred from the weighted maximum.

#### Consumer And No-Circularity

If eta>0 in PD.OPEN, absorb L_R into an absolute eta-dependent multiple of R^eta. Then ||C||<=||H||+||E|| gives GD's N_eta: D_G<=B'_eta R^(2+2eta)K_R. Its already accepted GD4 consumer gives MertensGrowthAtMost(1/2+eta). At eta=0 the same argument gives N_delta for each delta>0, NOT a finite zero-loss constant; choosing smaller positive losses yields MertensGrowthAtMost(1/2).

Conversely assume MertensGrowthAtMost(1/2). GD2-GD3 give ||C_R||<=B_eta R^(1+eta) for every eta>0. PD.1 and K_R>=1 then imply PD.OPEN for every eta>0, with logarithms absorbed and constants chosen before R. Thus the family is exactly RH-strength at the exponent level. The reverse implication uses an assumed growth theorem only in this explicit target-equivalence audit, never in PD1-PD3.

This is not a new self-improving recurrence: applying the certified Mertens baseline to the sampled values gives at best its existing power. In particular the q=1 coefficient is M(X) itself. Labeling it a future response cannot pay the original endpoint.

### F. Structural Consequence

The full gcd vector has a rigorous historical approximation with an R sqrt(K_R) log R norm bound. Its uncharged part is confined to at most sqrt(R-1) gcd coordinates and at most 3sqrt(R-1) powerful quotient sites; the other original coefficients are exactly historical. For G=sqrt(R-1), PD.2 pays the complete high-gcd energy by O(R^(3/2)K_R log^2 R), with absolute constants. This is stronger structural localization than an arbitrary sign-vector or degree-bound model.

It does NOT assert independent small-gcd coordinates, a favorable sign of C_R(g), a small total future response, or successful descent. All nonunit future columns have zero scalar total, yet their Gram can reinforce. There is therefore a precise difference between exact linear cancellation and quadratic norm control on this actual arithmetic source.

### G. Signed And Quantitative Relevance

The original scalar square is still Q_R^2=D_G(R)+2sum_(g<h)C_R(g)C_R(h). D_G is the COMPLETE diagonal of this gcd grouping, not the complete square Q_R^2, not an unsigned count, and not the canonical VF energy. PD.3 expands D_G without losing H/E terms; it does not erase the remaining inter-gcd term. The consumer is specifically GD4, whose proved head/tail iteration does NOT assume GC5 or a favorable sign of that remaining term.

#### 2. FOUR-WAY SOURCE MAP

| Source field | Euler / finite AC | VF / actual primes | NNS / OAI | Square blocks / native HIGH |
| --- | --- | --- | --- | --- |
| Literal carrier | Ordered mu(a)mu(b) floor occurrences, a,b<R, abk<=X_R; Q_R and complete gcd vector | Complete fractional wheel on all divisors of primorial(R-1), centered at li(X_R); #915 is a separate clipped weighted carrier | Original ideal-labelled compensated LOW polynomial, Hecke weights, source masks and principal normalizer | Full M(X_R), not one shell or sum of shell squares |
| Typed connection | EXACT_IDENTITY: PD1 reconstructs each C_R(g); compiled Euler endpoint reconstructs Q_R | NOT_EQUIVALENT to Q_R; #1122/#1124 retain virtual compensation. Prime/Mobius meeting point is a cofactor-weighted Buchstab coupling, not equality of errors | ONE_WAY global Mertens consequence through the native zeta bridge; OPEN_BRIDGE for literal coefficient transport from PD to original LOW | EXACT_IDENTITY: sum C_R=2M(R-1)-M(X_R), both historical and current boundary terms retained |
| Scales and weights | X_R=R^2-1, strict K_R, auxiliary powerful q<=R-1, exact a(q) and v_rad(q) | Original prime ownership, original seat weights, admission and clipping; target R log R | Source Z, ideal norm, height, character and frozen pools; none identified with q or gcd | All-prefix growth needs the established square-to-prefix interpolation and positive-loss quantifiers |
| Unpaid return | Small-gcd powerful norm and every H/E interaction | Full prime discrepancy and actual first-bad payment remain OPEN | New merged mass theorem is not a same-signal Mellin return; generic real/complex Gram isometry is not cancellation | PD.OPEN would feed GD4; it is not established here |

**Literal CORR4 overlap, with a barrier.** For each odd prime p with p^2<R, the single q=p^2 term has a(q)=1 and amplitude M(floor(X_R/p^2)), the exact raw daughter `lowOwnerRawMertensAmplitude R p` with `rawQ2ChildCutoff R p=X_R/(p*p)`. Its PD column is v_p=-e_1+e_p. This is an amplitude-level exact bridge, not an identification of the weighted critical CORR4 synthesis. PD also has prime 2, powers p^e with e>=3 weighted by e-1, every multi-prime powerful denominator, the endpoint and the complete historical mixed term. CORR4's own near/high, intermediate towers, Go-wall, owner-two, terminal and root corrections remain intact; a negative daughter credit cannot be spent on the PD source a second time. Prior JC's complete upper-band obligations are unchanged. This is a FINITE-AC/MU-LIFT continuation with a concrete CORR4 crosswalk, not retirement of any protected route.

#### 3. FIRST SIGNED LOSS

| Step | Exact signed input and discarded interaction | Cost and consumer | Payment / unresolved bill |
| --- | --- | --- | --- |
| Existing GD.13 | Three Mertens entries and all smooth labels bounded together | Earlier bound imports a global power c and preserves that same exponent | PD splits at T<R first, so the whole historical part is paid from actual K_R alone |
| PD.5 and divisor inversion | Signs within historical U_R and across mu(k) are discarded | 9, E0, sqrt(Y) and L_R; gives C_H R sqrt(K_R)L_R | Paid uniformly by PD2; no lost historical/future cross is declared negative |
| C=H-E to triangle | -2<H,E> | Norm sum, or squared factor at most 2; no exponent benefit at the unpaid E scale | Mixed term retained exactly in PD.3 and tests; sign changes already occur at R=2,3 |
| Powerful columns to diagonal-only | All d!=e terms mu(d)mu(e)2^omega(gcd(d,e))A_dA_e | Would be an unsupported saving | REFUTED even for the full nonunit arithmetic response: +24 at R=10 |
| PD.4 inverse | Weighted triangle over all nonunit powerful q | Finite Lambda_c; no new exponent | Locates a witness but does not exclude it; c>1/2 cannot be silently set to 1/2 |
| OAI LOW `norm_sum_le` / CORR4 mixed-tail gate | Different ideal-profile Gram / physical owner mixed bill | Their actual complete-return costs | NOT paid by PD; source transfer is open beyond the explicit raw-daughter overlap |

#### 4. PAID RECOVERY TEST

Compiled finite-wheel rough/smooth convolution plus the exact signed hyperbola/Newton support supplies GD1's genuine arithmetic bridge, then PD's exact coefficients. It is not a new cancellation assumption. The existing complete reciprocal-band telescope #1115 controls a contiguous complete band; it does not remove the simultaneous radical restrictions or the powerful weights. #1127's positive erased-unit fractional cofactor fibre has q in [R,2R), different coefficients and a different carrier; its positivity does not apply to C, A or their Gram. #1128's actual shared-prime near-resonance is a proper-source obstruction, not a bound on PD. Its warning against phase-independence is consistent with PD's nonzero coprime Gram.

The compiled CORR4 raw amplitude supplies the exact p^2 overlap above, but no theorem inspected controls the FULL PD response with the required weights. The OAI baseline can be substituted only at the output Mertens-growth level and buys no second gain. The complete source bound and the inverse exclusion therefore remain unpaid.

#### 5. NET RESULT / ADMISSION VERDICT

New supporting all-scale payment: PD.1-PD.2, from strict history alone. New exact complete-source organization and inverse: PD1/PD3. No independent exclusion of the PD.4 witness; no proof of PD.OPEN. The admission test for a new accepted RH route is NOT met. Smaller source support and an independently paid complement are useful, but no numerical global exponent changes and no substantial full-source contraction is claimed.

### H. Falsification, Novelty And Reproducibility

Checkpoint commit `6a0491c163ee24de79b13f9e9606ea2c5dffe784`, blob `19251f1328a22ec4bf79da6a82dbb0e73fba89d6`, was re-fetched exactly before the registered programs ran. It preserved every earlier same-day byte. This is a changed-source test, not an extension of GC5/H_Z or wheel-density scans.

Primary C++20 with -O2 -Wall -Wextra -Werror: every R=2..100 and held-outs 127,256,549,5561. A direct genuine Mobius sieve through 30,924,720 and literal ordered-pair gcd sum were compared with the historical rectangles and independently regrouped powerful terms. **103 roots; 11,689,857 nonzero ordered coefficient pairs; 39,223 rectangles; 11,439 complete coefficients; 2,254 future rectangle labels; 1,094 powerful columns; 5,154 Gram entries; 10,701 high-gcd historical coefficients. Zero mismatches.** Pair counts are not expanded floor-triple counts; all floor multiplicities remain in the sums.

The second program uses trial factorization and the quotient-block Mertens recurrence, not the primary sieve. It checks R=2..60 and the same four held-outs: 63 roots, 611 columns, 63 rational finite inverse bounds, and 1,770 rational historical majorants. It computes the literal pair vector independently through R=549; at R=5561 its independently reconstructed full vector/norm is checked against the primary direct result. Four exact negative controls pass. Syntax checking also passed. These are algorithmically different SELF_CHECKS, not independent specialist acceptance or Lean proofs.

| R | D_G | H squared norm | E squared norm | -2<H,E> | Nonunit cross |
| --- | ---: | ---: | ---: | ---: | ---: |
| 10 | 523 | 166 | 121 | 236 | 24 |
| 15 | 223 | 156 | 101 | -34 | 16 |
| 17 | 173 | 618 | 201 | -646 | 88 |
| 40 | 8785 | 14220 | 855 | -6290 | -56 |
| 56 | 12810 | 21016 | 1332 | -9538 | 270 |
| 549 | 213476 | 305112 | 70326 | -161962 | -14846 |
| 5561 | 19073482 | 31666626 | 7169554 | -19762698 | -692306 |

Here nonunit cross means ||sum_(d>1)A_d v_d||^2-sum_(d>1)2^omega(d)A_d^2; no q=1 or H mixed interaction is hidden in it. The known D_G and Q values are regression data, not new sign discoveries.

At R=10, (A_1,A_2,A_3)=(1,-6,-2); E=(9,-6,-2,0,...), and the nonunit vector is (8,-6,-2,0,...). Its energy is 104 while its radical diagonal is 80, producing +24. At R=40, (A_1,A_2,A_3,A_5,A_6)=(-7,-24,-5,-1,-3); nonunit energy 1184 versus diagonal 1240 gives -56. Thus the asserted uniformly nonpositive nonunit cross shortcut is decisively false. This does NOT refute GC5 or H_Z, which involve different complete expressions.

Strict-wall control: (A,B,T)=(1,1,4) has literal rectangular sum 4 but M(1)+M(1)-M(4)=3; the equality corner contributes +1. Mask control: v_2=(-1,+1,0,...), total zero, but projecting onto g=1 gives -1. This auxiliary clipping witness does not assert admission into #915; Owner MC supplies separate genuine-mask warnings. The proposed coprime-orthogonality shortcut is refuted by <v_2,v_3>=1; <v_2,v_6>=-2 also records the opposite sign.

Novelty search: current main code searches for powerful, squarefull, gcd/smooth/Mertens and radical/Mertens; the full retrieved two-date role reports were searched for the proposed denominator/support/column formulation. Inspected original Euler, Newton/hyperbola, restricted-floor, complete reciprocal-band, wheel and CORR4 sources and typed atlas. No matching complete historical/powerful gcd split plus strict-history norm bound was found. Existing OAI powerful ideal parts are a different carrier. This finite repository search does not establish literature priority or universal absence. The standard smooth convolution, divisor inversion, elementary powerful-integer count, Gram expansion and Euler-product convergence are explicitly credited tools; the claimed new combination is PD1-PD2's literal source and scope.

### I. Conceptual Interpretation

A large gcd norm cannot be blamed on many independent high-gcd classes: their entire contribution is already an explicit strict-history quantity. New growth must survive in a small common-prime response space whose columns are forced by prime-exponent multiplicities. But their zero totals hide, rather than eliminate, quadratic interactions. The q=1 endpoint and proper powerful descendants cannot be replaced by unsigned counts or treated as separate historical supplies.

### J. Competing Structural Hypotheses

Retain one main question: can the actual coupled powerful responses A_R(d), with the unit endpoint and H cross term, obey a new signed inequality unavailable to arbitrary columns? PD.4 narrows its possible witnesses but provides no exclusion. Retire coprime orthogonality and uniformly favorable nonunit-cross arguments at the precise refuted scope. Do not replace them with a statement equivalent to PD.OPEN and assume it true. A valid alternative may control C jointly without bounding E separately; PD.OPEN is a sufficient route, not a compulsory stronger component norm. Preserve the independently active CORR4 and MU-LIFT complete-return programs.

### K. Specialist Handoffs

**Coordinator:** PD2 pays the complete historical vector and g>sqrt(R-1) tail without a global Mertens input. Record it as supporting paper progress, not admission test 2 completion. PD1 exposes exactly where GD's loss lives; PD4 keeps the desired norm's RH-strength status explicit. The accepted OAI paper endpoint still needs its own formal return.

**Referee:** independently check the T>=R iff d^2hk<=R-1 cutoff, ordered tau(t) multiplicity, all quotient sites >R, growing-radical Euler products, the PD.2 tail, and the eta=0 logarithmic consumer. Review rank only on the formal coordinate space. First controls are equality wall (1,1,4), R=10, and the missing <v_2,v_3> term. No independent ACCEPT is claimed by this author.

**Analytic:** test whether an already-proved signed input controls the complete radical Gram BEFORE its weighted maximum, with H and unit mode retained. A Nyman or Hecke Gram has a different coefficient map; no transfer is supplied by a shared name. Today's DM E(1+V)>=1/768000 is read and remains a separate original-Nyman necessary restriction pending review, not a PD bound.

**Owner:** for q=p^2 the raw daughter amplitude matches exactly, but all higher powers, mixed radicals, prime 2 and H cross terms remain. Check any proposed physical owner map at occurrence and coefficient level; do not reuse FA's proper-source positive historical composites as negative credit or commute an actual current mask through divisor completion.

**Census:** the next useful test needs a NEW inequality on the complete A/H Gram, with constants and a null fixed before testing. Reuse these exact PD rows and earlier GC/DZ controls. Do not enlarge unchanged GC5/H_Z scans or claim that sparse support forces cancellation.

**Lean Verification:** no immediate duplicate identity PR is requested. Subject to independent review and strategic priority, PD1 plus PD2 form one coherent supplier: literal common-divisor split, powerful multiplicity, exact inversion, then absolute historical bound. Reuse compiled restricted-floor/Newton infrastructure. The accepted same-signal OAI return remains the more direct implementation queue; PD4's open estimate must never be an axiom or hidden premise.

### L. First Independently Missing Theorem

The precise arithmetic gap is a new original-coefficient restriction on

```text
||H_R - sum_(d squarefree,d^2<R) A_R(d)v_d||_2,
```

stronger than substituting the known Mertens power, with all constants chosen before R. One sufficient version is PD.OPEN for some fixed eta<b_base-1/2, followed by GD4; it is not claimed weaker or independently paid. Another is a joint H/E inequality that avoids the stronger component norm. A proof of sign coherence alone would still leave magnitude unbounded. No presently inspected theorem independently excludes PD.4's actual powerful witness.

### M. Next-Run Resume Capsule

Resume from PD1-PD3, not fresh wheel counts or the already accepted GD equivalence. Main `dda92f9ce59627b4c1f1317082f728648d330a0a`; checkpoint `6a0491c163ee24de79b13f9e9606ea2c5dffe784`. GD1-GD4 are now independently ACCEPTED_ON_PAPER; PD claims are SELF_AUDIT / REVIEW_PENDING / NOT_FORMALIZED. #1131 merged; global b_base unchanged. Canonical VF, finite A/C, complete wheel bound, original #915 payment and RH remain OPEN.

Highest-value next question: can the forced radical Gram, not mere denominator sparsity, exclude a large complete small-gcd mode using genuinely new arithmetic? First falsifier R=10; complete H/E cross retained. Formal data rank is not independence of actual M values. The all-positive-loss powerful-norm family is RH-strength. No new accepted route or VERIFIED_ETA.

Execution limitations: direct git fetch was unavailable (CONNECT tunnel 403); authoritative reads and publication used the configured GitHub connector. No local Lean ran. No main/source/other-report edits, proof branches, PRs, workflow launches, merges, agent launches, schedule changes or permission changes occurred. All arithmetic programs finished. Publication status is governed by immutable readback after this synthesis, not by this preparation text.


### Source And Continuity Ledger - PD

Final authority/status refresh: **2026-11-11 15:35:55 UTC / 10:35:55 EST**. Main remains `dda92f9ce59627b4c1f1317082f728648d330a0a`; agent-reports remains this run's verified checkpoint `6a0491c163ee24de79b13f9e9606ea2c5dffe784`. The open-PR collection is EMPTY, including drafts. All six other November 11 role blobs and both Coordinator mirrors are unchanged from intake. Therefore no newer report or main-source change appeared during this derivation. This is observed execution evidence, not an inference from schedules.

Both November 11 and November 10 were read using the America/New_York calendar. **TODAY=AVAILABLE for all seven roles; YESTERDAY=CARRY_FORWARD** for the verified predecessor derivations. A timestamp in the table is the author's recorded publication verification, not a claim that this run repeated the entire author's experiment. Full report bytes and the relevant review arguments were retrieved; the new PD arithmetic is independently reconstructed by the two algorithms below, but both remain this author's SELF_AUDIT.

| Date / role | Retrieved full-report blob | Original claims consumed; current scope | Recorded verification / substantive commit |
| --- | --- | --- | --- |
| Nov 11 Coordinator | `106f6d88708a7545caab43c56ae1bbb915fd97f2` | `20261111-coordinator-0710-EST`, M2 asks for pre-GD.13 inverse structure; FL1-FL5 remain paper/self-audit; NP1-NP3 independently accepted ON PAPER by Coordinator. | 12:46:58 UTC; `211dbc59d025d39cb72705f9eb9b450ee453b5db` |
| Nov 11 Owner | `accf2930372234b58e98e8e43e88aeb845b56e9b` | `20261111-owner-1/MC`: actual-mask commutator, r=10,p=3,b=101/115 opposite signs. `20261111-owner-2/FA`: historical composite ancestor support, E_r<=2r and proper-source positive cost <=36r/log^2(r); not full marked payment. Independent FA review pending. | 08:36:30 EST; `b3d5d8dcf49a22ec1e98448c192e14a26a35e978` |
| Nov 11 Analytic | `0309d49557af30da43a07d72dce93c93c1811157` | `20261111-analytic-1/NT` accepted ON PAPER by Referee NP; `20261111-analytic-2/DM1-DM4` full Nyman error/variance E(1+V)>=1/768000, self-audit pending review. DM5 is 49359 finite checks, not density. | 14:37:30 UTC; `a77c077555a80b5726dc18762c68c084d237778b` |
| Nov 11 Wheel, earlier run | `dbf68d8f8b1737b4b585811dae014329614ec595` | `20261111-wheel-1/GD1-GD4` independently ACCEPTED_ON_PAPER by Referee NP, superseding this earlier report's review-pending wording. GD5 remains finite. | 07:36:36 UTC; `a32bc3548eeb0daa7bd616380309f244bd71f78b` |
| Nov 11 Census | `49c1c48f672cf96c93909bd2b412d95bb3587d62` | `20261111-census-1/DZ`: H_Z remains a conjecture after 331 eligible roots. R=7 divisor weighting increases cross by +10, independently reproduced by Referee; no favorable-cross explanation. | 08:45:21 UTC; `8734c6b725119f549f8905cfb6f8d186ea2d981f` |
| Nov 11 Referee | `214e99d8d6133e720f9645dd650a57b01a8c05cf` | `20261111-referee-1/NP` ACCEPTS GD1-GD4, NT1-NT3 and FFR1-FFR4 at PAPER scopes. NP1-NP3 now separately accepted by Coordinator. No review of PD has yet occurred. | 09:39:40 UTC; `699de1abd45c69c0b4b579e30ca0bff686d13337` |
| Nov 11 Lean | `c86b058b6387de7348b123b22b8f5b8772d5ae9a` | `20261111-lean-1/FFR-MASS/LABEL/DELAY/LIMIT`: compiled finite supplier, same exact head checked here. Its historical UNMERGED status is superseded by verified human merge #1131 at 12:46:15 UTC, not by inference. | 10:55:01 UTC; `1f7a42287e913198c823049fcde303e5e75a8354` |
| Nov 10 Coordinator | `4d55b2893f974656c6aa14e48b243827fa8308f8` | `20261110-coordinator-2309-EST/FFR1-FFR4`: now independently accepted ON PAPER by Referee NP; same IR boundary, not an additional improvement. | Nov 11 04:36:23 UTC, Nov 10 NY date; `ce6a9344d7f86add41d7defd2a645e31bb8ae70d` |
| Nov 10 Owner | `84afec90414b2394a61b51df46c07b6b540e5942` | `20261110-owner-3/DR`: coherent same-integer reinforcement at R=6,n=30, q=78 repair fails at R=16; proper complete defect bound not original full payment. | 16:43:55 EST; `a565c31085995987d38f2e46b6d6224fe21e18eb` |
| Nov 10 Analytic | `7ed3a39bec4796f4173b692064af872ea8035048` | `20261110-analytic-3/IR1-IR4`: full response and b_IR independently accepted ON PAPER by Referee IRR, endpoint not compiled. | 22:38:54 UTC; `494509e00315ca7616ce235594ea098d14fc52dc` |
| Nov 10 Wheel | `62406503a1ddbbf9330abcdc4cf761f7fbf05795` | `20261110-wheel-3/RC1-RC5`: complete reciprocal radical identity and auxiliary logarithmic bound. `20261110-wheel-2/JC`: CORR4 upper eight bands and full mixed costs retained. No arbitrary-mask commutation. | 23:34:46 UTC; `4769b57101fbc0821dbc43110e837b05b7442302` |
| Nov 10 Census | `a3cfa56072f3893dbf92a18956e1794236bde057` | `20261110-census-2/GC`: C_15(2)=-6; coarse coprime/shared opposition false at R=17,549. GC5 remains CONJECTURE, not used in PD. | Nov 11 00:19:48 UTC, Nov 10 NY date; `d48d9ca10f0afdddef44c39c992b6aad0fec055e` |
| Nov 10 Referee | `6529562a5bb21fa192fddadaa91a758b9d125c29` | `20261110-referee-3/IRR`: MD/IR ACCEPTED_ON_PAPER; GC5 finite reproduction through R=2000 is not proof. Coherent critical response obstruction remains model-scoped. | 20:37 EST; `ce3f4087703d1ea869af4564481110d6ff62d8d5` |
| Nov 10 Lean | `682b334b8f37fa4bfe2d552a1142d852a0db2afd` | `20261110-lean-3/MD`: earlier #1131 finite product approximation; superseded implementation head checked, old result preserved. | Latest receipt has no explicit timestamp; `55f669489a46b1660b5fc85dfbc774f714c8639a` |

External inbox: `research/agent_reports/EXTERNAL_HANDOFFS.md`, blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, retrieved from agent-reports. Newest entries remain October 18. `EXT-20261018-PNT-1` retains the exact cofactor-weighted Mertens/prime coupling, not an independent small signed response. `EXT-20261014-5` concerns an unconditional all-R denominator claim, not every conditional first-bad strategy. No new external paper or unverified literature theorem is used in PD.

The following are actual main file blobs at the pinned source commit, not report paraphrases. The main tree and fetched source contents are the authority for the definitions and dependency comparisons.

| Main path | Blob SHA | Inspected role |
| --- | --- | --- |
| `AGENTS.md` | `c9c89f01b90b526de9f3e8ea92478e36504711b6` | Priority, own-report-only permission and proof integrity |
| `CURRENT_PROOF_CONTRACT.md` | `95566e37c8eaeb99ee680660df4f9d2e06ea5038` | Canonical theorem and open premises |
| `docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md` | `e922d4ba9362a1ae196af8f6de88f7417f92087c` | Five-stage governing directive |
| `docs/DYNAMIC_RESEARCH_AGENTS.md` | `0f0b63a82380e18068ab7f3c317feafd66939290` | Continuity and publication safeguards |
| `docs/COORDINATE_ATLAS.md` | `cd0419d00a37739fe5a292f5cb738e33213949d5` | Typed source bridges and barriers |
| `research/EULER_FRACTIONAL_COUPLED_20261027.lean` | `e6c4b1690e497760d366e36b28a1f7aa60e19f85` | Original Euler bilinear floor source |
| `research/EULER_SELF_DUAL_POINTWISE_20261027.lean` | `c327c556f39ee7014fd774b24d0f95a1ece050e0` | Endpoint reconstruction and exact carriers |
| `research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean` | `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73` | Conditional source consumer |
| `RHLean/Analysis/FiniteWheelRestrictedFloor.lean` | `94c4d4420fc58cd87d92780c6265decd2cad7e66` | Rough/smooth Mobius convolution supplier |
| `research/MERTENS_SIGNED_HYPERBOLA.lean` | `d199571f19346797229a25b0fa53c6e80499999f` | Exact signed rectangular support |
| `research/oai_434/VF919WindowErrorClosure.lean` | `f629db1b2b65d6ec042ac9432397d4b6316200c6` | Current compiled global endpoint |
| `research/oai_434/VF919NativeStrictMertens.lean` | `b33a4883e1ddb0551b0f11f062bce46680d87450` | Native arithmetic transfer |
| `scripts/lean/window_error_closure/WindowErrorClosureAudit.lean` | `1f17f9401a63d16227db2e2aad020b9f74bc5f4e` | Selected live dependency roots |
| `research/oai_434/VF919ExplicitSquareBlockPacking.lean` | `32999039fdeea99c58a070c1c4ee9c140720dd44` | Actual packed fixed-source count |
| `research/oai_434/VF919ExplicitFixedSourceSlotCount.lean` | `bad5aab0a60e96d19e7c9550cd7c0a072288bc0f` | Older count at the same fine length |
| `RHLean/Analysis/MertensPowerGrowth.lean` | `ae855e8212fa8f12bc225a4d60af004ebd002f7d` | Every-positive-loss growth quantifiers |
| `research/MERTENS_EXPONENT_ENVELOPES.lean` | `655b896e8d5a41c9f8fc3c456eae3944a98bfefe` | Native historical envelope |
| `research/FiniteWheelCofactorPositivity.lean` | `f83a3daefc2b9d603014af912ec82b4a7f52cfac` | Proper-source positivity, not PD Gram |
| `research/DyadicPrimeNearResonance.lean` | `f416e0149b73656e30a7f68a3934a937353d3f8d` | Shared-prime resonance scope |
| `research/CompleteSquareRootWheelFractionalBoundary.lean` | `ecb482e52deeee5e9b3853592a3ffdace662d2ff` | Full virtual-wheel compensation |
| `research/CompleteWheelRootAdmission.lean` | `a412632c1028d7728cd8d87ee6e5ac365377d338` | Genuine root admission |
| `research/TWOAB_RENEWAL_COMPLETE_BAND_20261108.lean` | `028d9f2bbfa1a8de1fe63e9bd368aca13aae6825` | Complete reciprocal band supplier |
| `research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean` | `bb0ee1252e7ba10c44ae5b8d827573d6c581b73a` | Complete CORR4 mixed-tail bill |
| `research/LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT.lean` | `72d66f61b3eeb000117ecdac393572558bb7c378` | Literal p-squared raw daughter amplitude |
| `RHLean/Proof/SignedTransportAmplificationAudit.lean` | `746f35f126f36e024d39e38c92dde30aabca266b` | Raw squared-child cutoff |
| `research/oai_434/VF919OriginalLowTupleSignedGram.lean` | `dd2fde01ae6e2446da4e69b30f6fc80fcadb858d` | Different ideal-labelled signed Gram |
| `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean` | `79030d70e8d3e0d08eef9bac53fef95c36eca2fb` | Explicit classical criterion in canonical consumer |

The fresh main tree additionally places the exact tested #1131 modules `research/oai_434/VF919PrincipalFiniteResponse.lean` at `8c7f21b34402758b18ce42f4484f518c4090c105` and `research/oai_434/VF919PrincipalResponseMass.lean` at `5f7e812108ff7eff4a60da7055c2dd5f852c4941`. The dedicated job inspected directly reports finite-response root closure sizes 618,647,660,730,735,197 and mass/delay closure sizes 422,533,182,841,230,223,101,85. Its exact theorem/standard-axiom checks certify these scopes; the complete Mellin endpoint is not among them.

### Reproducible Exact Arithmetic - PD

The following programs and outputs are the executed bytes, not pseudocode. Standard C++20 and Python standard library only. The independent program uses rational finite majorants: its inverse check replaces sqrt(tau(rad(q))) by tau(rad(q)) and uses the finite c=1 sum; its history check uses rational upper bounds for w(p). These finite checks supplement the all-scale paper proofs and do not numerically approximate the infinite Euler products.

Reproduction commands after extracting the code blocks under the displayed filenames:

```sh
g++ -O2 -std=c++20 -Wall -Wextra -Werror pd_check.cpp -o pd_check
./pd_check
python -m py_compile pd_independent.py
python pd_independent.py
```

| Executed artifact | SHA-256 |
| --- | --- |
| `pd_check.cpp` | `01c561e016c1f27518e2661d15ee0fe62e35f3363c7951b799ce16fa3cff7f79` |
| `pd_check.out` | `7cc53e8ffba751e1ba7d7c1a6106a9de0483d626a56ede467ca141d9f48a0910` |
| `pd_independent.py` | `3c40406ac6c895f6f91bcc1e7759cc880fec2bfc8059bdbcb7ece4af7a6d6b92` |
| `pd_independent.out` | `a04b5a7a0e7cd08ec4fe37d102ae70eb3b9cd344c85592b81a2e2d91be93e7e6` |


#### Executed pd_check.cpp

```cpp
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using i64 = std::int64_t;

std::vector<int> prime_factors(int n) {
    std::vector<int> out;
    for (int p = 2; p * p <= n; ++p) {
        if (n % p != 0) continue;
        out.push_back(p);
        while (n % p == 0) n /= p;
    }
    if (n > 1) out.push_back(n);
    return out;
}

std::vector<int> smooth(int d, int bound) {
    std::vector<int> out{1};
    for (int p : prime_factors(d)) {
        const auto old = out;
        for (int h : old)
            for (i64 t = static_cast<i64>(h) * p; t <= bound; t *= p)
                out.push_back(static_cast<int>(t));
    }
    std::sort(out.begin(), out.end());
    return out;
}

int main() {
    std::vector<int> roots;
    for (int r = 2; r <= 100; ++r) roots.push_back(r);
    for (int r : {127, 256, 549, 5561}) roots.push_back(r);
    const int limit = roots.back() * roots.back() - 1;
    std::vector<std::int8_t> mu(limit + 1, 1);
    std::vector<bool> prime(limit + 1, true);
    mu[0] = 0;
    for (int p = 2; p <= limit; ++p) {
        if (!prime[p]) continue;
        for (int n = p; n <= limit; n += p) {
            mu[n] = -mu[n];
            if (n > p) prime[n] = false;
        }
        const i64 square = static_cast<i64>(p) * p;
        if (square <= limit)
            for (i64 n = square; n <= limit; n += square) mu[n] = 0;
    }
    std::vector<int> m(limit + 1);
    for (int n = 1; n <= limit; ++n) m[n] = m[n - 1] + mu[n];

    i64 pairs = 0, rectangles = 0, coefficients = 0, gram_checks = 0;
    i64 future_labels = 0, column_checks = 0, history_tail_groups = 0;
    int first_positive_cross = 0, first_negative_cross = 0;
    int first_positive_mixed = 0, first_negative_mixed = 0;
    std::cout << "R,Q,D_G,H2,E2,mixed,nonunit_cross,powerful_count,radical_count,K_num,K_den\n";
    for (int r : roots) {
        const int n = r - 1;
        const i64 x = static_cast<i64>(r) * r - 1;
        std::vector<i64> c(r), s(r), hc(r), ec(r), h(r), e(r), a(r);
        for (int u = 1; u < r; ++u) {
            if (!mu[u]) continue;
            for (int v = u; v < r; ++v) {
                if (!mu[v]) continue;
                const int multiplicity = u == v ? 1 : 2;
                c[std::gcd(u, v)] += multiplicity * mu[u] * mu[v] * (x / (u * v));
                pairs += multiplicity;
            }
        }
        for (int d = 1; d < r; ++d) {
            for (int g = d; g < r; g += d) s[d] += c[g];
            if (!mu[d]) { assert(s[d] == 0); continue; }
            const int b = n / d;
            const auto hs = smooth(d, b);
            for (int u : hs) for (int v : hs) {
                const int aa = b / u, bb = b / v;
                const i64 q = static_cast<i64>(d) * d * u * v;
                const int t = static_cast<int>(x / q);
                assert(aa <= t && bb <= t && t < (aa + 1) * (bb + 1));
                hc[d] += m[aa] + m[bb];
                if (t < r) hc[d] -= m[t];
                else {
                    ec[d] += m[t];
                    assert(q <= n && t > r);
                    ++future_labels;
                }
                assert((t >= r) == (q <= n));
                ++rectangles;
            }
            assert(s[d] == hc[d] - ec[d]);
        }
        int powerful_count = 0;
        for (int q = 1; q <= n; ++q) {
            int rest = q, rad = 1, weight = 1;
            for (int p = 2; p * p <= rest; ++p) {
                if (rest % p != 0) continue;
                int exponent = 0;
                while (rest % p == 0) { rest /= p; ++exponent; }
                rad *= p;
                weight *= exponent - 1;
            }
            if (rest > 1) { rad *= rest; weight = 0; }
            if (!weight) continue;
            ++powerful_count;
            a[rad] += weight * m[x / q];
            assert(static_cast<i64>(rad) * rad <= q);
            i64 col_sum = 0, col_norm = 0;
            for (int g = 1; g <= rad; ++g) if (rad % g == 0) {
                const int z = mu[rad / g];
                e[g] += static_cast<i64>(weight) * z * m[x / q];
                col_sum += z;
                col_norm += z * z;
            }
            assert(col_sum == (q == 1 ? 1 : 0));
            assert(col_norm == (1LL << prime_factors(rad).size()));
            ++column_checks;
        }
        for (int d = 1; d < r; ++d) assert(a[d] == ec[d]);
        int radical_count = 0;
        for (int d = 1; d * d <= n; ++d) if (mu[d]) ++radical_count;
        assert(static_cast<i64>(powerful_count) * powerful_count <= 9LL * n);
        for (int g = 1; g < r; ++g) {
            i64 future = 0;
            for (int k = 1; g * k < r; ++k) {
                h[g] += mu[k] * hc[g * k];
                future += mu[k] * ec[g * k];
            }
            assert(e[g] == future);
            assert(c[g] == h[g] - e[g]);
            if (g * g > n) { assert(e[g] == 0 && c[g] == h[g]); ++history_tail_groups; }
            ++coefficients;
        }
        i64 h2 = 0, e2 = 0, dg = 0, mixed = 0, nonunit_diag = 0;
        i64 nonunit_norm = 0, gram_energy = 0;
        for (int g = 1; g < r; ++g) {
            h2 += h[g] * h[g]; e2 += e[g] * e[g]; dg += c[g] * c[g];
            mixed -= 2 * h[g] * e[g];
            const i64 f = e[g] - (g == 1 ? m[x] : 0);
            nonunit_norm += f * f;
        }
        for (int d = 1; d * d <= n; ++d) if (mu[d]) {
            if (d > 1) nonunit_diag += (1LL << prime_factors(d).size()) * a[d] * a[d];
            for (int z = 1; z * z <= n; ++z) if (mu[z]) {
                i64 dot = 0;
                for (int g = 1; g <= std::min(d, z); ++g)
                    if (d % g == 0 && z % g == 0) dot += mu[d / g] * mu[z / g];
                const i64 formula = mu[d] * mu[z] * (1LL << prime_factors(std::gcd(d, z)).size());
                assert(dot == formula);
                gram_energy += formula * a[d] * a[z];
                ++gram_checks;
            }
        }
        assert(gram_energy == e2);
        assert(dg == h2 + e2 + mixed);
        const i64 qsum = std::accumulate(c.begin(), c.end(), i64{0});
        assert(std::accumulate(h.begin(), h.end(), i64{0}) == 2LL * m[n]);
        assert(std::accumulate(e.begin(), e.end(), i64{0}) == m[x]);
        assert(qsum == 2LL * m[n] - m[x]);
        const i64 cross = nonunit_norm - nonunit_diag;
        if (cross > 0 && !first_positive_cross) first_positive_cross = r;
        if (cross < 0 && !first_negative_cross) first_negative_cross = r;
        if (mixed > 0 && !first_positive_mixed) first_positive_mixed = r;
        if (mixed < 0 && !first_negative_mixed) first_negative_mixed = r;
        i64 kn = 1, kd = 1;
        for (int t = 0; t < r; ++t) {
            const i64 num = static_cast<i64>(m[t] - 1) * (m[t] - 1);
            if (num * kd > kn * (t + 1)) { kn = num; kd = t + 1; }
        }
        const i64 reduce = std::gcd(kn, kd); kn /= reduce; kd /= reduce;
        if (r <= 10 || r == 15 || r == 17 || r == 56 || r > 100 ||
            r == first_positive_cross || r == first_negative_cross || r == first_positive_mixed)
            std::cout << r << ',' << qsum << ',' << dg << ',' << h2 << ',' << e2 << ','
                      << mixed << ',' << cross << ',' << powerful_count << ',' << radical_count
                      << ',' << kn << ',' << kd << '\n';
    }
    assert(m[1] + m[1] - m[4] == 3);
    assert(4 != m[1] + m[1] - m[4]);
    std::cout << "PASS roots=" << roots.size() << " limit=" << limit << " pairs=" << pairs
              << " rectangles=" << rectangles << " coefficients=" << coefficients
              << " future_labels=" << future_labels << " columns=" << column_checks
              << " gram_checks=" << gram_checks << " history_tail_groups=" << history_tail_groups << '\n';
    std::cout << "FIRST cross_positive=" << first_positive_cross << " cross_negative="
              << first_negative_cross << " mixed_positive=" << first_positive_mixed
              << " mixed_negative=" << first_negative_mixed << '\n';
}
```


#### Executed pd_check.out

```text
R,Q,D_G,H2,E2,mixed,nonunit_cross,powerful_count,radical_count,K_num,K_den
2,3,9,4,1,4,0,1,1,1,1
3,2,4,8,4,-8,0,1,1,1,1
4,-1,35,46,1,-12,0,1,1,1,1
5,0,104,110,2,-8,0,2,2,1,1
6,-3,299,242,5,52,0,2,2,3,2
7,1,55,56,5,-6,0,2,2,3,2
8,-3,201,192,1,8,0,2,2,3,2
9,0,274,192,26,56,0,3,2,3,2
10,-5,523,166,121,236,24,4,3,3,2
15,-7,223,156,101,-34,16,4,3,3,2
17,5,173,618,201,-646,88,5,3,3,2
40,7,8785,14220,855,-6290,-56,9,5,3,2
56,-10,12810,21016,1332,-9538,270,10,6,3,2
127,33,61309,89682,3011,-31384,2876,17,8,3,2
256,-16,68992,107116,5068,-43192,-7826,25,11,3,2
549,-186,213476,305112,70326,-161962,-14846,39,16,3,2
5561,2554,19073482,31666626,7169554,-19762698,-692306,137,47,3,2
PASS roots=103 limit=30924720 pairs=11689857 rectangles=39223 coefficients=11439 future_labels=2254 columns=1094 gram_checks=5154 history_tail_groups=10701
FIRST cross_positive=10 cross_negative=40 mixed_positive=2 mixed_negative=3
```


#### Executed pd_independent.py

```python
"""Exact PD checks with trial factoring and quotient-block Mertens recurrence."""

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, isqrt
import json


@lru_cache(None)
def factors(n):
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
    fs = factors(n)
    return 0 if any(e > 1 for _, e in fs) else (-1) ** len(fs)


@lru_cache(None)
def mertens(n):
    if n == 0:
        return 0
    value, left = 1, 2
    while left <= n:
        q = n // left
        right = n // q
        value -= (right - left + 1) * mertens(q)
        left = right + 1
    return value


def powerful(q):
    return all(e >= 2 for _, e in factors(q))


def radical(q):
    ans = 1
    for p, _ in factors(q):
        ans *= p
    return ans


def weight(q):
    ans = 1
    for _, e in factors(q):
        ans *= e - 1
    return ans


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def column(d, n):
    return [0] + [mu(d // g) if d % g == 0 else 0 for g in range(1, n + 1)]


def wbar(d):
    value = F(1)
    for p, _ in factors(d):
        value *= F(12) if p < 5 else F(isqrt(p), isqrt(p) - 1) ** 2
    return value


counts = Counter()
rows = []
witnesses = {}
for r in list(range(2, 61)) + [127, 256, 549, 5561]:
    n, x = r - 1, r * r - 1
    hc = [0] * r
    ec = [0] * r
    for d in range(1, r):
        if not mu(d):
            continue
        b = n // d
        hs = [h for h in range(1, b + 1) if all(d % p == 0 for p, _ in factors(h))]
        for h in hs:
            for k in hs:
                t = x // (d * d * h * k)
                hc[d] += mertens(b // h) + mertens(b // k)
                if t <= n:
                    hc[d] -= mertens(t)
                else:
                    ec[d] += mertens(t)
    hvec = [0] + [sum(mu(k) * hc[g * k] for k in range(1, n // g + 1))
                   for g in range(1, r)]
    evec = [0] * r
    by_radical = [0] * r
    future_points = []
    l_one = F(0)
    v_one = 0
    for q in range(1, r):
        if not powerful(q):
            continue
        d, aq, t = radical(q), weight(q), x // q
        future_points.append(t)
        by_radical[d] += aq * mertens(t)
        col = column(d, n)
        assert sum(col) == int(q == 1)
        for g in range(1, r):
            evec[g] += aq * mertens(t) * col[g]
        if q > 1:
            l_one += F(aq * len(divisors(d)), q)
            v_one = max(v_one, q * abs(mertens(t)))
        counts['columns'] += 1
    assert by_radical == ec
    assert len(future_points) == len(set(future_points))
    assert min(future_points) > r
    cvec = [h - e for h, e in zip(hvec, evec)]
    if r <= 549:
        direct = [0] * r
        for a in range(1, r):
            for b in range(1, r):
                direct[gcd(a, b)] += mu(a) * mu(b) * (x // (a * b))
        assert cvec == direct
        counts['direct_roots'] += 1
    assert sum(hvec) == 2 * mertens(n)
    assert sum(evec) == mertens(x)
    assert all(evec[g] == 0 for g in range(isqrt(n) + 1, r))
    fvec = evec.copy()
    fvec[1] -= mertens(x)
    assert sum(fvec) == 0
    assert sum(z * z for z in fvec) <= (l_one * v_one) ** 2
    counts['finite_inverse_bounds'] += 1
    kn = max(F((mertens(t) - 1) ** 2, t + 1) for t in range(r))
    if r <= 60:
        for g in range(1, r):
            upper = 9 * r * wbar(g) / g * sum(
                (F(wbar(k), k) for k in range(1, n // g + 1) if mu(k)), F(0))
            assert hvec[g] ** 2 <= kn * upper ** 2
            counts['rational_history_bounds'] += 1
    hs = sum(z * z for z in hvec)
    es = sum(z * z for z in evec)
    mixed = -2 * sum(h * e for h, e in zip(hvec, evec))
    dg = sum(z * z for z in cvec)
    assert dg == hs + es + mixed
    if r in [10, 15, 17, 40, 56, 127, 256, 549, 5561]:
        rows.append([r, sum(cvec), dg, hs, es, mixed, str(kn)])
    if r in [10, 40]:
        witnesses[r] = {"A": [[d, ec[d]] for d in range(1, isqrt(n) + 1) if mu(d)],
                        "H": hvec[1:], "E": evec[1:]}
    counts['all_roots'] += 1

v2, v3, v6 = (column(d, 6) for d in (2, 3, 6))
assert sum(x * y for x, y in zip(v2, v3)) == 1
assert sum(x * y for x, y in zip(v2, v6)) == -2
assert sum(v2) == 0 and v2[1] == -1
assert 4 != mertens(1) + mertens(1) - mertens(4) == 3
counts['negative_controls'] = 4
assert mertens(549 * 549 - 1) == 192
assert mertens(5561 * 5561 - 1) == -2544
print(json.dumps({"status": "PASS_INDEPENDENT_EXACT", "counts": dict(counts),
                  "rows": rows, "witnesses": witnesses,
                  "recurrence_cache": mertens.cache_info()._asdict()}, indent=2))
```


#### Executed pd_independent.out

```json
{
  "status": "PASS_INDEPENDENT_EXACT",
  "counts": {
    "columns": 611,
    "direct_roots": 62,
    "finite_inverse_bounds": 63,
    "rational_history_bounds": 1770,
    "all_roots": 63,
    "negative_controls": 4
  },
  "rows": [
    [
      10,
      -5,
      523,
      166,
      121,
      236,
      "3/2"
    ],
    [
      15,
      -7,
      223,
      156,
      101,
      -34,
      "3/2"
    ],
    [
      17,
      5,
      173,
      618,
      201,
      -646,
      "3/2"
    ],
    [
      40,
      7,
      8785,
      14220,
      855,
      -6290,
      "3/2"
    ],
    [
      56,
      -10,
      12810,
      21016,
      1332,
      -9538,
      "3/2"
    ],
    [
      127,
      33,
      61309,
      89682,
      3011,
      -31384,
      "3/2"
    ],
    [
      256,
      -16,
      68992,
      107116,
      5068,
      -43192,
      "3/2"
    ],
    [
      549,
      -186,
      213476,
      305112,
      70326,
      -161962,
      "3/2"
    ],
    [
      5561,
      2554,
      19073482,
      31666626,
      7169554,
      -19762698,
      "3/2"
    ]
  ],
  "witnesses": {
    "10": {
      "A": [
        [
          1,
          1
        ],
        [
          2,
          -6
        ],
        [
          3,
          -2
        ]
      ],
      "H": [
        -12,
        2,
        -1,
        0,
        3,
        2,
        2,
        0,
        0
      ],
      "E": [
        9,
        -6,
        -2,
        0,
        0,
        0,
        0,
        0,
        0
      ]
    },
    "40": {
      "A": [
        [
          1,
          -7
        ],
        [
          2,
          -24
        ],
        [
          3,
          -5
        ],
        [
          5,
          -1
        ],
        [
          6,
          -3
        ]
      ],
      "H": [
        79,
        -74,
        -39,
        0,
        -8,
        25,
        -12,
        0,
        0,
        5,
        -3,
        0,
        -3,
        8,
        1,
        0,
        1,
        0,
        0,
        0,
        3,
        3,
        3,
        0,
        0,
        2,
        0,
        0,
        1,
        1,
        1,
        0,
        1,
        1,
        1,
        0,
        1,
        1,
        1
      ],
      "E": [
        20,
        -21,
        -2,
        0,
        -1,
        -3,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0
      ]
    }
  },
  "recurrence_cache": {
    "hits": 3078083,
    "misses": 11167,
    "maxsize": null,
    "currsize": 11167
  }
}
```


### Prepublication Validation - PD

At 2026-11-11 15:38:23 UTC / 10:38:23 EST, validation passed all A-M sections and five directive stages, ASCII text, 50 balanced fence markers, seven consistent Markdown tables, all 27 listed main-source blob matches, exact embedding of both executed programs and outputs, the numerical summary rows, and agreement between the two algorithms' overlapping output rows. All four executed-artifact SHA-256 values were rechecked. The forthcoming update appends to a fresh current-file read; no earlier daily text is replaced.

Research execution is complete at its stated PAPER_PROOF / SELF_AUDIT and FINITE_COMPUTATION scopes. Independent PD review and formalization are pending; PD.OPEN remains open. Publication itself is still READBACK_PENDING at this preparation point. The separate immutable-readback receipt below, only if actually committed and verified, closes that publication status.


## Verified Publication Receipt - 20261111-wheel-2/PD

Verified **2026-11-11 15:39:35 UTC / 10:39:35 EST**. The complete substantive continuation was published on agent-reports at [commit 6747818c42c4b7f7e3b8472cedd8be04f98ca222](https://github.com/OVVO-Financial/RH_Lean/commit/6747818c42c4b7f7e3b8472cedd8be04f98ca222), blob `54b0dd1f2b85d7d33f25d5b1b4e51c910308c157`. Immutable-commit readback matched all **126125 intended characters** exactly, including the complete **62896-character** prior report/checkpoint as an unchanged prefix. Commit inspection confirms exactly this owned daily report: **1090 additions and ZERO deletions**. No other remote file changed in that commit.

`EXECUTION=COMPLETE; SUBSTANTIVE_PUBLICATION=PUBLISHED_READBACK_VERIFIED.` This closes this invocation's earlier IN_PROGRESS/READBACK_PENDING wording, not its mathematical review obligations. PD1-PD3 remain PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED; PD4 is the stated conditional and target-equivalence audit; PD5 is exact finite evidence and the narrowly scoped refutations. The historical norm and complete high-gcd tail are proved on paper; the powerful response bound and inverse-witness exclusion remain OPEN. No independent PD ACCEPT is claimed.

Both executed arithmetic programs finished successfully: 103 primary roots and 63 algorithmically distinct self-check roots, with the full source, output and hashes above. Source/format/summary validation passed. No local Lean ran. The scoped compiled baseline and the separately accepted OAI paper endpoint are unchanged. **NO_NEW_GLOBAL_GAIN; NO_NEW_ACCEPTED_ROUTE; VERIFIED_ETA=NONE.** Canonical VF, finite A/C, full wheel bound and RH remain OPEN.

Only this role's owned dated report was modified remotely. No main/source/other-report edit, proof branch or PR change, workflow launch, merge, agent launch, schedule change or permission change occurred. This receipt is appended against a fresh current blob and checked at its returned immutable commit before final user delivery; it records the already verified substantive commit rather than guessing its own future SHA.
