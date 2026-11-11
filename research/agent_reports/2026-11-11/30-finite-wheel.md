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


