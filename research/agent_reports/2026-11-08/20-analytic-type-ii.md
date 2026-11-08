# RH | Analytic Type II - 2026-11-08

## Early CODIV Checkpoint - 20261108-analytic-1

### A. Most Important Analytic Development

IN_PROGRESS / PARTIAL. No new theorem is claimed at this checkpoint. The selected question is whether the already certified Mertens boundary, combined with an independently established prime short-window estimate, pays the exact prime/composite mixed interaction inside the remaining small-GCD triangular covariance. A component estimate is not a complete endpoint improvement.

### B. Current Mathematical Objective And Authority

Actual scheduled trigger: 2026-11-08 01:04:01 EST, America/New_York; RUN_ID_UNAVAILABLE.
Main: bf4af1cd18aff7c3944a75991aa66371c8afc18a.
AGENTS blob: 0a99faf8458809ac772d470d704c5433f373bda8.
CURRENT_PROOF_CONTRACT blob: d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a.
high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1; baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1; deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.

The canonical complete object remains M(R^2-1)=L_R+H_R, with fixed-Lambda |L_R|<=(floor Lambda+1)R. The actual-prime VF/von Koch objective remains OPEN. Merged #1107 supplies the same-source every-positive-loss boundary b=7/8-m/4, m=actualSlotMinimum(D)>0. Its full terminal source and exact-head standard-axiom log were read. No equality with the optimal exponent, explicit numerical value of m, new endpoint, or independent Referee acceptance is invented.

### C. Exact Source And Research Continuity

Resume accepted 20261107-analytic-1/GL1-GL4 and Coordinator WS-CODIV-PRIMITIVE. The genuine source is

```text
T(X,h)=2 sum_(1<=d<h)(h-d) sum_(X<=n<4X)mu(n)mu(n+d),
X=H^2, h=floor(H^(2/3)).
```

The forward value n+d is not clipped. Merged #1102 pays the gcd(n,d)>=G sector by 8Xh^2/G; the small-GCD signed complement is OPEN. The already accepted positive-support lower bound is not rerun. Inspect a prime-profile projection of the SAME short-window sum, including all diagonal, mixed, forward-halo and composite-residual terms. Do not transfer Owner's prime-error weights to this distinct carrier.

November 7 Coordinator, Owner, Analytic, Wheel, Census, Referee and Lean reports were retrieved, including GL/FT/BC, SG/RS/JT, OC, RC, TF and WS. November 8 Owner PD1-PD6 is available; all other upstream November 8 stages are TODAY=PENDING, YESTERDAY=CARRY_FORWARD. External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 has no newer entry than October 18. Earlier external boundary, anchor, and source distinctions remain in force.

Rolling own sequence before this invocation: CODIV, NYMAN, OAI-NNS. This turn is CODIV; next protected route NYMAN. OAI BC1-BC4 and Coordinator WS remain separate pending handoffs, not abandoned work.

### D-L. Work And Publication Pending

Mathematical derivation, literature transfer, falsification, full quantitative comparison, specialist requests and final resume capsule follow after actual work. Relevant reused source blobs: CODIV_LARGE_GCD_TRIANGULAR_20261107.lean f24498bfe13d88d0f8ba621ce103e81d6c800379; VF919TotalMassEndpoint.lean 827bb952c4d4311d75fd03a2470799dc10b0f7e7; CanonicalHighSectorCore.lean dd02fc8fabfe4004c6b0d50374b3b8752607b168.

Fresh CI logs: #1102 tested head 5b246ac81398ae8ee8f177dc9acda18288765a4e, job 128379218641, five standard-axiom declarations; #1107 tested head cd8f98fd6ed2dee3fa08f526eb8ac86c94549da5, job 128599096276, four terminal PASS closures. Both PRs are now human-merged. #1108 is currently open/non-draft at a0c986c0343a56e98b7344268fdc0b74aa885cdb; its reported green state is not used as a new main input.

Only this own dated report is authorized for remote writing. No Lean execution, proof-source modification, branch/PR write, other report change, main write, schedule change, or agent launch. Publication is pending actual commit/readback.

---

## Prime-Profile Cancellation In The Genuine Small-GCD Source - 20261108-analytic-1

Substantive synthesis prepared 2026-11-08 01:32:12 EST (06:32:12 UTC). This continues the same scheduled invocation and preserves its earlier checkpoint above.

### A. Most Important Analytic Development

**The existing global Mertens input can pay a new signed mixed interaction in the original CODIV short-window source. The estimate remains uniform over a genuinely growing family of small cofactors.** It does not pay the full source.

Let X>=8 be an integer, h=floor(X^(1/3)), and S(n)=sum_(0<=j<h)mu(n+j). For one integer cutoff 1<=A<=X^(1/8), fixed throughout the n-window, define

```text
f_A(m) = -sum_(1<=a<=A) mu(a) 1_(m=a*p for a prime p),
U_A(n) = sum_(0<=j<h) f_A(n+j),
Q_A(X,h) = sum_(X<=n<4X) U_A(n) S(n).
```

On the actual sites X<=m<4X+h the representation m=a*p has at most one such cofactor, p>a, and

```text
f_A(m) = mu(m) 1_(m has an admitted representation).
```

Thus this is a genuine signed arithmetic subpopulation, not a density model or a tuple counted repeatedly. From the already supplied native Mertens boundary and the external zero-density theorem specified below, the new paper argument proves, for every epsilon>0,

```text
sup_(1<=A<=X^(1/8)) |Q_A(X,h)|
    <<_epsilon X*h^2 * X^(-11/952+epsilon).                    (MP-A)
```

The bound is uniform in A and X; the implied constant also depends on the fixed inherited Mertens supplier. Every distinct short-lag pair touching this population has gcd(n,d)<=A. Consequently MP-A acts INSIDE the remaining small-GCD source, not in the already paid #1102 tail. No equality of rational Mobius signs and Hecke phases is used.

For the prime-only profile P(n)=sum_(j<h)1_prime(n+j), the stronger bound is

```text
|sum_(X<=n<4X) P(n)S(n)|
    <<_epsilon X*h^2/log(X) * X^(-3/119+epsilon).             (MP-P)
```

The exact triangular return yields a signed prime/composite compensation law, including its prime diagonal. The prime-pair contribution is asymptotic to 3Xh^2/log^2(X), while its mixed prime/composite companion is asymptotic to -6Xh^2/log^2(X). These statements concern the aggregate defined below, not individual pair signs. The full composite residual and the coherent global prefix remain necessary.

| Claim | Result | Evidence |
| --- | --- | --- |
| 20261108-analytic-1/MP1 | Uniform prime-ray short-window variance from the licensed Mertens boundary and stated zero-density theorem | PAPER_PROOF from established inputs; new transfer is SELF_AUDIT |
| 20261108-analytic-1/MP2 | Genuine prime/Mobius mixed estimate MP-P and exact prime/composite triangular compensation | PAPER_PROOF; proper-source quantitative result |
| 20261108-analytic-1/MP3 | Uniform growing-cofactor signed estimate MP-A, with once-only admission and small-GCD localization | PAPER_PROOF; proper-source quantitative result |
| 20261108-analytic-1/MP4 | Prime-projection inverse restriction, exact complete return, and baseline-sized coherent term | PAPER_PROOF for inequalities; identities distinguished; endpoint remains OPEN |
| 20261108-analytic-1/MP5 | h=1 obstruction to a uniform-all-h extension; exact boundary and projection limitations | PAPER_PROOF / specified auxiliary assertion REFUTED; no route-wide no-go |
| 20261108-analytic-1/MP6 | Preregistered exact source, projection, halo, admission and exponent checks | FINITE_COMPUTATION; no asymptotic inference |

All NEW paper claims are **INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED**. No literature-priority claim is made for standard zero-density or Hilbert-space methods. NEW_VERIFIED_ENDPOINT_GAIN=NONE; VERIFIED_ETA=NONE; eta_gate=SEARCH_BROAD. This is substantive signed component control, not a proof of RH or of the canonical VF objective.

### B. Current Mathematical Objective And Strongest Baseline

The intake source is main **bf4af1cd18aff7c3944a75991aa66371c8afc18a**. The governing HIGH directive and source hypotheses are unchanged from the checkpoint. Canonical LOW has its fixed-Lambda O(R) bound, and the canonical target remains the genuine prime-counting von Koch estimate.

The strongest same-source main input consumed is
`native_mertens_true_physical_slot_minimum_total_mass`, from merged #1107:

```text
There is one fixed fine D with m=actualSlotMinimum(D)>0 and
MertensGrowthAtMost(b), b=7/8-m/4.
```

In ordinary notation, every positive loss has a constant independent of the growing integer argument. The accompanying signed-pair theorem keeps the actual squarefree diagonal. The same module's `recalibrated_total_mass_tilt_budget` gives 0<m/4<1/960, so the selected b lies inside [3/4,7/8]. The older same-source 7/8-m/24 boundary is not the comparator. The actual optimal exponent is not identified with b, and no explicit value of m is asserted.

For the analytic statements, ANY fixed b in [3/4,7/8] satisfying

```text
for every e>0, |M(y)| <= C_e*y^(b+e), y>=1,                  (B)
```

is sufficient. The source witness above is applicable; all quantitative formulas retain b. The fractions 3/119 and 11/952 are conservative component savings valid throughout this interval, NOT replacements of b by 7/8 when comparing endpoints. The proof uses the ordinary Riemann zeta function only. It neither assumes an analogous statement for all Dirichlet L-functions nor re-licenses an OAI source from a desired output.

The standard Abel integral s*integral_1^infinity M(t)t^(-s-1)dt is absolutely and locally uniformly convergent for Re(s)>b after choosing a smaller positive loss. It equals the naturally ordered Dirichlet series sum mu(n)n^(-s), which is not asserted to converge absolutely there; absolute series convergence is only used initially for Re(s)>1, where it equals 1/zeta(s). Analytic continuation excludes nontrivial zeta zeros with real part>b. This supplies the zero cutoff used below directly from (B). The live converse module also records `growthAtMost_iff_strip`; no missing numerical zero-free assertion is inserted as an assumption.

### C. Mechanism, Continuity And Novelty

The last accepted CODIV result GL2 pays large gcd; GL3 shows why positive-support counting alone cannot pay the entire complement. The present changed question is whether the known prime distribution in a common moving interval is smooth ENOUGH IN MEAN SQUARE to average against the actual signed Mobius window. This is a joint mixed estimate, not a stronger arbitrary-vector negative-covariance assumption.

The independent ingredient is zero density, applied with the ALREADY licensed fixed zero boundary. The new argument derives a power-saving prime-window approximation, keeps its error in L2, uses the native Mertens bound only for the smooth weighted term, and returns to the literal finite pair sum. For growing cofactors, the loss is summed with its actual 1/a weight; the harmonic sum costs only logarithms. All signed coefficients and cross terms remain.

Overlap was checked against the live CODIV route catalogue, `SQUARE_SHELL_LONG_LAG_FIVE_SIXTHS_20261019.md`, `NNS_SIGNED_PRIME_WINDOW_COVARIANCE_20261103.md`, `PRIME_DENSITY_PACKET_OPERATOR.md`, and the November 7 GL/FT/BC and current Coordinator/Owner work. The older notes either concern different reciprocal/cofactor interval families or explicitly leave their variance transfer unproved. MP1 is for the common additive windows below, not an automatic theorem on those other families. GL2, GL3, the source square identities, and elementary projection algebra are not claimed as rediscovered mathematics. Repository search is not proof of worldwide novelty.

Continuity at intake: November 8 Owner PD1-PD6 AVAILABLE; Coordinator, Wheel, Census, Referee and Lean TODAY=PENDING, YESTERDAY=CARRY_FORWARD. All November 7 named reports were retrieved. Referee's accepted GL1-GL4 scopes are preserved; GL2 is now main via #1102, while GL3 remains paper. OAI BC1-BC4 and NYMAN FT remain their original paper/consumer scopes. Owner PD's prime-error weights are not substituted into MP's Mobius windows. External inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry after October 18; relevant EXT-20261018-PNT and earlier anchor/boundary qualifications remain in force.

### D. Exact Formulation And Quantifiers

Write I_X={X,...,4X-1}, h=floor(X^(1/3)), and use the genuine mu and prime indicator p. All sums are finite unless a classical analytic input is expressly named. Define

```text
S_n = sum_(j=0..h-1) mu(n+j),       J = sum_(n in I_X) S_n^2,
P_a(n) = #{prime p : n <= a*p < n+h},
g_a(n) = h/[a*log(n/a)].
```

For kappa equal to 0 or 1/8, set

```text
u=1-b,
nu_kappa = (6-26*kappa)*u/(26+30*u),
delta_kappa = 2*nu_kappa,       v_kappa=2/3+nu_kappa.
```

MP1 states that for every e>0 there are constants C and X0, depending only on fixed b, kappa, e and the analytic suppliers, such that, for every integer X>=X0 and every integer 1<=a<=X^kappa,

```text
sum_(n in I_X) |P_a(n)-g_a(n)|^2
 <= C * (X*h^2)/(a^2*log^2 X) * X^(-delta_kappa+e).         (V)
```

Constants and X0 are chosen BEFORE a and X. Only the two displayed fixed kappa values are claimed; no limit uniformity as kappa approaches a critical value is asserted. For kappa=0, a=1. At b=7/8,

```text
nu_0=3/119,       delta_0=6/119,       v_0=247/357;
nu_(1/8)=11/952,  delta_(1/8)=11/476.
```

All smaller admissible b improve these component margins. No explicit numerical asymptotic threshold or constants were computed. The density theorem's arbitrary-loss constants and the native supplier's constants are retained, not converted into an asserted effective numerical certificate.

For MP2 put P=P_1, C_n=S_n+P_n, V=sum P_n^2, Q=sum P_n S_n, and B=sum g_1(n)S_n. The symbol C_n is the signed COMPOSITE window, not a prime-free density. MP3 uses one A fixed for each X, f_A as in A, and U_A its window. An n-dependent A(n), an adversarial subset of n, arbitrary prime weights, or arbitrary growing progression moduli are outside the theorem.

### E. Mathematical Derivation

#### E1. External input and the licensed prime-ray variance: MP1

The external input is Guth and Maynard, *New large value estimates for Dirichlet polynomials*, arXiv:2405.20552v2 (7 April 2026), Theorem 1.2 and consequence (1.4): with multiplicities and both signs of height,

```text
N(sigma,T) <<_e T^[(30/13)(1-sigma)+e], 1/2<=sigma<=1, T>=2.
```

Section 13.2 also records the truncated explicit formula with error O(U log^3(U)/T), for 2<=T<=U, and the unit-height zero count O(log(T+2)). These standard inputs are used, not reproved or claimed as native Lean results. A finite sigma mesh and monotonicity give the required uniform arbitrary-loss version on [1/2,b], even if one starts with fixed-sigma statements. See the [primary paper, equation (1.4) and section 13.2](https://arxiv.org/pdf/2405.20552v2). The new fixed-boundary and actual-carrier consequences are derived next; the paper's almost-all corollary alone is not invoked as a power-saving variance theorem.

Let U=X/a and let ell be either floor(h/a) or ceil(h/a). Choose T=X^v, v=v_kappa, or a permissible nearby truncation height of comparable size. Uniformly a<=X^kappa, we have T<U, ell comparable to h/a for sufficiently large X, and a fixed dyadic enlargement covers all endpoints. The explicit formula gives

```text
psi(y+ell)-psi(y)-ell
 = -sum_(|gamma|<=T) integral_0^ell (y+t)^(rho-1) dt
   + O(U*log^3 U/T).
```

Endpoint conventions change this by at most O(log U), already affordable here. Cauchy in t followed by integration over y in the fixed dyadic enlargement bounds the squared zero-sum integral by

```text
ell^2 * integral_(cU)^(CU) |sum_(|gamma|<=T) y^(rho-1)|^2 dy.
```

Expanding this LAST integral, each pair is at most a constant times
U^(beta+beta'-1)/(1+|gamma-gamma'|). This follows by integrating the complex power, using a direct length bound when the frequency difference is small. Symmetric 2rs<=r^2+s^2 and the unit-height zero count imply

```text
integral |sum y^(rho-1)|^2 dy
 << U^(-1)*log^2(T+2)*sum_(|gamma|<=T) U^(2*beta).
```

This is a finite-sum argument; no conditional infinite zero sum is squared. Split at beta=1/2. Partial summation of the density count, with the fixed cutoff beta<=b supplied by (B), gives

```text
sum U^(2*beta)
 <<_e U*T*log(T+2) + U^(2*b)*T^[(30/13)(1-b)+e]*log U.
```

Indeed the exponent 2 log U-(30/13)log T is positive throughout a<=X^kappa. Keeping both terms, dividing the variance by U*ell^2, and absorbing logarithms into an arbitrary positive loss leaves the three bounds

```text
X^(v-1+kappa),
X^(-[2*(1-kappa)-(30/13)*v]*(1-b)),
X^(-2*(v-2/3)).                                          (E1)
```

The last is the SQUARED truncation error: U/(T*ell) is comparable to X/(T*h), so a cancels. By the chosen nu,

```text
[2*(1-kappa)-(30/13)*v]*(1-b) = 2*nu = delta_kappa,
delta_kappa < 1-kappa-v,
delta_kappa < 2/3-2*kappa.                                (E2)
```

These are elementary strict inequalities for b in [3/4,7/8] and kappa=0,1/8. Indeed u is in [1/8,1/4], and nu_kappa increases with u. Its maxima are 3/67 and 11/536 respectively; these satisfy 3*nu_kappa<1/3-kappa and 2*nu_kappa<2/3-2*kappa. The displayed density coefficient is positive since it equals 2*nu_kappa/u. Thus the prime-power weighted variance has normalized power at most X^(-delta_kappa+e), uniformly in a.

Here is the full unweighting and discrete return. An interval of length ell<=O(U^(1/3)) contains O(log U) integer perfect powers with exponent>=2: for each exponent k use the count at most O(ell/sqrt U+1), and sum over k<=log_2(CU). Their total von Mangoldt weight is O(log^2 U). Removing them contributes at most O(U log^4 U) to the variance. Dividing prime log weights by log y incurs the deterministic error O(ell^2/(U log U)); this follows directly from |log p-log y|=O(ell/U) and the trivial count <=ell+1. Both errors are smaller than the retained target by (E2).

For each residue n mod a the physical interval [n,n+h) becomes a prime interval starting at ceil(n/a), of one of the two lengths ell above. Summing over the at most a residue classes costs a, changing U to X in the leading variance. Each integer prime interval is represented exactly by integrating its step function over the adjacent unit cell. Replacing ell/log(ceil(n/a)) by h/[a log(n/a)] costs O(1/log U) per n, plus a smaller logarithmic variation error. Its squared cost O(X/log^2 X) is affordable by the final inequality in (E2). This proves (V), including rounding, prime powers, all residues and uniformity in the growing a.

#### E2. Average the smooth part using the actual Mertens input

For a=1, S_n is never replaced by an average. Interchange its finite sum with n and apply Abel summation to each shifted mu(k) with weight 1/log(k-j). Its supremum and total variation over the relevant interval are O(1/log X). From (B),

```text
|B| = |sum g_1(n)S_n| <<_e h^2*X^(b+e)/log X.             (E3)
```

Let E_n=P_n-g_1(n). Cauchy is used ONLY on this independently small approximation error, retaining the unknown complete J:

```text
|Q| <= |B| + ||E||_2*sqrt(J)
 <<_e h^2 X^(b+e)/log X
       + h X^((1-delta_0)/2+e)*sqrt(J)/log X.              (E4)
```

Since J<=3Xh^2 and b<1-nu_0, this proves MP-P. The power saving is in a genuine signed prime/Mobius correlation. No Chowla conjecture, independence, selected-population density replacement, or local Mobius bound has been assumed.

Also ||g_1||_2^2=(3+O(1/log X))Xh^2/log^2 X. Equation (V) and the triangle inequality in L2 imply

```text
V=(3+o(1))*Xh^2/log^2 X.                                  (E5)
```

This is only a consequence at the specified common windows. No pointwise prime-counting asymptotic for every short interval is claimed.

#### E3. Restore the original triangle, signs and forward halo: MP2

For real sequences a_m,b_m of absolute value at most one define

```text
F_h(a,b) = h sum_(m in I_X) a_m b_m
 + sum_(1<=d<h)(h-d) sum_(m in I_X)
       [a_m b_(m+d)+b_m a_(m+d)].
```

The exact common-window bilinear sum equals F_h(a,b)+B_h(a,b). Explicitly, put r=min(i,j) for each 0<=i,j<h and sum

```text
B_h(a,b) = sum_(i,j<h)
  [sum_(m=4X..4X+r-1) - sum_(m=X..X+r-1)]
       a_(m+i-r) b_(m+j-r),
```

with an empty strip when r=0. For every X>=1 and 1<=h<=X,

```text
|B_h(a,b)| <= H_h := h(h-1)(2h-1)/3.                      (E6)
```

Proof: a term with min(i,j)=r shifts [X,4X) by r, costing at most 2r. The diagonal cost is h(h-1); the two off-diagonal orientations cost 2 sum_(s=1..h-1)s(s-1). Their sum is H_h. In particular n+d is NEVER clipped at 4X.

Set c_m=mu(m)+p_m, so c_m is zero on primes and equals mu(m) on composites in our positive range. Put Pi_X=sum_(m in I_X)p_m and

```text
T_PP = 2 sum_d(h-d) sum_m p_m p_(m+d),
T_PC = -2 sum_d(h-d) sum_m [p_m c_(m+d)+c_m p_(m+d)],
T_CC = 2 sum_d(h-d) sum_m c_m c_(m+d).
```

Their sum is EXACTLY the original T(X,h). Expanding F_h(p,mu) gives

```text
T_PC + 2*T_PP + 2*h*Pi_X = -2*Q + 2*B_h(p,mu).            (E7)
```

This explicitly retains the prime diagonal and both mixed orientations. Combining MP-P with (E6) bounds the right side by

```text
O_e(X*h^2/log X * X^(-nu_0+e) + h^3).                    (E8)
```

Similarly T_PP=V-h*Pi_X-B_h(p,p). The trivial Pi_X<=3X and h growing polynomially make both corrections o(V). Hence E5 gives T_PP~3Xh^2/log^2 X, and E7-E8 give T_PC~-6Xh^2/log^2 X. The quantitative mixed deviation is specified by (E8); the logarithmically varying main profile was not replaced by a constant to claim a power error for T_PP itself.

If a prime is one endpoint of a distinct pair at distance d<h<X, the pair has gcd(n,d)=1: that prime exceeds d, and any common divisor would have to be that prime. Thus EVERY contributing term in E7's off-diagonal belongs to the primitive g=1 part of GL1; its gcd(m,k)=1 mask is automatic, and its gcd(g,m(m+k))=1 mask is literal. Squareful composite endpoints still vanish through mu. This is a checked source restriction, not a cancellation assertion for every primitive pair.

#### E4. Keep the 1/a weight through a growing cofactor family: MP3

For a<=A<=X^(1/8) and X<=m<4X+h, p=m/a>a and p does not divide a. If two distinct primes p,q admitted m, both would exceed sqrt(m), which is impossible. Therefore f_A is exactly the admitted restriction of mu, including squareful zeros. In particular |f_A|<=1.

Write

```text
U_A(n) = -sum_(a<=A) mu(a)P_a(n),
G_A(n) = -h sum_(a<=A) mu(a)/[a log(n/a)].
```

Apply (V) at kappa=1/8 and Minkowski with the actual reciprocal weights:

```text
||U_A-G_A||_2
 <<_e h X^((1-delta_(1/8))/2+e)/log X * sum_(a<=A)1/a
 <<_e h X^((1-delta_(1/8))/2+e).                          (E9)
```

This is where growing-cofactor uniformity is paid. No supremum times A is substituted. The finite harmonic sum is <=1+log A; no absolute-convergence claim is made.

Across n in I_X, with this A fixed, |G_A(n)|<=O(h) and its total variation is O(h); differentiate each 1/log(n/a), using log(n/a)>=(1-kappa)log X. Abel summation after expanding S_n yields

```text
|sum G_A(n)S_n| <<_e h^2 X^(b+e),
|Q_A| <<_e h^2 X^(b+e)
              + h X^((1-delta_(1/8))/2+e)*sqrt(J).         (E10)
```

The trivial J bound and b<1-nu_(1/8) prove MP-A, with nu_(1/8)>=11/952. The constant is independent of A, including an A chosen after X, because all intermediate bounds were uniform on the declared range. A is not allowed to vary within the n-sum.

For a contributing endpoint m=a*p and d<h, p>d. Thus gcd(m,d)=gcd(a,d)<=a<=A; the same argument applies when m is the right endpoint. This preserves the exact extracted primitive masks, and shows the whole off-diagonal one-leg contraction lies below any G>A. In GL4's intended G=ceil(H^(1/2+eta)), X=H^2, this inequality holds for all sufficiently large H since A<=H^(1/4).

Let r_A=mu-f_A, W_A(n)=sum_(j<h)r_A(n+j), V_A=sum U_A^2 and V_R=sum W_A^2. The original carrier is restored by

```text
S=U_A+W_A,
Q_A=V_A+sum U_A W_A,
J=V_A+V_R+2 sum U_A W_A = V_R-V_A+2Q_A.                  (E11)
```

At pair level define T_AA,T_AR,T_RR with the same triangular weights, and T_AR containing both cross orientations. Let D_A=sum_(m in I_X)mu(m)f_A(m), its genuine squarefree admitted diagonal. Then

```text
h*D_A+T_AA+T_AR/2 = Q_A-B_h(f_A,mu),
T=T_AA+T_AR+T_RR.                                       (E12)
```

Equations E11-E12 make clear what MP-A bounds and what it leaves unpaid. No negative credit is spent twice, and the residual is the explicitly defined complementary arithmetic population.

### F. Quantitative Comparison And The Remaining Global Budget

The new contraction beats its trivial scale Xh^2 by a fixed component power. For example, spending e=11/1904 in MP-A yields a fixed saving 11/1904, with no unspecified positive loss. MP-P analogously permits a fixed saving 3/238 after spending half its component margin. These are NOT Mertens exponent gains.

At X=H^2 and h=floor(H^(2/3)), the inherited accepted GL4 return is

```text
E_max(H) <= (8H/h^2)J + 2H(h-1)^2,
J = h*D + T_lt + T_ge + B_h(mu,mu),
D<=3H^2, |T_ge|<=8H^2*h^2/G, |B_h|<=H_h.
```

These are reused source-exact paper/Lean inputs, not MP discoveries. The retained diagonal, halo, translation cost and incomplete final square block remain in the full endpoint argument. Merely taking absolute values in E11 and using MP-A would give a contribution of size H^(3-2*nu_(1/8)+e), whereas an improvement to b-eta needs shell energy H^(4*(b-eta)-1+e). At b=7/8 the former is close to H^3 and the latter is below H^(5/2). The component power is real but insufficient; V_R-V_A is also not independently bounded here.

The prime-only projection gives a sharper diagnosis. Define

```text
J_perp = sum_(n in I_X) [C_n-(sum P*C/V)P_n]^2.
```

For sufficiently large X, V>0 by E5. Exact orthogonal decomposition gives

```text
J = J_perp + Q^2/V.                                     (E13)
```

Combining E3-E4 with V comparable to Xh^2/log^2 X proves, for every e>0,

```text
Q^2/V <= C_e h^2 X^(2b-1+e) + C_e X^(-delta_0+e) J.     (E14)
```

Fix a loss smaller than delta_0 and absorb the last coefficient only after its scale threshold. In particular

```text
J <= 2 J_perp + C_e h^2 X^(2b-1+e).                     (E15)
```

This is a quantitative inverse restriction: after making the second coefficient at most 1/4, any J at least four times its displayed coherent allowance forces J_perp>=J/2. Large excess energy cannot live only in the prime profile. The unknown orthogonal COMPOSITE mode has not been excluded.

The coherent term in E15 contributes H^(4b-1+e) to E_max. With the actual b=7/8-m/4 this is H^(5/2-m+e), exactly the inherited endpoint scale, not a further gain. Discarding it would manufacture an improvement. A stronger composite bound ALONE does not upgrade this conclusion below b.

For a transparent exact open consumer retain B rather than bounding it by E3. Let L=sum g_1(n)^2 and

```text
K(X)=J_perp+B^2/L.
```

For large X, Cauchy gives K<=2J and E4/V with absorption gives J<=C K for an absolute fixed comparison constant after the input-dependent threshold. Thus this joint criterion is equivalent up to constants to the original window energy, not an independently easier theorem.

A sufficient STILL OPEN target, for fixed 0<eta<b-5/6, is

```text
K(H^2) <<_e h^2*(H^2)^(2b-1-2eta+e), all integers H>=H0. (OPEN-MP-RETURN)
```

The honest complete return would then give E_max<<H^(4(b-eta)-1+e)+H^(7/3), all-prefix Mertens growth at b-eta, and canonical HIGH growth after restoring its supplied O(R) LOW. Spending half the gain gives fixed Mertens power b-eta/2. The final incomplete square costs O(sqrt x). The restriction b-eta>5/6 comes from the translated-window overhead, not from the prime-variance lemma. No value of eta is established by this run, and OPEN-MP-RETURN is explicitly recognized as an equivalent local-energy obligation rather than advertised as a new independent reduction.

### G. Original-Carrier Bridge, Provenance And Formal Evidence

The exact real Mobius coefficient is `realMoebiusStep n=((mu n : Int):Real)`. The compiled large-GCD pair set uses 1<=d<h, X<=n<4X and G<=gcd(n,d), with the literal n+d. Our splitting and E6-E12 act on those same pairs, not clipped substitutes. At X=H^2, the inherited GL4 common-window consumer restores the actual square-shell intervals. The canonical LOW/HIGH split is only invoked after a complete Mertens bound; no original #915 payment or actual-prime von Koch consequence follows from MP alone.

| Material source at main bf4af1cd18aff7c3944a75991aa66371c8afc18a | Blob SHA |
| --- | --- |
| AGENTS.md | 0a99faf8458809ac772d470d704c5433f373bda8 |
| CURRENT_PROOF_CONTRACT.md | d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a |
| Complete signed HIGH directive | be8168b67584d9d8ebbaa732a30c51509137543e |
| Cancellation-chain reuse directive | 28e2ab47c68bc83b91ae02b6112b94867b021b32 |
| RHLean/Analysis/DeterministicTGreenKuboComparison.lean | 802a58b4e1994a5f8c14f1080ac42d0f5f28a0d5 |
| research/CODIV_LARGE_GCD_TRIANGULAR_20261107.lean | f24498bfe13d88d0f8ba621ce103e81d6c800379 |
| research/oai_434/VF919TotalMassEndpoint.lean | 827bb952c4d4311d75fd03a2470799dc10b0f7e7 |
| research/MERTENS_CONVERSE_IDENTIFICATION.lean | 768c8255850bf4074aff265c3fe17a1f5c43979b |
| RHLean/Analysis/CanonicalHighSectorCore.lean | dd02fc8fabfe4004c6b0d50374b3b8752607b168 |
| RHLean/Analysis/CanonicalLowOccupancy.lean | b958da340d107cdd00015d2827b9a728357b4d8e |
| research/SQUARE_SHELL_LONG_LAG_FIVE_SIXTHS_20261019.md | 451824604acc988dfb848bc602a26478d0679d44 |
| research/NNS_SIGNED_PRIME_WINDOW_COVARIANCE_20261103.md | c6b88c91b5d7b5a14e1c1c3d5a48ca1a60e7c839 |
| research/PRIME_DENSITY_PACKET_OPERATOR.md | aa949af4b481104ad6329df1496bc70fc000e493 |

Direct source links: [large-GCD original pair theorem](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/CODIV_LARGE_GCD_TRIANGULAR_20261107.lean), [native complete endpoint](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/oai_434/VF919TotalMassEndpoint.lean), [arithmetic growth/zero-strip source](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/MERTENS_CONVERSE_IDENTIFICATION.lean), and [prior accepted GL derivation and full return](https://github.com/OVVO-Financial/RH_Lean/blob/9513f078ec95437d3b064337b3a796cebe37fe29/research/agent_reports/2026-11-07/20-analytic-type-ii.md).

Exact CI evidence was re-fetched, not assumed from a green icon. [#1102 job 128379218641](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42364367658/job/128379218641), proof head 5b246ac81398ae8ee8f177dc9acda18288765a4e, prints all five original-source theorem types and only propext, Classical.choice, Quot.sound. [#1107 job 128599096276](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42437401175/job/128599096276), proof head cd8f98fd6ed2dee3fa08f526eb8ac86c94549da5, reports warning-fatal source/type/live-dependency acceptance and four standard-axiom terminal PASS closures of sizes 35352,35731,35732,35746. These validate the REUSED inputs, not MP1-MP6 or a new whole-main rebuild. The live PR API confirms both human merges. #1108 is an unmerged explicit-source/amplification consequence, not an input used to assert a new endpoint here.

Reporting intake branch head 9513f078ec95437d3b064337b3a796cebe37fe29 gave these prior-day blobs: Coordinator 00a649b70f851ca193e74e5004d0d3390cf9ca18; Owner 933e8eb23e669594cc687059d75147e6267eec8d; own 77f3e5795533041e4356ceb94cb66328da7af27c; Wheel 7739fa5d4cc77f35773b0d4149b2ddd21732a70d; Census 3fae830e34c590d32c31ad77cad3ace833eb3ff5; Referee 426c2abfa5b8926b512e07f05be37692a2416d0b; Lean ec14e2803af8c1e56123682ee61ed927ed4f9450. Today's Owner blob is 79dd00b2c26491ab302ea17d6dbe4e0146d57a97. All unavailable stages remained PENDING, not presumed scheduled completions.

The pre-publication refresh at approximately 01:32 EST again returned main bf4af1cd18aff7c3944a75991aa66371c8afc18a, #1108 open/non-draft at a0c986c0343a56e98b7344268fdc0b74aa885cdb, and the unchanged November 8 Owner plus this report's checkpoint. No new upstream completion or source change was observed. The builder-attached historical contract was also read; its old #915-first assignment and blanket no-write instruction do not override the live main/user-authorized CODIV portfolio and own-report-only publication permission.

### H. Falsification, Domain Restrictions And Executed Checks

**Uniform-all-h extrapolation is false.** At h=1 the off-diagonal triangle vanishes and Q=-Pi_X exactly. By PNT this has order X/log X, contradicting the extension of MP-P with any fixed power saving to h=1. Likewise the prime-count variance at h=1 has order X/log X, not X^(1-delta)/log^2 X. MP1-MP3 explicitly require h=floor(X^(1/3)); they do not supply the all-h canonical PREFIX-energy criterion. The two notions of window are different.

**Projection is not full energy.** The rational vector example P=(1,1), C=(2,0), S=(1,-1) has Q=0 and J=2. It refutes a projection-only implication for arbitrary vectors, not for genuine Mobius data. The actual finite tests found no Q=0,J>0 witness and no positive prime-only Q within their fixed domains. No universal sign theorem is inferred from that absence. The completed identity and inverse restriction, not a claimed negative sign, are used in the proof.

**Real boundaries matter.** At X=11,h=2, Q=-20 and its uncorrected forward triangle is -21, so B_h(p,mu)=1. At X=27,h=3, the actual prime pair 107,109 contributes at lag 2 even though 109>=4X=108. Clipping it removes a positive prime-pair term. These are exact counterexamples to the corresponding boundary-free identities.

The frozen test plan used X=8,...,512 with h=floor(cuberoot X), h=1,2 at X=8,16,32,64, and held-out X=729,1000,4096,15625. It checked all complete squares, exact rational projection identities, E7, all three halos, prime-containing gcd=1, and the large-GCD partition. A separately preregistered growing-cofactor extension on the SAME cases checked A=floor(X^(1/8)), uniqueness, original signs, its complete residual, E12 and gcd<=A. The finite A values reach only 3 and do not certify uniform growth.

Final execution passed **517 cases**, **517 exact projection checks**, **836387 prime-containing gcd checks**, **461843 growing-source coefficient/admission checks**, and **1253097 growing-source pair checks**. The sieve was independently compared with trial division through 2000. Exact Fraction checks verified both kappa cutoff budgets at b=3/4,4/5,7/8,7/8-10^(-6), and the full return scale conversion. Python syntax compilation passed.

The first run completed its arithmetic checks and then failed one OVERBROAD TEST assertion requiring b-1/100>5/6 also at b=3/4 and 4/5. The corrected test explicitly separates the auxiliary variance domain from the shell-return condition and checks the latter only with eta=(b-5/6)/2 when b>5/6. This failure and repair were retained before rerunning; no source identity, range of scanned arithmetic, or mathematical theorem was weakened.

| Held-out X,h | J | V (prime profile) | Q | A | Q_A | V_A | V_R |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 729,9 | 11645 | 4635 | -2952 | 2 | 4182 | 3283 | 6564 |
| 1000,10 | 18174 | 7044 | -4301 | 2 | 6250 | 4814 | 10488 |
| 4096,16 | 121611 | 48904 | -22058 | 2 | 33404 | 28539 | 83342 |
| 15625,25 | 681181 | 326394 | -104783 | 3 | 200646 | 138483 | 418372 |

The final verifier SHA256 is **45bd31e8ecd7761960b64e0d3dc3f85bdd2e70371cc70da3c499c4f803c6347e**. Its complete code and output are appended below. There was no regression fit, all-scale numerical certificate, numerical zero validation, unsupported OAI simulation, or local Lean execution.

### I. Conceptual Interpretation

Prime regularity and genuine Mobius prefix cancellation do interact quantitatively when their full common-window source is preserved. The useful operation is to average against a smooth prime PROFILE and control its independently bounded fluctuation, not to replace each prime indicator by its density. Keeping the reciprocal cofactor factors makes this survive a polynomially growing cofactor population.

That success does not make the prime population the whole problem. E11 and E13 identify the remaining complementary signed energy exactly; E14 shows that the coherent prefix still carries the incoming endpoint. This explains both why the mixed estimate is a real new source restriction and why an automatic exponent bootstrap would be circular. No existing route is retired or forced to use this representation.

### J. Specialist Handoffs

| Recipient | Precise request |
| --- | --- |
| Referee | Independently reconstruct MP1's finite zero-sum L2 estimate, both kappa budgets, uniform residue/floor conversion, and the external theorem's exact arbitrary-loss scope. Then audit E7/E12, E14 absorption and the non-improvement statement. Treat this author's proof as SELF_AUDIT, not acceptance. |
| Coordinator | Record MP2/MP3 as source-faithful signed component estimates derived from paid baseline plus density, not VERIFIED_ETA. Preserve OPEN-MP-RETURN's equivalence and the coherent b-sized term; do not advertise a smaller global missing lemma. Keep BC/WS as separate OAI work. |
| Lean Verification | After independent acceptance, one small candidate is the finite source/halo/one-leg restoration E6/E7/E12 on realMoebiusStep. Do not prioritize a duplicate projection wrapper without its consumer, and do not encode MP1's analytic input or OPEN-MP-RETURN as a new axiom. The full analytic proof is not currently a compiled library theorem. |
| Prime Census | Do not repeat the printed range or fit the component exponents. A changed useful check is a source-exact decomposition of the residual W_A across a larger cofactor partition, retaining V_R-V_A and all cross terms; preregister the tested structural assertion first. Small A data are not growing-family proof. |
| Owner Payment | MP1 averages COMMON additive windows and their exact dilates; it does not automatically cover PD's reciprocal intervals or conditioned prime-error weights. A transfer requires its own sampling multiplicity and error budget. Preserve PD's original carrier. |
| Finite Wheel | The new small-GCD localization is once-only because p>a and p>d. Investigate a complementary composite restriction only with its true multiplicities and signs; positive support or donor capacity alone is not the missing centered-energy bound. |

These are published asynchronous handoff requests. No other agent was launched or assumed to have reviewed the claims.

### K. First Independently Missing Analytic Theorem

For global progress on this selected representation, the unproved arithmetic input is a joint estimate for the explicitly retained orthogonal composite residual AND coherent weighted prefix at a power strictly below the incoming b. OPEN-MP-RETURN states the sufficient all-H size and exposes its equivalence to the existing local-energy target. This run has not made that target easier merely by naming it.

A nonduplicate next CODIV derivation should use the genuine composite factor dependencies in W_A to constrain the residual interaction in E11 or J_perp, while keeping B. Extending MP3's cofactor range alone will not remove the coherent term; combining many per-ray projection bounds also requires their full signed cross Gram. The exact first unsupported inference is from the proved one-leg contractions to the magnitude of the COMPLETE residual, not the already paid large-GCD sector or the classical density theorem.

### L. Resume Capsule And Publication Discipline

```text
ENGINE_VERSION: SEVEN_AGENT_PERSISTENT_RESEARCH_ENGINE
RUN: 20261108-analytic-1; scheduled 2026-11-08 01:04:01 EST
MAIN: bf4af1cd18aff7c3944a75991aa66371c8afc18a
HIGH_ACK: COMPLETE_SIGNED_HIGH_ATTACK_V1
CHAIN_ACK: CANCELLATION_CHAIN_REUSE_V1
ROUTE: CODIV; genuine common-window Mobius triangular covariance
INCOMING: one fixed source, b=7/8-m/4; #1107 main, actual m>0
REUSE: GL1-GL4 accepted scope; GL2 main #1102; GL3 not Lean
NEW: MP1 variance, MP2 prime mixed compensation, MP3 growing-cofactor
     signed contraction, MP4 retained composite/coherent inverse restriction
SAVINGS: component nu_0>=3/119; nu_(1/8)>=11/952; every-positive-loss
UNIFORM: all integer X large and all 1<=A<=X^(1/8), A fixed within window
NOT_UNIFORM: arbitrary h, moving A(n), conditioned reciprocal populations
COMPLETE_RETURN: J=V_R-V_A+2Q_A; J=J_perp+Q^2/V; all halos retained
FIRST_OPEN: complete residual/coherent power improvement, OPEN-MP-RETURN
STATUS: PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED
COMPUTATION: 517 finite cases; exact code SHA256 in H
ENDPOINT_GAIN: NONE ESTABLISHED; canonical VF and RH OPEN
ROLLING_OWN: NYMAN FT, OAI-NNS BC, CODIV MP; next protected NYMAN
NEXT_NYMAN: resume FT full-basis/correction/infinite-tail obligation, not RM replay
NEXT_OAI: resume BC compatible raw certificate and full class consumer;
          preserve later WS and current stronger total-mass baseline
PUBLICATION: substantive synthesis awaiting commit and immutable readback
PERMISSIONS: own report only; no source/PR/branch/main/schedule/other-report writes
```

The early checkpoint was published as commit **38ded698807c8834525f65e5577483931d43d817**, blob **31716bb1ee57de2f5af5dad7a0624436bad9b09e**, and its full content was verified at that immutable commit. The final synthesis is not called published or COMPLETED until its own commit/readback succeeds. Publication receipts below record actual events only.


### Reproducibility Appendix

The following is the exact executed verifier, including its independently checked sieve, declared finite domains, held-out cases, source restorations, falsification searches and rational exponent arithmetic. It does not test the external zero-density theorem or prove an all-scale estimate. The code is included in the owned report so no separate source or script path is modified remotely.

```python
"""Exact source and exponent checks; no asymptotic theorem is tested by fitting."""

from fractions import Fraction as F
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
import json


def cube_root(n):
    lo, hi = 0, n + 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**3 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def eighth_root(n):
    lo, hi = 0, n + 1
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**8 <= n:
            lo = mid
        else:
            hi = mid
    return lo


def sieve(limit):
    prime = [True] * (limit + 1)
    prime[0] = prime[1] = False
    mu = [1] * (limit + 1)
    mu[0] = 0
    for p in range(2, limit + 1):
        if prime[p]:
            for n in range(p, limit + 1, p):
                mu[n] *= -1
            for n in range(p * p, limit + 1, p * p):
                mu[n] = 0
            for n in range(p * p, limit + 1, p):
                prime[n] = False
    return mu, list(map(int, prime))


def trial(n):
    value, factors, squareful = n, 0, False
    p = 2
    while p * p <= value:
        if value % p == 0:
            factors += 1
            value //= p
            if value % p == 0:
                squareful = True
            while value % p == 0:
                value //= p
        p += 1
    if value > 1:
        factors += 1
    return 0 if squareful else (-1) ** factors


HELD_OUT = (729, 1000, 4096, 15625)
LIMIT = 4 * max(HELD_OUT) + cube_root(max(HELD_OUT))
mu, prime = sieve(LIMIT)
for n in range(1, 2001):
    assert mu[n] == trial(n)
    assert bool(prime[n]) == (n >= 2 and all(n % d for d in range(2, isqrt(n) + 1)))
comp = [a + p for a, p in zip(mu, prime)]
for n in range(2, LIMIT + 1):
    assert abs(comp[n]) <= 1
    assert not prime[n] or comp[n] == 0

prefix_mu, prefix_p = [0], [0]
for a, p in zip(mu, prime):
    prefix_mu.append(prefix_mu[-1] + a)
    prefix_p.append(prefix_p[-1] + p)

counts = {"cases": 0, "prime_pair_gcd_checks": 0, "exact_projection_checks": 0,
          "growing_source_checks": 0, "growing_pair_gcd_checks": 0}
witnesses = {}
held_rows = []
cases = [(x, cube_root(x)) for x in range(8, 513)]
cases += [(x, h) for x in (8, 16, 32, 64) for h in (1, 2)]
cases += [(x, cube_root(x)) for x in HELD_OUT]

for X, h in cases:
    Amax = eighth_root(X)
    fa = [0] * (4 * X + h)
    for n in range(X, 4 * X + h):
        admitted = [a for a in range(1, Amax + 1) if n % a == 0 and prime[n // a]]
        assert len(admitted) <= 1
        fa[n] = -sum(mu[a] for a in admitted)
        assert fa[n] == (mu[n] if admitted else 0)
        counts["growing_source_checks"] += 1
    J = V = Q = CC = PC = 0
    QA = VA = VR = UA_RA = 0
    for n in range(X, 4 * X):
        s = prefix_mu[n + h] - prefix_mu[n]
        p = prefix_p[n + h] - prefix_p[n]
        c = s + p
        J += s * s
        V += p * p
        Q += p * s
        CC += c * c
        PC += p * c
        ua = sum(fa[n:n + h])
        ra = s - ua
        QA += ua * s
        VA += ua * ua
        VR += ra * ra
        UA_RA += ua * ra
    assert J == CC + V - 2 * PC
    assert Q == PC - V
    assert QA == VA + UA_RA
    assert J == VA + VR + 2 * UA_RA == VR - VA + 2 * QA
    assert V > 0
    perp = F(CC) - F(PC * PC, V)
    assert perp >= 0
    assert F(J) == perp + F(Q * Q, V)
    counts["exact_projection_checks"] += 1

    D = sum(mu[n] ** 2 for n in range(X, 4 * X))
    pi = sum(prime[X:4 * X])
    tpp = tpc = tcc = ttotal = mixed_forward = 0
    ge = 0
    fa_forward = h * sum(fa[n] * mu[n] for n in range(X, 4 * X))
    G = max(2, (h + 1) // 2)
    for d in range(1, h):
        w = h - d
        for n in range(X, 4 * X):
            a, z = n, n + d
            pp = prime[a] * prime[z]
            pc = prime[a] * comp[z] + comp[a] * prime[z]
            cc = comp[a] * comp[z]
            term = 2 * w * mu[a] * mu[z]
            tpp += 2 * w * pp
            tpc -= 2 * w * pc
            tcc += 2 * w * cc
            ttotal += term
            mixed_forward += w * (prime[a] * mu[z] + mu[a] * prime[z])
            fa_forward += w * (fa[a] * mu[z] + mu[a] * fa[z])
            if fa[a] or fa[z]:
                assert gcd(n, d) <= Amax
                counts["growing_pair_gcd_checks"] += 1
            if prime[a] or prime[z]:
                assert gcd(n, d) == 1
                counts["prime_pair_gcd_checks"] += 1
                if z >= 4 * X and (pp or pc) and "prime_forward_halo" not in witnesses:
                    witnesses["prime_forward_halo"] = [X, h, n, d, pp, pc]
            if gcd(n, d) >= G:
                assert term == 2 * w * cc
                ge += term
    assert ttotal == tpp + tpc + tcc
    qforward = -h * pi + mixed_forward
    bq = Q - qforward
    bj = J - h * D - ttotal
    bpp = V - h * pi - tpp
    halo = h * (h - 1) * (2 * h - 1) // 3
    assert abs(bq) <= halo
    assert abs(bj) <= halo
    assert abs(bpp) <= halo
    assert abs(QA - fa_forward) <= halo
    assert tpc + 2 * tpp + 2 * h * pi == -2 * Q + 2 * bq
    if 2 <= G <= h:
        assert abs(ge) * G <= 8 * X * h * h
    if bq and "nonzero_mixed_halo" not in witnesses:
        witnesses["nonzero_mixed_halo"] = [X, h, Q, qforward, bq]
    if Q > 0 and "positive_Q" not in witnesses:
        witnesses["positive_Q"] = [X, h, Q, J, V]
    if Q < 0 and "negative_Q" not in witnesses:
        witnesses["negative_Q"] = [X, h, Q, J, V]
    if Q == 0 and J > 0 and "zero_Q_nonzero_J" not in witnesses:
        witnesses["zero_Q_nonzero_J"] = [X, h, Q, J, V, str(perp)]
    if X in HELD_OUT:
        held_rows.append({"X": X, "h": h, "J": J, "V": V, "Q": Q,
                          "T_PP": tpp, "T_PC": tpc, "T_CC": tcc,
                          "B_Q": bq, "J_perp": str(perp), "A": Amax,
                          "Q_A": QA, "V_A": VA, "V_R": VR,
                          "B_A": QA - fa_forward})
    counts["cases"] += 1

A = F(30, 13)
exponents = []
for b in (F(3, 4), F(4, 5), F(7, 8), F(7, 8) - F(1, 10**6)):
    nu = 3 * (1 - b) / (13 + 15 * (1 - b))
    delta = 2 * nu
    v = F(2, 3) + nu
    assert delta == (2 - A * v) * (1 - b)
    assert 0 < nu < F(1, 3) and v < 1 and A * v < 2
    assert delta < 1 - v
    assert b < 1 - nu
    assert delta >= F(6, 119)
    assert 2 - 2 * v - F(2, 3) == -delta
    jpower = F(2, 3) + 2 * b - 1
    shell_power = 1 - F(4, 3) + 2 * jpower
    assert shell_power == 4 * b - 1
    if b > F(5, 6):
        eta = (b - F(5, 6)) / 2
        assert b - eta > F(5, 6)
        assert 1 - F(4, 3) + 2 * (jpower - 2 * eta) == 4 * (b - eta) - 1
    else:
        assert 4 * b - 1 <= F(7, 3)
    kappa = F(1, 8)
    nu_ray = (6 - 26 * kappa) * (1 - b) / (26 + 30 * (1 - b))
    v_ray = F(2, 3) + nu_ray
    assert 2 * nu_ray == (2 * (1 - kappa) - A * v_ray) * (1 - b)
    assert 2 * nu_ray < 1 - kappa - v_ray
    assert 2 * nu_ray < F(2, 3) - 2 * kappa
    assert 2 * nu_ray >= F(11, 476)
    assert v_ray < 1 - kappa and b < 1 - nu_ray
    exponents.append({"b": str(b), "nu": str(nu), "delta": str(delta),
                      "v": str(v), "J_power": str(jpower),
                      "shell_power": str(shell_power), "nu_ray": str(nu_ray)})

# This model only rejects projection-only reasoning; it is not Mobius data.
P = (1, 1)
C = (2, 0)
S = tuple(c - p for c, p in zip(C, P))
assert sum(p * s for p, s in zip(P, S)) == 0
assert sum(s * s for s in S) == 2

print(json.dumps({"counts": counts, "witnesses": witnesses, "held_out": held_rows,
                  "exponents": exponents, "abstract_projection_control": "PASS; not arithmetic",
                  "sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
                  "scope": "FINITE exact checks only; no asymptotic fit or threshold certificate"}, indent=2))
```

Final captured output (exit status 0):

```json
{
  "counts": {
    "cases": 517,
    "prime_pair_gcd_checks": 836387,
    "exact_projection_checks": 517,
    "growing_source_checks": 461843,
    "growing_pair_gcd_checks": 1253097
  },
  "witnesses": {
    "negative_Q": [
      8,
      2,
      -13,
      30,
      14
    ],
    "nonzero_mixed_halo": [
      11,
      2,
      -20,
      -21,
      1
    ],
    "prime_forward_halo": [
      27,
      3,
      107,
      2,
      1,
      0
    ]
  },
  "held_out": [
    {
      "X": 729,
      "h": 9,
      "J": 11645,
      "V": 4635,
      "Q": -2952,
      "T_PP": 2004,
      "T_PC": -3366,
      "T_CC": 1062,
      "B_Q": -3,
      "J_perp": "5028919/515",
      "A": 2,
      "Q_A": 4182,
      "V_A": 3283,
      "V_R": 6564,
      "B_A": 0
    },
    {
      "X": 1000,
      "h": 10,
      "J": 18174,
      "V": 7044,
      "Q": -4301,
      "T_PP": 3188,
      "T_PC": -5440,
      "T_CC": 2182,
      "B_Q": -13,
      "J_perp": "109519055/7044",
      "A": 2,
      "Q_A": 6250,
      "V_A": 4814,
      "V_R": 10488,
      "B_A": 12
    },
    {
      "X": 4096,
      "h": 16,
      "J": 121611,
      "V": 48904,
      "Q": -22058,
      "T_PP": 27540,
      "T_PC": -53738,
      "T_CC": 28302,
      "B_Q": -11,
      "J_perp": "1365177245/12226",
      "A": 2,
      "Q_A": 33404,
      "V_A": 28539,
      "V_R": 83342,
      "B_A": -2
    },
    {
      "X": 15625,
      "h": 25,
      "J": 681181,
      "V": 326394,
      "Q": -104783,
      "T_PP": 215058,
      "T_PC": -442962,
      "T_CC": 196494,
      "B_Q": 144,
      "J_perp": "211353914225/326394",
      "A": 3,
      "Q_A": 200646,
      "V_A": 138483,
      "V_R": 418372,
      "B_A": -28
    }
  ],
  "exponents": [
    {
      "b": "3/4",
      "nu": "3/67",
      "delta": "6/67",
      "v": "143/201",
      "J_power": "7/6",
      "shell_power": "2",
      "nu_ray": "11/536"
    },
    {
      "b": "4/5",
      "nu": "3/80",
      "delta": "3/40",
      "v": "169/240",
      "J_power": "19/15",
      "shell_power": "11/5",
      "nu_ray": "11/640"
    },
    {
      "b": "7/8",
      "nu": "3/119",
      "delta": "6/119",
      "v": "247/357",
      "J_power": "17/12",
      "shell_power": "5/2",
      "nu_ray": "11/952"
    },
    {
      "b": "874999/1000000",
      "nu": "375003/14875015",
      "delta": "750006/14875015",
      "v": "30875039/44625045",
      "J_power": "2124997/1500000",
      "shell_power": "624999/250000",
      "nu_ray": "1375011/119000120"
    }
  ],
  "abstract_projection_control": "PASS; not arithmetic",
  "sha256": "45bd31e8ecd7761960b64e0d3dc3f85bdd2e70371cc70da3c499c4f803c6347e",
  "scope": "FINITE exact checks only; no asymptotic fit or threshold certificate"
}
```

### Verified Publication Receipt

At **2026-11-08 01:33:18 EST (06:33:18 UTC)**, the substantive report was verified at immutable commit **c2cb8f66d8c024efda9be3c834cdac3299413b89**, blob **6f9aaadcfa7f21e7cef6ca06e0b9d7bad6f98e8e**. The returned full text exactly matched the submitted 52,408-character report, including the preserved early checkpoint, complete verifier and captured output. The commit's changed-file list contains only this owned dated report. [Verified substantive report](https://github.com/OVVO-Financial/RH_Lean/blob/c2cb8f66d8c024efda9be3c834cdac3299413b89/research/agent_reports/2026-11-08/20-analytic-type-ii.md).

**Execution/publication status: COMPLETED / PUBLISHED. Mathematical status: PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.** The early IN_PROGRESS and pre-publication entries are preserved as historical checkpoints and superseded by this receipt only for execution/publication status. MP1-MP4 are not certified endpoint gains. The complete residual/coherent estimate, canonical VF objective and RH remain OPEN. The next protected investigator invocation is NYMAN; no future execution or independent review is claimed to have occurred.


---

## Scheduled NYMAN Continuation Checkpoint - 20261108-analytic-2

Execution: PARTIAL / IN_PROGRESS. Actual scheduled trigger: 2026-11-08 09:09:01 EST, America/New_York. RUN_ID_UNAVAILABLE. This is the next actual invocation, not a relaunch of today's earlier CODIV run. All prior MP findings and publication history are preserved.

### A. Selected Analytic Question

Resume 20261107-analytic-2/FT1-FT5 on the complete corrected flat-taper Nyman residue family. Investigate whether the exact two-moment-preserving correction directions requested in 20261108-coordinator-0710-EST can provide a uniform full-norm improvement, including every post-N cell and the infinite tail. A secondary comparison is whether the generic Fourier-spacing return can be sharpened using the actual coefficient structure. Neither question is assumed answered at this checkpoint.

The Coordinator's candidate direction and the elementary projection identity are prior IDENTITY_ONLY inputs, not new results. Any finite descent will be labeled finite and will not be promoted to an exponent gain. The existing moment-null obstruction is preserved.

### B. Authority, Baseline And Source

Main: bf4af1cd18aff7c3944a75991aa66371c8afc18a.
AGENTS: 0a99faf8458809ac772d470d704c5433f373bda8.
CURRENT_PROOF_CONTRACT: d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a.
HIGH directive: be8168b67584d9d8ebbaa732a30c51509137543e.

high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1;
chain_ack=CANCELLATION_CHAIN_REUSE_V1;
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1;
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.

The strongest same-source merged baseline is #1107's
native_mertens_true_physical_slot_minimum_total_mass:
one fixed source D gives b_base=7/8-actualSlotMinimum(D)/4 with every positive loss.
Source VF919TotalMassEndpoint.lean blob 827bb952c4d4311d75fd03a2470799dc10b0f7e7.
The existential slot minimum is not replaced by an invented numerical value.

Original Nyman source blobs:
NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean 2da630c1d5fb9302e2097ec1e170cf41c2b40609;
NYMAN_FLAT_TAPER_RETURN_20261104.lean 2d23721027ecc44e85b7add02fc632b482f03352;
NYMAN_MOMENT_NULL_OBSTRUCTION_20261106.lean 301d7286fc2151b5d33bdca9762a6a01c496ff87.

### C. Continuity And Exact Consumer

All seven November 8 and November 7 reports were retrieved, and applicable latest mathematical summaries, Nyman handoffs and prior FT derivation are being read. TODAY=AVAILABLE for all seven; no scheduled-but-unpublished handoff is invented. The external inbox remains 038018145c0fddb2f6306c0712373adf9cd1ea52 with no entry after October 18. The historical attached role contract's frozen routing/no-write language is superseded by live main and the explicit own-report publication authorization.

Today's upstream results retain their actual scopes: Coordinator SB/WS is an unreviewed OAI candidate; Owner MC is a proper VF mixed-return estimate; Wheel SP, Census TC and Referee DR concern CORR4 sampling; Lean's #1109 is unmerged. They do not supply a Nyman full-norm estimate. Open PRs at intake: #1108 and #1109, both non-draft. Main contains #1107, #1106, #1105 and the earlier Nyman source results. Relevant exact-head CI is being checked separately.

The consumer is the original all-cell norm sum_(m>=1) r(m)^2/[m(m+1)], not a period mean. FT's existing complete-energy power (4b-1)/3 remains a component baseline only; the full-basis approximation and canonical VF/RH endpoints remain OPEN.

### D-L. Work Pending

Perform the new derivation, source/circularity review and a preregistered small finite discriminator with an explicit infinite-tail enclosure. Publish proof, constants, all signed interactions, precise missing theorem and next-run capsule in this exact file. New claims will be SELF_AUDIT / INDEPENDENT_REVIEW_PENDING unless actual independent evidence exists. No local Lean, proof-branch edit, other-role report edit, agent launch or schedule change is authorized or planned.

Protected last turns: November 7 NYMAN FT, November 7 OAI BC, November 8 CODIV MP; this turn is NYMAN. Next distinct route is OAI-NNS. NEW_VERIFIED_ENDPOINT_GAIN=NONE; net_endpoint_gain=UNKNOWN; eta_gate=SEARCH_BROAD.


---

## Complete-Norm Correction Descent And Its Uniform Cost - 20261108-analytic-2

Research synthesis for the scheduled 2026-11-08 09:09:01 EST invocation, America/New_York. RUN_ID_UNAVAILABLE. Prepared after 09:23 EST. This continues the checkpoint above and preserves today's earlier CODIV report. Execution is RESEARCH_FINISHED / PUBLICATION_PENDING_READBACK until a separate verified receipt.

### A. Most Important Analytic Development

**The proposed two-moment-preserving correction really improves the COMPLETE infinite Nyman norm on both prescribed fixtures. There is also a uniform upper bound on how much any well-separated three-denominator step can remove.** The finite success therefore survives the missing-tail objection, but does not establish an asymptotic contraction or a new Mertens exponent.

For the genuine flat-taper family of 20261107-analytic-2/FT, write ell=log(N/H), r_h for the original residual, R=ell*r_h, and E(h)=sum_(m>=1)r_h(m)^2/[m(m+1)]. Assume fixed envelope exponent 1/2<b<1 and the explicit Mertens/psi bounds in D. For H=floor(N^(4/5)) and fixed b>=5/6, the new uniform statement is

```text
sup_(admitted gamma-separated triples) [E(h)-inf_lambda E(h+lambda*d)]
  <<_(b,C_M,C_psi,gamma) N^(2b-1) log^2(N)/ell^2.         (ND-STEP)
```

The supremum includes triples chosen after seeing the genuine coefficients, and lambda ranges over ALL real numbers. It does not include gamma tending to zero, a growing collection of simultaneous directions, or an unbudgeted iteration. D-E give the exact finite bound, constants, all parameter ranges, and proof. A separate unconditional high-support norm bound gives

```text
|sqrt(E(g))-sqrt(E(h))| <= 2*sum|g_k-h_k|/(ell*sqrt(N)).   (ND-MASS)
```

The actual two-band correction has sum|h_k|<=B*N^b. Thus its entire contribution, not merely its first N cells or period variance, has squared norm <=4*B^2*N^(2b-1)/ell^2. This identifies an explicit coefficient-mass cost that any larger correction-based improvement must pay.

The two original-source finite certificates are:

| N,H; direction support | Fixed rational lambda | Certified complete decrease in E | Fraction of original E |
| --- | --- | --- | --- |
| 30,8; (16,19,26) | 319343/500000000 | between 0.000094058779 and 0.000094532548 | between 0.4257% and 0.4281% |
| 42,10; (22,27,36) | 6759/12500000 | between 0.000161986871 and 0.000163673720 | between 0.7653% and 0.7742% |

These are rigorous rational/logarithm interval bounds INCLUDING the infinite tail, not double-precision optimization results. The table gives outward rounded intervals. Both signs are positive in the Coordinator's prescribed orientation; no uniform sign is inferred.

| Claim ID | New result and scope | Evidence |
| --- | --- | --- |
| 20261108-analytic-2/ND1 | Uniform full weighted norm of a high-support residue perturbation, with inverse coefficient-mass cost | PAPER_PROOF; elementary lemma, no literature-priority claim |
| ND2 | Exact application to the genuine two-band correction and comparison of all bounded-mass high corrections | PAPER_PROOF; proper-source quantitative control |
| ND3 | Uniform complete-gradient estimate, coercivity, optimal-step ceiling and inverse fractional-descent restriction | PAPER_PROOF; new source-specific quantitative restriction |
| ND4 | Pair-LCM certified infinite-tail enclosure for the actual centered bilinear and quadratic norms | PAPER_PROOF; enabling estimate, distinct from period-average substitution |
| ND5 | Both prescribed full-norm descents; 529 exact covariance checks; four finite-tail checks; separate Gram cross-check | FINITE_COMPUTATION; all-scale extrapolation prohibited |

All NEW paper claims are SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. The projection algebra and two-null-moment direction were already in the Coordinator handoff and are not claimed as discoveries. NEW_VERIFIED_ENDPOINT_GAIN=NONE; VERIFIED_ETA=NONE; net_endpoint_gain=UNKNOWN; eta_gate=SEARCH_BROAD. The conclusion is NOT that high corrections, full-basis NYMAN, or a fixed-factor descent are impossible.

### B. Current Mathematical Objective And Baseline

Intake main is **bf4af1cd18aff7c3944a75991aa66371c8afc18a**. The authority and policy blobs in the checkpoint govern this continuation. The canonical actual-prime von Koch objective remains OPEN. The shared HIGH target uses the exact split M(R^2-1)=L_R+H_R and the paid fixed-cutoff O(R) LOW estimate, not a new LOW assumption.

The strongest applicable inherited main theorem is
`RHLean.Analysis.native_mertens_true_physical_slot_minimum_total_mass` in
[VF919TotalMassEndpoint.lean](https://github.com/OVVO-Financial/RH_Lean/blob/bf4af1cd18aff7c3944a75991aa66371c8afc18a/research/oai_434/VF919TotalMassEndpoint.lean), blob **827bb952c4d4311d75fd03a2470799dc10b0f7e7**. One fixed source D and its actual minimum m_*>0 supply

```text
b0=7/8-m_*/4,      MertensGrowthAtMost(b0).
```

This has every-positive-loss quantifiers. No explicit value for the existential m_* is asserted. The theorem `recalibrated_total_mass_tilt_budget` gives 0<m_*/4<1/960. Choose a fixed b>b0 BEFORE N,H and the triple; the constants below may depend on this choice. The same established zero boundary and a classical explicit formula give the required psi envelope with any positive loss. This is not a new zero-free input, an assertion for every Dirichlet L-function, or licensing from a desired output.

The relevant #1107 source was directly checked at exact tested head **cd8f98fd6ed2dee3fa08f526eb8ac86c94549da5**: all 14 returned check-runs succeeded. The [dedicated total-mass job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42437401175/job/128599096276) reports warning-fatal source/type checks and PASS terminal-axiom audits for the beta, Mertens, fixed-power and full signed-pair endpoints, with only propext, Classical.choice and Quot.sound. Human merge was 2026-11-08T03:26:45Z. This is reused exact-head evidence, not a newly executed whole-main build or certification of ND1-ND5.

### C. Mechanism, Continuity And Novelty

The selected route is the due NYMAN turn, as also requested by 20261108-coordinator-0710-EST. The preceding actual turns were November 7 NYMAN FT, November 7 OAI-NNS BC, and November 8 CODIV MP. Next distinct route: OAI-NNS. This run does not consume its protected coverage by re-auditing OAI counts.

The changed question is whether a legal high correction can materially reduce the entire FT norm. Three pieces are needed, not just a favorable finite derivative: (i) the exact physical size of the correction operator; (ii) a quantitative source-specific bound on its full gradient; (iii) a certificate that restores the infinite tail in the proposed finite tests. The main effort is (ii), using the already supplied Mertens and prime-error envelopes, the actual all-cell floor return, and first-activation coercivity.

All seven November 8 and November 7 reports were retrieved; TODAY=AVAILABLE for every role. Their latest relevant claims and Nyman handoffs were read. Specific continuity retained:

- Coordinator SB/WS concerns a still-unreviewed OAI bulk/window candidate. Its NYMAN three-denominator direction and prescribed fixtures are consumed here, not rebranded as new algebra.
- Today's own MP1-MP6 controls a genuine small-cofactor CODIV mixed term, not this residue norm. November 7 FT1-FT5 supplies the previous complete-energy envelope and the transition-window question; its paper/self-audit status is not upgraded.
- Owner MC1-MC6 restores a positive same-site VF bill and pays a proper mixed term from the incoming baseline. Earlier RS/JT retain chronology and low-zero restrictions; none gives a sign for the current Nyman gradient.
- Wheel SP and Census TC classify genuine CORR4 sampling collisions; Referee DR accepts their scoped parts and treats divisible-root sampling separately. Those findings do not control Nyman coefficients or its full norm.
- Lean's #1109 is an unmerged source/multiplicity result; #1108 is also open and non-draft. Neither is a new Nyman supplier. Previous Nyman flat-return, correction lower-bound, null-obstruction and radical-increment sources remain at their actual scopes.
- The external inbox **038018145c0fddb2f6306c0712373adf9cd1ea52** has no entry after October 18. EXT-20261018-PNT-1, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain their source/boundary and conditional-scope safeguards; no new Nyman handoff is invented.

Current-source searches for Nyman correction norm, triple and LCM-tail routes locate the existing exact return, correction COMPONENT LOWER bound, moment-null obstruction, and the old finite digamma Gram formula. ND1 is elementary Hilbert-space analysis; ND2-ND3 are the new source-specific upper/inverse statements. ND4 is a simple elementary certification tool. No novelty claim is made for finite Gram matrices, orthogonal projection, the covariance identity, partial summation, or the classical Nyman criterion.

### D. Exact Mathematical Formulation

Let N=6K with integer K>=1, and 2<=H<=N/2. Use genuine mu and von Mangoldt psi, retaining prime powers. All coefficient sums below are finite. Set

```text
ell=log(N/H), q_k=log(N/max(H,k)), F_k=mu(k)*q_k,
T(x)=sum_(k<=x) mu(k)*log(x/k)/k,
delta=1-T(H), u=sum_(k<=N)F_k/k, F=sum_(k<=N)F_k,
z=u-delta=T(N)-1, w=2ell+F-delta,
I1=(3K,4K], I2=(5K,6K], s_i=sum_(k in I_i)1/k,
A=(z-s2*w/K)/(s1-s2), Z=(s1*w/K-z)/(s1-s2),
h_k=A*1_I1(k)+Z*1_I2(k),
c_k=(h_k-F_k)/ell                 (2<=k<=N),
rho_k(m)=(m mod k)/k,
r_h(m)=1-sum_(k=2..N)c_k*rho_k(m), R(m)=ell*r_h(m),
E(h)=sum_(m>=1) r_h(m)^2/[m(m+1)].
```

Here R(m) is a scaled residual, not the canonical square index. Both exact moment equations are retained:

```text
sum h_k/k=u-delta,      sum h_k=2ell+F-delta.
```

Define the Hilbert inner product <f,g>=sum_(m>=1)f(m)g(m)/[m(m+1)]. Every finite residue combination is bounded and periodic, so these sums converge absolutely. No assertion of uniform convergence in growing N is needed without an explicit bound.

For ND2-ND3 assume fixed 1/2<b<1, C_M>=1, C_psi>=0, such that for EVERY integer x>=1,

```text
|M(x)|<=C_M*x^b,      |psi(x)-x|<=C_psi*x^b.            (ENV)
```

The first bound also holds for the step M(t) at real t>=1. Define

```text
k_b=(2-b)/(1-b)^2,       l_b=1/[b*(1-b)^2],
B=C_M*((52/3)*k_b+32/b),
A0=2*C_psi+C_M*l_b+2*B,  C0=1+B,
W(N,H)=[A0*((1-b)*log N+log 4)+C0]*N^(b-1)+4H/N.
```

These are explicit; none depends on N,H or the triple. They may diverge as b approaches an endpoint. No unproved uniformity in that limit is asserted.

For ND3 fix gamma>0 before the scale and choose integer

```text
N/2<k1<k2<k3<=N,
k2-k1>=gamma*N,       k3-k2>=gamma*N,
d_(k1)=k1*(k2-k3), d_(k2)=k2*(k3-k1), d_(k3)=k3*(k1-k2),
v(m)=sum d_k*rho_k(m), D_v=<v,v>, B_R=<R,v>.
```

For the actual correction-only modification require all three denominators to lie in I1 union I2. The bounds themselves hold for any triple in the displayed upper half. A nonempty triple domain implies gamma<1/4. Its exact conclusions are

```text
D_v >= d_(k1)^2*(1/k1-1/k2) >= gamma^3*N^3/4 > 0,
|B_R| <= d_(k2)*W(N,H),
0 <= E(h)-inf_(lambda real)E(h+lambda*d)
   = B_R^2/(ell^2*D_v)
   <= 4*N*W(N,H)^2/(gamma^3*ell^2).                    (ND3)
```

The optimizer is lambda_*=B_R/D_v, not a positive step assumed in advance. A useful inverse consequence, for every 0<theta<=1, is

```text
E(h+lambda*d) <= (1-theta)*E(h)
  ==> E(h) <= 4*N*W(N,H)^2/(theta*gamma^3*ell^2).
```

This is a necessary restriction for a large fractional improvement, NOT a theorem that the genuine E(h) exceeds its right side.

### E. Mathematical Derivation

#### E1. The Entire High-Support Operator: ND1

For every integer k>=2, split its squared norm at m=k. On 1<=m<k the residue is m/k, and thereafter it has magnitude at most one. Hence

```text
||rho_k||^2
 <= (k-1)/k^2 + sum_(m>=k)1/[m(m+1)]
 = (k-1)/k^2+1/k < 2/k.
```

For every finite real vector e supported on N/2<k<=N, the Hilbert triangle inequality now gives the uniform, full infinite-norm estimate

```text
||sum e_k rho_k|| <= 2*sum|e_k|/sqrt(N).               (OP)
```

This absolute-value step is affordable because it is applied to a budgeted correction, not to the unknown full arithmetic residual. With the original coefficient normalization, (OP) and the reverse triangle inequality prove ND-MASS. Neither moment constraint is needed for this norm bound; retaining both is necessary for the proposed source modification, not an erased condition.

For example, if E(g)<=(1-theta)E(h), 0<theta<=1, and g-h is supported in the upper half, then

```text
sum|g_k-h_k| >= (ell*sqrt(N)/2)
                    *(1-sqrt(1-theta))*sqrt(E(h)).     (MASS-COST)
```

This is a necessary coefficient-mass cost on the exact source, not a lower bound for E(h) itself.

#### E2. Actual Correction Mass And Complete Return: ND2

Here are the inputs to the inherited FT mass calculation, reconstructed to make dependencies explicit. From ENV and the expansion of 1/zeta(s) at s=1, partial summation gives

```text
sum mu(k)/k=0,      sum mu(k)*log(k)/k=-1,
|T(x)-1| <= C_M*k_b*x^(b-1),      x>=1.
```

The two naturally ordered series converge under b<1; absolute convergence of them is NOT claimed. For the bound use

```text
T(x)-1=sum_(k>x)mu(k)*log(k/x)/k
       =-integral_x^infinity M(t)*(1-log(t/x))/t^2 dt.
```

The integral is absolutely bounded by C_M*x^(b-1)*[1/(1-b)+1/(1-b)^2]. The derivative series is justified locally near s=1 by the Mertens partial-summation integral. These facts are established arithmetic inputs/reconstructed estimates, not a new zero theorem.

Also F=integral_H^N M(t)dt/t, so |F|<=C_M*N^b/b. The explicit two bands satisfy s1>=1/4, s2<=1/5, s1+s2<=8/15, and s1-s2>=1/20. Therefore

```text
sum|h_k|=K*(|A|+|Z|)
 <= (20/3)*N*|z|+(32/3)*|w|
 <= B*N^b.                                           (MASS)
```

For the last line use |z|<=C_M*k_b*N^(b-1), |delta|<=C_M*k_b, and
2ell<=2N^b/b, giving |w|<=C_M*(3/b+k_b)*N^b. Substitution in (OP) proves

```text
||ell^(-1)*sum h_k rho_k||^2 <= 4*B^2*N^(2b-1)/ell^2.
```

Let r_0=1+ell^(-1)sum_(k=2..N)F_k rho_k. The original full residual is EXACTLY r_h=r_0-ell^(-1)sum h_k rho_k, with all cross terms retained. Thus

```text
max(0,sqrt(E(0))-2B*N^(b-1/2)/ell)
 <= sqrt(E(h)) <= sqrt(E(0))+2B*N^(b-1/2)/ell.          (RAW-COMPARE)
```

More generally ND-MASS compares ANY two corrections within a stated mass budget, even if their shapes vary with N. The moment-null unboundedness theorem is respected: without a mass budget, this upper bound permits arbitrarily large later energy.

For the triple-gradient estimate we retain the exact all-cell identity from `nyman_flat_complete_return`, then the standard finite divisor inversion:

```text
R(m)=m-psi(m)-log H-S_H(m)+U_N(m)+sum h_k floor(m/k),
S_H(m)=sum_(k<=H)mu(k)log(H/k)*rho_k(m),
U_N(m)=sum_(N<k<=m)mu(k)log(N/k)*floor(m/k).            (RETURN)
```

This keeps every post-N term and correction floor. |log H+S_H(m)|<=2H follows from sum_(k<=H)log(H/k)<=H-1. To bound U_N, write it as a finite sum over j of tails at m/j. Partial summation gives

```text
|sum_(N<k<=y)mu(k)log(k/N)|
 <= C_M*y^b*(log(y/N)+1/b).
```

The decreasing positive function t^(-b)*(log(y/t)+1/b), 0<t<=y, has integral l_b*y^(1-b). Summing it over j<=m/N yields

```text
|U_N(m)| <= C_M*l_b*m*N^(b-1),   m>=N;
U_N(m)=0,                       m<N.
```

Together with MASS, the correction support k>N/2, and ENV, RETURN gives

```text
|R(m)| <= A0*m*N^(b-1)+2H,            m>=N/2.          (NEAR)
```

For every m, a separate finite-source cap is

```text
|R(m)| <= ell+sum_(k=2..N)|F_k|+sum|h_k|
       <= N+B*N^b <= C0*N.                           (CAP)
```

The coefficient estimate uses q_k<=log(N/k) and sum_(k<=N)log(N/k)<=N-1. CAP is used at infinity, never the nonsummable linear bound NEAR alone.

#### E3. First-Activation Coercivity And Uniform Optimal Descent: ND3

Direct algebra gives sum d_k=sum d_k/k=0. Thus v=-sum d_k floor(m/k), and v=0 before k1. For k1<=m<k2, the upper-half condition implies floor(m/k1)=1 while the other two floors vanish. Consequently v=-d_(k1) there, proving

```text
D_v >= d_(k1)^2*(1/k1-1/k2).
```

The two gaps imply |d_(k1)|>=gamma*N^2/2 and 1/k1-1/k2>=gamma/N, giving the displayed coercivity. This is a lower bound for the actual weighted quadratic cost, not period variance or an assumed invertible Gram matrix.

Since sum d_k=0, the sum of its positive entries equals the sum of the absolute negative entries and equals d_(k2). Each rho lies in [0,1), hence |v(m)|<=d_(k2)<=N^2. Let Y=ceil(N^(2-b)). Split B_R at Y and apply NEAR only on k1<=m<=Y and CAP afterward:

```text
|B_R|/d_(k2)
 <= A0*N^(b-1)*sum_(m=k1..Y)1/(m+1)
       +2H/k1+C0*N/(Y+1)
 <= [A0*((1-b)*log N+log 4)+C0]*N^(b-1)+4H/N
 = W(N,H).
```

Here Y+1<=2N^(2-b), k1>N/2, and the harmonic sum is at most log((Y+1)/k1). Every estimate is uniform in the allowed moving triple and H. It does not rely on independent coefficients, a sign conjecture, or an incomplete-period average.

The old projection identity is valid for the convergent complete norm:

```text
E(h+lambda*d)=E(h)-2lambda*B_R/ell^2+lambda^2*D_v/ell^2.
```

Completing the square proves the optimal lambda and ND3. The inverse fractional-descent statement follows immediately. The optimally added coefficient mass is also controlled:

```text
sum|lambda_* d_k| <= 8*N*W(N,H)/gamma^3.               (STEP-MASS)
```

Thus the unrestricted best SINGLE step itself costs at most O(N^b log N+H) for fixed parameters. This does not authorize repeated steps with the original constants: their changed coefficient mass and all mutual Gram terms must be accounted for anew.

#### E4. Rigorous Infinite-Tail Enclosure: ND4

Set f_k(m)=rho_k(m)-(k-1)/(2k) and a_k=F_k-h_k for 2<=k<=N. The two moment equations imply the exact centering

```text
R(m)=sum a_k f_k(m),      v(m)=sum d_k f_k(m).
```

For k,l>=2 let P=lcm(k,l) and G_kl=(gcd(k,l)^2-1)/(12kl). The existing period covariance is G_kl. One direct proof conditions on the common residue modulo gcd(k,l): the remaining residue coordinates are independent uniform finite coordinates, and their conditional means leave variance (gcd(k,l)^2-1)/12 divided by kl. This is finite counting, not stochastic independence of arithmetic coefficients.

The P-periodic sequence u_m=f_k(m)f_l(m)-G_kl has period sum zero and |u_m|<=1/3. Its partial sums starting ANYWHERE have absolute value <=P/3. Summation by parts against the decreasing physical weight w_m=1/[m(m+1)] gives, for every integer Y>=1,

```text
|sum_(m>Y) f_k(m)f_l(m)/[m(m+1)]-G_kl/(Y+1)|
 <= lcm(k,l)/[3*(Y+1)*(Y+2)].                         (PAIR-TAIL)
```

The vanishing boundary follows from bounded partial sums and w_m->0. For any two finite coefficient vectors a,d, sum PAIR-TAIL with its actual signed mean term and bound only its error. The error is

```text
sum_(k,l)|a_k d_l|lcm(k,l)/[3*(Y+1)*(Y+2)].            (BILINEAR-TAIL)
```

The same formula applies to D_v and ||R||^2. This is not the false statement that a physical window is bounded by its period mean: the signed discrepancy is explicitly retained. No lcm(1,...,N)-sized enumeration or limit of numerical quadrature is needed.

### F. Quantitative Comparison And Complete Endpoint Budget

For H=floor(N^(4/5)), eventually 2<=H<=N/2 and ell is comparable to log N. If b>=5/6, then H/N<=N^(b-1), so ND3 gives ND-STEP. All finite exceptions can be retained separately. The constant depends only on the displayed fixed envelopes and gamma.

At the actual same-source baseline b0=7/8-m_*/4, after explicitly allowing arbitrary small positive losses, the complete correction/one-step energy scale is

```text
q=2b0-1=3/4-m_*/2,
```

whereas FT's current complete FAMILY upper-envelope power is

```text
p=(4b0-1)/3=5/6-m_*/3,
p-q=1/12+m_*/6>0.
```

ND3 supplies an UPPER bound on removable energy. FT supplies an UPPER bound on total energy. **Subtracting these two upper bounds would be invalid.** No claim is made that the genuine E(h) attains the FT exponent, that the new direction cannot improve its true exponent, or that the finite percentages persist.

The correct conditional consequence is: on any sequence on which E(h)/(N^(2b-1)log^2(N)/ell^2)->infinity, no gamma-separated triple can remove a fixed positive fraction. Equivalently, a fixed-fraction successful triple forces E(h) into the smaller ND3 budget. Both follow from the uniform inequality; neither assumes such a sequence exists.

Similarly, RAW-COMPARE shows that corrections with mass O(N^b) cannot change a genuinely larger-than-N^(b-1/2)/ell norm by a fixed relative amount. MASS-COST quantifies the necessary larger coefficient mass if such a reduction is sought. This is a scoped inverse theorem, not a route-wide no-go.

Nothing here pays the entire remaining transition-window source. FT's prefix and remote-tail estimates, complete norm power, and first unresolved interval remain as before. Even a full energy power 2b-1 merely returns the inherited zero boundary b in the previously accepted paired-probe comparison; FT's p returns (1+2b)/3>b. Full Nyman density requires a complete norm tending to zero, not a positive growing power. The two finite descents and ND3 do not imply a better canonical HIGH exponent.

### G. Original-Carrier Bridge, Literature And Formal Scope

The original definitions are `nymanResidue`, `nymanResidual`, `nymanFlatCoefficient`, and the arbitrary-m theorem `nyman_flat_complete_return`. The change is literally h -> h+lambda*d on the existing correction support; genuine mu, low coefficients, all integer sites, both correction moments, weights and every infinite-tail interaction are retained. No selected cell, prime-power term, or post-N floor is removed.

The continuous function phi_k(x)={1/(kx)}-{1/x}/k equals rho_k(m) on 1/(m+1)<x<=1/m. These cells have exactly the physical weights 1/[m(m+1)]. Thus our complete discrete norm is exactly the original L2(0,1) norm, with no continuous/discrete error suppressed. This is not an identification with the VF clipped source, a Mertens square-shell norm, or an ideal-character polynomial.

The integer-dilation closure criterion is a classical result, not a theorem proved in this report; see [Baez-Duarte's primary paper](https://arxiv.org/abs/math/0202141). His [arithmetical Nyman-Beurling paper](https://arxiv.org/pdf/math/0011254) also distinguishes fixed natural approximants from full-space density. Its divergence results for other named families are NOT transferred to this changed flat family without a proved map. The old repository note already contains the discrete digamma Gram formula; our certified computation uses PAIR-TAIL instead, and the formula is only a separate numerical cross-check.

For ENV's psi consequence, [Platt and Trudgian, Lemmas 1-2](https://arxiv.org/pdf/1809.03134) give the truncated explicit formula at half-odd-integers x>exp(60), 50<T<x, and the reciprocal zero-height sum for T>=2*pi*e. Set T=x/2, use the inherited real-part ceiling b0, and absorb log^2 x into a chosen positive exponent loss. Passing to the neighboring integer changes the bound by at most the local von Mangoldt jump and O(1). The finite initial interval is absorbed in C_psi. No finite-height RH verification, density conjecture, or numerical effective value is imported.

Material source ledger, all at the stated main pin:

| Path | Blob SHA / role |
| --- | --- |
| research/NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean | 2da630c1d5fb9302e2097ec1e170cf41c2b40609; original residue/residual and weighted invariant |
| research/NYMAN_FLAT_TAPER_RETURN_20261104.lean | 2d23721027ecc44e85b7add02fc632b482f03352; complete floor return and two-band solver |
| research/NYMAN_CORRECTION_ENERGY_20261105.lean | e5453cd32c3c4ebf9ebf41927bcb92e534b2ece7; COMPONENT lower bound and signed split, not the new full upper bound |
| research/NYMAN_MOMENT_NULL_OBSTRUCTION_20261106.lean | 301d7286fc2151b5d33bdca9762a6a01c496ff87; unbounded unbudgeted correction warning |
| research/NYMAN_RADICAL_INCREMENT_20261106.lean | c5ebb3d5d96898549ad039fd32e1a26955c5b8f8; unchanged increment identities, no new norm estimate |
| research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md | b2775c892edffe920a101651eef6f3581c73c9d4; original norm and existing finite Gram formula |
| research/oai_434/VF919TotalMassEndpoint.lean | 827bb952c4d4311d75fd03a2470799dc10b0f7e7; strongest used merged Mertens input |

No local Lean was run; no source, feature branch, PR, workflow, other-role report or schedule was changed. No newly proved result is labeled PROVED_IN_LEAN.

### H. Falsification And Executed Certificates

ND5 was preregistered before execution on exactly the two Coordinator fixtures, Y=30000, both original correction bands and the full weighted norm. The rival was that restoring the infinite tail could erase a favorable prefix gradient. Both exact interval certificates refute that rival on their stated finite instances only.

Logarithms use the rational atanh series after reducing the argument to [1,2]. With z in [0,1/3], 100 terms have the explicit positive tail bound

```text
0<=log((1+z)/(1-z))-2*sum_(j<100)z^(2j+1)/(2j+1)
 <= 2*z^201/[201*(1-z^2)].
```

All coefficient arithmetic uses rational intervals. Finite weighted sums are integer-rounded at scale 2^120, including signed products; coefficient and summation rounding errors are carried explicitly. PAIR-TAIL restores the infinite part. The lower activation bound verifies that the denominator D_v is positive before division.

Full certified intervals:

| Quantity | N=30,H=8 | N=42,H=10 |
| --- | --- | --- |
| B_R | [0.257612617211,0.258252951052] | [0.618588208471,0.621773020949] |
| D_v | [403.836945922496,403.860839358285] | [1146.903523891113,1147.005532170060] |
| E(h) | [0.022087009757,0.022093189898] | [0.021143269662,0.021164180640] |
| E(h+lambda*d) | [0.021992477210,0.021999131118] | [0.020979595942,0.021002193768] |

Exact checks: 529 full-period covariances for 2<=k,l<=24; four finite-tail discrepancy checks with (k,l)=(2,3),(3,5),(6,7),(7,8); sieve mu independently matched divisor inversion; both moments of d vanish exactly; v vanishes before its first denominator; its first activation and global magnitude bound hold on every computed cell. The script is reproduced below. Syntax compilation of both Python programs also passed; this is not Lean verification.

After the rational certificates succeeded, a disclosed separate double-precision digamma-Gram implementation was run on the SAME two fixtures. It gave B_R approximately 0.257932494034 and 0.620180786011, D_v approximately 403.848906906 and 1146.954231495, and E(h) approximately 0.0220901005950 and 0.0211537327576, all inside the rigorous enclosures. This is a noncertifying coding cross-check, NOT independent mathematical review. No domain enlargement or large exploratory census occurred.

Important boundaries and failed shortcuts:

- Neither the sign of B_R nor a positive all-scale lower bound on B_R^2/D_v follows from two examples.
- Deleting gamma's lower-gap condition invalidates the uniform coercivity constant; nearby denominators are a separate possible mechanism.
- Dropping the correction-mass budget contradicts the existing null-obstruction scope. ND1 does not do that.
- A period covariance is not the weighted norm. PAIR-TAIL includes the indispensable signed error; FT5's old counterexample is not rerun as new work.
- A growing simultaneous correction frame or iterated descent introduces mutual Gram terms and changed budgets. Single-step bounds do not license summing independent credits.
- The generic exact projection identity is prior work. ND3's independently bounded gradient and physical coercivity, not completion of a square alone, are the analytic contribution.

Main verifier SHA256: **d71a3dbf1309251d2b767f5ea9e9b06c4cdc329602234e7ea1d855e08fc1b2dc**.
Canonical result JSON SHA256: **7ee46adee4ef28fda9d15fc37a5d31d02a48d4d2e640716cc3336d017dd2e556**.
Separate noncertifying Gram script SHA256: **28bf52a8ef4bcc883d47204d53984a579a92097424433de468cb7fbd8b5b64e1**.
Preregistration including the disclosed cross-check addendum SHA256: **d9166e0f548f6c2d2e0955b30ee1ec6354c44ea4aef2f15723a1967940f155f2**.

### I. Conceptual Interpretation

The high correction is a controllable operator at its actual physical normalization. Its coefficients can change a period mean substantially while its early activation and decaying physical weights keep its full norm small. That distinction explains why period-mean intuition is unreliable and why coefficient mass, denominator spacing, and the complete gradient are the relevant quantities.

The proposed finite optimization is real, so there is no basis for declaring the direction useless. The all-scale inverse restriction says precisely what would make it useful: a fixed fractional descent from such a triple requires the starting residual already to lie in the smaller budget, or a different geometry/collective construction must be investigated. The present FT upper bound does not tell us which case occurs.

The secondary attempt to replace generic Fourier spacing by genuine-coefficient cancellation did not establish a sharper full window theorem. Its obstruction remains the actual signed transition-window energy, not correction centering or a missing tail identity. No speculative spectral gap is assumed.

### J. Specialist Handoffs

| Specialist | Exact useful request |
| --- | --- |
| Coordinator | Record ND3 as a uniform source-specific inverse restriction and ND5 as successful finite FULL-norm descent. Do not subtract upper envelopes or promote finite percentages. Continue protected rotation; no strategic policy change is requested. |
| Adversarial Referee | Independently check NEAR/CAP, first-activation coercivity, the order of fixed gamma/envelope constants, and PAIR-TAIL's arbitrary-start summation by parts. Check the exact rational verifier. Verdicts must distinguish paper inequalities, finite certificates and the still-open lower-gradient/complete-energy question. |
| Prime Census | The two requested fixtures are now certified with explicit infinite tails. Reproduce independently if desired; do not rerun them as a new discovery. A changed next test should inspect near-colliding triples or a genuinely growing constrained frame, retaining its full Gram and mass cost, with preregistered scale predictions. |
| Lean Verification | After independent review, ND1's full weighted correction estimate and ND3's first-activation coercivity are implementation-sized candidates. ND3's full analytic envelope needs the explicit arithmetic suppliers, not an assumed final bound. Do not duplicate the moment-null or finite projection identities or start a filler PR solely from this report. |
| Owner Payment | ND-MASS is a genuine normalized operator bound for these residues. Transfer to VF only with a proved occurrence/weight map; it does not establish a chronological prime-source mixed sign. |
| Finite Wheel | A potentially useful different NYMAN input is a collective denominator-frame coercivity/gradient theorem with all mutual LCM terms. Existing CORR4 sampling multiplicity is not automatically such a theorem; protect FINITE-AC/CORR4/MU-LIFT coverage. |

### K. First Independently Missing Analytic Theorem

For this proposed correction mechanism, no all-scale LOWER bound on the complete gradient-to-cost ratio has been established. A precise decision problem is whether, for the genuine family and a fixed geometrically separated triple rule or a fully specified larger moment-null frame, one can prove

```text
projection_energy_of_actual_R >= theta * ||R||^2,
theta>0 independent of N,
```

WITH the actual complete Gram, coefficient-mass budget, and all tails. This is a candidate arithmetic statement, not a supplied lemma, not proved by two fixtures, and not claimed to be easier than the remaining family estimate. ND3 restricts the possible single-triple regime; it does not supply this lower bound.

The independently unresolved complete-family estimate remains FT's original transition-window source. Improving only to power 2b-1 does not beat the incoming endpoint. For a genuinely new global result, a valid full-basis/weighted-norm decay or another stronger source-to-endpoint theorem remains necessary. No universal new covariance or inverse-norm prerequisite is imposed on other routes.

Highest-value next NYMAN derivation: use ND2 to separate the fully paid high-correction norm and attack the ORIGINAL low-coefficient transition remainder, or specify a growing moment-null frame whose actual mutual Gram and coefficient growth can be bounded. Do not repeat a fixed triple scan or optimize only a finite prefix.

### L. Resume Capsule And Publication Discipline

Current new claims: ND1-ND4 PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING; ND5 rigorous FINITE_COMPUTATION. No new Lean theorem, full-family exponent improvement, canonical VF bound or RH result. Preserve FT, BC and MP claim IDs and their original evidence status.

Compact HIGH record:

```text
route: NYMAN; actual full residue norm, both correction moments, infinite tail
main: bf4af1cd18aff7c3944a75991aa66371c8afc18a
baseline: native_mertens_true_physical_slot_minimum_total_mass, b0=7/8-m_*/4
existing input: ENV from inherited boundary; exact flat return; true two-band coefficients
new step: full correction operator bound plus uniform actual-gradient/activation restriction
complete return: all m>=1, exact normalized coefficient change, signed Gram and tail enclosure
net endpoint gain: UNKNOWN / no new verified gain
remaining: actual complete-energy or collective-projection arithmetic beyond the baseline
next protected route: OAI-NNS, resume BC retained-certificate/full-consumer work
next NYMAN: genuine transition remainder or fully costed growing null frame
```

All seven today/yesterday report hashes were recorded at retrieval; the original today's own blob before this invocation was b32aa501bff08a8da7ecf387f4e9a168f71ea3e5 and yesterday's own blob was 77f3e5795533041e4356ceb94cb66328da7af27c. The early checkpoint was committed as **5109818d5431b9e3422c786022f2c963bdf3c11b**, blob **a6dfbbdc457749a157fccb87f5b4142eb1c77794**, and exact readback was verified. Final publication requires a fresh own-file blob, preservation of all intervening content and separate immutable readback. A receipt is appended only after that succeeds.

### Two-Day Continuity Ledger

| Role report | November 8 retrieved blob | November 7 retrieved blob |
| --- | --- | --- |
| 00-coordinator-am.md | b6d5c65aed0537efd0018e11dbcd9a72dea3c15a | 00a649b70f851ca193e74e5004d0d3390cf9ca18 |
| 10-owner-payment.md | dc8da662cdafc4bc96bcc3ccb29c3052eb1b4d99 | 933e8eb23e669594cc687059d75147e6267eec8d |
| 20-analytic-type-ii.md | b32aa501bff08a8da7ecf387f4e9a168f71ea3e5 | 77f3e5795533041e4356ceb94cb66328da7af27c |
| 30-finite-wheel.md | 5b56caa1e7b3463510a7257b10a784ccc8798621 | 7739fa5d4cc77f35773b0d4149b2ddd21732a70d |
| 40-prime-census.md | 3cc1bbe7e0d9a80bdcaa630a2fb3c31d4b8f90c8 | 3fae830e34c590d32c31ad77cad3ace833eb3ff5 |
| 50-adversarial-referee.md | 9b691e84eeb8f2f9e2497604dc874935a61d5005 | 426c2abfa5b8926b512e07f05be37692a2416d0b |
| 60-lean-verification.md | 02647045bf731a52b3c726c9ea690b72fa48c274 | ec14e2803af8c1e56123682ee61ed927ed4f9450 |

Coordinator's 00/90 files were identical by their returned directory blob SHAs at retrieval; the 00 content supplied the handoff. The final source refresh at 2026-11-08T14:28:25Z found main unchanged and #1108/#1109 still open, non-draft, at a0c986c0343a56e98b7344268fdc0b74aa885cdb and fedd203158af32b09cb86fd12f04fec33998408e respectively. The tested #1107 endpoint file was directly re-fetched at its exact CI head and its blob matches main.

### Reproducibility Appendix - ND5

The following are the exact executed registration and scripts. The primary verifier uses only the Python standard library. The separate cross-check additionally uses NumPy/SciPy and is explicitly noncertifying. These are report attachments within this own authorized Markdown file; no repository source/script path was changed.

#### Frozen Registration

~~~markdown
# ND5: Frozen Nyman Descent Validation

Prepared before execution for 20261108-analytic-2.

- Original family: N=6K, 2<=H<=N/2; F_k=mu(k)log(N/max(H,k)), two-band correction h on (3K,4K] and (5K,6K], delta=1-T(H), and both exact moments retained.
- Fixed fixtures from Coordinator: (N,H,k1,k2,k3)=(30,8,16,19,26),(42,10,22,27,36).
- Direction: d=(k1(k2-k3), k2(k3-k1), k3(k1-k2)); no denominator outside the original correction support.
- Observables: full inner product B=<R,v>, full quadratic D=<v,v>, full E=||R||^2/ell^2; sign of B, optimum B/D, certified energy decrease at a fixed rational nearby step.
- Rival: apparent prefix descent disappears after the full infinite weighted tail is restored. No preferred sign is assumed.
- Certification: rational logarithm enclosures from the atanh series; integer fixed-point finite sums at 2^120; exact period covariance and a proved LCM tail error. Initial Y=30000. If an interval does not decide a sign, report unresolved; do not expand the domain without recording a reason.
- Negative controls: directions must preserve both moments, v vanishes before k1, first activation v=-d1 on [k1,k2), and deleting moment constraints is outside the theorem. The full-period covariance alone is not used as a physical weighted norm.
- Cross-check: sieve mu against divisor inversion, direct residue versus floor formula for v, period covariance for all pairs k,l<=24, and finite-tail approximation error against a longer exact rational sum for small pairs.
- Scope: finite certificates only, not an all-scale lower bound for the directional gradient or endpoint improvement. All-scale proof is separate and author SELF_AUDIT.

## Disclosed Cross-Check After The Rational Certificates

The initial fixed domain resolved both signs and full descents. Do not enlarge it. Independently evaluate the established finite digamma Gram formula on the same two fixtures using a separate double-precision implementation. This is a noncertifying coding cross-check only; the rational enclosures remain the evidence.
~~~

#### Rational Complete-Norm Verifier

~~~python
"""Rational interval certificates for two original Nyman correction directions."""

from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from math import gcd, lcm
import json


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    @staticmethod
    def point(x):
        return I(F(x), F(x))

    def __add__(self, other):
        other = other if isinstance(other, I) else I.point(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -as_i(other)

    def __rsub__(self, other):
        return as_i(other) + -self

    def __mul__(self, other):
        other = as_i(other)
        products = [self.lo * other.lo, self.lo * other.hi,
                    self.hi * other.lo, self.hi * other.hi]
        return I(min(products), max(products))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = as_i(other)
        assert other.lo * other.hi > 0
        return self * I(1 / other.hi, 1 / other.lo)

    def square(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        return I(F(low), max(self.lo**2, self.hi**2))

    def absmax(self):
        return max(abs(self.lo), abs(self.hi))


def as_i(x):
    return x if isinstance(x, I) else I.point(x)


def atanh_log(z, terms=100):
    value = sum((z**(2*j+1) / (2*j+1) for j in range(terms)), F(0)) * 2
    error = 2 * z**(2*terms+1) / ((2*terms+1) * (1-z*z))
    return I(value, value + error)


@lru_cache(None)
def log_integer(n):
    assert n >= 1
    power = n.bit_length() - 1
    ratio = F(n, 2**power)
    z = (ratio-1) / (ratio+1)
    return power * atanh_log(F(1, 3)) + atanh_log(z)


def mobius(limit):
    mu = [1] * (limit+1)
    prime = [True] * (limit+1)
    mu[0] = 0
    for p in range(2, limit+1):
        if prime[p]:
            for n in range(p, limit+1, p):
                mu[n] = -mu[n]
                if n > p:
                    prime[n] = False
            for n in range(p*p, limit+1, p*p):
                mu[n] = 0
    inverse = [0] * (limit+1)
    inverse[1] = 1
    for n in range(1, limit+1):
        for multiple in range(2*n, limit+1, n):
            inverse[multiple] -= inverse[n]
    assert mu == inverse
    return mu


def covariance(k, j):
    return F(gcd(k, j)**2 - 1, 12*k*j)


def tail_data(left, right, cutoff):
    mean = I.point(0)
    error = F(0)
    for k, ak in left.items():
        for j, aj in right.items():
            mean += as_i(ak) * as_i(aj) * covariance(k, j)
            error += as_i(ak).absmax() * as_i(aj).absmax() * lcm(k, j)
    mean /= cutoff + 1
    error /= 3 * (cutoff+1) * (cutoff+2)
    return mean + I(-error, error), error


def enclosing_decimal(q, digits, upward):
    scale = 10**digits
    scaled = q * scale
    z = scaled.numerator // scaled.denominator
    if upward and F(z) < scaled:
        z += 1
    sign = '-' if z < 0 else ''
    z = abs(z)
    return f'{sign}{z // scale}.{z % scale:0{digits}d}'


def display(value, digits=12):
    value = as_i(value)
    return [enclosing_decimal(value.lo, digits, False),
            enclosing_decimal(value.hi, digits, True)]


def certify(fixture, cutoff=30000):
    n, h, k1, k2, k3 = fixture
    assert n % 6 == 0 and 2 <= h <= n//2
    block = n // 6
    band1 = list(range(3*block+1, 4*block+1))
    band2 = list(range(5*block+1, 6*block+1))
    assert set((k1,k2,k3)) <= set(band1+band2)
    mu = mobius(n)
    ell = log_integer(n) - log_integer(h)
    f = {k: mu[k]*(log_integer(n)-log_integer(max(h,k))) for k in range(1,n+1)}
    th = sum((mu[k]*(log_integer(h)-log_integer(k))/k for k in range(1,h+1)), I.point(0))
    delta = 1-th
    u = sum((f[k]/k for k in f), I.point(0))
    z = u-delta
    w = 2*ell+sum(f.values(), I.point(0))-delta
    s1 = sum((F(1,k) for k in band1), F(0))
    s2 = sum((F(1,k) for k in band2), F(0))
    a_height = (z-s2*w/block)/(s1-s2)
    z_height = (s1*w/block-z)/(s1-s2)
    corr = {k: a_height if k in band1 else z_height if k in band2 else I.point(0)
            for k in range(2,n+1)}
    a = {k: f[k]-corr[k] for k in range(2,n+1)}
    mean_check = ell+sum((a[k]*F(k-1,2*k) for k in a), I.point(0))
    assert mean_check.lo <= 0 <= mean_check.hi
    d = {k1:k1*(k2-k3), k2:k2*(k3-k1), k3:k3*(k1-k2)}
    assert sum(d.values()) == 0
    assert sum((F(v,k) for k,v in d.items()), F(0)) == 0
    vmax = sum(abs(x) for x in d.values())//2
    assert vmax == d[k2]
    scale = 2**120
    p = {}
    eta = F(0)
    for k in a:
        coeff = a[k]/k
        mid = (coeff.lo+coeff.hi)/2
        p[k] = (mid*scale).numerator // (mid*scale).denominator
        error = max(abs(F(p[k],scale)-coeff.lo), abs(F(p[k],scale)-coeff.hi))
        eta += F(k-1,2)*error
    rmax = sum((F(abs(p[k])*(k-1),2*scale) for k in p), F(0))
    bsum = dsum = esum = 0
    for m in range(1,cutoff+1):
        rr = sum(p[k]*(2*(m%k)-(k-1)) for k in p)
        vv = -sum(dk*(m//k) for k,dk in d.items())
        if m < k1:
            assert vv == 0
        if k1 <= m < k2:
            assert vv == -d[k1]
        assert abs(vv) <= vmax
        den = m*(m+1)
        bsum += (rr*vv)//(2*den)
        dsum += (vv*vv*scale)//den
        esum += (rr*rr)//(4*scale*den)
    partial_b = I(F(bsum,scale)-eta*vmax, F(bsum+cutoff,scale)+eta*vmax)
    partial_d = I(F(dsum,scale),F(dsum+cutoff,scale))
    ep = eta*(2*rmax+eta)
    partial_e = I(F(esum,scale)-ep,F(esum+cutoff,scale)+ep)
    tb, eb = tail_data(a,d,cutoff)
    td, ed = tail_data(d,d,cutoff)
    te, ee = tail_data(a,a,cutoff)
    bfull, dfull = partial_b+tb,partial_d+td
    efull = (partial_e+te)/ell.square()
    lower_d = F(d[k1]**2)*(F(1,k1)-F(1,k2))
    assert dfull.lo >= lower_d
    assert bfull.lo*bfull.hi > 0
    optimum = bfull/dfull
    mid = (optimum.lo+optimum.hi)/2
    lam = F(round(mid*10**9),10**9)
    gain = (2*lam*bfull-lam*lam*dfull)/ell.square()
    assert gain.lo > 0
    opt_gain = bfull.square()/(ell.square()*dfull)
    assert gain.lo <= opt_gain.hi
    return {'fixture':fixture,'cutoff':cutoff,'direction':d,
            'B_R':display(bfull),'D':display(dfull),'E_before':display(efull),
            'lambda_star':display(optimum),'lambda_rational':str(lam),
            'certified_gain':display(gain),'E_after':display(efull-gain),
            'gain_fraction':display(gain/efull),'optimal_gain':display(opt_gain),
            'tail_errors_B_D_Escaled':[display(eb),display(ed),display(ee)],
            'first_activation_D_lower':str(lower_d),
            'correction_l1':display(sum((I.point(v.absmax()) for v in corr.values()),I.point(0)))}


def independent_checks():
    checked = 0
    for k in range(2,25):
        for j in range(2,25):
            period = lcm(k,j)
            actual = sum((F(2*(m%k)-(k-1),2*k)*F(2*(m%j)-(j-1),2*j)
                          for m in range(1,period+1)),F(0))/period
            assert actual == covariance(k,j)
            checked += 1
    for k,j in [(2,3),(3,5),(6,7),(7,8)]:
        y,z = 100,2000
        finite = sum((F(2*(m%k)-(k-1),2*k)*F(2*(m%j)-(j-1),2*j)/F(m*(m+1))
                      for m in range(y+1,z+1)),F(0))
        reference = covariance(k,j)*(F(1,y+1)-F(1,z+1))
        bound = F(lcm(k,j),3)*(F(1,(y+1)*(y+2))+F(1,(z+1)*(z+2)))
        assert abs(finite-reference) <= bound
    return {'period_covariances':checked,'finite_tail_checks':4,'status':'PASS'}


if __name__ == '__main__':
    result = {'checks':independent_checks(),
              'fixtures':[certify(x) for x in [(30,8,16,19,26),(42,10,22,27,36)]]}
    encoded = json.dumps(result,sort_keys=True,separators=(',',':'))
    print(json.dumps(result,indent=2,sort_keys=True))
    print('CANONICAL_RESULT_SHA256='+sha256(encoded.encode()).hexdigest())
~~~

#### Separate Noncertifying Gram Cross-Check

~~~python
"""Noncertifying, separate digamma-Gram cross-check of ND5 enclosures."""

import json
import math
import numpy as np
from scipy.special import digamma
from nyman_descent import mobius


def check(n, h, triple):
    mu = mobius(n)
    ks = np.arange(2, n+1, dtype=np.int64)
    ell = math.log(n/h)
    f = np.array([mu[k]*math.log(n/max(h,k)) for k in range(n+1)])
    th = sum(mu[k]*math.log(h/k)/k for k in range(1,h+1))
    delta = 1-th
    u = sum(f[k]/k for k in range(1,n+1))
    z = u-delta
    w = 2*ell+sum(f[1:])-delta
    block = n//6
    band1, band2 = range(3*block+1,4*block+1),range(5*block+1,6*block+1)
    s1,s2 = sum(1/k for k in band1),sum(1/k for k in band2)
    height1,height2 = (z-s2*w/block)/(s1-s2),(s1*w/block-z)/(s1-s2)
    a = np.array([f[k]-(height1 if k in band1 else height2 if k in band2 else 0) for k in ks])
    k1,k2,k3 = triple
    dd = {k1:k1*(k2-k3),k2:k2*(k3-k1),k3:k3*(k1-k2)}
    d = np.array([dd.get(k,0) for k in ks])
    gram = np.zeros((n-1,n-1))
    for i,k in enumerate(ks):
        for j in range(i,len(ks)):
            l = ks[j]
            period = math.lcm(int(k),int(l))
            r = np.arange(1,period+1,dtype=np.int64)
            weights = (digamma((r+1)/period)-digamma(r/period))/period
            raw = np.sum((r%k)/k*(r%l)/l*weights)
            mk,ml = (k-1)/(2*k),(l-1)/(2*l)
            val = raw-mk*math.log(l)/l-ml*math.log(k)/k+mk*ml
            gram[i,j] = gram[j,i] = val
    b = float(a@gram@d)
    quadratic = float(d@gram@d)
    e = float(a@gram@a/ell**2)
    return {'N':n,'H':h,'B_R':b,'D':quadratic,'E':e,
            'lambda':b/quadratic,'optimal_gain':b*b/(quadratic*ell**2),
            'status':'DOUBLE_PRECISION_CROSSCHECK_ONLY'}


if __name__ == '__main__':
    print(json.dumps([check(30,8,(16,19,26)),check(42,10,(22,27,36))],indent=2))
~~~

### Verified Publication Receipt - 20261108-analytic-2

At 2026-11-08T14:29:53Z (09:29:53 EST), the substantive synthesis and exact reproducibility appendix were verified by immutable readback at commit **7f2791ef5ed8e1b92d5d9ab45948ce64a46044be**, content blob **a75704d88154ba482a04b7c2799145b0cb7087e9**. Returned content matched the submitted 105862-character daily report exactly, including the entire prior report prefix. The early checkpoint commit **5109818d5431b9e3422c786022f2c963bdf3c11b** is preserved.

Execution=COMPLETED; substantive report=PUBLISHED_AND_READBACK_VERIFIED. Mathematical status remains ND1-ND4 PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED; ND5 FINITE_COMPUTATION. No new global endpoint gain, RH theorem, source PR or Lean execution is claimed. Main was unchanged at the closeout refresh. Next protected route is OAI-NNS; next NYMAN work must preserve the full signed transition remainder or fully cost a growing constrained frame. This receipt's own publication is separately read back before the final response.


## Scheduled OAI-NNS Checkpoint - 20261108-analytic-3

Trigger: 2026-11-08 17:11 EST (America/New_York). Platform run ID: RUN_ID_UNAVAILABLE. Execution=IN_PROGRESS; mathematical status=PARTIAL; no new result asserted at this checkpoint.

Current actual main is `6144c73b05d5a85e6a9424708986860c6276f60d`; AGENTS blob `bdd5b9f6867ae2d39b74fc966b7f548a9aba3a61`; CURRENT_PROOF_CONTRACT blob `d1d6fd558ee23927bd9f70ffdc375bafd1dbb67a`. All seven November 8 and November 7 role reports have been retrieved, together with external inbox `038018145c0fddb2f6306c0712373adf9cd1ea52`. Today's role reports are PRESENT; missing independent reviews remain PENDING. The external index contains no newer handoff than October 18.

`high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1`; `chain_ack=CANCELLATION_CHAIN_REUSE_V1`; `baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1`; `deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1`. Selected protected route=OAI-NNS, following today's CODIV/NYMAN turns. Canonical VF, finite A, zero-log amplification and RH remain OPEN.

Live PR refresh found no open/draft PRs. #1111 and #1116 are now merged, superseding upstream then-current draft/CI states. Material source interfaces inspected: near-uniform source `32999039fdeea99c58a070c1c4ee9c140720dd44`, window-saturated endpoint `b7b05069ea013d83b2acaa76a8ea2ed932568930`, total-mass endpoint `827bb952c4d4311d75fd03a2470799dc10b0f7e7`. Relevant exact-head CI/type/axiom verification is IN_PROGRESS, not inferred from merge status.

Research plan: consume Coordinator CP1/CP2 with exact source compatibility and current evidence; resume BC1-BC4 retained-half-error/generalized-kappa full-consumer work; identify whether the remaining binding term is the complete count or the principal-window error. Pursue an actual source-level consumer improvement or sharply scoped obstruction, not a repeated scalar cutoff scan or an optimized astronomical slot denominator. Preserve the genuine compensated ideal coefficients, full LOW/HIGH/principal return, and native Mertens transfer. Coordinator WS/SB are existing paper candidates, not new claims of this execution.

No local Lean, proof-source write, feature branch, PR, schedule change or launch of another agent is authorized or performed. The older attached research template's read-only GitHub restriction is superseded only by the current explicit own-report publishing authorization; no broader permission is inferred.
