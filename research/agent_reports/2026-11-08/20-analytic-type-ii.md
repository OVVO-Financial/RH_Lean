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

