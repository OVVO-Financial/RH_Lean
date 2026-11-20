# Analytic Type II | November 20, 2026

## Opening checkpoint

`20261120-analytic-0104-EST/SQUARE-CHECK` | Scheduled November 20 at 01:04:01 EST (06:04:01Z), America/New_York; RUN_ID_UNAVAILABLE. EXECUTION=IN_PROGRESS/PARTIAL.

Coordinator PORT H.3: on the predetermined JET heads H in G, N=H^2, does an actual zero of the inner Mobius clock near H force or constrain a zero of W within N^(7/8) of N? Investigate a signed arithmetic relation between the two scales, retaining both correction bands and the lower square-root cutoff. A conditional necessary restriction is not existence of infinitely many coincidences or an upper bound for the complete weighted energy. The H=12 miss and the Referee's single-derivative obstruction remain binding. No new result claimed at intake.

Main 6338941bb9d10387e9361ca3ca55468d4c710e4c; AGENTS 500b6daed5e867d19d97c30e43a7a1e7d2055a51; contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038; flat source 2d23721027ecc44e85b7add02fc632b482f03352; ridge profiles 1ce4bde64139395e79b9ceb2fd2a396457d7098a. Reports intake bdc1c610529504f2cfbbca204e81bcc645355fa3, 15 commits since previous intake. November 20 Owner SLICE available; other upstream TODAY=PENDING / November 19 YESTERDAY=CARRY_FORWARD. Latest: PORT, SLICE, PHASELOCK, GATE, CLOCK, ESCAPEMENT, PLATEAU/TWO-WITNESS. External inbox unchanged. No open/draft PR; #1152 human-merged, finite results only.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1. Direct Git tunnel 403; authorized Contents API, new canonical own-role path. RH=OPEN.

## 01:25 EST synthesis | Which factor pairs can move the outer zero?

### A. Main result

At an actual inner crossing near H, an outer zero near N=H^2 requires cancellation between an explicit expression in the inner moments and a signed sum over separated pairs of old factors. The uncertainty from pairs with both factors beyond the inner cutoff is at most `O_T(N^(-3/8)/(log N)^T)` for every fixed T>0, uniformly across the entire prescribed outer window. Each sign of the remaining old-pair sum has a strictly positive limiting mass. Bounding it by absolute values cannot produce a power saving. At three previously known crossing heads, signs of the physical outer clock can already be certified using only Mobius values through H.

Claim key `20261120-analytic-0104-EST/SQUARE`: **SQUARE1** uniform two-new-factor remainder, **SQUARE2** necessary old-pair restriction, **SQUARE3** positive-mass obstruction: PAPER_PROOF, SELF_AUDIT, independent review pending, NOT_FORMALIZED. **SQUARE4**: FINITE_CERTIFICATE on the declared domain only. The factorization itself is inherited, not a new estimate. No infinite sequence of joint crossings, improvement to the native exponent, or full energy bound is proved.

### B. Objective and source

At main `6338941bb9d10387e9361ca3ca55468d4c710e4c`, the canonical target is one C>=0 such that `|pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R` for every integer R>=2. `riemannHypothesis_of_vfCanonicalSquare` also takes `ClassicalVonKochRHCriterion`. PORT H.3 authorizes a necessary arithmetic phase obstruction on the predefined JET selector, not a change of target. The certified native baseline #1119 is `b*=7/8-7/(64 N_pack)` with each positive loss; #949 identifies the Mertens growth exponent with the rightmost zero abscissa Theta. We may fix `Theta<b<1`, in particular b=7/8, in `M(x)=O_b(x^b)`. There is no zero-loss bound at b*. Fixed fine mesh gives N_pack<=N_star by the ceilings at 1/(6 ell) and 1/(3 ell), so this baseline, not #1108, is the comparison.

### C. The two clocks

For integers H>=6 divisible by six, N=H^2=6K, L=log H, let `I=[N-N^(7/8),N+N^(7/8)]`. All finite sums use actual mu and inclusive upper cutoffs. Put M(x)=sum mu(k), m(x)=sum mu(k)/k, Phi(x)=sum mu(k)log(x/k), all over k<=x. Define

```text
delta(x) = 1 - sum mu(k)log(x/k)/k; G = {legal H : delta(y)=0 for some |y-H|<=3}.
tau(x) = 2 gamma - 2 log x + sum mu(k)log^2(x/k)/k = 2 int_x^infty delta(t)dt/t.
v(x) = log x + Phi(x)-Phi(sqrt x); W(x) = tau(x)+A delta(x)-D v(x)/x.
s=log(4/3), t=log(6/5), u=(log^2(2)-log^2(3/2))/2, v0=t^2/2;
A=(u-v0)/(s-t), D=6(s v0-t u)/(s-t), c=-A-D in (0.02633,0.02635).
```

The tau integral is absolutely convergent for b<1 (BAND4); W is continuous. Do not remove Phi(sqrt x). The idea is to predict this entire scalar with coefficients through y, then determine which pairs inside that prefix can actually obstruct a crossing.

### D. SQUARE1: the new factors

Take every real y with |y-H|<=3 and z in I. Throughout, asymptotic claims are for all sufficiently large H, uniformly in these y,z, not just at zeros. Let `a=mu 1_(n<=y)`, `C_y=2a-a*a*1` (Dirichlet convolution, 1 the constant function). In the finite formula for W, including the lower Phi, replace mu by C_y to define W_y. The original Newton lift gives `mu-C_y=(mu-a)*(mu-a)*1`; it vanishes below (floor(y)+1)^2. Here sqrt(z) is below that threshold and z<2y^2, so the third cofactor of any two-new-factor term is exactly 1. Thus, with **ordered** pairs, no coprimality assumption and no squarefree filter on the product,

```text
f(t)=t^2-A t-D t exp(-t); f(0)=0; f'(0)=c.
R_y(z)=W(z)-W_y(z)=sum_{i,j>y, ij<=z} mu(i)mu(j) f(log(z/(ij)))/(ij).
```

R is zero for h=log(z/y^2)<=0. Otherwise h=O(y^(-1/4)). Put `J(t)=sum_(y<i<=y exp(t)) mu(i)/i`, `C(u)=int_0^u J(t)J(u-t)dt`. Termwise integration of the finite sums gives `R=c C(h)+int_0^h f''(h-u) C(u)du`: the contribution to C(u) is the positive part of `u-log(ij/y^2)`. This identity retains the diagonal. The elementary absolute bound is `O(h(h+1/y)^2)=O(N^(-3/8))` since f(0)=0.

For a signed improvement, use Matomaki, Shao, Tao and Teravainen, *Higher uniformity of arithmetic functions in short intervals I: All intervals*, Forum Math. Pi 11 (2023), e29, arXiv:2204.03754v4, Thm 1.1(i), (1.4)-(1.5). Specialize to the constant nilsequence 1 of fixed complexity, epsilon=1/24, X=y and interval length J0=8 y^(3/4). Eventually `y^(5/8+1/24)<=J0<=y^(1-1/24)` and all prefixes used above lie inside this interval. The starred estimate covers every such subinterval as a progression. For each fixed B>0 the unweighted prefix sums are `O_B(J0/log^B y)` (use B>=1 if needed). Partial summation gives `sup|J|=O_B(y^(-1/4)/log^B y)`. Since `|C(u)|<=u sup|J|^2` and f'' is bounded on [0,h], for every fixed T>0

```text
sup_(|y-H|<=3, z in I) |W(z)-W_y(z)| <<_T N^(-3/8)/(log N)^T.
```

The source constant's dependence on T is ineffective. It is not used in any finite certificate. No independence, averaged-head input, zero sum or loss from iterating over heads is involved.

### E. SQUARE2: the old-factor restriction

Let `Z(s)=zeta(1+s), F=1/Z, K0(s)=2/s^3-A/s^2-D/(1+s)^2`. With the ordinary Stieltjes constants gamma_j, define

```text
P(t)=Res_0 exp(ts) K0(s) Z(s)
    =t^3/3+(gamma-A/2)t^2+(-2 gamma_1-A gamma)t+gamma_2+A gamma_1-D.
V(v)=sum_(q<=v) f(log(v/q))/q; g(v)=V(v)-P(log v)-D log(2 pi v)/(2v), v>0.
```

Uniformly for v>=1/2, `|g(v)|<=C/v^2` (absolute C for these fixed A,D). Indeed Euler-Maclaurin on a fixed disk about 0 gives `v^s sum_(q<=v) q^(-1-s)=v^s Z(s)-1/s+(1/2-{v})/v+O(v^(-2))`; the remainder is analytic and uniformly bounded on a slightly larger disk, so its first two derivatives cost the same order. The displayed floor term is constant in s. Stirling on floor(v)! gives `sum_(q<=v)log(v/q)=v-log(2 pi v)/2+O(1/v)` uniformly through integer cutoffs. Combine these for f, and use compactness on [1/2,1]. The log(v)/v term must be retained. References: NIST DLMF 2.10(i), 5.11(i)-(ii), 25.2(ii)-(iii).

Put `ell=log(z/y^2)`, `E_y(s)=y^s(sum_(i<=y) mu(i)i^(-1-s)-F(s))`, `E_j=E_y^(j)(0)`. Here `E_0=m(y), E_1=-delta(y), E_2=tau(y)`. For j<=3, `E_j=O_b(y^(b-1))`: apply partial summation to the tail with weights `log^j(t/y)/t` using M(t)=O_b(t^b); the log-weighted integrals converge at infinity. At an actual inner root E_1=0; m need not vanish. In the next formulas m=m(y), M=M(y). Define

```text
U_y(z) = m^2 P(ell)+(2ell+2gamma-A)m tau(y)+(2/3)m E_3
         + D[(ell+log(2 pi))M^2+2M Phi(y)]/(2z).
B_y(z) = sum_(a,b<=y) mu(a)mu(b) g(z/(ab))/(ab).
Bcore_y(z) = the same ordered sum restricted to z/(ab)<=Q=N^(1/5) and |a-b|>y^(1/5).
```

To verify the reduction off as well as on a root, expand C_y into singles and pairs. The inner cofactor sum for a pair is V(z/(ab)). Its P component combines with the single logarithmic moments by `2a_s-Z a_s^2=F-Z(a_s-F)^2`, where `a_s=sum_(i<=y)mu(i)i^(-1-s)`. The constant residue `Res_0 z^s K0 F=2log z-2gamma-A` cancels the constant part of W. The `1/v` drift sums to the M^2 and M Phi terms above. Exactly,

```text
W(z)=-Res_0 exp(ell s)K0 Z E_y(s)^2 - D[(ell+log(2 pi))M^2+2M Phi(y)]/(2z)
     -B_y(z)+L_y(z)+R_y(z),
L_y(z)=D[Phi(sqrt z)-log z-2 sum_(i<=y)mu(i)log(z/i)]/z.
```

These are Laurent coefficients at 0, not a contour shift. At E_1=0 expansion to degree three gives precisely the first three terms of U_y. The retained lower-clock term satisfies `L_y=O_b(y^(b-2)(1+log y))` by partial summation. For the near-diagonal, at most `O(y^(6/5))` terms each cost `O(y^(-2))` since `|g(z/(ab))|/(ab)<=C ab/z^2`. For `ab<z/Q`, sum that same bound, splitting a at z/(yQ) and using `sum_(b<=w)b<=w^2` for w>=1. The two totals cost `O((1+log Q)/Q^2)`. Thus both discarded regions together cost `O(N^(-2/5)(1+log N))`, even absolutely. At every inner root with |y-H|<=3, uniformly on I, taking fixed b=7/8 gives

```text
W(z)=-U_y(z)-Bcore_y(z)+O_T(N^(-3/8)/(log N)^T).
In particular W(z)=0 implies |U_y(z)+Bcore_y(z)| <<_T N^(-3/8)/(log N)^T.
```

This restriction uses a proper, explicitly delimited set of old pairs. It is not a bound of this order for Bcore alone, nor a sufficient condition for the existence of z.

### F. Size and an absolute-value obstruction (SQUARE3)

Uniformly for the same y,z as H increases (no inner zero required), for **each sign**,

```text
sum_core [ +/- mu(a)mu(b)g(z/(ab))/(ab) ]_+
   --> (1/(2 zeta(2)^2)) int_1^infty |g(v)| log(v) dv/v > 0.
```

Proof: after scaling a,b by y, the kernel `g((z/y^2)/(uv))/(uv)` extends by 0 at the axes, is uniformly O(uv) there, and converges uniformly on the unit square to `g(1/(uv))/(uv)`. Continuity through the integer thresholds follows from f(0)=0. The empirical measures `y^(-1) sum_(a<=y) mu(a) delta_(a/y)` converge weakly to zero by M(x)=o(x) and bounded total variation. With mu^2 in place of mu they converge to Lebesgue measure divided by zeta(2), by `mu^2(n)=sum_(d^2|n)mu(d)` and its `O(sqrt x)` counting error. Approximation by rectangles gives both product-measure limits, with no independence assumption. Take half the absolute sum plus or minus half the signed sum; putting u=exp(-p), v=exp(-q) in the double integral gives the factor log(w) at w=exp(p+q). Use the absolute discarded-region bounds from E. The integral is finite by quadratic decay. It is positive: the log-coordinate derivative of g jumps by c/2 at v=2; all subtracted terms are smooth there. The bounds for c follow directly by interval evaluation of the elementary logarithms. Thus the separated pairs are not small in absolute mass even after removing the diagonal and large cofactors. This is a different carrier from the earlier numerator-layer obstructions.

### G. Return to the original scalar and energy

For bands I1=(3K,4K], I2=(5K,6K], let `s_i=sum_Ii 1/k`, `l_i=sum_Ii log(N/k)/k`, `A_N=(l1-l2)/(s1-s2)`, `B_N=(s1 l2-s2 l1)/(s1-s2)`. Put `p_k=log(N/max(H,k))`, `U=delta(H)-delta(N)`, `h1=(U-s2 v(N)/K)/(s1-s2)`, `h2=v(N)/K-h1`; h(k) takes these values on the two bands and is zero elsewhere. The k=1 term in the solver and repairs at squareful sites stay. Physical coefficients `c_k=(h(k)-mu(k)p_k)/L`, 2<=k<=N, satisfy `sum c_k/k=1, sum c_k=3`. For `r(m)=1-sum c_k(m mod k)/k`, the unreduced norm is `E_H=sum_(m>=1) r(m)^2/[m(m+1)]`. BAND4/JET give exactly

```text
S_H=tau(N)-sum_k h(k)log(N/k)/k
   =tau(N)+A_N delta(N)-6B_N v(N)/N-A_N delta(H).
```

`A_N=A+O(1/N), 6B_N=D+O(1/N)`; on G, `S_H=W(N)+O_b(N^(b-2)+H^(b-2))`. Since `W'(x)=O_b(x^(b-2))` a.e. and W is locally absolutely continuous, a crossing in I gives `S_H=O_b(N^(b-9/8)+N^(b/2-1))`, only `O(N^(-1/4))` at b=7/8. A crossing within 5H instead gives `O_b(N^(b/2-1))`, hence `O(N^(-9/16))` at b=7/8. These refer only to heads with that crossing. The BAND4 subpower band's necessary exponent is `(b*+1/2)/2-1` with every positive loss; satisfying one scalar is not sufficient. For each fixed nontrivial zero rho of real part sigma>1/2 the full Mellin test demands `E_H >= (2sigma-1)(H+1)^(2sigma-1)/|rho|^2`. An unbounded common sequence with `E_H <<_epsilon H^epsilon` for every epsilon>0 would exclude all such zeros. No such norm bound is obtained.

### H. SQUARE4: finite certificates and falsifiers

Certified enclosures for the physical W in units of `10^(-10)`. The sign bounds below use only mu through H, not the computed later signs. For each omitted ordered pair set `t=f(log(z/(ij)))/(ij)`: delete multiples of 4 or 9 in either coordinate; otherwise use `[min(0,t),max(0,t)]` on the diagonal and `[-|t|,|t|]` off it. Add the resulting interval to W_H(z).

| H | inner zero cell | z=N: interval | other z: interval |
|---:|:---|:---|:---|
| 78 | (79,80) | 6084: [-26895,-26894] | 6400: [1222,1928] |
| 96 | (96,97) | 9216: [34810,34811] | 9409: [-50684,-50683] |
| 114 | (116,117) | 12996: [-6039,-6038] | 13225: [20368,20369] |

The intermediate value theorem gives the three known crossings, now from prefix certificates. At 6400 only (79,79) can survive; the unmasked symmetric error radius [1586,1587] exceeds W_H in [1222,1223]. At 8131 the same masked certificate for H=78 gives [90191,393898]. The masked test is inconclusive at the far right endpoint for 96 and 114, although the physical sign is known. At H=6,z=50 the true remainder is [79052,79053], disproving exact prefix equality above the first square. At H=66,z=5884 the prefix [37841,37842] and physical [-3103,-3102] have opposite signs, disproving transfer without a margin on unrestricted heads; 66 is not in G. H=12 remains the prior genuine miss on G. ESCAPEMENT's freely chosen small derivative is compatible with full-band exponent 4Theta-2.

Reproduction: for H in {6,12,66,78,96,114} take z=N, (H+1)^2, (H+2)^2 and N +/- floor(N^(7/8)); add z=50 at H=6 (31 endpoints). Sieve the physical mu by prime sign flips and square deletion; separately factor the prefix by trial division, initialize C_H=2a and subtract a(i)a(j) at every multiple of ij. Evaluate the finite formulas C-D with outward integer grids 10^(-28) and 10^(-37); logs from 75-digit correctly rounded Decimal enlarged by grid cells. Bound gamma by `Harmonic(512)-log(512)-1/(2*512)+1/(12*512^2)-1/(120*512^4)` plus `[0,1/(252*512^6)]`. Bracket inner zeros at integer endpoints, using affinity in log(x) per cell. Both grids passed the physical-versus-prefix-plus-tail tests. A separate floating check of the full residue identity at the integer endpoints and selected real inner cutoffs differed by <1.4e-13 (diagnostic only). Checker SHA256 `c9ece7064d61ed1eb8a68969fc5e9b5f9bdbf2b78ace2ee3e01ec8e23e271ccd`.

The accompanying checker in this invocation's delivery uses only the Python standard library: `python local_analytic_check.py 28` or `python local_analytic_check.py 37`. The repository write is limited to this research report.

### I. Interpretation and route boundaries

The outer clock is predictable to the displayed precision from the inner prefix even without choosing a root. Choosing an actual inner root deletes its first logarithmic moment, not the historical M^2 drift or the separated signed pairs. Two positive limiting masses explain why paying each sign independently cannot settle the remaining comparison. The Newton identity is an actual MU-LIFT to NYMAN bridge for this linear functional only. It does not bound the complete lifted prefix or transfer to the finite wheel `F_R-D_R=li(R^2-1)-pi(R^2-1)` (including virtual d>X), the clipped #915 prime source, native strict-history K_R, or the OAI/NNS Hermitian, conductor, principal and HIGH terms. Fixed physical 47/54 and the Hecke-side restrictions theta_Hecke>3/5 and Re(s)>21/25 are not improved. No strategic pivot.

### J. Specialist handoffs

- Coordinator: PORT H.3's necessary-obstruction alternative is supplied in SQUARE2, pending review. Keep the infinitely-often and full-norm boxes open.
- Owner: independently check the square-root single L_y and the signed `M Phi(y)` and `M^2` terms against the literal two repair bands. SLICE's exceptional-set bound is not every-square control.
- Wheel: test whether a factor restriction acts on the signed cofactor-threshold pairs near ab=z/2. Squarefree density alone pays neither sign.
- Census: on the existing selected-head list, use only mu through H to compare the signed prefix intervals at N,(H+1)^2,(H+2)^2 with the full-power endpoints. Record successes, misses and inconclusive intervals separately, and stratify the signed change at ab=z/2. Fixed outward interval arithmetic, not rounded signs.
- Referee: audit the sign of the single term, the Laurent drift, the starred short-interval transfer at a moving real cutoff and positivity at the first nontrivial cofactor threshold. SQUARE1-3 are not independently accepted yet.
- Lean Verification: after review the finite Newton remainder with ordered pairs and exact lower cutoff is a candidate; do not assume a crossing, the short-interval theorem or any full norm estimate as a new axiom.

### K. First missing theorem

A testable sufficient input strictly narrower than PORT H.3 is an unbounded sequence of H in the pre-existing G for which the prefix intervals at N and (H+j)^2 have opposite strict signs for some j in {1,2}. The signed square-divisibility envelope is defined in H; the trivial envelope here is `O(H^(-3))` because h=O(1/H). In particular at j=1 the first new pair has zero weight. This asks about two fixed tests of early coefficients, not the existence of a zero somewhere in I. We have no recurrence theorem for their signs. As a first diagnostic, separate the signed change from factors crossing `ab=z/2` from the rest, retaining the level U_y; that cusp is real by SQUARE3, but neither dominance nor sign bias follows. H=12 precludes a universal version. Even infinitely many successes would establish only scalar alignment, not subpower energy.

### L. Source receipts and resume capsule

Main paths and blobs beyond the checkpoint: `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean` 79030d70e8d3e0d08eef9bac53fef95c36eca2fb; `research/MERTENS_FINITE_PREFIX_EXTENSION.lean` 131e9af86207a42d4bf6488e3f64c9ce4f97e5df (`newtonLift_eq_moebius_sub_tail`, `newtonLift_prefix_exact`); `research/MERTENS_HEATH_BROWN_SIGNED.lean` af69b4811cf9f523eb7c96fb0ca836b2cdbd1180; `research/NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean` 2da630c1d5fb9302e2097ec1e170cf41c2b40609; ridge geometry 9cfc801b5154245e8925f4247a0390470761f327; clip difference 4cb8f1d2219bf77158afea908f4ce3e4c221695f; prime source b8ae464e9d9e172c731ce518604e67e707b3339d.

Verified evidence retained, not newly proved here: #1152 raw `907105ddda130ef046fbbaab1fc63076cb886b03`, tree `726dae6ed74c212a69923255f77ef36952494810`, run/job `44664507110/136050421713`, seven reports, only propext/Classical.choice/Quot.sound, dependency counts 346/726/734/841/525/568/868. #1151 raw `5fdbbe89dc595a5b14b647e8cf3f9faaf00cfa00`, `44590158125/135793679265` (finite moments/floor profiles); #1149 period and #1150 fixed cutoff are not full-energy theorems. #1119 raw `77ee815846d6d534c866f0752aa33b84c385610a`, `42552018910/128949473700`, `research/oai_434/VF919WindowErrorClosure.lean` f629db1b2b65d6ec042ac9432397d4b6316200c6, `native_mertens_near_uniform_window_error_closed` retains positive-error slots and full native return. #949 raw `982500b01f0f008b1164a172d06d28d14f8171d0`, `38741634035/116444547917`, `growthExponent_eq_rightmost` source 768c8255850bf4074aff265c3fe17a1f5c43979b. No new CI requested, no Lean file edited, no open/draft PR at final authority check.

Continuity, America/New_York: reports snapshot `6bdc88fa0267fe06129d99c66eda7ecca6802fd8` to `bdc1c610529504f2cfbbca204e81bcc645355fa3`: 15 commits, 14 paths, no deletions. November 19 directory tree c213b32e573aff1252c16326bff380683388a802. November 20 Owner `0009/SLICE1-4` 4efb6209fe5bafdd68b3308d6fd3bf65706b2dff after HINGE 85060bbc0910a64ce70a8c418d9fef35b16c768b. Other upstream TODAY=PENDING; YESTERDAY=CARRY_FORWARD: Coordinator `2309/PORT` recovery b107495e974bbf12d6571d646341126a3e7f5dba after JET 6790b8672ac80f6f3a36ca115929cf19f499cfb4; own `1711/PHASELOCK1-4` 62efb52db960cff6ff4ca43497d48589c56bc791 (scoped accept); Wheel `1806/GATE` a20b2ee34f37f8ec7a6d632eb1f7a31521889232 after HALL; Census `1900/CLOCK` 1093df2a14e84551dae3ca8216be7ac6c4bc30a8 after CROSS (CLOCK1-2 accepted, 3-4 scoped); Referee `2013/ESCAPEMENT` e063ee0f793705c9ca823e0a8cee6ddc3b309418 after LENS; Lean `2108/PLATEAU/TWO-WITNESS` 6231b48290c36a43b0f1246b7fbddf692652109c after RAMP (TWO-WITNESS is paper, not an eighth CI theorem). External inbox 7d63d434690d00dffce9c90335d41c4f62d85798: EXT-20261018-PNT-1 retains c=1,p=R; EXT-20261014-5 is all-R, not first-bad. Historical bytewise Nov 13-15 gaps remain CONTINUITY_UNVERIFIED; no inferred missing reports.

`finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1; high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1`. Directive blobs: half 96ad4439ec458af6168f7d9cb3eef5dde291d37c, cross-route e3ae4280438f591f1ffaddd754a1c3a6d35d0691, continuity 7eef0b36c7442be922d9bc99c6b35d853c4f1f4f, publication a9583516fd2e603320c771e32c170132bf0c53e9. Opening commit `fab20695d67ffc0d93365511802d97b0c4ac969c`, blob `896c2bc62ba82fef7acc33d8a6530bd7a7102707`, 1661 bytes verified. Final publication is established by immutable readback, not by this sentence.

**Resume:** preserve SQUARE1's logarithmic error; do not pay the old core by absolute values or re-scan known roots as discoveries. Review SQUARE2 independently, then test the signed q=2 threshold change and the fixed-endpoint sign margin on the predetermined selector. RH=OPEN; no uniform exponent improvement.
