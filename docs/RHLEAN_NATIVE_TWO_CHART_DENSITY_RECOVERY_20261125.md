# V7 — density-preserving concurrent-coordinate recovery for finite C

**2026-11-25; PR #1213; NATIVE_TWO_CHART_DENSITY_RECOVERY_V7.** User-directed native experiment. Prioritize the original historical finite-C carrier and its one-sided/subpower relaxation. V1–V6 remain available; no new factorial lattice is required here. #1201 remains final completion. No external theorem import, invented witnesses, assumed bound, or RH claim. Identities below have paper proofs; C++/LP checks are finite diagnostics. No new Lean declarations or Lean execution.

## 1. Original historical currency

Let X=R²−1, K=max_{0≤y<R}(M(y)−1)²/(y+1), Q=2M(R−1)−M(X). On [R,X] let z(n)=−mu(n), omitting squareful sites; on [1,R−1] let z(n)=mu(n). The signed sum is Q, equal to the existing historical floor bilinear. Unnormalized first partial moments U,L satisfy Q=U−L and U+L=sum mu(n)^2=6X/pi²+O(R). The total estimate is NOT a bound on either sign. Sources: [finite-C gate](../research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean), [partial moments](../RHLean/Analysis/AlpogeMobiusPartialMoments.lean), [density theorem](../research/MOBIUS_DENSITY_PRESERVING_MULTIPLICATIVE_GRAM_2026_10_11.md), [two-wall obstruction](../research/TWISTED_EULER_TWO_WALL_FINITE_C_LEDGER.md).

Strict finite C asks |Q|≤C R sqrt(K); a sufficient weaker target is |Q|≤C_eps R^(1+eps) sqrt(K). The [one-sided criterion](../research/ALPOGE_MOBIUS_UPM_LPM_ONE_SIDED_FINITE_C_20261121.md) permits a fixed orientation sigma and exponent kappa<1: sigma Q≤C_eps R^(1+eps) K^kappa. Its Landau handoff is paper-level. The two-sided subpower consumer is already in the universal-envelope chain. All signs, prefix, and cutoff stay unchanged.

## 2. Actual two-chart maps and historical core theorem

For squarefree n in [R,X], sort its prime factors p_1<...<p_s. Let i be the first ascending prefix whose product reaches R, and j the descending crossing (suffix beginning at j). Put a=product of factors before j, b=product after i, m=product from j through i. Since disjoint crossing products would have product at least R², j≤i. Thus a,b<R, gcd(a,b)=1, m≥2, n=amb with pairwise coprime factors and z(n)=−mu(a)mu(m)mu(b). The two recovery addresses are a,b; an occurrence can match an opposite-sign occurrence sharing **either numerical address**, including across charts. Sharing an address retains that factor and exchanges its coprime owner. This is not direct single-prime deletion; the isolated upper-half prime obstruction concerns the narrower graph.

**Exact core separation.** If a=1, the suffix without the smallest prime is <R; the prefix without the largest is no larger, so b=1. If b>1 then b>p_j and (m/p_j)b<R forces m<R. Hence ALL cells not incident to 1 have all three factors historical. Their middle cores satisfy maxprime(a)<minprime(m)≤maxprime(m)<minprime(b), mb≥R, ma≥R, (m/minprime(m))b<R, (m/maxprime(m))a<R, amb≤X. These conditions also prove the converse by sorted order. Their signed populations can be obtained from historical squarefree integers and products without post-root prime input.

The central set b=1 is exactly n/P+(n)<R. Writing n=tq, q=P+(n), its signed census is
    C_root = sum_{squarefree t<R} mu(t) [pi(X/t)−pi(max(P+(t),floor((R−1)/t)))]_+,
with P+(1)=1. Its high-prime subpopulation q≥R has addresses (t,1) and exposure N_R(t)=pi(floor(X/t))−pi(R−1). In general largest-prime cofactor t is not the descending address a in the smooth central cells. Keep both. Central and noncentral signed censuses plus M(R−1) reassemble Q.

## 3. Economical recovery and exact cut dual

Use source-to-positive-type arcs of actual occurrence capacity, arcs from each positive type to each incident label, arcs from labels to incident negative types, and negative-type-to-sink arcs of actual negative occurrence capacity. Internal arcs have capacity total mass+1. A type is (unordered label pair, sign). Integral flow expands into disjoint opposite-sign pairs, each occurrence used at most once. This is simultaneous reassignment, not greedy matching or sign-blind independence.

For a label subset J, U_in(J) counts upper tail sites with both labels in J; L_hit(J) counts lower tail sites with at least one label in J. Max-flow/min-cut gives D_U=U_tail−maxflow=max_J (U_in(J)−L_hit(J)); D_L is symmetric. For fixed J, all compatible positive types should be on the source side and every hit negative type must be there, giving exactly that cut cost. Complementation gives d_U(J)=U_tail−L_tail+d_L(J^c). Force label 1 to sink with an infinite arc to test all cuts excluding 1. If both rooted cut maxima vanish, flow matches min(U_tail,L_tail). This does NOT bound imbalance: J=all labels already equals U_tail−L_tail; a central-only arbitrary population passes all noncentral cuts. No principal capacity bound follows from Hall.

The rooted cut conjecture is a local theorem target: for J excluding 1, U_smooth,in(J)≤L_smooth,hit(J)+sum_{a in J,mu(a)=−1}N_R(a), and the opposite orientation. It is not a global bound.

## 4. Verified finite recovery

Exact integer results reproduced with g++ -O3 -std=c++17 -Wall -Wextra -Werror. Historical prefix separately paired, so U*,L* include its residual; pairs is tail flow.

| R | tail U | tail L | label types | pairs | U* | L* | Q |
|---:|---:|---:|---:|---:|---:|---:|---:|
|64|1235|1217|119|1217|18|1|17|
|317|30463|30438|1551|30438|25|3|22|
|1027|320106|320477|10191|320106|0|375|−375|
|2048|1274184|1274405|31070|1274184|7|221|−214|
|4096|5098290|5098520|96835|5098290|0|249|−249|

Both rooted cut maxima zero at every R=2..512 (1022 exact min-cuts) and all five selected roots (10 further cuts, overlap of 64 and 317 intentional). Not a universal proof. Earlier conversational greedy-order counts are not included as reproduced evidence. At R4096 noncentral count 1,538,789 signed +3333, central count 8,658,021 signed −3563, high-prime count 7,535,209 signed −74141, Q=−249 after prefix. Naive historical Abel cost of fixed chart allocations grows; scalar averaging is insufficient.

## 5. Independent measurement: unsigned density rows

This is the proposed native counterpart to the independent degree/count comparison. Do not define capacity from the known final Q or choose a matching based on its size.

For squarefree d<R define Z_d=#{n≤X : mu(n)^2=1, d|n}; S_d the same restricted to P+(n)<R, S_mu=sum_{n≤X,P+(n)<R}mu(n). H_d=Z_d−S_d. All high sites have n=ap with a<R squarefree and p≥R prime. Hence
    H_d = sum_{a<R,squarefree,d|a} N_R(a).
The triangular incidence matrix on squarefree historical labels has unit diagonal. Its signed decoding vector is c_d=(−2)^omega(d), since sum_{d|a}c_d=mu(a), unique for this complete dictionary. Thus
    Q = 2M(R−1)−S_mu+sum_d c_d(Z_d−S_d).
Each unsigned Z_d has independent center D_d=6X/(pi² product_{p|d}(p+1)) and |Z_d−D_d|≤(2^omega(d)+2)sqrt(X/d) by the coprime-squarefree estimate. Define
    B_R=2M(R−1)−S_mu+sum_d c_d(D_d−S_d)
    E_R=sum_d c_d(Z_d−D_d)
    Q=B_R+E_R.
B_R is frozen-history smooth-sector versus density comparison; E_R is signed density discrepancy. Neither is defined from Q. Their being computable does not prove the bound. Sufficient new estimates: |B_R|+|E_R|≤C_eps R^(1+eps)sqrt(K), or a proved joint fixed-sign comparison. The separate condition could be stronger than necessary.

**Common-coordinate identity.** For squarefree d,
    Z_d=sum_{k²d≤X,(k,d)=1} mu(k) sum_{e|d} mu(e) floor(X/(d e k²)).
Proof: n=dv squarefree iff v is squarefree and coprime to d; expand the squarefree indicator by square-divisor Möbius inversion and the coprime indicator by divisor inversion. All k<R, d,e historical. Every density row uses the SAME signed k-coordinate. Replace floors by their arguments with original limits retained to define the finite real-part center. The finite-floor discrepancy is
    E_floor=sum_{k<R} mu(k) F_R(k)
    F_R(k)=sum_{squarefree d<R,dk²≤X,(d,k)=1} c_d sum_{e|d} mu(e)(floor(X/(dek²))−X/(dek²)).
Keep B_finite=2M(R−1)−S_mu+sum_d c_d(Z_d^real−S_d); Q=B_finite+E_floor. Distinguish finite and infinite centers.

**Proposed economical common-denominator recovery.** Group t=d e k²=u v², u,v squarefree and coprime (squareful k contributes zero). Set d=u j,e=j,k=v/j, j|v. The floor coefficient is (−2)^omega(u) mu(v) sum_{j|v,uj<R}(−2)^omega(j). When uv<R the inner sum equals mu(v), giving the coefficient (−2)^omega(u), exactly the local mu*mu coefficient at uv². On partial faces retain the actual clipped divisor sum. For floor part t≤X makes dk²≤X automatic. For finite real part and fractional errors retain d k²=u v²/j≤X, including t>X terms with zero floor but nonzero real part. This is a concrete shared signed error kernel. Attack complete-face Euler compensation plus clipped-face costs with existing Perron and Co-Div overlap machinery, retaining smooth real comparison. An exact inversion is not a quantitative bound.

## 6. Cost audit: what the test earns, and what remains open

The independent unsigned row error bounds do not suffice directly: the triangle certificate is sqrt(X) sum_d 2^omega(d)(2^omega(d)+2)/sqrt(d). Its prime-only contribution grows like R^(3/2)/log R, a cost of this certificate NOT a lower bound for actual error. Normalized triangle ceiling is 435 at R317, 2772 at R4096. Observed actual absolute row errors cost 1.94 and 4.70 historical budgets. The signed error and history main are both small in these finite samples:

| R | Q | E_R | B_R | E_floor | B_finite | shared-k Abel cost/(R sqrt K) |
|---:|---:|---:|---:|---:|---:|---:|
|317|22|18.840|3.160|39.770|−17.770|9.253|
|1027|−375|−144.802|−230.198|132.191|−507.191|17.471|
|2048|−214|−70.294|−143.706|387.574|−601.574|27.810|
|4096|−249|−446.216|197.216|577.225|−826.225|45.801|

All Z_d historical floor counts and H_d high-fibre reassemblies checked exactly at seven roots 16 through 4096. Irrational density and finite-real centers use long double; numerical diagnostics, not certified intervals. K=1.5 on samples. The shared-k absolute Abel majorant still grows. No uniform subpower estimate has been proved.

Independent-row LP uses exact smooth counts, unsigned density intervals, nonnegativity, monotonicity and trivial prime-count difference caps, not actual high-prime counts in its constraints. At R317 permitted extremes / budget about +24.11 and −25.79; R512 +30.41 and −33.73. Floating LP is a relaxed diagnostic, NOT certified witnesses or asymptotic impossibility. Full exact Z_d inversion determines N_R and Q and cannot itself prove a uniform estimate. Need joint signed common-coordinate error bound or renewable exponent improvement, plus smooth-main comparison; do not infer it from finite recovery. The known finite density-mask and near-orthogonality results must be used only on their actual carriers.

## 7. Seven-role priority on #1213

Prioritize V7 before V6 research selection; retain prior valid results and #1201 final integration. No changes to main, schedules, agent permissions or runtime; this is not an agent invocation.

- COORDINATOR: maintain original Q, central/noncentral and density-row dependency ledger; select independent global signed supplier, distinguish one-sided Landau handoff.
- OWNER: prove actual middle-core and rooted cut conditions, then common signed recovery versus separate row estimates; account for central and smooth real main.
- WHEEL: prove grouped t=u v² coefficients with both clipping boundaries and t>X real tails; recover complete faces by Euler and clipped returns by existing Perron/CRT identities, no averaging incomplete periods.
- ANALYTIC: bound B_R and E_R jointly or separately at subpower historical budget; attack common square-divisor floor-error correlations, retain fixed sign for one-sided criterion and exact finite real correction.
- CENSUS: reproduce CSVs, extend cut tests, test grouped signed errors and denominator tails; exact rational/interval certificates for any LP witness.
- REFEREE: audit circular principal capacity, unearned main estimate, physical occurrence reuse, truncated face errors; test candidate overlap norms and both signs.
- LEAN: reuse existing finite-C and envelope consumers; formalize two-chart factor and exact signed density incidence/inversion first, then only independently earned bounds. One-sided Landau remains unformalized. No invented endpoint or imported RH.

## Reproduction

Compile the four C++ scripts with g++ -O3 -std=c++17 -Wall -Wextra -Werror. Run native_two_chart_recovery, native_two_chart_rooted_cuts (argument small for R=2..512), native_two_chart_global_capacity, native_two_chart_density_capacity. Run native_two_chart_density_lp.py using numpy/scipy (HiGHS). All four C++ diagnostics compiled locally and all assertions passed; small-root mode tested with the equivalent fixed root-vector edit before publication. Python LP ran. Environment lacked lean/lake. New scripts and CSVs are research, not Lean imports. #1201 unchanged.


## V8 follow-on

[Trace the actual numerical core and elementary height-two valuation attack](RHLEAN_NUMERICAL_CORE_HEIGHT_TWO_ATTACK_20261125.md). Local integral constructions and their global cost obstruction, not a new finite-C or RH bound.
