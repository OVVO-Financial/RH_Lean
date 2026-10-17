# RH_Lean current proof contract

**Live revision: 2026-10-16. Reviewed baseline: `main@df47c8ae0e751ce12bd0e493156a957d86e02ee4` (merged #961; #958/#959 already merged).** Refresh live main on every run. This contract changes research direction, not any Lean definition, theorem, coefficient or proof assumption.

## Unchanged canonical object and open theorem

For x>=4, R=floor(sqrt(x)), the single public real VF is

```text
VF_can(x) = sqrt(2)
  + sum_(2<=r<R) (2*r+1)/log(r^2+r+1/2)
  + (x-R^2)/log((R^2+x)/2).
F_R = vfMidFinishedMass R.
D_can(R) = pi(R^2) - F_R - sqrt(2).
```

The public arithmetic goal remains

```text
VFCanonicalSquareVonKochStatement:
  exists C >= 0, forall R >= 2, |D_can(R)| <= C*R*log(R).
```

Read the exact [canonical interface](research/VF_CANONICAL_SQRT_TWO.lean), [criterion and consumer](research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean), [all-real quadrature](research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean), and [coordinate autopsy](research/VF_CANONICAL_SQRT_TWO_AUTOPSY_2026_10_12.md). Preserve the actual `ClassicalVonKochRHCriterion` or other explicit hypotheses of any terminal consumer.

The global VF_can-Li_2 difference is unconditionally O(1). This does not bound pi-VF_can. Li_2=int_2^x dt/log(t); principal-value li differs by a fixed constant. The sqrt(2) phase is additive and fixed, not the old exact anchor, a multiplicative scale, or a proved uniformly superior pointwise choice.

Legacy raw defect `D_raw(R)=pi(R^2)-F_R` satisfies `D_can=D_raw-sqrt(2)`. Existence of a uniform von-Koch constant is phase invariant through the compiled equivalence; a fixed-K first-bad statement or energy is not. Carry the exact correction `-2*sqrt(2)*D_raw+2` when translating squared defects. Do not modify legacy definitions or original weights.

## Active research disposition after merged #961

Read the live [agent instructions](AGENTS.md), [dynamic protocol](docs/DYNAMIC_RESEARCH_AGENTS.md), [factor-depth/cut-mode brief](docs/FACTOR_DEPTH_RESEARCH_BRIEF.md) and [Mertens budget](docs/MERTENS_AMPLIFICATION_BUDGET.md). The canonical arithmetic objective, original weights and proof consumers are unchanged.

**PROVISIONALLY SUSPEND** unmodified raw-ledger `A+B` regrouping, same-tag/fixed-cofactor matching and a target-size estimate for the complete `B_R` about the **specific smooth B*** defined by the manual cycle. The October 16 cycle reports exact cut cancellation, a root-band Mertens-prime-reciprocal mode and `B-B*` ⇔ RH. The analytic no-go/necessity statements were **paper proofs self-audited by one AI**, not independently refereed; do not upgrade them to an impossibility theorem for every cutoff, arbitrary smooth main term, nonlocal signed transport or masked/clipped first-bad source.

**Current independent candidates:** a genuine signed reduction of the full Mobius `K1/K2/K3` hyperbola floor kernel (a Type II corner is only one proposed input, requiring other terms and full-prefix coverage); a separate Nyman positive-Hilbert norm/decay theorem; and any nonlocal owner/prime input with genuinely different source information and independent quantitative payoff. Finite A/C and CORR-4 remain eligible as distinct alternatives. Retain the full physical zero-target NNS statistic, once-only occurrences, clipped masks, source/anchor restoration and all quadratic mixed terms.

A new result is credited according to exact proof status and quantifier strength, not whether it sounds closer to RH. No canonical endpoint, Mertens exponent or finite A/C bound improved in this cycle.

## Proposed 2026-10-17 Hecke source-payment research contract — draft PR #964

**This subsection is proposed in draft PR #964; until a human merges it, the live main contract above governs automated runs. The unchanged endpoint remains `VFCanonicalSquareVonKochStatement`.** This independent-`7/8` milestone is a benchmark for genuine arithmetic savings, NOT a new assertion of `lambda_M <= 7/8` proved by RH_Lean or an equivalent replacement of the canonical goal.

Compiled on main by #919: `a6(n)=1_(gcd(n,6)=1)[mu*(chi_{-3}mu)](n)`, the original 36-period quotient kernel `K`, `M(X)=sum_(m<=X)a6(m)*K(floor(X/m))`. At a large split prime p>=5, `a6(p)=-2` for p=1 mod 3 and 0 for p=2 mod 3; at p^2 the respective coefficients are +1 and -1. This mod-3 character **selects** surviving first-power split primes: it does not supply an oscillating large-prime phase. The existing bounded signed Abel primitive is an exact identity, not a signed variation estimate.

**Two paid independent paper sectors, distinct carriers:**

1. `BAD_y(X)`, the Hecke norm terms divisible by p^2 for some p>y: `|BAD_y(X)|<=2X(1+log X)/y` by `|a6|<=tau`, `|K|<=2` and the prime reciprocal-square sum. With y=floor(X^(1/8)), the bound is `<=4X^(7/8)(1+log X)` for X>=256.
2. The original odd open-square VF physical weight on seats with p^2|n, p>R^(1/4): `0<=H_R^{large square}<=10 R^(7/4)/log R` (elementary paper argument, all R>=2). Original weights and seats are required; **do not identify this with the Hecke BAD carrier or count it as a bound on the whole signed original ledger**.

**Core alternatives, both exact but quantitatively unpaid:**

- `CORE_(floor(X^(1/8)))=sum_(k=0..7)(-2)^k P_k(X;y)` where distinct large primes are split and first power; completed `|CORE|=O_epsilon(X^(7/8+epsilon))` is target-equivalent, not independent progress.
- At `y=floor(sqrt X)`, `BAD_y=0` **exactly**, hence `M(X)=P_0(X;y)-2P_1(X;y)`; `P_1` is a high split-prime `q>sqrt X` sum with cofactor `s<=X/q`. It is a simpler two-layer owner/Hecke interface, but difficult cancellation may be entirely transferred to `P_0`. The exact recurrence `C_q(X)=C_(q^-)(X)-2C_(q^-)(floor(X/q))` generates the large-prime layers. Upper-half split primes `q in (X/2,X]` inject `-2` each and have no local insertion neighbour; only **nonlocal** signed cross-owner/layer response can offset their macroscopic mass.

**Stronger sufficient independent inputs (OPEN):** a uniform bound on the **complete** signed quotient bucket variation `V_X=sum_t|B_X(t)-B_X(t+1)|=O_epsilon(X^(7/8+epsilon))` gives `|M(X)|<=4V_X` through the existing signed Abel theorem. Alternatively, genuine square-shell second moment `sum_(H<=r<2H)delta_r^2=O_epsilon(H^(5/2+epsilon))` for all dyadic H yields Mertens exponent <=7/8 by Cauchy–Schwarz; it is a different, stronger sufficient condition, not the native #915 masked-source statistic. Neither is proved, and neither can be inferred from finite measurements.

**Next-cycle research obligation:** the Coordinator compares the full nonlocal `P_0-2P_1` cofactor/owner Gram, the signed quotient-bucket variation, the seven-layer baseline, and the separate shell-energy route against full K1/K2/K3, Nyman, finite A/C. Each of the seven specialists has a specific parallel assignment in `AGENTS.md` and `docs/DYNAMIC_RESEARCH_AGENTS.md` (same PR). Prove a **new uniform signed restriction** independent of OpenAI's theorem, preserving actual coefficient, physical prime/cofactor occurrence, cutoff, restoration and full covariance; check the R=317 rank obstruction before asserting single-rectangle moment admissibility. Historical first-bad returned admission needs its separate bridge. Keep every actual mathematical/CI status precise.

**Evidence and reproducibility:** [Hecke cutoff research note](research/HECKE_SPLIT_PRIME_CUTOFF_TRADEOFF_20261016.md), [separate shell-energy mechanism](research/INDEPENDENT_SEVEN_EIGHTHS_SQUARE_SHELL_ENERGY_20261016.md), and their C++/Python scripts in PR #964. Their finite census claims are to be independently reproduced before credit. These paper sectors are not automatically Lean compiled, the independent uniform signed core remains **OPEN**, and no improvement of the canonical endpoint is claimed.

## Raw factor-depth ledger and exact scope

For natural R>=3, the raw odd-seat carrier is

```text
C_R = {(r,n): 2<=r<R, r^2<n<(r+1)^2, n odd}.
w_r = (2*r+1)/(r*log(r^2+r+1/2)).
c(r,n) = w_r - 1_Prime(n).
L_R = sum_(C_R) c(r,n).
```

For odd prime tags 5<=q<R^2, let X_R(q) sum `w_floor(sqrt(p*q))` over odd primes p<q with p*q<R^2; put `Y(q)=1-w_floor(sqrt(q))`, `G_R(q)=X_R(q)-Y(q)`, and `T_R=sum_q G_R(q)`. Let H_R be the positive native weight of the remaining composite seats: squareful seats and squarefree seats with at least three prime factors. Perfect squares excluded by the strict block convention must not be silently added.

The reported exact partition is `L_R=T_R+H_R` (`20261015-census-1`, referee accepted on paper). Under these displayed endpoint conventions, telescoping prime counts gives the elementary coordinate relation `L_R=F_R-pi(R^2)+2`, hence `D_can(R)=2-sqrt(2)-L_R`. This paragraph is paper-level algebra, not a newly compiled bridge. Verify its match to native definitions before a Lean/source transfer.

Thus an O(R log R) bound for the total mismatch is the endpoint problem in these coordinates, not an independently paid new lemma. The **masked/clipped first-bad returned-pair carrier remains a separate object**: raw-seat admission or eligible ancestry is not a theorem of returned-cell admission.

The complete square is `L_R^2=T_R^2+H_R^2+2*T_R*H_R`. Keep all within-tag, cross-tag, cross-depth, anchor and restoration interactions when using the full zero-target NNS statistic. This raw square must not be silently substituted for the compressed #915 normalization. A sum of tag squares, local signs or mean-centered empirical correlations is not the global statistic.

## Merged #958: exact one-ninth support and the remaining complete complement

**PROVED_IN_LEAN_ON_MAIN (2026-10-16):** [OddResidualCofactorSupport.lean](RHLean/Proof/OddResidualCofactorSupport.lean) is merged by PR #958. The exact final theorem `RHLean.Proof.nine_mul_canonicalLargestPrimeFactor_lt_sq` says

```text
1<m, Odd(canonicalCofactor m),
IsOddFactorDepthResidual m, m<R^2
  ==> 9*canonicalLargestPrimeFactor m < R^2.
```

The residual predicate explicitly excludes primes, distinct products of two primes and prime squares. This theorem is **not** an implemented set equivalence for the paper raw `H_R`, a signed-weight bound, a returned-cell admission lemma, or a proof of the canonical endpoint statement.

**Raw-paper applications (2026-10-16 Wheel/Census/Referee):** physical positive `H_R` occurrences uniquely have `n=a*q`, odd composite `a>=9`, `q=P+(n)<R^2/9`; the upper tag sector `A_R` consists of prime tags `q>R^2/3`. Hence a tag-preserving direct `A_R`-to-`H_R` transport has no edges. Define `B_R=L_R-A_R`, **including lower tag charges and all `H_R` occurrences**; the proved leading-order statement is `A_R~ -R^2/(3*log R)` and `B_R~+R^2/(3*log R)`, not `A_R+H_R=o(R^2/log R)`. These estimates are PNT-scale only and do not yield `O(R log R)`.

For a fixed finite composite-cofactor set `S`, `H_R(S)/H_R -> 0` is a referee-accepted **PAPER_PROOF**, sharpened for fixed `a` to `H_R(a)~2*R^2/(a*log^2(R^2))`. The cofactor-depth staircase `a^(j+1)>=(R^2)^j => Omega(n)>=j+2` is also a **PAPER_PROOF**. Neither is the Lean content of #958. Reject a fixed-cofactor-only or tag-preserving mechanism **at its stated raw-carrier scope**. The post-#961 manual cycle later showed that pure `A+B` cut reassembly is an identity and provisionally suspended that route absent a genuinely new independently provable signed input; see the newer section below.

At this partition retain `L_R^2=A_R^2+B_R^2+2*A_R*B_R`. At the nested partition retain `L_R^2=T_R^2+H_R^2+2*T_R*H_R`; neither alone is the complete original zero-target NNS returned-cell source. The owner-3 `q -> 3q` distinct-semiprime crossings remain in `T_R`, never reclassify them as `H_R`. A theorem asserting the full residual is `O(R log R)` without a genuinely independent arithmetic input is `TARGET_EQUIVALENT`. MU-LIFT is a separate, still-open route.

## Merged #961 and manually reported cut-mode/Type II results

**PROVED_IN_LEAN_ON_MAIN:** [RootWallCompleteFibre.lean](RHLean/Proof/RootWallCompleteFibre.lean), PR #961 merged, certifies for prime `q>=R` the greatest-prime complete fibre below `R^2`, multiplier `a<q`, non-square property, and explicit odd-residual characterization. Merged #958 separately supplies the one-ninth support theorem. Neither certifies the paper weighted `Phi_R` identity, a native signed/covariance estimate or returned-cell admission.

**Raw `A+B` paper identity** (October 16 Owner, same-session self-audit, independently review before retirement):
```text
x = R^2
A_R = sum_(prime x/3<q<x) (w(q)-1)
B_R = F_R + 2 - pi(x/3) - sum_(prime x/3<q<x) w(q)
L_R = A_R+B_R.
```
`B_R` contains the lower-tag sector and every positive `H_R` seat. The report proposes `|B_R-B*_R|=O(R log R)` **iff RH**, for its exact `B*_R` only. This is `PAPER_PROOF / INDEPENDENT_REVIEW_REQUIRED`, **not** a new independent subgoal, all-model equivalence or Lean theorem.

**Prime reciprocal band** uses `E_prime(y)=sum_(p<=y)1/p-log(log y)-M_Meissel`, which is **not** the Mertens summatory budget `E_mu(B)`. The reported formula for `[R,2R)` is
```text
T_R-M_R^band = F_R*(E_prime(2R-1)-E_prime(R-1)) + rho_R,
rho_R = O(R/log^2 R).
```
The companion `PAPER_PROOF / INDEPENDENT_REVIEW_REQUIRED` argues via a known zeta zero that `T_R-M_R^band` is not `O(R^(3/2-delta))` for fixed positive `delta`. Analytic's extension treats specified `x^theta` bands `1/2<=theta<2/3`. This limits a **band alone relative to that prime-free model**; it is not a universal ban on joint signed cross-band cancellation or explicitly oscillatory main terms.

**Genuine-Mobius hyperbola identity:** for `N=B-1` and `B<=X<B^2`, `M(X)=2M(N)+K1-K2+K3`, with exact summands in the amplification budget. A prospective signed Type II bound for `X/H<ij<=X` within `K3` must specify `H`, all other K3 ranges, `K1/K2`, integer-pair multiplicities, source normalization, full-prefix interpolation and the true input exponent `r<2`. A formal `ij -> X/(ij)` reflection is **not** an integer-lattice involution without a proved map and boundary defects. The corner is a candidate attack, not a proved unique necessary source.

**No quantitative improvement:** canonical endpoint, full zero-target source payment, genuine-Mobius gain, finite A/C, CORR-4 and RH remain OPEN.

## Verified Mertens baseline: do not re-prove the completed coordinate map

Live source, not the overnight report's old queue, is authoritative. PRs #948-#951 and #954 are merged at the reviewed baseline; a stale PR body may still say draft/unmerged.

- [Mertens converse identification](research/MERTENS_CONVERSE_IDENTIFICATION.lean), source blob `c15bdfcb0b050b26e3f0ea54775d8fd61d8af8bb`: `growthAtMost_iff_strip`, `growthExponent_eq_rightmost` and `logLimsup_eq_rightmost` identify the independently defined arithmetic growth exponent, literal natural-number logarithmic limsup and rightmost nontrivial-zero boundary. PR #949 head `982500b01f0f008b1164a172d06d28d14f8171d0` had all ten attached workflows successful. This is the **bidirectional** identification; the converse is no longer open. It gives no new numerical value of the common boundary.
- PR #950 establishes the finite positive-amplitude/complex-strip coordinate map. Constructed strip points are not asserted to be zeta zeros; the height is supplied independently. Zero amplitudes have no finite sample coordinate, while the separate asymptotic coordinate displays `max(1,|M(n)|)` explicitly. Finite lower-cone crossings do not imply a new upper exponent bound.
- [Finite-prefix extension](research/MERTENS_FINITE_PREFIX_EXTENSION.lean), source blob `0474a156e020dd11b32a9c023cc1ac25e48195ce`: in the integer Dirichlet convolution ring, `T(a)=2a-a*a*zetaInt` and `D(a)=1-a*zetaInt` satisfy `D(T(a))=D(a)*D(a)`. Agreement below B propagates below B^2; seed-only iteration reconstructs genuine coefficients. `guarded_interval_extension` consumes an explicitly checked finite anchor margin. Neither result proves an all-scale summatory norm estimate or perpetual guard availability. PR #951's finite computational certificates are not kernel-certified numerical data, and its optimized double-loop implementation is not silently identified with the formal convolution without the stated bridge.
- Merged #954: [signed higher-order lift](research/MERTENS_HEATH_BROWN_SIGNED.lean), blob `bb028fc18b8228412dafa21f990eeb84dc376b95`, proves `heathBrownLift_agrees_below_power`, exact signed geometric/defect formulas and the quadratic Newton specialization. [Signed hyperbola](research/MERTENS_SIGNED_HYPERBOLA.lean) proves the complete finite convolution split with overlap retained. These are exact identities, not an estimate for the remaining signed rows or alternating families. Its sparse artificial-prefix control excludes scalar-prefix-only arguments for arbitrary inputs, not genuine-Mobius estimates using additional arithmetic.

A new arithmetic gain theorem would be quantitative progress. Repackaging `MertensGrowthAtMost(1/2)`, a finite-A/C bound or universal certificate preservation as an assumed input is not. There is no new unconditional seven-eighths or half-exponent estimate in these coordinate/extension results.

## Relaxed MU-LIFT quantitative target

Let `E(B)=max_(1<=n<B)|M(n)|/sqrt(n)>=1`, for integer B>=2. On one chain `B_j=B_0^(2^j)`, an independently established whole-prefix recurrence

```text
E(B_j^2) <= G_j*E(B_j)^r,
1<=r<2 fixed, G_j>=1, log G_j/log B_j -> 0
```

is sufficient. Its normalized logarithmic budget satisfies `u_(j+1)<=(r/2)*u_j+g_j/2`, so u_j->0; full-prefix interpolation yields `MertensGrowthAtMost (1/2)`. Eventual validity and any finite initial budget suffice. The paper proof, polylogarithmic accumulation, target-equivalence audit and r=2/vanishing-gap countermodels are in the [amplification budget](docs/MERTENS_AMPLIFICATION_BUDGET.md); no new Lean theorem is asserted here.

The genuine signed input to seek for each chain member B is

```text
|2*M(B-1)-Q_(B-1)(X)| <= G_j*E(B)^r*sqrt(X)
for every integer B<=X<B^2,
Q_N(X)=sum_(1<=i,j<=N)mu(i)*mu(j)*floor(X/(i*j)).
```

The old prefix is included because G_j>=1, E(B)>=1 and r>=1. An endpoint-only bound needs a separately proved interpolation. A polylogarithmic G is sufficient, not necessary; do not reject a uniform larger subpower loss. Do not infer subpower growth from finite ratios, assume the actual-gain condition, silently vary r toward two, or drop signed overlap to change the arithmetic object. If a fixed-k whole-prefix estimate is independently proved using #954, replace the threshold by r<k; the larger interval and all dependence on k must be accounted for. Consistently squared energy inequalities must be converted to their final amplitude-budget exponent before this comparison.

## Frozen #915 source and no-narrowing safeguards

For the original raw implementation in its proved range, retain

```text
m_R=(2*R+1)/log(R^2+R+1/2), w_R=m_R/R,
P_R=pi((R+1)^2)-pi(R^2),
beta_R=m_R+(1-2*w_R)*P_R,
Source(R)=D_raw(R+1)=D_raw(R)+P_R-m_R,
TotalMass(R)=(|D_raw(R)|+beta_R)^2.
```

The historical fixed-2 first-bad payment is `2*Source(R)^2 <= TotalMass(R)` **under its exact first-bad hypothesis**. Merged #939 audits this condition; it is not an independent positive covariance budget. Merged #938 proves target equivalences for signed-late correction, VF tracking and actual-prime owner-escape admissibility. Check both compiled arrows before calling any reformulation a narrower last lemma.

Do not replace compressed `|D_raw(R)|` by an uncompressed historical absolute mass without the exact lost/restored terms. Owner-cell no-independent-persistence, rank descent and Sector Six reassembly are established infrastructure on their stated carriers, not actual-source admission or the missing uniform estimate. Multi-block child runs cannot be replaced by an unsupported pointwise bad-child selector.

The paper-level original-denominator limsup obstruction `EXT-20261014-5` concerns an **unconditional all-R strict-fraction bound**, not a disproof of a conditional first-bad strategy. Preserve this distinction and its paper status. New signed mechanisms are not excluded by a technique-specific no-go.

## Retained model and local-theorem warnings

Floor-Li's bounded rounding error is by construction, not prime-counting control. Actual-prime/floor-Li, Abel, Duhamel and Volterra transports are exact identities until an independent size estimate is supplied. The continuous-Li density quadratic collision budget is finite; the naive prime-indicator version contains divergent reciprocal-prime mass. The centered sitewise scalar correction has paper asymptotic `-(1/2)*log(log X)+O(1)` (analytic-6). That refutes this local summable correction, not every response-weighted/renormalized mechanism; compare any residual logarithm with the actual permitted endpoint loss.

Local same-tag spacing, sharp four-owner packets and isolated signed inequalities retain their exact local hypotheses. They do not cover unrestricted historical descendants or survive arbitrary quadratic regrouping. The brief records mandatory small regressions and a direct full-depth census. Reuse them; do not rerun unchanged large searches merely to rediscover an accepted obstruction.

## Sufficient alternatives and history

Finite A/C remain unproved sufficient alternatives on their genuine Mertens carrier; consult [scope and assumptions audit](research/FINITE_A_C_VF_ALIGNMENT_2026_10_11.md). Their existence equivalence does not make `Gamma_R<=B*R^2*K_R` an independently known bound. Preserve native K_R, all signed cross-family terms and the actual conditional consumer. Fixed-T density/CRT or ancestry statements need a uniform transfer to growing selected carriers. CORR-4 remains optional and open; its existing conditional Stokes/remainder consumer and #797-#800 no-rediscovery restriction are unchanged.

The entire pre-update contract is preserved **byte-for-byte**, at its original root-relative link depth, in [PROOF_CONTRACT_HISTORY_2026_10_15.md](PROOF_CONTRACT_HISTORY_2026_10_15.md), blob `90510f021cf3dda5ab981fed22e7747306fa80be`. Its older 'route lock', 'binding' and 'single remaining seam' language is historical and superseded by this live portfolio; no archived prose upgrades a theorem. `CURRENT_RESEARCH_HANDOFF.md` and `RESEARCH_ROUTE_REGISTRY.md` remain detailed contextual navigation. Existing Lean source, counterexample modules, original definitions and theorem hypotheses are untouched.

**Open quantitative obligations:** canonical endpoint bound; complete-source signed payment; finite A/C; CORR-4; new uniform Mertens gain/amplitude bound. The completed bidirectional exponent identification is not on that open list. A report must distinguish independently proved structural, quantitative, finite, conditional and formal implementation progress.
