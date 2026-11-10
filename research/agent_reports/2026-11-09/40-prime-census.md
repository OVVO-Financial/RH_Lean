# RH | Prime Census Laboratory - 2026-11-09

## Pre-Registered Cross-Root Test - 20261109-census-1

Execution: IN_PROGRESS. Mathematical status: PENDING. Scheduled trigger 2026-11-09 03:11:02 EST, America/New_York; platform RUN_ID_UNAVAILABLE. This is one actual invocation.

finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.
Pinned main: 8110624150e444964f998676bf54e2e9a3b7e91c.
AGENTS blob: 6695522a45d67fd1e80a7cff1f98d909405036e2.
CURRENT_PROOF_CONTRACT blob: 95566e37c8eaeb99ee680660df4f9d2e06ea5038.
Finite-wheel directive blob: e505f35522b675c6b5b263eac73618d717346973.
Original complete-wheel Lean source blob: ecb482e52deeee5e9b3853592a3ffdace662d2ff.
Initial report snapshot: 136dad6b6c6c401bb5b60f2d59ca85eec5356eae.

The governing target remains ONE C>=0, before every integer R>=2, with |F_R-D_R|<=C R log R, where X=R^2-1, y=R-1, F_R=sum_(d|P_y)mu(d)fract(X/d), D_R=X delta(y)+pi(y)-1-li(X). The certified identity F_R-D_R=li(X)-pi(X) does not supply the missing bound. All virtual divisors remain until Euler compensation.

### Continuity And Changed Question

November 9 Owner FW1-FW6, Analytic SC1-SC6 and Wheel RA1-RA5 are available and their relevant derivations/handoffs have been read. Today's Coordinator, Referee, Lean and prior Census are PENDING; use their November 8 reports as YESTERDAY=CARRY_FORWARD. All seven November 8 latest summaries and the external inbox were retrieved. The inbox has no entry newer than October 18. Preserve old FM's non-Mobius scope, FR's different Mobius carrier, SG's unreviewed paper status, and EC's later merge in #1119. No open/draft PR at intake; recent accepted changes include #1123, #1118, #1121, #1122, #1120 and #1119. No local Lean or new CI is authorized or needed.

Do not repeat the leading owner-bias or root-admission scans. The new question is whether the proper cross-root quadratic error supplies deterministic negative compensation for its TWO linear responses, or whether the full product-boundary shape defeats marginal-sign heuristics.

### Frozen Carrier And Competing Predictions

For each integer R>=8 put A=[R/2,R), B=[R,2R], X=R^2-1, and Omega={(u,v) in A x B:uv<=X}. All lower prime atoms and pq=X are included, p=R excluded, q=R included. Write dnu=dpi-dt/log t and

N = integral_Omega dpi dpi,
C = integral_Omega dli dli,
U = integral_Omega dpi dli,
V = integral_Omega dli dpi,
L_A = U-C, L_B = V-C,
Q = N-U-V+C,
L = L_A+L_B,
N-C = L+Q.

These are proper terms of the original upper owner band, not the complete wheel. Define a0=nu(A), b0=nu(B), c0=a0*b0/2, retaining Analytic SC's constant frequency.

New laboratory hypotheses, NOT attributed to an upstream author:
H_CANCEL: Q*L<=0 for every R>=8; also measure the stronger |L+Q|<=|L|.
H_MODE: Q*c0>=0 for every R>=8.
Rivals: product-boundary shape allows reinforcement and/or reverses the marginal-mode sign. Strictly certified opposite inequalities reject the respective hypotheses; an unresolved interval is not a sign result.

Predeclared discovery range R=8..64; held-out range R=65..256; stress roots 257,317,549,1027,4096. Record smallest violations within the full stated domain, strongest observed margins and all sign changes. No fitted universal constant will be inferred. Track |F-D|/(R log R) only as a finite numerical diagnostic.

### Execution And Verification Plan

Exact prime pairs: sieve plus independent trial division / direct pair enumeration. Evaluate U,V from exact prime endpoints and li differences. Evaluate C independently in two coordinates: nested original hyperbola integration and the product-variable integral

C = integral_(R^2/2)^X log(log(s/R)*log(2s/R)/(log R*log(R/2)))/log s ds.

Derive and document this elementary change of variables; it is a numerical adapter, not a new bound. All comparisons preserve the continuous corner X/R<u<R, whose sharp measure is zero.

Primary sign certificates will use directed decimal intervals, the convergent logarithmic-integral difference series and explicit quadrature error bounds, or exact rational enclosures. A binary64 alternate implementation is an independent diagnostic, not by itself a certificate. Higher precision and finer quadrature will be checked at important extrema. The optional Arb package is unavailable after actual network-denied installation attempts; no Arb execution is claimed.

Check small complete wheels (R=2..16) by exact Fraction arithmetic, separate physical and virtual ledgers then reunite; at larger tested R use the certified compensated floor source, not exponential cube enumeration. Independently check the specific upstream witnesses R=2,3,5,14 and Owner R=10 without repeating unchanged large tables. Preserve historical triangle, finite Euler mass, every other owner and D_R in the full return; reconstruct all six cross terms when squaring a four-part decomposition.

Stop after the registered informative range. If hypotheses fail, preserve minimal certificates and state a corrected structural question. No RH, uniform target bound, independently reviewed paper proof, or Lean certification is claimed in advance.


## Certified Cross-Root Sign Falsifiers - 20261109-census-1/CR

### A. Most Important Mathematical Discovery

**REFUTED, by certified finite computation on actual primes:** neither of the two registered local sign rules holds. At the smallest allowed failure, **R=9**, the proper cross-root quadratic error reinforces the combined linear error even though the constant-frequency term is positive. Both interval discrepancies are negative, so their signs alone do not determine the quadratic sign. R=8 has the same pair of marginal signs but the opposite quadratic sign.

The first failure in the predeclared held-out range is **R=68** for both rules. Across the complete registered 254-root set there are 92 reinforcement events and 88 constant-mode sign reversals. All these signs have numerical enclosures excluding zero. This is a falsification of new laboratory hypotheses, not a correction of a theorem claimed by Owner or Analytic.

There is also a separate overshoot at R=37: Q and the combined linear error have opposite signs, but adding Q increases the magnitude. Thus a favorable cross-product sign alone would not prove contraction even where that sign happens to hold.

**No uniform O(R log R) bound is proved or refuted.** The proper quadratic bound, the complete finite-wheel target, canonical VF, finite A/C, and RH remain OPEN. No new Lean theorem or independently reviewed all-scale paper result is claimed.

| Claim ID | Finding | Evidence |
| --- | --- | --- |
| 20261109-census-1/CR1 | H_CANCEL and H_MODE both fail first at R=9, domain R>=8 | REFUTED; certified numerical enclosures and exact prime enumeration |
| CR2 | Held-out failures at R=68; 254-root sign census with no unresolved signs | FINITE_COMPUTATION |
| CR3 | Opposite-sign overshoot at R=37 | FINITE_COMPUTATION; refutes the corresponding contraction inference |
| CR4 | Complete physical/virtual and cross-language source reconciliation | FINITE_COMPUTATION; verification of existing identities, not a new theorem |
| CR5 | Product-variable quadrature and independent original-coordinate error certificate | PAPER_PROOF of computational adapters; self-audit, not a new analytic saving |

### B. Authority, Provenance, And Formal Scope

Actual trigger: **2026-11-09 03:11:02 EST**, America/New_York, scheduled; platform RUN_ID_UNAVAILABLE. This report completes the same invocation as the checkpoint above. Initial main retrieval was at approximately 08:11 UTC. The main head remains **8110624150e444964f998676bf54e2e9a3b7e91c** at the prepublication refresh. Activation: `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`.

| Governing material | Observed blob SHA |
| --- | --- |
| main:AGENTS.md | 6695522a45d67fd1e80a7cff1f98d909405036e2 |
| main:CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| Complete-wheel seven-agent directive | e505f35522b675c6b5b263eac73618d717346973 |
| docs/DYNAMIC_RESEARCH_AGENTS.md | e8d913ff9663bb5163eaf0eddca9f76e0508a7ef |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

The original definitions inspected are `finiteWheelFract`, `finiteWheelSquareDeterministic`, `vfMidPrefixWheelCounting` on Ioc(0,N), and `vfMidPrefixWheelDensity`, the full finite Euler product. The existing physical/virtual, Euler reciprocal, Legendre, and arbitrary-reference centered equalities are reused, not credited as discoveries. Source: [pinned complete-wheel module](https://github.com/OVVO-Financial/RH_Lean/blob/8110624150e444964f998676bf54e2e9a3b7e91c/research/CompleteSquareRootWheelFractionalBoundary.lean).

For R>=2, X=R^2-1 and y=R-1, preserve

```text
F_R = sum_(d|P_y) mu(d) fract(X/d),
D_R = X delta(y)+pi(y)-1-li(X),
Z_R = F_R-D_R = li(X)-pi(X).
TARGET: exists C>=0, forall integers R>=2, |Z_R|<=C R log R.
```

The constant is fixed before R. The reference is principal-value li, not Li_2. Their derivative measures agree, but their additive anchors must not be silently exchanged in Z_R. The canonical `VFCanonicalSquareVonKochStatement` remains unchanged, and its inspected terminal implication still takes `ClassicalVonKochRHCriterion` explicitly.

Formal evidence was refreshed, not inferred from a report title: #1122 has eleven successful checks attached to head c53e9cf234500aea2605fd2557e638995f380407. The [actual targeted job log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42561949462/job/128980092032) checks out synthetic merge **1e3c182076a6e1a23ef132c41a78b0f26adab507**, compiles with Lean 4.34.1, and prints only propext, Classical.choice, Quot.sound for the two displayed source theorems. The complete-wheel source at that tested checkout was fetched and is byte-identical to current main. The executed compiler script, blob eb3d429b14bf66ba2fba22e55b70ca0048f748c6, explicitly sets `-DwarningAsError=true`. This is reused verified source evidence, NOT a new current-main full build. No local Lean or workflow launch occurred.

Open/draft PR collection: empty at intake and prepublication refresh. Recent main changes #1123, #1118, #1121, #1122, #1120, #1119 were inspected through commit metadata. The new task supersedes yesterday's frozen-Mobius frequency experiment; that carrier is not silently identified with this prime-pair measure.

### C. Registered Hypotheses And Prior Credit

Registration was committed BEFORE arithmetic execution at **0fe84c6ef60dae801f27cd0751f01d0c7ca4ed04**, blob **8c5e81e183bea6a93784a8529e5d9adee3dd3216**, and read back byte-for-byte.

Owner FW1 supplied the signed owner packet and the proper cross-root question. Analytic SC supplied a paper smoothing-error bound and warned that the constant frequency is nonzero. Wheel RA supplied the exact root-admission channel and its noncontraction witnesses. This run measures the previously uncomputed continuous quadratic and BOTH linear terms, rather than repeating their leading-bias or root-count scans.

Registered H_CANCEL: for every R>=8, Q_R L_R<=0. Its stronger contraction version is |L_R+Q_R|<=|L_R|. Registered H_MODE: for every R>=8, Q_R c0_R>=0. These were laboratory candidates, not accepted upstream claims. Competing explanation: the curved product boundary retains spatial discrepancy information absent from either marginal total.

Discovery range: every R=8..64. Held-out range: every R=65..256. Fixed stress roots: 257,317,549,1027,4096. Both hypotheses and all ranges were fixed before output. No constants or ranges were changed to fit the failures.

### D. Exact Carrier And Reconstruction

For R>=8 set A=[R/2,R), B=[R,2R], Omega={(u,v) in A x B:uv<=X}, and dnu=dpi-du/log u. Define

```text
N = integral_Omega dpi(u) dpi(v),
C = integral_Omega dli(u) dli(v),
U = integral_Omega dpi(u) dli(v),
V = integral_Omega dli(u) dpi(v),
L_A=U-C,  L_B=V-C,  L=L_A+L_B,
Q=N-U-V+C,  N-C=L+Q.
a0=nu(A), b0=nu(B), c0=a0*b0/2.
```

These C and L symbols are local to the experiment, not the global bound constant or an older source ledger. The carrier includes p=R/2 if prime, q=R if prime, and every pq=X atom. It excludes p=R. The continuous outer interval ends at X/R, not R. The two orientations U and V remain distinct.

The exact integer count uses actual ordered cross-root prime pairs. Since the two intervals are disjoint, each corresponding semiprime has a unique orientation. Prime-root and closed-product tests are part of the range; at R=12, (11,13) lies exactly on pq=X.

Explicit integration formulas are

```text
U = sum_(prime R/2<=p<R) [li(X/p)-li(R)],
V = sum_(prime R<=q<=2X/R) [li(X/q)-li(R/2)],
C = integral_(R/2)^(X/R) [li(X/u)-li(R)]/log u du.
```

For a second coordinate system put s=uv. The Jacobian is 1/u, and the inner integral is

```text
integral_(R/2)^(s/R) du/[u log u log(s/u)]
  = log(log(s/R)*log(2s/R)/(log R*log(R/2)))/log s.
```

Hence C is the integral of that expression over R^2/2<=s<=X. Substituting s=R^2 w gives a smooth one-dimensional integrand on 1/2<=w<=1-1/R^2. This is a directly derived numerical adapter, not a new prime-distribution theorem.

### E. Executed Results And Smallest Certificates

At R=9, X=80, A has primes {5,7}, B has {11,13,17}, and the admitted pairs are exactly {(5,11),(5,13),(7,11)}. Thus N=3. The two mixed terms are explicitly

```text
U = li(16)+li(80/7)-2li(9),
V = li(80/11)+li(80/13)+li(80/17)-3li(9/2).
```

The following deliberately widened finite-decimal intervals contain the final 70-digit enclosures. Their endpoints are rational; the inequalities are certified by the algorithms and error bounds in G, not by printed decimal agreement.

| Quantity at R=9 | Certified enclosure |
| --- | --- |
| C | [3.5557623910, 3.5557623919] |
| Q | [-0.0010377898, -0.0010377889] |
| L | [-0.5547246030, -0.5547246012] |
| a0 | [-0.407761590, -0.407761589] |
| b0 | [-0.504636560, -0.504636559] |
| c0 | [0.1028857029, 0.1028857031] |
| QL | [0.0005756870, 0.0005756876] |
| Qc0 | [-0.0001067738, -0.0001067736] |
| abs(L+Q)-abs(L) | [0.0010377871, 0.0010377915] |

At the only earlier admissible root R=8, Q is in [0.0114319634,0.0114319644], L is negative, and c0 is positive. Both registered signs hold there, and the amplitude decreases. Therefore R=9 is the smallest counterexample in the exact domain R>=8, not merely the smallest tested in a delayed search.

Independent original-coordinate composite midpoint integration, using an explicit SECOND-derivative bound rather than the primary fourth-derivative Simpson bound, gives at R=9

```text
-0.001055803 < Q < -0.001026135.
```

This separately resolves the small negative sign. It uses the same outward-decimal/log primitive, so it is an independent coordinate/quadrature check, not an independently implemented transcendental arithmetic library.

The full registered census gave:

| Regime | Roots | QL>0 | Qc0<0 | Magnitude increases | Unresolved signs |
| --- | ---: | ---: | ---: | ---: | ---: |
| Discovery, 8..64 | 57 | 28 | 26 | 29 | 0 |
| Held-out, 65..256 | 192 | 64 | 61 | 64 | 0 |
| Five fixed stress roots | 5 | 0 | 1 | 0 | 0 |
| Total | 254 | 92 | 88 | 93 | 0 |

The held-out first failure for both rules is R=68: Q approximately -0.1519591762, L approximately -9.0120429807, and c0 approximately +0.6380876407. These displayed midpoints are illustrative; their signs are enclosed, and a separate midpoint calculation also gives Q<0 there.

Within this registered set, the largest reinforcement product is at R=227, QL in [234.851860,234.851898]. The most negative Qc0 is at R=549, in [-5.666048,-5.666044]. Both extrema were checked by strict separation from every other root's enclosure, not just sorted floating-point midpoints.

### F. Exceptional Cases And Scope Of Refutation

At R=37 the certified values satisfy

```text
Q in [0.5063814,0.5063822],
L in [-0.2221981,-0.2221966],
QL<0, but abs(L+Q)-abs(L) in [0.0619854,0.0619889].
```

The positive quadratic term overshoots twice the negative linear magnitude. This explains the one extra magnitude-increase event beyond the 92 positive cross-product events. The overshoot was found while examining the registered stronger contraction test; it is not a post-hoc change of its definition.

R=9 has no pq=X atom, is not a prime root, and has no prime at R/2. Its counterexample therefore survives removal of those three particular endpoint complications. R=68 likewise has no equality pair. Boundary bookkeeping remains necessary, but it does not explain away the failures.

The findings refute universal local sign and contraction assertions only. They do not refute an eventual conditional sign law, an average theorem with quantified exceptions, OPEN-FW-CROSS-QUADRATIC, Analytic SC's error estimate, any first-bad theorem, or RH. No synthetic coefficient model was used for the counterexamples.

### G. Numerical Certification And Reproducibility

Actual environment: Python **3.12.14**, SciPy **1.17.0**, g++ **13.3.0**. Discrete enumeration is integer arithmetic; small complete wheels use Fraction. There is no random seed because no randomized experiment was used.

Primary certificates use **50 decimal digits**, interval endpoints with directed rounding, and one-ulp outward padding around correctly rounded natural logarithms. Python documents this rounding guarantee for Decimal.ln in its [standard-library specification](https://docs.python.org/3/library/decimal.html#decimal.Decimal.ln). Decimal endpoints are finite rationals; interval arithmetic carries their enclosure error through every operation.

For li differences, Euler's constant cancels exactly. Use the convergent identity [DLMF 6.6.1](https://dlmf.nist.gov/6.6.E1), with z=log x>0:

```text
li(x)-gamma = log z + sum_(k>=1) z^k/(k*k!).
t_(k+1)/t_k = z*k/(k+1)^2.
```

One hundred terms were used. After t_100 the remaining positive tail is enclosed by t_101/(1-z/102); all tested arguments have z<102. This controls truncation explicitly, rather than treating a repeated special-function call as certification.

For C, the product-variable integrand g_R(w) is smooth on [a,b]=[1/2,1-1/R^2]. Fourth-order interval Taylor coefficients bound g_R'''' everywhere on this interval. Composite Simpson with an even number n of subintervals has error at most

```text
R^2 * (b-a)^5 * sup|g_R''''| / (180*n^4).
```

This is the standard [composite Simpson remainder](https://dlmf.nist.gov/3.5.ii); the derivative bound is computed with enclosing interval arithmetic, not sampled derivatives. The primary scan used 64..512 subintervals, selected by the predeclared absolute-error tolerance 10^-6. Its largest certified quadrature radius was less than 9.966e-7. No sign interval in the registered tests contained zero.

For the independent midpoint check set a=R/2, b=X/R, f(u)=[li(X/u)-li(R)]/log u. On that interval a sufficient bound is

```text
sup|f''| <= 16/[R log R log a]
             +20/[R log R (log a)^2]
             + 8/[R log R (log a)^3].
```

To verify it, write f=h*r, h=integral_R^(X/u) dv/log v and r=1/log u. Then h<=R/log R, |h'|<=4/log R, |h''|<=16/(R log R), |r'|<=2/(R(log a)^2), and r''<=4/(R^2(log a)^2)+8/(R^2(log a)^3). Combine h''r+2h'r'+hr''. The 512-panel midpoint remainder is at most (b-a)^3 sup|f''|/(24*512^2). It was executed independently at R=8,9,68.

Precision/refinement checks: R=8,9,68,227,549,4096 were rerun at **70 digits**, tolerance 10^-8, followed by another factor-two panel refinement. Every refined C,Q,L,c0 interval lay inside its primary enclosure. This is a stability check, not a substitute for either error proof.

The independent floating-point implementation uses SciPy expi and adaptive quadrature in BOTH coordinates. It is a diagnostic only; SciPy's reported integration errors are not the rigorous certificate. All values agreed with the enclosing computation to the stated diagnostic tolerance. The two high-precision calculations share the interval implementation; the C++ source census is algorithmically independent of the Python Eratosthenes/pair reconstruction.

Implementation audit: before the full certificate scan, two context-rounding-sensitive expressions in the preliminary interval draft were replaced by exact copy_abs and directed multiplication. Every primary certificate was regenerated afterward. The preliminary small test is not used as evidence. An attempted optional Arb installation was denied by the network; Arb was not used or claimed. This did not prevent the standard-library certificates.

Measured subprocess times, not promised performance: binary64 scout 17.03 s; full interval scan 40.71 s; independent midpoint checks 3.05 s; 70-digit refined checks 7.82 s; C++ physical census 0.315 s. These exclude source intake, compilation and report preparation. Python syntax checks passed; C++ compiled with `-std=c++17 -O2 -Wall -Wextra -Werror`. No local Lean was run.

### H. Complete Source, Virtual Ledger, And Global Return

All **15 complete wheels R=2..16**, containing **347 divisor occurrences**, were enumerated with exact rational weights. Physical and virtual fractional sums were computed separately, reunited, and compared with both the signed floor sum and direct survivor count. At the decisive root R=9:

```text
P_8=210, delta(8)=8/35,
F_physical=-1/3, F_virtual=-8/21, F=-5/7,
F-80*delta(8)=-19,
pi(80)=22, pi(8)=4, 22=4-1+19.
```

Thus no virtual divisor was simply dropped. For larger roots the exact symbolic virtual correction remains

```text
V_R = X * [delta(R-1) - sum_(d<=X,d|P_(R-1)) mu(d)/d].
F_physical + V_R - X delta(R-1)
  = -sum_(d<=X,d|P_(R-1)) mu(d) floor(X/d).
```

No exponentially large full cube is enumerated at large R. The C++ linear least-prime-factor sieve constructs mu(d) and greatest prime factor independently and sums precisely the physical signed divisor form. It also counts actual survivors and reconstructs cross-root pairs by factoring physical semiprimes, not by reusing the Python pair list.

All **260 roots R=2..257 and 317,549,1027,4096** passed this exact floor/survivor/prime-count check. All 254 shared pair counts matched Python. Sieve primality was additionally checked by trial division on every integer 0..8192.

| R | X | Physical squarefree divisors | Exact signed floor total | pi(X) | Cross-root N |
| --- | ---: | ---: | ---: | ---: | ---: |
| 9 | 80 | 14 | 19 | 22 | 3 |
| 68 | 4623 | 661 | 606 | 624 | 44 |
| 257 | 66048 | 9652 | 6542 | 6595 | 416 |
| 549 | 301400 | 45185 | 26012 | 26112 | 1438 |
| 1027 | 1054728 | 161806 | 82291 | 82462 | 4130 |
| 4096 | 16777215 | 2664092 | 1077308 | 1077871 | 47002 |

The complete return uses Owner's original packet B_R(p), n=#{prime R/2<=p<R}, E=sum_(R/2<=p<R)delta(p-1)/p, F_other=sum_(p<R/2)B_R(p). Define

```text
K_rest = F_other-D_R+n(n+3)/2-X E+C.
Z_R = K_rest + L_A + L_B + Q.
```

The historical triangle n(n+3)/2 retains unit, prime-square, and distinct historical prime-pair contributions. Euler mass, other owners, and D_R are all present. This is the same sharp-source expansion used by the upstream handoff. If a four-vector t=(K_rest,L_A,L_B,Q) is squared, the exact identity is sum_i t_i^2+2sum_(i<j)t_i*t_j; all SIX cross terms were retained in the numerical reconstruction. It is NOT the original #915 NNS normalization, and no claim is made about that distinct object.

At all 254 roots the complete linear and quadratic returns matched the original li(X)-pi(X) diagnostic to absolute tolerances 10^-7 and 10^-5 respectively. These final li-anchor checks are binary64 numerical diagnostics, not certified bounds on Z_R. The underlying floor conservation tests and the proper Q/L sign enclosures have the stronger statuses stated above.

Illustrative normalized complete-source values, **NUMERICAL ONLY**, are:

| R | abs(Z_R)/(R log R) |
| --- | ---: |
| 8 | 0.2220406222 |
| 9 | 0.1860203874 |
| 68 | 0.0551191784 |
| 257 | 0.0246381512 |
| 549 | 0.0247408425 |
| 1027 | 0.0167387274 |
| 4096 | 0.0102918867 |

The finite observed maximum is at R=8. The largest observed abs(Q)/(R log R) is about 0.0325510045 at R=12. Neither is an estimate of an all-scale supremum or a fitted universal constant.

### I. Mathematical Interpretation And Surviving Question

The full product region, not just the two interval totals, controls the sign. Both a0 and b0 are negative at R=8 and R=9, yet Q changes sign. At R=9 the two linear orientations themselves oppose each other, and Q reinforces their negative sum. At R=37 Q opposes that sum but overshoots it. These are concrete failures of three different shortcuts: marginal signs, presumed anti-alignment, and anti-alignment-as-contraction.

Analytic SC's c0 is its exact constant mode of the SMOOTHED expression. Here Q is the SHARP expression. The report does **not** identify Q-c0 with SC's finite-band oscillatory integral at T=R/log^2 R. That smoothed integral was not computed, and its paper cutoff-error bound is not silently treated as an exact equality. H_MODE is a tested comparison, not a claim that the two objects coincide.

The precise surviving proper conjecture remains

```text
exists C_Q>=0, forall integers R>=8,
  |integral_Omega dnu(u)dnu(v)| <= C_Q R log R.
```

Status: CONJECTURE, inherited OPEN-FW-CROSS-QUADRATIC, not established by these finite observations. Even a proof would pay only Q: both linear terms and K_rest remain. No smaller independently sufficient theorem for the complete target was discovered. The new contribution is removing invalid local-sign requirements from the search, not replacing them with an unsupported norm estimate.

### J. Proof Impact And Falsification Audit

Quantifier discipline: R=9 refutes the exact all-R>=8 laboratory statements; it says nothing about an unformulated eventual version. R=68 is genuinely held out under the pre-registration, not a changed training range. Boundary, prime-root, empty-wheel, squareful physical occurrence, and virtual-divisor conditions were retained at the relevant scopes.

Upstream finite checks independently reproduced here: Owner's R=10 packet values are 2/5 and 8/35, total 22/35. Wheel's old-wheel composite shell survivors are {4,6,8} at R=2, {9,15} at R=3, {25,35} at R=5, and empty at R=14. This verifies those finite claims only. The all-scale FW and RA proofs and the SC smoothing theorem still require their separately assigned review.

No post-root Mobius coefficient is used as an independent bound. Actual prime counts above the root are explicit experimental observations, and the large-root exact source calculation also reconstructs them from the certified physical wheel. No first-bad hypothesis is asserted, no local negative contribution is spent as global payment, and no Mertens or Hecke source estimate is transferred by analogy.

### K. Two-Day Continuity

At intake, agent-reports was **136dad6b6c6c401bb5b60f2d59ca85eec5356eae**. Today's upstream material actually read:

| Report | Blob | Consumed scope |
| --- | --- | --- |
| November 9 Owner | bb695ee0ba98f44038cce54d3ae3039e1c28c7f2 | FW packet source, proper Q question, no separate upper-band payment |
| November 9 Analytic | f17f13f252d8855accc04cf5c2b5e2ebd1297522 | SC smoothing source, two linear terms, nonzero constant mode |
| November 9 Wheel | dbb85c912cb56a3a1203e1276bbac55d02ab4c93 | RA support, finite witnesses, no automatic contraction |

Today's Coordinator, Referee, and Lean remain `TODAY=PENDING` at the prepublication directory check. Before this execution, today's own Census file was absent. For missing upstream stages use `YESTERDAY=CARRY_FORWARD`, not an assumption that a schedule succeeded.

| November 8 report | Blob | Read and retained |
| --- | --- | --- |
| Coordinator, identical AM/PM blobs | 8b640304f6c233a2c4409b9882799de485888a9e | FM generalized non-Mobius obstruction, not an actual-prime theorem |
| Owner | 4e1b83a1e5ff8c134e9ca64404397c70c2b07252 | JS finite spectral-packet scope; today's FW changes the selected carrier |
| Analytic | edecba8785a45cda87c0035d0348695941f1b8ea | EC positive-error closure, subsequently merged as #1119 |
| Wheel | 60d4cf1b65d4b1b2cc4f13f6c0940c14cb2c50fd | FD donor-depth/allocation claims, different source |
| Census | 00f4f9c0d670821a0c9d1da31fd1c4d0afd09142 | FR additive-frequency falsifiers; not reused as this wheel's signs |
| Referee | 5371324ebbdbd88afb9abf843e83da2ce86b752f | EC scoped acceptance; SG remains its own paper claim |
| Lean | 5a110685bbe375d8ebff42df7391162914e52cef | #1119 exact-head implementation; its old unmerged status is superseded |

External inbox blob **038018145c0fddb2f6306c0712373adf9cd1ea52** was read. It contains no entry after October 18. Its genuine-carrier, fixed-cutoff, and no-circularity safeguards remain relevant; its historical routing and PR statuses do not override current main. No outside-session result is substituted for a missing scheduled report.

### L. Specialist Handoffs

| Recipient | Concrete next action |
| --- | --- |
| Proof Architect | Reject H_CANCEL and H_MODE at their stated universal scopes. Preserve the sharp proper Q bound and the complete return as OPEN. Do not turn the finite signs into an endpoint theorem. |
| Owner Payment | Use the certified U,V,C,Q data rather than an uncentered pair count. R=9 shows why a marginal deficit does not force helpful quadratic compensation. Both orientations and other owners are essential. |
| Analytic Type II | The sharp Q and constant mode can have opposite signs. A genuinely changed next test is the SC finite-band expression at the SAME R=9,68,227, with a certified smoothing difference and constant/oscillatory recombination; do not equate it to Q-c0. |
| Finite Wheel | Your R=2,3,5,14 shell witnesses independently pass. The new failure at R=9 has no root-prime or pq=X event, so RA's affordable admission channel cannot by itself explain its sign. |
| Adversarial Referee | Audit the product-variable change of variables, closed endpoints, interval implementation and derivative remainder. R=9 is the minimal certificate; independent midpoint bounds are supplied. No independent acceptance is presumed. |
| Lean Verification | No conjectural sign lemma should be implemented. After review, a finite counterexample certificate may be worthwhile only with an actual rigorous logarithmic-integral interface; do not encode numerical decimals or this open Q bound as assumptions. |

No specialist was launched, no other report was edited, and no branch, PR, issue, review, schedule, or workflow was created.

### M. Ranked Experimental Portfolio

| Rank | Exact hypothesis | Evidence and counterevidence | Required ingredient and next test | Disposition |
| --- | --- | --- | --- | --- |
| 1 | Uniform abs(Q_R)<=C_Q R log R, R>=8 | Survives this finite range; no proof or optimal constant | Original prime-pair signed estimate, not marginal signs; compute SC's coupled finite-frequency expression at fixed adverse roots | CONTINUE as proper-term conjecture only |
| 2 | Q_R L_R<=0 for all R>=8 | R=9 certified failure; 92 failures in registered set | No repair by omitting endpoint atoms; any conditional replacement must state a new arithmetic hypothesis before testing | REJECT universal form |
| 3 | Q_R c0_R>=0 for all R>=8 | R=9 certified failure; 88 failures | Marginal totals omit product-boundary shape | REJECT universal form |
| 4 | QL<=0 implies abs(L+Q)<=abs(L) on this carrier | R=37 overshoot | A magnitude restriction is additionally necessary; no such all-scale input is supplied | REJECT implication |

### N. Resume Capsule And Publication Discipline

```text
RUN=20261109-census-1; trigger=scheduled 03:11:02 EST; RUN_ID_UNAVAILABLE.
MAIN=8110624150e444964f998676bf54e2e9a3b7e91c.
ACK=FINITE_WHEEL_CENTERED_RH_V1.
SOURCE=ecb482e52deeee5e9b3853592a3ffdace662d2ff, complete wheel.
NEW=CR1 smallest R=9 sign falsifiers; CR2 held-out R=68;
    CR3 R=37 overshoot; CR4 independent exact source checks.
REUSE=FW packet, SC proper source, RA finite support, certified #1122.
NOT_COMPUTED=SC finite-band oscillatory integral at its prescribed T.
NO_GLOBAL_GAIN; NO_NEW_LEAN; INDEPENDENT_REVIEW=PENDING.
NEXT=certify the SC smoothed versus sharp decomposition at R=9,68,227,
     retaining c0, oscillatory part, smoothing difference, U,V and rest.
DO_NOT_REPEAT=leading owner-bias, full root-admission, or this unchanged scan.
```

The mathematical obstruction is the still-unproved uniform signed estimate, not lack of an exact representation. The execution produced reproducible finite results despite the optional package-install failure. Publication is claimed only after the actual commit and immutable readback receipt below.

### Reproduction Appendix

The complete executed source follows. Generated JSON and CSV are reproducible from these scripts; source hashes and command outputs are recorded here instead of committing extra repository files outside the owned report.

```text
python census_crossroot.py
python census_intervals.py
python census_intervals.py --roots 8,9,68 --independent-midpoint
python census_intervals.py --roots 8,9,68,227,549,4096 --digits 70 --refinement 2 --tolerance 0.00000001
g++ -std=c++17 -O2 -Wall -Wextra -Werror census_physical.cpp -o census_physical
python census_audit.py
python -m py_compile census_crossroot.py census_intervals.py census_audit.py
```

The scripts use /workspace for generated data and the compiled executable. No Lean code is generated or executed. Hashes:

| Source | SHA-256 |
| --- | --- |
| census_crossroot.py | 3d0cf2ab67d4a9689fc868adb9d8da7cd43511183ad7e0b334c515120eb9dec3 |
| census_intervals.py | 95dda94489c6d5fef1e23c92bea3b1ec2b50e31aece7913c2cf4ef0754c89101 |
| census_physical.cpp | 0e47729e5b9908ef00cce968ab66dc8d931035a4ac48a1030959de3f6b6300dc |
| census_audit.py | 008e911724835be7f202ef38808b3726fcbc5b77ac15245132e0253f3c1c8a93 |


#### census_crossroot.py

```python
"""Registered genuine-prime cross-root experiment; float scout, not certificates."""

import bisect
import hashlib
import json
import math
import platform
import time
from fractions import Fraction
from pathlib import Path

import scipy
from scipy.integrate import quad
from scipy.special import expi


ROOTS = list(range(8, 257)) + [257, 317, 549, 1027, 4096]


def sieve(n):
    flags = bytearray(b"\1") * (n + 1)
    flags[:2] = b"\0\0"
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p * p::p] = b"\0" * ((n - p * p) // p + 1)
    return flags, [p for p in range(2, n + 1) if flags[p]]


def trial(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def li(x):
    return float(expi(math.log(x)))


def row(R, primes):
    X = R * R - 1
    pa = [p for p in primes if R <= 2 * p and p < R]
    pb = [p for p in primes if R <= p <= 2 * R]
    pairs = [(p, q) for p in pa for q in pb if p * q <= X]
    N = len(pairs)
    bucket = sum(bisect.bisect_right(pb, X // p) for p in pa)
    assert N == bucket
    U = sum(li(X / p) - li(R) for p in pa)
    V = sum(li(X / q) - li(R / 2) for q in pb if R * q <= 2 * X)
    C, quad_error = quad(
        lambda u: (li(X / u) - li(R)) / math.log(u),
        R / 2, X / R, epsabs=1e-9, epsrel=3e-13,
    )
    C_product, product_error = quad(
        lambda w: R * R * (
            math.log(math.log(R * w)) + math.log(math.log(2 * R * w))
            - math.log(math.log(R)) - math.log(math.log(R / 2))
        ) / math.log(R * R * w),
        0.5, 1 - 1 / (R * R), epsabs=1e-9, epsrel=3e-13,
    )
    assert abs(C - C_product) < 1e-7
    la, lb = U - C, V - C
    Q = N - U - V + C
    L = la + lb
    a0 = len(pa) - (li(R) - li(R / 2))
    b0 = len(pb) - (li(2 * R) - li(R))
    c0 = a0 * b0 / 2
    LA = li(R) - li(R / 2)
    LB = li(2 * R) - li(R)
    alpha, beta = a0 / LA, b0 / LB
    projected = [alpha * beta * C, alpha * (lb - beta * C),
                 beta * (la - alpha * C)]
    projected.append(Q - sum(projected))
    n = len(pa)
    prime_count = bisect.bisect_right(primes, X)
    pi_y = bisect.bisect_left(primes, R)
    density = math.prod(1 - 1 / p for p in primes[:pi_y])
    all_F = X * density - (1 + prime_count - pi_y)
    euler_band = 0.0
    prior_density = 1.0
    for p in primes[:pi_y]:
        if 2 * p >= R:
            euler_band += prior_density / p
        prior_density *= 1 - 1 / p
    upper = n * (n + 3) / 2 + N - X * euler_band
    D = X * density + pi_y - 1 - li(X)
    complement = (all_F - upper) - D + n * (n + 3) / 2 - X * euler_band + C
    Z = li(X) - prime_count
    parts = [complement, la, lb, Q]
    assert abs(sum(parts) - Z) < 1e-7
    square = sum(v * v for v in parts) + 2 * sum(
        parts[i] * parts[j] for i in range(4) for j in range(i + 1, 4)
    )
    assert abs(square - Z * Z) < 1e-5
    return dict(R=R, X=X, N=N, U=U, V=V, C=C, C_product=C_product,
                quadrature_reported_error=quad_error + product_error,
                LA=la, LB=lb, Q=Q, L=L, QL=Q * L, Qc0=Q * c0,
                a0=a0, b0=b0, c0=c0, projection=projected,
                amplitude_change=abs(L + Q) - abs(L),
                endpoint_pairs=[pair for pair in pairs if math.prod(pair) == X],
                pa=pa, pb=pb, Z=Z, normalized=abs(Z) / (R * math.log(R)),
                Qnormalized=abs(Q) / (R * math.log(R)),
                full_parts=parts, floor_total=1 + prime_count - pi_y)


def small_exact(primes):
    checks = []
    for R in range(2, 17):
        X = R * R - 1
        ps = [p for p in primes if p < R]
        ds = [(1, 1)]
        for p in ps:
            ds += [(d * p, -m) for d, m in ds]
        physical = sum((m * Fraction(X % d, d) for d, m in ds if d <= X), Fraction())
        virtual = sum((m * Fraction(X, d) for d, m in ds if d > X), Fraction())
        density = math.prod(Fraction(p - 1, p) for p in ps)
        floors = sum(m * (X // d) for d, m in ds)
        direct = sum(all(n % p for p in ps) for n in range(1, X + 1))
        assert physical + virtual - X * density == -floors == -direct
        checks.append(dict(R=R, physical=str(physical), virtual=str(virtual),
                           density=str(density), floor=floors, occurrences=len(ds)))
    upstream = []
    for R in [2, 3, 5, 14]:
        Y = (R + 1) ** 2 - 1
        old = [p for p in primes if p < R]
        composites = [n for n in range(R * R, Y + 1)
                      if not trial(n) and all(n % p for p in old)]
        expected = [4, 6, 8] if R == 2 else (
            [R * R] + ([Y] if trial(R + 2) else []) if trial(R) else []
        )
        assert composites == expected
        upstream.append(dict(R=R, composite_survivors=composites))
    return checks, upstream


def main():
    start = time.perf_counter()
    flags, primes = sieve(max(ROOTS) ** 2 - 1)
    assert all(bool(flags[n]) == trial(n) for n in range(8193))
    exact, upstream = small_exact(primes)
    rows = [row(R, primes) for R in ROOTS]
    summary = {
        "status": "NUMERICAL_DIAGNOSTICS_NOT_CERTIFIED_SIGNS",
        "python": platform.python_version(), "scipy": scipy.__version__,
        "roots": len(rows), "exact_small": exact, "upstream": upstream,
        "first_cancel_failure": next(r for r in rows if r["QL"] > 0),
        "first_mode_failure": next(r for r in rows if r["Qc0"] < 0),
        "first_amplitude_failure": next(r for r in rows if r["amplitude_change"] > 0),
        "first_heldout_cancel": next(r for r in rows if r["R"] >= 65 and r["QL"] > 0),
        "first_heldout_mode": next(r for r in rows if r["R"] >= 65 and r["Qc0"] < 0),
        "largest_QL": max(rows, key=lambda r: r["QL"]),
        "most_negative_Qc0": min(rows, key=lambda r: r["Qc0"]),
        "max_Qnormalized": max(rows, key=lambda r: r["Qnormalized"]),
        "max_normalized": max(rows, key=lambda r: r["normalized"]),
        "seconds": time.perf_counter() - start,
    }
    Path("/workspace/crossroot_rows.json").write_text(json.dumps(rows, indent=2) + "\n")
    Path("/workspace/crossroot_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    for key, val in summary.items():
        if isinstance(val, dict) and "R" in val:
            print(key, {k: val[k] for k in ["R", "N", "LA", "LB", "Q", "c0", "QL", "Qc0"]})
        elif key not in ["exact_small", "upstream"]:
            print(key, val)
    print("source_sha256", hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
```


#### census_intervals.py

```python
"""Outward Decimal enclosures plus an explicit composite-Simpson remainder.

No binary64 value is used in a certificate. Coefficients of Jet are f^(k)/k!.
The li differences use the convergent Ei series, so Euler's constant cancels.
"""

import argparse
import json
import math
import time
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN
from fractions import Fraction
from pathlib import Path


def precision(digits):
    global DN, UP, NEAR
    DN = Context(prec=digits, rounding=ROUND_FLOOR)
    UP = Context(prec=digits, rounding=ROUND_CEILING)
    NEAR = Context(prec=digits, rounding=ROUND_HALF_EVEN)


precision(50)


class I:
    def __init__(self, lo=0, hi=None):
        if isinstance(lo, I):
            self.lo, self.hi = lo.lo, lo.hi
        elif isinstance(lo, Fraction):
            self.lo = DN.divide(Decimal(lo.numerator), Decimal(lo.denominator))
            self.hi = UP.divide(Decimal(lo.numerator), Decimal(lo.denominator))
        else:
            self.lo, self.hi = Decimal(lo), Decimal(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = I(other)
        return I(DN.add(self.lo, other.lo), UP.add(self.hi, other.hi))

    __radd__ = __add__

    def __neg__(self):
        return I(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, other):
        return self + (-I(other))

    def __rsub__(self, other):
        return I(other) + (-self)

    def __mul__(self, other):
        other = I(other)
        endpoints = [(x, y) for x in [self.lo, self.hi] for y in [other.lo, other.hi]]
        return I(min(DN.multiply(x, y) for x, y in endpoints),
                 max(UP.multiply(x, y) for x, y in endpoints))

    __rmul__ = __mul__

    def reciprocal(self):
        assert self.lo > 0 or self.hi < 0
        return I(DN.divide(Decimal(1), self.hi), UP.divide(Decimal(1), self.lo))

    def __truediv__(self, other):
        return self * I(other).reciprocal()

    def __rtruediv__(self, other):
        return I(other) * self.reciprocal()

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        ans = I(1)
        for _ in range(n):
            ans *= self
        return ans

    def ln(self):
        assert self.lo > 0
        return I(NEAR.next_minus(NEAR.ln(self.lo)), NEAR.next_plus(NEAR.ln(self.hi)))

    def abs(self):
        a, b = self.lo.copy_abs(), self.hi.copy_abs()
        return I(0 if self.lo <= 0 <= self.hi else min(a, b), max(a, b))

    def out(self):
        return [str(self.lo), str(self.hi)]


class Jet:
    def __init__(self, value, variable=False):
        self.c = [I(value), I(1 if variable else 0), I(0), I(0), I(0)]

    @classmethod
    def coefficients(cls, c):
        result = cls(0)
        result.c = c
        return result

    @staticmethod
    def lift(v):
        return v if isinstance(v, Jet) else Jet(v)

    def __add__(self, other):
        other = self.lift(other)
        return self.coefficients([a + b for a, b in zip(self.c, other.c)])

    __radd__ = __add__

    def __neg__(self):
        return self.coefficients([-a for a in self.c])

    def __sub__(self, other):
        return self + (-self.lift(other))

    def __rsub__(self, other):
        return self.lift(other) + (-self)

    def __mul__(self, other):
        other = self.lift(other)
        return self.coefficients([sum((self.c[k] * other.c[n-k] for k in range(n+1)), I(0))
                                  for n in range(5)])

    __rmul__ = __mul__

    def reciprocal(self):
        ans = [1 / self.c[0]]
        for n in range(1, 5):
            ans.append(-sum((self.c[k] * ans[n-k] for k in range(1, n+1)), I(0)) / self.c[0])
        return self.coefficients(ans)

    def __truediv__(self, other):
        return self * self.lift(other).reciprocal()

    def ln(self):
        derivative = self.coefficients([(k+1) * self.c[k+1] for k in range(4)] + [I(0)])
        quotient = derivative / self
        return self.coefficients([self.c[0].ln()] + [quotient.c[k-1] / k for k in range(1, 5)])


def li_no_gamma(x, terms=100):
    z = I(x).ln()
    term = z
    total = z.ln() + term
    for k in range(1, terms):
        term = term * z * k / ((k + 1) ** 2)
        total += term
    following = term * z * terms / ((terms + 1) ** 2)
    ratio = z / (terms + 2)
    assert ratio.hi < 1
    tail = following / (1 - ratio)
    return total + I(0, tail.hi)


def ll_integrand(R, w):
    return ((w * R).ln().ln() + (w * (2 * R)).ln().ln()
            - I(R).ln().ln() - I(Fraction(R, 2)).ln().ln()) / (w * (R * R)).ln()


def certified_C(R, tolerance="0.000001", refinement=1):
    a, b = Fraction(1, 2), Fraction(R * R - 1, R * R)
    domain = I(I(a).lo, I(b).hi)
    jet = ll_integrand(R, Jet(domain, variable=True))
    fourth = (24 * jet.c[4].abs()).hi
    bound = I(R * R) * I(b - a) ** 5 * I(fourth) / 180
    n = 2
    while (bound / (n ** 4)).hi > Decimal(tolerance):
        n *= 2
    n *= refinement
    total = I(0)
    for k in range(n + 1):
        weight = 1 if k in [0, n] else (4 if k % 2 else 2)
        total += ll_integrand(R, I(a + (b - a) * Fraction(k, n))) * weight
    S = total * I(b - a) * (R * R) / (3 * n)
    error = (bound / (n ** 4)).hi
    return S + I(error.copy_negate(), error), n, str(error)


def verify_row(record, tolerance="0.000001", refinement=1):
    R, X = record["R"], record["X"]
    pA, pB = record["pa"], record["pb"]
    baseA = li_no_gamma(Fraction(R, 2))
    baseB = li_no_gamma(R)
    U = sum((li_no_gamma(Fraction(X, p)) - baseB for p in pA), I(0))
    V = sum((li_no_gamma(Fraction(X, q)) - baseA for q in pB if R*q <= 2*X), I(0))
    C, n, error = certified_C(R, tolerance, refinement)
    LA, LB = U - C, V - C
    Q, L = record["N"] - U - V + C, LA + LB
    a0 = len(pA) - (baseB - baseA)
    b0 = len(pB) - (li_no_gamma(2 * R) - baseB)
    c0 = a0 * b0 / 2
    result = {"R": R, "N": record["N"], "panels": n, "C_error": error}
    for name, val in dict(U=U, V=V, C=C, LA=LA, LB=LB, Q=Q, L=L, a0=a0,
                          b0=b0, c0=c0, QL=Q*L, Qc0=Q*c0,
                          amplitude_change=(L+Q).abs()-L.abs()).items():
        result[name] = val.out()
        if name in record:
            assert val.lo - Decimal("1e-7") <= Decimal(str(record[name])) <= val.hi + Decimal("1e-7"), name
    return result


def self_test():
    j = Jet(I(1, 2), variable=True)
    reciprocal = (j + 1).reciprocal()
    assert reciprocal.c[4].lo <= Fraction(1, 3**5) <= reciprocal.c[4].hi
    assert reciprocal.c[4].lo <= Fraction(1, 2**5) <= reciprocal.c[4].hi
    logjet = j.ln()
    assert logjet.c[4].lo <= Decimal("-0.25") <= logjet.c[4].hi
    assert logjet.c[4].lo <= Decimal("-0.015625") <= logjet.c[4].hi
    assert (I(Fraction(1, 3))*3).lo <= 1 <= (I(Fraction(1, 3))*3).hi


def independent_midpoint(record, n=512):
    R, X = record["R"], record["X"]
    a, b = Fraction(R, 2), Fraction(X, R)
    loga, logr = I(a).ln(), I(R).ln()
    M2 = 16 / (R*logr*loga) + 20 / (R*logr*loga**2) + 8 / (R*logr*loga**3)
    base = li_no_gamma(R)
    values = I(0)
    for k in range(n):
        u = a + (b-a)*Fraction(2*k+1, 2*n)
        values += (li_no_gamma(Fraction(X, 1)/u)-base)/I(u).ln()
    center = values*I(b-a)/n
    error = (I(b-a)**3*M2/(24*n*n)).hi
    C = center+I(error.copy_negate(), error)
    U = sum((li_no_gamma(Fraction(X, p))-base for p in record["pa"]), I(0))
    ba = li_no_gamma(a)
    V = sum((li_no_gamma(Fraction(X, q))-ba for q in record["pb"] if R*q<=2*X), I(0))
    return {"R": R, "panels": n, "C": C.out(), "error": str(error),
            "Q": (record["N"]-U-V+C).out()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--roots", default="all")
    parser.add_argument("--digits", type=int, default=50)
    parser.add_argument("--refinement", type=int, default=1)
    parser.add_argument("--tolerance", default="0.000001")
    parser.add_argument("--independent-midpoint", action="store_true")
    args = parser.parse_args()
    precision(args.digits)
    self_test()
    rows = json.loads(Path("/workspace/crossroot_rows.json").read_text())
    if args.roots != "all":
        chosen = set(map(int, args.roots.split(",")))
        rows = [r for r in rows if r["R"] in chosen]
    start = time.perf_counter()
    results = []
    for record in rows:
        result = (independent_midpoint(record) if args.independent_midpoint else
                  verify_row(record, args.tolerance, args.refinement))
        results.append(result)
        if len(results) % 25 == 0:
            print("progress", len(results), "last_R", record["R"], flush=True)
    out = {"digits": args.digits, "refinement": args.refinement,
           "seconds": time.perf_counter()-start, "results": results}
    suffix = "midpoint" if args.independent_midpoint else str(args.refinement)
    dest = f"/workspace/crossroot_certificates_{args.digits}_{suffix}.json"
    Path(dest).write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2) if len(rows) < 15 else
          json.dumps({k:v for k,v in out.items() if k != "results"}), flush=True)


if __name__ == "__main__":
    main()
```


#### census_physical.cpp

```cpp
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <vector>

int main() {
    const int limit = 4096 * 4096 - 1;
    std::vector<int> least(limit + 1), greatest(limit + 1), primes;
    std::vector<int8_t> mu(limit + 1);
    mu[1] = 1;
    for (int n = 2; n <= limit; ++n) {
        if (!least[n]) {
            primes.push_back(n);
            least[n] = greatest[n] = n;
            mu[n] = -1;
        }
        for (int p : primes) {
            if (static_cast<int64_t>(n) * p > limit) break;
            int v = n * p;
            least[v] = p;
            greatest[v] = std::max(greatest[n], p);
            if (n % p == 0) {
                mu[v] = 0;
                break;
            }
            mu[v] = -mu[n];
        }
    }
    std::vector<int> roots;
    for (int r = 2; r <= 257; ++r) roots.push_back(r);
    for (int r : {317, 549, 1027, 4096}) roots.push_back(r);
    std::cout << "R,X,physical_divisors,signed_floor,survivors,prime_count,N_pairs\n";
    for (int r : roots) {
        const int x = r * r - 1;
        int64_t floor = 0, count = 0, survivor = 0, pairs = 0;
        for (int d = 1; d <= x; ++d) {
            if (mu[d] && greatest[d] < r) {
                floor += static_cast<int64_t>(mu[d]) * (x / d);
                ++count;
            }
            if (d == 1 || least[d] >= r) ++survivor;
        }
        for (int n = r * ((r + 1) / 2); n <= x; ++n) {
            int p = least[n];
            if (p == 0 || 2 * p < r || p >= r) continue;
            int q = n / p;
            if (q >= r && q <= 2 * r && least[q] == q) ++pairs;
        }
        int pi_x = std::upper_bound(primes.begin(), primes.end(), x) - primes.begin();
        int pi_y = std::lower_bound(primes.begin(), primes.end(), r) - primes.begin();
        if (floor != survivor || survivor != 1 + pi_x - pi_y) return 1;
        std::cout << r << ',' << x << ',' << count << ',' << floor << ','
                  << survivor << ',' << pi_x << ',' << pairs << '\n';
    }
}
```


#### census_audit.py

```python
"""Cross-language reconciliation and certificate-only sign summary."""

import csv
import hashlib
import io
import json
import platform
import subprocess
import time
from decimal import Decimal
from fractions import Fraction
from pathlib import Path


def sign(bounds):
    lo, hi = map(Decimal, bounds)
    return 1 if lo > 0 else (-1 if hi < 0 else 0)


def main():
    started = time.perf_counter()
    result = subprocess.run(["/workspace/census_physical"], capture_output=True, text=True, check=True)
    elapsed = time.perf_counter()-started
    Path("/workspace/crossroot_physical.csv").write_text(result.stdout)
    physical = {int(r["R"]): {k: int(v) for k,v in r.items()}
                for r in csv.DictReader(io.StringIO(result.stdout))}
    rows = json.loads(Path("/workspace/crossroot_rows.json").read_text())
    certificates = json.loads(Path("/workspace/crossroot_certificates_50_1.json").read_text())["results"]
    for row in rows:
        other = physical[row["R"]]
        assert other["N_pairs"] == row["N"]
        assert other["signed_floor"] == row["floor_total"]
    buckets = {}
    for name, pred in [("discovery", lambda r: r <= 64),
                       ("heldout", lambda r: 65 <= r <= 256),
                       ("stress", lambda r: r >= 257), ("all", lambda r: True)]:
        chosen = [r for r in certificates if pred(r["R"])]
        buckets[name] = {
            "roots": len(chosen),
            "cancel_failures": [r["R"] for r in chosen if sign(r["QL"]) == 1],
            "mode_failures": [r["R"] for r in chosen if sign(r["Qc0"]) == -1],
            "amplitude_failures": [r["R"] for r in chosen if sign(r["amplitude_change"]) == 1],
            "unresolved": [r["R"] for r in chosen if 0 in (sign(r["QL"]), sign(r["Qc0"]), sign(r["Q"]))],
        }
    # Independent direct least-prime reconstruction of Owner's exact witness.
    owner = []
    X = 99
    for p in [5, 7]:
        below = [n for n in range(2, p) if all(n%d for d in range(2, int(n**0.5)+1))]
        delta = Fraction(1)
        for q in below:
            delta *= Fraction(q-1, q)
        count = sum(all(k%q for q in below) for k in range(1, X//p+1))
        owner.append(Fraction(count)-Fraction(X,p)*delta)
    assert owner == [Fraction(2,5), Fraction(8,35)]
    summary = {
        "classification": "FINITE_COMPUTATION",
        "python": platform.python_version(),
        "cpp_seconds": elapsed,
        "physical_roots": len(physical), "paired_roots": len(rows),
        "buckets": buckets,
        "owner_R10": list(map(str, owner)),
        "smallest": [r for r in certificates if r["R"] in [8,9]],
        "selected_physical": [physical[r] for r in [2,3,9,68,257,549,1027,4096]],
        "max_C_error": str(max(Decimal(r["C_error"]) for r in certificates)),
        "panel_range": [min(r["panels"] for r in certificates),max(r["panels"] for r in certificates)],
        "source_sha256": {p: hashlib.sha256(Path('/workspace',p).read_bytes()).hexdigest()
                          for p in ['census_crossroot.py','census_intervals.py','census_physical.cpp','census_audit.py']},
    }
    Path("/workspace/crossroot_audit.json").write_text(json.dumps(summary,indent=2)+"\n")
    print(json.dumps({k:v for k,v in summary.items() if k not in ['buckets','smallest']},indent=2))
    print(json.dumps({k:{key:len(v) if isinstance(v,list) else v for key,v in val.items()}
                      for k,val in buckets.items()},indent=2))


if __name__ == '__main__':
    main()
```


### Verified Publication Receipt - 2026-11-09 03:35 EST

The complete synthesis was published to the owned report on agent-reports at commit **32b779e69604804c2b314214e9d4031deefa1129**, blob **91a376f41bf0e936fe97eb1dea16c731d3e495be**. Immutable readback at 2026-11-09 08:35:20 UTC matched the entire prepared document byte-for-byte and preserved the preregistration as an unchanged prefix. This receipt is an append-only continuation of that verified publication, not another research invocation.

Final research status: COMPLETED finite experiment; CR1/CR3 scoped assertions REFUTED; CR2/CR4 FINITE_COMPUTATION; independent mathematical review PENDING. The uniform proper-Q and complete RH-scale estimates remain OPEN. No new formal theorem or global exponent improvement is claimed.


## Scheduled Continuation And Frozen Band Test - 20261109-census-2/BL

Execution IN_PROGRESS; mathematical findings PENDING. Actual trigger 2026-11-09 11:00:01 EST, America/New_York; platform RUN_ID_UNAVAILABLE. This is a continuation of the same dated report, preserving the earlier CR findings and publication receipts.

finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.
MAIN=02f00cee544278ad1bb9022ee76fc5916d459a95.
AGENTS=6695522a45d67fd1e80a7cff1f98d909405036e2.
CONTRACT=95566e37c8eaeb99ee680660df4f9d2e06ea5038.
DIRECTIVE=e505f35522b675c6b5b263eac73618d717346973.
COMPLETE_WHEEL=ecb482e52deeee5e9b3853592a3ffdace662d2ff.
ROOT_ADMISSION=a412632c1028d7728cd8d87ee6e5ac365377d338.
Intake agent-reports=2b7df755c4d16de12b63398c66a04f3c13ab2827.

### Authority And Continuity

Current source retains X=R^2-1, all d dividing the full primorial, physical and virtual ledgers reunited before Euler compensation, and Z_R=F_R-D_R=li(X)-pi(X). The uniform ONE-C bound |Z_R|<=C R log R remains OPEN. The canonical VF terminal keeps its explicit classical-criterion interface.

Read November 9 Coordinator FB/MP/SHIFT, Owner FW/CT, Analytic SC/MB, Wheel RA/DG, own CR and Lean root-admission implementation. Read applicable November 8 summaries/handoffs for all seven roles. Today's Referee is TODAY=PENDING; YESTERDAY=CARRY_FORWARD at its reported scopes, not approval of today's papers. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no newer entry than October 18. There are no open/draft PRs at intake; #1124 is human-merged. No upstream paper theorem is promoted merely because its report exists.

### Exact New Question And Pre-Registration

This resumes the unfinished certified finite-frequency follow-up from CR, updated to Coordinator OPEN-MIDBAND and Analytic MB's precise source. It is not another sharp-Q sign census or a broader repetition of MB's generous bound checks.

For every tested integer R>=16, U=sqrt(R), X=R^2-1,
I_-=[R/2,R), I_+=[R,2R], and dnu=dpi-du/log(u), define
A(t)=integral_(I_-)(u/R)^(-it)dnu(u), B(t)=integral_(I_+)(u/R)^(-it)dnu(u).
Use the ORIGINAL nonconjugated product and the exact phase a=log(X/R^2).
The weight is b(t/R), with b(w)=1-6w^2+6w^3 on this entire band.
M_mid=(1/pi)integral_U^(2U)b(t/R) Im(exp(ita) A(t)B(t))/t dt.
J_mid uses the two prime polynomials instead, retaining both mixed reference orientations in M=J-PC-CP+CC.

For the full prime rectangle define the EXACT rational collar
C_R={(p,q): abs(pq-X)<=floor(X/(4*ceil(sqrt(R))))}.
Keep p=R/2 when prime, exclude p=R, include q=R and pq=X. Above-wall pairs are essential to the frequency source and are NOT discarded. Each pair has its actual occurrence multiplicity. Define J_close as the same K_R(pq) sum on C_R, J_far=J_mid-J_close.

New laboratory localization hypothesis, not attributed to an upstream author:
H_LOCAL: J_mid(R)*J_close(R)>=0 for EVERY integer R>=16.
Record the stronger dominance test abs(J_far)<=abs(J_close), but do not confuse it with the sign assertion.
Competing explanation: the oscillatory complement can reverse the near-wall contribution. A certified opposite product falsifies H_LOCAL. An interval containing zero is unresolved. No universal amplitude constant is fitted or claimed.

Discovery roots: every R=16..48.
Held-out roots: 64,127,257,549,1024,4096.
Compute exact collar counts and below/on/above wall classifications. Rank signed and absolute packet contributions; inspect the smallest counterexample in the declared domain, if any. Independently certify that witness and its predecessors needed for minimality. At the six held-out roots compute certified M_mid, J_mid, both mixed reference terms, CC, and the two weighted discrepancy-transform energies. Binary64 exploratory packet totals are diagnostic until enclosed.

### Numerical And Source Validation Plan

Use a transparent exact sieve, independently checked by trial division / C++ enumeration. For transcendental certificates use directed Decimal interval arithmetic, exact rational bracketing of Gauss-Legendre nodes, interval trigonometry with an explicit Taylor remainder, and explicit high-order quadrature remainder bounds. Recompute key results at increased precision / quadrature refinement. An independent SciPy direct-product kernel / separate factored-transform calculation checks the central values but is not itself a certificate.

The source adapter b is piecewise in general, but R>=16 ensures t/R<=1/2 on [U,2U], including equality at R=16; this avoids silently integrating across a polynomial join. Track the wrong conjugated-product diagnostic and pq=X zero-band contribution while retaining that atom in the sharp source.

Reuse CR's verified complete physical/virtual and full-return checks where hashes match. For any newly reported global Z_R comparison, independently reconstruct the compensated physical floor total and retain the symbolic virtual correction
X*(delta(R-1)-sum_(physical d)mu(d)/d).
Do not enumerate a large complete cube. Numerical |Z_R|/(R log R) remains NUMERICAL ONLY. A proper middle-band certificate does not pay the constant mode, other bands, physical linear responses, other owners, or original #915 covariance.

Stop after the registered domain and decisive checks. Publish code, actual outputs, uncertainty, limitations and one precise next lemma. No local Lean, no source/branch/PR/other-report edits, no agent launch or schedule change.


### Disclosed Proof-Led Extension - 20261109-census-2/BL-Pair

After the first registered R=16 reversal was independently verified by exact rational series, a new proper-component lemma emerged. This was NOT part of the initial registration; it is disclosed before its pair-specific arithmetic validation. The original domain, samples and hypothesis are unchanged.

Let h=ceil(sqrt R), X=R^2-1 and D=floor(X/(4h)), R>=16. Products pq in the original cross-root rectangle have unique prime-pair occurrences. Pair a product X-d with X+d only if BOTH original occurrences exist, 1<=d<=D; each is used once. Let J_match be the sum of their original K_R contributions. The proposed PAPER_PROOF is

0<=J_match<=4R/765, uniformly for every integer R>=16.

Indeed t*abs(log(X/(X+/-d)))<=2sqrt(R)/(4h-1)<=8/15 on the full band, so the sine response is strictly increasing in log phase. Each reflected pair is positive, not exactly cancelling, and is at most
sqrt(R)*d^2/[pi*(X^2-d^2)].
Summing at most D distinct offsets and using h>=sqrt R, h>=4, X<R^2 and pi>3 gives the displayed 4R/765 bound. No prime-distribution estimate or desired discrepancy bound is used.

This is only a quantitatively paid subset of the NEAR collar. The unmatched collar and ALL far products remain, as do both reference orientations and the full wheel complement. It is not a bound for J_mid or Z_R. Exact reflection is additive in product, not logarithmic; the latter distinction creates the positive curvature bias.

Validation: classify matched/unmatched occurrences at the already-registered 39 roots, verify one-use/injective accounting and total reconstruction, test the sign and explicit bound numerically with separate certificates at selected nonempty cases, and keep the zero-offset product atom separate. No new root is selected to improve the constant.


## Reflected Product Payment And Certified Band Reversals - 20261109-census-2/BL

### A. Most Important Mathematical Discovery

**Exact reflected prime products in the near-cutoff collar have a uniformly paid positive curvature bias, but the collar does not determine the full signed band.** A direct paper argument gives `0<=J_match(R)<=4R/765` for every integer `R>=16`, with no prime-distribution assumption. The matching uses each actual product occurrence once. This pays only that subset; it supplies neither enough partners nor a bound on the unmatched or far contributions.

The registered localization rule is **REFUTED** at the smallest allowed root, `R=16`: `J_close>0` while `J_mid<0`. An independent exact-rational series calculation confirms the certificate. The held-out root `R=257` has the opposite reversal, `J_close<0<J_mid`. Restoring the continuous reference terms can change the sign again: at R=16 the centered M_mid is positive, whereas J_mid is negative; at R=127 the reverse occurs.

These findings separate three objects that must not be treated as interchangeable: a same-sign near-cutoff packet, the entire signed prime-product band, and its centered prime-minus-li band. **No new global exponent, uniform middle-band bound, canonical VF estimate, finite A/C, or RH proof is claimed.**

| Claim ID | Result | Evidence And Scope |
| --- | --- | --- |
| 20261109-census-2/BL1 | H_LOCAL fails at R=16, the first admissible root; held-out failure at R=257 | REFUTED by certified FINITE_COMPUTATION |
| BL2 | Certified proper-band/reference/energy values; two explicit reference-induced sign reversals | FINITE_COMPUTATION, not an all-scale norm estimate |
| BL3 | Every reflected collar-pair has positive bias; their TOTAL is at most 4R/765 | PAPER_PROOF, SELF_AUDIT, independent review pending, not formalized |
| BL4 | Exact one-use matched/unmatched partition at all 39 registered roots | FINITE_COMPUTATION; corroborates, but does not prove, BL3 |
| BL5 | Independent rational witness, C++ count reconciliation, and full physical/virtual R=16 ledger | FINITE_COMPUTATION; existing source identities are credited, not rediscovered |

### B. Current Authoritative Objective

Actual trigger: **2026-11-09 11:00:01 EST**, America/New_York. Run label `20261109-census-2`; platform RUN_ID_UNAVAILABLE. Authority was refreshed at the beginning of this invocation. Acknowledgment: `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`.

Pinned main: **02f00cee544278ad1bb9022ee76fc5916d459a95**, human merge #1124. Intake reporting snapshot: **2b7df755c4d16de12b63398c66a04f3c13ab2827**. Earlier CR results and receipts remain unchanged above.

| Inspected Source | Blob SHA |
| --- | --- |
| AGENTS.md | 6695522a45d67fd1e80a7cff1f98d909405036e2 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| Complete-wheel seven-role directive | e505f35522b675c6b5b263eac73618d717346973 |
| docs/DYNAMIC_RESEARCH_AGENTS.md | e8d913ff9663bb5163eaf0eddca9f76e0508a7ef |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| research/CompleteWheelRootAdmission.lean | a412632c1028d7728cd8d87ee6e5ac365377d338 |
| research/CompleteWheelRootAdmissionAcceptance.lean | d0b22fa38c254a22b38b678e77bb520a70eae1af |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

For every integer R>=2, the original source is

```text
X=R^2-1, y=R-1, P_y=product_(prime p<=y)p,
delta(y)=product_(p<=y)(1-1/p),
F_R=sum_(d|P_y)mu(d)fract(X/d),
D_R=X delta(y)+pi(y)-1-li(X), Z_R=F_R-D_R=li(X)-pi(X).
OPEN: exists ONE C>=0, forall R>=2, abs(Z_R)<=C R log R.
```

The inspected original declarations are `finiteWheelFract`, `finiteWheelSquareDeterministic`, `vfMidPrefixWheelCounting`, and `vfMidPrefixWheelDensity`, with the full finite Euler product. Their compiled physical/virtual compensation, Legendre count, and arbitrary-reference centered identity are reused. [Pinned source](https://github.com/OVVO-Financial/RH_Lean/blob/02f00cee544278ad1bb9022ee76fc5916d459a95/research/CompleteSquareRootWheelFractionalBoundary.lean).

The public canonical target remains `VFCanonicalSquareVonKochStatement`; its terminal theorem still takes `ClassicalVonKochRHCriterion` explicitly. Principal-value li and Li_2 differ by a fixed constant, not zero. The band uses their common derivative measure without changing the global anchor.

### C. Competing Hypotheses And Prior Credit

The original registration was committed **before arithmetic execution** at `075800ea1d8657f7e60b8dbf6922bd7decb5749a`, blob `6753c4c66bc066e35699ee3ce0af037609836e72`, and read back byte-for-byte. Discovery roots are every integer 16..48; held-out roots are exactly 64,127,257,549,1024,4096.

H_LOCAL asserted `J_mid(R)*J_close(R)>=0` for every integer R>=16. The rival was that the retained oscillatory complement can reverse the near-cutoff contribution. The stronger dominance diagnostic was `abs(J_far)<=abs(J_close)`. No all-scale amplitude constant was fitted. These were new laboratory tests, not claims attributed to an upstream author.

Coordinator FB/OPEN-MIDBAND supplied the requested actual-source frequency test. Analytic MB supplied the precise spline, nonconjugated prime/reference expansion and paid reference bound. Owner FW/CT and Wheel RA/DG supplied endpoint and incidence safeguards. CR's sharp-hyperbola sign census was NOT rerun. Analytic's broad, generously bounded diagnostic was not presented as new research here: the new work supplies numerical certificates, the specific localization falsifier, and the reflected-product subdivision.

BL3 is a **disclosed proof-led extension**, developed after seeing the R=16 result. Its statement, proof outline, and pair-specific tests were registered at `732779322bfe307546eb58f79c244f3330dd7017`, blob `0373dcf16703cbe23700b970883366038340a99e`, before running that classification. It does not retroactively change the initial test or its constant.

### D. Exact Experimental Carrier

For integer R>=16 set U=sqrt(R), a=log(1-R^(-2)), I_-=[R/2,R), I_+=[R,2R]. Put

```text
P_-(t)=sum_(prime p in I_-)(p/R)^(-it),
P_+(t)=sum_(prime q in I_+)(q/R)^(-it),
C_-(t)=integral_(I_-)(u/R)^(-it)du/log u,
C_+(t)=integral_(I_+)(u/R)^(-it)du/log u,
A=P_--C_-, B=P_+-C_+.
T(V,W)=(1/pi)integral_U^(2U)b(t/R) Im(exp(ita)V(t)W(t))/t dt.
J=T(P_-,P_+), PC=T(P_-,C_+), CP=T(C_-,P_+), CC=T(C_-,C_+),
M=T(A,B)=J-PC-CP+CC.
```

No factor is conjugated in T. On this domain `t/R<=1/2`, hence `b(t/R)=1-6(t/R)^2+6(t/R)^3` throughout. Equality at R=16 is included. The 8..15 piecewise-spline cases are outside this registered theorem/test domain, not silently approximated by the wrong polynomial.

With tau=t/U, the exact integration weight is `w_R(tau)=1/tau-6tau/R+6tau^2/R^(3/2)` on [1,2]. Define the weighted energies `E_A=integral_1^2 w_R(tau)|A(Utau)|^2 dtau`, and similarly E_B. They give `abs(M)<=sqrt(E_A E_B)/pi`; they are not an original #915 NNS statistic.

For each prime pair in the FULL rectangle, including pq>X,

```text
K_R(z)=(1/pi)integral_U^(2U)b(t/R)sin(t log(X/z))/t dt,
h=ceil(sqrt R), D=floor(X/(4h)),
J_close=sum_(abs(pq-X)<=D)K_R(pq), J_far=J-J_close.
```

Prime p=R/2 is admitted, p=R is excluded, and q=R is admitted. Products pq=X remain in the source even though their value in this one band is zero. The product map is injective because p<R<=q are distinct primes; no duplicate physical occurrences are removed. No new Mobius or prime value beyond the historical root is used as an independently assumed bound.

### E. Executed Results

At R=16 the left prime set is {11,13}, the right set is {17,19,23,29,31}, X=255 and D=15. The only close products are 247=13*19 and 253=11*23. An entirely rational log-series/integrated-sine-series calculation gives

```text
-0.135768199376325 < J < -0.135768199376324,
 0.024008396864762 < J_close < 0.024008396864763.
```

Thus H_LOCAL fails at its first admissible root, not merely at the first root of a delayed scan. The directed-interval Gauss computation independently gives J_far approximately -0.15977659624108655. The five above-wall products contribute approximately -0.4377148865985686, exceeding the positive total below the wall, approximately 0.3019466872222443. Keeping only the two close products loses the deciding sign.

At R=257 the certified values satisfy `1.5898050420104157<J<1.5898050420104159` and `-0.1534403737498834<J_close<-0.1534403737498832`. This is the only H_LOCAL failure in the six predeclared held-out roots. At R=16 and R=127, the independently enclosed reference restoration has opposite-sign J and M:

```text
R=16:  M in (0.0339253491284779, 0.0339253491284781),
       PC=-0.2442864883..., CP=-0.1004266674..., CC=-0.1750196072....
R=127: J in (0.376119397678,0.376119397682),
       M in (-0.705915550896,-0.705915550881).
```

The reference-sign observations were discovered in the registered full decomposition; they are not a separately preregistered universal hypothesis. They do not refute MB2's amplitude bound.

The binary64 scout covers all 39 roots and 134,609 pair occurrences. It reports 15 localization sign failures and 32 stronger-dominance failures. Only the individually enclosed examples are used as rigorous full-J sign claims; the remaining scout signs are explicitly diagnostic. Every collar value, including the matched/unmatched split, is separately enclosed by the integrated series calculation.

The following displayed real entries each denote an enclosure of **printed value +/- 0.000001**; integer counts are exact. The full tighter intervals are preserved in the reproduction data. Cauchy is the enclosed value sqrt(E_A E_B)/pi, not an assumed all-scale constant.

| R | J_mid | J_close | M_mid | Cauchy |
| ---: | ---: | ---: | ---: | ---: |
| 16 | -0.135768 | 0.024008 | 0.033925 | 0.051610 |
| 64 | -0.477921 | -0.146202 | -0.202789 | 0.434278 |
| 127 | 0.376119 | 0.073829 | -0.705916 | 1.075317 |
| 257 | 1.589805 | -0.153440 | 0.471821 | 0.999190 |
| 549 | 0.402822 | 0.229553 | 0.269846 | 1.458931 |
| 1024 | -6.314323 | -0.122733 | -4.441193 | 5.564345 |
| 4096 | -9.022460 | -0.732730 | -0.541146 | 22.903178 |

| R | E_A | E_B | PC | CP | CC |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 0.083969 | 0.313068 | -0.244286 | -0.100427 | -0.175020 |
| 64 | 1.311334 | 1.419460 | -0.551622 | 0.292745 | 0.016255 |
| 127 | 7.905908 | 1.443514 | 0.915456 | 0.090584 | -0.075995 |
| 257 | 3.411283 | 2.888541 | 0.522449 | 0.488508 | -0.107026 |
| 549 | 3.827646 | 5.488294 | 0.778780 | -1.136908 | -0.491103 |
| 1024 | 9.636861 | 31.709710 | -1.504448 | -0.999732 | -0.631050 |
| 4096 | 45.401203 | 114.031247 | -1.376669 | -6.942345 | 0.162299 |

At R=4096 the centered amplitude is about 2.36% of its weighted Cauchy bound; at R=1024 it is about 79.8%. These are finite diagnostics of variable cancellation, not an inferred uniform improvement. The maximum displayed absolute M is at R=1024, not at the largest root.

| R | Collar Occurrences | Reflected Pairs | J_match | J_unmatched |
| ---: | ---: | ---: | ---: | ---: |
| 20 | 3 | 1 | 0.000313 | -0.007827 |
| 64 | 9 | 0 | 0.000000 | -0.146202 |
| 127 | 20 | 1 | 0.000005 | 0.073825 |
| 257 | 41 | 2 | 0.000567 | -0.154007 |
| 549 | 99 | 1 | 0.000035 | 0.229518 |
| 1024 | 231 | 3 | 0.000526 | -0.123259 |
| 4096 | 1267 | 26 | 0.002739 | -0.735468 |


### F. Reflected-Pair Theorem And Proof

**BL3, PAPER_PROOF / SELF_AUDIT.** For every integer R>=16, let

```text
D_R^match={d in {1,...,D}: both X-d and X+d occur as pq in I_- x I_+},
J_match=sum_(d in D_R^match)[K_R(X-d)+K_R(X+d)].
Then 0<=J_match<=4R/765.
```

This is a bound for the total matched subset, not a per-pair estimate multiplied by an unrecorded descendant count. D_R^match is a set of integer offsets; product uniqueness ensures each actual occurrence is used once. The zero-offset atom has band value zero and is kept separately.

Proof. Write U=sqrt R, h=ceil U and u=d/X. Then 0<u<=1/(4h), h>=4. For every t in [U,2U],

```text
0<t*(-log(1-u)) <= 2U/(4h-1) <= 8/15 < pi/2.
```

The function `f(s)=(1/pi)integral_U^(2U)b(t/R)sin(ts)/t dt` is strictly increasing throughout the needed positive phase interval, because its derivative integrates positive `b(t/R)cos(ts)`. Moreover `0<f'(s)<=U/pi`, since 0<=b<=1 and the interval length is U. As `-log(1-u)>log(1+u)>0`, the pair contributes

```text
0<f(-log(1-u))-f(log(1+u))
 <= (U/pi)*[-log(1-u^2)]
 <= U*d^2/[pi*(X^2-d^2)].
```

The final elementary log bound follows by integrating 1/(1-v) from 0 to u^2. Since there are at most D distinct positive offsets,

```text
J_match <= U*D^3/[pi*(X^2-D^2)]
        <= U*X/[64*pi*h^3*(1-1/(16h^2))]
        < 4R/(255*pi) < 4R/765.
```

Here U/h^3<=1/R, X<R^2, `1-1/(16h^2)>=255/256`, and pi>3. The empty matching gives zero. Every constant is fixed before R. The proof uses no PNT, prime error, equidistribution, unproved incidence estimate, or RH hypothesis.

The effect is a **positive curvature bias**, not exact cancellation: additive product reflection is not exact reflection of logarithmic phase. For example, R=20 has the pair 391=17*23 and 407=11*37, centered at X=399. Its certified contribution is between 0.00031299588626595 and 0.00031299588626597, not zero.

Across the 39 fixed roots there are 41 such matched pairs, with nonempty matchings at 11 roots. R=4096 has 26 pairs among 1,267 collar occurrences, so only 52 occurrences are removed by this matching. No estimate for the unmatched population is inferred from these finite proportions. This is a source-specific elementary estimate, not a claim of literature priority for Taylor expansion or reflection pairing.

### G. Numerical Certification And Independent Checks

The primary certificates use 64-digit directed Decimal arithmetic. Each of the 16 Gauss-Legendre nodes is bracketed by exact rational sign tests of its degree-16 polynomial, followed by 160 rational bisections; the brackets are disjoint. The usual derivative formula encloses each positive weight. Polynomial moment identities through degree 31 are checked with intervals. NumPy supplies only initial guesses, not trusted quadrature nodes.

For m panels on an interval of length H, the quadrature remainder used is

```text
error <= c_16 H^33 m^(-32) sup|f^(32)|,
c_n=(n!)^4/[(2n+1)((2n)!)^3].
```

This follows by rescaling the [Gauss remainder and Legendre norm](https://dlmf.nist.gov/3.5.v). The program supplies explicit derivative bounds, not sampled derivatives. For the reference transform in logarithmic coordinates, `g_t(s)=R exp((1-it)s)/(log R+s)`, it uses

```text
sup|g_t^(32)(s)| <= 2R*32!*sum_(j=0)^32
   (1+2sqrt R)^j/[j!*(log(R/2))^(33-j)].
```

For the outer integrand, differentiate the exact `w_R(tau) exp(i v tau)`. The reciprocal part is bounded by `32!*sum_(j=0)^32 V^j/j!`; the two polynomial parts are differentiated explicitly in the code. Here `|v|<=sqrt R`, and the total variation factors are bounded by `n_-+R/(2log(R/2))` and `n_++R/log R`. Energies use their squared masses. The deliberately wrong conjugated control instead uses the conservative phase bound `2sqrt R`.

Reference quadrature intervals are propagated through every product before the outer remainder is added. Log, exp and sqrt endpoints use outward padding around the Decimal routines; the [Python Decimal documentation](https://docs.python.org/3.12/library/decimal.html) specifies their rounding behavior. Trigonometry is implemented by a Taylor enclosure at an argument of magnitude at most 1/8, followed by complex squaring; an explicit degree-50 remainder and the initial input-radius bound are retained. Pi is enclosed by exact alternating arctangent series using Machin's identity. There is no reliance on an uncertified special-function library for the sign certificates.

The independent R=16 witness uses **Fraction arithmetic only**, an atanh series for logarithms with a geometric tail, and an analytically integrated sine series with a degree-51 remainder. It uses neither Gaussian quadrature nor Decimal logarithms. This separately certifies J and J_close. The collar-only verifier uses the convergent integrated power series at every registered root and checks each reflected-pair positivity and bound.

R=16,127,257 were recomputed at 80 digits with twice as many panels in both coordinates. Every refined interval lies inside the corresponding primary interval. The independent SciPy audit integrates continuous references in the original u-coordinate and uses adaptive frequency quadrature; the scout instead evaluates prime products through a sine-integral antiderivative. These are cross-checks, not the certificates. Exact sieve/trial primality agrees on every integer 0..8192, and a separately compiled C++ trial-factor enumeration agrees on all 39 pair counts and collar side counts.

The nonconjugation control is decisive at R=64: the correct M is negative, approximately -0.202789000854, while the conjugated expression lies between 0.06903216202 and 0.06903216225. At R=18 the equality pair (17,19), product 323=X, has zero band contribution but remains an admitted sharp-source atom. Root-prime cases R=127 and R=257 retain the actual q=R atom and exclude p=R.

These are software-assisted finite certificates with explicit error analysis, not kernel-certified Lean numerical data or independent Referee acceptance. The new paper theorem remains review-pending.

### H. Original Source And Complete Signed Return

At the decisive R=16, exact Fraction enumeration separates all 64 complete-wheel divisor occurrences into 36 physical and 28 virtual entries:

```text
P_15=30030, delta(15)=192/1001,
F_physical=183/1001, F_virtual=-272/1001, F=-89/1001,
F-255*delta(15)=-49,
direct survivors=49, pi(255)=54=pi(15)-1+49.
```

The virtual mass is exactly `X*(delta(15)-sum_(physical d)mu(d)/d)`. It was not discarded. The corresponding principal-value-li diagnostic is `Z_16=6.332664826664185...`, normalized `abs(Z_16)/(16log16)=0.14275162720375606...`; these last decimals are **NUMERICAL ONLY**. No larger unchanged prime-count table or exponential wheel cube was rerun. CR's unchanged complete-source checks remain available under their original provenance.

Retain the upstream FW/SC/MB paper adapter at its own review status. With the full hyperbolic mixed responses and other-owner restoration in S_rest, it reads

```text
Z_R = S_rest + J_mid + delta_ref + e_smooth,
S_rest = C_rest + I_Lnu + I_nuL + A(0)B(0)/2
         + I_[0,sqrt R] + I_[2sqrt R,R],
C_rest = F_other-D_R+n_R(n_R+3)/2-X*E_R^wheel+I_LL,
delta_ref=-PC-CP+CC.
```

The historical triangle retains units, prime squares and distinct historical pairs; the whole Euler compensation occurred before this adapter. MB's paper bound is `abs(delta_ref)<=40R`; SC's reported paper smoothing cost at T=R is `abs(e_smooth)<=6144R/log R`. These are credited upstream estimates, not newly Lean-certified by this report. The physical hyperbola responses I_Lnu and I_nuL are NOT the two middle-band reference terms PC and CP.

The new partition therefore gives the six-part complete accounting

```text
Z_R = S_rest + J_match + J_unmatched + J_far + delta_ref + e_smooth.
```

No term is dropped. If this is squared, retain all six diagonals and all fifteen doubled cross terms. The certificate computes the proper-band pieces, not S_rest or a full zero-target covariance. No numerical reconstruction of uncomputed full-source interactions is claimed.

### I. Mathematical Interpretation And Surviving Conjecture

Distance from the product cutoff is not enough to predict the signed band. At R=16 two positive near products coexist with a negative full J; after the reference is restored the centered M is positive. An unsigned count, a local sign, and an affordable error in amplitude do not transport the sign between these three objects.

The additional useful variable is **existence of the exact reflected product occurrence**. When both X-d and X+d belong to the actual prime rectangle, their pair has a uniformly summable curvature bias. When the reflected product is absent, no partner is invented. This is a valid small source reduction, not a mechanism that supplies the missing partners.

The surviving precise proper conjecture may be written

```text
exists C>=0, forall integer R>=16,
  abs(J_unmatched(R)+J_far(R))<=C R log R.
```

By BL3 this is equivalent up to a paid O(R) term to the original proper J_mid question on this domain. It is explicitly **not a newly independent assumption or a solved smaller sufficient RH lemma**. The finite excluded roots 8..15 do not settle the all-scale question. The applicable proper-band paper baseline remains MB's `384 R^(3/2)/log^2 R+40R` (or its minimum with FB's bound); BL3 does not change that full-band exponent. A genuinely useful next input must bound the signed unmatched-plus-far expression using new prime arithmetic, while S_rest remains unpaid before any global consequence.

### J. Falsification And Uncertainty Audit

BL1 refutes only the newly registered all-R>=16 localization rule. It does not refute OPEN-MIDBAND, an unspecified existential constant, a conditional first-bad theorem, or RH. BL3 is established by its displayed elementary paper argument, not inferred from its 39 finite checks. No optimal constant is claimed. The two independently evaluated reference-sign reversals are finite observations, not universal sign laws.

The first complete certificate and rational witness passed without a source correction. A later implementation change enabled the already-registered collar certificate on all held-out roots, instead of only the small witness. A self-audit then replaced a context-rounded multiplication in the separate collar-series tail bound with directed interval multiplication; all collar outputs were regenerated. The primary Gauss and exact-rational witness calculations were unaffected. No mathematical sample, hypothesis, weight, cutoff, or bound constant was fitted to output. The reflected-pair extension is separately timestamped and disclosed.

No local Lean, workflow trigger, source modification, branch/PR creation, merge, other-agent report edit, schedule change, or agent launch occurred. A malformed read-only commit lookup returned an error and was replaced by the correct immutable proof-head check query; it had no publication or mathematical effect.

### K. Two-Day Continuity And Formal Evidence

Both America/New_York dates were fetched at the pinned reporting snapshot. Relevant summaries, derivations, handoffs and resume sections were read; unrelated historical embedded programs were not rerun. Coordinator 00/90 mirrors had identical blobs on each date and were counted once.

| Role | November 9 Intake Blob | November 8 Blob | Consumed Scope |
| --- | --- | --- | --- |
| 00-coordinator-am | 9e7253329c409aa920d7e1d43e2fab8971bdc93b | 8b640304f6c233a2c4409b9882799de485888a9e | FB/MP/SHIFT; prior FM scope |
| 10-owner-payment | cfc6b8f473f7702c6e0759746095f048c1378756 | 4e1b83a1e5ff8c134e9ca64404397c70c2b07252 | FW/CT; prior JS finite-packet scope |
| 20-analytic-type-ii | 0f9b1362677ac9adbcec45225e5d6b172cf84cb9 | edecba8785a45cda87c0035d0348695941f1b8ea | SC/MB; prior EC, now inherited merged work |
| 30-finite-wheel | 932fe82483d30c49b6277baeaede629d29445b1e | 60d4cf1b65d4b1b2cc4f13f6c0940c14cb2c50fd | RA/DG; prior FD distinct carrier |
| 40-prime-census | 185b493a7c4bdc4dda79254f63c6541562e1140f | 00f4f9c0d670821a0c9d1da31fd1c4d0afd09142 | CR; prior FR distinct Mobius carrier |
| 50-adversarial-referee | TODAY=PENDING | 5371324ebbdbd88afb9abf843e83da2ce86b752f | TODAY=PENDING; prior EC acceptance, SG self-audit |
| 60-lean-verification | 873cc077a0eafb87a39c1c9c12ff22ad891d7ba7 | 5a110685bbe375d8ebff42df7391162914e52cef | RA implementation; prior EC repair/implementation |


Today's Referee is `TODAY=PENDING`; its November 8 findings are `YESTERDAY=CARRY_FORWARD`, not approval of FB/CT/MB/DG/BL. The external inbox is unchanged at `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry after October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 retain their source, endpoint and no-go qualifications; their historical task priorities do not override current main.

Formal evidence was checked directly. #1124 has thirteen successful completed checks at literal proof head `1b80f147dab3c0c2525052b3c6c3f8c447089da1`. The [targeted job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42600910899/job/129104842737) logs that checkout, Lean 4.34.1, dependency closures 746/772, and only propext, Classical.choice and Quot.sound. Its root-admission source was fetched at tested head and matches current main's blob.

#1122 has eleven successful attached checks at head `c53e9cf234500aea2605fd2557e638995f380407`. Its [targeted job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42561949462/job/128980092032) actually compiled synthetic merge `1e3c182076a6e1a23ef132c41a78b0f26adab507`; the full-wheel source at that checkout was fetched and matches current main. The compiler script, blob `eb3d429b14bf66ba2fba22e55b70ca0048f748c6`, explicitly uses `-DwarningAsError=true`. These are reused source-specific formal results, not a new complete main build and not certification of BL3.

No open/draft PR was returned at intake. Recent accepted source changes include #1124, #1123, #1118, #1121, #1122, #1120 and #1119; inherited formal progress is not credited as this invocation's discovery.

### L. Specialist Handoffs

**Coordinator:** record BL3 only as a paid O(R) subset of the proper band. Keep OPEN-MIDBAND and S_rest open. H_LOCAL is false; certified sign changes do not license a new universal rule. The finite data are now available with explicit errors rather than floating agreement alone.

**Owner:** reflection pairs require BOTH admitted prime products. At R=20 the exact pair is 391 and 407; at R=16 both close products have absent partners. Do not infer partner admission from geometric eligibility or identify the above-wall spectral term with a below-wall physical count.

**Analytic:** consume certified J, both unequal mixed terms, CC, M and weighted energies. MB2's amplitude equivalence does not preserve signs, as R=16 and R=127 show. A next genuine arithmetic argument must address unmatched and far products together, not replace them by this paid matched subset.

**Wheel:** BL3 uses product uniqueness and one-use matching, not DG's Hermitian cross-scale kernel. Quantify actual partner defects only with the original K_R weights and retained far complement; no unweighted coverage conjecture is being assumed.

**Referee:** independently audit BL3's phase interval, derivative bound, 4/765 constant, and one-use injection. For BL1, the small rational witness uses only ten products and no quadrature. Audit the primary Gauss derivative bounds and Decimal enclosures separately before promoting the numerical certificates beyond this report's self-audited status.

**Lean:** no immediate source/PR request. BL3 is not independently accepted, and its consumer is only a proper subset. Do not formalize a conditional remainder bound or decimal sign assertion as if the missing arithmetic were proved. Existing #1122/#1124 infrastructure is already paid.

### M. Ranked Experimental Portfolio

| Rank | Exact Candidate | Evidence / Falsifier | Disposition And Next Requirement |
| --- | --- | --- | --- |
| 1 | Uniform O(R log R) for the signed unmatched-plus-far K_R sum | Finite band certificates only; no all-scale supplier | CONTINUE as the existing proper conjecture, not a new independent hypothesis; require prime-specific signed control |
| 2 | Reflected collar subset satisfies 0<=J_match<=4R/765 | Complete paper proof plus exact finite partition and interval checks | SEND FOR REVIEW; do not optimize an already affordable constant |
| 3 | J_mid*J_close>=0 for every R>=16 | R=16 exact rational falsifier, R=257 held-out certificate | REJECT universal form; retain the oscillatory complement |
| 4 | Affordable reference correction preserves the sign of the band | R=16 and R=127 give opposite sign changes | REJECT that inference; retain PC, CP and CC |

### N. Next-Run Resume Capsule

```text
RUN=20261109-census-2; actual trigger=11:00:01 EST; one invocation.
MAIN=02f00cee544278ad1bb9022ee76fc5916d459a95.
ACK=FINITE_WHEEL_CENTERED_RH_V1.
NEW=BL1 localization falsifier; BL2 certified proper band/reference energies;
    BL3 reflected-pair O(R) paper payment; BL4 exact one-use classification.
KEEP=original spline/phase/nonconjugation; all above-wall products;
     both mixed orientations; virtual Euler cancellation; S_rest and all crosses.
OPEN=unmatched-plus-far signed band, full centered wheel, canonical VF, finite A/C, RH.
NEXT=independent BL review; a NEW quantitative prime-specific constraint on the
     unmatched-plus-far weighted sum, not another local-sign or matching-count scan.
DO_NOT_REPEAT=CR scan; unchanged BL samples; already paid root admission;
              refinement of the affordable 4/765 constant without a new consumer.
NEW_GLOBAL_ENDPOINT_GAIN=NONE. NEW_LEAN_PROOF=NONE.
```

Only the owned daily report is published. Final source freshness, execution metrics, script hashes and publication verification are recorded below after actual completion; no pending execution or write is reported as successful.

### Execution Manifest And Reproduction

Final data checks completed with exit code zero. Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0, g++ 13.3.0; no random seed or probable-prime test was used. Python syntax checks passed; C++ compiled with `-std=c++17 -O2 -Wall -Wextra -Werror`.

Measured subprocess times: scout 0.239 s; complete primary certificate run 374.898 s (R=4096 alone 322.884 s); 80-digit refinement 30.991 s; final collar partition 4.211 s; final independent audit 0.375 s. These exclude intake, compilation, mathematical derivation and report preparation. The finite run is COMPLETE; no calculation is left running.

The independent SciPy values lie within 2.113e-12 of the primary enclosing intervals, which is a diagnostic tolerance, not the basis of certification. All 39 C++ counts match. All 3 refined roots are contained in their original intervals. No disagreement in the exact carrier remains.

Reproduction commands, after placing the embedded programs together in the same working directory (their output paths use /workspace):

```bash
python band_probe.py
g++ -std=c++17 -O2 -Wall -Wextra -Werror band_reference.cpp -o /workspace/band_reference
python band_certificate.py --roots 16,64,127,257,549,1024,4096
python band_certificate.py --roots 16,127,257 --precision 80 --refine 2 --output /workspace/band-refined.json
python band_rational_witness.py
python band_pairs.py
python band_audit.py
```

Executed source SHA-256 hashes:

```text
b294bbd02d4ce587fd5fdecfd609b346f3385015dd2a7a710bffe4fae3ed0379  /workspace/band_probe.py
e59cf4e04c77864a9f5a9a39afd78711a81e7849fd7fc31258d548a15352b0c8  /workspace/band_certificate.py
077cb66db205338f944e47680754a06e7ba29bb5a59062ab6f3812164ae9101a  /workspace/band_rational_witness.py
8ed04a9822b7ecfd14cf30722bca4590a95d70da49efae3b940148e5ad9f589d  /workspace/band_reference.cpp
d2a3d98f6af9aa16f47d0fafbf1ce674f308b67ecf154b1b75ad52bfe0487d94  /workspace/band_audit.py
e2f812792a5fc194941fd9df42143261e77337be1b5db240c7950e56a149c26e  /workspace/band_pairs.py
```

Prepublication refresh at 2026-11-09 16:25 UTC confirmed main unchanged and all upstream November 9 blobs unchanged; today's Referee remains PENDING. The new report is appended to the freshly fetched own-report blob, never replacing prior content. Substantive publication is not claimed until the separate commit/readback receipt.



### Exact Executed Programs

#### band_probe.py

```python
"""Independent binary64 scouts; these are not numerical certificates."""
import json
import math
from pathlib import Path
import time

import numpy as np
from scipy.integrate import quad
from scipy.special import sici


def primes_upto(n):
    flags = bytearray(b'\x01') * (n + 1)
    flags[:2] = b'\x00\x00'
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p*p:n+1:p] = b'\x00' * ((n-p*p)//p + 1)
    return [p for p in range(2, n + 1) if flags[p]]


def kernel(v, R):
    v = np.asarray(v, dtype=float)
    ans = np.zeros_like(v)
    small = abs(v) < 0.25
    x = v[small]
    for k in range(18):
        j = 2*k+1
        moment = ((2**j-1)/j - 6/R*(2**(j+2)-1)/(j+2)
                  + 6/R**1.5*(2**(j+3)-1)/(j+3))
        ans[small] += (-1)**k*x**j/math.factorial(j)*moment
    x = v[~small]
    i0 = sici(2*x)[0] - sici(x)[0]
    i1 = (-2*np.cos(2*x)+np.cos(x))/x + (np.sin(2*x)-np.sin(x))/x**2
    i2 = ((-4*np.cos(2*x)+np.cos(x))/x
          +(4*np.sin(2*x)-2*np.sin(x))/x**2
          +2*(np.cos(2*x)-np.cos(x))/x**3)
    ans[~small] = i0 - 6/R*i1 + 6/R**1.5*i2
    return ans/math.pi


def scout(R, primes):
    X = R*R-1
    left = np.array([p for p in primes if R <= 2*p and p < R], dtype=np.int64)
    right = np.array([p for p in primes if R <= p <= 2*R], dtype=np.int64)
    products = (left[:, None]*right[None, :]).ravel()
    k = kernel(math.sqrt(R)*np.log(X/products), R)
    ceiling = math.isqrt(R) + (math.isqrt(R)**2 != R)
    width = X//(4*ceiling)
    close = abs(products-X) <= width
    rows = {'R': R, 'X': X, 'width': width,
            'pair_count': len(products), 'left_count': len(left), 'right_count': len(right),
            'J': float(sum(k)), 'J_close': float(sum(k[close])),
            'J_far': float(sum(k[~close])), 'abs_mass': float(sum(abs(k))),
            'abs_close': float(sum(abs(k[close]))),
            'close_counts': [int(sum(close & (products < X))), int(sum(products == X)),
                             int(sum(close & (products > X)))],
            'below': float(sum(k[products<X])), 'above': float(sum(k[products>X]))}
    rows['reinforces_close'] = rows['J']*rows['J_close'] >= 0
    rows['far_dominated'] = abs(rows['J_far']) <= abs(rows['J_close'])
    # A factored prime-polynomial integral is independent of the product antiderivative.
    lp, lq = np.log(left/R), np.log(right/R)
    a = math.log1p(-1/R**2)
    def integrand(tau):
        t = math.sqrt(R)*tau
        weight = 1/tau - 6*tau/R + 6*tau*tau/R**1.5
        pp = np.exp(-1j*t*lp).sum()*np.exp(-1j*t*lq).sum()
        return weight*(np.exp(1j*t*a)*pp).imag/math.pi
    alternative, _ = quad(integrand, 1, 2, epsabs=1e-9, limit=300)
    assert abs(rows['J']-alternative) < 1e-7
    rows['factored_J'] = alternative
    if R <= 48:
        rows['close_pairs'] = [[int(p), int(q)] for p in left for q in right if abs(p*q-X)<=width]
    return rows


def main():
    start = time.monotonic()
    roots = list(range(16, 49)) + [64, 127, 257, 549, 1024, 4096]
    primes = primes_upto(8192)
    for n in range(8193):
        assert (n in primes) == (n>=2 and all(n%d for d in range(2, math.isqrt(n)+1)))
    rows = [scout(r, primes) for r in roots]
    out = {'rows': rows, 'elapsed_seconds': time.monotonic()-start,
           'first_sign_failure': next((r for r in rows if not r['reinforces_close']), None),
           'sign_failures': [r['R'] for r in rows if not r['reinforces_close']],
           'dominance_failures': [r['R'] for r in rows if not r['far_dominated']]}
    Path('/workspace/band-scout.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    main()
```

#### band_certificate.py

```python
"""Directed-decimal finite certificates, with explicit Gauss remainders."""
import argparse
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN
from fractions import Fraction
import json
import math
from pathlib import Path
import time

import numpy as np
from band_probe import primes_upto

PREC = 64
DOWN = Context(prec=PREC, rounding=ROUND_FLOOR)
UP = Context(prec=PREC, rounding=ROUND_CEILING)
NEAR = Context(prec=PREC, rounding=ROUND_HALF_EVEN)


class I:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo=0, hi=None):
        if isinstance(lo, I):
            self.lo, self.hi = lo.lo, lo.hi
            return
        self.lo = Decimal(lo)
        self.hi = self.lo if hi is None else Decimal(hi)
        assert self.lo <= self.hi

    @staticmethod
    def frac(x):
        return I(DOWN.divide(Decimal(x.numerator), Decimal(x.denominator)),
                 UP.divide(Decimal(x.numerator), Decimal(x.denominator)))

    def __add__(self, x):
        x = I(x)
        return I(DOWN.add(self.lo, x.lo), UP.add(self.hi, x.hi))
    __radd__ = __add__

    def __neg__(self):
        return I(self.hi.copy_negate(), self.lo.copy_negate())

    def __sub__(self, x):
        return self + (-I(x))

    def __rsub__(self, x):
        return I(x) - self

    def __mul__(self, x):
        x = I(x)
        return I(min(DOWN.multiply(a, b) for a in (self.lo, self.hi) for b in (x.lo, x.hi)),
                 max(UP.multiply(a, b) for a in (self.lo, self.hi) for b in (x.lo, x.hi)))
    __rmul__ = __mul__

    def __truediv__(self, x):
        x = I(x)
        assert not x.lo <= 0 <= x.hi
        return self * I(DOWN.divide(Decimal(1), x.hi), UP.divide(Decimal(1), x.lo))

    def __rtruediv__(self, x):
        return I(x) / self

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        out, base = I(1), self
        while n:
            if n & 1:
                out = out * base
            n //= 2
            if n:
                base = base * base
        return out

    def ln(self):
        assert self.lo > 0
        return I(DOWN.next_minus(NEAR.ln(self.lo)), UP.next_plus(NEAR.ln(self.hi)))

    def sqrt(self):
        assert self.lo >= 0
        return I(max(Decimal(0), DOWN.next_minus(NEAR.sqrt(self.lo))),
                 UP.next_plus(NEAR.sqrt(self.hi)))

    def exp(self):
        return I(DOWN.next_minus(NEAR.exp(self.lo)), UP.next_plus(NEAR.exp(self.hi)))

    def mag(self):
        return max(self.lo.copy_abs(), self.hi.copy_abs())

    def pad(self, radius):
        r = I(radius).mag()
        return I(DOWN.subtract(self.lo, r), UP.add(self.hi, r))

    def mid(self):
        return NEAR.divide(NEAR.add(self.lo, self.hi), Decimal(2))

    def json(self):
        return [str(self.lo), str(self.hi)]


def cadd(z, w):
    return z[0]+w[0], z[1]+w[1]


def csub(z, w):
    return z[0]-w[0], z[1]-w[1]


def cmul(z, w):
    return z[0]*w[0]-z[1]*w[1], z[0]*w[1]+z[1]*w[0]


def cscale(z, a):
    return z[0]*a, z[1]*a


def expi(x):
    x = I(x)
    m = x.mid()
    radius = (x-I(m)).mag()
    k = 0
    y = I(m)
    while y.mag() > Decimal('0.125'):
        k += 1
        y = y/2
    square = -y*y
    c, s, ct, st = I(1), y, I(1), y
    for j in range(1, 25):
        ct = ct*square/((2*j-1)*(2*j))
        st = st*square/((2*j)*(2*j+1))
        c, s = c+ct, s+st
    error = (I(y.mag())**50/math.factorial(50)).hi
    z = c.pad(error), s.pad(error)
    for _ in range(k):
        z = cmul(z, z)
    return z[0].pad(radius), z[1].pad(radius)


def pi_interval():
    def atan_inv(q):
        s = sum((Fraction((-1)**k, (2*k+1)*q**(2*k+1)) for k in range(100)), Fraction(0))
        e = Fraction(1, 201*q**201)
        return I.frac(s).pad(I.frac(e).hi)
    return 16*atan_inv(5)-4*atan_inv(239)


def legendre(x, n):
    p0, p1 = x*0+1, x
    if n == 0:
        return p0, p0
    for j in range(2, n+1):
        p0, p1 = p1, ((2*j-1)*x*p1-(j-1)*p0)/j
    return p1, p0


def gauss_rule(n=16):
    roots, _ = np.polynomial.legendre.leggauss(n)
    data = []
    previous = Fraction(-1)
    for approx in roots:
        a = Fraction(str(float(approx))) - Fraction(1, 10**12)
        b = a+Fraction(2, 10**12)
        sa = legendre(a, n)[0] > 0
        assert (legendre(b, n)[0] > 0) != sa
        for _ in range(160):
            mid = (a+b)/2
            if (legendre(mid, n)[0] > 0) == sa:
                a = mid
            else:
                b = mid
        assert previous < a < b < 1
        previous = b
        node = I(I.frac(a).lo, I.frac(b).hi)
        pn, pp = legendre(node, n)
        derivative = n*(node*pn-pp)/(node*node-1)
        weight = 2/((1-node*node)*derivative*derivative)
        assert weight.lo > 0
        data.append((node, weight))
    assert sum(w for _, w in data).lo <= 2 <= sum(w for _, w in data).hi
    return data


def nodes_between(a, b, panels, rule):
    h = (I(b)-a)/panels
    return [(I(a)+h*(j+(node+1)/2), h*weight/2)
            for j in range(panels) for node, weight in rule]


def remainder(length, panels, derivative, n=16):
    coefficient = I.frac(Fraction(math.factorial(n)**4,
                                 (2*n+1)*math.factorial(2*n)**3))
    return (coefficient*I(length)**(2*n+1)*I(derivative)/panels**(2*n)).hi


def weight_derivative(R, V, m=32):
    first = sum(math.factorial(m)*I(V)**j/math.factorial(j) for j in range(m+1))
    linear = 6/I(R)*(2*I(V)**m+m*I(V)**(m-1))
    quadratic = 6/(I(R)*I(R).sqrt())*(4*I(V)**m+4*m*I(V)**(m-1)
                                                 +m*(m-1)*I(V)**(m-2))
    return (first+linear+quadratic).hi


def choose_panels(length, derivative, tolerance):
    panels = 1
    while remainder(length, panels, derivative) > Decimal(tolerance):
        panels *= 2
    return panels


def certificate(R, rule, pi, refine=1, collar=False):
    started = time.monotonic()
    assert R >= 16
    U, L, ell = I(R).sqrt(), I(R).ln(), I(2).ln()
    a = (I(R*R-1)/(R*R)).ln()
    primes = primes_upto(2*R)
    left = [p for p in primes if 2*p>=R and p<R]
    right = [p for p in primes if p>=R]
    lp, lq = [(I(p)/R).ln() for p in left], [(I(p)/R).ln() for p in right]
    mass_minus = (I(R)/(2*(L-ell))).hi
    mass_plus = (I(R)/L).hi
    ma, mb = I(len(left))+mass_minus, I(len(right))+mass_plus
    v = math.isqrt(R)+(math.isqrt(R)**2 != R)
    derivative = weight_derivative(R, v)
    maxmass = max((ma*ma).hi, (mb*mb).hi, (ma*mb).hi)
    panels_t = choose_panels(1, (I(derivative)*maxmass).hi, '1e-10')*refine
    t_nodes = nodes_between(1, 2, panels_t, rule)
    # Repeated Leibniz differentiation of R exp((1-it)s)/(L+s).
    lower_log = L-ell
    velocity = 1+2*U
    derivative_s = (2*R*math.factorial(32)*sum(
        velocity**j/(math.factorial(j)*lower_log**(33-j)) for j in range(33))).hi
    panels_s = choose_panels(ell.hi, derivative_s, '1e-12')*refine
    error_s = remainder(ell.hi, panels_s, derivative_s)
    s_minus = [(s, w*R*s.exp()/(L+s)) for s, w in nodes_between(-ell, 0, panels_s, rule)]
    s_plus = [(s, w*R*s.exp()/(L+s)) for s, w in nodes_between(0, ell, panels_s, rule)]
    def reference(t, data):
        z = I(0), I(0)
        for s, w in data:
            z = cadd(z, cscale(expi(-t*s), w))
        return z[0].pad(error_s), z[1].pad(error_s)
    def prime_transform(t, logs):
        z = I(0), I(0)
        for s in logs:
            z = cadd(z, expi(-t*s))
        return z
    names = ['J', 'PC', 'CP', 'CC', 'M', 'EA', 'EB', 'wrong_conjugated']
    total = {name: I(0) for name in names}
    X = R*R-1
    width = X//(4*v)
    close = [(p,q) for p in left for q in right if abs(p*q-X)<=width]
    close_logs = [(I(X)/(p*q)).ln() for p,q in close]
    if collar:
        total['J_close'] = I(0)
    for tau, wt in t_nodes:
        t = U*tau
        w = 1/tau-6*tau/R+6*tau*tau/(R*U)
        phase = expi(t*a)
        pm, pp = prime_transform(t, lp), prime_transform(t, lq)
        cm, cp = reference(t, s_minus), reference(t, s_plus)
        aa, bb = csub(pm, cm), csub(pp, cp)
        pairs = {'J':(pm,pp), 'PC':(pm,cp), 'CP':(cm,pp), 'CC':(cm,cp), 'M':(aa,bb),
                 'wrong_conjugated':(aa,(bb[0],-bb[1]))}
        for name, pair in pairs.items():
            total[name] = total[name]+wt*w*cmul(phase, cmul(*pair))[1]/pi
        total['EA'] = total['EA']+wt*w*(aa[0]*aa[0]+aa[1]*aa[1])
        total['EB'] = total['EB']+wt*w*(bb[0]*bb[0]+bb[1]*bb[1])
        if collar:
            total['J_close'] = total['J_close']+wt*w*sum(expi(t*x)[1] for x in close_logs)/pi
    masses = {'J': I(len(left)*len(right)), 'PC':I(len(left))*mass_plus,
              'CP':I(len(right))*mass_minus, 'CC':I(mass_minus)*mass_plus,
              'M':ma*mb, 'EA':ma*ma, 'EB':mb*mb,
              'wrong_conjugated':ma*mb, 'J_close':I(len(close))}
    errors_t = {}
    for name in total:
        # The wrong conjugate has phase width at most 2 log 2 + |a| < 2.
        bound = weight_derivative(R, 2*v) if name == 'wrong_conjugated' else derivative
        err = remainder(1, panels_t, (I(bound)*masses[name]).hi)
        if name not in ('EA','EB'):
            err = (I(err)/pi).hi
        total[name] = total[name].pad(err)
        errors_t[name] = str(err)
    reconstruction = total['M']-(total['J']-total['PC']-total['CP']+total['CC'])
    assert reconstruction.lo <= 0 <= reconstruction.hi
    assert total['EA'].lo > 0 and total['EB'].lo > 0
    cauchy = (total['EA']*total['EB']).sqrt()/pi
    if collar:
        total['J_far'] = total['J']-total['J_close']
    return {'R':R, 'precision':PREC, 'panels_t':panels_t,'panels_s':panels_s,
            'reference_component_error':str(error_s), 'outer_errors':errors_t,
            'intervals':{k:v.json() for k,v in total.items()}, 'cauchy':cauchy.json(),
            'close_pairs':close if collar else None,
            'elapsed_seconds':time.monotonic()-started}


def main():
    global PREC, DOWN, UP, NEAR
    p = argparse.ArgumentParser()
    p.add_argument('--roots', default='16,64,127,257,549,1024,4096')
    p.add_argument('--precision',type=int,default=64)
    p.add_argument('--refine',type=int,default=1)
    p.add_argument('--output',default='/workspace/band-certificates.json')
    args = p.parse_args()
    PREC=args.precision
    DOWN=Context(prec=PREC,rounding=ROUND_FLOOR)
    UP=Context(prec=PREC,rounding=ROUND_CEILING)
    NEAR=Context(prec=PREC,rounding=ROUND_HALF_EVEN)
    started=time.monotonic()
    rule, pi = gauss_rule(), pi_interval()
    # These exact identities exercise interval containment, not floating agreement.
    for k in range(32):
        z=sum(w*x**k for x,w in rule)
        exact=I(0) if k%2 else I(2)/(k+1)
        assert z.lo <= exact.lo and z.hi >= exact.hi
    results=[]
    for R in map(int,args.roots.split(',')):
        row=certificate(R,rule,pi,args.refine,collar=True)
        results.append(row)
        print(json.dumps(row),flush=True)
        Path(args.output).write_text(json.dumps({'rows':results,'elapsed_seconds':time.monotonic()-started},indent=2)+'\n')


if __name__ == '__main__':
    main()
```

#### band_rational_witness.py

```python
"""Independent rational series certificate for the predeclared R=16 witness."""
from fractions import Fraction as F
import json
import math
from pathlib import Path


def log_interval(x):
    z = (x-1)/(x+1)
    s = 2*sum((z**(2*k+1)/(2*k+1) for k in range(80)), F(0))
    e = 2*abs(z)**161/(161*(1-z*z))
    scale = 10**60
    a, b = s-e, s+e
    return F(a.numerator*scale//a.denominator, scale), F(b.numerator*scale//b.denominator+1, scale)


def atan_bounds(q):
    s = sum((F((-1)**k,(2*k+1)*q**(2*k+1)) for k in range(100)), F(0))
    e = F(1,201*q**201)
    return s-e, s+e


aa, bb = atan_bounds(5), atan_bounds(239)
PI = (16*aa[0]-4*bb[1], 16*aa[1]-4*bb[0])


def kernel(z):
    lo, hi = log_interval(F(255,z))
    m = (lo+hi)/2
    v = 4*m
    total = F(0)
    for k in range(25):
        j = 2*k+1
        moment = F(2**j-1,j)-F(6,16)*F(2**(j+2)-1,j+2)+F(6,64)*F(2**(j+3)-1,j+3)
        total += (-1)**k*v**j/math.factorial(j)*moment
    # w(tau)>=0 and w(tau)<=1 on [1,2].
    error = (2*abs(v))**51/math.factorial(51)+4*(hi-lo)/2
    values = [(total-error)/p for p in PI]+[(total+error)/p for p in PI]
    return min(values), max(values)


def outward_decimal(interval, digits=15):
    scale = 10**digits
    lo, hi = interval
    a = lo.numerator*scale//lo.denominator
    b = hi.numerator*scale//hi.denominator+1
    def fmt(v):
        return ('-' if v<0 else '')+str(abs(v)//scale)+'.'+str(abs(v)%scale).zfill(digits)
    return [fmt(a),fmt(b)]


def main():
    primes = [n for n in range(8,33) if n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))]
    left=[p for p in primes if p<16]
    right=[p for p in primes if p>=16]
    pairs=[(p,q) for p in left for q in right]
    vals={str(p*q):kernel(p*q) for p,q in pairs}
    all_sum=tuple(sum(vals[str(p*q)][i] for p,q in pairs) for i in (0,1))
    close_sum=tuple(sum(vals[str(p*q)][i] for p,q in pairs if abs(p*q-255)<=15) for i in (0,1))
    assert all_sum[1] < 0 < close_sum[0]
    out={'R':16,'primes_left':left,'primes_right':right,'J':outward_decimal(all_sum),
         'J_close':outward_decimal(close_sum),
         'product_terms':{z:outward_decimal(v) for z,v in vals.items()},
         'method':'exact Fraction atanh-log series and integrated sine series; no floating quadrature'}
    Path('/workspace/band-rational-witness.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':
    main()
```

#### band_reference.cpp

```cpp
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <vector>

bool prime(int n) {
    if (n < 2) return false;
    for (int d = 2; d <= n/d; ++d) if (n % d == 0) return false;
    return true;
}

int main() {
    std::vector<int> roots;
    for (int r = 16; r <= 48; ++r) roots.push_back(r);
    for (int r : {64,127,257,549,1024,4096}) roots.push_back(r);
    for (int r : roots) {
        const std::int64_t x = std::int64_t(r)*r-1;
        int ceiling = 0;
        while (ceiling*ceiling < r) ++ceiling;
        const auto width = x/(4*ceiling);
        std::int64_t pairs = 0, below = 0, equal = 0, above = 0;
        // Factor products independently instead of looping over the prime rectangle.
        for (int p = (r+1)/2; p < r; ++p) {
            if (!prime(p)) continue;
            for (std::int64_t n = std::int64_t(p)*r; n <= std::int64_t(p)*2*r; n += p) {
                const int q = static_cast<int>(n/p);
                if (!prime(q)) continue;
                ++pairs;
                if (std::abs(n-x) <= width) {
                    if (n<x) ++below;
                    else if (n==x) ++equal;
                    else ++above;
                }
            }
        }
        std::cout << r << ' ' << pairs << ' ' << below << ' ' << equal << ' ' << above << '\n';
    }
}
```

#### band_audit.py

```python
"""Cross-method checks and an exact full-wheel ledger at the decisive root."""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import subprocess
import time

import numpy as np
from scipy.integrate import quad_vec
from scipy.special import expi

from band_probe import primes_upto


def independent(R):
    pp=primes_upto(2*R)
    p=np.array([p for p in pp if 2*p>=R and p<R])
    q=np.array([p for p in pp if p>=R])
    # Direct u-coordinates, unlike the certified logarithmic-coordinate rule.
    z,w=np.polynomial.legendre.leggauss(160)
    u=R*(3+z)/4
    v=R*(3+z)/2
    wu=R/4*w/np.log(u)
    wv=R/2*w/np.log(v)
    def fn(tau):
        t=math.sqrt(R)*tau
        P=np.exp(-1j*t*np.log(p/R)).sum()
        Q=np.exp(-1j*t*np.log(q/R)).sum()
        C=np.dot(wu,np.exp(-1j*t*np.log(u/R)))
        D=np.dot(wv,np.exp(-1j*t*np.log(v/R)))
        A,B=P-C,Q-D
        phase=np.exp(1j*t*math.log1p(-1/R**2))
        ww=1/tau-6*tau/R+6*tau*tau/R**1.5
        return ww*np.array([(phase*P*Q).imag/math.pi,
                            (phase*P*D).imag/math.pi,
                            (phase*C*Q).imag/math.pi,
                            (phase*C*D).imag/math.pi,
                            (phase*A*B).imag/math.pi,
                            abs(A)**2, abs(B)**2,
                            (phase*A*B.conjugate()).imag/math.pi])
    vals,err=quad_vec(fn,1,2,epsabs=1e-10,epsrel=1e-12)
    return dict(zip(['J','PC','CP','CC','M','EA','EB','wrong_conjugated'],map(float,vals))),float(err)


def wheel16():
    R,X=16,255
    primes=primes_upto(15)
    cube=[(1,1)]
    for p in primes:
        cube += [(d*p,-mu) for d,mu in cube]
    primorial=math.prod(primes)
    delta=math.prod(F(p-1,p) for p in primes)
    phys=sum((mu*F(X%d,d) for d,mu in cube if d<=X),F(0))
    virt=sum((mu*F(X,d) for d,mu in cube if d>X),F(0))
    reciprocal=sum((F(mu,d) for d,mu in cube if d<=X),F(0))
    floor=sum(mu*(X//d) for d,mu in cube)
    survivors=sum(math.gcd(n,primorial)==1 for n in range(1,X+1))
    piX=len(primes_upto(X))
    assert phys+virt-X*delta == -floor == -survivors
    assert virt == X*(delta-reciprocal)
    assert piX == len(primes)-1+floor
    Z=float(expi(math.log(X))-piX)
    return {'R':R,'X':X,'primorial':primorial,'physical_divisors':sum(d<=X for d,_ in cube),
            'virtual_divisors':sum(d>X for d,_ in cube),'F_physical':str(phys),
            'F_virtual':str(virt),'F':str(phys+virt),'delta':str(delta),
            'floor_sum':floor,'survivors':survivors,'piX':piX,
            'Z_diagnostic':Z,'Z_normalized_diagnostic':abs(Z)/(R*math.log(R))}


def main():
    start=time.monotonic()
    scout=json.loads(Path('/workspace/band-scout.json').read_text())
    cert=json.loads(Path('/workspace/band-certificates.json').read_text())
    rows={r['R']:r for r in scout['rows']}
    run=subprocess.run(['/workspace/band_reference'],check=True,capture_output=True,text=True)
    for line in run.stdout.splitlines():
        R,total,below,equal,above=map(int,line.split())
        assert total==rows[R]['pair_count'] and [below,equal,above]==rows[R]['close_counts']
    differences=[]
    vals=[]
    for row in cert['rows']:
        R=row['R']
        ref,err=independent(R)
        for key,value in ref.items():
            lo,hi=map(float,row['intervals'][key])
            discrepancy=max(lo-value,value-hi,0)
            differences.append(discrepancy)
            assert discrepancy<1e-8
        vals.append({'R':R,'values':ref,'quad_error_diagnostic':err})
    # Product-equality atoms must have zero band kernel, not be erased from the source.
    assert rows[18]['close_counts'][1]==1
    assert [17,19] in rows[18]['close_pairs']
    from band_probe import kernel
    assert kernel(np.array([0.0]),18)[0]==0
    out={'independent_rows':vals,'max_distance_from_certificate':max(differences),
         'exact_cpp_roots':len(run.stdout.splitlines()),'wheel16':wheel16(),
         'endpoint_control':{'R':18,'pair':[17,19],'product':323,'band_value':0},
         'elapsed_seconds':time.monotonic()-start}
    Path('/workspace/band-audit.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':
    main()
```

#### band_pairs.py

```python
"""One-use reflected-product partition and independent collar certificates."""
import json
import math
from pathlib import Path
import time

from band_certificate import I, pi_interval
from band_probe import primes_upto


def collar_kernel(R,z,pi):
    U=I(R).sqrt()
    v=U*(I(R*R-1)/z).ln()
    total=I(0)
    for k in range(12):
        j=2*k+1
        moment=(I(2**j-1)/j-6*I(2**(j+2)-1)/(R*(j+2))
                +6*I(2**(j+3)-1)/(R*U*(j+3)))
        total=total+(-1)**k*v**j/math.factorial(j)*moment
    error=((2*I(v.mag()))**25/math.factorial(25)).hi
    return total.pad(error)/pi


def main():
    start=time.monotonic()
    roots=list(range(16,49))+[64,127,257,549,1024,4096]
    primes=primes_upto(8192)
    pi=pi_interval()
    results=[]
    for R in roots:
        X=R*R-1
        h=math.isqrt(R)+(math.isqrt(R)**2!=R)
        D=X//(4*h)
        products={}
        for p in primes:
            if not R<=2*p or not p<R:
                continue
            for q in primes:
                if R<=q<=2*R and abs(p*q-X)<=D:
                    assert p*q not in products
                    products[p*q]=(p,q)
        values={z:collar_kernel(R,z,pi) for z in products}
        offsets=[d for d in range(1,D+1) if X-d in products and X+d in products]
        paired={X+sign*d for d in offsets for sign in (-1,1)}
        matched=sum((values[X-d]+values[X+d] for d in offsets),I(0))
        unmatched=sum((v for z,v in values.items() if z not in paired),I(0))
        full=sum(values.values(),I(0))
        for d in offsets:
            pair=values[X-d]+values[X+d]
            bound=I(R).sqrt()*d*d/(pi*(X*X-d*d))
            assert pair.lo>0 and pair.hi<bound.lo
        assert not offsets or matched.lo>0
        assert matched.hi<(I(4*R)/765).lo
        residual=full-matched-unmatched
        assert residual.lo<=0<=residual.hi
        for z,v in values.items():
            if z<X:
                assert v.lo>0
            elif z>X:
                assert v.hi<0
            else:
                assert v.lo<=0<=v.hi
        results.append({'R':R,'D':D,'collar_count':len(products),'matched_pairs':len(offsets),
                        'offsets':offsets,'J_close':full.json(),'J_match':matched.json(),
                        'J_unmatched':unmatched.json(),
                        'small_pairs':[[products[X-d],products[X+d]] for d in offsets] if R<=48 else None})
    out={'rows':results,'elapsed_seconds':time.monotonic()-start}
    Path('/workspace/band-pairs.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps([{k:r[k] for k in ['R','collar_count','matched_pairs','offsets','J_match','J_unmatched']} for r in results],indent=2))


if __name__=='__main__':
    main()
```

### Executed Data

The primary and refined records omit only the verbose complete collar pair lists; the programs reconstruct them exactly. Pair-partition offsets and the small witness are retained. JSON decimal endpoints are strings so their precision is not lost.

```json
{
  "primary": {
    "rows": [
      {
        "R": 16,
        "precision": 64,
        "panels_t": 1,
        "panels_s": 1,
        "reference_component_error": "6.468605688613288849294478435399993259545548349890687605332154610E-26",
        "outer_errors": {
          "J": "1.457635698731562088088094606218778239675984612208061524605535348E-17",
          "PC": "1.682339035186194970696488998067471083815863411757827551746037559E-17",
          "CP": "2.803898391976991617827481663445785139693105686263045919576729264E-17",
          "CC": "3.236136244209395735667330832026064476945556430295958410530687437E-17",
          "M": "9.180009370104144412279396099758098940130510140524893406458989611E-17",
          "EA": "1.565643221336510975626919174229565167061381351545174178328239095E-16",
          "EB": "5.312429655204055942809339999750565939050733940993675179098014906E-16",
          "wrong_conjugated": "5.012115291610062423931438048264916359152444702062895601857729906E-15",
          "J_close": "2.915271397463124176176189212437556479351969224416123049211070696E-18"
        },
        "intervals": {
          "J": [
            "-0.1357681993763243707190609393777136935375342298500191601830289327",
            "-0.1357681993763243415663469647464719317756421054744543664419435136"
          ],
          "PC": [
            "-0.2442864883038773602422200081921412977584483975079234877795835744",
            "-0.2442864883038773265954392728542324550258489702266383579331010295"
          ],
          "CP": [
            "-0.1004266674235791690593489551437865458361917880522500907195906198",
            "-0.1004266674235791129813810855895735981654217671475852752484079410"
          ],
          "CC": [
            "-0.1750196072226541535629247470096683521460416768396426053927760324",
            "-0.1750196072226540888401997883641499789828300743967642664354912746"
          ],
          "M": [
            "0.03392534912847791529483472726263188959897023149678168783256580204",
            "0.03392534912847809889502215501909805074489260487673630444599337293"
          ],
          "EA": [
            "0.08396949809355287840438261572388580610848944325162727013515817037",
            "0.08396949809355319153302693407808499994517723942342153945162355857"
          ],
          "EB": [
            "0.3130676056466670352693636266206028805097238010374116520252382757",
            "0.3130676056466680977552947741653742686348394252481812301111881309"
          ],
          "wrong_conjugated": [
            "0.01745574067703208063966108479605985106857118423048217312450523178",
            "0.01745574067704210487024433059448562950266809228117629202469158996"
          ],
          "J_close": [
            "0.02400839686476219440328456363182069050335495368814657578678530385",
            "0.02400839686476220023382735855806904285573337856325953451564265641"
          ],
          "J_far": [
            "-0.1597765962410865709528882979357827363932676084132786946986715892",
            "-0.1597765962410865359696315283782926222789970591626009422287288174"
          ]
        },
        "cauchy": [
          "0.05160953805759038737206578148475357072775013806549857945586698084",
          "0.05160953805759057117599731960935793567397989487892757450283909813"
        ],
        "elapsed_seconds": 0.8397051829999782
      },
      {
        "R": 64,
        "precision": 64,
        "panels_t": 1,
        "panels_s": 1,
        "reference_component_error": "3.282593143287786015925173276339622635611947386332780982431859640E-19",
        "outer_errors": {
          "J": "7.242163344628666335818778987134439408944366610193638238931899514E-15",
          "PC": "8.572909245213214989127363684865490391086669136711898532548338608E-15",
          "CP": "9.552670301809010987884776677421546435782288466621829793411005876E-15",
          "CC": "1.130797134085508719623299765022284209097023116146151402147261043E-14",
          "M": "3.667571423250597950906391699964431832678355537498888058636385445E-14",
          "EA": "6.588516796175894983979953853156037973087213764319350801834185893E-14",
          "EB": "2.014973079708059758727842974364968889109314936765545387695482845E-13",
          "wrong_conjugated": "1.093234039090869217663630491207220598750713594278163791513506137E-10",
          "J_close": "7.162579132050329343117473723539555459395527416675026829712867654E-16"
        },
        "intervals": {
          "J": [
            "-0.4779205724124989145420566261687136540268197636541577198055473269",
            "-0.4779205724124844302153673688360420164688454947753398302622912635"
          ],
          "PC": [
            "-0.5516215363408948843610627429273893244564479666772826916688158589",
            "-0.5516215363408777383232706473280555661501061524364795430432852209"
          ],
          "CP": [
            "0.2927449772224225451482475075280542135735550041194380136186961198",
            "0.2927449772224416509167080805937654915396666323826667614368094921"
          ],
          "CC": [
            "0.01625501244036337292060050006166828853911262881419080533239915852",
            "0.01625501244038598941816408416248102464775275909257052064167544511"
          ],
          "M": [
            "-0.2027890008536994538274134925706204057145426091804710539812915835",
            "-0.2027890008536261019718681160763607661092978241441493145731754007"
          ],
          "EA": [
            "1.311333662006929646730221967798860829872220359250185200133625501",
            "1.311333662007061418435933041217459566827082273325589417084601805"
          ],
          "EB": [
            "1.419459551306686255753486539296745889261686871358328427804175171",
            "1.419459551307089251674942595152450627549111288992275339166768207"
          ],
          "wrong_conjugated": [
            "0.06903216202547040501359106653410913446762245445163639668225546710",
            "0.06903216224411721325884527460207674448031207060144728795014700517"
          ],
          "J_close": [
            "-0.1462022617988296739358712806930109971528554781155154500968756441",
            "-0.1462022617988282414200448706271423736581107702044235708428120201"
          ],
          "J_far": [
            "-0.3317183106136706731220117555415712803687089934497341489627353068",
            "-0.3317183106136547562794960881430310193159900166598243801654156194"
          ]
        },
        "cauchy": [
          "0.4342784137895105292857830745258548869126117506206887758790226361",
          "0.4342784137895939964647280275327280273357547169856321262065538266"
        ],
        "elapsed_seconds": 1.1524920979999251
      },
      {
        "R": 127,
        "precision": 64,
        "panels_t": 1,
        "panels_s": 1,
        "reference_component_error": "1.269785228465067711822465015422111080973580970557763053989558548E-14",
        "outer_errors": {
          "J": "1.251403177720156932442287322008156908080910891463847283579976886E-12",
          "PC": "1.367000977442348596843200973205541626809828989482486062944891273E-12",
          "CP": "1.595264953413864781802027652162740704776962143162542115824507761E-12",
          "CC": "1.742626828364933154311544859950072436829567801796267850070481062E-12",
          "M": "5.956295936941303465399060807326511676497269825905143312419856979E-12",
          "EA": "1.017176463264074799913265349934097448538917778368017973747299589E-11",
          "EB": "3.442357552671740678783560118816566166754665846378209083196580442E-11",
          "wrong_conjugated": "9.283047564311138534022938649233474213023743494823546877500594725E-7",
          "J_close": "8.690299845278867586404773069501089639450770079610050580416506146E-14"
        },
        "intervals": {
          "J": [
            "0.3761193976785712109914422204007365213987513815964901412178696408",
            "0.3761193976810740173468825342656210960427676954126519650274395406"
          ],
          "PC": [
            "0.9154560021015441473727377228192315764996537193728411302034336528",
            "0.9154560021043037354858261489454220252748971206614584585664395582"
          ],
          "CP": [
            "0.09058369921429993044404795056321356373242639164650032493832257847",
            "0.09058369921751600451182371983108188504420004590535758237412751035"
          ],
          "CC": [
            "-0.07599524725154369724382182342552701421868945500019441331202857936",
            "-0.07599524724802192298087371594270745822929332243526497258512800903"
          ],
          "M": [
            "-0.7059155508947637053226968453763460696046000716551173931519603670",
            "-0.7059155508828205043781094815142199960403373976857961409336375502"
          ],
          "EA": [
            "7.905907693123204883923690336243487931921264140066726979300919546",
            "7.905907693143686914507253244356734240067982025299847337593101705"
          ],
          "EB": [
            "1.443513710470210763226360031337691833136865735090842099844605822",
            "1.443513710539111530005333844894847882850637220432401968804988951"
          ],
          "wrong_conjugated": [
            "-0.1203299137645476618029503183561364219884222289139139234150330894",
            "-0.1203280571550041905045387568370786233439699735488882458271316593"
          ],
          "J_close": [
            "0.07382919351957743917366860893309033760534586322109640887195047782",
            "0.07382919351975124517057418628481843306673588501388542434873360606"
          ],
          "J_far": [
            "0.3022902041588199658208680341159180883320154965826047168691360347",
            "0.3022902041614965781732139253325307584374218321915555561554890628"
          ]
        },
        "cauchy": [
          "1.075316855933595573279875120395594169805517801818574592465031462",
          "1.075316855960651626841259045906547249114251903338259657883859013"
        ],
        "elapsed_seconds": 1.864776230000075
      },
      {
        "R": 257,
        "precision": 64,
        "panels_t": 2,
        "panels_s": 2,
        "reference_component_error": "2.274319146326125439182135565132136628681320919158237600581533181E-19",
        "outer_errors": {
          "J": "1.484462404208302685000711776186143093181500332259636651196959307E-19",
          "PC": "1.598870137662588871121273631355037962008783639667394566017517444E-19",
          "CP": "1.707938290254567889602401956843075438102320393414003128206396131E-19",
          "CC": "1.839569342758067180303924726881887287294418854334613440223950795E-19",
          "M": "6.630840174883526626028312091266143780587023219675647785644823677E-19",
          "EA": "1.153652053119822987984787152541882576624540633836064960994407024E-18",
          "EB": "3.761508281291996593562488782643494964968745624625681782030023609E-18",
          "wrong_conjugated": "6.638280272677866377451865107875680003429531214491954573897733881E-12",
          "J_close": "6.153989744442913052075751549406659941399546372360475500412065881E-21"
        },
        "intervals": {
          "J": [
            "1.589805042010415792722347012946612189626483243356673661595357278",
            "1.589805042010415793019239493788272726626625598593902282188037505"
          ],
          "PC": [
            "0.5224491739687429170033091885688243596494695708712113612225973435",
            "0.5224491739687429177737292887032964067763993497231359484559203470"
          ],
          "CP": [
            "0.4885084706727661461087532826413936311867611460797381033129746028",
            "0.4885084706727661469653941570567211930748894497657500003259411326"
          ],
          "CC": [
            "-0.1070262116258177194484587885837518979806182506546209875716976894",
            "-0.1070262116258177183850455123571754077400859034807732680116319018"
          ],
          "M": [
            "0.4718211857430890091198329814670482899531714177209794414009587984",
            "0.4718211857430890109370633073566737299042282972989676723631355864"
          ],
          "EA": [
            "3.411283175804363964311127953987092503835564595275142163950755830",
            "3.411283175804363968203420429365217089834179628314457887095943579"
          ],
          "EB": [
            "2.888540868251030572748297452822018251758065358191621101496142030",
            "2.888540868251030581770633899179936187918037694584292388803674908"
          ],
          "wrong_conjugated": [
            "0.05219874417665778219854906598395831883971408015435698254380517112",
            "0.05219874418993434323496708965178216380085990148597551930341391220"
          ],
          "J_close": [
            "-0.1534403737498832753439690090756280611195507994888168104508281586",
            "-0.1534403737498832753316610295867422350153992963900034904111190402"
          ],
          "J_far": [
            "1.743245415760299068054008042533354424641882539746677152006476318",
            "1.743245415760299068363208502863900787746176398082719092638865664"
          ]
        },
        "cauchy": [
          "0.9991904435928346313022822369958906685597577938612591931935536818",
          "0.9991904435928346334328051265282394270131894730993706685514297051"
        ],
        "elapsed_seconds": 10.497366466000017
      },
      {
        "R": 549,
        "precision": 64,
        "panels_t": 2,
        "panels_s": 2,
        "reference_component_error": "5.288861897115363430649991623353314993984410000622678515920304067E-14",
        "outer_errors": {
          "J": "5.607291754712923233326645426465840409715485382996103001359652708E-16",
          "PC": "5.879615735770164193303215712665680655387962463363732871169145672E-16",
          "CP": "6.375012724585558915920421813865794460185970670366241178320873331E-16",
          "CC": "6.684621876452954376879844159211342690099435930413141058324637064E-16",
          "M": "2.454654209152160071943012711220865821538885444713921810917430880E-15",
          "EA": "4.167424922205218499521506829950360275029140124016891024353411305E-15",
          "EB": "1.426962640360168150393617743853087372698062689197992034582494851E-14",
          "wrong_conjugated": "6.440611088430608600710156288977129434638126687819391394659427240E-7",
          "J_close": "1.555398945689491174276654237097557300537498046838369843470455641E-17"
        },
        "intervals": {
          "J": [
            "0.4028220306792257201541886799967817271238706675687784959307462979",
            "0.4028220306792268416125396225814283924529559607368604406450658855"
          ],
          "PC": [
            "0.7787803010806769873963276091043555807065618629461585938202163075",
            "0.7787803010807458764341705753905051659894441399901181362566442812"
          ],
          "CP": [
            "-1.136907543044620335448835446975397791941139686747236858363252250",
            "-1.136907543044431978091153755531642917327037369441143246344317397"
          ],
          "CC": [
            "-0.4911032580580400552496733642738900406879019117370171181067963012",
            "-0.4911032580578097279236340795204245058629742530377457752495471858"
          ],
          "M": [
            "0.2698460145850440426203833520434500822986422899259475809395439662",
            "0.2698460145851881856825285245414452141311849229573858399417013009"
          ],
          "EA": [
            "3.827645500496580309374522523041348598119265645823222108465347015",
            "3.827645500496985888413406714517216073714396331891779221370102697"
          ],
          "EB": [
            "5.488294028303998873913651806663881969200938845071588581999116007",
            "5.488294028304504904520110271354339526556691211041700687353598155"
          ],
          "wrong_conjugated": [
            "0.4893263578982554304403130241910194841542772266916695748537466436",
            "0.4893276460206123503157600344001285253872843456168023199062013191"
          ],
          "J_close": [
            "0.2295532899921116336316765379550376711117048108836340457692721640",
            "0.2295532899921116647396554517448611566447895528347800567539778425"
          ],
          "J_far": [
            "0.1732687406871140554145332282519205704790811147339984391767684554",
            "0.1732687406871152079808630846263907213412511498532263948757937215"
          ]
        },
        "cauchy": [
          "1.458930711635026474930507706411795059321928755190831418217218228",
          "1.458930711635171027428971535592345585025787197500592706811467407"
        ],
        "elapsed_seconds": 13.690058668000006
      },
      {
        "R": 1024,
        "precision": 64,
        "panels_t": 2,
        "panels_s": 4,
        "reference_component_error": "3.546999345992623095902205673495872712156620681721871506056593979E-19",
        "outer_errors": {
          "J": "2.764649547861483703261621960616822009553309798850051507625868682E-12",
          "PC": "2.981219927821586632284977367607656848006950530550948639312562305E-12",
          "CP": "3.025386148974499026837347402683325838347794242114666396932007671E-12",
          "CC": "3.262381477484131718222451360850831244409047602124235725174454501E-12",
          "M": "1.203363710214170108060639809175863594031710217363990226904489316E-11",
          "EA": "2.085513302222621302562351336682304335896224855881431067373163512E-11",
          "EB": "6.852997948445153288177372854207879490536033147349531844235653647E-11",
          "wrong_conjugated": "0.01300633062575293968510683882345002928265090541787614251711138005",
          "J_close": "6.215416501761583800033427473503512255054156336100845725173485790E-14"
        },
        "intervals": {
          "J": [
            "-6.314323301619939615165654528455083833839856980394443275158021059",
            "-6.314323301614410316069931561048560589918623336375336651159049841"
          ],
          "PC": [
            "-1.504447652020258870453254812146969342539709403892133890793108776",
            "-1.504447652014296429597265001343434370713316650821999141298221630"
          ],
          "CP": [
            "-0.9997320142125411633402414971256641492665410636530278248313126658",
            "-0.9997320142064903891791839370396757176783014677887642265889688451"
          ],
          "CC": [
            "-0.6310496449939561213369742168566087811356903289268179458290739458",
            "-0.6310496449874313564250913602997759453240297668960480324104868506"
          ],
          "M": [
            "-4.441193280393108916341700469006745962778492498057055129612845912",
            "-4.441193280369041640086005949997539607302326838658311721125471241"
          ],
          "EA": [
            "9.636861415161279430219574152378217638749720291508887355976254740",
            "9.636861415202989700787834524745178861842426437530700465249247176"
          ],
          "EB": [
            "31.70970962945209566816771948543055515056717036449691770731178429",
            "31.70970962958915563550163385117912068319964347325006346847802422"
          ],
          "wrong_conjugated": [
            "0.7024244547284848700564125206588483814480507671470028903369626067",
            "0.7284371159799907514780373151537419993060009655008643770837912082"
          ],
          "J_close": [
            "-0.1227331223632335672930389936237629524041896585791572621488311674",
            "-0.1227331223631092589630037619477622838547195883340561788965698456"
          ],
          "J_far": [
            "-6.191590179256830356202650766507321549985137392060387096261451214",
            "-6.191590179251176748776892567424797637514433677796179389010218673"
          ]
        },
        "cauchy": [
          "5.564345223223508627928070695064076756244241860691726460438161294",
          "5.564345223247575909706070098479348663484268280253833210437293222"
        ],
        "elapsed_seconds": 22.283492125999942
      },
      {
        "R": 4096,
        "precision": 64,
        "panels_t": 8,
        "panels_s": 8,
        "reference_component_error": "8.633790032094686837926536029049394457382240312303149583764969509E-19",
        "outer_errors": {
          "J": "1.853924689573307544798614093089434715656490069068411283235115884E-21",
          "PC": "1.967557116931694139076646587404808443748256832157659066172652044E-21",
          "CP": "1.952826742794237605415110195841349984811104107211024185463338071E-21",
          "CC": "2.072521164170735705137879779106767664773629385215270316752325233E-21",
          "M": "7.846829713469974994428250655442360808989480393652364851623431230E-21",
          "EA": "1.349550138259503688575513472565630996737812758389925111691977070E-20",
          "EB": "4.502971282314881198453321807878240914506527020949915984645402593E-20",
          "wrong_conjugated": "2.303487666445441606547558751464550084075171101965480183645925069E-11",
          "J_close": "1.985228686350051267122924320439751339365088672675521548224215538E-23"
        },
        "intervals": {
          "J": [
            "-9.022460377467389281113268564917804823231456281223312517168386631",
            "-9.022460377467389281109560715538658208141859053037133627618034065"
          ],
          "PC": [
            "-1.376669493509135317046248708208991387867125964698278190396187257",
            "-1.376669493509135312528153203256349873248138062660087308394111688"
          ],
          "CP": [
            "-6.942345439397818423062000350914229611685860411500607388322464598",
            "-6.942345439397818415721351063759952398755628277434230268981003332"
          ],
          "CC": [
            "0.1622990419849765912865322955787368409926033462628062466480705775",
            "0.1622990419849765994998922686238790371339197395359160255927753687"
          ],
          "M": [
            "-0.5411464025754589562962361492032558554694266108462339176839134391",
            "-0.5411464025754589467824152409110680262375359426113576190001475192"
          ],
          "EA": [
            "45.40120266377273871459366517997901968530937272001524133508666860",
            "45.40120266377273873788718425798480293790143088504670976756336018"
          ],
          "EB": [
            "114.0312473881907468240787996581530827236902125608964419411450058",
            "114.0312473881907468605805004655150747723205394204773223116111960"
          ],
          "wrong_conjugated": [
            "-1.752831909761033891928471981730385391844360065114766633116435203",
            "-1.752831909714964129101435900734186337572034896509271632625944446"
          ],
          "J_close": [
            "-0.7327297775608075796415328908628569352865256025692201774492151885",
            "-0.7327297775608075796414931862891299342611831440828113816725418279"
          ],
          "J_far": [
            "-8.289730599906581701471775378628674888970273137140501135495844804",
            "-8.289730599906581701468027824675801272855333450467913450168818876"
          ]
        },
        "cauchy": [
          "22.90317774432397219078974065666743021667830494754299855008218080",
          "22.90317774432397220033077088094996822139091783402370321629660391"
        ],
        "elapsed_seconds": 322.884398571
      }
    ],
    "elapsed_seconds": 374.89761721800005
  },
  "refined": {
    "rows": [
      {
        "R": 16,
        "precision": 80,
        "panels_t": 2,
        "panels_s": 2,
        "reference_component_error": "1.5060896260229146222803924315143360894977926159954368149238066756693931154511178E-35",
        "outer_errors": {
          "J": "3.3938225794852759877408263418329372994508235999570729318203761145562780398887575E-27",
          "PC": "3.9170008040643180038232565812474840409491756273382984840917343261766087075296034E-27",
          "CP": "6.5283346734405300063720943020791400682486260455638308068195572102943478458826725E-27",
          "CC": "7.5347168469088984086814588681470241326502441202661916858765467976101040562343460E-27",
          "M": "2.1373874903899022406617636093306585541298869393125393908608214448637338649535380E-26",
          "EA": "3.6452971895609772196666318323220246635875230458219865763751768044958884193612270E-26",
          "EB": "1.2368964159870650486111035569921522259364682112340059082717669152884389491404203E-25",
          "wrong_conjugated": "1.1669740294129733051945078299066322760545752714534512725327466307100664389794697E-24",
          "J_close": "6.7876451589705519754816526836658745989016471999141458636407522291125560797775149E-28"
        },
        "intervals": {
          "J": [
            "-0.13576819937632435614270395545591539214186415508204784234094392059849958767495096",
            "-0.13576819937632435614270394866827023317131217960039515850973674422498816263169657"
          ],
          "PC": [
            "-0.24428648830387734341882964444018662021024496983560913252716127447209246589452177",
            "-0.24428648830387734341882963660618500471545528831185020665842631147840793122509370"
          ],
          "CP": [
            "-0.10042666742357914102036502689501486136305220118764556737863296705218755513648216",
            "-0.10042666742357914102036501383834550749421503198055946332438651294408028477579543"
          ],
          "CC": [
            "-0.17501960722265412120156227522162512659289660427897660919275587258314173103241653",
            "-0.17501960722265412120156226015219141544754101471282074995070761839136805411761079"
          ],
          "M": [
            "0.033925349128478007094928419766990006325760258732439047162623870114530550107818612",
            "0.033925349128478007094928462514739820103593278908984962731839040034240218428544028"
          ],
          "EA": [
            "0.083969498093553034968705279041482536037196232435971027222560196012990900664279688",
            "0.083969498093553034968705351947426339156165743822397837540550125195002178006124546"
          ],
          "EB": [
            "0.31306760564666756651232907916184942599599841599519089206430076652279656690442902",
            "0.31306760564666756651232932654113264826046928634676665224082781469593124732710280"
          ],
          "wrong_conjugated": [
            "0.017455740677037092754951540721248542843471743802142006248011683391099026446695921",
            "0.017455740677037092754953874669307374769870339759075548463547521364499810915530993"
          ],
          "J_close": [
            "0.024008396864762197318555960416180350782488968577537786772301711675778546115866488",
            "0.024008396864762197318555961773709382576599363673868323530126248988541723304824808"
          ],
          "J_far": [
            "-0.15977659624108655346125991722962477471846351875591616587107016958704131097977577",
            "-0.15977659624108655346125990908445058395380114817793294528203845590076670874756305"
          ]
        },
        "cauchy": [
          "0.051609538057590479274031695482544814622143525633286292046835443665691652091416161",
          "0.051609538057590479274031738277732500759514110391270715480008200366561747495856794"
        ],
        "elapsed_seconds": 2.862751461000016
      },
      {
        "R": 127,
        "precision": 80,
        "panels_t": 2,
        "panels_s": 2,
        "reference_component_error": "2.9564491204569761450925493040636905491668287910468947468082385782149155724353684E-24",
        "outer_errors": {
          "J": "2.9136500733908194406942634890045898688978303490761837074066905194373744936164841E-22",
          "PC": "3.1827971745337094106785975704098623870169487536942727466693410224336355790564120E-22",
          "CP": "3.7142656590181048535789075590733920800894548724464655756589671257023164575493154E-22",
          "CC": "4.0573692609670878255542946512579741813930864487687774237023690850633848024778825E-22",
          "M": "1.3868082167909721530506063269745818517397320423985699453437367752636711332700093E-21",
          "EA": "2.3682985065134121103055434067130495061607048343122423946561747722890060695357484E-21",
          "EB": "8.0148632467532080569853077615065643721135934963315005488614095798594474922853483E-21",
          "wrong_conjugated": "2.1613779394680491029338302671055947926416395918520975107095657573013370785240316E-16",
          "J_close": "2.0233681065214023893710163118087429645123821868584609079213128607203989539003361E-23"
        },
        "intervals": {
          "J": [
            "0.37611939767982261416887101231418713635312793813862333776753093398225631727437966",
            "0.37611939767982261416945374232886530024126679083642425742280510852486997086921358"
          ],
          "PC": [
            "0.91545600210292393203250971820340889085622813106283403540757416399909458047285990",
            "0.91545600210292393203315222282242076082511324435567471040001513859577134362588088"
          ],
          "CP": [
            "0.090583699215907985875952744123843330674874325431420424013640582191188839210466862",
            "0.090583699215907985876701571050738062720755100622349452164973026352427014719733818"
          ],
          "CC": [
            "-0.075995247249782788462093920750753919233713396171523676779613996042482658598180946",
            "-0.075995247249782788461273933856995728116292917362155459729313788060550211015969646"
          ],
          "M": [
            "-0.70591555088879209220307005263844852678625574048418640730617682002615607372044402",
            "-0.70591555088879209220028930352665972904632664554861757608484042843488991220280976"
          ],
          "EA": [
            "7.9059076931334459262820942004650645691505802967001919801767666708744816052702355",
            "7.9059076931334459262868630672310467253124833334221545054077259656475449221473752"
          ],
          "EB": [
            "1.4435137105046610871711773625693934252855698746633718561722572805088991344397611",
            "1.4435137105046610871872195873817935803894797060843471196763067611151926383835557"
          ],
          "wrong_conjugated": [
            "-0.12032898545977611974910680049286170581363019470353638445958182164291717872741374",
            "-0.12032898545977568747351177420483426561374889130295818876445422758437466234403662"
          ],
          "J_close": [
            "0.073829193519664342172101163927889171312147163954372829142975741668405748751882860",
            "0.073829193519664342172141631290019599359934584280609004077708340269662410511371652"
          ],
          "J_far": [
            "0.30229020416015827199672938102416753699319335385801433368982259371259390676300800",
            "0.30229020416015827199735257840097612892911962688205142827982936685646422211733072"
          ]
        },
        "cauchy": [
          "1.0753168559471235797602972987920142270212670747787805059539083723077925869182251",
          "1.0753168559471235797665967842437010316939422679649960467468740357770507754717501"
        ],
        "elapsed_seconds": 4.457611794999934
      },
      {
        "R": 257,
        "precision": 80,
        "panels_t": 4,
        "panels_s": 4,
        "reference_component_error": "5.2953119071343108992607695170029453669705449583899173899123750141674782969197544E-29",
        "outer_errors": {
          "J": "3.4562833705178990145230474327368268118740532832677398137677444569345935555790186E-29",
          "PC": "3.7226596327093170749053210750106674665789670303170442721283003556059593503284682E-29",
          "CP": "3.9766037144106065146680966877450128973050052146753369090296237706974268169393944E-29",
          "CC": "4.2830811412028669852389132764234377241097829638389252131431148874314127525786879E-29",
          "M": "1.5438627858840689589335378471915944899867808492099046208068783470669392475425568E-28",
          "EA": "2.6860555008049658219907133666376643269894193714392952644135966370173876943009456E-28",
          "EB": "8.7579439424257646164914797587401582043821588731968816882698414638902255860689826E-28",
          "wrong_conjugated": "1.5455950686423728190017550037884339698193434659605740043096555981641474682988226E-21",
          "J_close": "1.4328373932379561131996455484551051495130049000402156963041205534309235164685517E-30"
        },
        "intervals": {
          "J": [
            "1.5898050420104157928707932533328832465549206224397670731774620392515363203489417",
            "1.5898050420104157928707932534020089139652786027302280240108333951226206953007837"
          ],
          "PC": [
            "0.52244917396874291738779931035488844618638224680139254278348410732063992680678345",
            "0.52244917396874291738779931053429212704850327706063970252883052578747653282428859"
          ],
          "CP": [
            "0.48850847067276614653676065201304576390733420596782935834504607494389012384339675",
            "0.48850847067276614653676065221255244013070894355110836182229326042274460211814556"
          ],
          "CC": [
            "-0.10702621162581771891744596417949359506398414384910438377790272869256170588303150",
            "-0.10702621162581771891744596393174238649033629800235003542205073031947267657910771"
          ],
          "M": [
            "0.47182118574308901002878732654294139111061557864542132280307116642530299733611580",
            "0.47182118574308901002878732696593601058233453129214938970643260834748957012917006"
          ],
          "EA": [
            "3.4112831758043639662594451021387912258109490129589573123118507773328039416352826",
            "3.4112831758043639662594451030448885617009429230554847892832020987249612990813441"
          ],
          "EB": [
            "2.8885408682510305772595010858417634044189281552724242605574179217141719947330298",
            "2.8885408682510305772595010879418822016167922747402373761151747990995274696434120"
          ],
          "wrong_conjugated": [
            "0.052198744183296062715062662562850007771496829949760082108358765213352995793429174",
            "0.052198744183296062718153852814356815704405500817357447409906445461972733622502831"
          ],
          "J_close": [
            "-0.15344037374988327533781501933261798546071300405260979605790503603754232376955626",
            "-0.15344037374988327533781501932975231067423709182621050480404218544380438928884229"
          ],
          "J_far": [
            "1.7432454157602990682086082726626355572291577142659775779815042246953407096377839",
            "1.7432454157602990682086082727346268994259916067828378200687384311601630190703400"
          ]
        },
        "cauchy": [
          "0.99919044359283463236786774414819036091257549141713222674502694603487076902569609",
          "0.99919044359283463236786774464412331413115602507451076715713842321305980081301938"
        ],
        "elapsed_seconds": 22.46255807299997
      }
    ],
    "elapsed_seconds": 30.99065851699993
  },
  "rational_witness": {
    "R": 16,
    "primes_left": [
      11,
      13
    ],
    "primes_right": [
      17,
      19,
      23,
      29,
      31
    ],
    "J": [
      "-0.135768199376325",
      "-0.135768199376324"
    ],
    "J_close": [
      "0.024008396864762",
      "0.024008396864763"
    ],
    "product_terms": {
      "187": [
        "0.104494105069357",
        "0.104494105069358"
      ],
      "209": [
        "0.096110138136552",
        "0.096110138136553"
      ],
      "221": [
        "0.077334047151572",
        "0.077334047151573"
      ],
      "247": [
        "0.019232236212333",
        "0.019232236212334"
      ],
      "253": [
        "0.004776160652428",
        "0.004776160652429"
      ],
      "299": [
        "-0.083637385753807",
        "-0.083637385753806"
      ],
      "319": [
        "-0.101492992243934",
        "-0.101492992243933"
      ],
      "341": [
        "-0.105932898836422",
        "-0.105932898836421"
      ],
      "377": [
        "-0.086530086739283",
        "-0.086530086739282"
      ],
      "403": [
        "-0.060121523025125",
        "-0.060121523025124"
      ]
    },
    "method": "exact Fraction atanh-log series and integrated sine series; no floating quadrature"
  },
  "pair_partition": {
    "rows": [
      {
        "R": 16,
        "D": 15,
        "collar_count": 2,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.02400839686476219731855596109494486667951392279682263972399269850",
          "0.02400839686476219731855596109494486667957373778001597934798548669"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.02400839686476219731855596109494486667951392279682263972399269850",
          "0.02400839686476219731855596109494486667957373778001597934798548669"
        ],
        "small_pairs": []
      },
      {
        "R": 17,
        "D": 14,
        "collar_count": 1,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.02426875931434053006025869124258985872666444332506194748141156370",
          "-0.02426875931434053006025869124258985871932806974407083334734690149"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.02426875931434053006025869124258985872666444332506194748141156370",
          "-0.02426875931434053006025869124258985871932806974407083334734690149"
        ],
        "small_pairs": []
      },
      {
        "R": 18,
        "D": 16,
        "collar_count": 2,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.008689287200022225951151173397654301682048824303873715154111657489",
          "0.008689287200022225951151173397654301682048824303890269236694439748"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.008689287200022225951151173397654301682048824303873715154111657489",
          "0.008689287200022225951151173397654301682048824303890269236694439748"
        ],
        "small_pairs": []
      },
      {
        "R": 19,
        "D": 18,
        "collar_count": 1,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.03375212875921721697853239675315591477766454056567588826492041830",
          "-0.03375212875921721697853239675315590946128325329768978669088834220"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.03375212875921721697853239675315591477766454056567588826492041830",
          "-0.03375212875921721697853239675315590946128325329768978669088834220"
        ],
        "small_pairs": []
      },
      {
        "R": 20,
        "D": 19,
        "collar_count": 3,
        "matched_pairs": 1,
        "offsets": [
          8
        ],
        "J_close": [
          "-0.00751350524430647970855808461355880677246345544985217106411459343",
          "-0.00751350524430647970855808461355880677246343681919841065202602133"
        ],
        "J_match": [
          "0.00031299588626595784860960844867501666368562380558206198642709012",
          "0.00031299588626595784860960844867501666368564243623558534861507777"
        ],
        "J_unmatched": [
          "-0.007826501130572437557167693062233823436149079255434233050541683542",
          "-0.007826501130572437557167693062233823436149079255433996000641099106"
        ],
        "small_pairs": [
          [
            [
              17,
              23
            ],
            [
              11,
              37
            ]
          ]
        ]
      },
      {
        "R": 21,
        "D": 22,
        "collar_count": 2,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.01467633714642586105072698771642861816694888200613112872313889920",
          "-0.01467633714642586105072698771642861816694585577853612806781217496"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.01467633714642586105072698771642861816694888200613112872313889920",
          "-0.01467633714642586105072698771642861816694585577853612806781217496"
        ],
        "small_pairs": []
      },
      {
        "R": 22,
        "D": 24,
        "collar_count": 3,
        "matched_pairs": 1,
        "offsets": [
          10
        ],
        "J_close": [
          "0.00397163450055783034300072204903795467495334624645064107654024592",
          "0.00397163450055783034300072204903795467495348332728933431185898996"
        ],
        "J_match": [
          "0.00036857008853551485253952056409222311326033920210823569754382354",
          "0.00036857008853551485253952056409222311326047628294692893286233284"
        ],
        "J_unmatched": [
          "0.003603064412022315490461201484945731561693007044342405378996422382",
          "0.003603064412022315490461201484945731561693007044342405378996657117"
        ],
        "small_pairs": [
          [
            [
              11,
              43
            ],
            [
              17,
              29
            ]
          ]
        ]
      },
      {
        "R": 23,
        "D": 26,
        "collar_count": 3,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.04500251806907597970864664620843005275321408033901445096522242028",
          "-0.04500251806907597970864664620843004470616377061821113425118278671"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.04500251806907597970864664620843005275321408033901445096522242028",
          "-0.04500251806907597970864664620843004470616377061821113425118278671"
        ],
        "small_pairs": []
      },
      {
        "R": 24,
        "D": 28,
        "collar_count": 3,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.04366931215425405378804569447441648123830791181429180023656715871",
          "0.04366931215425405378804569447441649491103590442786797829496670187"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.04366931215425405378804569447441648123830791181429180023656715871",
          "0.04366931215425405378804569447441649491103590442786797829496670187"
        ],
        "small_pairs": []
      },
      {
        "R": 25,
        "D": 31,
        "collar_count": 2,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.01282061082355047103486528499520662405636686645355467168031725571",
          "0.01282061082355047103486528499520662405636736338357434676204375635"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.01282061082355047103486528499520662405636686645355467168031725571",
          "0.01282061082355047103486528499520662405636736338357434676204375635"
        ],
        "small_pairs": []
      },
      {
        "R": 26,
        "D": 28,
        "collar_count": 3,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.06133858163198456446437060115247989890437271375660985271275083706",
          "-0.06133858163198456446437060115247988762515261129319090335357903462"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.06133858163198456446437060115247989890437271375660985271275083706",
          "-0.06133858163198456446437060115247988762515261129319090335357903462"
        ],
        "small_pairs": []
      },
      {
        "R": 27,
        "D": 30,
        "collar_count": 3,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.05429651934714319161097320691813476092281716945296963704109460746",
          "0.05429651934714319161097320691813476133529102940898798774877358731"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.05429651934714319161097320691813476092281716945296963704109460746",
          "0.05429651934714319161097320691813476133529102940898798774877358731"
        ],
        "small_pairs": []
      },
      {
        "R": 28,
        "D": 32,
        "collar_count": 2,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.01649495521038918355658394398151715925216592051266040342480421432",
          "-0.01649495521038918355658394398151715925216516643266898704832045183"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.01649495521038918355658394398151715925216592051266040342480421432",
          "-0.01649495521038918355658394398151715925216516643266898704832045183"
        ],
        "small_pairs": []
      },
      {
        "R": 29,
        "D": 35,
        "collar_count": 2,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.01649288210813809490551498487077383524238032115746176358101670451",
          "0.01649288210813809490551498487077383524558319433344522687060787733"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.01649288210813809490551498487077383524238032115746176358101670451",
          "0.01649288210813809490551498487077383524558319433344522687060787733"
        ],
        "small_pairs": []
      },
      {
        "R": 30,
        "D": 37,
        "collar_count": 3,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.005224750644043389943128246687587464809486734050979851965723476947",
          "0.005224750644043389943128246687587464809486734050979853740409837217"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.005224750644043389943128246687587464809486734050979851965723476947",
          "0.005224750644043389943128246687587464809486734050979853740409837217"
        ],
        "small_pairs": []
      },
      {
        "R": 31,
        "D": 40,
        "collar_count": 2,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.01402538583205551820728273686106780854325786122510889190410557364",
          "-0.01402538583205551820728273686106780850135805996782243043277810407"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.01402538583205551820728273686106780854325786122510889190410557364",
          "-0.01402538583205551820728273686106780850135805996782243043277810407"
        ],
        "small_pairs": []
      },
      {
        "R": 32,
        "D": 42,
        "collar_count": 4,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.06820875190967743519904855393568649342697818413413221994282060265",
          "0.06820875190967743519904855393568649492810271352312493077176577571"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.06820875190967743519904855393568649342697818413413221994282060265",
          "0.06820875190967743519904855393568649492810271352312493077176577571"
        ],
        "small_pairs": []
      },
      {
        "R": 33,
        "D": 45,
        "collar_count": 3,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.01175194663364966437528949020511395075816986055123893273550124914",
          "-0.01175194663364966437528949020511395065703011970358519797340364340"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.01175194663364966437528949020511395075816986055123893273550124914",
          "-0.01175194663364966437528949020511395065703011970358519797340364340"
        ],
        "small_pairs": []
      },
      {
        "R": 34,
        "D": 48,
        "collar_count": 5,
        "matched_pairs": 1,
        "offsets": [
          34
        ],
        "J_close": [
          "0.02376157555350847966335539768548593440316744936786485573741277798",
          "0.02376157555350847966335539768548593462026656938519839205204839596"
        ],
        "J_match": [
          "0.00109241944279993484844294102913435901651028587665547456385067449",
          "0.00109241944279993484844294102913435923360940510592591331882698175"
        ],
        "J_unmatched": [
          "0.02266915611070854481491245665635157538665716349120938117356210349",
          "0.02266915611070854481491245665635157538665716427927247873322141421"
        ],
        "small_pairs": [
          [
            [
              19,
              59
            ],
            [
              29,
              41
            ]
          ]
        ]
      },
      {
        "R": 35,
        "D": 51,
        "collar_count": 5,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.08168387248312781396252687305956948812978770884924392606007307776",
          "-0.08168387248312781396252687305956922505553674662967829347781884740"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.08168387248312781396252687305956948812978770884924392606007307776",
          "-0.08168387248312781396252687305956922505553674662967829347781884740"
        ],
        "small_pairs": []
      },
      {
        "R": 36,
        "D": 53,
        "collar_count": 4,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.06030214471136981785535644010557129307594946799184641641671886047",
          "0.06030214471136981785535644010557139827142215948435703869490426315"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.06030214471136981785535644010557129307594946799184641641671886047",
          "0.06030214471136981785535644010557139827142215948435703869490426315"
        ],
        "small_pairs": []
      },
      {
        "R": 37,
        "D": 48,
        "collar_count": 6,
        "matched_pairs": 2,
        "offsets": [
          19,
          35
        ],
        "J_close": [
          "0.01754237032104961415271032240136170889455235761521514584079128085",
          "0.01754237032104961415271032240136170891297761743664291212721434510"
        ],
        "J_match": [
          "0.00115767801910646838305917493377583439478144333277698977533186909",
          "0.00115767801910646838305917493377583441320670315420213806432026720"
        ],
        "J_unmatched": [
          "0.01638469230194314576965114746758587449977091428243815606545941176",
          "0.01638469230194314576965114746758587449977091428244077406289407790"
        ],
        "small_pairs": [
          [
            [
              19,
              71
            ],
            [
              19,
              73
            ]
          ],
          [
            [
              31,
              43
            ],
            [
              23,
              61
            ]
          ]
        ]
      },
      {
        "R": 38,
        "D": 51,
        "collar_count": 2,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.02592265346709794692599237673116661713922016312828004564018346458",
          "0.02592265346709794692599237673116661726756297464405212923727462008"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.02592265346709794692599237673116661713922016312828004564018346458",
          "0.02592265346709794692599237673116661726756297464405212923727462008"
        ],
        "small_pairs": []
      },
      {
        "R": 39,
        "D": 54,
        "collar_count": 3,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.03325526771379850224404829016964598845384670022852964234767196748",
          "-0.03325526771379850224404829016964598845384669731523837226652414528"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.03325526771379850224404829016964598845384670022852964234767196748",
          "-0.03325526771379850224404829016964598845384669731523837226652414528"
        ],
        "small_pairs": []
      },
      {
        "R": 40,
        "D": 57,
        "collar_count": 3,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.06357500536737802426151586537554268673090812801898321378000663987",
          "-0.06357500536737802426151586537554268662907571023250000764329295477"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.06357500536737802426151586537554268673090812801898321378000663987",
          "-0.06357500536737802426151586537554268662907571023250000764329295477"
        ],
        "small_pairs": []
      },
      {
        "R": 41,
        "D": 60,
        "collar_count": 5,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.00206047918758270139451734133731916950377955477095966009835110176",
          "-0.00206047918758270139451734133731911292305971954982478130220116382"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.00206047918758270139451734133731916950377955477095966009835110176",
          "-0.00206047918758270139451734133731911292305971954982478130220116382"
        ],
        "small_pairs": []
      },
      {
        "R": 42,
        "D": 62,
        "collar_count": 5,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.01553226818918205808087072434718030910883319893432676188375649864",
          "0.01553226818918205808087072434718031389791007633705131132105538888"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.01553226818918205808087072434718030910883319893432676188375649864",
          "0.01553226818918205808087072434718031389791007633705131132105538888"
        ],
        "small_pairs": []
      },
      {
        "R": 43,
        "D": 66,
        "collar_count": 4,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.04341619368565737897577216478729889893873525147188545933335841663",
          "-0.04341619368565737897577216478729887673948653530326988970186846048"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.04341619368565737897577216478729889893873525147188545933335841663",
          "-0.04341619368565737897577216478729887673948653530326988970186846048"
        ],
        "small_pairs": []
      },
      {
        "R": 44,
        "D": 69,
        "collar_count": 5,
        "matched_pairs": 2,
        "offsets": [
          8,
          26
        ],
        "J_close": [
          "0.03685130991529777877180350153496677391254988958488613385839917037",
          "0.03685130991529777877180350153496677391787177372599830786044238618"
        ],
        "J_match": [
          "0.000314118564365594935742527541046548024902749917364173969442255057",
          "0.000314118564365594935742527541046548024902765656771540074498451266"
        ],
        "J_unmatched": [
          "0.03653719135093218383606097399392022588764713966752195988895691532",
          "0.03653719135093218383606097399392022589296900806922676778594393490"
        ],
        "small_pairs": [
          [
            [
              41,
              47
            ],
            [
              29,
              67
            ]
          ],
          [
            [
              23,
              83
            ],
            [
              37,
              53
            ]
          ]
        ]
      },
      {
        "R": 45,
        "D": 72,
        "collar_count": 5,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.03475326484849622242883830634274231561202968207782801102106027999",
          "-0.03475326484849622242883830634274229536291942483996909462174961861"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.03475326484849622242883830634274231561202968207782801102106027999",
          "-0.03475326484849622242883830634274229536291942483996909462174961861"
        ],
        "small_pairs": []
      },
      {
        "R": 46,
        "D": 75,
        "collar_count": 6,
        "matched_pairs": 1,
        "offsets": [
          68
        ],
        "J_close": [
          "0.02958800459679907686698280738286819352363154600337953902655294291",
          "0.02958800459679907686698280738286828178901600957526628708344549132"
        ],
        "J_match": [
          "0.00162348748266580868681207533131938917859468839175374485886652895",
          "0.00162348748266580868681207533131947647064335452041768838679645718"
        ],
        "J_unmatched": [
          "0.02796451711413326818017073205154880434503685761162579416768641405",
          "0.02796451711413326818017073205154880531837265505484859869664903408"
        ],
        "small_pairs": [
          [
            [
              23,
              89
            ],
            [
              37,
              59
            ]
          ]
        ]
      },
      {
        "R": 47,
        "D": 78,
        "collar_count": 6,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.07876723886669303947314376423392797428035318243769473748918911479",
          "-0.07876723886669303947314376423392793877716330724820109277527006126"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.07876723886669303947314376423392797428035318243769473748918911479",
          "-0.07876723886669303947314376423392793877716330724820109277527006126"
        ],
        "small_pairs": []
      },
      {
        "R": 48,
        "D": 82,
        "collar_count": 4,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "0.09092143235388510724323527443006520701080475385604143320688332333",
          "0.09092143235388510724323527443006520701141854743173693126106655093"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "0.09092143235388510724323527443006520701080475385604143320688332333",
          "0.09092143235388510724323527443006520701141854743173693126106655093"
        ],
        "small_pairs": []
      },
      {
        "R": 64,
        "D": 127,
        "collar_count": 9,
        "matched_pairs": 0,
        "offsets": [],
        "J_close": [
          "-0.1462022617988289576779580756600768051437953064407478438473965956",
          "-0.1462022617988289576779580756600765724734381170770289981612767172"
        ],
        "J_match": [
          "0",
          "0"
        ],
        "J_unmatched": [
          "-0.1462022617988289576779580756600768051437953064407478438473965956",
          "-0.1462022617988289576779580756600765724734381170770289981612767172"
        ],
        "small_pairs": null
      },
      {
        "R": 127,
        "D": 336,
        "collar_count": 20,
        "matched_pairs": 1,
        "offsets": [
          19
        ],
        "J_close": [
          "0.07382919351966434217212139760895418414000552643176373070503086921",
          "0.07382919351966434217212139760895459426378299195474763667321323080"
        ],
        "J_match": [
          "0.000004507040358666632006799962582187975236327328474780701694426384",
          "0.000004507040358666632006799962582187975236327328474780701694434027"
        ],
        "J_unmatched": [
          "0.07382468647930567554011459764637199616476919910328895000333644291",
          "0.07382468647930567554011459764637240628854666462627285597151879680"
        ],
        "small_pairs": null
      },
      {
        "R": 257,
        "D": 971,
        "collar_count": 41,
        "matched_pairs": 2,
        "offsets": [
          155,
          709
        ],
        "J_close": [
          "-0.1534403737498832753378150193311853821815163262369159077477523328",
          "-0.1534403737498832753378150193311849200217359554315632738588405850"
        ],
        "J_match": [
          "0.00056684362266217867003253066548724647940258942366898564920734722",
          "0.00056684362266217867003253066548724669717427680166433781479777312"
        ],
        "J_unmatched": [
          "-0.1540072173725454540078475499966726286609189156605848933969596800",
          "-0.1540072173725454540078475499966721667189102322332276116736383584"
        ],
        "small_pairs": null
      },
      {
        "R": 549,
        "D": 3139,
        "collar_count": 99,
        "matched_pairs": 1,
        "offsets": [
          663
        ],
        "J_close": [
          "0.2295532899921116491856659948499472257310425931845552366002946010",
          "0.2295532899921116491856659948499514751516539443257518122173979656"
        ],
        "J_match": [
          "0.00003512329710245558854181455749907738354823348866932400427285385",
          "0.00003512329710245558854181455749907738354823348868686687853464835"
        ],
        "J_unmatched": [
          "0.2295181666950091935971241802924481483474943596958859125960217471",
          "0.2295181666950091935971241802924523977681057108370649453388633174"
        ],
        "small_pairs": null
      },
      {
        "R": 1024,
        "D": 8191,
        "collar_count": 231,
        "matched_pairs": 3,
        "offsets": [
          1982,
          2584,
          7042
        ],
        "J_close": [
          "-0.1227331223631714131280213777857688299662929254027317076133330968",
          "-0.1227331223631714131280213777857564186364656062515053214225855021"
        ],
        "J_match": [
          "0.00052568415998603587795548281650239454715590123513013810377480507",
          "0.00052568415998603587795548281650245049809213056271246941387639535"
        ],
        "J_unmatched": [
          "-0.1232588065231574490059768606022712245134488266378618457171079017",
          "-0.1232588065231574490059768606022588691345577368142177908364618978"
        ],
        "small_pairs": null
      },
      {
        "R": 4096,
        "D": 65535,
        "collar_count": 1267,
        "matched_pairs": 26,
        "offsets": [
          5014,
          8272,
          9788,
          10378,
          11164,
          11626,
          17678,
          22798,
          27992,
          27998,
          29866,
          34432,
          35848,
          36212,
          40442,
          43552,
          45088,
          45452,
          45532,
          45716,
          52288,
          53084,
          53876,
          58622,
          64228,
          64976
        ],
        "J_close": [
          "-0.7327297775608075796415130385760243781918186941431620255737355855",
          "-0.7327297775608075796415130385759622807124090367153929672137963452"
        ],
        "J_match": [
          "0.002738568378728397412760762142218477239675595729290014678137471327",
          "0.002738568378728397412760762142222124838502252201629484026519511358"
        ],
        "J_unmatched": [
          "-0.7354683459395359770542738007182428554314942898724520402518730541",
          "-0.7354683459395359770542738007181844055509112889170224512403158632"
        ],
        "small_pairs": null
      }
    ],
    "elapsed_seconds": 4.2113015610000275
  },
  "audit": {
    "independent_rows": [
      {
        "R": 16,
        "values": {
          "J": -0.1357681993763244,
          "PC": -0.24428648830387567,
          "CP": -0.10042666742357843,
          "CC": -0.1750196072226516,
          "M": 0.03392534912847813,
          "EA": 0.08396949809355465,
          "EB": 0.3130676056466568,
          "wrong_conjugated": 0.01745574067703749
        },
        "quad_error_diagnostic": 1.6610378200819336e-14
      },
      {
        "R": 64,
        "values": {
          "J": -0.4779205724124923,
          "PC": -0.5516215363408816,
          "CP": 0.2927449772224351,
          "CC": 0.01625501244038339,
          "M": -0.2027890008536621,
          "EA": 1.3113336620070102,
          "EB": 1.4194595513069073,
          "wrong_conjugated": 0.06903216213480066
        },
        "quad_error_diagnostic": 7.286816722240331e-14
      },
      {
        "R": 127,
        "values": {
          "J": 0.3761193976798232,
          "PC": 0.9154560021029052,
          "CP": 0.09058369921592083,
          "CC": -0.07599524724976446,
          "M": -0.7059155508887675,
          "EA": 7.905907693133542,
          "EB": 1.4435137105045606,
          "wrong_conjugated": -0.12032898545977566
        },
        "quad_error_diagnostic": 2.8200425403000015e-13
      },
      {
        "R": 257,
        "values": {
          "J": 1.5898050420104168,
          "PC": 0.5224491739688011,
          "CP": 0.488508470672779,
          "CC": -0.10702621162575335,
          "M": 0.4718211857430836,
          "EA": 3.4112831758044186,
          "EB": 2.888540868251022,
          "wrong_conjugated": 0.0521987441832496
        },
        "quad_error_diagnostic": 1.8625098094527045e-13
      },
      {
        "R": 549,
        "values": {
          "J": 0.40282203067923256,
          "PC": 0.7787803010807227,
          "CP": -1.1369075430443822,
          "CC": -0.49110325805773686,
          "M": 0.2698460145851552,
          "EA": 3.8276455004964856,
          "EB": 5.488294028304628,
          "wrong_conjugated": 0.4893270019594981
        },
        "quad_error_diagnostic": 3.480043989707852e-13
      },
      {
        "R": 1024,
        "values": {
          "J": -6.314323301617171,
          "PC": -1.5044476520169192,
          "CP": -0.999732014209384,
          "CC": -0.6310496449903137,
          "M": -4.4411932803811816,
          "EA": 9.636861415181805,
          "EB": 31.709709629521218,
          "wrong_conjugated": 0.715430785354158
        },
        "quad_error_diagnostic": 1.5606985095968917e-12
      },
      {
        "R": 4096,
        "values": {
          "J": -9.022460377467299,
          "PC": -1.3766694935086534,
          "CP": -6.942345439396498,
          "CC": 0.16229904198708878,
          "M": -0.5411464025750561,
          "EA": 45.40120266377345,
          "EB": 114.03124738819176,
          "wrong_conjugated": -1.7528319097375602
        },
        "quad_error_diagnostic": 7.737071662775884e-12
      }
    ],
    "max_distance_from_certificate": 2.1121715487737447e-12,
    "exact_cpp_roots": 39,
    "wheel16": {
      "R": 16,
      "X": 255,
      "primorial": 30030,
      "physical_divisors": 36,
      "virtual_divisors": 28,
      "F_physical": "183/1001",
      "F_virtual": "-272/1001",
      "F": "-89/1001",
      "delta": "192/1001",
      "floor_sum": 49,
      "survivors": 49,
      "piX": 54,
      "Z_diagnostic": 6.332664826664185,
      "Z_normalized_diagnostic": 0.14275162720375606
    },
    "endpoint_control": {
      "R": 18,
      "pair": [
        17,
        19
      ],
      "product": 323,
      "band_value": 0
    },
    "elapsed_seconds": 0.37536909799996465
  },
  "scout": {
    "elapsed_seconds": 0.23851944299997285,
    "roots": [
      {
        "R": 16,
        "pair_count": 10,
        "close_counts": [
          2,
          0,
          0
        ],
        "J": -0.1357681993763241,
        "J_close": 0.024008396864762225,
        "J_far": -0.15977659624108634,
        "abs_mass": 0.739661573820813
      },
      {
        "R": 17,
        "pair_count": 10,
        "close_counts": [
          0,
          0,
          1
        ],
        "J": 0.054440991167622785,
        "J_close": -0.02426875931434052,
        "J_far": 0.07870975048196331,
        "abs_mass": 0.8393235887683123
      },
      {
        "R": 18,
        "pair_count": 12,
        "close_counts": [
          1,
          1,
          0
        ],
        "J": -0.0944474665067113,
        "J_close": 0.008689287200022272,
        "J_far": -0.10313675370673357,
        "abs_mass": 0.7942052081732353
      },
      {
        "R": 19,
        "pair_count": 15,
        "close_counts": [
          0,
          0,
          1
        ],
        "J": -0.06547520817583737,
        "J_close": -0.03375212875921726,
        "J_far": -0.03172307941662014,
        "abs_mass": 1.0749415474919282
      },
      {
        "R": 20,
        "pair_count": 16,
        "close_counts": [
          1,
          0,
          2
        ],
        "J": -0.1953332825635943,
        "J_close": -0.007513505244306579,
        "J_far": -0.1878197773192877,
        "abs_mass": 1.1311349024895632
      },
      {
        "R": 21,
        "pair_count": 20,
        "close_counts": [
          1,
          0,
          1
        ],
        "J": -0.14354202877842828,
        "J_close": -0.01467633714642581,
        "J_far": -0.1288656916320025,
        "abs_mass": 1.5019867125416229
      },
      {
        "R": 22,
        "pair_count": 24,
        "close_counts": [
          2,
          0,
          1
        ],
        "J": -0.09470478612481047,
        "J_close": 0.003971634500557732,
        "J_far": -0.09867642062536806,
        "abs_mass": 1.7437041138319356
      },
      {
        "R": 23,
        "pair_count": 18,
        "close_counts": [
          1,
          0,
          2
        ],
        "J": -0.2024592503909915,
        "J_close": -0.04500251806907597,
        "J_far": -0.15745673232191554,
        "abs_mass": 1.4086235190454353
      },
      {
        "R": 24,
        "pair_count": 24,
        "close_counts": [
          2,
          0,
          1
        ],
        "J": -0.4399152402909309,
        "J_close": 0.04366931215425403,
        "J_far": -0.4835845524451847,
        "abs_mass": 1.900935894429363
      },
      {
        "R": 25,
        "pair_count": 24,
        "close_counts": [
          1,
          0,
          1
        ],
        "J": -0.2792633955060591,
        "J_close": 0.012820610823550379,
        "J_far": -0.29208400632960946,
        "abs_mass": 2.0278330496143764
      },
      {
        "R": 26,
        "pair_count": 24,
        "close_counts": [
          1,
          0,
          2
        ],
        "J": -0.08316845725275893,
        "J_close": -0.061338581631984565,
        "J_far": -0.021829875620774396,
        "abs_mass": 2.1670027150390583
      },
      {
        "R": 27,
        "pair_count": 21,
        "close_counts": [
          2,
          0,
          1
        ],
        "J": -0.2743053372538051,
        "J_close": 0.05429651934714326,
        "J_far": -0.3286018566009484,
        "abs_mass": 1.8121869715125438
      },
      {
        "R": 28,
        "pair_count": 21,
        "close_counts": [
          1,
          0,
          1
        ],
        "J": -0.042690750030306444,
        "J_close": -0.016494955210389073,
        "J_far": -0.026195794819917427,
        "abs_mass": 1.8183924271346659
      },
      {
        "R": 29,
        "pair_count": 21,
        "close_counts": [
          1,
          0,
          1
        ],
        "J": 0.18122921021132363,
        "J_close": 0.016492882108138103,
        "J_far": 0.16473632810318536,
        "abs_mass": 1.8743232050653247
      },
      {
        "R": 30,
        "pair_count": 28,
        "close_counts": [
          1,
          1,
          1
        ],
        "J": -0.0029123692141232727,
        "J_close": 0.005224750644043437,
        "J_far": -0.008137119858166647,
        "abs_mass": 2.4082872604743892
      },
      {
        "R": 31,
        "pair_count": 32,
        "close_counts": [
          1,
          0,
          1
        ],
        "J": -0.030891218245986937,
        "J_close": -0.014025385832055703,
        "J_far": -0.016865832413931234,
        "abs_mass": 2.9276161232710045
      },
      {
        "R": 32,
        "pair_count": 35,
        "close_counts": [
          3,
          0,
          1
        ],
        "J": -0.08378845606250977,
        "J_close": 0.06820875190967751,
        "J_far": -0.15199720797218724,
        "abs_mass": 3.1410584798407717
      },
      {
        "R": 33,
        "pair_count": 35,
        "close_counts": [
          2,
          0,
          1
        ],
        "J": -0.04913229460954359,
        "J_close": -0.0117519466336496,
        "J_far": -0.03738034797589394,
        "abs_mass": 3.1388644487452737
      },
      {
        "R": 34,
        "pair_count": 40,
        "close_counts": [
          3,
          0,
          2
        ],
        "J": -0.0105107384699904,
        "J_close": 0.023761575553508794,
        "J_far": -0.034272314023499284,
        "abs_mass": 3.4625445269894772
      },
      {
        "R": 35,
        "pair_count": 32,
        "close_counts": [
          2,
          0,
          3
        ],
        "J": -0.060024859938113836,
        "J_close": -0.08168387248312808,
        "J_far": 0.021659012545014247,
        "abs_mass": 2.723348483378494
      },
      {
        "R": 36,
        "pair_count": 36,
        "close_counts": [
          3,
          0,
          1
        ],
        "J": 0.058762919697395596,
        "J_close": 0.0603021447113696,
        "J_far": -0.0015392250139739522,
        "abs_mass": 3.155792085470854
      },
      {
        "R": 37,
        "pair_count": 40,
        "close_counts": [
          4,
          0,
          2
        ],
        "J": 0.15981397373762513,
        "J_close": 0.017542370321049446,
        "J_far": 0.14227160341657574,
        "abs_mass": 3.5462084828497207
      },
      {
        "R": 38,
        "pair_count": 45,
        "close_counts": [
          1,
          0,
          1
        ],
        "J": 0.08602454572136835,
        "J_close": 0.025922653467097892,
        "J_far": 0.060101892254270525,
        "abs_mass": 4.115320916823391
      },
      {
        "R": 39,
        "pair_count": 36,
        "close_counts": [
          1,
          0,
          2
        ],
        "J": -0.1574860165242788,
        "J_close": -0.03325526771379827,
        "J_far": -0.12423074881048056,
        "abs_mass": 3.31382964017278
      },
      {
        "R": 40,
        "pair_count": 40,
        "close_counts": [
          1,
          0,
          2
        ],
        "J": -0.10393757519034114,
        "J_close": -0.06357500536737795,
        "J_far": -0.0403625698229631,
        "abs_mass": 3.716474569583228
      },
      {
        "R": 41,
        "pair_count": 40,
        "close_counts": [
          3,
          0,
          2
        ],
        "J": -0.10459406259897541,
        "J_close": -0.0020604791875828074,
        "J_far": -0.10253358341139268,
        "abs_mass": 3.7416236926627375
      },
      {
        "R": 42,
        "pair_count": 50,
        "close_counts": [
          2,
          1,
          2
        ],
        "J": -0.12348240944895694,
        "J_close": 0.015532268189182137,
        "J_far": -0.13901467763813902,
        "abs_mass": 4.423542828242008
      },
      {
        "R": 43,
        "pair_count": 50,
        "close_counts": [
          2,
          0,
          2
        ],
        "J": -0.07973121412690395,
        "J_close": -0.04341619368565752,
        "J_far": -0.03631502044124642,
        "abs_mass": 4.634420425677619
      },
      {
        "R": 44,
        "pair_count": 54,
        "close_counts": [
          3,
          0,
          2
        ],
        "J": -0.12610673451695464,
        "J_close": 0.036851309915297586,
        "J_far": -0.16295804443225226,
        "abs_mass": 5.060495875104395
      },
      {
        "R": 45,
        "pair_count": 60,
        "close_counts": [
          2,
          0,
          3
        ],
        "J": -0.0895364977666234,
        "J_close": -0.03475326484849637,
        "J_far": -0.05478323291812712,
        "abs_mass": 5.659359846254915
      },
      {
        "R": 46,
        "pair_count": 60,
        "close_counts": [
          3,
          0,
          3
        ],
        "J": -0.06970452866142351,
        "J_close": 0.029588004596799118,
        "J_far": -0.09929253325822271,
        "abs_mass": 5.756370462863934
      },
      {
        "R": 47,
        "pair_count": 50,
        "close_counts": [
          3,
          0,
          3
        ],
        "J": -0.3095228797158941,
        "J_close": -0.07876723886669292,
        "J_far": -0.2307556408492013,
        "abs_mass": 4.946670305345294
      },
      {
        "R": 48,
        "pair_count": 54,
        "close_counts": [
          4,
          0,
          0
        ],
        "J": -0.4272120204666072,
        "J_close": 0.09092143235388533,
        "J_far": -0.5181334528204926,
        "abs_mass": 5.256185373977134
      },
      {
        "R": 64,
        "pair_count": 91,
        "close_counts": [
          3,
          0,
          6
        ],
        "J": -0.47792057241249136,
        "J_close": -0.14620226179882936,
        "J_far": -0.33171831061366214,
        "abs_mass": 8.973845574697277
      },
      {
        "R": 127,
        "pair_count": 288,
        "close_counts": [
          10,
          0,
          10
        ],
        "J": 0.3761193976798227,
        "J_close": 0.07382919351966402,
        "J_far": 0.3022902041601587,
        "abs_mass": 25.712949323834355
      },
      {
        "R": 257,
        "pair_count": 989,
        "close_counts": [
          20,
          0,
          21
        ],
        "J": 1.5898050420104273,
        "J_close": -0.15344037374988204,
        "J_far": 1.7432454157603103,
        "abs_mass": 77.00189470975313
      },
      {
        "R": 549,
        "pair_count": 3569,
        "close_counts": [
          50,
          0,
          49
        ],
        "J": 0.40282203067923505,
        "J_close": 0.22955328999211175,
        "J_far": 0.17326874068712575,
        "abs_mass": 225.09517665108115
      },
      {
        "R": 1024,
        "pair_count": 10275,
        "close_counts": [
          116,
          0,
          115
        ],
        "J": -6.31432330161722,
        "J_close": -0.12273312236317345,
        "J_far": -6.191590179254042,
        "abs_mass": 536.3145990711898
      },
      {
        "R": 4096,
        "pair_count": 118320,
        "close_counts": [
          629,
          0,
          638
        ],
        "J": -9.022460377467628,
        "J_close": -0.7327297775608385,
        "J_far": -8.289730599906752,
        "abs_mass": 3894.7834008786845
      }
    ],
    "sign_failures": [
      16,
      17,
      18,
      22,
      24,
      25,
      27,
      30,
      32,
      34,
      42,
      44,
      46,
      48,
      257
    ],
    "dominance_failures": [
      16,
      17,
      18,
      20,
      21,
      22,
      23,
      24,
      25,
      27,
      28,
      29,
      30,
      31,
      32,
      33,
      34,
      37,
      38,
      39,
      41,
      42,
      44,
      45,
      46,
      47,
      48,
      64,
      127,
      257,
      1024,
      4096
    ]
  }
}
```


### Verified Publication Receipt - 20261109-census-2

Substantive findings were published at **2026-11-09 16:27:51 UTC (11:27:51 EST)** in commit **dd0624f85eaf5941ab756df14667abce8f70a8ef**, report blob **1c81fba8b27f02fc306c636b83935453d45b3bc7**. Immutable full-content readback matched the intended report byte-for-byte. Commit metadata verifies exactly one changed path: research/agent_reports/2026-11-09/40-prime-census.md.

The initial registration commit 075800ea1d8657f7e60b8dbf6922bd7decb5749a was created at 16:08:40 UTC; the disclosed pair-extension commit 732779322bfe307546eb58f79c244f3330dd7017 at 16:16:56 UTC. Both were read back before their respective arithmetic tests, and both commit records also show only the owned report changed.

All computation sessions completed. The six embedded source blocks match the actual executed program files, the 50 continuation fence markers are balanced, and all required A-N sections are present. An initial shell-quoted report-lint command failed before execution; the subsequent direct content validation passed. This was a presentation check, not a failed mathematical run.

EXECUTION=COMPLETE. PUBLICATION=VERIFIED for the substantive commit above. NEW_LEAN_PROOF=NONE. NEW_GLOBAL_ENDPOINT_GAIN=NONE. BL3 remains PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING. BL1-BL2/BL4-BL5 retain their stated finite scopes. This receipt preserves the prior report and will itself be verified after its append.


## Scheduled Nearest-Centre Registration - 20261109-census-3/NC

Actual trigger: 2026-11-09 19:00:01 EST, America/New_York; platform RUN_ID_UNAVAILABLE. This is one scheduled continuation of the existing report. Execution=IN_PROGRESS; mathematics=PENDING finite checks; final synthesis=PENDING.
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.

Authority at intake: main e7ffe4e01fd049dfe6f47af86a9984bc0b843576; AGENTS 6695522a45d67fd1e80a7cff1f98d909405036e2; contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038; directive e505f35522b675c6b5b263eac73618d717346973; complete-wheel source ecb482e52deeee5e9b3853592a3ffdace662d2ff. Original source definitions were read. Both November 9 and November 8 reports of all seven roles and EXTERNAL_HANDOFFS were retrieved at agent-reports 2790c7061df77c4ba3c27fd290cc539128611273. TODAY=PRESENT for all roles; yesterday retains its original status. No scheduled launch is inferred from filenames.

Selected new question, responding to Wheel RF's explicit approximate-reflection handoff: can once-only reflection about the nearest centre permitted by a shared LOWER prime produce a larger affordable matched subset, and does its sign remain positive? This is NOT another unchanged BL/CR sign scan. No claim that this subset closes the full source is being tested.

For integer R>=16 put X=R^2-1, h=ceil(sqrt R), D=floor(X/(4h)). The genuine rectangle is primes R<=2p, p<R, R<=q<2R; its collar has |pq-X|<=D, including equality. For each p set k_p=floor(X/p+1/2), c_p=p*k_p, e_p=c_p-X. Pair distinct primes q_-<q_+ once when q_-+q_+=2k_p and BOTH products lie in the original collar. A fixed point q=k_p remains an unpaired atom. No absent prime is supplied, no occurrence is reused, and the above-wall member is not misidentified as a physical below-X site.

The signed kernel is the existing BL/MB kernel K_R(n)=(1/pi) integral_[sqrt R,2sqrt R] b(t/R) sin(t log(X/n))/t dt with the original spline, without conjugation. Let J_NC be the sum of all selected pair contributions. Existing exact reflected pairs may overlap this matching; their credits MUST NOT be added twice.

Competing hypotheses: H_POS asserts each selected pair has nonnegative signed contribution; the rival is that the arithmetic rounding defect e_p can overpower curvature. An advance analytical prediction, not an observation, is that the sign is determined by X^2-(p*q_-)*(p*q_+)=v^2-2X*e_p-e_p^2, v=p*(q_+-q_-)/2. We will test this exact integer discriminator, including whether e_p>0 can still yield a positive pair. A proof-led proposed uniform bound is |J_NC|<=8R/85, with constants fixed now; it requires a full analytic proof and is not inferred from samples.

Frozen domains: discovery EVERY integer R=16..128; held-out roots EXACTLY 193,383,769,1531,3079. Independent trial-factor enumeration must match the primary sieve's complete pair lists, collar counts, fixed points, overlap with BL, and sign classifications. Verify the original compensated physical floor total versus direct prime/survivor enumeration at these roots; enumerate the full exponential divisor cube only for R=2,3,14,16 and the smallest new sign witness if feasible. At larger roots retain the symbolic virtual correction X*(delta-sum_physical mu(d)/d) and compute the exact compensated integer total.

Record first negative and first positive witnesses, largest exact matching coverage/defect and any e_p>0 positive witness. This is a finite specified search, not a fitted global density law. Use rational log/sine series to enclose decisive pair values independently of a floating scout; use 50/80-digit li only for explicitly NUMERICAL ONLY normalized full-source diagnostics. No floating sign becomes a finite certificate without an error bound. The original complete return, BOTH physical mixed terms and complementary owners remain explicit and unbounded; only the matched-subset replacement is proposed. No global inequality or first-bad hypothesis is being refuted.

New work and reproducible programs will be appended after execution. Only this report may be changed remotely. No Lean, main, other report, branch, PR, issue, workflow, schedule or permission edits; no agent launches or local Lean.


## Nearest-Centre Prime Pairing: Exact Sign And Uniform Cost - 20261109-census-3/NC

### A. Most Important Mathematical Discovery

**Moving a reflection to the nearest centre allowed by a shared prime does not preserve positivity. It does preserve an affordable total cost.** For the exact same-lower-prime matching defined below, every individual pair has the sign of the INTEGER
`G=X^2-n_-n_+=v^2-2Xe-e^2`. The smallest negative example in the stated domain is R=31. At R=114, two pairs have the SAME centre and SAME positive rounding offset e=3 but opposite signs: their different spans cross the exact quadratic threshold.

There is also a uniform paper bound for the ENTIRE selected population, not merely for one pair:

```text
forall integer R>=16:
  sum_(selected pairs) |K_R(n_-)+K_R(n_+)| <= 8R/85.
```

Thus no favorable-sign hypothesis is needed to control this subset. The bound remains valid for any measurable real band weight of absolute value at most one. It does NOT supply partners for the unmatched products, control the far products, or bound the complete centered wheel.

| Claim | Result | Evidence |
| --- | --- | --- |
| 20261109-census-3/NC1 | Exact one-use nearest-centre matching and geometric-mean sign law | PAPER_PROOF; SELF_AUDIT, independent review pending |
| NC2 | Uniform sum of absolute pair totals <=8R/85; overlap-safe combination with BL costs <=76R/765 | PAPER_PROOF; proper subset only |
| NC3 | H_POS refuted at the smallest admissible failing root R=31; offset-only classification also fails | REFUTED, exact finite arithmetic and rational band certificates |
| NC4 | Positive pairs above the wall centre require 0<e<R/32; same-centre opposite-sign witness at R=114 | PAPER_PROOF for the restriction; FINITE_COMPUTATION for the witnesses |
| NC5 | Two independent reconstructions agree at all 118 registered roots; complete physical/virtual source checks | FINITE_COMPUTATION |

No literature-priority claim is made for the sine addition formula, Taylor bounds, or integer reflection. The new laboratory result is this precisely admitted, once-only source reduction and its exact sign discriminator. **NEW_VERIFIED_GLOBAL_ENDPOINT_GAIN=NONE; NEW_LEAN_PROOF=NONE.** The complete finite-wheel bound, canonical VF estimate, finite A/C and RH remain OPEN.

### B. Authority And Current Objective

Actual trigger: **2026-11-09 19:00:01 EST**, America/New_York, UTC-05:00. Run label 20261109-census-3; platform RUN_ID_UNAVAILABLE. This is a scheduled continuation of the preserved daily report, not a new agent launch. `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`.

Main was fetched at intake and again before synthesis: **e7ffe4e01fd049dfe6f47af86a9984bc0b843576**, unchanged. Reporting intake: **2790c7061df77c4ba3c27fd290cc539128611273**. Retrieval began shortly after 2026-11-10 00:00 UTC, which is November 9 in the reporting timezone.

For every integer R>=2 retain the original definitions

```text
X=R^2-1, y=R-1, P_y=product_(prime p<=y)p,
delta(y)=product_(prime p<=y)(1-1/p),
F_R=sum_(d|P_y)mu(d)fract(X/d),
D_R=X delta(y)+pi(y)-1-li(X),
Z_R=F_R-D_R=li(X)-pi(X).
OPEN: exists ONE C>=0, forall R>=2, |Z_R|<=C R log R.
```

Here li is principal-value li. Li_2 differs by a fixed constant. Every virtual divisor d>X remains until it cancels against its own Euler term; d=X is included. The public canonical target remains `VFCanonicalSquareVonKochStatement`. The directly inspected terminal `riemannHypothesis_of_vfCanonicalSquare` still requires its explicit `ClassicalVonKochRHCriterion`.

| Inspected current source | Blob SHA |
| --- | --- |
| AGENTS.md | 6695522a45d67fd1e80a7cff1f98d909405036e2 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| Complete-wheel seven-role directive | e505f35522b675c6b5b263eac73618d717346973 |
| Dynamic research protocol | e8d913ff9663bb5163eaf0eddca9f76e0508a7ef |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| research/CompleteWheelRootAdmission.lean | a412632c1028d7728cd8d87ee6e5ac365377d338 |
| research/DyadicPrimeNearResonance.lean | 0080496ada9c7ce230690ed773ee52df9575c245 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

[Immutable complete-wheel source](https://github.com/OVVO-Financial/RH_Lean/blob/e7ffe4e01fd049dfe6f47af86a9984bc0b843576/research/CompleteSquareRootWheelFractionalBoundary.lean). Definitions `finiteWheelFract`, `finiteWheelSquareDeterministic`, `vfMidPrefixWheelCounting`, `vfMidPrefixWheelDensity`, `finiteWheelCenteredAt`, `dyadicPrimePair` and `admittedDyadicPrimePair` were read, not reconstructed from theorem names alone.

### C. Competing Hypotheses And Prior Credit

The registration was published BEFORE arithmetic execution at **3f37ca15ffbbe233abcf5b0fc5f935709009fd40**, report blob **59d7729b12f12af15679baaba0f2442a432bb07a**, then re-fetched at that immutable commit. All bytes matched, with the previous report preserved as an unchanged prefix.

H_POS asserted that EVERY nearest-centre selected pair has nonnegative original band contribution. The competing explanation was that centre rounding can outweigh the positive curvature seen in exact reflection. The geometric-mean discriminator and constant 8/85 were derived as analytical candidates before execution and stated in the registration; this was not a blind discovery of their formulas. Discovery roots were EVERY integer 16..128; held-out roots were EXACTLY 193,383,769,1531,3079. No cutoff or constant was fitted afterward.

The existing BL3 exact-reflection O(R) bound is credited, including Referee DA's scoped independent acceptance. Wheel RF1-RF3 classifies the narrow exactly reflected shared-factor population and explicitly requests a NEW approximate map, not a larger repetition of that scan. NC changes the reflection centre and therefore selects a different population. The old CR and full BL sign scans were not repeated. Computing BL overlap here is necessary to prevent duplicate credit.

The e<R/32 inverse restriction and the same-centre interpretation at R=114 are disclosed post-result deductions, not retroactively preregistered thresholds. They follow from the displayed algebra, not a fitted regression.

### D. Exact Carrier And Matching

For integer R>=16, set U=sqrt(R), h=ceil(sqrt(R)), D=floor(X/(4h)). The actual prime rectangle is

```text
E_R={(p,q): p,q prime, R<=2p, p<R, R<=q<2R}.
Collar={(p,q) in E_R: |pq-X|<=D}.
k_p=floor(X/p+1/2), c_p=p*k_p, e_p=c_p-X.
```

Every lower p is odd. There is no half-integer rounding tie because p cannot divide 2X without dividing X. Thus `2|e_p|<p<R`. Pair distinct actual primes q_-<q_+ when

```text
q_-+q_+=2k_p,
(p,q_-),(p,q_+) BOTH belong to the original collar.
n_-=p*q_-, n_+=p*q_+, v=p*(q_+-q_-)/2.
```

No absent prime is manufactured. The involution has at most one partner per occurrence; a prime fixed point q=k_p is kept unpaired. Since distinct odd primes differ by at least two, v>=p>|e_p|, so n_-<X<n_+. Unique factorization and p<R<=q make the product map injective across rows. Each selected occurrence is used once.

The upper product is a genuine spectral rectangle term but is NOT a sharp physical site below X. Likewise q>=R is not a divisor coordinate of P_(R-1). A spectral pairing is not automatically an owner-payment map.

Keep the actual BL/MB kernel

```text
K_R(n)=(1/pi_circle) integral_U^(2U)
       b(t/R)*sin(t log(X/n))/t dt,
b(w)=1-6w^2+6w^3 on 0<=w<=1/2.
```

For this domain t/R<=1/2, including equality at R=16. There is no conjugation. The full piecewise spline outside this domain is not replaced by this polynomial. The integer-root upper endpoint 2R is composite, so the earlier closed prime interval and the present strict q<2R contain the same primes.

### E. Paper Proofs

**NC1, exact sign.** Write a=log(X/n_-), b=log(X/n_+). Both absolute phases satisfy, for U<=t<=2U,

```text
|t*a|, |t*b| <= 2sqrt(R)/(4h-1) <= 8/15 < pi_circle/2.
sin(t*a)+sin(t*b)
  =2 sin(t*(a+b)/2) cos(t*(a-b)/2).
```

The cosine is strictly positive and the sine has the sign of a+b. The spline is strictly positive on this interval. Therefore

```text
sign(K_R(n_-)+K_R(n_+))
 =sign(log(X^2/(n_-n_+)))
 =sign(G),  G=v^2-2Xe_p-e_p^2.
```

G cannot vanish for these distinct prime pairs: n_-n_+=p^2 q_-q_+ is not a square, whereas X^2 is a square. This is a sign theorem for the pair, not for a full row, band, centered band, or global covariance.

**NC2, total cost with no sign assumption.** The proof works with b replaced by ANY measurable real eta_R(t), |eta_R|<=1. Put

```text
f(s)=(1/pi_circle) integral_U^(2U) eta_R(t) sin(ts)/t dt.
```

Then f is odd and has Lipschitz constant at most U/pi_circle. For a selected n_-=X-w, 0<w<=D, let n_*=X+w be its exact geometric reflection in product position. This comparison point need not be a prime product and is used only inside an analytic inequality, never added to the arithmetic carrier. Since n_+-n_*=2e_p,

```text
|K(n_-)+K(n_+)|
 <= (U/pi_circle) *
    [ 2|e_p|/(X-D) + w^2/(X^2-w^2) ]
 <= (h/pi_circle) *
    [ R/(X-D) + D^2/(X^2-D^2) ].
```

The first term uses the logarithm's derivative on [X-D,X+D]. The second uses
`-log(1-w^2/X^2)<=w^2/(X^2-w^2)`, with the two original signs combined BEFORE absolute values.

There are at most D selected pairs because their distinct lower products lie in the D integers X-D,...,X-1. Also h>=4, D<=X/(4h), h^2>=R and X<R^2. Consequently

```text
sum_pairs |pair contribution|
 <= h*D*R/[pi_circle*(X-D)]
      +h*D^3/[pi_circle*(X^2-D^2)]
 <= 4R/(15*pi_circle)+4R/(255*pi_circle)
  =24R/(85*pi_circle) < 8R/85.
```

All constants are fixed before R. This is an aggregate estimate with all multiplicities accounted for. No PNT, prime gap distribution, independence, RH-strength premise or all-interval equidistribution is used.

**Overlap-safe combination.** Select NC pairs first. Keep only old BL exact-reflection pairs whose TWO endpoints avoid every NC endpoint. Call this disjoint submatching BL_free. Its contribution is nonnegative and at most 4R/765 by BL3. Hence

```text
|J_NC+J_BL_free| <= 8R/85+4R/765 = 76R/765.
```

A common edge and an edge sharing just one endpoint both require exclusion. Adding J_NC to the entire old J_match is invalid. The chosen priority rule is not asserted to maximize coverage or increase it at every possible root.

**NC4, inverse restriction.** If e<=0 then G>0, because v>|e|. If e>0 and G>0, both collar endpoints give v+e<=D, while G>0 gives v^2>2Xe+e^2. Thus

```text
0<e< D^2/[2(X+D)] < X/(32h^2) < R/32.
```

In particular e>=R/32 forces a negative pair. A small positive e is only necessary for positivity, not sufficient. These proofs are PAPER_PROOF / SELF_AUDIT, not independently accepted or Lean-certified.

### F. Executed Results And Exceptions

Both programs agree on every pair list, collar count, fixed-point list, exact BL edge list, and every compensated integer total at all **118 roots**. The domain contains 2,557 collar occurrences and 277 NC pairs: 145 positive and 132 negative by exact G. NC is nonempty at 73 roots; 49 roots have a negative pair. There are five e>0, G>0 pairs in the frozen domain.

The first selected pair is positive at R=24. The smallest H_POS violation is

```text
R=31, X=960, h=6, D=40,
p=23, q_-=41, q_+=43,
k=42, c=966, e=6, v=23,
n_-=943, n_+=989,
G=960^2-943*989=-11027.
```

These are the ONLY two collar products at R=31, so the entire collar is selected. Independent rational series give the closed enclosure

```text
K_31(943)+K_31(989) in
[-0.014025385832055518207283,
 -0.014025385832055518207282].
```

All smaller roots 16..30 were checked independently. This refutes H_POS at its smallest admissible failing root, NOT RH, OPEN-MIDBAND, a full first-bad theorem, or an existential constant in the complete target.

At **R=114**, X=12995 and D=295, the pair (67;191,197) and the pair (97;131,137) have the SAME centre c=12998=2*67*97 and SAME e=3:

| Pair | v | G | Certified pair contribution |
| --- | ---: | ---: | --- |
| (67;191,197) | 201 | -37578 | [-0.000656211617438955193138, -0.000656211617438955193137] |
| (97;131,137) | 291 | 6702 | [0.000112975601926191614543, 0.000112975601926191614544] |

The exact threshold is 2Xe+e^2=77979, between 201^2=40401 and 291^2=84681. This is the smallest root in the frozen discovery range having e>0 but G>0. It explains why conditioning on rounding direction ALONE is insufficient.

| Held-out R | Collar | NC pairs | Negative pairs | BL_free pairs | Remaining collar atoms | Certified J_NC, rounded display |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 193 | 30 | 3 | 1 | 0 | 24 | -0.001733198515 |
| 383 | 70 | 6 | 2 | 2 | 54 | 0.011369288934 |
| 769 | 148 | 20 | 12 | 1 | 106 | -0.010180570815 |
| 1531 | 371 | 42 | 22 | 8 | 271 | -0.007277180243 |
| 3079 | 878 | 90 | 38 | 11 | 676 | 0.017552869525 |

Each last-column display has absolute error <1e-12; full rational outward decimal enclosures are included below. They certify matched sums only, not J_mid or M_mid. In total, 167 selected pair contributions at the nine declared certificate roots were individually enclosed.

Across the whole frozen domain, BL has 64 pairs: two are common NC edges, 19 other BL edges touch NC endpoints, and 43 remain disjoint. The resulting partition uses 640 of 2,557 collar occurrences once and leaves 1,917 occurrences. No asymptotic coverage claim follows.

The first partial-overlap example is R=65. NC pairs products 4189=59*71 and 4307=59*73. BL pairs 4141=41*101 with 4307. Adding both credits would count the physical PRODUCT OCCURRENCE 4307 twice. At R=37, the common NC/BL edge is exactly Wheel RF's inherited 1349,1387 example; it is counted once, not rediscovered as new arithmetic.

Largest exact G values in this finite search occur at R=3079: G=23029239683 for (2683;3527,3539), e=-1201, v=16098; and G=-25076973511 for (2963;3191,3209), e=1360, v=26667. These rank the algebraic discriminator, not the size of the full band. The maximum NC coverage is 100% at R=31. None supplies a universal coverage or amplitude constant.

### G. Independent Methods And Numerical Control

Primary exact reconstruction: Python 3.12.14, Eratosthenes prime flags, integer partner lookup and Fraction arithmetic. Secondary reconstruction: g++ 13.3.0, C++17, `-O2 -Wall -Wextra -Werror`; trial division independently tests the prime pair factors and enumerates BOTH upper factors, rather than looking up a reflected partner. Its separate linear sieve builds actual Mobius values and greatest-prime factors for the physical floor source.

The largest finite endpoint is X=9,480,240. Python sieves each original low-prime survivor population directly; C++ independently sums

```text
sum_(1<=d<=X, mu(d)!=0, greatestPrime(d)<R) mu(d)*floor(X/d).
```

The values agree at every registered root. The unit d=1 is included. Squareful physical integers remain in the survivor population; only squareful DIVISORS have zero Mobius coefficient. Prime classification throughout the stated finite domain is deterministic, not probable-prime testing.

The numerical sign certificates do NOT depend on mpmath, floating quadrature, or a library logarithm. They use Fraction arithmetic, the atanh power series for log(X/n) with explicit geometric remainder, rational brackets for sqrt(R), and Machin's alternating arctangent formula for pi. The exact cubic spline times 15 sine monomials is integrated symbolically. With V>=2sqrt(R)|log(X/n)|<1, the integrated remainder is at most

```text
V^31/(3*31!),
```

because 0<=b<=1, integral_U^(2U)dt/t=log(2)<1, and pi>3. Every operation is rounded OUTWARD on an exact rational 10^-200 grid. Thus finite denominator control does not lose enclosure. Log series use 36 terms and square-root brackets use 60 decimal digits. R=31 and the R=114 positive-e witness were refined to 20 sine terms, 48 log terms and 72 square-root digits; refined intervals lie inside the primary intervals.

Two implementation issues were exposed and resolved, not hidden. The initial optional mpmath import failed; package retrieval was blocked by HTTP 403. No mathematical result was obtained from that path. The final programs use only the standard library. An unrounded Fraction aggregate was stopped because unrelated denominators made exact addition unnecessarily expensive. A first outward 10^-80 grid was valid but its absolute rounding errors grew under high-power refinement, so the required interval-nesting check failed (the intervals overlapped). The final 10^-200 grid passes the stronger nesting test. No sign, root, coefficient, constant or hypothesis was changed to obtain agreement.

Observed Python main elapsed time: 0.2813678219999929 seconds; final certificate elapsed time: 4.8044845439999335 seconds, as measured inside the executed programs. These are measurements from this environment, not performance guarantees. C++ execution completed successfully; no independently instrumented CPU/memory benchmark is asserted.

### H. Complete Original Source And Signed Return

The new mechanism is a proper spectral subset, not the complete first-owner ledger. To guard the source distinction, the original compensated integer total was reconstructed independently at all 118 roots. The full divisor cube was evaluated with exact rationals ONLY at R=2,3,14,16,31. At larger roots the virtual correction remains explicitly

```text
F_virtual=X*(delta(y)-sum_(physical d|P_y,d<=X)mu(d)/d),
F_physical=X*sum_(physical d)mu(d)/d - floor_source,
F_R-X*delta(y)=-floor_source.
```

No exponential cube was enumerated at the larger roots, and no virtual term was simply discarded.

At the decisive R=31, all 1,024 divisors split into 131 physical and 893 virtual entries:

```text
delta(30)=442368/2800733,
F_physical=-492645169/215656441,
F_virtual=197052256/215656441,
F_R=-3838869/2800733,
F_R-960*delta(30)=-153,
pi(960)=162=10-1+153.
```

R=2 has the empty prime wheel and the unit divisor. R=14 retains d=X=195. These and the prior R=16 ledger were narrow boundary regressions for the changed matching experiment, not new claims of the certified identities.

| R | pi(X) | pi(R-1) | Exact floor source | Normalized absolute Z_R, NUMERICAL ONLY |
| ---: | ---: | ---: | ---: | ---: |
| 31 | 162 | 10 | 153 | 0.092077712425 |
| 193 | 3945 | 43 | 3903 | 0.027015118431 |
| 383 | 13566 | 75 | 13492 | 0.021466425190 |
| 769 | 48446 | 135 | 48312 | 0.015083593161 |
| 1531 | 172482 | 241 | 172242 | 0.013177097448 |
| 3079 | 632357 | 439 | 631919 | 0.010568826460 |

The li diagnostics use Decimal at 50 and 80 digits, Euler--Maclaurin gamma and the convergent Ei(log X) series. Their maximum observed absolute change in Z is below 3e-45. This is a stability check, NOT a certified li enclosure or a uniform theorem.

Preserve the upstream FW/SC/MB paper adapter and its actual review status. With A=P_--C_-, B=P_+-C_+ and the nonconjugated bilinear band functional T,

```text
J_mid=T(P_-,P_+),
delta_ref=-T(P_-,C_+)-T(C_-,P_+)+T(C_-,C_+),
Z_R=S_rest+J_mid+delta_ref+e_smooth,
S_rest=C_rest+I_Lnu+I_nuL+A(0)B(0)/2
              +I_[0,U]+I_[2U,R].
```

Here the physical hyperbolic mixed terms I_Lnu and I_nuL are NOT the band reference terms T(P_-,C_+) and T(C_-,P_+). They remain separate. Define J_rem_close from every collar occurrence not selected by NC or BL_free, including zero-wall/fixed atoms, and J_far from the entire remaining prime rectangle. The exact new bookkeeping is

```text
Z_R = S_rest + J_NC + J_BL_free + J_rem_close
              + J_far + delta_ref + e_smooth.
```

All seven terms remain. Squaring requires seven diagonals and ALL 21 doubled cross terms. The new program did NOT compute S_rest, these physical mixed terms, full J_mid, or their global quadratic interactions, and no such computation or global comparison is claimed. The independent exact full-wheel total is not falsely presented as a numerical reconstruction of that spectral decomposition. NC2 bounds only the two indicated disjoint matched pieces.

### I. Interpretation And Proof Impact

The relevant hidden variables are the exact centre residue e_p and the product span v. Prime ancestry determines the available lattice centre; logarithmic phase then compares the GEOMETRIC mean with X, not the arithmetic mean. A sign change is therefore explained by an exact quadratic inequality, not by presumed random signs.

This produces a larger type of uniformly affordable matched subset than exact product reflection, without proving its coverage. The estimate is elementary enough to hold for broader admissible integer-product populations; it is NOT claimed to rule out Referee DA or Coordinator SA's synthetic models. Genuine source admission and the unpaid complements are still essential.

The proper band can now be written as an explicitly O(R) selected part plus J_rem_close+J_far. A uniform O(R log R) estimate for that remaining sum would be equivalent, up to this paid part, to the OLD proper-band question on R>=16. It is NOT a new independently established supplier and does not by itself close the full RETURN. Analytic ZD's claimed 17/12+epsilon proper-band estimate remains unreviewed paper work; it is not used in NC's proof. No change to the strongest certified global Mertens baseline is claimed.

### J. Falsification And Uncertainty Audit

H_POS is REFUTED. The stronger informal inference that upward centre rounding always makes a pair negative is also REFUTED by the R=114 witness. The corrected sign law and inverse restriction have full paper arguments and independent finite checks, but still need external mathematical review.

The fixed 8/85 bound survives the exact finite tests and has a displayed all-scale argument. It is not an empirical maximum, not asserted sharp, and not a bound on the full discrepancy. The overlap-safe 76/765 cost does not pay the unmatched population. No genuine-prime theorem is refuted with synthetic data, and no first-bad premise has been assumed or claimed satisfied.

The numerical certificates are software-assisted exact rational enclosures, not Lean kernel certificates or independent Referee acceptance. The normalized li values are approximate diagnostics only. No unexecuted program is reported as run. All computation sessions needed for this report completed or were explicitly terminated before replacement.

### K. Continuity And Formal Evidence

All seven roles on BOTH November 9 and November 8 were retrieved at the intake report snapshot. TODAY=PRESENT throughout; YESTERDAY=CARRY_FORWARD means retaining each claim's original scope/status, not endorsing every paper claim. Coordinator 00/90 mirrors had identical blobs on each date and were counted once.

| Role | November 9 blob | November 8 blob |
| --- | --- | --- |
| Coordinator | 35edd925446bfaf4babab99017ad8019db322915 | 8b640304f6c233a2c4409b9882799de485888a9e |
| Owner | 643e8a004d9d8e0be102b03e2f79bb3b217ae916 | 4e1b83a1e5ff8c134e9ca64404397c70c2b07252 |
| Analytic | d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3 | edecba8785a45cda87c0035d0348695941f1b8ea |
| Wheel | 0624246d03b19cf76c01e186b7d868a248d896ef | 60d4cf1b65d4b1b2cc4f13f6c0940c14cb2c50fd |
| Census | 6ad4c84512730dfc1cb7fc79540c248931cb8ddf | 00f4f9c0d670821a0c9d1da31fd1c4d0afd09142 |
| Referee | 01869acbc9d0535fe4791354a0029b8f77981723 | 5371324ebbdbd88afb9abf843e83da2ce86b752f |
| Lean | 4402811bbc7198731f83036f73836ef336c2015a | 5a110685bbe375d8ebff42df7391162914e52cef |

Relevant current handoffs consumed: Coordinator FB/MP/SA; Owner FW/CT/CF; Analytic SC/MB/ZD; Wheel RA/DG/RF; own CR/BL; Referee DA and its BL3 acceptance; Lean RA and near-resonance implementation/CI limitation. Yesterday's FM, JS, EC, FD, AF and SG concern other carriers or accepted baseline work; none was rerun or transferred by analogy.

EXTERNAL_HANDOFFS blob **038018145c0fddb2f6306c0712373adf9cd1ea52** has no entry later than October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 were consumed as signed-source, prime-root endpoint and unconditional/first-bad safeguards. Their old campaign priorities do not override the current finite-wheel directive.

No open/draft PR was returned at intake. Recent accepted changes were checked directly: #1119-#1124 are merged, and #1125 merged at 2026-11-09T23:01:09Z into the pinned main.

Formal evidence was checked rather than inferred from the merge title. The actual [#1122 targeted job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42561949462/job/128980092032) checks out synthetic merge **1e3c182076a6e1a23ef132c41a78b0f26adab507**, compiles CompleteSquareRootWheelFractionalBoundary, and prints only propext, Classical.choice and Quot.sound for the centered identity and physical compensation. Its source was fetched at that compiled commit and exactly matches current main's blob **ecb482e52deeee5e9b3853592a3ffdace662d2ff**. This is reused source-specific formal evidence, not a new build of all current main.

For #1125, the literal proof head is **538aa743a3e0de86b5ec44c9b4f159df3f5bd050**. Its dedicated [run 42674337064](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42674337064) is completed/failure and returns ZERO jobs. The merge changes repository state, not that missing targeted verification. The initial conversational description of the merge as a certification was corrected during this run. No near-resonance PROVED_IN_LEAN promotion is made here, and no local Lean was executed.

### L. Specialist Handoffs

**Proof Architect:** record NC2 as an independently derived proper O(R) cost and NC3 as a scoped falsifier, not an endpoint gain. Its exact consumer is the displayed seven-part RETURN; all complementary obligations stay open. RF's approximate-map suggestion has now been tested without changing the research campaign.

**Owner Payment:** nearest-centre pairs preserve one lower prime, but their upper member is above X. No physical donor or Euler reference is created by this. A worthwhile NEXT question is the exact missing-partner map: for an unpaired above-wall pq, put q'=2k_p-q; when q' is an admitted odd composite and p*q'<=X, trace its actual lower owner, duplicate donor multiplicity, and original signed reference. This is a proposed new experiment, NOT a source-payment theorem supplied here.

**Analytic Type II:** NC2 works for arbitrary bounded real band weights; the positive/negative sign law uses the actual nonnegative spline and the small phase range. Use the full nonconjugated source, both physical mixed terms and J_far. No new pointwise independence or a replacement for ZD's analytic input is claimed.

**Finite Wheel:** independent enumeration confirms RF's R=37 exception and shows why that exact-reflection scarcity does not persist unchanged after centre rounding. Check NC's unique row centre, fixed points, exact sign, and overlap rule. Enlarging the same count table is not the next task; a genuine composite-partner owner bridge would be different.

**Adversarial Referee:** audit NC1's phase range, NC2's termwise signed combination and count<=D, constants 8/85 and 76/765, and NC4's strict inverse inequality. Check R=31, the equal-centre R=114 pair, and the R=65 double-credit trap. All new proof claims are SELF_AUDIT pending your independent review.

**Lean Verification:** no immediate proof-source edit is requested. First restore the exact required #1125 verification evidence under existing permissions. NC's finite certificates and compact arithmetic sign discriminator are available for later accepted-scope work; do not formalize an assumed remainder bound and call that global progress.

These are asynchronous report handoffs only. No agent was launched or rescheduled.

### M. Ranked Experimental Portfolio

| Rank | Exact proposal | Evidence and counterevidence | Disposition / next requirement |
| --- | --- | --- | --- |
| 1 | Missing reflected prime partners with composite q' can be traced to specified original lower-owner sites with controlled multiplicity and exact coefficients | Concrete map proposed in L; NO computation or signed payment proved for it here | INVESTIGATE only after fixing its physical admission and Euler allocation; first falsifier is duplicated donor or coefficient mismatch |
| 2 | Selected nearest-centre pair absolute totals <=8R/85 for every R>=16 | Displayed paper proof; 118-root exact census and rational certificates | SEND FOR REVIEW; do not optimize the constant or expand unchanged counts without a new consumer |
| 3 | sign(pair)=sign(v^2-2Xe-e^2), positive above-centre pairs imply e<R/32 | Exact paper discriminator; R=114 shows e alone is insufficient | RETAIN as a structural classification, not a full cancellation principle |
| 4 | Every nearest-centre pair is nonnegative | Smallest counterexample R=31 | REJECT; do not impose positivity as an entrance condition |
| 5 | J_rem_close+J_far is uniformly O(R log R) | Still the prior proper-band conjecture after an O(R) reduction | OPEN; needs a new arithmetic estimate, and full RETURN remains separate |

### N. Resume Capsule And Reproduction

```text
RUN=20261109-census-3; scheduled 19:00:01 EST; platform RUN_ID_UNAVAILABLE.
MAIN=e7ffe4e01fd049dfe6f47af86a9984bc0b843576, unchanged before synthesis.
ACK=FINITE_WHEEL_CENTERED_RH_V1.
REGISTRATION=3f37ca15ffbbe233abcf5b0fc5f935709009fd40, readback verified.
NEW=NC1 exact sign, NC2 uniform 8R/85 subset bound,
    NC3 minimal R=31 falsifier, NC4 inverse restriction/R=114 same-centre split.
RANGE=all R16..128 plus held-outs 193,383,769,1531,3079.
CHECKS=118 independent pair/floor-source comparisons; 167 pair enclosures;
       five full rational wheel cubes; exact overlap/fixed-point accounting.
KEEP=all virtual compensation, original spline and phase, both physical mixed
     orientations, far/unmatched terms, and all global cross terms.
NEXT=specify and test composite reflected-partner -> physical lower-owner map
     with original coefficients, reference allocation and donor multiplicity.
DO_NOT_REPEAT=CR/BL sign scans, unchanged NC coverage tables, paid RF exact
              classification, or constant optimization with no new consumer.
GLOBAL_GAIN=NONE; NEW_LEAN=NONE; RH and full uniform bound remain OPEN.
```

Execution commands, from the directory containing the three embedded programs:

```bash
python -m py_compile nc_probe.py nc_certificates.py
g++ -O2 -std=c++17 -Wall -Wextra -Werror nc_reference.cpp -o nc_reference
./nc_reference > nc-reference.json
python nc_probe.py
python nc_certificates.py
```

The programs generate complete root/pair lists, exact rational source ledgers and certificate outputs. No randomness or seed is used. Reproduction requires only Python's standard library and a C++17 compiler. Source and artifact hashes:

```text
6d92698c02e6232eac6d848ff3db40200787e550f689e8b1afaf545ca9ca1224  nc_probe.py
0a200858bab6992330973e61d13b7ac954cda805400721369c5686c38439e157  nc_reference.cpp
085d74119afdba6e710a30d9ffdf8028391adbe6a4e53f9ce6cb475f7c761877  nc_certificates.py
547bb657dc3c87b6e52500a3df162a0e57ebbdab03e3b6e1a4d17feb825ec167  nc-results.json
904a70a8ed434d78e5705947c6ac5ca07b0ed0aeaf4e61fa122baac5e00f78a0  nc-reference.json
48fd8035797fbd71fac2e572a19728abae7a59ff0210b9ad5bf394f663a825ad  nc-certificates.json
4937180c5edeb68148f936ecb4910a26fe5b66a290160c8483834f4b88591bdc  nc-registration.md
```

Runtime-dependent timing fields cause regenerated JSON hashes to differ even when mathematical output is identical. Compare those fields separately. Publication is PENDING until the immutable commit/readback receipt appended below. Only the owned daily report is changed remotely.

### Exact Executed Programs - NC

#### nc_probe.py

```python
"""Frozen NC discovery: exact arithmetic first; transcendental output diagnostic."""

import bisect
import hashlib
import json
import math
import platform
import time
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path

ROOTS = list(range(16, 129)) + [193, 383, 769, 1531, 3079]
HERE = Path(__file__).resolve().parent


def sieve(limit):
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(limit) + 1):
        if flags[p]:
            flags[p * p :: p] = b"\x00" * ((limit - p * p) // p + 1)
    return flags


def census(r, primes, flags):
    x = r * r - 1
    h = math.isqrt(r - 1) + 1
    d = x // (4 * h)
    lo = [p for p in primes if r <= 2 * p and p < r]
    hi = [q for q in primes if r <= q < 2 * r]
    collar = {p * q: (p, q) for p in lo for q in hi if abs(p * q - x) <= d}
    assert len(collar) == sum(abs(p * q - x) <= d for p in lo for q in hi)
    pairs, fixed, used = [], [], set()
    for p in lo:
        k = (2 * x + p) // (2 * p)
        e = p * k - x
        assert 2 * abs(e) < p
        if r <= k < 2 * r and flags[k] and abs(p * k - x) <= d:
            fixed.append([p, k])
        for q in hi:
            qq = 2 * k - q
            if q < qq < 2 * r and qq >= r and flags[qq]:
                n, nn = p * q, p * qq
                if n not in collar or nn not in collar:
                    continue
                assert n < x < nn
                assert n not in used and nn not in used
                used.update([n, nn])
                v = p * (qq - q) // 2
                g = x * x - n * nn
                assert g == v * v - 2 * x * e - e * e
                assert g != 0
                if e <= 0:
                    assert g > 0
                if e > 0 and g > 0:
                    assert 32 * e < r
                    assert 2 * (x + d) * e < d * d
                pairs.append([p, q, qq, e, v, g])
    bl = [(n, 2 * x - n) for n in sorted(collar) if n < x and 2 * x - n in collar]
    nc_edges = {(p * q, p * qq) for p, q, qq, *_ in pairs}
    common = [edge for edge in bl if edge in nc_edges]
    free = [edge for edge in bl if edge[0] not in used and edge[1] not in used]
    conflict = [edge for edge in bl if edge not in common and edge not in free]
    for n, nn in free:
        used.update([n, nn])
    residual = sorted(set(collar) - used)
    assert 2 * len(pairs) + 2 * len(free) + len(residual) == len(collar)
    assert len(pairs) <= d
    bound = Fraction(len(pairs) * h, 3) * (
        Fraction(r, x - d) + Fraction(d * d, x * x - d * d)
    )
    assert bound <= Fraction(8 * r, 85)
    return {
        "R": r, "X": x, "h": h, "D": d,
        "rectangle": len(lo) * len(hi), "collar": len(collar),
        "pairs": pairs, "fixed": fixed, "BL_pairs": bl,
        "BL_common": common, "BL_conflict": conflict, "BL_free": free,
        "residual": residual, "negative": sum(z[-1] < 0 for z in pairs),
        "positive_e_positive": [z for z in pairs if z[3] > 0 and z[-1] > 0],
        "rational_abs_budget": str(bound),
    }


def complete_wheel(r, primes, prime_flags):
    x = r * r - 1
    low = primes[:bisect.bisect_left(primes, r)]
    survivors = bytearray(b"\x01") * (x + 1)
    survivors[0] = 0
    delta = Fraction(1)
    for p in low:
        survivors[p::p] = b"\x00" * (x // p)
        delta *= Fraction(p - 1, p)
    count = sum(survivors)
    pi_x = sum(prime_flags[:x + 1])
    assert count == 1 + pi_x - len(low)
    f = x * delta - count
    assert f - x * delta == -count
    result = {"R": r, "survivors": count, "pi_X": pi_x, "pi_root": len(low),
              "delta": str(delta), "F": str(f), "compensated": -count,
              "virtual": "X*(delta - sum_{d|P,d<=X} mu(d)/d)"}
    return result


def cube(r, primes):
    x = r * r - 1
    terms = [(1, 1)]
    delta = Fraction(1)
    for p in primes:
        if p >= r:
            break
        terms += [(p * n, -s) for n, s in terms]
        delta *= Fraction(p - 1, p)
    physical = sum((s * Fraction(x % n, n) for n, s in terms if n <= x), Fraction())
    virtual = sum((s * Fraction(x, n) for n, s in terms if n > x), Fraction())
    floor = sum(s * (x // n) for n, s in terms)
    reciprocal = sum((Fraction(s, n) for n, s in terms if n <= x), Fraction())
    assert physical + virtual - x * delta == -floor
    assert virtual == x * (delta - reciprocal)
    assert sum((Fraction(s, n) for n, s in terms), Fraction()) == delta
    return {"R": r, "divisors": len(terms), "physical_count": sum(n <= x for n, _ in terms),
            "physical": str(physical), "virtual": str(virtual), "delta": str(delta),
            "F": str(physical + virtual), "floor": floor}


def bernoulli(n):
    b = [Fraction(1)]
    for m in range(1, n + 1):
        b.append(-sum(Fraction(math.comb(m + 1, k)) * b[k] for k in range(m)) / (m + 1))
    return b


def li_diagnostic(x, precision):
    # Euler--Maclaurin gamma and the convergent Ei series; not an interval certificate.
    with localcontext() as ctx:
        ctx.prec = precision + 15
        n = 1000
        b = bernoulli(60)
        gamma = sum((Decimal(1) / k for k in range(1, n + 1)), Decimal(0))
        gamma -= Decimal(n).ln() + Decimal(1) / (2 * n)
        for k in range(1, 31):
            c = b[2 * k]
            gamma += Decimal(c.numerator) / (c.denominator * (2 * k) * n ** (2 * k))
        z = Decimal(x).ln()
        total, power = Decimal(0), Decimal(1)
        for k in range(1, 5000):
            power *= z / k
            term = power / k
            total += term
            if k > 2 * z and abs(term) < Decimal(10) ** (-precision - 10):
                break
        else:
            raise AssertionError("Ei series did not converge")
        ctx.prec = precision
        return +(gamma + z.ln() + total)


def main():
    start = time.perf_counter()
    flags = sieve(max(ROOTS) ** 2 - 1)
    small = [n for n in range(2, 2 * max(ROOTS)) if flags[n]]
    rows = [census(r, small, flags) for r in ROOTS]
    first_negative = next((dict(R=a["R"], pair=z) for a in rows for z in a["pairs"] if z[-1] < 0), None)
    first_positive = next((dict(R=a["R"], pair=z) for a in rows for z in a["pairs"] if z[-1] > 0), None)
    first_crossover = next((dict(R=a["R"], pair=z) for a in rows for z in a["positive_e_positive"]), None)
    wheels = [complete_wheel(r, small, flags) for r in ROOTS]
    cubes = [cube(r, small) for r in sorted({2, 3, 14, 16, first_negative["R"]})]
    selected = sorted({16, first_negative["R"], first_positive["R"], 37, *ROOTS[-5:],
                       *([first_crossover["R"]] if first_crossover else [])})
    diagnostics = []
    for r in selected:
        row = next(a for a in rows if a["R"] == r)
        w = next(a for a in wheels if a["R"] == r)
        data = {}
        for precision in (50, 80):
            with localcontext() as ctx:
                ctx.prec = precision
                z = li_diagnostic(r * r - 1, precision) - w["pi_X"]
                data[str(precision)] = {"Z": str(z), "normalized_Z": str(abs(z) / (r * Decimal(r).ln()))}
        diagnostics.append({"R": r, "NUMERICAL_ONLY": data})
    report = {"root_domain": ROOTS, "rows": rows, "wheels": wheels, "cubes": cubes,
              "first_negative": first_negative, "first_positive": first_positive,
              "first_positive_e_positive": first_crossover, "diagnostics": diagnostics,
              "total_pairs": sum(len(a["pairs"]) for a in rows),
              "total_negative_pairs": sum(a["negative"] for a in rows),
              "python": platform.python_version(), "transcendental_method": "stdlib Decimal; NUMERICAL ONLY",
              "elapsed_seconds": time.perf_counter() - start,
              "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE / "nc-results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("rows", "wheels", "diagnostics", "root_domain")}, indent=2))
    print("SELECTED COUNTS", json.dumps([{k: row[k] for k in ("R", "collar", "negative")} |
          {"NC_pairs": len(row["pairs"]), "BL_pairs": len(row["BL_pairs"]),
           "BL_free": len(row["BL_free"]), "residual": len(row["residual"])}
           for row in rows if row["R"] in selected]))


if __name__ == "__main__":
    main()
```

#### nc_reference.cpp

```cpp
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <vector>

bool prime(int n) {
  if (n < 2) return false;
  for (int d = 2; d <= n / d; ++d) if (n % d == 0) return false;
  return true;
}

int main() {
  std::vector<int> roots;
  for (int r = 16; r <= 128; ++r) roots.push_back(r);
  for (int r : {193, 383, 769, 1531, 3079}) roots.push_back(r);
  const int limit = roots.back() * roots.back() - 1;
  std::vector<int> spf(limit + 1), largest(limit + 1), primes;
  std::vector<int8_t> mu(limit + 1);
  mu[1] = 1;
  for (int n = 2; n <= limit; ++n) {
    if (!spf[n]) { spf[n] = n; mu[n] = -1; largest[n] = n; primes.push_back(n); }
    for (int p : primes) {
      if (p > spf[n] || p > limit / n) break;
      const int m = p * n;
      spf[m] = p;
      largest[m] = std::max(p, largest[n]);
      mu[m] = (n % p == 0) ? 0 : -mu[n];
    }
  }
  std::cout << "[";
  bool first_root = true;
  for (int r : roots) {
    const int x = r * r - 1;
    int h = 1; while (h * h < r) ++h;
    const int d = x / (4 * h);
    int collar = 0, fixed = 0;
    std::vector<std::vector<long long>> pairs;
    std::vector<std::vector<int>> fixed_points;
    std::vector<int> products;
    for (int p = (r + 1) / 2; p < r; ++p) if (prime(p)) {
      int k = x / p;
      if (2 * (x % p) > p) ++k;
      for (int q = r; q < 2 * r; ++q) if (prime(q)) {
        if (std::abs(p * q - x) > d) continue;
        ++collar;
        products.push_back(p * q);
        if (q == k) { ++fixed; fixed_points.push_back({p, q}); }
        // Enumerate both genuine factors, independently of the partner lookup.
        for (int qq = q + 1; qq < 2 * r; ++qq) if (prime(qq)) {
          if (q + qq != 2 * k || std::abs(p * qq - x) > d) continue;
          const long long n = p * q, nn = p * qq;
          pairs.push_back({p, q, qq, p * k - x, p * (qq - q) / 2, 1LL * x * x - n * nn});
        }
      }
    }
    long long floor_sum = 0;
    for (int n = 1; n <= x; ++n) if (mu[n] && largest[n] < r)
      floor_sum += static_cast<long long>(mu[n]) * (x / n);
    if (!first_root) std::cout << ",";
    first_root = false;
    std::cout << "{\"R\":" << r << ",\"collar\":" << collar
              << ",\"fixed_count\":" << fixed << ",\"floor_sum\":" << floor_sum << ",\"pairs\":[";
    bool first_pair = true;
    for (const auto& z : pairs) {
      if (!first_pair) std::cout << ",";
      first_pair = false;
      std::cout << "[";
      for (size_t i = 0; i < z.size(); ++i) { if (i) std::cout << ","; std::cout << z[i]; }
      std::cout << "]";
    }
    std::cout << "],\"fixed\":[";
    for (size_t i = 0; i < fixed_points.size(); ++i) {
      if (i) std::cout << ",";
      std::cout << "[" << fixed_points[i][0] << "," << fixed_points[i][1] << "]";
    }
    std::cout << "],\"BL_pairs\":[";
    std::sort(products.begin(), products.end());
    bool first_bl = true;
    for (int n : products) for (int nn : products) if (n < x && n + nn == 2 * x) {
      if (!first_bl) std::cout << ",";
      first_bl = false;
      std::cout << "[" << n << "," << nn << "]";
    }
    std::cout << "]}";
  }
  std::cout << "]\n";
}
```

#### nc_certificates.py

```python
"""Independent exact rational log/sine certificates for the frozen NC pairs."""

import hashlib
import json
import math
import time
from fractions import Fraction as F
from pathlib import Path


HERE = Path(__file__).resolve().parent
GRID = 10 ** 200


def outward(a):
    lo = a[0].numerator * GRID // a[0].denominator
    hi = -((-a[1].numerator * GRID) // a[1].denominator)
    return F(lo, GRID), F(hi, GRID)


def point(x):
    return (F(x), F(x))


def add(a, b):
    return outward((a[0] + b[0], a[1] + b[1]))


def neg(a):
    return (-a[1], -a[0])


def mul(a, b):
    v = [x * y for x in a for y in b]
    return outward((min(v), max(v)))


def div(a, b):
    assert b[0] > 0
    return mul(a, (1 / b[1], 1 / b[0]))


def power(a, k):
    if k == 0:
        return point(1)
    vals = [a[0] ** k, a[1] ** k]
    if k % 2 == 0 and a[0] <= 0 <= a[1]:
        vals.append(F(0))
    return outward((min(vals), max(vals)))


def log_ratio(a, b, terms=36):
    w = F(a - b, a + b)
    total = 2 * sum((w ** (2 * j + 1) / (2 * j + 1) for j in range(terms)), F())
    error = 2 * abs(w) ** (2 * terms + 1) / ((2 * terms + 1) * (1 - w * w))
    return outward((total - error, total + error))


def arctan(inv, terms):
    w = F(1, inv)
    total = sum(((-1) ** j * w ** (2 * j + 1) / (2 * j + 1) for j in range(terms)), F())
    following = total + (-1) ** terms * w ** (2 * terms + 1) / (2 * terms + 1)
    return min(total, following), max(total, following)


PI = add(mul(point(16), arctan(5, 60)), neg(mul(point(4), arctan(239, 18))))
assert 3 < PI[0] < PI[1] < F(22, 7)


def sqrt_interval(n, digits=60):
    scale = 10 ** digits
    lo = math.isqrt(n * scale * scale)
    return F(lo, scale), F(lo + 1, scale)


def kernel(r, n, terms=15, log_terms=36, sqrt_digits=60):
    ell = log_ratio(r * r - 1, n, log_terms)
    u = sqrt_interval(r, sqrt_digits)
    total = point(0)
    for j in range(terms):
        power_ = 2 * j + 1
        # Integrate the exact cubic spline times each sine monomial in t.
        a = mul(point(F(2 ** power_ - 1, power_)), power(u, power_))
        b = mul(point(F(-6 * (2 ** (power_ + 2) - 1), r * r * (power_ + 2))), power(u, power_ + 2))
        c = mul(point(F(6 * (2 ** (power_ + 3) - 1), r ** 3 * (power_ + 3))), power(u, power_ + 3))
        integrated = add(add(a, b), c)
        coeff = mul(point(F((-1) ** j, math.factorial(power_))), power(ell, power_))
        total = add(total, mul(coeff, integrated))
    v = 2 * u[1] * max(abs(x) for x in ell)
    assert v < 1
    # 0<=b<=1, integral_U^(2U) dt/t=log(2)<1, and pi>3.
    error = v ** (2 * terms + 1) / (3 * math.factorial(2 * terms + 1))
    total = div(total, PI)
    return total[0] - error, total[1] + error


def display(interval, digits=24):
    scale = 10 ** digits
    def dec(n):
        sign = "-" if n < 0 else ""
        n = abs(n)
        return f"{sign}{n // scale}.{n % scale:0{digits}d}"
    lo = interval[0].numerator * scale // interval[0].denominator
    hi = -((-interval[1].numerator * scale) // interval[1].denominator)
    return [dec(lo), dec(hi)]


def main():
    start = time.perf_counter()
    primary = json.loads((HERE / "nc-results.json").read_text())
    reference = json.loads((HERE / "nc-reference.json").read_text())
    wheels = {a["R"]: a for a in primary["wheels"]}
    for a, b in zip(primary["rows"], reference, strict=True):
        assert a["R"] == b["R"]
        assert a["pairs"] == b["pairs"]
        assert a["collar"] == b["collar"]
        assert len(a["fixed"]) == b["fixed_count"]
        assert a["fixed"] == b["fixed"]
        assert a["BL_pairs"] == b["BL_pairs"]
        used = {p * q for p, q, qq, *_ in b["pairs"]} | {p * qq for p, q, qq, *_ in b["pairs"]}
        assert a["BL_free"] == [edge for edge in b["BL_pairs"] if not used.intersection(edge)]
        assert wheels[a["R"]]["survivors"] == b["floor_sum"]
    selected = {24, 31, 37, 114, 193, 383, 769, 1531, 3079}
    totals, certificates = [], []
    for row in primary["rows"]:
        r = row["R"]
        if r not in selected:
            continue
        total = point(0)
        for p, q, qq, e, v, g in row["pairs"]:
            val = add(kernel(r, p * q), kernel(r, p * qq))
            assert val[0] > 0 if g > 0 else val[1] < 0
            total = add(total, val)
            if r in (24, 31, 37, 114):
                certificates.append({"R": r, "p": p, "q_minus": q, "q_plus": qq,
                                     "e": e, "v": v, "G": g, "interval": display(val)})
            if (r, p, q, qq) in ((31, 23, 41, 43), (114, 97, 131, 137)):
                refined = add(kernel(r, p * q, terms=20, log_terms=48, sqrt_digits=72),
                              kernel(r, p * qq, terms=20, log_terms=48, sqrt_digits=72))
                assert val[0] <= refined[0] <= refined[1] <= val[1]
        assert -F(8 * r, 85) <= total[0] <= total[1] <= F(8 * r, 85)
        totals.append({"R": r, "pairs": len(row["pairs"]), "interval": display(total),
                       "abs_budget": row["rational_abs_budget"]})
    output = {"independent_root_checks": len(reference), "certified_pairs": certificates,
              "certified_sums": totals, "terms": 15, "log_terms": 36,
              "sqrt_decimal_digits": 60, "pi_interval": display(PI, 60),
              "outward_rational_grid_digits": 200,
              "refinement_witnesses": [[31, 23, 41, 43], [114, 97, 131, 137]],
              "elapsed_seconds": time.perf_counter() - start,
              "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (HERE / "nc-certificates.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
```

### Certified Numerical Output - NC

```json
{
  "independent_root_checks": 118,
  "certified_pairs": [
    {
      "R": 24,
      "p": 19,
      "q_minus": 29,
      "q_plus": 31,
      "e": -5,
      "v": 19,
      "G": 6086,
      "interval": [
        "0.017096109094279513403053",
        "0.017096109094279513403054"
      ]
    },
    {
      "R": 31,
      "p": 23,
      "q_minus": 41,
      "q_plus": 43,
      "e": 6,
      "v": 23,
      "G": -11027,
      "interval": [
        "-0.014025385832055518207283",
        "-0.014025385832055518207282"
      ]
    },
    {
      "R": 37,
      "p": 19,
      "q_minus": 71,
      "q_plus": 73,
      "e": 0,
      "v": 19,
      "G": 361,
      "interval": [
        "0.000267398147149267111990",
        "0.000267398147149267111991"
      ]
    },
    {
      "R": 114,
      "p": 67,
      "q_minus": 191,
      "q_plus": 197,
      "e": 3,
      "v": 201,
      "G": -37578,
      "interval": [
        "-0.000656211617438955193138",
        "-0.000656211617438955193137"
      ]
    },
    {
      "R": 114,
      "p": 97,
      "q_minus": 131,
      "q_plus": 137,
      "e": 3,
      "v": 291,
      "G": 6702,
      "interval": [
        "0.000112975601926191614543",
        "0.000112975601926191614544"
      ]
    },
    {
      "R": 114,
      "p": 101,
      "q_minus": 127,
      "q_plus": 131,
      "e": 34,
      "v": 202,
      "G": -844012,
      "interval": [
        "-0.014697220568103436351941",
        "-0.014697220568103436351940"
      ]
    }
  ],
  "certified_sums": [
    {
      "R": 24,
      "pairs": 1,
      "interval": [
        "0.017096109094279513403053",
        "0.017096109094279513403054"
      ],
      "abs_budget": "76280/989523"
    },
    {
      "R": 31,
      "pairs": 1,
      "interval": [
        "-0.014025385832055518207283",
        "-0.014025385832055518207282"
      ],
      "abs_budget": "163/2300"
    },
    {
      "R": 37,
      "pairs": 1,
      "interval": [
        "0.000267398147149267111990",
        "0.000267398147149267111991"
      ],
      "abs_budget": "15953/233640"
    },
    {
      "R": 114,
      "pairs": 3,
      "interval": [
        "-0.015240456583616199930535",
        "-0.015240456583616199930534"
      ],
      "abs_budget": "3524587/33756600"
    },
    {
      "R": 193,
      "pairs": 3,
      "interval": [
        "-0.001733198514963826198512",
        "-0.001733198514963826198511"
      ],
      "abs_budget": "108632076/1386971279"
    },
    {
      "R": 383,
      "pairs": 6,
      "interval": [
        "0.011369288934015394583883",
        "0.011369288934015394583884"
      ],
      "abs_budget": "160649152/1434267297"
    },
    {
      "R": 769,
      "pairs": 20,
      "interval": [
        "-0.010180570814754110566969",
        "-0.010180570814754110566968"
      ],
      "abs_budget": "645239/2483514"
    },
    {
      "R": 1531,
      "pairs": 42,
      "interval": [
        "-0.007277180243160179562746",
        "-0.007277180243160179562745"
      ],
      "abs_budget": "714116401600/1831311296133"
    },
    {
      "R": 3079,
      "pairs": 90,
      "interval": [
        "0.017552869525285799699860",
        "0.017552869525285799699861"
      ],
      "abs_budget": "38095249080/65505218153"
    }
  ],
  "terms": 15,
  "log_terms": 36,
  "sqrt_decimal_digits": 60,
  "pi_interval": [
    "3.141592653589793238462643383279502884197169399375105820974944",
    "3.141592653589793238462643383279502884197169399375105820974945"
  ],
  "outward_rational_grid_digits": 200,
  "refinement_witnesses": [
    [
      31,
      23,
      41,
      43
    ],
    [
      114,
      97,
      131,
      137
    ]
  ],
  "elapsed_seconds": 4.8044845439999335,
  "source_sha256": "085d74119afdba6e710a30d9ffdf8028391adbe6a4e53f9ce6cb475f7c761877"
}
```
