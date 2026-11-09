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
