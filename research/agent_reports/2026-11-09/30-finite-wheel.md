# RH | Finite Wheel & Incidence - 2026-11-09

## Early Root-Adjunction Checkpoint - 20261109-wheel-1

### A. Most Important Structural Question

IN_PROGRESS / PARTIAL. No new mathematical result is claimed at this checkpoint. Investigate whether the COMPLETE Euler-compensated effect of adjoining the root prime has a uniformly bounded physical support, and whether the resulting cumulative innovation is affordable independently of the unresolved shell discrepancy. Do not assume adding primes improves cancellation.

### B. Current Authoritative Objective

Actual scheduled trigger: 2026-11-09 02:05:03 EST, America/New_York; platform RUN_ID_UNAVAILABLE.
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.
Main: 8110624150e444964f998676bf54e2e9a3b7e91c.
AGENTS blob: 6695522a45d67fd1e80a7cff1f98d909405036e2.
Contract blob: 95566e37c8eaeb99ee680660df4f9d2e06ea5038.
Directive blob: e505f35522b675c6b5b263eac73618d717346973.
Complete-wheel source: research/CompleteSquareRootWheelFractionalBoundary.lean,
blob ecb482e52deeee5e9b3853592a3ffdace662d2ff.
Original prefix count/density: research/VF_MID_DYADIC_PREFIX_OWNER.lean,
blob c499ca7bd7d90fb32f9cd99d652961ea023bed58.

For R>=2, X_R=R^2-1, delta(z)=prod_(p<=z)(1-1/p),
F_R=sum_(d|P_(R-1))mu(d)fract(X_R/d),
D_R=X_R delta(R-1)+pi(R-1)-1-li(X_R).
The exact certified identity is Z_R=F_R-D_R=li(X_R)-pi(X_R).
One constant C>=0 before all R with |Z_R|<=C R log R remains OPEN.
The canonical VF square von Koch statement is also OPEN. The formal classical RH bridge retains its explicit criterion hypothesis.

### C. Continuity And Source Evidence

Report intake: agent-reports@41ee0c5ef84460b6ef869d8444ea2dbd893fe4ee.
Today Owner FW1-FW6 (bb695ee0ba98f44038cce54d3ae3039e1c28c7f2)
and Analytic SC1-SC6 (f17f13f252d8855accc04cf5c2b5e2ebd1297522)
are available. They retain independent-review-pending paper status.
Today Coordinator, Census, Referee and Lean are TODAY=PENDING;
their November 8 reports are YESTERDAY=CARRY_FORWARD.
Own November 8 FD report blob 60d4cf1b65d4b1b2cc4f13f6c0940c14cb2c50fd
is read as continuity, not the new task selector.
Preserve Coordinator FM's non-Mobius scope, Census FR sign falsifiers,
Referee's paper EC acceptance and separately pending SG, and Lean's actual EC
certification. Current metadata verifies #1119, #1118 and #1122 merged;
stale PR-body statements do not override that metadata.
External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry
newer than October 18. Retain EXT-20261018-PNT-1..3's signed-source safeguards
and EXT-20261017-XCOORD-1's prime-root endpoint warning; old routing is superseded.

### D. Frozen Test And Competing Hypotheses

Define C_z(N)=finiteWheelFract(z,N)-N delta(z)=-Phi_z(N).
At the root step let X=R^2-1, Y=(R+1)^2-1 and
A_R=Phi_(R-1)(Y)-Phi_(R-1)(X).
Compare adjoining prime R at X versus Y, retaining the centered pi increment.

Hypothesis to prove or refute: for prime R>=3 the Y-adjunction removal is
2+1_(R+2 prime); the difference between old-wheel and new-wheel shell counts
is 1+1_(R+2 prime). R=2 is tested separately, not assumed generic.
Rival: additional squareful/compound cofactors or boundary transfers break this
bounded-support claim. A positive all-root centered admission also tests the
shortcut that new primes always improve the signed remainder.

Before execution, freeze these exact tests:
- Full Boolean-divisor rational ledgers and virtual/Euler pairing for R=2..43,
  at BOTH X and Y, including all divisors d>X or d>Y.
- Independent direct integer survivor enumeration, primality and least-factor
  classification for every shell R=2..256.
- Root-prime cofactor tests for every prime R<=4096 using exact trial division,
  without computing pi(R^2) there.
- Generic prime-adjunction floor and fractional recurrences on fixed wheels
  1,2,6,30,210 with each next prime and N=0..128.
- Explicit endpoint witnesses: R=2,3,5,10,12,14 and 17; prime-root equality,
  twin endpoint R(R+2)=Y, d=X, virtual-to-physical transfer, and nonmonotonic
  fractional discrepancy. Any later tests must be labeled additions.

No fitted logarithmic integral or RH-strength statistical inference is planned.
Existing accepted wheel computations are not rerun as new discoveries;
these tests target the changed root-transition hypothesis.

### E-M. Pending Research And Publication

Derivation, novelty search, counterexamples, complete signed return, specialist
handoffs and final resume capsule will be appended after the actual work.
No source edit, local Lean, PR, branch, other report, schedule or agent launch.
Self-audit is not independent Referee acceptance. This checkpoint is not a
completed proof or successful publication claim until immutable readback.

## Root-Adjunction Support, Uniform Cost, And Contraction Falsifiers - 20261109-wheel-1/RA

### A. Most Important Structural Discovery

**PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.** The exact root-admission channel of the fully compensated fractional wheel has bounded physical support. For an odd prime root R, its centered innovation is exactly one prime-square occurrence, plus one further occurrence if R+2 is prime. It is positive, not an automatic cancellation. At R=2 the innovation is three, and at composite roots it is zero.

For EVERY pair of integers 2<=A<=B, the cumulative centered admission satisfies

```text
0 <= K(A,B) <= 2(B-A) + 1_(A=2<B).
```

Thus this particular moving-cutoff channel is affordable at O(B), uniformly in the exponentially growing wheel. This is NOT a bound on the entire signed innovation: expanding the physical square shell leaves a separate, unpaid signed discrepancy.

The decisive mechanism result is a **genuine-source counterexample to automatic absolute contraction**. At root R=3 and the next endpoint Y=15, adjoining prime 3 changes the intermediate centered remainder from li(15)-8 to li(15)-6. Its squared magnitude increases by 4(li(15)-7)>0. A rational, nonnumerical lower certificate for li(15)>7 is proved below. At the old endpoint X=8, the centered remainder is instead unchanged and nonzero, which separately rules out any uniform strict per-adjunction contraction factor less than one.

| Claim ID | Content | Evidence And Novelty Scope |
| --- | --- | --- |
| 20261109-wheel-1/RA1 | Correct natural-argument fractional recurrence, including the fractional-quotient correction | IDENTITY_ONLY; adapter derived from existing counting/Euler identities, not credited as a new sieve recurrence |
| RA2 | Exact lower-closed square-shell admission support and prime-square/twin correction, with R=2 exception | PAPER_PROOF; source-specific sharpening of existing owner/terminal structure |
| RA3 | Uniform cumulative compensated admission cost and complete centered return | PAPER_PROOF for the proper-component bound; remaining whole-shell bound is TARGET_EQUIVALENT / OPEN |
| RA4 | Actual-li failure of nonincreasing absolute centered error; strict contraction also impossible at the old endpoint | REFUTED auxiliary mechanisms, proved on the genuine source |
| RA5 | Exact registered finite diagnostics and disclosed rational logarithm certificates | FINITE_COMPUTATION / PASS; no Lean or independent Referee certification |

The coarse O(B) capacity is consistent with prior two-slot owner bounds; it is not advertised as a new global cancellation principle. The useful additional information is the exact signed root response, its endpoint atoms, and the explicit failure of the proposed local contraction rule on this complete-wheel source. No literature-priority claim is made.

NEW_VERIFIED_ENDPOINT_GAIN=NONE. Canonical VF, the uniform complete-wheel O(R log R) bound, finite A/C, and RH remain OPEN.

### B. Current Authoritative Objective

This is the same scheduled invocation triggered at 2026-11-09 02:05:03 EST, America/New_York. RUN_ID_UNAVAILABLE. The main authority is **8110624150e444964f998676bf54e2e9a3b7e91c**; `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`.

For integer z,N>=0 let

```text
P_z = product_(prime p<=z) p,
delta(z) = product_(prime p<=z) (1-1/p),
Phi_z(N) = #{integer n: 1<=n<=N, gcd(n,P_z)=1},
F_z(N) = sum_(d|P_z) mu(d)*fract(N/d),
C_z(N) = F_z(N)-N*delta(z) = -Phi_z(N),
G_z(N;L) = C_z(N)-pi(z)+1+L.
```

All divisor sums are COMPLETE, including d>N. `F_z` here is exactly the source's `finiteWheelFract z N`; `Phi_z` and `delta` are `vfMidPrefixWheelCounting` and `vfMidPrefixWheelDensity`. G is an explicitly defined intermediate centered coordinate, not a replacement for the endpoint target. The reference L is an arbitrary real in the certified interface.

At X_R=R^2-1, the original target is

```text
Z_R = G_(R-1)(X_R;li(X_R)) = F_R-D_R = li(X_R)-pi(X_R).
exists C>=0, forall integers R>=2, |Z_R|<=C R log R.     OPEN
```

The logarithmic integral is the principal-value li. Li_2 denotes integral_2^x dt/log t and differs by li(2). This fixed anchor is never discarded in Z_R.

The canonical `VFCanonicalSquareVonKochStatement` and its consumer were read at blob **79030d70e8d3e0d08eef9bac53fef95c36eca2fb**. The displayed Lean consumer `riemannHypothesis_of_vfCanonicalSquare` retains its explicit `ClassicalVonKochRHCriterion` argument. No unconditional formal von Koch import is newly asserted. The inherited Mertens improvement in merged #1119 is not transported to this wheel by analogy.

### C. Structural Mechanism Investigated

Separate the two operations in the exact root step:

```text
(cutoff R-1, endpoint X_R) -> (cutoff R-1, endpoint X_(R+1))
                         -> (cutoff R,   endpoint X_(R+1)).
```

The first expands the physical interval; the second adds a prime coordinate only when R is prime. Reverse the order to compare their interaction. Unique factorization and the strict upper square wall constrain the removed physical integers, even though the divisor cube grows exponentially.

This is distinct from Owner FW2-FW4's proportional owner-band bias, Analytic SC's hyperbola smoothing cost, and the previous MU-LIFT FD matching carrier. Their conclusions remain at their original scopes. The question is whether the moving root itself offers a contracted signed recurrence, not whether another fixed wheel has a slightly better density.

### D. Exact Theorem Statements

#### RA1. Prime Adjoining With The Actual Natural-Number Interface

For every prime p and every integer N>=0, write q=floor(N/p), theta=N/p-q. Then

```text
delta(p) = (1-1/p)*delta(p-1),
Phi_p(N) = Phi_(p-1)(N)-Phi_(p-1)(q),                  (1)
F_p(N) = F_(p-1)(N)-F_(p-1)(q)-theta*delta(p-1),       (2)
C_p(N) = C_(p-1)(N)-C_(p-1)(q),                       (3)
G_p(N;L)-G_(p-1)(N;L) = Phi_(p-1)(q)-1.              (4)
```

The last formula holds for EVERY real L. For a nonprime cutoff r>=2 all four cutoff-indexed quantities are unchanged except that the displayed prime-specific formulas are not invoked. The missing theta term makes the naive natural-argument F recurrence false.

#### RA2. Exact Root Support

For every integer R>=2, put X=R^2-1 and Y=(R+1)^2-1=R(R+2). Let i_R=1_(R prime), t_R=1_(R+2 prime), and e_R=1_(R=2). Define

```text
I_R = C_R(Y)-C_(R-1)(Y),
kappa_R = G_R(Y;L)-G_(R-1)(Y;L),
A_R = Phi_(R-1)(Y)-Phi_(R-1)(X).
```

Then, independently of L,

```text
I_R = i_R*(2+t_R)+2e_R,
kappa_R = I_R-i_R = i_R*(1+t_R)+2e_R,                 (5)
G_R(X;L)-G_(R-1)(X;L) = 0.                           (6)
```

The composite old-wheel survivors in the LOWER-CLOSED, UPPER-OPEN square shell [R^2,(R+1)^2) are exactly

```text
{4,6,8}                                      if R=2;
{R^2} union {R(R+2): R+2 prime}               if R>=3 is prime;
empty                                       if R is composite.
```

These sets contain kappa_R physical integers, each once. In particular

```text
A_R = pi(Y)-pi(X)+kappa_R.                              (7)
```

Removing R^2 changes the original shell convention and invalidates (5). The possible twin-product R(R+2)=Y is INCLUDED. The next square (R+1)^2=Y+1 is EXCLUDED.

#### RA3. Uniform Cumulative Innovation And Complete Return

For integers 2<=A<=B define H=B-A and

```text
K(A,B) = sum_(A<=r<B) kappa_r,
T(A,B) = #{prime p: A<=p<B, p+2 prime}.
```

Then

```text
K(A,B) = pi(B-1)-pi(A-1)+T(A,B)+2*1_(A=2<B),           (8)
0 <= K(A,B) <= 2H+1_(A=2<B).                            (9)
```

No theorem on the frequency of twin primes is used. The exact support gives the uniform bound even if every eligible prime were the smaller member of a twin pair.

For the original li reference, define the entire old-wheel shell residual

```text
E(A,B) = integral_(A^2-1)^(B^2-1) dt/log(t)
         - sum_(A<=r<B) A_r.
```

Then exactly

```text
Z_B-Z_A = E(A,B)+K(A,B),                                (10)
|(Z_B-Z_A)-E(A,B)| <= 2H+1_(A=2<B).                     (11)
```

The estimate pays ONLY the centered cutoff-admission channel. `E(2,B)=O(B log B)` is TARGET_EQUIVALENT to the current whole-endpoint bound, because the anchor Z_2 is fixed and K(2,B)=O(B). It is not an independently established or weaker final supplier.

### E. Mathematical Proofs

#### Finite Factorization, Signs, And Rounding

The complete divisor set for P_p is the disjoint union of d|P_(p-1) and p*d with d|P_(p-1). Squarefreeness gives mu(pd)=-mu(d). This is a unique DIVISOR occurrence decomposition, not yet a partition of physical integers. The density recursion follows by retaining the full reciprocal sum.

The count recurrence (1) is already the on-main declaration `vfMidPrefixWheelCounting_cast_int_prime_step`. Its physical map is n=p*k: the old survivors removed by adding p correspond bijectively to k<=floor(N/p) with gcd(k,P_(p-1))=1. No removed physical integer is counted twice.

To check (2) directly without changing the source's natural argument, write q=a*d+b with integers 0<=b<d. Since 0<=theta<1,

```text
fract((q+theta)/d) = b/d+theta/d
                 = fract(q/d)+theta/d.
```

Summing mu(d) over the complete old divisor set proves (2). Alternatively it follows algebraically from (1) and F=N delta-Phi. Equation (3) is the same identity after Euler compensation; pi(p)-pi(p-1)=1 gives (4). The raw correction theta*delta(p-1) cannot be dropped by treating floor(N/p) as the exact real quotient.

For a virtual new divisor pd>N, its fractional contribution -mu(d)*N/(pd) and its contribution to minus the Euler bulk +mu(d)*N/(pd) cancel BEFORE any bound. This includes divisors with p*d above BOTH X and Y. During endpoint expansion, each old divisor d in (X,Y] enters the compensated floor sum with its actual sign -mu(d). For R>=3, Y<2X, so its new floor is exactly one. R=2 has no such old divisor. Divisors d=X stay physical, and their floor terms do not vanish merely because fract(X/d)=0. These exact floor changes are all included in A_R; none is replaced by a favorable-sign population.

#### Root Cofactors And Complete Physical Support

For prime R,

```text
floor(X/R)=R-1,       Y/R=R+2.
```

The only positive old-wheel survivor <=R-1 is 1, so (4) at X is zero. At Y and prime R>=3, the old cofactor survivors <=R+2 are precisely 1, R, and possibly R+2. Every integer in [2,R-1] has a prime factor below R; R+1 is even; a composite R+2 has a prime factor <=sqrt(R+2)<R. The surviving cofactor R+2 is therefore present exactly when it is prime. At R=2 the old wheel is empty and its cofactor survivors are 1,2,3,4. This proves (5)-(6). For composite R no coordinate or pi(R) increment is added.

There is also a direct independent shell proof. If a composite n in [R^2,(R+1)^2) survives all primes below R, its least prime factor p satisfies R<=p<=sqrt(n)<R+1. Hence p=R and R is prime. Writing n=R*m gives R<=m<=R+2. For R>=3 only m=R and, if prime, m=R+2 survive the old wheel. At R=2 direct inspection gives 4,6,8. Every prime in the shell survives both cutoffs, and no other composite survives cutoff R. This proves the set statement and (7).

The factor R^2 is a genuine physical occurrence even though mu(R^2)=0. Its weight in the survivor count is one: the source uses signed DIVISOR coefficients mu(d), not the physical function mu(n). Confusing those two roles would delete the leading correction in (5).

Each counted physical correction lies in its unique shell, so it cannot be spent again in another root step. The exact labels R+2 are not an assumed distribution of future primes: primality in this tiny cofactor range can itself be tested by the old primes below R. The uniform bound simply uses t_R<=1.

#### Cumulative Bound And Reassembly

Sum (5). The i_R terms count primes in [A,B), the i_R*t_R terms count the stated twin pairs, and the exceptional root 2 contributes its extra two. This proves (8). Each summand kappa_R<=2 except kappa_2=3; thus (9) follows for all A,B, including A=B. There is no scale-dependent modulus or hidden constant.

At a fixed old cutoff, C_(R-1)(Y)-C_(R-1)(X)=-A_R. With the changing reference L=li(endpoint), the complete root increment is

```text
Z_(R+1)-Z_R = li(Y)-li(X)-A_R+kappa_R.                  (12)
```

To exhibit both original fractional and deterministic terms before subtraction, write d_R=delta(R-1). For prime R the admission contribution to F is I_R-(R+2)d_R; for composite R it is zero. In unified form,

```text
F_(R+1)-F_R = (2R+1)d_R-A_R+I_R-i_R(R+2)d_R,
D_(R+1)-D_R = (2R+1)d_R-i_R(R+2)d_R+i_R-[li(Y)-li(X)].
```

Their difference is (12). The full finite Euler change, unit/prime correction, every virtual divisor, and both physical endpoints are accounted for. Summing over R telescopes li with its original normalization and proves (10)-(11).

If the scalar return is squared, it is exactly

```text
Z_B^2 = Z_A^2+E(A,B)^2+K(A,B)^2
        +2Z_A E(A,B)+2Z_A K(A,B)+2E(A,B)K(A,B).
```

No mixed term is declared negative or deleted. This report uses the scalar additive estimate (11), not an unjustified separate quadratic reserve. Bounding the proper K term does not independently bound its product with the unpaid E term.

### F. Structural Consequence

The moving square-root cutoff is incapable of creating an arbitrary large admission packet at a single step. Its entire compensated response is supported on one square and at most one twin-prime product, except for the explicit first root. It also cannot improve the already centered old endpoint at all: (6) is an exact plateau.

This identifies a quantitative limit of the proposed recurrence mechanism. The root channel costs O(B), and its sign is nonnegative. The substantial global question lies in the joint physical shell residual E, which is not controlled by this support theorem. No large-wheel extrapolation, independence assumption, prime-density replacement, or matching theorem is used.

### G. Signed And Quantitative Relevance

The constant in (9) is explicit and independent of A, B and the number of wheel primes. At A=2, it costs at most 2B-3 for B>=3. This is below the allowed O(B log B) scale, but it applies to only one term of the exact complete return.

For example, if an independently proved |E(2,B)|<=C B log B became available, (10) would yield the target with the enlarged constant

```text
C + 2/log(2) + |Z_2|/(2 log(2)).
```

Conversely the same triangle inequality bounds E from the target. Therefore this proposed whole-residual supplier is explicitly TARGET_EQUIVALENT, not a smaller independently paid lemma. The report does NOT assume it.

This has no automatic transfer to Owner's OPEN-FW-CROSS-QUADRATIC or Analytic's retained finite-frequency interaction. Those proper terms retain the two linear responses, historical triangle, other owners, and their own masks. SC's paid boundary error remains useful at its paper scope. RA does not provide a correlation estimate for those transforms or a new Mertens exponent.

### H. Falsification, Novelty, And No-Circularity Review

#### RA4. Actual-Source Contraction Fails

At R=3, X=8, the old wheel is {2} and the enlarged wheel is {2,3}. Direct exact values are

```text
F_2(8)=0,       F_3(8)=-1/3,
Phi_2(8)=4,    Phi_3(8)=3,
G_2(8;L)=L-4 = G_3(8;L).
```

Thus omitting theta=2/3 in (2), where delta(2)=1/2, would give the false F_3(8)=0. The raw fractional magnitude also increases from zero. More importantly, the exact centered remainder stays unchanged. With L=li(8)>4 proved below, no fixed q<1 can satisfy |G_R(X_R;li(X_R))|<=q|G_(R-1)(X_R;li(X_R))| for every R>=2.

At the next endpoint Y=15,

```text
Phi_2(15)=8,     Phi_3(15)=5,
G_2(15;L)=L-8,  G_3(15;L)=L-6,
|G_3(15;L)|^2-|G_2(15;L)|^2 = 4(L-7).
```

The absolute centered-error nonincrease claim is therefore FALSE for the genuine reference L=li(15). The two extra physical composites are 9 and 15. This refutes an auxiliary per-prime monotonicity mechanism, not the complete Z bound, not Owner's stated strip inequality, and not RH.

Here are exact analytic sign certificates, without a fitted numerical li value. First li(2)>0, since its principal-value integral can be paired as

```text
li(2) = integral_0^1 [1/log(1+s)+1/log(1-s)] ds > 0.
```

For 0<s<1 the integrand is log(1-s^2)/(log(1+s)log(1-s))>0; its endpoint limits are finite (at zero the limit is one). For t>1, f(t)=1/log t is strictly convex because f''(t)=(log t+2)/(t^2 log^3 t)>0. Thus every midpoint panel supplies a lower integral bound width/log(midpoint).

On panels [2,3], [3,5], [5,8], use the respective strict logarithm upper bounds 23/25, 7/5, 2 at midpoints 5/2,4,13/2. Consequently

```text
Li_2(8) > 25/23+10/7+3/2 = 1293/322 = 4+5/322.
```

For [2,3], [3,4], [4,6], [6,8], [8,12], [12,15], use upper bounds 23/25,63/50,81/50,39/20,231/100,261/100 at midpoints 5/2,7/2,5,7,10,27/2. Then

```text
Li_2(15) > 25/23+50/63+100/81+40/39+400/231+100/87
          = 54249785/7725861 > 7.
```

Each log(m)<b is certified by the exact rational inequality sum_(k=0)^12 b^k/k!>m, a positive lower partial sum for exp(b). These nine rational checks passed. Since li(2)>0, both strict inequalities also hold for principal-value li. The logarithm certificates were a disclosed proof-led addition to the originally frozen arithmetic tests, not retroactively labeled preregistered numerical integration.

#### RA5. Executed Exact Checks

The original test registration was committed BEFORE execution at **c9499fe0a74c245c76ca554ce9f31bd7b546e9a0**, blob **2ff29a93277aebfc6e478ad88623884bc38ea408**, and read back identically. The standard-library verifier passed twice; Python syntax validation also passed.

| Diagnostic | Exact Executed Scope |
| --- | --- |
| Complete wheels | 42 roots R=2..43; 168 rational endpoint/cutoff ledgers |
| Full divisor processing | 240234 divisor visits, including 224233 virtual visits |
| Old virtual-to-physical transitions | 99 divisor occurrences, preserving signs |
| Fixed prototype recurrences | 645 cases for wheels 1,2,6,30,210 and N=0..128 |
| Direct physical shell comparison | Every R=2..256, 66045 integer sites |
| Independent local root classification | All 564 primes R<=4096, via trial factorization, without large-root pi(R^2) |
| Primality cross-check | Trial division versus sieve on 0..4098 |
| Complete squared return | 126 exact rational-reference reconstructions, all three diagonals and three cross terms |

Finite cumulative kappa on roots 2..256 is 73. This is an observation, not the proof of the all-scale bound. The boundary d=X appears at R=14,d=195,mu(d)=-1, among others. Its compensated term is retained. At R=2 the actual composite correction is {4,6,8}, refuting the unqualified odd-prime formula. At R=3 and R=5 the corrections are {9,15} and {25,35}, retaining the upper twin-product atom. At composite roots 10,12,14 the correction is empty. R=17 has {289,323}.

Verifier SHA-256: **4ccd46b23415715963f63116d5c5ed978da6ded9dab0bc499f0aa9ad08f9fb2d**.
Canonical records SHA-256: **628e8e36c990e917da29e8f43773f3e82d36e4ba87351c26d88f02027f21f56d**.

The cube calculation, direct physical survivor filter, and trial least-factor classification are separate finite checks within this SAME execution. This is SELF_AUDIT, not independent Referee acceptance. No finite census proves the all-root assertions; their elementary proofs are above.

#### Novelty And Existing No-Go Audit

Repository searches for `finiteWheelFract`, `vfMidPrefixWheelCounting`, root/twin and prime-adjunction terms located the existing generic recurrence, owner counting modules and compensated source. The generic recurrence (1), inclusion-exclusion, and Legendre identity are explicitly reused, not renamed as new results.

`VF_MID_DYADIC_OWNER_PARITY_TWO.lean` already has a two-slot bound on a STRICTLY OPEN square band with a fixed earlier cutoff, and an unsigned triangular run consequence. It is not an identical statement about this lower-closed square-prefix transition: the prime square is excluded there and included here. RA2 specifies the exact remaining slots and RA3 transports them through the original fractional, Euler, pi and li ledgers. The coarse capacity is a specialization of familiar existing arithmetic restrictions; the meaningful negative result is RA4 on the actual centered source.

`LowWheelSurvivorFloorExpansion.lean` already warns that a different one-prime Mertens frontier collapses to a source identity. Its no-go is retained at its own carrier. Here (10) likewise does not constitute a new endpoint restriction, and its target-equivalent residual is labeled explicitly. No claim is made that all prime-adjunction methods, cross-owner compensation, or the current campaign are impossible.

Search scope was the current default-branch index, named original modules, relevant two-day reports and no-go sources. This is not an exhaustive literature-priority assertion or a proof that every equivalent theorem in the repository has been excluded.

### I. Conceptual Interpretation

The root cutoff and the physical endpoint are coupled, but the coupling is highly rigid: at this exact square step there are only the specified exceptional composites. This explains why root admission can be quantitatively harmless after compensation while providing no strict damping at the old endpoint and sometimes worsening the centered error at the new one.

The old prime-square omission and the naive floor-argument substitution each lose essential information. Correcting them pays the root-transfer bookkeeping, not the actual prime-shell discrepancy. The next reasoning effort should address genuine joint signed arithmetic in the remaining shell/owner response, not another enlargement of a fixed wheel or a repeated check of the now-explicit root events.

### J. Competing Structural Hypotheses

| Mechanism | Decision |
| --- | --- |
| A fixed strict contraction follows merely from adding the root prime at X_R | REFUTED by the exact plateau and nonzero R=3 source |
| Root prime addition never increases absolute centered error at X_(R+1) | REFUTED at R=3 with the actual principal-value li reference |
| Moving-cutoff compensation alone has a uniformly small cumulative cost | PROVED ON PAPER at (9), with the explicit first-root exception |
| Small cutoff cost implies the complete source bound | REJECTED inference; the full shell residual is target-equivalent and OPEN |
| Joint cross-owner or finite-frequency compensation | Still eligible; Owner FW and Analytic SC preserve its actual unpaid terms |

This is a refinement within the authorized campaign, not a request to change the proof contract. The earlier FINITE-AC/CORR4/MU-LIFT results and their scopes remain preserved; the latest merged directive supersedes their rotation for current task selection.

### K. Specialist Handoffs

| Recipient | Precise Next Action |
| --- | --- |
| Proof Architect | Record (9) as a paid proper root-admission channel, not a new endpoint. Reject strict local admission contraction and absolute monotonicity at RA4's exact scopes. Keep E(2,B) visibly target-equivalent. |
| Owner Payment | Compare this root event with FW1 only through the complete signed/Euler adapter. Include the physical square R^2 even though its physical Mobius value is zero; do not conflate divisor signs with survivor weights. RA does not pay the proportional-band complement. |
| Analytic Type II | The root-shift bookkeeping costs O(B), but no new signed estimate for A_r or the SC retained transforms follows. Investigate a source-faithful joint response rather than assuming these finite admissions provide a contraction factor. Preserve both linear terms and other owners. |
| Prime Census Laboratory | Independently check the small exact witnesses R=2,3,5,14 and the supplied verifier. A changed follow-up should test a concrete proposed joint shell/cross-owner inequality, including its original weights; no larger identical root scan is requested. |
| Adversarial Referee | Audit the lower-closed square, upper twin atom, R=2 exception, theta term, pi shift and rational li certificates. Confirm the target-equivalence of the remaining global E bound. RA is presently SELF_AUDIT only. |
| Lean Verification | After independent review and novelty triage, reuse `vfMidPrefixWheelCounting_cast_int_prime_step` and #1122. The smallest useful candidate is the exact root-support/centered-innovation theorem plus its first-root counterexample. Do not re-prove generic Legendre identities, introduce the global shell estimate as an assumption, or launch a filler formalization solely for theorem count. |

These requests are published only in this owned report. No agent was launched, no queue or another report was edited, and no independent acceptance is implied.

### L. First Independently Missing Theorem

No new smaller independently justified SUFFICIENT theorem for the whole RH-scale estimate was found. The exact remaining aggregate is E(2,B), and an O(B log B) bound for it has the SAME strength as the original target after (9). Renaming it a shell innovation estimate does not make it paid.

The proper research question in today's upstream reports remains the genuinely signed cross-root quadratic interaction (Owner OPEN-FW-CROSS-QUADRATIC, equivalently Analytic's proper low-frequency version after its paper smoothing bound), together with its two linear responses and full complement. RA neither proves that question nor establishes that it is independent of RH. There is no justified new cross-frequency constraint supplied by the two-atom admission support alone.

The strongest next task is therefore to formulate and test a NEW joint-source inequality with independent arithmetic content, explicitly excluding RA4's false local contraction mechanism. A complete recurrence identity or an additional already-affordable boundary term should not be reported as the missing global estimate.

### M. Continuity, Formal Evidence, And Resume Capsule

Source authority and original definitions were pinned before research. Relevant module hashes:

| File | Blob SHA |
| --- | --- |
| AGENTS.md | 6695522a45d67fd1e80a7cff1f98d909405036e2 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_SEVEN_AGENT_FINITE_WHEEL_BOUNDARY_20261108.md | e505f35522b675c6b5b263eac73618d717346973 |
| docs/DYNAMIC_RESEARCH_AGENTS.md | e8d913ff9663bb5163eaf0eddca9f76e0508a7ef |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| research/VF_MID_PHI_OWNER_BRIDGE.lean | 5c81e968179c8b069ff86570002555ba54f8b789 |
| research/VF_MID_DYADIC_OWNER_EXACT.lean | 4fccb05e6f8b3f2f0ec134daecd8990083aa563f |
| research/VF_MID_DYADIC_OWNER_PARITY_TWO.lean | f129aa1acb11011e2af771882ce87562ab675b25 |
| RHLean/Proof/LowWheelSurvivorFloorExpansion.lean | 41a81289c5a49830b6d1a73d3a16d372c907c6b7 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

Two-day continuity was retrieved at agent-reports@**41ee0c5ef84460b6ef869d8444ea2dbd893fe4ee**. Relevant conclusions, handoffs, original claim IDs and evidence status were read; no historical test was represented as rerun here.

| Role | November 8 Blob And Consumed Claims | November 9 Intake |
| --- | --- | --- |
| Coordinator | 8b640304f6c233a2c4409b9882799de485888a9e; FM1-FM3, generalized non-Mobius obstruction, latest 23:33 EST receipt | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |
| Owner | 4e1b83a1e5ff8c134e9ca64404397c70c2b07252; PD/MC/JS scopes and latest signed packet/tail warnings | bb695ee0ba98f44038cce54d3ae3039e1c28c7f2; FW1-FW6, 00:37 EST receipt, paper self-audit |
| Analytic | edecba8785a45cda87c0035d0348695941f1b8ea; EC1-EC5, later EC formalization distinguished | f17f13f252d8855accc04cf5c2b5e2ebd1297522; SC1-SC6, 01:25 EST receipt, independent review pending |
| Wheel | 60d4cf1b65d4b1b2cc4f13f6c0940c14cb2c50fd; latest FD1-FD5, forced factor-depth and exact allocation, not a global bound | Own report absent at intake; this is its first actual run |
| Census | 00f4f9c0d670821a0c9d1da31fd1c4d0afd09142; FR1-FR5; held-out R=258/307 and retrospective R=6/28 sign falsifiers | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |
| Referee | 5371324ebbdbd88afb9abf843e83da2ce86b752f; EC1-EC4 ACCEPT/ACCEPT_WITH_SCOPE at paper level; SG remains self-audit | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |
| Lean | 5a110685bbe375d8ebff42df7391162914e52cef; #1119 exact proof head 77ee815846d6d534c866f0752aa33b84c385610a and 03:11 UTC receipt | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |

The external inbox blob **038018145c0fddb2f6306c0712373adf9cd1ea52** has no entry newer than October 18. EXT-20261018-PNT-1..3 retain the complete signed/cofactor and original-source safeguards; EXT-20261017-XCOORD-1 records the q=R endpoint correction; EXT-20261014-5 remains limited to its original unconditional-denominator limsup scope. None supplies the new root theorem, a new signed endpoint bound, or current task routing. Old schedules and PR status prose in that inbox do not override current authority.

**Formal evidence actually inspected:** #1122 is merged at 8c9e54ec3dffbe8c0a4136e835814a0c041054a1. The ten returned PR-triggered workflow runs attached to head c53e9cf234500aea2605fd2557e638995f380407 all succeeded; this is not an exhaustive count of every check type. The actual [targeted job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42561949462/job/128980092032) checked out **synthetic merge 1e3c182076a6e1a23ef132c41a78b0f26adab507**, not the literal PR head. The source was fetched there and matched current main byte-for-byte at ecb482e52deeee5e9b3853592a3ffdace662d2ff. The job compiled Lean 4.34.1 and printed only propext, Classical.choice, Quot.sound for the centered equality and physical compensation declarations. Its compiler script blob eb3d429b14bf66ba2fba22e55b70ca0048f748c6 explicitly sets `-DwarningAsError=true`. This is inherited tested-source evidence, not a newly run exact-main build; runtime warnings are not denied.

Current metadata independently verifies #1119 merged 2026-11-09T04:57:27Z, #1122 at 04:59:27Z and #1118 at 05:12:59Z. Their old report/PR-body unmerged labels are superseded. #1123 is the merged research-direction update, not an arithmetic theorem. The open/draft PR search at intake returned none. No new CI was requested. RA1-RA5 are NOT new compiled declarations.

Actual execution limitations: direct git access returned CONNECT tunnel HTTP 403, so immutable authenticated connector reads/writes were used. No local Lean was run. No main/source/central-policy/branch/PR/issue/workflow/schedule/permission changes were made, and no other report or agent was touched. All finite command sessions completed. No background work is promised.

```text
RUN=20261109-wheel-1; scheduled 02:05:03 EST; RUN_ID_UNAVAILABLE.
MAIN=8110624150e444964f998676bf54e2e9a3b7e91c.
ACK=FINITE_WHEEL_CENTERED_RH_V1.
SOURCE=complete signed fractional wheel, X_R=R^2-1, every virtual divisor retained.
REUSED=on-main prime-step count recurrence, Euler identity, #1122 compensation.
NEW_SCOPE=exact prime-square/twin root correction and actual-li contraction falsifiers.
PAID=0<=K(A,B)<=2(B-A)+1_(A=2<B), a proper scalar channel only.
UNPAID=joint signed physical shell residual and complete O(R log R) target.
STATUS=PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.
NO_GLOBAL_GAIN; RH and canonical VF remain OPEN.
NEXT=independent root-support/contraction audit; new joint-source arithmetic,
     not another generic recurrence or repeated bounded root-event census.
```

Substantive publication is not claimed until commit/readback and changed-path verification. The following reproducibility appendix and subsequent publication receipt preserve the checkpoint as an unchanged prefix.

### Reproducibility Appendix - RA5

Command: `python root_adjunction_check.py`. Syntax validation: `python -m py_compile root_adjunction_check.py`. Both executions and the syntax check exited successfully. The source and exact captured output follow.


```python
"""Exact diagnostics for 20261109-wheel-1/RA; no Lean or RH assertion."""

from fractions import Fraction as Q
from hashlib import sha256
from math import factorial, gcd, isqrt, prod
import json


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def trial_minfactor(n):
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            return d
    return n


def sieve(n):
    flags = [True] * (n + 1)
    flags[0] = flags[1] = False
    for p in range(2, isqrt(n) + 1):
        if flags[p]:
            for k in range(p * p, n + 1, p):
                flags[k] = False
    return flags


def faces(primes):
    out = [(1, 1)]
    for p in primes:
        out += [(d * p, -mu) for d, mu in out]
    return out


def ledger(ds, n):
    density = sum((Q(mu, d) for d, mu in ds), Q(0))
    fractional = sum((mu * Q(n % d, d) for d, mu in ds), Q(0))
    floors = sum(mu * (n // d) for d, mu in ds)
    physical = sum((mu * Q(n % d, d) for d, mu in ds if d <= n), Q(0))
    virtual = sum((Q(mu * n, d) for d, mu in ds if d > n), Q(0))
    assert fractional == physical + virtual
    assert fractional - n * density == -floors
    for d, mu in ds:
        if d > n:
            assert mu * Q(n % d, d) - Q(mu * n, d) == 0
    return fractional, density, floors, physical, virtual


def direct_count(primes, n):
    modulus = prod(primes)
    return sum(gcd(k, modulus) == 1 for k in range(1, n + 1))


def main():
    flags = sieve(66048)
    primes = [p for p in range(66049) if flags[p]]
    pi = [0] * len(flags)
    for n in range(1, len(flags)):
        pi[n] = pi[n - 1] + flags[n]
    assert all(flags[n] == trial_prime(n) for n in range(4099))

    records = []
    full_ledgers = divisor_visits = virtual_visits = 0
    crossing_visits = 0
    endpoint_witnesses = []
    for r in range(2, 44):
        x, y = r * r - 1, r * r + 2 * r
        ps = [p for p in primes if p < r]
        qs = [p for p in primes if p <= r]
        old, new = faces(ps), faces(qs)
        data = {}
        for z, pset, ds in [(r - 1, ps, old), (r, qs, new)]:
            for n in [x, y]:
                f, density, count, physical, virtual = ledger(ds, n)
                assert density == prod((Q(p - 1, p) for p in pset), start=Q(1))
                assert count == direct_count(pset, n)
                data[z, n] = (f, density, count)
                full_ledgers += 1
                divisor_visits += len(ds)
                virtual_visits += sum(d > n for d, _ in ds)
                records.append([r, z, n, str(f), str(physical), str(virtual), count])
        a = data[r - 1, y][2] - data[r - 1, x][2]
        innovation = data[r - 1, y][2] - data[r, y][2]
        kappa = innovation - flags[r]
        expected = int(flags[r]) * (1 + int(flags[r + 2])) + 2 * (r == 2)
        assert kappa == expected
        assert data[r - 1, x][2] - data[r, x][2] == flags[r]
        for left, right in [(Q(0), Q(0)), (Q(7, 3), Q(8)), (Q(-5), Q(2, 7))]:
            z0 = left + 1 - pi[r - 1] - data[r - 1, x][2]
            z1 = right + 1 - pi[r] - data[r, y][2]
            growth = right - left - a
            assert z1 == z0 + growth + kappa
            assert z1**2 == (z0**2 + growth**2 + kappa**2
                            + 2 * z0 * growth + 2 * z0 * kappa + 2 * growth * kappa)
        for d, mu in old:
            if x < d <= y:
                assert y // d == 1
                assert -mu * ((y // d) - (x // d)) == -mu
                crossing_visits += 1
            if d == x:
                endpoint_witnesses.append([r, d, mu])
        if flags[r]:
            for n in [x, y]:
                q, rem = divmod(n, r)
                f0, delta, _ = data[r - 1, n]
                f1 = data[r, n][0]
                fq = ledger(old, q)[0]
                assert f1 == f0 - fq - Q(rem, r) * delta

    generic_cases = 0
    for count in range(5):
        ps, p = primes[:count], primes[count]
        old, new = faces(ps), faces(ps + [p])
        assert prod(ps) in [1, 2, 6, 30, 210]
        for n in range(129):
            f0, d0, c0, _, _ = ledger(old, n)
            f1, d1, c1, _, _ = ledger(new, n)
            q, rem = divmod(n, p)
            fq, _, cq, _, _ = ledger(old, q)
            assert d1 == d0 * Q(p - 1, p)
            assert f1 == f0 - fq - Q(rem, p) * d0
            assert c1 == c0 - cq
            assert c1 == direct_count(ps + [p], n)
            generic_cases += 1

    shell_rows = []
    physical_sites = 0
    cumulative = 0
    for r in range(2, 257):
        x, y = r * r - 1, r * r + 2 * r
        ps = [p for p in primes if p < r]
        old_survivors = [n for n in range(x + 1, y + 1)
                         if all(n % p for p in ps)]
        independent = [n for n in range(x + 1, y + 1)
                       if trial_minfactor(n) >= r]
        assert old_survivors == independent
        physical_sites += y - x
        composites = [n for n in old_survivors if not trial_prime(n)]
        if r == 2:
            expected = [4, 6, 8]
        elif flags[r]:
            expected = [r * r] + ([r * (r + 2)] if flags[r + 2] else [])
        else:
            expected = []
        assert composites == expected
        new_survivors = [n for n in old_survivors if not flags[r] or n % r]
        assert new_survivors == [n for n in range(x + 1, y + 1) if flags[n]]
        kappa = len(composites)
        assert len(old_survivors) == pi[y] - pi[x] + kappa
        cumulative += kappa
        twin_count = sum(flags[p + 2] for p in primes if p <= r)
        assert cumulative == pi[r] + twin_count + 2
        assert cumulative <= 2 * (r - 1) + 1
        shell_rows.append([r, len(old_survivors), pi[y] - pi[x], kappa, composites])

    cofactor_cases = 0
    for p in [n for n in range(2, 4097) if trial_prime(n)]:
        survivors = [k for k in range(1, p + 3)
                     if k == 1 or trial_minfactor(k) >= p]
        expected = [1, 2, 3, 4] if p == 2 else [1, p] + ([p + 2] if trial_prime(p + 2) else [])
        assert survivors == expected
        cofactor_cases += 1

    # Registered literal source controls, not a numerical li evaluation.
    assert ledger(faces([2]), 8)[0] == 0
    assert ledger(faces([2, 3]), 8)[0] == -Q(1, 3)
    assert ledger(faces([2]), 15)[2] == 8
    assert ledger(faces([2, 3]), 15)[2] == 5
    assert [14, 195, -1] in endpoint_witnesses

    # Disclosed proof-led addition: rational certificates for logarithm bounds.
    # Convexity gives midpoint lower bounds for integrals of 1/log(t).
    panels8 = [(1, Q(5, 2), Q(23, 25)),
               (2, Q(4), Q(7, 5)), (3, Q(13, 2), Q(2))]
    panels15 = [(1, Q(5, 2), Q(23, 25)), (1, Q(7, 2), Q(63, 50)),
                (2, Q(5), Q(81, 50)), (2, Q(7), Q(39, 20)),
                (4, Q(10), Q(231, 100)), (3, Q(27, 2), Q(261, 100))]
    for _, mid, upper_log in panels8 + panels15:
        assert sum((upper_log**k / factorial(k) for k in range(13)), Q(0)) > mid
    lower8 = sum((Q(width) / bound for width, _, bound in panels8), Q(0))
    lower15 = sum((Q(width) / bound for width, _, bound in panels15), Q(0))
    assert lower8 == 4 + Q(5, 322)
    assert lower15 > 7

    print(json.dumps({
        "status": "PASS",
        "full_wheel_roots": 42,
        "full_rational_ledgers": full_ledgers,
        "divisor_visits": divisor_visits,
        "virtual_visits": virtual_visits,
        "virtual_to_physical_occurrences": crossing_visits,
        "d_equals_X_witnesses": endpoint_witnesses,
        "generic_adjunction_cases": generic_cases,
        "shell_roots": len(shell_rows),
        "direct_physical_sites": physical_sites,
        "prime_root_cofactor_cases": cofactor_cases,
        "trial_sieve_checks": 4099,
        "centered_square_reconstructions": 126,
        "kappa_sum_R2_to_256": cumulative,
        "root_examples": [row for row in shell_rows if row[0] in [2, 3, 5, 10, 12, 14, 17]],
        "Li2_8_strict_lower_bound": str(lower8),
        "Li2_15_strict_lower_bound": str(lower15),
        "records_sha256": sha256(json.dumps([records, shell_rows], separators=(",", ":")).encode()).hexdigest(),
        "scope": "Finite exact diagnostics and rational certificates; not Lean, independent review, or a global RH estimate."
    }, indent=2))


if __name__ == "__main__":
    main()
```

Executed output:

```json
{
  "status": "PASS",
  "full_wheel_roots": 42,
  "full_rational_ledgers": 168,
  "divisor_visits": 240234,
  "virtual_visits": 224233,
  "virtual_to_physical_occurrences": 99,
  "d_equals_X_witnesses": [
    [
      14,
      195,
      -1
    ],
    [
      20,
      399,
      -1
    ],
    [
      32,
      1023,
      -1
    ],
    [
      34,
      1155,
      1
    ],
    [
      38,
      1443,
      -1
    ]
  ],
  "generic_adjunction_cases": 645,
  "shell_roots": 255,
  "direct_physical_sites": 66045,
  "prime_root_cofactor_cases": 564,
  "trial_sieve_checks": 4099,
  "centered_square_reconstructions": 126,
  "kappa_sum_R2_to_256": 73,
  "root_examples": [
    [
      2,
      5,
      2,
      3,
      [
        4,
        6,
        8
      ]
    ],
    [
      3,
      4,
      2,
      2,
      [
        9,
        15
      ]
    ],
    [
      5,
      4,
      2,
      2,
      [
        25,
        35
      ]
    ],
    [
      10,
      5,
      5,
      0,
      []
    ],
    [
      12,
      5,
      5,
      0,
      []
    ],
    [
      14,
      4,
      4,
      0,
      []
    ],
    [
      17,
      7,
      5,
      2,
      [
        289,
        323
      ]
    ]
  ],
  "Li2_8_strict_lower_bound": "1293/322",
  "Li2_15_strict_lower_bound": "54249785/7725861",
  "records_sha256": "628e8e36c990e917da29e8f43773f3e82d36e4ba87351c26d88f02027f21f56d",
  "scope": "Finite exact diagnostics and rational certificates; not Lean, independent review, or a global RH estimate."
}
```


### Prepublication Freshness - 2026-11-09 02:25 EST

Live main remained 8110624150e444964f998676bf54e2e9a3b7e91c, the owned report remained the verified checkpoint blob 2ff29a93277aebfc6e478ad88623884bc38ea408, and no open/draft PR was returned. The final directory check confirmed today's available Owner and Analytic reports unchanged; Coordinator, Census, Referee and Lean remain TODAY=PENDING. Both November 8 Coordinator mirror blobs agree. This is source/report freshness evidence, not a claim that any pending agent ran.


### Verified Publication Receipt - 2026-11-09 02:26:50 EST

The substantive report was published at **3e134a504f486ed6c5f936058623a0003e844a19**, blob **8a34a2331f309b2b1ea9b23cb603a4dc4ee6454f**, and fetched at that immutable commit. All **47264 characters** matched the intended content exactly. The initial checkpoint remains an unchanged prefix. Commit metadata confirms that the ONLY changed path is research/agent_reports/2026-11-09/30-finite-wheel.md.

[Immutable substantive report](https://github.com/OVVO-Financial/RH_Lean/blob/3e134a504f486ed6c5f936058623a0003e844a19/research/agent_reports/2026-11-09/30-finite-wheel.md).

EXECUTION=COMPLETE; SUBSTANTIVE_PUBLICATION=PUBLISHED_AND_READBACK_VERIFIED. RA2-RA4 remain PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED; RA1 is reused-source algebra; RA5 is FINITE_COMPUTATION. The proper root-admission cost is paid, but no global endpoint gain, finite A/C, canonical VF or RH proof is claimed. The complete O(R log R) bound remains OPEN.

No main, Lean source, proof branch, PR, issue, workflow, policy, other report, schedule or permission was changed. No agent was launched and no local Lean executed. Every required command session finished. Resume with independent audit of the exact root-support and actual-li contraction falsifiers, then a new joint-source arithmetic hypothesis, not another generic recurrence or unchanged root scan.

This receipt records the already completed substantive verification. Its own append is separately checked by immutable readback before the final user-facing response.


## Early Dyadic Incidence Checkpoint - 20261109-wheel-2

### A. Most Important Structural Question

IN_PROGRESS / PARTIAL. Investigate whether unique factorization restricts exact normalized prime-product resonances between adjacent dyadic roots, and whether this restriction can justify a signed cross-scale potential. Distinct frequencies alone will not be assumed to be orthogonal on a finite band. No new global estimate or independently reviewed theorem is claimed at this checkpoint.

### B. Current Authority And Continuity

Actual scheduled trigger: 2026-11-09 10:12:01 EST, America/New_York; RUN_ID_UNAVAILABLE. Checkpoint prepared after source intake, 2026-11-09 10:18 EST (timestamp will be verified in the final receipt).
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.
Main=02f00cee544278ad1bb9022ee76fc5916d459a95.
AGENTS=6695522a45d67fd1e80a7cff1f98d909405036e2.
CURRENT_PROOF_CONTRACT=95566e37c8eaeb99ee680660df4f9d2e06ea5038.
Directive=e505f35522b675c6b5b263eac73618d717346973.
Complete-wheel source=ecb482e52deeee5e9b3853592a3ffdace662d2ff.

The original target remains one C>=0 before all integers R>=2 with
|F_R-D_R|=|li(R^2-1)-pi(R^2-1)|<=C R log R. OPEN.
Every virtual divisor and its Euler compensation, the li anchor, full physical
owner complement, both linear orientations and all square cross terms remain.

Report intake agent-reports@5fe5e114d31c9d7f37548e2097f0c03fa15b1fdc:
today Coordinator FB/MP/SHIFT, Owner FW/CT, Analytic SC/MB, own RA,
Census CR and Lean RA implementation are available and read at their stated scopes.
Referee TODAY=PENDING; November 8 EC acceptance/SG is YESTERDAY=CARRY_FORWARD.
All seven relevant November 8 reports were also retrieved and their latest
results/resume capsules read. Yesterday's FD allocation problem is preserved
but superseded for task selection by the live complete-wheel directive.
External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 is unchanged since its
October 18 entry; original EXT-PNT and prime-root endpoint safeguards remain.

Live open/draft PR collection is empty. #1124 is human-merged, not pending:
its literal-head 1b80f147dab3c0c2525052b3c6c3f8c447089da1 has 13 successful
checks, and the targeted log prints the standard terminal axioms and live
dependency audits. Its root cost is a PAID proper component, not this run's
discovery. #1122's actual synthetic checkout and source evidence were read.
No local Lean, source edit, PR or CI launch.

### C. Registered Structural Attempt

For integer R>=8 put X=R^2-1, Y=4R^2-1 and define the actual prime pairs
E_R={(p,q): p,q prime, R/2<=p<R<=q<2R}.
Each product is a unique cross-root semiprime occurrence; it is physically
admitted at X precisely when pq<=X. The larger rectangle remains necessary
for the frequency representation, and its inadmitted portion is not deleted.

Test whether equality X/(pq)=Y/(uv), with (p,q) in E_R and (u,v) in E_(2R),
forces pq=X and uv=Y. If true, characterize the boundary atoms and exploit
gcd(X,Y)=gcd(X,3), rather than assume generic phase separation.

Test the competing hypothesis that such exact resonance rigidity supplies
finite-band orthogonality or nonpositive shared-prime cross terms. Examine
actual chains p,q,r with r=4p+1 or 4p-1 and overlapping middle prime q.
No assertion of infinitely many such chains is required or presumed.

For the proposed dyadic potential set R_j=2^j R0, a_j=log(1-R_j^(-2)),
theta_0=0, theta_(j+1)=a_j-log 2-theta_j, z_j(t)=exp(it theta_j)A_(R_j)(t).
Inspect the exact polarization of Im(z_j z_(j+1)) using Im(z_j^2) and
Im((z_(j+1)-z_j)^2). Keep all interior, first/last and constant-frequency
terms; do not silently alternate the original scale weights or conjugate
the original product. Fixed smooth modes and MB4 remain required scope tests.

### D. Frozen Validation Before Arithmetic Execution

- Exact rational phase-set intersections for every R=8..128 and held-out
  R=129..256, plus fixed R=257 and 1024, retaining pq=X and uv=Y.
- Independently compare prime sieving and trial division through 4096.
- Exact shared-prime witnesses at R=8 and 64, with closed physical product
  admission checked at both roots; derive rational bounds certifying the
  sign over the ENTIRE common band [sqrt(R),2sqrt(R)], not sampled cosines.
- Actual A/B SHIFT diagnostics at integer roots 8,12,30,64,257 and frequencies
  0,1,3,8; half-integer R=11/2 and 13/2 retain the prime atom at 2R.
  Continuous integrals are diagnostic unless separately enclosed.
- Exact Gaussian-integer polarization checks for chain lengths 1..6,
  including a constant chain which would falsify a boundary-only telescope.
- A fixed smooth power-density mode, on one global measure across scales,
  tests the claimed source-generic potential; it is explicitly NON-PRIME.
- Search current source and report statements for duplication before claiming
  novelty. No unchanged wheel census or accepted root-admission proof rerun.

### E-M. Pending Work And Publication

The final A-M derivation, complete signed return, precise no-go scope,
reproducer and specialist handoffs will be appended after actual verification.
This checkpoint does not certify a theorem, claim RH progress, or trigger
other agents. Prior report bytes and all original claim IDs are preserved.
Publication is PENDING until immutable readback.
