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


### Proof-Led Registration Addendum - 20261109-wheel-2/DG

This is a disclosed extension of the checkpoint, before execution of the new
test script, not a retroactive claim of preregistration. Analytic MB4's
root-dependent model can be placed on disjoint adjacent pairs of dyadic
annuli R_j=4096*4^j. This proposes ONE fixed, locally finite absolutely
continuous signed measure on [2,infinity), with zero mass on every aligned
dyadic interval and |sigma|<=dli/2. Its entire dyadic transform sequence
automatically obeys SHIFT, including the intermediate roots 2R_j.

Question: does this globally consistent assembly retain MB4's original
moving-band lower bound along R_j? Prove the assembly and recheck the reused
local bound independently. It is a NON-PRIME model, not a wheel/divisor
counterexample and not an asserted zeta mode. New diagnostic tests concern
cross-annulus consistency, both even and intermediate scales, zero marginals
and SHIFT. The three pair roots 4096,16384,65536 are fixed; using them again
is justified only by the new ONE-MEASURE assembly, not a new census or an
independent rediscovery of MB4. All exact arithmetic cases in the original
registration are unchanged.

## Dyadic Product Rigidity And Cross-Scale Potential Limits - 20261109-wheel-2/DG

### A. Most Important Structural Discovery

**Genuine prime-product phases at adjacent dyadic roots can coincide only at one explicitly characterized square-boundary configuration. Nevertheless, distinct phases with a shared prime can reinforce each other on the ENTIRE relevant finite frequency band.** Unique factorization supplies exact rigidity, not the quantitative separation needed for a cancellation estimate.

There is also a stronger, precisely scoped continuation of Analytic MB4: its separate scale-dependent countermodels can be assembled into **ONE fixed signed measure**, consistent across all dyadic scales, with zero mass on every aligned dyadic interval, half-reference density domination, and the exact SHIFT relation. Its prescribed middle-band response still exceeds the RH scale along an infinite subsequence. Thus cross-scale consistency does not repair the density-and-zero-marginal shortcut. This is a NON-PRIME method obstruction, not a counterexample to actual prime arithmetic, the complete wheel, or RH.

| Claim ID | Result | Evidence and scope |
| --- | --- | --- |
| 20261109-wheel-2/DG1 | Exact adjacent-scale normalized-product resonance classification; only the simultaneous pairs (R-1,R+1) and (2R-1,2R+1) can coincide | PAPER_PROOF; genuine-prime structural theorem |
| DG2 | Shared-prime chains with outer relation r=4p+/-1 have strictly positive cross-phase response throughout [sqrt(R),2sqrt(R)]; actual admitted witnesses at R=8 and 64 | PAPER_PROOF plus exact rational FINITE_COMPUTATION; refutes a termwise decorrelation shortcut |
| DG3 | Exact weighted signed-square potential accounting, including all interior and endpoint terms | IDENTITY_ONLY; the specified boundary-only telescope is REFUTED, not all possible potentials |
| DG4 | One fixed globally consistent half-density, dyadic-zero-mass measure retains MB4's oversized moving-band responses on R=4096*4^j | PAPER_PROOF; new global assembly of the credited MB4 local example, NON-PRIME |
| DG5 | Registered exact phase intersections, rational whole-band witnesses, potential algebra, SHIFT endpoints, and separate floating diagnostics | FINITE_COMPUTATION; no inference of an infinite theorem from the sample |

All NEW paper claims are SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. No literature-priority claim is made for unique factorization, polarization, Fourier integrals, or patching disjoint intervals. NEW_VERIFIED_ENDPOINT_GAIN=NONE. The uniform complete-wheel bound, canonical VF, finite A/C and RH remain OPEN.

### B. Current Authoritative Objective

Actual invocation: scheduled 2026-11-09 10:12:01 EST, America/New_York; RUN_ID_UNAVAILABLE. This is the continuation of the registered checkpoint, not another launch. Source and validation refresh through 2026-11-09 15:31 UTC found main unchanged:

```text
MAIN=02f00cee544278ad1bb9022ee76fc5916d459a95
finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1
AGENTS=6695522a45d67fd1e80a7cff1f98d909405036e2
CURRENT_PROOF_CONTRACT=95566e37c8eaeb99ee680660df4f9d2e06ea5038
FINITE_WHEEL_DIRECTIVE=e505f35522b675c6b5b263eac73618d717346973
DYNAMIC_PROTOCOL=e8d913ff9663bb5163eaf0eddca9f76e0508a7ef
```

For every integer R>=2, X_R=R^2-1, y=R-1, preserve the COMPLETE original source:

```text
F_R=sum_(d|P_y) mu(d)*fract(X_R/d),
D_R=X_R*prod_(p<=y)(1-1/p)+pi(y)-1-li(X_R),
Z_R=F_R-D_R=li(X_R)-pi(X_R).
OPEN: exists ONE C>=0, forall integers R>=2, |Z_R|<=C R log R.
```

The reference is principal-value li; its anchor is not silently replaced by Li_2. All virtual d>X_R cancel against their Euler reciprocal terms BEFORE the physical carrier is used. The inspected `finiteWheel_squareFractional_centered_eq_reference_sub_pi` accepts arbitrary real reference L and supplies an equality, not an estimate. The public `VFCanonicalSquareVonKochStatement` remains unchanged; the inspected terminal `riemannHypothesis_of_vfCanonicalSquare` still takes `ClassicalVonKochRHCriterion` explicitly.

| Original source read at main | Blob SHA |
| --- | --- |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/CompleteWheelRootAdmission.lean | a412632c1028d7728cd8d87ee6e5ac365377d338 |
| research/CompleteWheelRootAdmissionAcceptance.lean | d0b22fa38c254a22b38b678e77bb520a70eae1af |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

These are inherited declarations, not this run's new mathematics. [Pinned complete-wheel source](https://github.com/OVVO-Financial/RH_Lean/blob/02f00cee544278ad1bb9022ee76fc5916d459a95/research/CompleteSquareRootWheelFractionalBoundary.lean).

### C. Structural Mechanism Investigated

The immediate handoff is Coordinator `20261109-coordinator-0710-EST/SHIFT`: with dnu=dpi-du/log u,

```text
A_R(t)=integral_[R/2,R) (u/R)^(-it) dnu(u),
B_R(t)=integral_[R,2R] (u/R)^(-it) dnu(u),
B_R(t)=2^(-it)*A_(2R)(t),                 integer R>=8.
```

The upper endpoint 2R is composite at integer roots. At half-integer roots with 2R prime the correction is exactly `2^(-it)`, not zero. SHIFT is reused, not presented as a new theorem.

The attempted mechanism is to use this shared middle interval to organize signed dyadic interactions. Two distinct issues must be separated: exact equality of product phases, and their resolution on a finite band of length about sqrt(R). The former admits an arithmetic theorem; the latter admits actual positive shared-prime cross terms. The registered signed-square potential is then audited without introducing a conjugate into the original product. Finally, DG4 tests whether a SINGLE consistent measure across scales, rather than MB4's separate rootwise measures, would itself supply the missing saving.

### D. Exact Theorem Statements

#### DG1. Normalized-Product Resonance Rigidity

For every integer R>=8 define

```text
E_R={(p,q): p,q prime, R/2<=p<R<=q<2R},
omega_R(p,q)=log((R^2-1)/(pq)).
```

The right endpoint 2R can be written closed without changing this prime set, since 2R is composite. A physical cross-root occurrence is identified by (R,p,q), with least prime p; the root label is retained. Distinct pairs in E_R have distinct products. Products in E_R are below 2R^2, whereas products in E_(2R) are at least 2R^2, so these adjacent-scale physical values are disjoint. An occurrence is admitted under its product wall precisely when pq<=R^2-1. The frequency representation uses the FULL rectangle E_R, including its above-wall part; it must not be silently truncated.

For (p,q) in E_R and (u,v) in E_(2R),

```text
omega_R(p,q)=omega_(2R)(u,v)
  iff (p,q)=(R-1,R+1) and (u,v)=(2R-1,2R+1).
```

The right side includes primality of all four displayed numbers through the membership hypotheses. Thus the intersection of the two phase sets is EMPTY unless those four integers are prime; in that exceptional case it is exactly {0}, with one occurrence in each rectangle. This is an exact all-root theorem, not a statement about how often the four-prime pattern occurs.

As a limited corollary, for the finite pure-prime phase polynomial

```text
H_R(t)=sum_((p,q) in E_R) exp(it*omega_R(p,q)),
lim_(T->infinity) (1/T) integral_0^T H_R(t)*conj(H_(2R)(t)) dt
  = indicator(R-1,R+1,2R-1,2R+1 all prime).
```

Here R is FIXED before T tends to infinity. No useful uniform rate at T=sqrt(R) is claimed. This Hermitian cross-scale diagnostic is not the original nonconjugated wheel integrand.

#### DG2. Actual Shared-Prime Near Resonances

For every integer R>=8 and primes p,q,r satisfying (p,q) in E_R, (q,r) in E_(2R), and r=4p+k with k in {-1,1}, put

```text
Delta=omega_R(p,q)-omega_(2R)(q,r).
```

Then

```text
Delta != 0,
|Delta| <= 1/(R-1),
forall t in [sqrt(R),2sqrt(R)],
  Re(exp(it*omega_R(p,q))*conj(exp(it*omega_(2R)(q,r))))
    =cos(t*Delta)>=1-2R/(R-1)^2>=33/49>1/2.
```

Every nonnegative weighted average of these two phases on this band therefore retains a positive lower bound after normalization by its total weight. No theorem asserting infinitely many primes r=4p+/-1 is assumed. The following two examples are actual primes and BOTH products are physically admitted:

| R | (p,q,r) | (pq,qr) | (X_R,X_(2R)) | exp(Delta) | Certified cosine lower bound on the whole band |
| --- | --- | --- | --- | --- | --- |
| 8 | (5,11,19) | (55,209) | (63,255) | 399/425 | 148385/159201 |
| 64 | (37,67,149) | (2479,9983) | (4095,16383) | 203385/202057 | 40066392689/40292131441 |

This refutes the specific rule that distinct adjacent-scale prime-product phases, or shared-prime chains, have zero or nonpositive termwise cross-phase averages on the relevant band. It does NOT establish the sign of the COMPLETE discrepancy Gram, of A_R*B_R, or of the full source return.

#### DG3. The Registered Potential Does Not Telescope To Endpoints Alone

Fix integer R0>=8 and m>=1; put R_j=2^j R0, a_j=log(1-R_j^(-2)), theta_0=0, theta_(j+1)=a_j-log 2-theta_j. For real t define

```text
z_j=exp(it*theta_j)*A_(R_j)(t),
q_j=Im(z_j^2), d_j=Im((z_(j+1)-z_j)^2).
```

For ANY real weights w_0,...,w_(m-1), the exact identity is

```text
2 sum_(j=0..m-1) w_j Im(exp(it*a_j)*A_(R_j)(t)*B_(R_j)(t))
 =w_0 q_0+w_(m-1) q_m
  +sum_(j=1..m-1)(w_(j-1)+w_j)q_j
  -sum_(j=0..m-1)w_j d_j.                         POT
```

The interior coefficients ADD for the actual nonnegative frequency weights. Alternating the scale weights can cancel them algebraically, but changes the statistic. Both q_j and d_j are signed imaginary squares, not nonnegative energies. POT contains no independently established favorable-sign inequality. The separate SC constant-frequency term A_R(0)B_R(0)/2 is not supplied by a positive-frequency imaginary-part identity and must still be retained.

#### DG4. One Fixed Measure With All Dyadic Dependencies Still Fails The Generic Bound

There exists ONE locally finite, absolutely continuous real signed measure sigma on [2,infinity) with all the following properties. It is fixed before R is queried:

```text
|dsigma| <= (1/2) du/log u;
sigma([4096*2^(k-1),4096*2^k))=0 for every integer k>=0;
B_R^sigma(t)=2^(-it)*A_(2R)^sigma(t) for every integer R>=8 and every real t.
```

In particular dli+dsigma is a positive measure. Define A^sigma,B^sigma by replacing dnu with dsigma in the original transforms, and use the ORIGINAL nonconjugated phase and spline:

```text
M_sigma(R)=(1/pi) integral_(sqrt R)^(2sqrt R)
  b(t/R)*Im(exp(it*log(1-R^(-2)))*A_R^sigma(t)*B_R^sigma(t))/t dt.
```

Here b(w)=1-6w^2+6|w|^3 for |w|<=1/2, b(w)=2(1-|w|)^3 for 1/2<=|w|<=1, and b=0 outside. For EVERY integer j>=0, with S_j=4096*4^j,

```text
M_sigma(S_j) <= - S_j^(3/2)/(32768*log(S_j)^2).
```

Consequently no constant C bounds |M_sigma(R)| by C R log R for all integer R. The new content over `20261109-analytic-2/MB4` is the ONE-MEASURE quantifier and exact consistency at the intermediate roots 2S_j; the local packet and its lower-bound mechanism are credited to MB4 and rechecked below. Sigma is piecewise smooth, NOT asserted globally smooth at the dyadic joins, NOT a prime measure, and NOT a wheel/divisor-inversion model.

### E. Mathematical Proofs

#### DG1: GCD, Integer Multiplicity And Prime Factorization

Put X=R^2-1 and Y=4R^2-1=4X+3. Equality of the phases is equivalent to `X*uv=Y*pq`. Set g=gcd(X,Y)=gcd(X,3), so g is 1 or 3. Coprimality after dividing by g implies `(X/g) divides pq`. Write pq=hX/g. The interval restrictions give

```text
R^2/2 <= pq < 2R^2.
```

If g=1, these bounds imply h is 1 or 2. The product pq is odd, so h cannot be 2. Thus pq=X and the equality gives uv=Y.

If g=3, the same bounds and R>=8 imply 2<=h<=6. The primes p and q are at least 5, so pq is divisible by neither 2 nor 3. This excludes h=2,3,4,6. If h=5, unique factorization forces p=5, q=X/3; but `(R^2-1)/3>2R` for R>=8, contradicting q<2R. Thus g=3 is impossible.

Finally `(R-1)(R+1)=pq` is the product of two primes, while both R-1 and R+1 exceed one. Each must therefore be prime, and the increasing order gives p=R-1,q=R+1. Apply the same argument to Y. The converse follows immediately. Each product has exactly one orientation because the two prime intervals are disjoint. This proves coverage, uniqueness, and the complete resonance classification, including the equality wall.

For the long-interval corollary expand the two FINITE sums. The normalized integral of exp(it*d) tends to zero when d!=0 and equals one when d=0. DG1 counts the latter exactly. This limit exchanges no growing prime population with an integral. It cannot be evaluated at a growing R with T=sqrt(R) without a NEW quantitative estimate.

#### DG2: Shared Factors Cancel, But The Remaining Phase Is Unresolved

Cancel the shared prime q and use r=4p+k:

```text
exp(Delta)=X*r/(Y*p)=1+epsilon,
epsilon=(kX-3p)/(Yp).
```

For k=1 the numerator is positive because X>3p at R>=8; for k=-1 it is negative. Thus Delta is nonzero. Since p>=R/2 and p<R,

```text
|epsilon| <= (R^2+3R)/[(4R^2-1)R/2] <= 1/R.
```

The last elementary inequality holds for R>=8. Integrating 1/(1+s) between 0 and epsilon gives `|log(1+epsilon)|<=|epsilon|/(1-|epsilon|)<=1/(R-1)`. The inequality cos x>=1-x^2/2 now proves the stated whole-band bound. The final inequality is equivalent to `(R-8)(8R-1)>=0`.

The sharper witness bounds use exact epsilon values -26/425 and 1328/202057. The respective rational bounds for |Delta| are 26/399 and 1328/200729. Substituting these into `1-2R*bound^2` gives the table. No numerical logarithm, sampled cosine, or statistical inference certifies these signs.

Conjugation in this calculation is ONLY the correctly stated cross-scale phase comparison. The original signed band still uses A_R B_R without conjugation. The two physical witness products have distinct values and different root labels; the common prime q is an incidence relation, not a historical occurrence spent twice.

#### DG3: Exact Accounting Of The Proposed Potential

The theta recurrence and SHIFT give `z_j z_(j+1)=exp(it*a_j)A_(R_j)B_(R_j)`. The algebraic identity

```text
2 z_j z_(j+1)=z_j^2+z_(j+1)^2-(z_(j+1)-z_j)^2
```

then proves POT by taking imaginary parts and collecting each interior q_j twice with its two respective weights. For w_j=1 there is a full interior sum, not a telescoping difference. The exact constant-chain negative control z_j=1+i has every edge imaginary part 2, every q_j=2 and every d_j=0. Three edges therefore sum to 6, whereas keeping just half the two endpoint q values gives 2. This is an algebraic negative control, not alleged prime data.

A separate fixed smooth power-density diagnostic uses dsigma=u^(-1/4)du. Its transforms satisfy SHIFT but `|A_(2R)(t)|^2=2^(3/2)|A_R(t)|^2`, so SHIFT does not express energy contraction. This elementary diagnostic is not a replacement for DG4, which also retains zero dyadic marginals and reference domination.

#### DG4: Global Assembly And Rechecked Local Lower Bound

Fix S_j=4096*4^j, U_j=sqrt(S_j), L_j=log S_j, ell=log 2, and

```text
c_j=S_j/(4L_j),
n_j=ceil(5U_j*ell/(8pi)), t_j=2pi*n_j/ell.
```

Because U_j>=64 and 2pi/ell<10, `5U_j/4<=t_j<=7U_j/4`. Define sigma to be zero on [2,2048), and on the disjoint successive interval pairs put

```text
dsigma(u)=c_j*cos(t_j*log(S_j/u))*du/u,  S_j/2<=u<S_j;
dsigma(u)=c_j*sin(t_j*log(u/S_j))*du/u,  S_j<=u<2S_j.
```

The next pair starts at S_(j+1)/2=2S_j, so these rules define ONE measure on the whole half-line without overlaps, gaps, or contradictory assignments to a shared middle interval. Values at the endpoints have no measure-theoretic effect. Local finiteness is immediate on compact intervals.

Each half-annulus has zero mass since t_j*ell=2pi*n_j. On both half-annuli `u/log u>=S_j/(2L_j)`, so `c_j/u<=1/(2log u)`. This proves the density domination and positivity of dli+dsigma. The endpoints have no atoms, hence SHIFT holds for this measure at ALL roots where its integrals are defined, in particular every specified integer root. At intermediate roots 2S_j, its left interval is the previous sine packet and its right interval is the NEXT cosine packet; they are not chosen independently after seeing that root.

At a paired root S=S_j let c=c_j, U=U_j, t0=t_j and define

```text
F(w)=integral_0^ell exp(-iws)ds,
G=F(t-t0), H=F(t+t0).
A_S^sigma=c*(conj(G)+conj(H))/2,
B_S^sigma=c*(G-H)/(2i).
```

Consequently

```text
Im(A_S^sigma B_S^sigma)=-c^2*(|G|^2-|H|^2)/4 <=0, t>0.
```

For the sign, F(t-t0) and F(t+t0) have the same numerator 1-exp(-it*ell), and `|t-t0|<=t+t0`; the removable point t=t0 is included by continuity. On the interval |t-t0|<=1, contained in [U,2U], one has `|G|>=ell/2`, `|H|<=1/U<=ell/4`. Thus the negative imaginary part has magnitude at least c^2*ell^2/32 there. Also b(t/S)>=1/2 throughout the band, since 2U/S=2/U<=1/32. If the small original phase a_S=log(1-S^(-2)) is temporarily set to zero, the NONPOSITIVE integrand on the whole band and this width-two interval give

```text
M_sigma,0(S) <= -c^2*ell^2/(64pi U).
```

Restoring the phase costs at most

```text
|M_sigma(S)-M_sigma,0(S)|
 <= |a_S| c^2 ell^2 U/pi
 <= 2c^2 ell^2 U/(pi S^2).
```

Its ratio to the preceding lower magnitude is at most 128/S<=1/2. Therefore `M_sigma(S)<=-c^2 ell^2/(128pi U)`. Substitute c=S/(4log S), ell>1/2 and pi<4 to obtain DG4. Every constant is fixed before j. Dividing its magnitude by S log S leaves `sqrt(S)/(32768 log(S)^3)`, which tends to infinity. The finite diagnostics are not used in this proof.

The pairwise local construction and estimates are MB4's mechanism. The new logical strengthening is that the model is now fixed globally, has shared intervals at every intermediate scale, and satisfies the exact dyadic dependence relation simultaneously. It still lacks the discrete prime atoms and arithmetic divisor inversion required by the genuine source.

### F. Structural Consequence

DG1 rules out every nonboundary exact cross-scale resonance on this genuine prime carrier, even when the rectangles share a prime interval. It is stronger than an unsigned degree bound, but not a lower bound on spectral spacing of the size needed by OPEN-MIDBAND. DG2 proves directly on admitted arithmetic occurrences that the two notions differ: neighboring phases separated on the order of 1/R remain coherent during an observation band of length sqrt(R).

DG3 locates the exact unpaid terms in the registered potential. DG4 rules out the specific rescue that merely requiring one globally consistent centered measure and the full SHIFT chain supplies the missing signed saving. Neither theorem forbids a different potential using additional prime-specific restrictions. No general sieve-parity impossibility or universal no-go for combinatorics is claimed.

### G. Signed And Quantitative Relevance

The new arithmetic rigidity is a structural theorem, not a new bound for the full signed response. The proper transform uses the same actual prime-minus-li measure as Owner FW/CT and Analytic SC/MB. To keep the complete return visible, let n_R count primes in [R/2,R), let E_R^wheel=sum_(prime p in [R/2,R))delta(p-1)/p, and let F_other be the sum of all remaining original first-owner fractional packets. On the SAME closed hyperbola uv<=X_R write I_LL,I_Lnu,I_nuL for the reference and two mixed integrals. Then the exact physical source accounting is

```text
C_rest=F_other-D_R+n_R(n_R+3)/2-X_R*E_R^wheel+I_LL,
Z_R=C_rest+I_Lnu+I_nuL+Q_R,
Q_R=integral_(u in [R/2,R),v in [R,2R],uv<=X_R) dnu(u)dnu(v).
```

The historical n_R(n_R+3)/2 term retains units, prime squares and historical distinct-prime pairs. Virtual compensation occurs before this adapter, not after a norm. DG1-DG2 do not omit any owners, post-wall rectangle atoms, or either linear orientation.

Using the PREVIOUSLY REPORTED SC paper decomposition at T=R, with U=sqrt(R),

```text
Q_R=A_R(0)B_R(0)/2+I_[0,U]+M_R+I_[2U,R]+e_R,
|e_R|<=6144 R/log R,
Z_R=S_rest+M_R+e_R,
S_rest=C_rest+I_Lnu+I_nuL+A_R(0)B_R(0)/2+I_[0,U]+I_[2U,R].
```

These SC and MB error bills retain their inherited PAPER_PROOF / independent-review-pending status; they are NOT newly certified Lean results. MB2 separately gives M_R=J_mid(R)+delta_R with |delta_R|<=40R for its precise weight and band. DG4 does not claim that this prime-specific reference payment applies to its artificial measure.

The full square remains `Z_R^2=S_rest^2+M_R^2+e_R^2+2S_rest*M_R+2S_rest*e_R+2M_R*e_R`. Restoring delta_R likewise restores every cross term. No favorable local cross sign pays this full square. No upper bound is supplied for S_rest, M_R, J_mid or the whole Z_R by the new results. The already Lean-proved root-admission cost remains a paid O(R) PROPER component and is not re-proved here.

### H. Falsification, Novelty And No-Circularity Review

**Exact registered results.** Sieve and independent trial division agreed for all 4,097 integers 0..4096. All 251 registered root cases passed DG1: R=8..256 plus 257 and 1024, inspecting 443,539 pair occurrences across the two scales. The ONLY collision among those roots was R=30, with (29,31) and (59,61), both at their respective closed product boundaries. This also refutes the overstrong claim that ALL cross-scale phases are disjoint. It is the first such root in the tested consecutive domain R>=8, not a statement about larger untested roots.

The two DG2 witnesses passed primality, interval, shared-factor, physical admission and exact rational whole-band checks. Eighteen exact Gaussian-integer weighted potential checks passed; the constant-chain boundary-only negative control failed as predicted. No logarithm was approximated for the DG1 intersections or DG2 signs.

**Separate diagnostics, not certificates.** Twenty-eight actual A/B SHIFT cases used roots 8,12,30,64,257,11/2,13/2 and t=0,1,3,8. Maximum identity residual was below 9.4e-15; Gauss orders 96/144 differed below 5.0e-14. The two half-integer t=0 omissions were exactly one in the discrete arithmetic. Sixteen fixed power-mode checks gave energy ratio 2^(3/2), not contraction. These continuous calculations are binary64 diagnostics only.

The fixed global model was tested on paired AND intermediate roots, so it is not merely a rerun of MB4's isolated packets:

| Root | Role in the ONE measure | M_sigma diagnostic | M_sigma*log(R)^2/R^(3/2) |
| --- | --- | --- | --- |
| 4096 | paired | -61.8395277841 | -0.0163207329 |
| 8192 | intermediate | 2.3133841512 | 0.0002533381 |
| 16384 | paired | -371.0987277235 | -0.0166635124 |
| 32768 | intermediate | 6.9920833210 | 0.0001274281 |
| 65536 | paired | -2295.6200776895 | -0.0168294920 |

No all-scale estimate or sign is inferred for the intermediate roots. Analytic transforms were independently compared with direct 384-point logarithmic quadrature; maximum absolute difference was below 1.7e-11. The six window zero-mass residuals were below 4.0e-14. Frequency integration orders 20/28 differed below 4.6e-13. The paper proof, not these numbers, establishes DG4.

**Novelty audit.** Current repository searches for normalized-prime/dyadic, GCD/square-root endpoints, and cross-scale potential statements found no matching DG1-DG4 declaration. `PrimeFaceProductUniqueness.lean` (24d66c70db26dd284b2e2391cfb703e26b7c3f1f) already supplies ordinary prime-product uniqueness; that is credited, not rediscovered. `DyadicCompressedPacketGram.lean` (9ec545502a4b1c5dae1b0a6030ae8606daec3dcc) concerns the different doubled-cofactor transport and restores both cross orientations, not the present normalized prime-product phases. `SpectralEndpointGramBridge.lean` (be856466f3cca1ed7c5ef5a38789f16524a31b6e) explicitly ASSUMES local separation and coherent/orthogonal controls; it is not an independent supplier here. This is a scoped source/report search, not exhaustive literature novelty certification.

Prior credit: Coordinator SHIFT and MP remain exact identity / scoped mode obstruction; Analytic MB4 supplies DG4's local model; Owner FW and CT retain their physical bridges and paid curvature error; Census CR retains R=9 reinforcement and R=37 overshoot; RA2's centered-step statement and RA3's cumulative bound are now formalized, but the full physical-set classification and RA4's actual-li contraction witness are not additional Lean declarations. DG2's conjugated diagnostic is not substituted for the original nonconjugated phase. The model has no genuine-prime or full-wheel claim. No desired uniform estimate is used as a premise.

### I. Conceptual Interpretation

The arithmetic distinction exposed here is exact resonance versus resolvable separation. Unique factorization and the square endpoint's GCD restrict exact coincidences sharply. A shared prime still couples neighboring scales strongly enough to defeat a termwise orthogonality shortcut at the target bandwidth. The full dyadic dependence of a measure is a further exact constraint, but DG4 shows that it does not by itself force the missing signed saving, even with every aligned marginal zero.

This makes the next structural requirement more precise: a useful potential must exploit something beyond SHIFT, density domination, marginal centering, and exact noncoincidence. Discrete prime-product balance or a genuinely quantitative signed interaction is still needed. Its existence is not established by this report.

### J. Competing Structural Hypotheses

- Continue the genuine-prime signed product-band investigation. DG1 can organize its resonances, but supplies no free power saving at U=sqrt(R).
- Reject boundary-only polarization, universal nonpositive shared-prime cross averages, and the globally-consistent-density-only version of the proposed bound, at their exact stated scopes.
- Preserve potentials using new prime-specific inequalities, longer-range interactions, or retained mixed terms. No theorem here excludes them.
- Preserve Owner CT's proper curved-to-additive transfer and Analytic MB's paid reference terms without identifying their spatial and frequency projections by analogy.
- Do not resume the old root-admission proof or unchanged wheel census. Yesterday's FD allocation results remain valid at their MU-LIFT scope but are not the current task selector.

### K. Specialist Handoffs

**Coordinator:** add DG1 as a genuine arithmetic exact-restriction edge, DG2 as a finite-band sign obstruction, and DG4 as the ONE-MEASURE strengthening of MB4. The registered POT is not an endpoint telescope. No positive endpoint budget or new sufficient RH lemma was obtained; keep OPEN-MIDBAND and the full return open.

**Analytic Type II:** DG4 explicitly reuses and credits MB4, but removes the root-dependent-family qualification by disjoint annular assembly. Intermediate scales share the very same measure. A saving from SHIFT plus centered half-density alone is therefore unavailable. DG1 does not provide a large-sieve spacing hypothesis at sqrt(R); DG2 gives admitted near-resonant shared-prime rows. A prospective quantitative potential must retain these rows and both physical linear responses.

**Owner Payment:** both DG2 witness chains are admitted at BOTH product walls, so their positive cross-phase terms cannot be rejected merely as above-wall rectangle artifacts. This is not a returned-cell or original #915 admission theorem. The shared prime is not a repeated physical occurrence. Preserve FW's historical triangle and CT's continuous corner when adapting any potential.

**Prime Census:** no wider unchanged phase or sign scan is requested. A useful next test needs a NEW quantified proposed near-resonant signed restriction, with weights, common frequency interval and full returned complement specified in advance. Keep R=8/30/64, the zero-log-phase boundary, and the half-integer endpoint correction as regression cases.

**Adversarial Referee:** independently reconstruct DG1's g=1/3 and h=5 cases; DG2's whole-band constants and Hermitian-versus-original distinction; POT's interior coefficients; and DG4's single-measure quantifier, disjoint annuli, density bound, zero masses, phase restoration and NON-PRIME scope. None is preapproved. In particular do not interpret DG4 as a new fixed zeta-zero counterexample or a full-wheel surrogate.

**Lean Verification:** no source or PR action is requested before independent acceptance and an assessment of quantitative usefulness. DG1 is a precise finite-factorization candidate, not an RH-strength estimate. Reuse #1124 rather than create a duplicate root-admission branch. Do not formalize a hypothesis asserting spectral separation or OPEN-MIDBAND and call its conditional wrapper a new bound.

These are asynchronous handoffs published only in the owned report. No other agent was launched, synchronized or rescheduled.

### L. First Independently Missing Theorem

No new independently sufficient smaller lemma for the COMPLETE target was proved. The first retained proper quantitative obligation remains the genuine signed prime-product band:

```text
exists C>=0, forall integer R>=8,
 |sum_(prime R/2<=p<R, prime R<=q<=2R) K_R(pq)| <= C R log R,
K_R(z)=(1/pi) integral_(sqrt R)^(2sqrt R)
       b(t/R)*sin(t*log((R^2-1)/z))/t dt.
```

This is Analytic's J_mid / Coordinator OPEN-MIDBAND after the paid MB2 reference correction, not a renamed NEW result. Neither equivalence nor non-equivalence of this proper statement with RH has been established. Even its proof would leave S_rest. DG1-DG4 identify restrictions and invalid shortcuts, but provide no valid bound for this signed sum or its complete complement.

For the SPECIFIC potential attempt, the missing ingredient is a genuine arithmetic estimate on the FULL joint interior-and-difference expression in POT with the actual scale-dependent weights, not a favorable sign assumed for either family. No claim is made that estimating this entire renamed expression is automatically easier than estimating the original band.

### M. Continuity, Formal Evidence And Resume Capsule

Both required America/New_York dates were retrieved at reporting snapshot `5fe5e114d31c9d7f37548e2097f0c03fa15b1fdc`. Applicable newest results, source scopes, handoffs and resume capsules were read; unrelated embedded programs were not all rerun. Coordinator 00/90 mirrors had identical blobs and were counted once.

| Role | November 9 intake blob and consumed claims | November 8 verified carry-forward blob |
| --- | --- | --- |
| Coordinator | 9e7253329c409aa920d7e1d43e2fab8971bdc93b; FB1-FB2, MP1-MP3, SHIFT and dyadic-potential assignment | 8b640304f6c233a2c4409b9882799de485888a9e; FM's exact non-Mobius scope |
| Owner | cfc6b8f473f7702c6e0759746095f048c1378756; FW and CT1-CT6 | 4e1b83a1e5ff8c134e9ca64404397c70c2b07252; JS finite-packet obstruction |
| Analytic | 0f9b1362677ac9adbcec45225e5d6b172cf84cb9; SC and MB1-MB5 | edecba8785a45cda87c0035d0348695941f1b8ea; EC complete-consumer closure |
| Wheel | dbb85c912cb56a3a1203e1276bbac55d02ab4c93; RA1-RA5 | 60d4cf1b65d4b1b2cc4f13f6c0940c14cb2c50fd; FD1-FD5 allocation work |
| Census | 185b493a7c4bdc4dda79254f63c6541562e1140f; CR1-CR5 | 00f4f9c0d670821a0c9d1da31fd1c4d0afd09142; FR scoped frequency falsifiers |
| Referee | TODAY=PENDING, no present-day report or verdict inferred | 5371324ebbdbd88afb9abf843e83da2ce86b752f; EC accepted with scope, SG separately self-audited |
| Lean | 873cc077a0eafb87a39c1c9c12ff22ad891d7ba7; RA2-RA3 implementation | 5a110685bbe375d8ebff42df7391162914e52cef; exact EC implementation and repair record |

External inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` contains no entry after October 18. Carry forward original EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 for signed-source, prime-root endpoint and unconditional-versus-first-bad safeguards, not their superseded routing or stale PR descriptions.

**Formal evidence actually checked.** #1124 is human-merged at 2026-11-09T12:30:32Z. Its literal proof head `1b80f147dab3c0c2525052b3c6c3f8c447089da1` has 13 successful completed checks. The [targeted log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42600910899/job/129104842737) was read: Lean 4.34.1, two newly emitted modules, standard terminal axioms `[propext, Classical.choice, Quot.sound]`, and live dependency closures 746/772. Both source files were fetched at that tested head and matched current main byte-for-byte. The original [#1122 targeted log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42561949462/job/128980092032) uses synthetic checkout `1e3c182076a6e1a23ef132c41a78b0f26adab507`, not a falsely labeled literal head. Its full-wheel source was fetched at the tested checkout and matched current main. The compiler script blob `eb3d429b14bf66ba2fba22e55b70ca0048f748c6` explicitly sets `-DwarningAsError=true`. This is reused exact-source verification, not a new full-main build or a certification of DG.

Live open/draft PR collection was empty at intake. Recent merge metadata confirms #1118-#1124 at their actual respective heads. The inherited Mertens/OAI result is not transported to the present source by analogy. No local Lean, source edit, branch/PR action, other report edit, merge, auto-merge, workflow trigger, schedule change or agent launch occurred. Direct git transport failed with CONNECT tunnel 403; the connector supplied source and publication access. No missing execution was inferred from a schedule.

**Publication and registration.** The early checkpoint was committed at `2288c2b07d485c2e9bc2e7332859e91b1ce2665e`, blob `d916e5f9018bdacd2ccbd3570dd75d11759bae1c`, and re-fetched byte-for-byte. GitHub's actual commit time is **2026-11-09T15:20:47Z = 10:20:47 EST**; this is the authoritative publication time, correcting the checkpoint's unverified 10:18 preparation label. The disclosed one-measure extension was committed at `7d7f4862c49cc81fd25224c72d4a00590eedb2c3`, blob `bb769e3aab12e11bc0c6a2e8bea726b8ac4750b2`, at 15:24:39Z, and likewise read back before arithmetic execution. Both commits changed ONLY the owned daily report.

The exact executed script follows. Its final SHA-256 is `62bd0fe79c28c73c2038ffa6871132ec5db9a0e117a577b15f952148f803570b`; Python syntax validation passed. The first execution already passed the registered arithmetic, potential, actual SHIFT and assembled-model checks. The final small edit completed the separately registered fixed-power-mode diagnostic; no theorem constant, sample range, or hypothesis was fitted to output. All computation sessions completed.

```text
RUN=20261109-wheel-2; scheduled 10:12:01 EST; one actual invocation.
MAIN=02f00cee544278ad1bb9022ee76fc5916d459a95.
ACK=FINITE_WHEEL_CENTERED_RH_V1.
NEW=DG1 exact arithmetic rigidity; DG2 positive shared-prime phase terms;
    DG3 complete potential accounting; DG4 ONE fixed non-prime stress measure.
EVIDENCE=PAPER_PROOF/SELF_AUDIT, exact finite checks, separate float diagnostics.
REVIEW=INDEPENDENT_REVIEW_PENDING; NOT_FORMALIZED.
PAID_PRIOR=#1122 complete source; #1124 proper root-admission cost;
           SC/CT/FB/MB proper paper estimates at their own scopes.
OPEN=actual J_mid, all complementary signed return, canonical VF, finite A/C, RH.
NO_GO_SCOPE=boundary-only POT, pairwise nonpositive phase averages,
            SHIFT plus fixed centered half-density as a generic band supplier.
DO_NOT_REPEAT=RA census, DG phase scan, MB4 packet tests without a new hypothesis.
BEST_NEXT=prime-specific quantitative control of near-resonant signed products,
          with DG2 rows, constant term and complete complement retained.
NO_GLOBAL_ENDPOINT_GAIN.
```

This synthesis preserves all preceding report bytes and claim IDs. SUBSTANTIVE_PUBLICATION=PENDING until its own immutable commit/readback; a verified receipt will be appended only after success.

### Reproducibility Appendix - DG5

The following is the exact final executed Python script. It uses only the standard library and NumPy. Exact arithmetic and binary64 diagnostics are separated in its JSON output; the universal proofs above do not depend on the diagnostics.

```python
"""Registered DG checks: exact arithmetic plus separately labeled diagnostics.

No finite computation here establishes a uniform analytic estimate.
"""

import cmath
import json
import math
from fractions import Fraction
from functools import lru_cache

import numpy as np
from numpy.polynomial.legendre import leggauss


LIMIT = 4096
ELL = math.log(2)
R0 = 4096
flags = [True] * (LIMIT + 1)
flags[0:2] = [False, False]
for d in range(2, math.isqrt(LIMIT) + 1):
    if flags[d]:
        for n in range(d * d, LIMIT + 1, d):
            flags[n] = False
primes = [n for n, yes in enumerate(flags) if yes]


def trial(n):
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


assert all(flags[n] == trial(n) for n in range(LIMIT + 1))


@lru_cache(None)
def phases(root):
    x = root * root - 1
    pairs = [(p, q) for p in primes if root <= 2 * p < 2 * root
             for q in primes if root <= q < 2 * root]
    result = {Fraction(x, p * q): (p, q) for p, q in pairs}
    assert len(result) == len(pairs)
    return result


roots = list(range(8, 257)) + [257, 1024]
collisions = []
pair_count = 0
for root in roots:
    left, right = phases(root), phases(2 * root)
    pair_count += len(left) + len(right)
    intersection = left.keys() & right.keys()
    expected = all(flags[n] for n in
                   [root - 1, root + 1, 2 * root - 1, 2 * root + 1])
    assert intersection == ({Fraction(1)} if expected else set())
    if intersection:
        collisions.append({"root": root, "left": left[Fraction(1)],
                           "right": right[Fraction(1)]})


certificates = []
for root, p, q, r in [(8, 5, 11, 19), (64, 37, 67, 149)]:
    assert all(trial(n) for n in [p, q, r])
    assert root <= 2 * p < 2 * root <= 2 * q < 4 * root
    assert 2 * root <= r < 4 * root and abs(r - 4 * p) == 1
    x, y = root * root - 1, 4 * root * root - 1
    assert p * q <= x and q * r <= y
    ratio = Fraction(x * r, y * p)
    eps = ratio - 1
    assert eps and abs(eps) <= Fraction(1, root)
    log_upper = abs(eps) / (1 - abs(eps))
    cosine_lower = 1 - 2 * root * log_upper**2
    assert log_upper <= Fraction(1, root - 1)
    assert cosine_lower > Fraction(1, 2)
    certificates.append({
        "root": root, "primes": [p, q, r],
        "products": [p * q, q * r], "endpoints": [x, y],
        "phase_ratio": str(ratio), "epsilon": str(eps),
        "log_abs_upper": str(log_upper),
        "cosine_lower_whole_band": str(cosine_lower),
    })


def gadd(a, b):
    return a[0] + b[0], a[1] + b[1]


def gsub(a, b):
    return a[0] - b[0], a[1] - b[1]


def gmul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


polarization_checks = 0
for m in range(1, 7):
    z = [(j * j - 2, 3 * j + 1) for j in range(m + 1)]
    for weights in [[1] * m, [(-1)**j for j in range(m)],
                    [j + 1 for j in range(m)]]:
        q = [gmul(v, v)[1] for v in z]
        d = [gmul(gsub(z[j + 1], z[j]), gsub(z[j + 1], z[j]))[1]
             for j in range(m)]
        lhs = 2 * sum(weights[j] * gmul(z[j], z[j + 1])[1]
                      for j in range(m))
        rhs = weights[0] * q[0] + weights[-1] * q[-1]
        rhs += sum((weights[j - 1] + weights[j]) * q[j]
                   for j in range(1, m))
        rhs -= sum(weights[j] * d[j] for j in range(m))
        assert lhs == rhs
        polarization_checks += 1
constant_chain = {"edges": 3, "true_sum": 6, "boundary_only": 2}
assert constant_chain["true_sum"] != constant_chain["boundary_only"]


@lru_cache(None)
def quadrature(order):
    return leggauss(order)


def continuous(root, lower, upper, t, order):
    nodes, weights = quadrature(order)
    u = lower + (upper - lower) * (nodes + 1) / 2
    values = np.exp(-1j * t * np.log(u / root)) / np.log(u)
    return (upper - lower) * np.sum(weights * values) / 2


def actual_A(root, t, order):
    discrete = sum(cmath.exp(-1j * t * math.log(p / root))
                   for p in primes if root / 2 <= p < root)
    return discrete - continuous(root, root / 2, root, t, order)


def actual_B(root, t, order):
    discrete = sum(cmath.exp(-1j * t * math.log(p / root))
                   for p in primes if root <= p <= 2 * root)
    return discrete - continuous(root, root, 2 * root, t, order)


shift_error = 0.0
refinement_error = 0.0
half_atoms = []
for root in [8, 12, 30, 64, 257, 5.5, 6.5]:
    for t in [0, 1, 3, 8]:
        phase = cmath.exp(-1j * t * ELL)
        atom = phase if trial(int(2 * root)) else 0
        b = actual_B(root, t, 144)
        a = actual_A(2 * root, t, 144)
        residual = b - phase * a
        shift_error = max(shift_error, abs(residual - atom))
        refinement_error = max(refinement_error,
                               abs(b - actual_B(root, t, 96)))
        if root in [5.5, 6.5] and t == 0:
            half_atoms.append({"root": root, "omitted_atom": residual.real})
assert shift_error < 1e-10 and refinement_error < 1e-10


fixed_mode_error = 0.0
fixed_mode_checks = 0
beta = 0.75
for root in [8, 16, 64, 256]:
    for t in [0, 1, 3, 8]:
        z = complex(beta, -t)
        a = root**beta * (1 - 2**(-z)) / z
        b = root**beta * (2**z - 1) / z
        a_next = (2 * root)**beta * (1 - 2**(-z)) / z
        error = abs(b - cmath.exp(-1j * t * ELL) * a_next)
        fixed_mode_error = max(fixed_mode_error, error)
        assert abs(abs(a_next)**2 / abs(a)**2 - 2**(2 * beta)) < 1e-12
        fixed_mode_checks += 1


def F(t):
    arr = np.asarray(t, dtype=float)
    return ELL * np.exp(-0.5j * arr * ELL) * np.sinc(arr * ELL / (2 * math.pi))


def model_parameters(k):
    pair_root = R0 * 4**(k // 2)
    u = math.sqrt(pair_root)
    n = math.ceil(5 * u * ELL / (8 * math.pi))
    freq = 2 * math.pi * n / ELL
    assert 5 * u / 4 <= freq <= 7 * u / 4
    return pair_root / (4 * math.log(pair_root)), freq


def model_window(k, t):
    c, freq = model_parameters(k)
    g, h = F(t - freq), F(t + freq)
    return c * (g + h) / 2 if k % 2 == 0 else c * (g - h) / (2j)


def model_direct(k, t, order):
    c, freq = model_parameters(k)
    nodes, weights = quadrature(order)
    s = ELL * (nodes + 1) / 2
    density = c * (np.cos(freq * s) if k % 2 == 0 else np.sin(freq * s))
    return ELL * np.sum(weights * density * np.exp(-1j * t * s)) / 2


def spline(w):
    w = np.abs(w)
    return np.where(w <= 0.5, 1 - 6 * w**2 + 6 * w**3,
                    np.where(w <= 1, 2 * (1 - w)**3, 0))


def model_band(k, order):
    root = R0 * 2**k
    u = math.sqrt(root)
    panels = math.ceil(u / 4)
    nodes, weights = quadrature(order)
    total = 0.0
    for j in range(panels):
        lo, hi = u * (1 + j / panels), u * (1 + (j + 1) / panels)
        t = lo + (hi - lo) * (nodes + 1) / 2
        a = np.exp(1j * t * ELL) * model_window(k, t)
        b = model_window(k + 1, t)
        original_phase = np.exp(1j * t * math.log1p(-1 / root**2))
        integrand = spline(t / root) * (original_phase * a * b).imag / t
        total += (hi - lo) * np.sum(weights * integrand) / (2 * math.pi)
    return total


model_rows = []
model_transform_error = 0.0
model_zero_error = 0.0
model_refinement_error = 0.0
for k in range(6):
    c, freq = model_parameters(k)
    model_zero_error = max(model_zero_error, abs(model_window(k, 0)))
    for t in [0, 1, freq - 1, freq, freq + 1]:
        analytic = model_window(k, t)
        direct = model_direct(k, t, 384)
        model_transform_error = max(model_transform_error, abs(analytic - direct))
        assert abs(analytic - direct) < 1e-8 * max(1, c)
    if k <= 4:
        root = R0 * 2**k
        value = model_band(k, 28)
        coarse = model_band(k, 20)
        model_refinement_error = max(model_refinement_error, abs(value - coarse))
        lower = root**1.5 / (32768 * math.log(root)**2)
        if k % 2 == 0:
            assert value < -lower
        model_rows.append({"root": root, "paired_scale": k % 2 == 0,
                           "band_diagnostic": value,
                           "normalized": value * math.log(root)**2 / root**1.5,
                           "paper_lower_bound": lower if k % 2 == 0 else None})


result = {
    "exact": {"prime_checks": LIMIT + 1, "phase_root_cases": len(roots),
              "pair_occurrences_inspected": pair_count,
              "shared_phase_cases": collisions,
              "whole_band_rational_certificates": certificates,
              "polarization_cases": polarization_checks,
              "boundary_only_negative_control": constant_chain},
    "diagnostic_only": {"actual_shift_cases": 28,
                        "actual_shift_max_error": shift_error,
                        "actual_quadrature_refinement_error": refinement_error,
                        "half_integer_atoms": half_atoms,
                        "fixed_power_mode_cases": fixed_mode_checks,
                        "fixed_power_mode_shift_max_error": fixed_mode_error,
                        "fixed_power_mode_energy_ratio": 2**(2 * beta),
                        "fixed_model_rows": model_rows,
                        "model_zero_mass_max_error": model_zero_error,
                        "model_transform_max_error": model_transform_error,
                        "model_band_refinement_error": model_refinement_error},
}
print(json.dumps(result, indent=2, sort_keys=True))
```

### Executed JSON Output - DG5

```json
{
  "diagnostic_only": {
    "actual_quadrature_refinement_error": 4.9547302015829164e-14,
    "actual_shift_cases": 28,
    "actual_shift_max_error": 9.349633632383858e-15,
    "fixed_model_rows": [
      {
        "band_diagnostic": -61.839527784071755,
        "normalized": -0.01632073288136112,
        "paired_scale": true,
        "paper_lower_bound": 0.11563161005586713,
        "root": 4096
      },
      {
        "band_diagnostic": 2.313384151175358,
        "normalized": 0.0002533380755672015,
        "paired_scale": false,
        "paper_lower_bound": null,
        "root": 8192
      },
      {
        "band_diagnostic": -371.09872772349365,
        "normalized": -0.016663512435154272,
        "paired_scale": true,
        "paper_lower_bound": 0.6796306876753007,
        "root": 16384
      },
      {
        "band_diagnostic": 6.992083320970647,
        "normalized": 0.0001274280779979272,
        "paired_scale": false,
        "paper_lower_bound": null,
        "root": 32768
      },
      {
        "band_diagnostic": -2295.6200776895275,
        "normalized": -0.016829491960709674,
        "paired_scale": true,
        "paper_lower_bound": 4.1627379620112155,
        "root": 65536
      }
    ],
    "fixed_power_mode_cases": 16,
    "fixed_power_mode_energy_ratio": 2.8284271247461903,
    "fixed_power_mode_shift_max_error": 1.4210854715202004e-14,
    "half_integer_atoms": [
      {
        "omitted_atom": 1.0,
        "root": 5.5
      },
      {
        "omitted_atom": 1.0,
        "root": 6.5
      }
    ],
    "model_band_refinement_error": 4.547473508864641e-13,
    "model_transform_max_error": 1.6816876859565095e-11,
    "model_zero_mass_max_error": 3.9917279564998405e-14
  },
  "exact": {
    "boundary_only_negative_control": {
      "boundary_only": 2,
      "edges": 3,
      "true_sum": 6
    },
    "pair_occurrences_inspected": 443539,
    "phase_root_cases": 251,
    "polarization_cases": 18,
    "prime_checks": 4097,
    "shared_phase_cases": [
      {
        "left": [
          29,
          31
        ],
        "right": [
          59,
          61
        ],
        "root": 30
      }
    ],
    "whole_band_rational_certificates": [
      {
        "cosine_lower_whole_band": "148385/159201",
        "endpoints": [
          63,
          255
        ],
        "epsilon": "-26/425",
        "log_abs_upper": "26/399",
        "phase_ratio": "399/425",
        "primes": [
          5,
          11,
          19
        ],
        "products": [
          55,
          209
        ],
        "root": 8
      },
      {
        "cosine_lower_whole_band": "40066392689/40292131441",
        "endpoints": [
          4095,
          16383
        ],
        "epsilon": "1328/202057",
        "log_abs_upper": "1328/200729",
        "phase_ratio": "203385/202057",
        "primes": [
          37,
          67,
          149
        ],
        "products": [
          2479,
          9983
        ],
        "root": 64
      }
    ]
  }
}
```

### Prepublication Freshness - 20261109-wheel-2

At 2026-11-09 15:37:36 UTC (10:37:36 EST), main remained `02f00cee544278ad1bb9022ee76fc5916d459a95`; the six available upstream November 9 report blobs were unchanged and Referee remained TODAY=PENDING. The open/draft PR collection was still empty. The own checkpoint/registration blob was unchanged. Final environment: Python 3.12.14, NumPy 2.3.5. The synthesis has all A-M sections and balanced code fences. New claims retain paper/self-audit status; no global estimate is promoted.


### Verified Publication Receipt - 20261109-wheel-2

SUBSTANTIVE_PUBLICATION=VERIFIED. The completed DG synthesis, exact reproducer,
and separated diagnostic output were committed at
`3c20c5b472820185c5f41f4d3c9f6a8a27d2b4ed`, report blob
`4f5f421b702b859b929b2f0f079d79e19db3b13d`, GitHub timestamp
`2026-11-09T15:38:17Z` (2026-11-09 10:38:17 EST).
An immutable readback matched the complete intended contents exactly.
The preceding daily report and both registered checkpoint sections remain
unchanged prefixes. The commit changed ONLY
`research/agent_reports/2026-11-09/30-finite-wheel.md`.

The later source-evidence check also fetched the actual compiler script at
BOTH tested CI checkouts. Each matched main at blob
`eb3d429b14bf66ba2fba22e55b70ca0048f748c6` and explicitly enabled
`-DwarningAsError=true`. The original logs contain their respective
literal-head / synthetic-merge checkout SHAs exactly as reported.

Receipt prepared at 2026-11-09 15:39:38 UTC. Execution is COMPLETE.
DG1-DG4 remain PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING,
DG3's positive content is exact accounting, and DG5 retains its split exact
versus diagnostic grades. No Lean certification of DG, new global endpoint
bound, or proof of RH is claimed. No further research or background process
is running for this invocation.


## Scheduled Reflected-Incidence Checkpoint - 20261109-wheel-3/RF

### A. Structural Question

IN_PROGRESS / PARTIAL. No new verified theorem is asserted at this checkpoint. Investigate whether two distinct cross-root prime products reflected about X=R^2-1 can share a prime ancestor, and whether the surviving shared-factor channel has a uniform cumulative signed cost. This tests a precise one-factor reflection mechanism after Owner CF's terminal two-ancestor obstruction. It does not repeat RA root admission, DG cross-scale near resonance, or BL3's already paid bound for all exactly reflected pairs.

Proof-led candidate, NOT YET VALIDATED: for primes R/2<=p_- ,p_+<R<=q_- ,q_+<2R, with p_-q_-=X-d and p_+q_+=X+d, d>0, a nontrivial common factor may force p_-=p_+=(R+1)/2, d=(R+1)/2, q_-=2R-3 and q_+=2R-1. Test the overstrong universal-coprimality rule as a negative control. A preliminary algebraic prediction is R=37 with (19,71) and (19,73); this is a pre-test prediction, not discovered finite evidence.

### B. Live Authority And Continuity

Actual trigger: scheduled 2026-11-09 18:06:01 EST, America/New_York. Platform RUN_ID_UNAVAILABLE. Current source main e7ffe4e01fd049dfe6f47af86a9984bc0b843576; AGENTS 6695522a45d67fd1e80a7cff1f98d909405036e2; contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038; directive e505f35522b675c6b5b263eac73618d717346973. finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.

The open target is one C>=0 for every integer R>=2: |F_R-D_R|<=C R log R. Complete wheel divisors, virtual Euler compensation, the principal-value-li anchor, both physical mixed terms and all other owners remain. No new global bound is assumed.

All seven roles' November 9 and November 8 reports were retrieved at agent-reports snapshot 0ef342f5019c2e884c3ced6d8d65fd3f1f03fc91; TODAY=PRESENT and YESTERDAY=CARRY_FORWARD. Latest intake includes Coordinator SA, Owner CF, Analytic ZD (new PAPER_PROOF, self-audit), own RA/DG, Census BL, Referee DA and scoped acceptances, and Lean's infrastructure limitation. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no post-October-18 entry; its source and endpoint safeguards remain, not its obsolete routing priorities.

Live PR correction: #1125 has human-merged at 2026-11-09T23:01:09Z, but its literal head 538aa743a3e0de86b5ec44c9b4f159df3f5bd050 still has zero check runs and twelve failed workflow records. Merge is not successful proof verification. No new PROVED_IN_LEAN claim is made from that merge. No open PR was returned at intake.

### C. Registered Tests Before Execution

Exhaustively enumerate the complete prime rectangles for R=8..256 and held-out R=257,549,1024. Preserve exact half-root inequalities, prime-root q=R admission, and the closed product wall. Match actual products by n -> 2X-n, keep the d=0 boundary separately, compute every gcd, and test both directions of the proposed classification and product uniqueness. Check that the unique allowed shared-factor offset lies in D=floor(X/(4 ceil(sqrt R))). Use exact rational squared comparisons for the proposed band upper bound; no sampled sine/log values certify an all-band sign. Independently repeat R=8..80 using trial division and a differently organized product-factor audit. Include once-only matching, omitted-boundary and omitted-exception negative controls. Small complete-wheel direct expansion is limited to R=2,3,8,12,14 to independently verify the original-source adapter under the NEW reflected partition, not to re-credit old wheel computations.

### D-M. Remaining Work

Give a full paper proof or explicit counterexample, identify the exact pure-prime-band consumer and its full complement, check main-source duplication, and report the first remaining arithmetic obstacle without renaming the RH target. All new claims will remain SELF_AUDIT / INDEPENDENT_REVIEW_PENDING unless actually independently verified. Only this owned report will be changed remotely. Publication is PENDING until commit/readback.


## Reflected Prime Products: Exceptional Shared Ancestry And Summable Band Cost - 20261109-wheel-3/RF

### A. Most Important Structural Discovery

**Two distinct genuine cross-root prime products reflected about R^2-1 almost never share a prime factor: there is exactly one possible configuration, not an arbitrary incidence graph.** If both reflected products occur in the original prime rectangle and their gcd exceeds one, they must be

```text
R=2p-1,
n_-=p(4p-5)=R^2-1-p,
n_+=p(4p-3)=R^2-1+p,
with p,4p-5,4p-3 all prime.
```

There is at most one such edge per root, and its integer product vertices are never reused at a different root. The resulting exact-reflection graph on product VALUES is a matching, not a chain capable of transporting a large population. Its signed contribution to the original middle-frequency prime-product band is positive and absolutely summable over ALL integer roots:

```text
0 <= J_shared(R) <= sqrt(R)/(pi*(4*(R-1)^2-1))
                  <= 1/(3*pi*R^(3/2)),            R>=8,
sum_(A<=R<B) J_shared(R) <= 2/(3*pi*sqrt(A-1)),    B>=A>=8.
```

Here pi in the denominator is the circle constant. The result uses unique prime factorization and exact integer endpoints, not a wheel-density or independence hypothesis. The overstrong statement that ALL distinct reflected products are coprime is false: the smallest root in the stated domain is R=37, with 1349=19*71 and 1387=19*73, centered at X=1368.

| Claim | New result | Evidence |
| --- | --- | --- |
| 20261109-wheel-3/RF1 | Complete gcd classification of reflected genuine prime products | PAPER_PROOF / SELF_AUDIT |
| RF2 | Global once-only product matching; exact next-root admission retains the same owner | PAPER_PROOF; restricted allocation obstruction |
| RF3 | Uniform signed bound and absolute summability of the shared-factor band channel, also for arbitrary bounded real band weights | PAPER_PROOF; proper-component inequality |
| RF4 | Registered integer classification, independent trial-factor check, exact original-source algebra and rational band enclosures | FINITE_COMPUTATION |

All new paper claims are INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. The elementary techniques carry no literature-priority claim. **NEW_VERIFIED_GLOBAL_ENDPOINT_GAIN=NONE.** Census BL3 already pays the ENTIRE exactly reflected collar at O(R). RF3 is a stronger bound on a narrower subpopulation of that paid channel, not a solution of its unmatched complement or a new global exponent. The canonical VF estimate, complete-wheel O(R log R), finite A/C and RH remain OPEN.

### B. Current Authoritative Objective

Actual trigger: scheduled 2026-11-09 18:06:01 EST, America/New_York, UTC-05:00. Run label 20261109-wheel-3; platform RUN_ID_UNAVAILABLE. This is the completion of the existing registered checkpoint, not another launch. finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.

Main retrieved at intake is **e7ffe4e01fd049dfe6f47af86a9984bc0b843576**, the human merge of #1125. For integer R>=2, preserve

```text
X=R^2-1, y=R-1, P_y=product_(prime p<=y)p,
F_R=sum_(d|P_y)mu(d)*fract(X/d),
D_R=X*product_(prime p<=y)(1-1/p)+pi(y)-1-li(X),
Z_R=F_R-D_R=li(X)-pi(X).
OPEN: exists ONE C>=0, forall integer R>=2, |Z_R|<=C R log R.
```

The reference is principal-value li. Every virtual d>X is retained until its Euler term cancels. The canonical VF statement is still `VFCanonicalSquareVonKochStatement`; the inspected terminal `riemannHypothesis_of_vfCanonicalSquare` still has the explicit `ClassicalVonKochRHCriterion` argument. No arithmetic estimate or formal classical interface is silently supplied by RF.

| Read source at pinned main | Blob SHA |
| --- | --- |
| AGENTS.md | 6695522a45d67fd1e80a7cff1f98d909405036e2 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_SEVEN_AGENT_FINITE_WHEEL_BOUNDARY_20261108.md | e505f35522b675c6b5b263eac73618d717346973 |
| docs/DYNAMIC_RESEARCH_AGENTS.md | e8d913ff9663bb5163eaf0eddca9f76e0508a7ef |
| research/CompleteSquareRootWheelFractionalBoundary.lean | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| research/CompleteWheelRootAdmission.lean | a412632c1028d7728cd8d87ee6e5ac365377d338 |
| research/VF_MID_DYADIC_PREFIX_OWNER.lean | c499ca7bd7d90fb32f9cd99d652961ea023bed58 |
| research/VF_MID_PHI_OWNER_BRIDGE.lean | 5c81e968179c8b069ff86570002555ba54f8b789 |
| research/DyadicPrimeNearResonance.lean | 0080496ada9c7ce230690ed773ee52df9575c245 |
| research/DyadicPrimeNearResonanceAcceptance.lean | 76522788cefb3201b98e4ccbc419bb2bfca6c059 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

The current `finiteWheelFract`, `finiteWheelSquareDeterministic`, `finiteWheelCenteredAt`, `vfMidPrefixWheelCounting`, `vfMidPrefixWheelDensity`, `dyadicPrimePair`, and `admittedDyadicPrimePair` definitions were read. In particular the prime rectangle uses the exact condition R<=2p, not a rounded-down half-root cutoff. The complete-wheel centered identity has an arbitrary real-reference parameter; it is an equality, not a bound.

### C. Structural Mechanism Investigated

Coordinator SA asks for an actual arithmetic restriction beyond the fixed-wheel counting-path model. Owner CF proves that a different same-endpoint donor cannot retain BOTH ancestors p and q of an upper cross-root product, and leaves one-factor substitutions open. Census BL3 has an actual additive-product reflection n -> 2X-n with a paid small curvature cost, but does not assert that partners preserve an ancestor or even exist.

This run tests that particular one-factor refinement. It does NOT assert that every possible useful substitution must be an exact reflection. It also does not relabel the upper reflected product as an original physical site: n_+>X is part of the FULL Fourier prime rectangle, not the sharp physical count at root R. RF2 states exactly when it becomes physical at the next root and what happens to its owner.

The hypotheses being falsified are: (i) all nonzero reflected prime products are coprime; and (ii) every reflected pair can be realized by changing only one prime factor. Neither is a theorem of the source. RF1 gives the exact replacement, while RF3 quantifies its actual signed contribution.

### D. Exact Theorem Statements

#### RF1. The Complete Shared-Factor Classification

For every integer R>=8 let X=R^2-1 and

```text
E_R={(p,q): p,q prime, R<=2p, p<R, R<=q<2R}.
```

For d>0 and (p_-,q_-),(p_+,q_+) in E_R satisfying p_-q_-=X-d and p_+q_+=X+d,

```text
gcd(X-d,X+d)>1
  iff R is odd,
      p_-=p_+=d=(R+1)/2,
      q_-=2R-3, q_+=2R-1.
```

Primality of all three displayed factors is part of the membership hypotheses. Conversely, whenever R is odd and (R+1)/2,2R-3,2R-1 are prime, those formulas give the unique nonzero shared-factor reflection. Its gcd is exactly (R+1)/2. Hence such a root necessarily has R=1 mod 12. No infinitude or density of that prime triple is asserted.

There is at most one edge per root. The d=0 case is separate: a product in E_R equals X exactly iff p=R-1 and q=R+1 are prime. That original sharp-wall atom is not removed by RF1.

#### RF2. Once-Only Matching And Chronological Scope

Form a graph whose vertices are the INTEGER PRODUCT VALUES occurring in the nonzero shared-factor pairs of RF1, across ALL roots R>=8, and whose edges are those pairs. Each vertex belongs to exactly one edge. In particular there are no paths of two or more edges in this graph. This statement does not forbid paths in a different graph whose vertices are individual primes.

Put h=ceil(sqrt R) and D=floor(X/(4h)). Every exceptional offset d=(R+1)/2 lies in 1<=d<=D. The lower product is admitted at root R. The upper product is not admitted there but satisfies

```text
X<n_+<= (R+1)^2-1.
```

Its least prime factor at the next root is still p=(R+1)/2, exactly the lower product's least prime. Thus this reflection supplies neither a same-root physical donor nor a descent to a lower owner. A matching confined to exact reflections that preserve any prime ancestor can use at most one pair per root; every other exact reflected pair replaces BOTH prime factors.

#### RF3. Original Signed Band And Uniform Accumulation

Let U=sqrt R. For any real measurable eta_R on [U,2U] with |eta_R|<=1 define the original product-phase kernel

```text
k_(R,eta)(n)=(1/pi) integral_U^(2U)
              eta_R(t)*sin(t*log(X/n))/t dt.
```

Let J_shared,eta(R) sum k(X-d)+k(X+d) over exactly the common-factor pairs classified in RF1. The sum is empty or has one term. Then, uniformly in R and in the choice of eta_R,

```text
|J_shared,eta(R)| <= U/[pi*(4*(R-1)^2-1)]
                    <= 1/(3*pi*R^(3/2)).              RF3.1
sum_(A<=R<B)|J_shared,eta(R)|
                    <= 2/(3*pi*sqrt(A-1)),            RF3.2
```

for all integers B>=A>=8. The same tail bound holds for the infinite sum.

For the ACTUAL source take eta_R(t)=b(t/R), where

```text
b(w)=1-6w^2+6|w|^3, |w|<=1/2;
     2(1-|w|)^3,    1/2<=|w|<=1;
     0,            |w|>=1.
```

Then J_shared(R)>=0, and it is strictly positive exactly when the prime triple exists. All phases retain X=R^2-1. This is a real signed pair sum arising from the original NONCONJUGATED product of the two prime transforms, not a Hermitian substitute.

### E. Mathematical Proofs

#### RF1: Factorization Leaves Only One Configuration

All four primes are odd and at least five. The intervals p<R<=q are disjoint, so a shared factor must be either a shared lower prime p or a shared upper prime q; cross-identification is impossible. It divides both products and hence 2X. Being odd and prime, it divides X=(R-1)(R+1), and therefore one of R-1,R+1.

If the common factor is an upper q>=R, it can divide only R+1 and must equal R+1. The relation q(p_-+p_+)=2X forces p_-+p_+=2(R-1). Since both lower primes are <=R-1, both equal R-1. The products are equal to X, contradicting d>0. There are no nonzero shared-UPPER-prime reflections.

If the common factor is a lower p in [R/2,R), divisibility of R-1 forces p=R-1, because (R-1)/p<2. Divisibility of R+1 forces p=(R+1)/2: its positive integer quotient is less than three, and quotient one would put p outside the interval. In the first case R is even, both q values are odd and >=R+1, and their sum is 2(R+1). Again both equal R+1 and d=0, impossible.

In the remaining case p=(R+1)/2 and q_-+q_+=4(R-1). The strict product order gives q_-<q_+. Both are odd and <=2R-1. Thus q_->=2R-3 and q_-<=2R-3, forcing q_-=2R-3 and q_+=2R-1. Substitution gives d=p. Their distinct prime factors imply gcd(n_-,n_+)=p. The converse is direct integer multiplication. Since p is odd, R=1 mod 4. Since neither q is divisible by three, R=1 mod 3, proving the necessary mod-12 condition. This congruence is not used as a prime-distribution estimate.

For d=0, X=(R-1)(R+1) is a product of two primes, with both displayed factors greater than one. Unique factorization forces each of R-1,R+1 to be prime and fixes their interval orientation. This includes the strict versus nonstrict wall convention exactly.

#### RF2: Global Product Values, Not Duplicated Labels

Every exceptional product has least prime factor p=(R+1)/2. If the same integer product occurred in an exceptional pair at another root S, its unique least prime factor would also be (S+1)/2, so S=R. Within that root, n_- and n_+ differ by 2p>0. This proves global vertex disjointness, without identifying distinct physical values merely because they share a prime.

For R>=8, 2ceil(sqrt R)<=R-1. R=8 is immediate; for R>=9 use 2sqrt R+3<=R and ceil(sqrt R)<=sqrt R+1. Therefore d=(R+1)/2<=X/(4h); since d is an integer, d<=D. Also d<R<2R+1, proving n_+<=X+2R+1=(R+1)^2-1. Its two factors are still ordered p<q_+, so its least owner has not changed. These facts do not create an extra occurrence in the root-R physical source.

#### RF3: The Actual Pair Bias Has A Summable Size

If there is no exceptional pair, the result is trivial. Otherwise put

```text
u=d/X=1/[2(R-1)],
a=-log(1-u)>0, c=log(1+u)>0.
```

Then a>c and the two original phases are a and -c. For U<=t<=2U,

```text
0<t*c<t*a<= 2sqrt R/(2R-3)<1.
```

The first upper bound uses -log(1-u)<=u/(1-u). The last follows by squaring, since (2R-3)^2-4R>0 for R>=8. On this whole phase interval, 0<cos s<=1; for example cos s>=1-s^2/2>1/2. Therefore

```text
0<sin(t*a)-sin(t*c)<=t*(a-c),
a-c=-log(1-u^2)<=u^2/(1-u^2).
```

The original phase signs have been retained before taking absolute values. Integrating against any |eta_R|<=1 yields

```text
|k(X-d)+k(X+d)|
 <= (U/pi)*u^2/(1-u^2)
 = U/[pi*(4*(R-1)^2-1)].
```

For the original spline b, its first positive-axis piece decreases from 1 to 1/4 on [0,1/2], and its second is 2(1-w)^3. Since 0<t/R<=2/sqrt R<1, its values are in (0,1] throughout this band. The strict pointwise sign therefore proves positive pair bias, not exact cancellation. Finally

```text
4*(R-1)^2-1-3R^2=R*(R-8)+3>0.
```

This gives RF3.1. Comparison with the decreasing integrand x^(-3/2) gives

```text
sum_(R>=A) R^(-3/2) <= integral_(A-1)^infinity x^(-3/2)dx
                      =2/sqrt(A-1),
```

which proves RF3.2. All constants precede R. There is no fixed/growing-modulus transfer, assumed triple infinitude, or finite-to-infinite extrapolation.

### F. Structural Consequence

The original arithmetic forbids a rich exact-reflection network with shared prime ancestry. It permits only a very specific lower-prime/twin-upper-prime edge, with no repeated product values and no lowering of its physical owner. This is more precise than an unsigned degree bound and directly falsifies the proposed one-factor version of the reflection mechanism.

The useful signed consequence is that this entire shared-factor subchannel is uniformly summable. The theorem says nothing favorable about the signs of all coprime pairs, unmatched products, the centered quadratic, or their interactions with lower owners. It is not a proof that the Coordinator's loop countermodel violates this particular restriction: a synthetic population could satisfy it vacuously. RF supplies a necessary genuine-prime incidence fact, not a sufficient exclusion of every large-area model.

### G. Original Source And Complete Signed Return

The following adapter is credited to Owner FW/CF, Analytic SC/MB and Referee DA. It is restated to fix exactly where RF enters, not counted as new RF mathematics.

Partition every nonunit wheel DIVISOR by its GREATEST prime coordinate p. Writing it as p*e with e|P_(p-1) gives

```text
B_owner(p)=-sum_(e|P_(p-1))mu(e)*fract(X/(p*e))
          =N_p(X)-X*delta(p-1)/p,
F_R=sum_(prime p<R)B_owner(p),
N_p(X)=#{2<=n<=X: leastPrime(n)=p}.
```

The largest prime of the divisor coordinate is NOT being identified with the largest prime of a physical integer. Inclusion-exclusion is what converts it to the physical LEAST-prime owner. All virtual p*e>X cancel with their Euler terms before N_p is used.

For p in [R/2,R), p^3>X. Thus its physical cofactors are one or a prime >=p. If n_R counts these upper owners and E_R^wheel=sum_p delta(p-1)/p, their historical units, squares and distinct pairs contribute exactly n_R(n_R+3)/2, and their remaining physical count is the closed hyperbola on E_R. Let I_-=[R/2,R), I_+=[R,2R], dnu=dpi-dell, dell=du/log u, and H(u,v)=1_(uv<=X). Define

```text
I_LL=integral H dell dell,
I_Lnu=integral H dell dnu,
I_nuL=integral H dnu dell,
Q_sharp=integral H dnu dnu,
C_rest=F_other-D_R+n_R(n_R+3)/2-X*E_R^wheel+I_LL.
Z_R=C_rest+I_Lnu+I_nuL+Q_sharp.                     RETURN1
```

Both mixed orientations remain different. q=R is included when prime. 2R is composite but is retained as a reference endpoint. The products above X occur only in the full rectangle used by the Fourier representation, not in the physical count.

For a self-contained exact frequency return, put

```text
A_R(t)=integral_(I_-) (u/R)^(-it)dnu(u),
B_R(t)=integral_(I_+) (u/R)^(-it)dnu(u),
a_R=log(1-R^(-2)),
W_R(s)=1/2+(1/pi)integral_0^R b(t/R)*sin(ts)/t dt,
Q_smooth=integral W_R(log(X/(uv)))dnu(u)dnu(v),
epsilon_sharp=Q_sharp-Q_smooth.
```

This DEFINES and retains the whole sharp-wall error; no new bound for it is assumed. Finite-variation Fubini, with the removable t=0 value retained, gives

```text
Q_smooth=A_R(0)*B_R(0)/2+I_low+M_mid+I_high,
I_low: 0<=t<=sqrt R; I_high: 2sqrt R<=t<=R,
integrand=b(t/R)*Im(exp(it*a_R)*A_R(t)*B_R(t))/(pi*t).
```

There is NO conjugation. Decompose A=P_--C_- and B=P_+-C_+, where P are the actual prime sums and C the exact Li transforms. Then M_mid=J_prime+delta_ref with

```text
delta_ref=middle-band integral of
  exp(it*a_R)*(-P_-*C_+-C_-*P_++C_-*C_+),
with the same imaginary part, spline and 1/(pi*t).
```

These band-reference terms are not the physical mixed integrals I_Lnu,I_nuL. Partition J_prime into shared reflected pairs, coprime reflected pairs in the collar, unmatched collar occurrences, and far occurrences. The zero-offset band value is zero, but its SHARP wall atom is still present in RETURN1 and epsilon_sharp. RF2 proves that all shared reflected pairs lie inside the collar. Hence exactly

```text
Z_R=T_rest(R)+J_shared(R),
T_rest=C_rest+I_Lnu+I_nuL+A_R(0)*B_R(0)/2
       +I_low+I_high+epsilon_sharp+delta_ref
       +J_reflected_coprime+J_unmatched+J_far.        RETURN2
Z_R^2=T_rest^2+2*T_rest*J_shared+J_shared^2.           RETURN3
```

Every interaction within T_rest remains part of its square; it is not a sum of individual squares. RF3 pays only J_shared and its absolute cumulative magnitude, not the mixed term 2*T_rest*J_shared without a bound on T_rest. The prime-adjunction/root-admission channel RA is distinct; summability here is not a new bound for the entire physical-shell innovation in `finiteWheel_centered_root_return`.

The scalar complete-wheel baseline is unchanged. BL3 already controls the total exact reflected collar at O(R), with its original hypotheses; RF3 is not advertised as a new endpoint improvement over that stronger coverage. Analytic ZD's newly reported O_epsilon(R^(17/12+epsilon)) for M_mid remains PAPER_PROOF / SELF_AUDIT, and is neither assumed nor independently certified by this argument.

### H. Falsification, Novelty And No-Circularity Review

The verified checkpoint commit **5e55580da53959c9422c534601cdc7f2847b645d**, blob **c74b8a6822169f0259a1b29b6f577022ef5d0a75**, registered the theorem, domains and R=37 prediction BEFORE running the arithmetic scripts. Immutable readback matched the original report plus the append exactly.

RF4 checked 252 roots: every R=8..256 and held-outs 257,549,1024. It inspected 107,547 root-labelled prime-product occurrences and 1,909 exact nonzero reflected pairs. Every product map was injective, every reflection used both occurrences once, both directions of RF1 held, all exceptional pairs lay in the collar and next-root physical shell, and no exceptional product value was reused. The only shared-factor roots in this declared domain were:

| R | d=p | q_- | q_+ |
| --- | --- | --- | --- |
| 37 | 19 | 71 | 73 |
| 121 | 61 | 239 | 241 |
| 157 | 79 | 311 | 313 |
| 217 | 109 | 431 | 433 |

The independently implemented trial-factor audit scanned INTEGER VALUES, not the primary program's prime rectangles, for all 73 roots R=8..80. It independently found all 104 reflected pairs in that smaller domain and the sole shared pair at R=37. Thus the first failure of universal coprimality in R>=8 is certified by exhaustive exclusion of 8..36, not guessed from a large scan. This is independent IMPLEMENTATION by this author, not independent Referee acceptance.

The held-outs contain 14,29,163 full reflected pairs and 2,1,3 collar pairs respectively; none is shared. These finite counts are not population asymptotics. The already known BL3 R=20 pair 391=17*23 and 407=11*37 was reused for the NEW gcd test: gcd=1, so the universal one-factor reflection rule fails even in the collar. Its existence and previous signed evaluation are credited to Census, not rediscovered here.

Additional exact controls retained R=18's d=0 wall pair (17,19), genuine prime-root admission, and the original full divisor cubes at R=2,3,8,12,14. The latter checks verify the new partition's adapter, not new wheel theorems. They include virtual terms, all upper-owner historical units/squares/pairs, and all six doubled cross terms in the four-part rational-reference version of RETURN1. The rational reference in that algebra test is explicitly synthetic; it is not a claimed numerical evaluation of Li. At R=14 the actual wheel divisor d=X=195 is not discarded; squareful physical integers remain in complementary owner counts.

One test fixture failed: the first program typed the old R=20 offset as 16, whereas 399-391=8. The fixture was corrected to 8 and the complete program rerun. Its RF1 classification checks had already passed before that unrelated assertion. This failure is recorded rather than described as a mathematical counterexample or a completely clean first run.

After classification, a disclosed proof-led extension evaluated the ACTUAL band at the four exceptional discovery roots using rational intervals. These are not held-outs. The calculation uses integer square-root brackets, the convergent atanh series for log, Machin's pi formula with alternating tails, and the exactly integrated sine polynomial. For R>=16 the whole band has t/R<=1/2, so the actual spline is exactly 1-6(t/R)^2+6(t/R)^3. The omitted sine tail is bounded using 0<=b<=1 before integration. Every interval is strictly positive and strictly below the analytic bound in RF3.1. For example,

```text
267398147149267111990187682 / 10^30
  <= J_shared(37) <=
267398147149267111990187683 / 10^30.
```

No floating-point logarithm, sine, primality guess, or sampled sign certifies the theorem. The all-root result follows from E, separately from all finite tests. Python syntax checks passed; all required computation sessions completed.

Novelty review: searched main for reflected prime products, shared-prime and reflection/gcd statements, examined the current source tree and newly merged DG2 source, and searched the full retrieved current reports for matching formulas. The GitHub search index returned the older 02f00c snapshot for some results; the changed e7ffe4 modules were therefore read directly. No equivalent RF classification was found in that scoped review. This is not an exhaustive literature/repository priority claim. DG1 classifies cross-SCALE equal normalized phases; RF1 classifies same-root ADDITIVE product reflections. BL3 bounds all matched offsets but has no gcd classification. CF addresses genuine masked cofactor banks, not this Fourier pairing. Those results are credited at their own scopes.

Also inspected the source statements and scope of `PrimeBoundaryCollisionQuotientNoGo.lean` (blob 4b024c9355156a7166499e0108f326a752e1fb53) and `PrimeSquareCollisionPhysicalFibreNoGo.lean` (8e9696482b313934c18a8a520f10984c23186e74). Their literal square-hit corrected-weight obstructions concern a different carrier; RF does not evade them by assigning a new physical meaning to a symbolic label. Earlier R=549 BLOCK, fixed-wheel FM, and DG/DA/SA countermodels remain at their stated scopes.

### I. Conceptual Interpretation

Common ancestry and cancellation are distinct. The exact reflection that gives opposite logarithmic-phase signs can almost never preserve a prime ancestor, and its one surviving ancestry pattern gives a SMALL POSITIVE curvature bias. The arithmetic also fixes its chronology: an above-wall partner is a new shell occurrence with the SAME least owner, not a lower-owner payment.

This provides an exact restriction on a specific incidence mechanism. It does not couple all sign changes of the two prime-error paths to lower-owner compensation, and it does not disprove every nonlocal matching, approximate reflection, weighted transport or spectral method. That broader requested coupling remains undiscovered in this execution.

### J. Competing Structural Hypotheses

| Mechanism | Decision and reason |
| --- | --- |
| Every reflected pair is coprime | REFUTED at R=37; replace by RF1 |
| Complete exact reflection by changing only one prime factor | REFUTED in the genuine collar by the credited R=20 pair; RF1/RF2 bound all surviving edges |
| Shared-factor reflection produces a long cross-root payment chain | REFUTED for the explicitly defined product-value graph; its components have two vertices |
| Shared-factor band channel is harmless cumulatively | PROVED ON PAPER with fixed constants in RF3; narrower than the already paid whole matched sector |
| Coprime reflection and unmatched/far terms have sufficient joint compensation | OPEN; RF supplies no estimate for this return |
| A more flexible cross-owner transfer with changed factors and its exact reference defect | Still admissible; must specify the map, capacities and actual signed consumer before new scans |

No campaign change is proposed, and no universal sieve-parity or combinatorial impossibility conclusion is asserted.

### K. Specialist Handoffs

**Coordinator / Proof Architect:** record RF1/RF2 as the exact obstruction to one-factor additive reflection and RF3 as a summable proper-channel consequence. Do not mark the SA loop model excluded, the lower-owner coupling solved, or the complete target improved. This refines the mechanism map, not the global quantitative frontier.

**Owner Payment:** any exact reflected partner retaining one factor is the displayed exceptional pair. Its upper member is outside the root-R physical source and, when admitted at R+1, keeps the same least owner. Thus a useful lower-owner map must alter the geometry or factors and restore its exact reference; CF's common-q mask is not identified with this channel.

**Analytic Type II:** RF3 applies to arbitrary measurable real band weights of modulus at most one, including the original spline. It preserves the true nonconjugated product phase. The shared-factor tail is summable but already lies inside BL3's paid sector; no saving for OPEN-MIDBAND, the zero-density return, or the full source should be inferred. ZD1-ZD4 were consumed as new unreviewed paper work, not as premises here.

**Prime Census Laboratory:** the classification now has a proof and a decisive small falsifier; a larger unchanged scan has no purpose. Useful independent verification is R=37 and the interval certificate, or a NEW precisely specified approximate/cross-owner map with exact admission and reference costs. Preserve R=20's existing credit and R=18's zero-offset atom.

**Adversarial Referee:** check all shared-factor cases, especially the exclusion of a shared upper prime, R odd versus even, strict q<2R, d=0, the global product-value uniqueness rather than prime-label uniqueness, collar inclusion, owner preservation, and the all-band cosine range. Audit RF3's arbitrary signed eta scope separately from positivity for b. No independent acceptance is claimed by the author.

**Lean Verification:** RF1/RF2 are compact possible structural statements, but no new implementation task is requested before independent review and a useful consumer. RF3 is paper analysis, not Lean. First resolve the exact coverage of merged #1125: generic post-merge green checks do not replace its missing dedicated proof/type/axiom execution. Do not implement an assumed bound on T_rest and call that arithmetic progress.

These are asynchronous handoffs in this report only. No agent was launched, rescheduled, or promised background work.

### L. First Independently Missing Theorem

**No new smaller sufficient lemma for the complete RH target was obtained.** For the tested mechanism, the missing step is no longer an unproved rich one-factor reflection matching: RF1/RF2 rule it out. The remaining exact reflected pairs are coprime, while unmatched/far and both physical mixed terms still need genuine arithmetic control or a different joint representation.

The prior optional proper-band question remains precise: does ONE C>=0 satisfy |M_mid(R)|<=C R log R for every integer R>=8, for the exact A_R,B_R,a_R,b in G? ZD reports a strictly weaker proper-band power bound, still awaiting independent review. RF does not prove this question weaker than RH, necessary for the whole source, or a new hypothesis supplied by incidence. A bound for the whole T_rest+J_shared would simply rename the original target and is not proposed as an independent lemma.

The next structural investigation should begin only after a concrete cross-owner or approximate-reflection rule is specified, with its once-only occurrence map and reference defect. The current theorem rules out an exact one-factor shortcut; it does not provide that missing rule.

### M. Continuity, Formal Evidence And Resume Capsule

All seven roles on BOTH November 9 and November 8 were retrieved at report snapshot 0ef342f5019c2e884c3ced6d8d65fd3f1f03fc91. TODAY=PRESENT; YESTERDAY=CARRY_FORWARD. Coordinator mirrors had identical blobs and were counted once. Relevant newest mathematical claims, assignments, counterexamples and verdicts were read; historical embedded programs were not all rerun.

| Role | November 9 intake blob | November 8 carried-forward blob |
| --- | --- | --- |
| Coordinator | 35edd925446bfaf4babab99017ad8019db322915 | 8b640304f6c233a2c4409b9882799de485888a9e |
| Owner | 643e8a004d9d8e0be102b03e2f79bb3b217ae916 | 4e1b83a1e5ff8c134e9ca64404397c70c2b07252 |
| Analytic | d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3 | edecba8785a45cda87c0035d0348695941f1b8ea |
| Wheel | 932fe82483d30c49b6277baeaede629d29445b1e | 60d4cf1b65d4b1b2cc4f13f6c0940c14cb2c50fd |
| Census | 6ad4c84512730dfc1cb7fc79540c248931cb8ddf | 00f4f9c0d670821a0c9d1da31fd1c4d0afd09142 |
| Referee | 01869acbc9d0535fe4791354a0029b8f77981723 | 5371324ebbdbd88afb9abf843e83da2ce86b752f |
| Lean | 4402811bbc7198731f83036f73836ef336c2015a | 5a110685bbe375d8ebff42df7391162914e52cef |

Consumed current claims: Coordinator FB/MP/SA; Owner FW/CT/CF; Analytic SC/MB/ZD; own RA/DG; Census CR/BL; Referee DA and its ACCEPT_WITH_SCOPE decisions for DG1-DG4, BL3 and RA2-RA3; Lean RA implementation and DG2 infrastructure limitation. CF/SA/ZD retain paper self-audit status. Yesterday's Coordinator FM, Owner JS, Analytic EC, Wheel FD, Census FR and Referee SG concern other carriers. EC has since been implemented by #1119; that is not a certification of SG, ZD or RF.

External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry later than October 18. EXT-20261018-PNT-1..3, EXT-20261017-XCOORD-1 and EXT-20261014-5 were consumed for their original signed-source, prime-root endpoint and unconditional-versus-first-bad safeguards, not obsolete task selection. No external claim was upgraded to a new theorem.

GitHub evidence verified in this run:

- #1125 merged at 2026-11-09T23:01:09Z as e7ffe4e01fd049dfe6f47af86a9984bc0b843576. Its old literal PR head 538aa743a3e0de86b5ec44c9b4f159df3f5bd050 still has zero check runs and twelve failed workflow records. The dedicated run 42674337064 has zero jobs. This supersedes the old report's DRAFT/unmerged metadata, not its missing formal evidence.
- The MERGE head has ten successful general checks. The retrieved Hosted Lean job 129500775818 checked out that exact merge and succeeded, but its log contains no DyadicPrimeNearResonance compilation, new theorem types or near-resonance axiom audit. No dedicated DG2 certification is inferred from those generic successes. The checkpoint's PR-head statement remains accurate; its evidence was incomplete about the distinct merge head and is supplemented here.
- #1124's literal head 1b80f147dab3c0c2525052b3c6c3f8c447089da1 has thirteen successful checks. The actual dedicated log, job 129104842737, checks out that head, emits CompleteWheelRootAdmission and its acceptance module, prints live dependency closures 746/772 and standard terminal axioms propext/Classical.choice/Quot.sound for the root-step, cumulative bound and return. This is inherited RA evidence, not RF proof.
- #1122's literal head c53e9cf234500aea2605fd2557e638995f380407 has eleven successful checks; its source definitions and theorem statements were read. This run does not claim a new compilation or a new axiom audit for that source. Recent merged metadata also confirms #1119-#1123. No open/draft PR was returned at intake.

Observed local runtime: Python 3.12.14. No local Lean was run. Direct git access returned CONNECT tunnel HTTP 403, so all authority and publication used the authorized GitHub connector; this did not prevent pinned reads or own-report writes. No Lean, main, proof branch, PR, shared instruction, other report, workflow, permission or schedule was changed.

Reproducibility SHA-256 values:

```text
reflected_incidence_check.py
bc0fb863649fea32cb96db5c1539fc2a5a3ace99d6ef5f1e6f79870d94cd61de
reflected_incidence_audit.py
6aefec2eade5ecd3528c9fe29efa5becf4379dc292e7ea4b89009c4cb0e8cda1
reflected_band_certificate.py
598d6893f336eb646ac93ed44c49e2c157c0366d2c774944aa352e2a211a558b
```

Resume from RF1-RF3, not another unchanged reflected-pair scan. Preserve the R=37 exception, coprime R=20 pair, wall R=18 atom, complete virtual compensation, largest-divisor versus least-physical-owner distinction, and the unpaid RETURN2. The strongest new outcome is a specific incidence/matching restriction with a summable signed subchannel, not global cancellation. Mathematical work is complete at this paper/finite scope. Substantive publication is PENDING until the immutable commit/readback receipt below.


### Prepublication Freshness - 20261109-wheel-3/RF

At 2026-11-09 23:31:42 UTC (18:31:42 EST), main remained e7ffe4e01fd049dfe6f47af86a9984bc0b843576. All six upstream November 9 report blobs and both Coordinator mirrors were unchanged from intake. The owned report was still the verified checkpoint blob c74b8a6822169f0259a1b29b6f577022ef5d0a75. Direct open-PR enumeration returned none. The final report has all thirteen A-M sections, balanced code fences, three byte-exact executable script blocks and their recorded SHA-256 values, complete captured outputs, and an explicit unpaid full return. The independent programs agree on all 104 reflected pairs in their common smaller domain. No further source change or mathematical assumption was introduced.


### Reproducibility Appendix - RF4

Run each Python program below. They use only the standard library and exact integers/rationals. The first two implement different enumeration paths; the third certifies the actual band, not a surrogate.

#### reflected_incidence_check.py

```python
"""Registered RF integer/rational audit. No Lean or numerical Li evaluation."""

from fractions import Fraction as F
from math import gcd, isqrt
import json


def sieve(limit):
    flags = [True] * (limit + 1)
    flags[:2] = [False, False]
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            for n in range(p * p, limit + 1, p):
                flags[n] = False
    return flags


def faces(primes):
    result = [(1, 1)]
    for p in primes:
        result += [(d * p, -mu) for d, mu in result[:]]
    return result


def frac(x):
    return x - x.numerator // x.denominator


def audit_root(r, prime):
    x = r * r - 1
    left = [p for p in range((r + 1) // 2, r) if prime[p]]
    right = [q for q in range(r, 2 * r) if prime[q]]
    products = {}
    for p in left:
        for q in right:
            assert p * q not in products
            products[p * q] = (p, q)
    reflected = []
    used = set()
    for n, pair in sorted(products.items()):
        mate = 2 * x - n
        if n >= x or mate not in products:
            continue
        assert n not in used and mate not in used
        used.update((n, mate))
        d = x - n
        p, q = pair
        pp, qq = products[mate]
        common = gcd(n, mate)
        exceptional = (
            2 * p == r + 1 and pp == p and d == p
            and q == 2 * r - 3 and qq == 2 * r - 1
        )
        assert (common > 1) == exceptional
        if common > 1:
            assert common == p
        reflected.append((d, pair, products[mate], common))
    shared = [row for row in reflected if row[-1] > 1]
    expected = (
        r % 2 == 1 and prime[(r + 1) // 2]
        and prime[2 * r - 3] and prime[2 * r - 1]
    )
    assert len(shared) == int(expected)
    h = isqrt(r)
    h += h * h < r
    collar = x // (4 * h)
    for d, pair, mate, common in shared:
        assert d <= collar
        assert x + d <= (r + 1) ** 2 - 1
        assert pair[0] == mate[0]  # Chronological admission does not lower owner.
        u = F(d, x)
        assert 4 * r * (u / (1 - u)) ** 2 < 1
        assert u * u / (1 - u * u) == F(1, 4 * (r - 1) ** 2 - 1)
    assert 4 * (r - 1) ** 2 - 1 >= 3 * r * r
    if x in products:
        assert products[x] == (r - 1, r + 1)
    return {
        "R": r, "products": len(products), "reflected_pairs": len(reflected),
        "shared": shared, "wall": products.get(x),
        "collar_pairs": sum(d <= collar for d, *_ in reflected),
    }


def original_source_audit(r, prime):
    x = r * r - 1
    ps = [p for p in range(2, r) if prime[p]]
    cube = faces(ps)
    density = sum((F(mu, d) for d, mu in cube), F(0))
    full = sum((mu * frac(F(x, d)) for d, mu in cube), F(0))
    physical = sum((mu * frac(F(x, d)) for d, mu in cube if d <= x), F(0))
    virtual = sum((F(mu * x, d) for d, mu in cube if d > x), F(0))
    survivor = sum(all(n % p for p in ps) for n in range(1, x + 1))
    assert full == physical + virtual
    assert full - x * density == -survivor
    pi_x = sum(prime[:x + 1])
    assert survivor + len(ps) == pi_x + 1
    owners = {}
    for p in ps:
        lower = [ell for ell in ps if ell < p]
        owners[p] = -sum((mu * frac(F(x, p * e)) for e, mu in faces(lower)), F(0))
    assert sum(owners.values(), F(0)) == full
    if r < 8:
        return {"R": r, "full": str(full), "virtual": str(virtual)}
    left = list(range((r + 1) // 2, r))
    right = list(range(r, 2 * r + 1))
    nleft = sum(prime[p] for p in left)
    ew = sum((sum((F(mu, e) for e, mu in faces([ell for ell in ps if ell < p])), F(0)) / p
              for p in left if prime[p]), F(0))
    cross = sum(prime[p] and prime[q] and p * q <= x for p in left for q in right)
    upper = sum((owners[p] for p in left if prime[p]), F(0))
    historical = F(nleft * (nleft + 3), 2)
    assert upper == historical + cross - x * ew
    # Arbitrary rational reference tests the full bilinear algebra, not Li values.
    ll = ln = nl = nn = F(0)
    for p in left:
        for q in right:
            if p * q > x:
                continue
            a, b = F(1, p + 1), F(1, q + 1)
            da, db = int(prime[p]) - a, int(prime[q]) - b
            ll += a * b
            ln += a * db
            nl += da * b
            nn += da * db
    assert ll + ln + nl + nn == cross
    reference = F(17, 3)
    deterministic = x * density + len(ps) - 1 - reference
    z = full - deterministic
    rest = full - upper - deterministic + historical - x * ew + ll
    terms = [rest, ln, nl, nn]
    assert sum(terms) == z == reference - pi_x
    all_cross = sum(a * a for a in terms) + 2 * sum(
        terms[i] * terms[j] for i in range(4) for j in range(i + 1, 4)
    )
    assert z * z == all_cross
    return {"R": r, "full": str(full), "virtual": str(virtual), "return": "PASS"}


def main():
    roots = list(range(8, 257)) + [257, 549, 1024]
    prime = sieve(max(2 * max(roots), 14 ** 2))
    rows = [audit_root(r, prime) for r in roots]
    shared = [row for row in rows if row["shared"]]
    physical_values = []
    for row in shared:
        for d, left, right, _ in row["shared"]:
            assert row["R"] == 2 * left[0] - 1
            physical_values.extend([left[0] * left[1], right[0] * right[1]])
    assert len(physical_values) == len(set(physical_values))
    assert shared[0]["R"] == 37
    assert shared[0]["shared"] == [(19, (19, 71), (19, 73), 19)]
    assert rows[18 - 8]["wall"] == (17, 19)
    assert (8, (17, 23), (11, 37), 1) in [
        (399 - n, (p, q), (pp, qq), gcd(n, nn))
        for p in range(10, 20) for q in range(20, 40)
        for pp in range(10, 20) for qq in range(20, 40)
        if prime[p] and prime[q] and prime[pp] and prime[qq]
        and (n := p * q) < 399 and (nn := pp * qq) + n == 798
    ]
    source = [original_source_audit(r, prime) for r in [2, 3, 8, 12, 14]]
    print(json.dumps({
        "status": "PASS_EXACT", "root_cases": len(rows),
        "product_occurrences": sum(row["products"] for row in rows),
        "reflected_pairs": sum(row["reflected_pairs"] for row in rows),
        "independent_domain_pairs": sum(row["reflected_pairs"] for row in rows if row["R"] <= 80),
        "shared_roots": [{"R": row["R"], "pairs": row["shared"]} for row in shared],
        "held_out": [row for row in rows if row["R"] in [257, 549, 1024]],
        "source_checks": source,
        "global_shared_product_reuse": False,
        "negative_controls": ["universal coprimality false at R=37", "zero offset retained at R=18", "coprime reflected pair at R=20"],
        "uniform_proof": "separate paper proof; not inferred from finite enumeration",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
```

#### reflected_incidence_audit.py

```python
"""Independent trial-factor audit; scans integer products, not prime rectangles."""

from math import gcd, isqrt
import json


def factors(n):
    result = []
    p = 2
    while p * p <= n:
        while n % p == 0:
            result.append(p)
            n //= p
        p += 1
    if n > 1:
        result.append(n)
    return result


def pair_at(n, r):
    fs = factors(n)
    if len(fs) != 2:
        return None
    p, q = fs
    return (p, q) if r <= 2 * p and p < r <= q < 2 * r else None


rows = []
total_pairs = 0
for r in range(8, 81):
    x = r * r - 1
    pairs = []
    # The smaller reflected product is at least ceil(R^2/2).
    for n in range((r * r + 1) // 2, x):
        a, b = pair_at(n, r), pair_at(2 * x - n, r)
        if a is None or b is None:
            continue
        g = gcd(n, 2 * x - n)
        if g > 1:
            assert 2 * g == r + 1
            assert a == (g, 2 * r - 3) and b == (g, 2 * r - 1)
            assert x - n == g
        pairs.append((x - n, a, b, g))
    shared = [p for p in pairs if p[-1] > 1]
    total_pairs += len(pairs)
    assert len(shared) <= 1
    if shared:
        rows.append({"R": r, "pair": shared[0]})
assert rows[0] == {"R": 37, "pair": (19, (19, 71), (19, 73), 19)}
print(json.dumps({"status": "PASS_INDEPENDENT_TRIAL_FACTOR", "roots": 73, "reflected_pairs": total_pairs, "shared": rows}, sort_keys=True))
```

#### reflected_band_certificate.py

```python
"""Exact rational enclosures of the original nonconjugated pair kernel."""

from fractions import Fraction as F
from math import factorial, isqrt
import json


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    xs = [a[i] * b[j] for i in range(2) for j in range(2)]
    return min(xs), max(xs)


def scale(a, b):
    return mul(a, (F(b), F(b)))


def power(a, n):
    out = (F(1), F(1))
    for _ in range(n):
        out = mul(out, a)
    return out


def logarithm_ratio(a, b):
    z = F(a - b, a + b)
    n = 14
    center = 2 * sum((z ** (2 * k + 1) / (2 * k + 1) for k in range(n)), F(0))
    tail = 2 * abs(z) ** (2 * n + 1) / ((2 * n + 1) * (1 - z * z))
    return center - tail, center + tail


def atan_inverse(q, n):
    center = sum((F((-1) ** k, (2 * k + 1) * q ** (2 * k + 1)) for k in range(n)), F(0))
    nxt = F((-1) ** n, (2 * n + 1) * q ** (2 * n + 1))
    return min(center, center + nxt), max(center, center + nxt)


PI = add(scale(atan_inverse(5, 48), 16), scale(atan_inverse(239, 20), -4))
assert 3 < PI[0] < PI[1] < 4


def sqrt_interval(r):
    den = 10 ** 36
    low = isqrt(r * den * den)
    return F(low, den), F(low + 1, den)


def integrated_power(t, exponent):
    return scale(power(t, exponent), F(2 ** exponent - 1, exponent))


def kernel(r, n):
    assert r >= 16
    t = sqrt_interval(r)
    s = logarithm_ratio(r * r - 1, n)
    count = 12
    total = (F(0), F(0))
    for k in range(count):
        e = 2 * k + 1
        moment = add(integrated_power(t, e), scale(integrated_power(t, e + 2), F(-6, r * r)))
        moment = add(moment, scale(integrated_power(t, e + 3), F(6, r ** 3)))
        total = add(total, scale(mul(power(s, e), moment), F((-1) ** k, factorial(e))))
    # b(t/R) lies in [0,1]; Taylor degree 2*count has zero even term.
    e = 2 * count + 1
    smax = max(abs(s[0]), abs(s[1]))
    tail = (2 * t[1] * smax) ** e / (e * factorial(e))
    total = (total[0] - tail, total[1] + tail)
    return mul(total, (1 / PI[1], 1 / PI[0]))


def display_interval(a):
    den = 10 ** 30
    low = (a[0] * den).numerator // (a[0] * den).denominator
    high = -((-a[1] * den).numerator // (-a[1] * den).denominator)
    return {"lower_numerator": low, "upper_numerator": high, "denominator": den}


rows = []
for r in [37, 121, 157, 217]:
    x = r * r - 1
    d = (r + 1) // 2
    pair = add(kernel(r, x - d), kernel(r, x + d))
    lower_upper_bound = sqrt_interval(r)[0] / (PI[1] * (4 * (r - 1) ** 2 - 1))
    assert 0 < pair[0] <= pair[1] < lower_upper_bound
    rows.append({"R": r, "signed_pair": display_interval(pair), "proved_bound_test": "PASS"})
print(json.dumps({"status": "PASS_RATIONAL_BAND_CERTIFICATES", "rows": rows, "uniform_status": "paper proof separate"}, sort_keys=True))
```

#### Executed Outputs

```json
{"global_shared_product_reuse": false, "held_out": [{"R": 257, "collar_pairs": 2, "products": 989, "reflected_pairs": 14, "shared": [], "wall": null}, {"R": 549, "collar_pairs": 1, "products": 3569, "reflected_pairs": 29, "shared": [], "wall": null}, {"R": 1024, "collar_pairs": 3, "products": 10275, "reflected_pairs": 163, "shared": [], "wall": null}], "independent_domain_pairs": 104, "negative_controls": ["universal coprimality false at R=37", "zero offset retained at R=18", "coprime reflected pair at R=20"], "product_occurrences": 107547, "reflected_pairs": 1909, "root_cases": 252, "shared_roots": [{"R": 37, "pairs": [[19, [19, 71], [19, 73], 19]]}, {"R": 121, "pairs": [[61, [61, 239], [61, 241], 61]]}, {"R": 157, "pairs": [[79, [79, 311], [79, 313], 79]]}, {"R": 217, "pairs": [[109, [109, 431], [109, 433], 109]]}], "source_checks": [{"R": 2, "full": "0", "virtual": "0"}, {"R": 3, "full": "0", "virtual": "0"}, {"R": 8, "full": "-3/5", "return": "PASS", "virtual": "-6/5"}, {"R": 12, "full": "-2/7", "return": "PASS", "virtual": "-39/35"}, {"R": 14, "full": "-123/77", "return": "PASS", "virtual": "-19/154"}], "status": "PASS_EXACT", "uniform_proof": "separate paper proof; not inferred from finite enumeration"}
```

```json
{"reflected_pairs": 104, "roots": 73, "shared": [{"R": 37, "pair": [19, [19, 71], [19, 73], 19]}], "status": "PASS_INDEPENDENT_TRIAL_FACTOR"}
```

```json
{"rows": [{"R": 37, "proved_bound_test": "PASS", "signed_pair": {"denominator": 1000000000000000000000000000000, "lower_numerator": 267398147149267111990187682, "upper_numerator": 267398147149267111990187683}}, {"R": 121, "proved_bound_test": "PASS", "signed_pair": {"denominator": 1000000000000000000000000000000, "lower_numerator": 54650745822275010149449916, "upper_numerator": 54650745822275010149449917}}, {"R": 157, "proved_bound_test": "PASS", "signed_pair": {"denominator": 1000000000000000000000000000000, "lower_numerator": 37717271950816635376129400, "upper_numerator": 37717271950816635376129401}}, {"R": 217, "proved_bound_test": "PASS", "signed_pair": {"denominator": 1000000000000000000000000000000, "lower_numerator": 23649433958794853904463119, "upper_numerator": 23649433958794853904463120}}], "status": "PASS_RATIONAL_BAND_CERTIFICATES", "uniform_status": "paper proof separate"}
```
