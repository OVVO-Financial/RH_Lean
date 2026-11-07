# RH | Prime Census Laboratory - 2026-11-06

## Early Research Checkpoint - 20261106-census-1

**PARTIAL / IN_PROGRESS.** No new mathematical result is claimed yet.

Actual trigger: scheduled 2026-11-06 03:11:01 EST (America/New_York,
UTC-05:00); RUN_ID_UNAVAILABLE. This report is the same invocation.
Authority retrieved from 08:11 UTC onward.

### Authority And Continuity

Main: 4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a.
AGENTS: 547dda0d9456e7a4e1165dc72d59da6f70d5c023.
CURRENT_PROOF_CONTRACT: 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c.
deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1,
policy ffd8f1c65cc4da656174956d4e03b48bea46768b.
eta_gate: SEARCH_BROAD; net endpoint gain UNKNOWN.

Canonical objective remains VFCanonicalSquareVonKochStatement:
there exists C>=0 such that every integer R>=2 satisfies
|pi(R^2)-VF_can(R^2)|<=C R log R. It is OPEN.

Reporting snapshot: 829cd934dc291efb742d33c81c7efd4f51ce8cda.
Today's Owner, Analytic and Wheel are present. Coordinator, Referee,
Lean and prior Census are TODAY=PENDING; use their retrieved November 5
reports as YESTERDAY=CARRY_FORWARD. Both Coordinator mirror paths have
the same November 5 blob. External inbox
038018145c0fddb2f6306c0712373adf9cd1ea52 has no newer entry than October 18;
its historical task priorities do not supersede live multi-front policy.

Consumed relevant continuations: Wheel PE1-PE4, Referee-11 through -14,
Coordinator C63-C68, Census J1-J3 and JL1-JL5; today's Owner BT/RZ,
Analytic FP, and Wheel CP results are distinct paper claims, not
automatically independently accepted. No unchanged large census is repeated.

PR #1096 is now human-merged, unlike the prior evening reports.
Its source blob is 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1.
There are no open PRs in the actual repository listing at intake.
Recent accepted changes include #1094's finite Nyman correction,
#1095's fail-closed audit repair, and #1096's finite odd-boundary cancellation.

### Selected Mathematical Question

Route: MU-LIFT, as distinct support after yesterday's CORR4 and JOH.
The explicit requested C66 unused-donor certificate will be independently
checked. The new question is whether allowing ALL three-prime-coordinate
edits removes the fixed-prime-bank obstruction, or merely replaces it with
a genuine matching-capacity obstruction.

Exact original carrier, with closed upper and strict lower endpoints:
U_X={n integer: X/2<n<=X, n odd, mu(n)!=0}, X>=4.
The live sum_moebius_eq_oddSquarefreeUpper identifies its signed sum with M(X).
No free signs, prime density, VF weights, or Hecke occurrence map is used.
The full ordered square is retained.

Define a bipartite graph on the positive/negative members of U_X.
An edge joins n,m exactly when their prime-factor sets have symmetric
difference of size THREE. This permits an actual p<->qr replacement
with a shared coprime cofactor, and any size prime, not only 3,5,13.
Let nu_3(X) be maximum matching cardinality and
T_3(X)=|U_X|-2nu_3(X).

### Preregistered Competing Hypotheses And Tests

H3: T_3(X)=|M(X)| for every integer X>=4. Thus global sign imbalance is
the only obstruction, even with the three-edit restriction.
Rival: some subset has too few opposite-sign arithmetic neighbors,
so T_3(X)>|M(X)|. A single exact matching plus a same-size vertex cover,
or a rigorous Hall witness, rejects H3 at that cutoff.

A second discriminator freezes the previously specified increasing-list
PE1 matching for P9={3,5,7,11,13,17,19,23,29} and the qualified 13c/15c
pairs. Compare the best remaining three-edit matching against a fully
reoptimized matching. This distinguishes insufficient edges from
prematurely committed partner choices. Do not reuse a frozen endpoint.

Development: all integer X=4..512.
Held-out: all integer X=513..2048 and X=4095,8191,16383.
Stop extension at this range; a counterexample triggers certificate
analysis, not an unbounded scan. Record smallest and largest excess,
isolated vertices, connected-component imbalances and exact Hall/cover
certificates. Any data-driven repair is explicitly post-discovery.

Independent methods: Python prime-factor sieve/bitset graph and exact
augmenting paths with cover verification; separately implemented C++
trial-factorization/gcd edge test and independently structured matching.
No Lean execution. Integers only. Code is not yet executed.

Support controls: X=1155,2001,2002,4095 and c=31 at X=465;
C66 at X=16383 with all old endpoints retained and six new pairs.
The original coefficient-level lift bridge applies only at X<B^k.
A small raw ordered-atom reconstruction will check signs, multiplicities
and the full square; no unrestricted recurrence is inferred.

### First Missing Quantitative Step

Even finite H3 survival would not give an all-scale bound on M(X).
A useful MU-LIFT theorem still needs a whole-prefix subcritical estimate
E(B^k)<=G(B)E(B)^r with fixed r<k and subpower G, on a covered power chain.
The present matching experiment tests one proposed structural supplier,
not the canonical theorem.

Publication is claimed only after actual commit/readback. Only this
own report path may change remotely.


## Final Research Synthesis - 20261106-census-1

Same scheduled 2026-11-06 03:11:01 EST invocation as the checkpoint.
Prepared 2026-11-06 03:33 EST, America/New_York (UTC-05:00).
RUN_ID_UNAVAILABLE. Computational verification is complete; publication
requires the separate commit/readback receipt below.

### A. Most Important Mathematical Discovery

**Large-prime escape does not require changing the greatest prime, but
locally valid cancellation choices cannot always be frozen.**

The new finite construction pairs the entire rough-semiprime cohort from
Coordinator C65 with unused negative triples using only THREE changed
prime coordinates, preserving the greatest prime factor. It replaces
C66's five-coordinate construction for that same cohort, rather than
spending the positive endpoints twice. An elementary injection and the
ordinary prime number theorem give an all-sufficiently-large-X paper
statement. The complete remainder is still linear; this is not a new
Mertens exponent.

Separately, **X=145 is the smallest cutoff at which a partial three-edit
matching need not extend to a matching leaving only |M(X)| sites.** The
actual PE1 increasing-list matching for P={3,5,7} leaves precisely
105=3*5*7 and 143=11*13. Their signs cancel, but they differ in five prime
coordinates and cannot be joined by a three-edit edge. Releasing just
73<->77 and replacing it by 105<->77 and 73<->143 gives a perfect matching.
Thus the obstruction is committed neighbor capacity, not missing full-graph
capacity or a failure of genuine Mobius cancellation.

The original preregistered full-graph claim survived: at all 2,048 tested
cutoffs, an exact maximum three-edit matching leaves exactly |M(X)| sites.
Python and an independently implemented C++ reconstruction agree on every
output column. Finite survival remains a CONJECTURE at unrestricted scope.

| Claim ID | Actual result | Evidence classification |
| --- | --- | --- |
| GM1 | T_3(X)=abs(M(X)) on the declared finite domain, with exact matching/cover certificates | FINITE_COMPUTATION |
| GM2 | Universal extension of every partial three-edit matching is false; smallest X=145, explicit repair | REFUTED; exact finite certificate and minimality argument |
| GM3 | Greatest-prime-preserving three-edit escape for the C65 cohort, conditional only on an explicit finite prime-count condition; condition eventually holds by PNT | PAPER_PROOF; SELF_AUDIT, INDEPENDENT_REVIEW_PENDING, NOT_FORMALIZED |
| GM4 | Original source, full ordered-square, R14, C66 and strict-cutoff lift checks | FINITE_COMPUTATION |

Claim prefix: 20261106-census-1/. No new Lean theorem, complete uniform
norm bound, canonical VF estimate or RH proof is asserted.
eta_gate=SEARCH_BROAD; new net endpoint gain=UNKNOWN.

### B. Current Authoritative Objective And Provenance

Repository: OVVO-Financial/RH_Lean. Main was fetched, not inferred:
**4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a**;
tree **48b193cd105e21183b1cfd68b059894c8056f35c**.
Initial authority retrieval: 2026-11-06 08:11 UTC onward.
Initial reporting snapshot: **829cd934dc291efb742d33c81c7efd4f51ce8cda**.

The live canonical target is VFCanonicalSquareVonKochStatement:

```text
exists C>=0, forall integer R>=2:
 |pi(R^2)-VF_can(R^2)| <= C R log R.
```

It remains OPEN. The inspected riemannHypothesis_of_vfCanonicalSquare
also takes ClassicalVonKochRHCriterion explicitly. The existing VF/Li
coordinate bridge is not the actual-prime bound. MU-LIFT has its own
genuine-Mobius consumer; no Mobius-to-VF or Mobius-to-Hecke identification
is invented here.

| Material source, pinned to main above | Blob SHA |
| --- | --- |
| AGENTS.md | 547dda0d9456e7a4e1165dc72d59da6f70d5c023 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| Independent multi-front policy | ffd8f1c65cc4da656174956d4e03b48bea46768b |
| Complete-return contract | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| Persistent research engine | 6c1d1c10e2755017ffe9d7f40df8b9ae7692f23a |
| research/MERTENS_ODD_BOUNDARY_PRIME_ESCAPE_20261105.lean | 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1 |
| research/MERTENS_HEATH_BROWN_SIGNED.lean | af69b4811cf9f523eb7c96fb0ca836b2cdbd1180 |
| research/MERTENS_FINITE_PREFIX_EXTENSION.lean | 131e9af86207a42d4bf6488e3f64c9ce4f97e5df |
| RHLean/Proof/AdaptivePrimeMatching.lean | c2caaace0f4e99ea06107d939119c12fa005bcbc |
| RHLean/Proof/RecursivePrimeReplacement.lean | f15bc14ae94677661f2499707b6d60f1d887fcb7 |
| RHLean/Arithmetic/TopPrimeReplacementIsolation.lean | 950173fc3e5271f3eeed8cc6f7831ca89bb11a90 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1. This is distinct
MU-LIFT support following the previous Census CORR4 and JOH investigations.
No team-wide campaign change or unrelated OAI audit is imposed.

PR #1096 was human-merged at 2026-11-06T05:44:44Z. The actual open-PR
listing was empty. Recent accepted work includes #1094's finite Nyman
correction theorem and #1095's fail-closed audit repair; neither is a
supplier for today's new conjecture.

The actual dedicated #1096 run 42150511056 is SUCCESS at head
ecf701ff2fea1de52e505ee34048a2b3c220f0fc. Job 127672350630's log was
retrieved: warning-fatal exact-type audit, ten actual axiom lists, and
PASS with only propext, Classical.choice, Quot.sound (the static-partner
lemma uses only propext and Quot.sound). Its tested merge commit
7783734bdc9960d3c2483af380759db85e87bc8f has exactly the main tree above.
This verifies the existing finite source infrastructure at merged-tree
scope. It does not certify GM1-GM3. Unchanged compiled source artifacts
were reused by that CI; no fresh local Lean compilation is claimed.

### C. Competing Hypotheses And Preregistration

The early checkpoint, committed as
**419ed2670ca774a2aec600c1ab68dc87fd3df0e2** and exactly read back, fixed:

```text
H3: for every integer X>=4, T_3(X)=|M(X)|.
Rival: genuine arithmetic neighbor shortages force T_3(X)>|M(X)|.
Development: X=4..512.
Held-out: X=513..2048,4095,8191,16383.
```

It also fixed the comparison with the previously specified P9 increasing
matching plus qualified 13c/15c pairs. Neither H3 nor that particular
frozen-stage comparison failed in the declared finite range. No new
cutoff was added and no exponent was fitted.

**Post-discovery tests are explicitly separate.** After seeing that output,
I registered H-EXT, the stronger assertion that EVERY partial three-edit
matching can be retained. The same small domain was used to seek a legal
neighbor-exhaustion witness. It failed at X=145. A later elementary
argument and independent C++ check establish global minimality in X,
not merely minimality for the search heuristic.

GM3 was developed after these results and separately recorded before its
finite tests. It is a proof-driven repair, not a retroactively preregistered
prediction. Its eventual count assertion comes from PNT, not from the
two nonempty finite examples.

### D. Exact Carrier And Independent Methods

Use the original source definition, not a surrogate:

```text
U_X={n in Z: 0<n<=X, n odd, X<2n, mu(n)!=0}, X>=4;
M(X)=sum_(1<=n<=X)mu(n)=sum_(n in U_X)mu(n).
```

The latter is sum_moebius_eq_oddSquarefreeUpper on main. Factor-two
cancellation is reused with its actual endpoints; squareful physical
coefficients are zero, not silently removed from the original raw lift.

On U_X join opposite-sign n,m when

```text
|primeFactors(n) symmetric_difference primeFactors(m)|=3.
nu_3(X)=maximum number of disjoint such edges;
T_3(X)=|U_X|-2nu_3(X).
```

All primes, including large ones, may change. This is an endpoint matching,
not a claim about disjoint intermediate paths. In the upper half no
single-prime edit can connect two sites: their ratio would be at least
three. Three changed factors consequently replace one prime by two, and
change factor depth by one. Arbitrarily high common-cofactor depth is
allowed; fixed-bank results do not settle this graph.

Python uses an exact prime-factor sieve, factor-set bit masks, layered
augmenting paths and a separately verified equal-size vertex cover.
For every graph, every edge is covered, matched endpoints are distinct,
and all matched edges are legal. Matching size equals cover size, giving
a direct upper/lower certificate of optimality. Component signed masses
and isolated vertices are also reconstructed.

C++ independently trial-factors integers, builds edges using
omega(n)+omega(m)-2omega(gcd(n,m))=3, and uses degree-ordered recursive
augmenting paths. It separately reconstructs covers, components and
the frozen residual. Its entire 2,048-row output is byte-identical to
Python's. The implementations share mathematical definitions and cutoffs,
not a factor table, edge array or matching. This is independent
implementation verification by the same researcher, not independent
Referee acceptance of an all-scale claim.

All acceptance decisions are integer or exact combinatorial comparisons.
No floating-point primality, approximate roots, randomized signs or
uncertified numerical inequalities are used. The source code uses
integer squares for every fractional-root band boundary.

### E. Executed Results

Exactly **2,048 cutoffs** were tested: all 2,045 integers 4..2048 plus
4095,8191,16383. There were zero H3 violations, zero gaps between the
component-imbalance bound and the matching optimum, and zero penalties
for the SPECIFIED P9/13-15 frozen matching.

| X | Population | Positive | Negative | Three-edit edges | Maximum matching | T_3 | M(X) | P9/13-15 fixed pairs |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 145 | 30 | 15 | 15 | 224 | 15 | 0 | 0 | 5 |
| 1155 | 235 | 115 | 120 | 11435 | 115 | 5 | -5 | 86 |
| 2001 | 408 | 206 | 202 | 32408 | 202 | 4 | 4 | 138 |
| 2002 | 407 | 206 | 201 | 32346 | 201 | 5 | 5 | 137 |
| 2048 | 415 | 211 | 204 | 33590 | 204 | 7 | 7 | 139 |
| 4095 | 831 | 406 | 425 | 121776 | 406 | 19 | -19 | 262 |
| 8191 | 1660 | 841 | 819 | 449751 | 819 | 22 | 22 | 482 |
| 16383 | 3320 | 1644 | 1676 | 1634628 | 1644 | 32 | -32 | 912 |

All selected large fixtures have no isolated vertex in the FULL graph.
The finite finding is stronger than merely locating a few negative pairs,
but it does not provide a bound on the remaining |M(X)| itself.

Observed environment: Linux 6.18.57 x86_64; Python **3.12.14**;
g++ 13.3.0, -std=c++17 -O2 -Wall -Wextra -pedantic. The actual Python
version differs from the generic runtime description and is reported as
observed. Python census elapsed 17.908 seconds; independent C++ census
4.17518 seconds; raw-return/stress script 19.151 seconds. These are measured
process times, not estimates of total invocation or future cost.

### F. Exact Smallest Extension Counterexample

At X=145, use the valid finite PE1 pool P={3,5,7}, with large partner
factor q>7. Its increasing lists give these 14 genuine pairs:

```text
73:77   79:85   83:87   89:91   97:93   101:95   103:111
107:115 109:119 113:123 127:129 131:133 137:141 139:145
```

The left entries are ALL 14 primes in (145/2,145]. The right entries
are exactly the admissible s*q semiprimes for s in P, q>7. Thus this is
not an artificial choice of signs or an invalid PE1 population. The
unmatched sites are exactly

```text
105=3*5*7, mu(105)=-1;
143=11*13, mu(143)=+1;
M(145)=0.
```

Their symmetric difference has size five, so the residual graph has
no edge. Its empty cover certifies zero further three-edit matches.
All 14 possible three-edit neighbors of 105 were used by the displayed
prime/semiprime stage. The universal retention claim H-EXT is false.

An explicit alternating path repairs it:

```text
105 -- 77 == 73 -- 143.
```

The middle pair is the previously selected mate. Delete 73<->77;
insert 105<->77 and 73<->143; leave the other 13 pairs unchanged.
Every new edge changes three prime factors, and no final occurrence is
used twice. The resulting 15 pairs cover all of U_145.

**Minimality among ALL partial matchings, not just the search rule.** For
4<=X<105 the carrier contains only primes and distinct semiprimes, so
its graph is complete bipartite; every partial matching extends. For
105<=X<145 the only possible additional negative site is 105; no
positive four-factor site is possible below 1155. Exact arithmetic at
each of these 40 cutoffs verifies that the number of top primes is at
least the number of positive semiprimes. After any k matched pairs,
at least P-k top primes remain and only S-k positive sites remain, with
P-k>=S-k. Every remaining positive site is adjacent to every remaining
top prime, so extension is always possible. Both programs independently
verify the required counts and factor classifications at all 141 lower
cutoffs 4..144.

This does not refute the PE1 residual theorem, whose conclusion is exactly
preserved, nor H3, nor the P9 comparison actually preregistered. It refutes
the stronger assertion that ANY such partial matching can be irrevocably
retained while achieving the global three-edit optimum.

### G. Hidden Variables And Complete Signed Square

The missing variable is **remaining partner capacity shared across factor
depths**. A top prime can use any semiprime in the upper half; a triple
can use only semiprimes sharing a prime (until deeper populations appear).
At 145, the flexible prime population consumes all of the constrained
triple's neighbors. This is an arithmetic Hall deficit created by the
chosen partial matching. It is not diagnosed by separate endpoint signs.

There is also a useful exact sign-reversal diagnostic. Let C be the
UNORDERED off-diagonal sum on the indicated physical residual, so that
M(X)^2=D+2C, with D equal to its cardinality. At X=16383:

| Complete represented residual | D | C | Signed mass | D+2C |
| --- | ---: | ---: | ---: | ---: |
| Original U_X | 3320 | -1148 | -32 | 1024 |
| After P9 and qualified 13/15 | 1496 | -236 | -32 | 1024 |
| After the new GM3 packet instead of C66 | 1484 | -230 | -32 | 1024 |
| After a maximum unrestricted three-edit matching | 32 | 496 | -32 | 1024 |

The off-diagonal changes sign while the COMPLETE square stays unchanged.
No negative credit may be counted again after removing its paired sites.
This is the genuine Mobius ordered-square reconstruction, not the original
clipped #915 zero-target NNS statistic and not a mean-centered covariance.

### H. New Greatest-Prime-Preserving Repair: Proof

Write J_X={p prime: (4/5)sqrt(X)<p<=(9/10)sqrt(X)}, sorted
p_1<...<p_m, and define

```text
K_X={r prime: r>13, (1/4)sqrt(X)<r<=(9/25)sqrt(X)},
r_1<...<r_l.
```

**Finite theorem GM3.** Suppose every p in J_X exceeds 13 and
l>=m-1. Let the earlier PE1 pool be any finite odd-prime set whose primes
are at most (4/5)sqrt(X). Preserve its chosen endpoints and every
qualified R14 pair. Then the entire C65 cohort

```text
V_X={p_i*p_j: 1<=i<j<=m}
```

has the following disjoint, unused, sign-reversing matching:

```text
p_i*p_j <-> 3*r_i*p_j,  i<j.                         (GM3a)
```

Proof of admission:

```text
16X/25 < p_i*p_j <= 81X/100;
3X/5 < 3*r_i*p_j <= 243X/250 < X.
```

Both endpoints are strictly above X/2 and at most X. The three prime
factors 3,r_i,p_j are distinct; their ranges separate r_i from J_X.
The signs are +1 and -1. Both greatest prime factors equal p_j, since
i<j and r_i<p_j. Exactly the coordinates {p_i,3,r_i} change.

The donors are injective: their greatest prime identifies p_j and their
unique middle prime r_i identifies i. Distinct pairs therefore never
reuse a physical endpoint. Sources have depth two and donors depth three,
so the two endpoint populations are disjoint.

Neither endpoint was consumed by factor two, since both are odd upper-half
sites. Sources have both primes greater than every PE1 pool prime, so
they are not PE1 semiprime partners; donors are not prime or semiprime.
Neither source nor donor is divisible by 13 or by 15, because the varying
primes exceed 13 and the donor's only small prime is 3. Thus neither can
be an R14 endpoint. This proves full once-only admission, uniformly over
the allowed earlier PE1 choices. It does NOT allow retaining C66's pairs
on the SAME source cohort as well.

For the independently established PNT input, fixed macroscopic windows give

```text
|J_X| ~ (1/5) sqrt(X)/log(X),
|K_X| ~ (11/50) sqrt(X)/log(X),
|K_X|/|J_X| -> 11/10 > 1.
```

Therefore all finite hypotheses hold for every sufficiently large X.
No effective numerical threshold is asserted. The only external analytic
input is pi(x)~x/log x, verified at
[NIST DLMF 27.2.3](https://dlmf.nist.gov/27.2.E3); the new conclusion is
derived from it, not stated in that source. No short-interval PNT,
growing-modulus estimate, independence or RH premise is used.

Consequently GM3 removes 2*binom(m,2) sites, with
binom(m,2)~X/(50 log(X)^2), exactly as C66's cohort size. It improves
the permitted edit geometry and preserves the greatest prime; it does
NOT improve the number of removed sites or the remainder exponent.

At X=16383, J={103,107,109,113}, K={37,41,43}. The six new pairs are:

```text
11021 <-> 11877     11227 <-> 12099     11639 <-> 12543
11663 <-> 13407     12091 <-> 13899     12317 <-> 14577
```

For example, 103*107 <-> 3*37*107 preserves greatest prime 107.
The original remainder size 1496 decreases to 1484, with signed sum
still -32. At X=8191 the single pair is 73*79 <-> 3*23*79,
or 5767<->5451. Python and independent C++ checks agree.
Across the original tested cutoffs, 1265 satisfy the finite selection
conditions, but only TWO have a nonempty cohort, totaling SEVEN pairs.
Empty tests are not counted as substantive large-cohort evidence.

### I. Precise Conjecture And First Missing Theorem

**CONJECTURE GM1-infinite:** for EVERY integer X>=4 the graph in D
admits a matching of size min(|U_X^+|,|U_X^-|), equivalently T_3=|M(X)|.
There is no arbitrary mask, fixed prime bank or requirement to retain
previous mates. The checked domain and strongest attempted tests are
exactly C/E/F above. GM2 refutes one strengthening, not this conjecture.

A proof would require genuine simultaneous neighbor-capacity control
across factor depths, not merely individual partner existence or PNT
counts for a single cohort. By itself, even the unrestricted conjecture
does not bound |M(X)|: the certified residual would still be precisely
the unknown target amplitude. Do not present Hall's equivalent criterion
as an independently paid arithmetic estimate.

The first missing quantitative MU-LIFT input remains a whole-prefix bound,
on an unbounded covered chain B_(j+1)=B_j^k, with fixed k>=2 and 1<=r<k:

```text
E(B_j^k) <= G_j E(B_j)^r,
E(B)=max_(1<=n<B) |M(n)|/sqrt(n),
G_j>=1, log(G_j)/log(B_j) -> 0.
```

No part of today's work proves that recurrence or its equivalent signed
window estimate. Endpoint-only checks, static mates, constant-density
removals and a finite small residual do not supply full-prefix uniformity.

### J. Relationship To The Proof Objective And Original Lift

The original heathBrownLift is a finite signed convolution, with
mobiusPrefix(B-1), and is coefficient-exact only below B^k. Actual raw
occurrences retain

```text
(j,v,a_1,...,a_j,b_1,...,b_(j-1)),
1<=j<=k; 1<=v<=binom(k,j); 1<=a_i<B; b_l>=1;
n=product(a_i)*product(b_l)<=X<B^k;
sign=(-1)^(j-1)*product mu(a_i).
```

Zero seed coefficients may be omitted; squareful product fibers and
distinct ordered/binomial copies remain. The current formal source
bridge is coefficient-level; the explicit raw matching here is an
executed finite construction, not an assertion that #1096 formalized it.

The verifier first cancels opposite atoms inside each physical n-fiber,
then uses the original factor-two matching, then the actual three-edit
matching on the surviving physical representatives. Every atom is used
at most once. On the FULL ordered square, the involution flips the first
nonfixed coordinate, or the second if the first is fixed. Both mixed
orientations, diagonal and all cross-family terms are retained.

| B | k | X=B^k-1 | Raw atoms | Ordered pairs checked | Final fixed atoms | M(X)^2 |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 2 | 8 | 22 | 484 | 2 | 4 |
| 3 | 3 | 26 | 429 | 184041 | 1 | 1 |
| 4 | 3 | 63 | 1867 | 3485689 | 1 | 1 |
| 3 | 4 | 80 | 9236 | 85303696 | 4 | 16 |

An independently structured divisor-convolution recursion also reproduces
every coefficient on these four carriers. In total, 11,554 raw atoms and
88,973,910 ordered pairs were explicitly checked. This is finite source
verification, not a new all-scale occurrence theorem or energy estimate.

For GM3's packet, if v=|V_X| and Z is the complete signed final remainder,

```text
M(X)=v-v+Z;
M(X)^2=v^2+v^2+Z^2-2v^2+2vZ-2vZ=Z^2.
```

The complete source remains unchanged. In particular, the known linear
absolute remainder after the old stages stays linear after removing this
O(X/log^2 X) cohort. No fixed power margin survives a complete return
because none has been established. Both endpoints are composite in the
native VF carrier and have positive VF seat weights, so this unweighted
Mobius cancellation cannot be transferred there by the identity map.

### K. Falsification, Independence And Uncertainty Audit

The preregistered rival Hall obstruction was NOT observed in the full
graph. It is not relabeled as supported. The new counterexample concerns
extension of a selected partial matching and explicitly changes the
hypothesis. The separate P9 comparison survives all tested cutoffs.

The requested Coordinator C66 certificate was independently reconstructed:

```text
11021:8205 11227:8355 11639:8445
11663:8535 12091:8565 12317:8655
```

These six original five-edit pairs are valid and unused at X=16383;
1496->1484 sites, signed mass -32. GM3 is an alternative improvement of
their edit geometry, not a correction claiming those pairs were invalid.

R14 also passes: 1001<->1155 is present at X=1155 and 2001, absent at
2002; the seven X=4095 pairs agree with direct source enumeration.
At X=465 the forbidden low-depth cofactor c=31 would reuse 403, already
paired with 383 by P9. The exact coprime-squarefree count Q_390(4095)=961
agrees with the separately expanded double-divisor inversion. These are
independent requested checks, not claimed rediscoveries.

All central finite claims have exact witnesses and independent arithmetic
implementations. The larger raw tensor check is one implementation plus
a separately structured coefficient recursion, NOT two full independent
tensor enumerations. PNT is an established external input; GM3's new paper
proof awaits a separate Referee. Two programs do not establish an
all-scale theorem or independent mathematical acceptance.

No Lean ran locally. No new compiler certification, finite-to-infinite
extrapolation, fitted exponent, probabilistic primality, or numerical
precision claim is made. The finite maximum is not an asymptotic constant.

Novelty is scoped to the inspected original matching/replacement modules
and the retrieved two-day handoffs. The fixed-bank saturation result,
generic augmenting-path principle, PNT and coefficient compression are
prior mathematics. The specific greatest-prime-preserving band injection
and X=145 source-qualified extension failure are new in this inspected
continuation; no exhaustive literature-priority claim is made.

### L. Continuity And Specialist Handoffs

Relevant result, correction and resume sections were read from all seven
roles for November 5, and every available November 6 role. Executable
appendices were retrieved but unrelated old computations were not rerun.

| Role | November 5 report blob | November 6 report blob at intake |
| --- | --- | --- |
| Coordinator, identical 00/90 mirrors | be661bb2ed2830fc4aeddf14713455e550d982cc | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |
| Owner | 39665b5b28fc48378519ab9d56cee8df4d3e2681 | a86a79671728b3ddfc3fdc4e4e0a7f509e1ffaf9 |
| Analytic | 9490aa2eecafcd19d8007043cc5f978fe421a7c9 | 8ad0bdd80168555773271bbc70cda5c78746a4b4 |
| Wheel | afc85d800c47f82f2db634591a7798005cb668de | d7bf40e297ed87f0899f759fa7aab7f577e134ed |
| Census | 24fcd6a631eca9ae44238d927215f49e1d8a174f | No earlier run present |
| Referee | 789ed87021fe98963c244a8d0c9075638e76be43 | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |
| Lean | 5e0ecdd8f08c2e19b4614f00c1a5657f58722344 | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |

The external inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 was read.
Its newest October 18 entry concerns a different PNT/cofactor source;
its obsolete compulsory routing is superseded, and none of its scalar
identities is used as today's norm estimate. Historical VF/NNS guards
are retained; no new external entry was assumed.

**Proof Architect:** consume GM2 as the smallest exact partner-reservation
falsifier, GM3 as a refinement of C66, and GM1 only at finite scope. The
C66 support request is complete. C63-C65's small-bank restrictions are
not refuted: GM3 explicitly changes a prime larger than their bank cutoff.
No change of authorized campaign is requested.

**Owner Payment:** GM3 preserves greatest-prime ancestry on this Mobius
carrier, but both endpoints are positive-weight composites on VF. Any
cross-route payment needs a separate signed-weight/chronology map. Keep
today's SAT BT/RZ and yesterday's JOH/VF continuations distinct.

**Analytic Type II:** exact finite full-graph cancellation provides no
amplitude estimate. A useful new supplier must bound the unmatched signed
source or complete recurrence, not infer independence from its neighbor
graph. Today's frequency FP conclusions are not imported into these sums.

**Finite Wheel:** GM3 provides a concrete large-prime p->3r replacement
that preserves the greatest prime and avoids every old PE1/R14 endpoint.
For a growing-depth extension, prioritize simultaneous capacity and
reserved donors. The X=145 pattern must survive any irreversible-stage
claim. Preserve the due FINITE-AC rotation; this handoff does not launch it.

**Adversarial Referee:** audit GM2's minimality and the exact finite GM3
hypotheses, the disjoint donor ranges, the 11/10 PNT count margin, and
the explicit exclusion of retaining C66 simultaneously. GM3 remains
SELF_AUDIT pending that review. No claim about the canonical first-bad
predicate is made.

**Lean Verification:** no unreviewed conjecture should be formalized as
a supplier. After independent acceptance, GM2 is a small exact regression
and GM3's finite injection is a potential source lemma. The all-large-X
PNT consequence and the unrestricted H3 assertion are different obligations;
no new branch or PR was created or requested to bypass review.

### M. Ranked Experimental Hypothesis Portfolio

| Rank | Hypothesis / evidence | Counterevidence and next ingredient | Disposition |
| ---: | --- | --- | --- |
| 1 | GM3's explicit greatest-prime-preserving donor injection; seven nonempty finite pairs and full elementary paper proof | Only depth-two source cohort; full remainder stays linear. Need a genuine higher-depth, simultaneously disjoint extension with a quantitative consumer | Continue at proper-packet scope; review pending |
| 2 | H3: full three-edit graph leaves only abs(M(X)) | Survives all 2,048 cutoffs; all-scale factor-depth Hall control is unproved and would still not estimate the Mertens amplitude | CONJECTURE; no larger scan without a new mechanism |
| 3 | Every partial three-edit matching can be frozen without loss | Smallest X=145 exact counterexample; an alternating reassignment repairs it | REFUTED; reject the universal supplier |
| 4 | Specified P9 plus qualified 13/15 mates may be retained in an optimal three-edit completion | Finite survival only; X=145 refutes an arbitrary-pool/arbitrary-choice upgrade | CONJECTURE at unbounded scope; distinguish from rank 3 |
| 5 | Repeated fixed-bank or low-depth-only removals yield a subcritical absolute certificate | Existing C64/C65 and Referee-13 obstructions remain; no new uniform error control | Reject those finishes at their stated scope, not MU-LIFT |

### N. Next-Run Resume Capsule

```text
RUN: 20261106-census-1; scheduled 03:11:01 EST; RUN_ID_UNAVAILABLE.
MAIN: 4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a.
SOURCE: odd-boundary blob 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1;
  lift af69b4811cf9f523eb7c96fb0ca836b2cdbd1180.
CHECKPOINT: 419ed2670ca774a2aec600c1ab68dc87fd3df0e2; exact readback PASS.
ROUTE: MU-LIFT, true odd squarefree upper boundary, original mu and weight 1.
GM1: every X=4..2048 plus 4095,8191,16383 has T3=|M(X)|;
  2048 exact matching/cover certificates, independent C++ table identical.
GM2: smallest nonextendible partial matching at X=145, PE1 P={3,5,7};
  residual {105,143}; repair 105--77==73--143; M=0 unchanged.
GM3: J=(.8,.9]sqrt X, K=(.25,.36]sqrt X, K primes>13;
  if |K|>=|J|-1 and J>13, pair p_i p_j with 3 r_i p_j, i<j.
  Preserve greatest prime, all old PE1 with pool<=.8sqrt X, and R14;
  replace C66 for the same source cohort, never add both.
  PNT count ratio 11/10; PAPER_PROOF/SELF_AUDIT, separate review pending.
GM4: C66, R14, Q390=961, raw lift and full ordered-square checks PASS.
QUANTITATIVE LIMIT: residual after GM3 still linear; no new exponent.
NEXT SINGLE EXPERIMENT: given a proposed higher-depth common-cofactor
  extension of GM3, test donor collisions and Hall deficits on the SAME
  registered finite carriers, including X=145, before enlarging a cutoff.
  Do not repeat the unchanged full-graph scan or optimize bank constants.
OTHER ROUTES: retain prior JOH X=209 halo falsifier and CORR4 R=57/58
  joint facets; no new cross-carrier inference or fixed-K first-bad claim.
FORMAL: existing #1096 merged-tree audit verified; no new Lean execution.
GAIN: UNKNOWN; SEARCH_BROAD; canonical VF and RH remain OPEN.
PERMISSIONS: only today's own report changed remotely; no main, Lean,
  policy, other report, issue, PR, workflow, schedule, merge, or agent launch.
```

### Reproducibility

Complete executed sources follow, so the experiment does not depend on
private scratch files. The five source blocks correspond to files with
the displayed basenames in one directory. Reproduction commands:

```bash
python three_edit.py
g++ -std=c++17 -O2 -Wall -Wextra -pedantic three_edit_verify.cpp -o three_edit_verify
./three_edit_verify
python matching_stress.py
python large_prime_repair.py
g++ -std=c++17 -O2 -Wall -Wextra -pedantic repair_verify.cpp -o repair_verify
./repair_verify
python -m py_compile three_edit.py matching_stress.py large_prime_repair.py
```

All commands were executed successfully. No network or third-party
computational dependency is needed. Runtime fields in generated JSON
vary; the two exact TSV files are deterministic.

| Artifact | SHA-256 |
| --- | --- |
| three_edit.py | c1951c01584df5a745a09761ef819eba266a787919b977b2918709bbc214de87 |
| three_edit_verify.cpp | 2fc211242e1a3f240c6277f327e44c7bee00bf930400a654ba0103a15bfe23a2 |
| matching_stress.py | 417eb7bc2a98630c9346f52549d7bc98f6cd05b405666e088d2fb09fdee29630 |
| large_prime_repair.py | 06cc8d3c5d7517115b27f215311dbd8ba58adff1001849f577b82816b90b364e |
| repair_verify.cpp | ed2d7439a6db1331f0fc668d2a3d75388f1d1527a8d27d4667805a72e47b31fc |
| Python and C++ exact TSV, both | 0ab9c0801709c9a9b10c03502fe47683f173d870c17a28100d813e7bbf4a3555 |

The Python all-cutoff matching/cover/component certificate stream has
SHA-256 b7976962f2b4530dcea6d49cfed1cb7e934a3e224230ca1c0efe157f8a26eebd.
The script deterministically regenerates it; saved selected certificates
include actual edge and cover lists for the larger fixtures.


### Executed Source: three_edit.py

```python
"""Exact three-prime-edit matchings on the genuine odd upper boundary."""

from collections import Counter, deque
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
import json
import platform
import time


P9 = (3, 5, 7, 11, 13, 17, 19, 23, 29)
CUTOFFS = list(range(4, 2049)) + [4095, 8191, 16383]


def sieve(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    masks = [0] * (limit + 1)
    primes = []
    for p in range(2, limit + 1):
        if masks[p]:
            continue
        bit = 1 << len(primes)
        primes.append(p)
        for n in range(p, limit + 1, p):
            mu[n] = -mu[n]
            masks[n] |= bit
        for n in range(p * p, limit + 1, p * p):
            mu[n] = 0
    return mu, masks, primes


def graph(sites, mu, masks):
    left = [n for n in sites if mu[n] == 1]
    right = [n for n in sites if mu[n] == -1]
    adj = [[j for j, m in enumerate(right)
            if (masks[n] ^ masks[m]).bit_count() == 3] for n in left]
    return left, right, adj


def matching(left, right, adj):
    """Layered augmenting paths, with a separate minimum-cover certificate."""
    nl, nr = len(left), len(right)
    ml, mr = [-1] * nl, [-1] * nr
    inf = nl + nr + 1
    while True:
        dist = [0 if m < 0 else inf for m in ml]
        queue = deque(i for i, m in enumerate(ml) if m < 0)
        shortest = inf
        while queue:
            i = queue.popleft()
            if dist[i] >= shortest:
                continue
            for j in adj[i]:
                k = mr[j]
                if k < 0:
                    shortest = dist[i] + 1
                elif dist[k] == inf:
                    dist[k] = dist[i] + 1
                    queue.append(k)
        if shortest == inf:
            break

        def augment(i):
            for j in adj[i]:
                k = mr[j]
                if ((k < 0 and dist[i] + 1 == shortest)
                        or (k >= 0 and dist[k] == dist[i] + 1 and augment(k))):
                    ml[i], mr[j] = j, i
                    return True
            dist[i] = inf
            return False

        assert any([augment(i) for i in range(nl) if ml[i] < 0])

    zl = {i for i, j in enumerate(ml) if j < 0}
    zr = set()
    queue = deque(zl)
    while queue:
        i = queue.popleft()
        for j in adj[i]:
            if j == ml[i] or j in zr:
                continue
            zr.add(j)
            k = mr[j]
            assert k >= 0
            if k not in zl:
                zl.add(k)
                queue.append(k)
    cover_l = set(range(nl)) - zl
    cover_r = zr
    edges = [(left[i], right[j]) for i, j in enumerate(ml) if j >= 0]
    assert len(edges) == len(cover_l) + len(cover_r)
    assert len({b for _, b in edges}) == len(edges)
    assert all(j in adj[i] and mr[j] == i for i, j in enumerate(ml) if j >= 0)
    assert all(i in cover_l or j in cover_r for i, row in enumerate(adj) for j in row)
    cover = [left[i] for i in sorted(cover_l)] + [right[j] for j in sorted(cover_r)]
    hall = [left[i] for i in sorted(zl)]
    neighbors = [right[j] for j in sorted(zr)]
    return edges, cover, hall, neighbors


def components(left, right, adj):
    rev = [[] for _ in right]
    for i, row in enumerate(adj):
        for j in row:
            rev[j].append(i)
    seen = set()
    out = []
    for v in range(len(left) + len(right)):
        if v in seen:
            continue
        seen.add(v)
        queue = [v]
        pos, neg = [], []
        while queue:
            a = queue.pop()
            if a < len(left):
                pos.append(left[a])
                ns = [len(left) + j for j in adj[a]]
            else:
                j = a - len(left)
                neg.append(right[j])
                ns = rev[j]
            for b in ns:
                if b not in seen:
                    seen.add(b)
                    queue.append(b)
        out.append((sorted(pos), sorted(neg)))
    return out


def frozen_pairs(x, mu, masks, primes):
    upper_primes = [p for p in primes if x < 2 * p <= 2 * x]
    partners = sorted({s * q for s in P9 for q in primes
                       if q > max(P9) and x < 2 * s * q <= 2 * x})
    old = list(zip(upper_primes, partners))
    old += [(13 * c, 15 * c) for c in range(1, x // 15 + 1)
            if mu[c] and gcd(c, 390) == 1 and masks[c].bit_count() >= 2
            and x < 26 * c]
    flat = [n for edge in old for n in edge]
    assert len(flat) == len(set(flat))
    assert all(mu[a] == -mu[b] and mu[a] != 0 for a, b in old)
    assert all(n % 2 and x < 2 * n <= 2 * x for n in flat)
    assert all((masks[a] ^ masks[b]).bit_count() == 3 for a, b in old)
    return old


def main():
    started = time.perf_counter()
    mu, masks, primes = sieve(max(CUTOFFS))
    prefix = [0]
    for v in mu[1:]:
        prefix.append(prefix[-1] + v)
    digest = sha256()
    records, examples = [], {}
    stats = Counter()
    maximum_excess = maximum_penalty = -1
    for x in CUTOFFS:
        sites = [n for n in range(x // 2 + 1, x + 1) if n % 2 and mu[n]]
        assert sum(mu[n] for n in sites) == prefix[x]
        left, right, adj = graph(sites, mu, masks)
        edges, cover, hall, neighbors = matching(left, right, adj)
        comps = components(left, right, adj)
        t = len(sites) - 2 * len(edges)
        clb = sum(abs(len(p) - len(n)) for p, n in comps)
        isolated = [p[0] if p else n[0] for p, n in comps if len(p) + len(n) == 1]
        assert t >= clb >= abs(prefix[x])
        unmatched = set(sites) - {n for edge in edges for n in edge}
        s = sum(mu[n] for n in unmatched)
        d = sum(mu[n] ** 2 for n in unmatched)
        off = (s * s - d) // 2
        assert (s * s - d) % 2 == 0
        assert s == prefix[x] and s * s == d + 2 * off
        old = frozen_pairs(x, mu, masks, primes)
        removed = {n for edge in old for n in edge}
        rest = [n for n in sites if n not in removed]
        fl, fr, fa = graph(rest, mu, masks)
        fe, fc, fh, fn = matching(fl, fr, fa)
        ft = len(rest) - 2 * len(fe)
        assert ft >= t
        assert sum(mu[n] for n in rest) == prefix[x]
        row = [x, len(sites), len(left), len(right), sum(map(len, adj)),
               len(edges), t, prefix[x], clb, len(isolated), len(old), ft]
        records.append(row)
        cert = {"x": x, "row": row, "matching": edges, "cover": cover,
                "hall_positive": hall, "hall_neighbors": neighbors,
                "components": comps, "isolated": isolated,
                "frozen": old, "frozen_matching": fe, "frozen_cover": fc,
                "frozen_hall_positive": fh, "frozen_hall_neighbors": fn}
        digest.update(json.dumps(cert, sort_keys=True, separators=(",", ":")).encode())
        digest.update(b"\n")
        excess, penalty = t - abs(prefix[x]), ft - t
        if excess:
            stats["H3_failures"] += 1
            examples.setdefault("first_H3_failure", cert)
        if t > clb:
            stats["internal_Hall_failures"] += 1
            examples.setdefault("first_internal_Hall_failure", cert)
        if penalty:
            stats["frozen_penalties"] += 1
            examples.setdefault("first_frozen_penalty", cert)
        if excess > maximum_excess:
            maximum_excess = excess
            examples["max_H3_excess"] = cert
        if penalty > maximum_penalty:
            maximum_penalty = penalty
            examples["max_frozen_penalty"] = cert
        if x in [1155, 2001, 2002, 2048, 4095, 8191, 16383]:
            examples[str(x)] = cert
        stats["cutoffs"] += 1
    Path("three_edit.tsv").write_text(
        "X\tU\tpositive\tnegative\tedges\tmatching\tT3\tM\tcomponent_bound\tisolated\tfrozen_pairs\tT_frozen\n"
        + "".join("\t".join(map(str, row)) + "\n" for row in records))
    Path("three_edit_certificates.json").write_text(json.dumps(examples, indent=2) + "\n")
    summary = {"python": platform.python_version(), "cutoffs": CUTOFFS[-5:],
               "statistics": dict(stats), "maximum_excess": maximum_excess,
               "maximum_frozen_penalty": maximum_penalty,
               "all_certificate_sha256": digest.hexdigest(),
               "seconds": time.perf_counter() - started,
               "examples": {k: v["row"] for k, v in examples.items()}}
    Path("three_edit_summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
```


### Executed Source: three_edit_verify.cpp

```cpp
#include <algorithm>
#include <cassert>
#include <chrono>
#include <fstream>
#include <functional>
#include <iostream>
#include <numeric>
#include <queue>
#include <sstream>
#include <string>
#include <vector>

using namespace std;

struct Arithmetic {
    vector<int> mu, omega, primes;
    explicit Arithmetic(int limit) : mu(limit + 1), omega(limit + 1) {
        mu[1] = 1;
        for (int n = 2; n <= limit; ++n) {
            int t = n, sign = 1, count = 0;
            bool square = false;
            for (int p = 2; p <= t / p; ++p) {
                if (t % p) continue;
                int exponent = 0;
                do { t /= p; ++exponent; } while (t % p == 0);
                square |= exponent > 1;
                sign = -sign;
                ++count;
            }
            if (t > 1) { sign = -sign; ++count; }
            mu[n] = square ? 0 : sign;
            omega[n] = count;
            if (count == 1 && !square) primes.push_back(n);
        }
    }
    bool edge(int a, int b) const {
        return omega[a] + omega[b] - 2 * omega[gcd(a, b)] == 3;
    }
};

struct Result { int positive, negative, edge_count, mates, component_bound, isolated; };

Result solve(const vector<int>& sites, const Arithmetic& a) {
    vector<int> left, right;
    for (int n : sites) (a.mu[n] == 1 ? left : right).push_back(n);
    vector<vector<int>> adj(left.size()), rev(right.size());
    int ec = 0;
    for (int i = 0; i < (int)left.size(); ++i) {
        for (int j = 0; j < (int)right.size(); ++j) {
            if (a.edge(left[i], right[j])) {
                adj[i].push_back(j); rev[j].push_back(i); ++ec;
            }
        }
    }
    vector<int> order(left.size()), mate(right.size(), -1), seen(right.size());
    iota(order.begin(), order.end(), 0);
    stable_sort(order.begin(), order.end(), [&](int i, int j) {
        return adj[i].size() < adj[j].size();
    });
    int count = 0, stamp = 0;
    function<bool(int)> augment = [&](int i) {
        for (int j : adj[i]) {
            if (seen[j] == stamp) continue;
            seen[j] = stamp;
            if (mate[j] < 0 || augment(mate[j])) { mate[j] = i; return true; }
        }
        return false;
    };
    for (int i : order) { ++stamp; count += augment(i); }
    vector<int> left_mate(left.size(), -1);
    for (int j = 0; j < (int)right.size(); ++j) if (mate[j] >= 0) {
        assert(left_mate[mate[j]] < 0);
        left_mate[mate[j]] = j;
    }
    vector<bool> zl(left.size()), zr(right.size());
    queue<int> q;
    for (int i = 0; i < (int)left.size(); ++i) if (left_mate[i] < 0) {
        zl[i] = true; q.push(i);
    }
    while (!q.empty()) {
        int i = q.front(); q.pop();
        for (int j : adj[i]) if (left_mate[i] != j && !zr[j]) {
            zr[j] = true;
            assert(mate[j] >= 0);
            if (!zl[mate[j]]) { zl[mate[j]] = true; q.push(mate[j]); }
        }
    }
    int cover = 0;
    for (bool b : zl) cover += !b;
    for (bool b : zr) cover += b;
    assert(cover == count);
    for (int i = 0; i < (int)left.size(); ++i)
        for (int j : adj[i]) assert(!zl[i] || zr[j]);

    vector<bool> visited(left.size() + right.size());
    int clb = 0, isolated = 0;
    for (int root = 0; root < (int)visited.size(); ++root) {
        if (visited[root]) continue;
        visited[root] = true; q.push(root);
        int imbalance = 0, population = 0;
        while (!q.empty()) {
            int v = q.front(); q.pop(); ++population;
            if (v < (int)left.size()) {
                ++imbalance;
                for (int j : adj[v]) {
                    int w = (int)left.size() + j;
                    if (!visited[w]) { visited[w] = true; q.push(w); }
                }
            } else {
                --imbalance;
                for (int w : rev[v - left.size()])
                    if (!visited[w]) { visited[w] = true; q.push(w); }
            }
        }
        clb += abs(imbalance); isolated += population == 1;
    }
    return {(int)left.size(), (int)right.size(), ec, count, clb, isolated};
}

int main() {
    auto start = chrono::steady_clock::now();
    Arithmetic a(16383);
    const vector<int> pool{3,5,7,11,13,17,19,23,29};
    vector<int> xs;
    for (int x = 4; x <= 2048; ++x) xs.push_back(x);
    for (int x : {4095,8191,16383}) xs.push_back(x);
    ofstream output("three_edit_cpp.tsv");
    output << "X\tU\tpositive\tnegative\tedges\tmatching\tT3\tM\tcomponent_bound\tisolated\tfrozen_pairs\tT_frozen\n";
    for (int x : xs) {
        int sum = 0;
        vector<int> sites, top, partners;
        for (int n = 1; n <= x; ++n) {
            sum += a.mu[n];
            if (n % 2 && 2*n > x && a.mu[n]) sites.push_back(n);
        }
        for (int p : a.primes) if (p <= x && 2*p > x) top.push_back(p);
        for (int n : sites) if (a.mu[n] == 1 && a.omega[n] == 2) {
            for (int p : pool) if (n % p == 0 && n/p > 29 &&
                    binary_search(a.primes.begin(), a.primes.end(), n/p)) {
                partners.push_back(n); break;
            }
        }
        vector<bool> removed(x+1);
        int frozen = min(top.size(), partners.size());
        for (int i = 0; i < frozen; ++i) {
            removed[top[i]] = true; removed[partners[i]] = true;
        }
        for (int n : sites) {
            if (n % 13) continue;
            int c = n/13, m = 15*c;
            if (m > x || a.omega[c] < 2 || gcd(c,390) != 1 || !a.mu[c]) continue;
            assert(!removed[n] && !removed[m]);
            assert(a.mu[n] == -a.mu[m] && a.edge(n,m));
            removed[n] = removed[m] = true; ++frozen;
        }
        vector<int> rest;
        for (int n : sites) if (!removed[n]) rest.push_back(n);
        Result full = solve(sites,a), locked = solve(rest,a);
        int t = (int)sites.size()-2*full.mates;
        int ft = (int)rest.size()-2*locked.mates;
        vector<int> row{x,(int)sites.size(),full.positive,full.negative,
                        full.edge_count,full.mates,t,sum,full.component_bound,
                        full.isolated,frozen,ft};
        for (int i=0;i<(int)row.size();++i) output << (i ? "\t" : "") << row[i];
        output << '\n';
    }
    output.close();
    ifstream py("three_edit.tsv"), cpp("three_edit_cpp.tsv");
    string s,t;
    int lines=0;
    while (getline(py,s)) { assert((bool)getline(cpp,t)); assert(s==t); ++lines; }
    assert(!getline(cpp,t));
    cout << "PASS: independent trial factorization, gcd graph, DFS matching, covers, components and frozen return\n";
    cout << "exact identical rows=" << lines-1 << ", mu domain=1..16383\n";
    cout << "seconds=" << chrono::duration<double>(chrono::steady_clock::now()-start).count() << '\n';
}
```


### Executed Source: matching_stress.py

```python
"""Post-discovery extension test and independent source-return controls."""

from collections import Counter, defaultdict
from itertools import combinations, product
from math import comb, gcd, isqrt, prod
from pathlib import Path
import json
import time

from three_edit import sieve, graph, matching, frozen_pairs


def raw_atoms(b, k, x, mu):
    atoms = []
    seed = [n for n in range(1, b) if mu[n]]
    for j in range(1, k + 1):
        for aa in product(seed, repeat=j):
            v = prod(aa)
            if v > x:
                continue
            sign = (-1) ** (j - 1) * prod(mu[n] for n in aa)

            def visit(bb, n, remaining):
                if remaining == 0:
                    for copy in range(comb(k, j)):
                        atoms.append(((j, copy, aa, bb), n, sign))
                    return
                for q in range(1, x // n + 1):
                    visit(bb + (q,), n * q, remaining - 1)

            visit((), v, j - 1)
    return atoms


def convolution(a, b):
    out = [0] * len(a)
    for n in range(1, len(a)):
        for d in range(1, isqrt(n) + 1):
            if n % d:
                continue
            out[n] += a[d] * b[n // d]
            if d * d != n:
                out[n] += a[n // d] * b[d]
    return out


def lift_check(b, k, mu, masks):
    x = b ** k - 1
    atoms = raw_atoms(b, k, x, mu)
    assert len(atoms) == len({a[0] for a in atoms})
    fibers = defaultdict(list)
    for i, (_, n, _) in enumerate(atoms):
        fibers[n].append(i)
    assert all(sum(atoms[i][2] for i in fibers[n]) == mu[n] for n in range(1, x + 1))
    seed = [mu[n] if n < b else 0 for n in range(x + 1)]
    defect = [-v for v in convolution(seed, [0] + [1] * x)]
    defect[1] += 1
    lift = [0] * (x + 1)
    for _ in range(k):
        tmp = convolution(defect, lift)
        lift = [s + t for s, t in zip(seed, tmp)]
    assert lift == mu[:x + 1]
    mate = {}
    representative = {}

    def pair(i, j):
        assert i != j and i not in mate and j not in mate
        assert atoms[i][2] == -atoms[j][2]
        mate[i], mate[j] = j, i

    for n, ids in fibers.items():
        pos = [i for i in ids if atoms[i][2] == 1]
        neg = [i for i in ids if atoms[i][2] == -1]
        for i, j in zip(pos, neg):
            pair(i, j)
        rem = [i for i in ids if i not in mate]
        assert len(rem) == abs(mu[n])
        if rem:
            representative[n] = rem[0]
    for n in range(1, x // 2 + 1, 2):
        if mu[n]:
            pair(representative[n], representative[2 * n])
    sites = [n for n, i in representative.items() if i not in mate]
    l, r, adj = graph(sorted(sites), mu, masks)
    edges, _, _, _ = matching(l, r, adj)
    for n, m in edges:
        pair(representative[n], representative[m])
    fixed = [i for i in range(len(atoms)) if i not in mate]
    assert sum(atoms[i][2] for i in fixed) == sum(mu[1:x + 1])
    # Explicit tensor involution uses the first nonfixed coordinate.
    square_sum = 0
    ordered_fixed = 0
    for i in range(len(atoms)):
        for j in range(len(atoms)):
            sign = atoms[i][2] * atoms[j][2]
            square_sum += sign
            if i in mate:
                ii, jj = mate[i], j
            elif j in mate:
                ii, jj = i, mate[j]
            else:
                ordered_fixed += 1
                continue
            assert atoms[ii][2] * atoms[jj][2] == -sign
            back = (mate[ii], jj) if ii in mate else (ii, mate[jj])
            assert back == (i, j)
    assert ordered_fixed == len(fixed) ** 2
    assert square_sum == sum(mu[1:x + 1]) ** 2
    return {"B": b, "k": k, "X": x, "atoms": len(atoms),
            "ordered_pairs": len(atoms) ** 2, "fixed": len(fixed),
            "M": sum(mu[1:x + 1]), "square": square_sum}


def main():
    start = time.perf_counter()
    mu, masks, primes = sieve(16383)
    witness = None
    candidates_checked = 0
    for x in range(4, 2049):
        m = sum(mu[1:x + 1])
        if m < 0:
            continue
        sites = [n for n in range(x // 2 + 1, x + 1) if n % 2 and mu[n]]
        top = [n for n in sites if masks[n].bit_count() == 1]
        for n in sites:
            if masks[n].bit_count() != 3:
                continue
            candidates_checked += 1
            neighbors = [a for a in sites if mu[a] == 1
                         and (masks[a] ^ masks[n]).bit_count() == 3]
            if len(neighbors) > len(top) or any(masks[a].bit_count() != 2 for a in neighbors):
                continue
            old = list(zip(top, neighbors))
            removed = {v for edge in old for v in edge}
            assert len(removed) == 2 * len(old)
            assert all((masks[a] ^ masks[b]).bit_count() == 3 and mu[a] == -mu[b]
                       for a, b in old)
            rest = [v for v in sites if v not in removed]
            l, r, adj = graph(rest, mu, masks)
            edges, cover, hall, hn = matching(l, r, adj)
            t = len(rest) - 2 * len(edges)
            assert t >= m + 2
            final = old + edges
            used = {v for edge in final for v in edge}
            unused_pos = [v for v in sites if mu[v] == 1 and v not in used]
            repair = next(([n, b, a, p] for a, b in old for p in unused_pos
                           if (masks[a] ^ masks[p]).bit_count() == 3), None)
            if repair:
                assert all((masks[a] ^ masks[b]).bit_count() == 3
                           for a, b in zip(repair, repair[1:]))
            witness = {"X": x, "M": m, "isolated_negative": n,
                       "neighborhood": neighbors, "frozen_matching": old,
                       "remaining_matching": edges, "remaining_cover": cover,
                       "remaining_sites": rest, "T_frozen": t,
                       "hall_positive": hall, "hall_neighbors": hn,
                       "augmenting_path": repair}
            break
        if witness:
            break

    x = 16383
    old = frozen_pairs(x, mu, masks, primes)
    used = {n for edge in old for n in edge}
    js = [p for p in primes if 25 * p * p > 16 * x and 100 * p * p <= 81 * x]
    cohort = sorted(a * b for a, b in combinations(js, 2))
    donors = [15 * p for p in primes if p > 13 and x < 30 * p and 15 * p <= x]
    new = list(zip(cohort, donors))
    assert len(new) == len(cohort) == 6
    assert len({n for edge in new for n in edge}) == 12
    assert not used.intersection(n for edge in new for n in edge)
    assert all(mu[a] == 1 and mu[b] == -1 and x < 2 * a <= 2 * x
               and x < 2 * b <= 2 * x for a, b in new)
    upper = [n for n in range(x // 2 + 1, x + 1) if n % 2 and mu[n]]
    before = [n for n in upper if n not in used]
    used.update(n for edge in new for n in edge)
    after = [n for n in upper if n not in used]
    assert len(after) == len(before) - 12
    assert sum(mu[n] for n in before) == sum(mu[n] for n in after) == sum(mu[1:x + 1])
    r14 = {}
    for z in [1155, 2001, 2002, 4095]:
        pairs = [(13*c, 15*c) for c in range(1, z//15 + 1)
                 if mu[c] and gcd(c,390) == 1 and masks[c].bit_count() >= 2
                 and z < 26*c]
        r14[z] = pairs
    assert (1001,1155) in r14[1155] and (1001,1155) in r14[2001]
    assert (1001,1155) not in r14[2002]
    assert (383,403) in frozen_pairs(465, mu, masks, primes)
    d = 390
    divisors = [e for e in range(1,d+1) if d % e == 0]
    q_direct = sum(bool(mu[n]) and gcd(n,d)==1 for n in range(1,4096))
    q_formula = sum(mu[a] * sum(mu[e] * (4095//(a*a*e)) for e in divisors)
                    for a in range(1,isqrt(4095)+1) if gcd(a,d)==1)
    assert q_formula == q_direct
    lifts = [lift_check(b,k,mu,masks) for b,k in [(3,2),(3,3),(4,3),(3,4)]]
    result = {"postdiscovery_extension_witness": witness,
              "targeted_candidates_checked": candidates_checked,
              "C66": {"X":x,"prime_band":js,"new_pairs":new,
                      "before":len(before),"after":len(after),"M":sum(mu[1:x+1])},
              "R14_pairs":r14,"Q390_4095":q_direct,
              "raw_lift_checks":lifts,"seconds":time.perf_counter()-start}
    Path("matching_stress.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
```


### Executed Source: large_prime_repair.py

```python
"""Post-discovery three-edit repair and exact minimality certificate."""

from itertools import combinations
from pathlib import Path
import json

from three_edit import CUTOFFS, sieve, frozen_pairs


def main():
    mu, masks, primes = sieve(16383)
    lower_checks = []
    for x in range(4, 145):
        sites = [n for n in range(x // 2 + 1, x + 1) if n % 2 and mu[n]]
        positives = [n for n in sites if mu[n] == 1]
        top = [n for n in sites if masks[n].bit_count() == 1]
        other = [n for n in sites if mu[n] == -1 and n not in top]
        assert all(masks[n].bit_count() == 2 for n in positives)
        assert not other or len(top) >= len(positives)
        assert all((masks[a] ^ masks[b]).bit_count() == 3
                   for a in positives for b in top)
        lower_checks.append([x, len(positives), len(top), len(other)])
    x = 145
    psmall = (3,5,7)
    top = [p for p in primes if x < 2*p <= 2*x]
    partners = sorted({p*q for p in psmall for q in primes
                       if q > 7 and x < 2*p*q <= 2*x})
    assert len(top) == len(partners) == 14
    frozen = list(zip(top,partners))
    used = {n for e in frozen for n in e}
    sites = [n for n in range(x//2+1,x+1) if n%2 and mu[n]]
    assert set(sites)-used == {105,143}
    assert (masks[105]^masks[143]).bit_count() == 5
    repaired = [e for e in frozen if e != (73,77)] + [(105,77),(73,143)]
    assert len(repaired) == 15 and {n for e in repaired for n in e} == set(sites)
    assert all(mu[a] == -mu[b] and (masks[a]^masks[b]).bit_count() == 3
               for a,b in repaired)
    eligible = nonempty = pairs_checked = 0
    fixtures = []
    for x in CUTOFFS:
        j = [p for p in primes if 25*p*p > 16*x and 100*p*p <= 81*x]
        r = [p for p in primes if p > 13 and 16*p*p > x and 625*p*p <= 81*x]
        if any(p<=29 for p in j) or len(r) < len(j)-1:
            continue
        eligible += 1
        new = [(p*q, 3*r[i]*q) for i,p in enumerate(j) for q in j[i+1:]]
        nonempty += bool(new)
        pairs_checked += len(new)
        old = frozen_pairs(x,mu,masks,primes)
        old_sites = {n for edge in old for n in edge}
        new_sites = [n for edge in new for n in edge]
        assert len(set(new_sites)) == len(new_sites)
        assert not old_sites.intersection(new_sites)
        assert all(mu[a]==1 and mu[b]==-1 and x<2*a<=2*x and x<2*b<=2*x
                   and (masks[a]^masks[b]).bit_count()==3 for a,b in new)
        assert all(max(p for p in primes if a%p==0)==max(p for p in primes if b%p==0)
                   for a,b in new)
        remaining = [n for n in range(x//2+1,x+1)
                     if n%2 and mu[n] and n not in old_sites]
        total = sum(mu[n] for n in remaining)
        final = [n for n in remaining if n not in set(new_sites)]
        assert sum(mu[n] for n in final) == total == sum(mu[1:x+1])
        v = len(new)
        assert v*v+v*v+total*total-2*v*v+2*v*total-2*v*total == total*total
        if x in [4095,8191,16383]:
            fixtures.append({"X":x,"J":j,"K":r,"pairs":new,
                             "before":len(remaining),"after":len(final),"M":total})
    result = {"minimality_cutoffs":len(lower_checks),
              "X145_P":psmall,"X145_frozen":frozen,"X145_repaired":repaired,
              "eligible_cutoffs":eligible,"nonempty_cutoffs":nonempty,
              "pairs_checked":pairs_checked,"fixtures":fixtures}
    Path("large_prime_repair.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__ == "__main__":
    main()
```


### Executed Source: repair_verify.cpp

```cpp
#include <algorithm>
#include <cassert>
#include <iostream>
#include <numeric>
#include <set>
#include <utility>
#include <vector>
using namespace std;

struct Factor {
    int sign = 1;
    vector<int> primes;
    explicit Factor(int n) {
        for (int p=2;p<=n/p;++p) {
            if (n%p) continue;
            primes.push_back(p);
            int exponent=0;
            do {n/=p;++exponent;} while(n%p==0);
            if(exponent>1) sign=0;
            else sign=-sign;
        }
        if(n>1) {primes.push_back(n);sign=-sign;}
    }
};

int main() {
    vector<Factor> f;
    for(int n=0;n<=16383;++n) f.emplace_back(n);
    vector<int> primes;
    for(int n=2;n<=16383;++n)
        if(f[n].primes.size()==1 && f[n].sign==-1) primes.push_back(n);
    auto edge=[&](int a,int b) {
        vector<int> diff;
        set_symmetric_difference(f[a].primes.begin(),f[a].primes.end(),
                                 f[b].primes.begin(),f[b].primes.end(),back_inserter(diff));
        return diff.size()==3;
    };
    for(int x=4;x<145;++x) {
        int pos=0,top=0,other=0;
        for(int n=x/2+1;n<=x;++n) if(n%2 && f[n].sign) {
            if(f[n].sign==1) {++pos;assert(f[n].primes.size()==2);}
            else if(f[n].primes.size()==1) ++top;
            else ++other;
        }
        assert(!other || top>=pos);
    }
    vector<pair<int,int>> locked{{73,77},{79,85},{83,87},{89,91},{97,93},
        {101,95},{103,111},{107,115},{109,119},{113,123},{127,129},
        {131,133},{137,141},{139,145}};
    set<int> used;
    for(auto [a,b]:locked) {
        assert(a>145/2 && a<=145 && b>145/2 && b<=145);
        assert(f[a].sign==-f[b].sign && edge(a,b));
        assert(used.insert(a).second && used.insert(b).second);
        assert(b%3==0 || b%5==0 || b%7==0);
    }
    vector<int> remaining;
    int total=0;
    for(int n=1;n<=145;++n) {
        total+=f[n].sign;
        if(n%2 && 2*n>145 && f[n].sign && !used.count(n)) remaining.push_back(n);
    }
    assert(total==0 && remaining==vector<int>({105,143}) && !edge(105,143));
    assert(edge(105,77) && edge(73,143));
    cout << "PASS X=145 legal locked PE1, empty residual graph, explicit augmenting repair; 141 lower cutoffs certified\n";
    vector<int> xs;
    for(int x=4;x<=2048;++x) xs.push_back(x);
    for(int x:{4095,8191,16383}) xs.push_back(x);
    int cases=0,nonempty=0,pairs=0;
    for(int x:xs) {
        vector<int> j,k;
        for(int p:primes) {
            long long p2=1LL*p*p;
            if(25*p2>16*x && 100*p2<=81*x) j.push_back(p);
            if(p>13 && 16*p2>x && 625*p2<=81*x) k.push_back(p);
        }
        if((!j.empty() && j.front()<=29) || (int)k.size()<(int)j.size()-1) continue;
        ++cases; nonempty+=j.size()>=2;
        set<int> endpoints;
        for(int i=0;i<(int)j.size();++i) for(int h=i+1;h<(int)j.size();++h) {
            int a=j[i]*j[h], b=3*k[i]*j[h];
            assert(f[a].sign==1 && f[b].sign==-1 && edge(a,b));
            assert(a>x/2 && a<=x && b>x/2 && b<=x);
            assert(endpoints.insert(a).second && endpoints.insert(b).second);
            assert(f[a].primes.back()==j[h] && f[b].primes.back()==j[h]);
            assert(b%5 && b%13 && f[b].primes.size()==3);
            assert(f[a].primes.front()>29);
            ++pairs;
            if(x==16383) cout<<a<<" <-> "<<b<<"; greatest prime "<<j[h]<<'\n';
        }
    }
    cout<<"PASS three-edit repair eligible="<<cases<<", nonempty="<<nonempty<<", pairs="<<pairs<<'\n';
}
```


### Closeout Source Freshness

At 2026-11-06 08:42:27 UTC (03:42:27 EST), main was re-fetched and
remained 4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a. Today's Owner, Analytic and Wheel report
blobs were unchanged; Coordinator, Referee and Lean were still absent.
Their TODAY=PENDING / YESTERDAY=CARRY_FORWARD status is retained.
The preregistration remains an exact prefix of this completed report.
No additional scan or unobserved upstream execution is claimed.


### Verified Publication Receipt - 20261106-census-1

At 2026-11-06 08:44:24 UTC, the completed synthesis and all five executable
source blocks were re-fetched at immutable commit
**d65c6c19807681396b4ba1f5e9b71ab352e959d8**, blob
**294df90c7831c4fa2a949a59b2068fb61bcb40a2**, and matched the submitted bytes exactly.
The commit API confirmed that only this authorized report path changed.
The earlier checkpoint is preserved as an exact prefix.

Execution and publication: COMPLETE / PUBLISHED.
Mathematics: GM1/GM4 FINITE_COMPUTATION; GM2 scoped REFUTED assertion;
GM3 PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.
The unrestricted H3 remains CONJECTURE. No new endpoint gain or RH claim.
This receipt describes the already verified synthesis, not its own future
commit. No other role was launched and no unauthorized remote path changed.


## Scheduled Higher-Depth Checkpoint - 20261106-census-2

Actual trigger: scheduled 2026-11-06 11:00:01 EST (America/New_York).
RUN_ID_UNAVAILABLE. Checkpoint prepared 2026-11-06 16:12 UTC.
Status: PARTIAL / IN_PROGRESS. No new experiment result is asserted here.

Main fetched at invocation: 4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a.
AGENTS blob 547dda0d9456e7a4e1165dc72d59da6f70d5c023; contract
7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c; routing policy
ffd8f1c65cc4da656174956d4e03b48bea46768b.
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1; eta_gate=SEARCH_BROAD.
The canonical actual-prime VF bound remains OPEN.

### Resumed Question And Source

Resume this morning's GM3 and its explicit higher-depth common-cofactor
continuation. Original carrier:
U_X={n:1<=n<=X, n odd, X<2n, mu(n)!=0}, with original unit weights.
Read main's odd-boundary source (blob 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1),
signed lift (af69b4811cf9f523eb7c96fb0ca836b2cdbd1180), and original
finite-prefix and canonical consumers. #1096's merged status, exact-head
successful dedicated run 42150511056, and actual ten-declaration standard-axiom
log were freshly retrieved; these do not certify the new extension.

All Nov 5 and available Nov 6 role reports and external inbox were retrieved.
The Nov 6 Coordinator is PARTIAL: completed synthesis TODAY=PENDING,
YESTERDAY=CARRY_FORWARD. New RM, DR, PB and TD results stay on their own
carriers. MU-LIFT is selected to finish a precise ready continuation,
not to impose a common campaign. No unchanged full-graph scan is planned.
Only open PR at intake: #1097, non-draft, head bc727dc9f7dd655fdd2addc943b246ad70ef576d.

### Preregistered Hypotheses And Discriminator

For each squarefree c coprime to 390, put y=X/c (a rational, NOT floor(X/c)),
J_c={prime p:(4/5)sqrt(y)<p<=(9/10)sqrt(y)}, sorted p_i,
K_c={prime r>13:(1/4)sqrt(y)<r<=(9/25)sqrt(y)}, sorted r_i.
Require J_c>29 and |K_c|>=|J_c|-1, and form
c*p_i*p_j <-> 3*c*r_i*p_j for i<j.

H-LOCAL: keeping only individually squarefree legal endpoint pairs is
enough to combine all these cofactor lifts without endpoint collisions.
Rival: distinct cofactors can reserve the same physical endpoint.
Reject H-LOCAL upon an exact duplicate endpoint from two distinct tuples.

H-SEPARATED: adding 16*c*Pplus(c)^2<=X, Pplus(1)=1, makes the entire
union disjoint, greatest-prime-preserving and disjoint from every retained
P9 prime/semiprime pair and qualified 13c/15c pair.
Reject on any repeated endpoint, wrong sign, incorrect factor edit, old-site
reuse, failed interval admission or failed complete signed reconstruction.

Test development: X=4..2048 plus 4095,8191,16383, including X=145.
Held-out stress fixtures: 65535,262143,1048575.
For H-LOCAL only, search EVERY integer X=4..131071 and stop at the first
collision; if none is found report finite survival, not a theorem.
Each search tests new cofactor multiplicity, not the prior maximum matching.

Proof-driven quantitative candidate, not a fitted exponent:
for fixed 0<alpha<1/3, restrict c<=X^alpha. Determine whether the all-large-X
pair count is asymptotic to
delta_390*alpha/[50*(1-alpha)] * X/log X,
delta_390=(1/zeta(2))*product_(p|390)p/(p+1)=65/(28*pi^2).
This would improve the former fixed-c packet's logarithmic count, NOT the
linear residual exponent or a Mertens bound. Audit PNT uniformity and
cofactor separation before accepting the candidate.

Methods planned: exact Python arithmetic and independent C++ trial-factor/
endpoint reconstruction; no local Lean. Preserve all original signs,
squares and mixed terms. Publish code, exact certificates, honest finite
coverage, proof scope and the first unpaid complete-source inequality.


## Higher-Depth Final Synthesis - 20261106-census-2

This completes the scheduled 2026-11-06 11:00:01 EST invocation, not a
new launch. RUN_ID_UNAVAILABLE. Calculations and independent implementation
checks are complete. Publication is established by the later receipt.

Operational correction: the checkpoint's typed `16:12 UTC` preparation
timestamp was inaccurate. Its write and exact readback were already complete
by the observed clock reading **2026-11-06 16:11:29 UTC**. The actual scheduled
trigger above is unchanged. This correction preserves the original entry.

### A. Most Important Mathematical Discovery

**A higher-depth extension is possible, but local legality does not prevent
different cofactors from spending the same donor. A recoverable cofactor
fixes that collision, while a separate factor-ratio obstruction limits the
entire construction.**

At **X=87283**, the two individually valid lifts

```text
17*59*61 = 61183  <->  3*17*19*61 = 59109,
19*59*61 = 68381  <->  3*19*17*61 = 59109
```

reuse one physical donor. This is the first collision for the precisely
registered unrestricted lift at every integer cutoff from 4 onward.
It is not a Hall obstruction to every matching: changing the first donor
to `3*17*23*61=71553` repairs the whole 15-source packet.

The constructive repair is to require
`16*c*Pplus(c)^2<=X`. Then the original cofactor is recoverable uniquely
from both endpoints, so ALL permitted cofactors can be combined at once.
This extends morning GM3 beyond depth two, retains greatest-prime ownership,
and preserves the old P9 and qualified 13/15 matches without double use.

For every FIXED `0<alpha<1/3`, the subfamily `c<=X^alpha` has a proved
paper asymptotic

```text
number of pairs ~ delta_390*alpha/[50*(1-alpha)] * X/log X,
delta_390 = 65/(28*pi^2).
```

This gains a logarithmic factor over GM3's fixed-cofactor packet. However,
even the union over EVERY separated cofactor contains only
`O(X/log log X)` pairs. Its two largest source primes are too close in
ratio to cover a positive-density population. The complete remainder
after all three stages still has leading term `157X/(84*pi^2)`.
Thus growing factor depth alone does not repair an absolute-remainder
MU-LIFT finish.

| Claim | Result | Evidence |
| --- | --- | --- |
| HC1 | First duplicate donor at X=87283; exact full-packet repair | REFUTED for H-LOCAL; FINITE_COMPUTATION |
| HC2 | Simultaneous separated-cofactor injection, all finite X under stated hypotheses | PAPER_PROOF |
| HC3 | Growing cofactor subfamily has the displayed X/log X asymptotic | PAPER_PROOF |
| HC4 | Entire separated family is O(X/log log X); complete cardinality remains linear | PAPER_PROOF |
| HC5 | Exact source, multiplicity, sign, full-square and independent reconstruction checks | FINITE_COMPUTATION |

Claim prefix: `20261106-census-2/`. Paper proofs are SELF_AUDIT,
INDEPENDENT_REVIEW_PENDING and NOT_FORMALIZED. No new Lean result, uniform
Mertens estimate, canonical VF estimate or RH proof is asserted.
`eta_gate=SEARCH_BROAD`; new net endpoint gain `UNKNOWN`.

### B. Current Authoritative Objective And Provenance

Repository: OVVO-Financial/RH_Lean. Main actually retrieved at invocation:
**4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a**, tree
**48b193cd105e21183b1cfd68b059894c8056f35c**. Initial reporting snapshot:
**12f56ca7cc7a9a9d450cc7907e3411b219593e21**.
Authority retrieval began at 16:00 UTC on November 6, America/New_York
date November 6, UTC offset -05:00.

The unchanged canonical target is

```text
VFCanonicalSquareVonKochStatement:
exists C>=0, forall integers R>=2,
 |pi(R^2)-VF_can(R^2)| <= C*R*log R.
```

It is OPEN. The inspected canonical consumer still explicitly requires
ClassicalVonKochRHCriterion. This run instead uses the genuine Mobius
MU-LIFT carrier and does not identify it with weighted native VF or Hecke.

| Source at pinned main | Blob SHA |
| --- | --- |
| AGENTS.md | 547dda0d9456e7a4e1165dc72d59da6f70d5c023 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| Independent multi-front policy | ffd8f1c65cc4da656174956d4e03b48bea46768b |
| Stable task selector | 4fbab59cc6fcc33a4f4e7a8ef447b2f7947b53dd |
| Broad-search policy | 8317f08996b65f2e4b32c00c91b31cb6d0c09718 |
| Complete-return contract | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| Persistent research engine | 6c1d1c10e2755017ffe9d7f40df8b9ae7692f23a |
| Role prompts | 53143573cd5b014178d11ded008dbfb1a7e6dcc5 |
| Dynamic protocol | 23b6fae1d3b6b5a69155628df709d255aea7aeca |
| research/MERTENS_ODD_BOUNDARY_PRIME_ESCAPE_20261105.lean | 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1 |
| research/MERTENS_HEATH_BROWN_SIGNED.lean | af69b4811cf9f523eb7c96fb0ca836b2cdbd1180 |
| research/MERTENS_FINITE_PREFIX_EXTENSION.lean | 131e9af86207a42d4bf6488e3f64c9ce4f97e5df |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

`deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1`. Selected task:
MU-LIFT-HIGHER-DEPTH-DONOR-UNIQUENESS, the explicit morning resume request.
Prior Census support was CORR4 then JOH then morning MU-LIFT. This targeted
completion does not bind other investigators or supersede protected rotation.

Recent accepted source changes were discovered: #1094's Nyman correction
inequality, #1095's fail-closed Euler audit repair and #1096's odd-boundary
theorem. Only #1097 is open, non-draft, head
bc727dc9f7dd655fdd2addc943b246ad70ef576d, concerning CORR4 sampling.
It is not used as a supplier here.

Relevant formal evidence was actually fetched: #1096 was merged at
2026-11-06T05:44:44Z; proof head ecf701ff2fea1de52e505ee34048a2b3c220f0fc.
[Dedicated run 42150511056](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42150511056)
and job 127672350630 succeeded. The log contains warning-fatal checking,
the ten exact declarations, and actual axiom lists limited to propext,
Classical.choice and Quot.sound. Its synthetic merge
7783734bdc9960d3c2483af380759db85e87bc8f has the SAME tree as pinned main.
This verifies inherited finite source infrastructure, NOT HC1-HC4.
No local Lean or new GitHub Actions run was launched.

### C. Competing Hypotheses And Preregistration

The early checkpoint was committed as
**7c31c079056bc7b73400f2cf10aed6b1337cccb4**, blob
**130cd84b6d4e5db608f9162ce9d1ca1830c12073**, and read back byte-identically.
It fixed the following before the census:

1. H-LOCAL: individually legal common-cofactor lifts can be united without
   endpoint collisions. Rival: different cofactors reuse a donor.
2. H-SEPARATED: `16*c*Pplus(c)^2<=X` supplies a collision-free, sign-reversing,
   greatest-prime-preserving union that does not reuse prior endpoints.
3. Quantitative candidate: fixed `0<alpha<1/3` permits the displayed
   `X/log X` pair count for `c<=X^alpha`, with uniform PNT and exact density.

The rejection conditions were a duplicate endpoint, incorrect admission,
wrong sign, factor-edit mismatch, old-site reuse, or failed full reconstruction.
Development: every X=4..2048 plus 4095,8191,16383. Held-out fixtures:
65535,262143,1048575. H-LOCAL alone was to scan every X=4..131071 and stop
at its first collision. It stopped at 87283, after 87,280 cutoffs.
No result is claimed for the unexecuted remainder of that search.

Before the first program ran, its supplementary donor-capacity check was
also fixed: at a collision, allow every r in the SAME admitted K_c and
test whether distinct donors remain available. This was written in the
program after the published checkpoint, not retroactively claimed to be
part of that earlier remote text.

HC4's all-cofactor upper bound and the six high-depth fixture pairs were
developed after the initial results. They are expressly post-discovery
proof analysis and exact checks, not preregistered predictions.

### D. Exact Carrier And Construction

For integer X>=4, reuse the literal main definition

```text
U_X={n: 1<=n<=X, n odd, X<2n, mu(n)!=0},
M(X)=sum_(1<=n<=X)mu(n)=sum_(n in U_X)mu(n).
```

The equality is the inspected `sum_moebius_eq_oddSquarefreeUpper`.
Signs are genuine Mobius signs and weights are one. Squareful coefficients
are zero; no nonzero physical site or historical occurrence is deduplicated.

Set Pplus(1)=1. For squarefree positive c coprime to 390, let y=X/c as
a RATIONAL number, without replacing it by floor(X/c). Define

```text
J_c={prime p: 25*c*p^2>16X, 100*c*p^2<=81X}={p_1<...<p_m},
K_c={prime r>13:16*c*r^2>X,625*c*r^2<=81X}={r_1<...<r_l}.
```

Only nonempty packets with m>=2, min(J_c)>29 and l>=m-1 are used.
The proposed edge for i<j is

```text
a_(c,i,j)=c*p_i*p_j  <->  b_(c,i,j)=3*c*r_i*p_j.      (HC)
```

The unrestricted H-LOCAL test keeps only those edges for which
gcd(c,p_i*p_j*r_i)=1. The separated construction instead requires
`16*c*Pplus(c)^2<=X`, which automatically gives that coprimality.
There is no cofactor cutoff in HC2; HC3 alone adds c<=X^alpha.

The retained old matching is exactly the sorted-list P9 stage, with
P9={3,5,7,11,13,17,19,23,29}, partner s*q, q>29, X/2<s*q<=X,
followed by qualified R14 pairs 13d<->15d with
gcd(d,390)=1, mu(d)!=0, omega(d)>=2, X<26d and 15d<=X.
The new c=1 packet CONTAINS morning GM3. It replaces that stage as part
of a larger union; it must not be added to GM3 or C66 a second time.

All nonempty packets require r_1>=17, hence
`625*c*17^2<=81X`. This proves the finite cofactor loop bound used by
both implementations; it is not a heuristic cutoff.

### E. Executed Results And Independent Checks

Python and independently structured C++ computations agree on EVERY one
of the 2,051 output rows. All separated-packet admission, sign, three-edit,
greatest-prime, old-mate preservation and complete reconstruction checks pass.
The new full-source tests do not recompute GM1's maximum full-graph matching.

| X | Original U_X size | M(X) | Old P9/R14 pairs | New pairs, all separated c | Of these c>1 | Of these c^4<=X | Final remainder size |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 145 | 30 | 0 | 5 | 0 | 0 | 0 | 20 |
| 8191 | 1660 | 22 | 482 | 1 | 0 | 1 | 694 |
| 16383 | 3320 | -32 | 912 | 7 | 1 | 7 | 1482 |
| 65535 | 13286 | 14 | 3239 | 7 | 1 | 7 | 6794 |
| 262143 | 53114 | 24 | 11715 | 46 | 18 | 46 | 29592 |
| 1048575 | 212485 | 257 | 42899 | 190 | 70 | 178 | 126307 |

At X=145 this uses the previously registered P9 pool, NOT GM2's
{3,5,7} pool. Thus the 20-site remainder does not contradict that earlier
zero-residual repair. No new matching is claimed there.

At X=1048575 the 190 new pairs use 13 distinct cofactors. Pair counts by
omega(c) are 120 at depth zero, 64 at depth one and 6 at depth two.
The first depth-two-cofactor pair is

```text
c=77=7*11: 754369=77*97*101 <-> 723261=3*77*31*101.
```

For the exact higher-depth fixture X=21445347, c=1309=7*11*17, the six
morning base pairs scale to six legal depth-five/depth-six pairs. One is

```text
14426489=7*11*17*103*107
 <-> 15546993=3*7*11*17*37*107.
```

This is a direct twelve-endpoint certificate, not a population census to
21 million. Trial division verifies all twelve endpoints, all signs, the
bands, separation, distinctness and greatest-prime preservation. Old-stage
nonuse follows from the proved depth/divisibility tests in H, not from a
claimed scan of all earlier endpoints at that larger X.

Python uses a prime-multiple sign sieve, exact integer square roots and
factor-set checks. C++ independently trial-factors EVERY integer through
1048575, enumerates the bands by direct integer inequalities, and recovers
old semiprimes from actual sites rather than multiplying the Python prime
table. It directly accumulates the residual off-diagonal sum by streaming
signed partial sums. No factor arrays, endpoint tables or matchings are
shared between the two census implementations.

The standalone certificate audit uses only trial division and exact rational
arithmetic. It independently checks the duplicate and repair, the high-depth
fixture, and the squarefree/coprime double-divisor count at six specified
cutoffs. For example Q_390(4095)=961 is reused as a regression, not a new
discovery. The rational constant at alpha=1/4 is checked as 13/840 times
1/pi^2. No decimal fitting, probabilistic primality or floating sign test
is used. Running two implementations is not independent Referee acceptance
of an all-scale proof.

### F. Smallest Collision, Its Scope And Repair

At X=87283 the actual lists are

```text
c=17: J={59,61}, K={19,23};
c=19: J={59,61}, K={17,19,23}.
```

Both cofactors are squarefree and coprime to 390; each displayed edge is
squarefree, lies in (X/2,X], changes exactly three prime factors, preserves
greatest prime 61 and reverses -1 to +1. Both are unused by P9 (their
depths exceed two) and by R14 (neither endpoint is divisible by 13 or 15).
Nevertheless their donor is identical. The cofactor 19 is interchangeable
with donor factor 19 in the other presentation. Separate endpoint legality
therefore cannot justify the union.

The actual separated test keeps c=17 and excludes c=19 here:

```text
16*17^3=78608 <=87283; 16*19^3=109744 >87283.
```

Alternatively retain both sources and change ONLY c=17's donor to
71553=3*17*23*61. The standalone audit reconstructs all 15 local source
records and verifies that this one replacement yields 30 different legal
endpoints. The expanded-donor program separately obtains 15 matches for
15 sources from 33 available donors. Thus a fixed assigned-edge subgraph
has a two-sources/one-donor deficit, but the expanded graph does not.

Both programs exhaust every smaller integer X=4..87282 and find no
duplicate for the REGISTERED rule. Minimality concerns that exact sorted
band lift with min(J)>29 and the count/coprimality filters, not every
conceivable common-cofactor construction or arbitrary partial matching.
The previous X=145 failure concerns a different assertion and remains valid.

### G. Hidden Variables And Complete Signed Square

The operative hidden variable is **whether the original cofactor can be
recovered from the donor's factorization**. A donor representation can
exchange a prime inside c with r_i. Greatest-prime preservation and the
sign of each individual pair do not detect this collision. The separation
condition imposes a canonical factor ordering and prevents the exchange.

Let v be the total number of new disjoint pairs, let
`S=sum_(c,i<j)mu(c)`, and let Z be the signed final remainder. Unlike the
old c=1 packet, S is NOT necessarily v. All factor-depth signs remain:

```text
M(X)=S-S+Z;
M(X)^2=S^2+S^2+Z^2-2S^2+2SZ-2SZ=Z^2.
```

At X=1048575, v=190 but S=62: 126 source endpoints are positive and
64 are negative. The complete signed mass is Z=257 and Z^2=66049.
The final physical diagonal is D=126307; the exact UNORDERED
off-diagonal is C=-30129, giving D+2C=66049. Before this new stage,
D=126687 and C=-30319. Removing the matched sites changes both terms;
their negative interactions cannot be spent again as a global payment.

This is the true Mobius square, not empirical mean-centered covariance or
the clipped historical #915 NNS normalization. All cross-cofactor and
matched/remainder interactions are included before their algebraic cancellation.

### H. Finite Simultaneous Injection: Complete Proof Of HC2

Fix any X>=4 and take ALL cofactors meeting D's conditions and separation.
The band inequalities give, for each i<j,

```text
16X/25 < c*p_i*p_j <= 81X/100;
3X/5 < 3*c*r_i*p_j <= 243X/250 < X.
```

Thus both endpoints belong to the exact upper half. Separation gives

```text
every prime dividing c <= Pplus(c) <= (1/4)sqrt(X/c) < r_i < p_i < p_j.
```

Since gcd(c,390)=1, c contains none of 2,3,5,13. All listed factors are
distinct. Consequently mu(a)=mu(c), mu(b)=-mu(c), and their factor sets
differ precisely at {p_i,3,r_i}. Their greatest prime is p_j.

Source injectivity across ALL cofactors: p_i,p_j are the two largest
prime factors of a; deleting them recovers c. Their ordered values then
recover i,j in J_c. Donor injectivity: p_j,r_i are the two largest prime
factors of b; its factor 3 occurs once and is not in c. Deleting those
three factors recovers c, then r_i identifies i and p_j identifies j.
Source and donor populations cannot intersect because sources are not
divisible by 3 and donors are. Hence the entire union is a matching.

No endpoint is consumed by the factor-two pairing: both are odd upper-half
sites. If c>1, the source has at least three prime factors and the donor
at least four, so neither is a PE1 prime or semiprime. If c=1, the source
has two primes greater than 29, so it is not a P9 partner; the donor has
depth three. No new endpoint is divisible by 13 or 15, so none is an R14
endpoint. This proves simultaneous admission and exact old-mate preservation.

It follows for every such finite X that removing 2v distinct endpoints
preserves M(X) and the full square in G. A finite theorem does not assume
the prime-count condition always holds; failed packets are omitted. HC3
separately proves its eventual uniform availability on a prescribed subfamily.

### I. Counting The Growing Packet And Its Limitation

#### HC3: Uniform lower-scale cofactor family

Fix 0<alpha<1/3 BEFORE X. For all c<=X^alpha,

```text
16*c*Pplus(c)^2 <= 16*c^3 <= 16*X^(3alpha) <= X
```

eventually, including c=1 under its stated convention. Also y=X/c ranges
over [X^(1-alpha),X]. The ordinary prime number theorem applied to the
fixed macroscopic band endpoints gives UNIFORMLY throughout that range

```text
|J_c|=(1+o(1)) sqrt(y)/(5 log y),
|K_c|=(1+o(1)) 11 sqrt(y)/(50 log y).
```

Uniformity follows directly from the definition of the PNT limit: the
smallest argument is a constant times X^((1-alpha)/2), tending to infinity.
It does not invoke short-interval PNT or a modulus that grows with c.
The ratio tends uniformly to 11/10, and min |J_c| tends to infinity.
Hence every such squarefree coprime c eventually passes the count and
small-prime filters, and

```text
binom(|J_c|,2)=(1+o(1))*X/[50*c*log(X/c)^2]
```

with one uniform o(1). The external input is the established
[prime number theorem, DLMF 27.2.3](https://dlmf.nist.gov/27.2.E3).
Everything concerning this particular matching and its uniform cofactor
sum is derived here, not attributed to that reference.

For a fixed D=390, expand both squarefree and coprimality indicators:

```text
A(t)=sum_(c<=t, gcd(c,390)=1)mu(c)^2
 =sum_(d<=sqrt(t),gcd(d,390)=1)mu(d)
    *sum_(e|390)mu(e) floor(t/(d^2*e))
 =delta_390*t+O(sqrt(t)).
```

There are finitely many e; all floor errors and the absolutely convergent
d-tail cost O(sqrt(t)). The Euler product gives
`delta_390=zeta(2)^(-1)*(2/3)*(3/4)*(5/6)*(13/14)=65/(28*pi^2)`, using
[zeta(2)=pi^2/6, DLMF 25.6.1](https://dlmf.nist.gov/25.6.E1).
This counting lemma is inherited R14/C64 mathematics, not a new discovery.

Write L=log X, Y=floor(X^alpha). Partial summation, with the above error
and `(L-log t)>=(1-alpha)L`, now yields

```text
sum_(c<=Y,gcd(c,390)=1) mu(c)^2/[c*(L-log c)^2]
 =delta_390*integral_1^Y dt/[t*(L-log t)^2]+O_alpha(L^(-2))
 =delta_390*alpha/[(1-alpha)*L]+O_alpha(L^(-2)).
```

For clarity, the error integral is bounded by a constant times
`L^(-2)*integral_1^Y t^(-3/2)dt`; the endpoint error has the same or
smaller order. Replacing X^alpha by its integer floor changes only a
smaller endpoint term. Summing the uniform pair formula proves HC3.

In particular alpha=1/4 gives

```text
v_(1/4)(X) ~ 13/(840*pi^2) * X/log X,
removed endpoints ~ 13/(420*pi^2) * X/log X.
```

This is an all-sufficiently-large-X PAPER_PROOF, not an effective numerical
threshold or an asymptotic inferred from the finite table.

#### HC4: Why unrestricted cofactor depth is still insufficient

Let v_all(X) count ALL separated packets, with no c<=X^alpha restriction.
Every source a=c*p*q has p,q as its two largest primes and
`p<q<(9/8)*p`. This source restriction alone gives

```text
v_all(X)=O(X/log log X)=o(X).                         (HC4a)
```

Proof: set Y=(log X)/4. If p<=Y, every prime factor of the SQUAREFREE a
is <=9Y/8, so

```text
log a <= theta(9Y/8) <= 2*(9Y/8) = (9/16)*log X
```

eventually, by the elementary PNT consequence theta(t)~t. This contradicts
a>X/2 for large X. Thus every source has p>Y. Discarding the remaining
cofactor restrictions only increases its count, so

```text
v_all(X) <= X*sum_(p>Y, prime) (1/p)
                       *sum_(p<q<9p/8, prime) (1/q)
         << X*sum_(p>Y, prime) 1/[p*log p]
         << X/log Y = O(X/log log X).
```

The first prime upper bound follows from pi(t)<<t/log t. For the last,
split p into [2^jY,2^(j+1)Y): the contribution is
`O((log Y+j log 2)^(-2))`, whose sum is O(1/log Y).
The source injection from H prevents double-counting problems; this is
an upper bound on actual physical endpoints, not a random model.

This argument controls any matching whose source population has this same
near-equal-two-largest-primes restriction. It does NOT prohibit arbitrary
three-edit matchings, unequal-largest-factor packets, or signed estimates
on the residual. The particular constants are not being optimized.

R14's already independently reconstructed complete old remainder is
`157X/(84*pi^2)+O(X/log X)`. It can also be recovered directly from the
odd-squarefree upper-half count, the qualified 13/15 count, and the fact
that P9 removes at most O(X/log X) pairs. Combining HC4a with exact
once-only cardinality gives

```text
|R_final(X)|=157X/(84*pi^2)+O(X/log log X).            (HC4b)
```

Thus even the full separated union, not merely the alpha subfamily,
retains the old positive linear leading term. HC3 and HC4 are compatible:
they sandwich different aspects of a sublinear removable population;
no asymptotic equality is asserted for v_all.

### J. Proof Objective, Complete Return And First Missing Bound

The original `heathBrownLift_prefix_exact` identifies the coefficient at n
with mu(n) only for n<(N+1)^k. With N=B-1 and X<B^k, the inspected
coefficient-level bridge therefore transports any exact residual identity
from H to the original lift sum. Squareful fibers and ordered/binomial
copies are not reinterpreted as extra physical donors. This invocation
did not materialize the enormous raw lift tensor again; morning GM4's
unchanged raw-source tests are retained only at their documented scope.

One can first cancel opposite atoms within each finite physical n-fiber,
then pair its surviving representatives through HC2. A product involution
on the full ordered square flips the first nonfixed coordinate, otherwise
the second. This preserves both mixed orientations. It is a paper finite
construction, not a claim that main formalizes the new packet map.

The genuine quantitative MU-LIFT objective remains a whole-prefix
recurrence along an unbounded covered chain, for fixed k>=2 and 1<=r<k:

```text
E(B_j^k) <= G_j*E(B_j)^r,
E(B)=max_(1<=n<B)|M(n)|/sqrt(n),
G_j>=1, log(G_j)/log(B_j) -> 0.
```

Neither HC2 nor the growing count proves this. In fact, an absolute-value
finish using the final cardinality alone fails: E(B)<=sqrt(B-1) and
HC4b at X=B^k-1 imply, for any fixed C>0 and subpower G,

```text
|R_final(B^k-1)|/[C*G(B)*E(B)^r*sqrt(B^k-1)]
 >= const * B^((k-r)/2)/G(B) -> infinity.
```

This is NOT a lower bound on |M(X)|. The first missing ingredient is
genuine signed control of that linear remainder, or a substantially
broader packet family with a proved complete recurrence. Larger cofactor
depth inside the same near-equal-prime geometry cannot provide that alone.
Both endpoints remain positive-weight composite seats in native VF;
there is no sign-preserving identity transfer to original #915 payment.

### K. Falsification, Numerical Scope And Novelty Audit

H-LOCAL is REFUTED at its exact stated scope. H-SEPARATED passes the entire
declared finite domain and additionally has the elementary proof in H.
The quantitative candidate has the independent paper argument in I; it is
not promoted from finite data. HC4 is a later proof-derived limitation.

The greatest-prime-preserving three-edit map itself is inherited GM3.
The squarefree density, PNT, general matching principle and tensor
involution are also inherited tools. New relative to the inspected sources
and two-day reports are the specific duplicate-donor certificate, the
simultaneous recoverable-cofactor extension, its uniform growing-cofactor
count, and the explicit all-cofactor near-equal-prime coverage limit.
No exhaustive literature-priority claim is made.

No new full-graph Hall failure was found or claimed. No first-bad predicate
is being tested, and no local counterexample refutes the canonical theorem.
The X=145 frozen-matching obstruction is retained without repeating its
old minimality census. The high-depth fixture is separate from the main
finite domain. No floating-point approximation is used for a decision.

The infinity-scope arguments await independent mathematical review.
Source integrity, arithmetic tests, independent implementations and author
self-audit are different evidence categories. HC1-HC4 are NOT newly
PROVED_IN_LEAN. The source's existing green audit is not their certification.

### L. Two-Day Continuity And Specialist Handoffs

All seven roles' November 5 reports and available November 6 reports were
retrieved at the initial reporting snapshot. Applicable summaries,
source definitions, derivations, corrections and continuation sections
were read. Unrelated large numerical appendices were not rerun.

| Role | November 5 blob | November 6 intake blob |
| --- | --- | --- |
| Coordinator, equal 00/90 mirrors | be661bb2ed2830fc4aeddf14713455e550d982cc | ed98da5ddf755803c0fb9249ccf5bdb58f59658c |
| Owner | 39665b5b28fc48378519ab9d56cee8df4d3e2681 | fd30796d1b10e58e694f1d85252dac3cd8099a94 |
| Analytic | 9490aa2eecafcd19d8007043cc5f978fe421a7c9 | b075be67af6294e41f6eb232f611c208799c5e04 |
| Wheel | afc85d800c47f82f2db634591a7798005cb668de | be64667df80910bc9cc8fa3034aeeb579df5829a |
| Census | 24fcd6a631eca9ae44238d927215f49e1d8a174f | dfe20627512b4ad1fe62c83bbb2e0412390c100f |
| Referee | 789ed87021fe98963c244a8d0c9075638e76be43 | 01cf41cbc62f430f9034870509f6b3947866a4e9 |
| Lean | 5e0ecdd8f08c2e19b4614f00c1a5657f58722344 | 7138b713a44f514ade3a64db44268c1934b215d0 |

Coordinator's November 6 report is only PARTIAL: completed synthesis
TODAY=PENDING, YESTERDAY=CARRY_FORWARD. The other listed reports are
available at their individual evidence scopes, not blanket-endorsed.
No scheduled completion is inferred from a filename.

External inbox blob **038018145c0fddb2f6306c0712373adf9cd1ea52** has no
entry newer than October 18. Its prime-error, source-restoration and
conditional-first-bad safeguards remain applicable at their scopes;
none supplies a new norm bound here. Historical routing is superseded.

**Proof Architect:** consume HC1-HC4 as completion of the morning higher-depth
question. The packet count increases but the complete leading remainder
does not change. Do not count cofactor multiplication as new exponent gain
or assign a larger same-geometry census. C63-C66 and fixed-bank no-gos are
not refuted: the new rule explicitly edits large factors.

**Finite Wheel:** the now-ready MU-LIFT continuation is HC2's canonical
factor-order proof and HC4's coverage restriction. Test any broader
factor-ratio proposal against the 87283 donor swap and the 145 frozen
matching witness. Distinguish local assignments from simultaneous capacity.
The new PB1-PB4 prime-column correlation question is a different finite-C
carrier and remains unpaid; no result is transferred to it.

**Adversarial Referee:** independently check HC2's cross-cofactor recovery,
the J>29 and gcd390 exclusions, uniformity in HC3, the weighted partial
summation constant, and HC4's squarefree primorial argument. The repaired
15-source certificate must prevent overstatement as a Hall obstruction.
The current TD/CP review remains at its separate coherent-prefix scope.

**Lean Verification:** existing #1096 source evidence is verified and reused.
HC1 is a small exact duplicate-donor regression; HC2 is a finite candidate
only after independent qualification and utility review. Do not formalize
the all-scale count or norm conclusion by assuming its unproved supplier.
No new branch, PR or local compilation was created.

**Analytic Type II:** no signed-norm estimate follows from this injection.
Today's RM1-RM6 changed Nyman family still owes its middle return and new
low-coefficient arithmetic; FP1-FP5's phase averaging is distinct. A future
Census turn should switch to a precise changed hypothesis there or in
finite-C, rather than indefinitely supporting the same matching geometry.

**Owner Payment:** earlier RC/CR/MC and current BT/RZ/DR conclusions retain
their original weights and review status. Both HC endpoints are composites
in native VF, so their Mobius sign cancellation is not chronological
prime-seat payment. Donor recoverability is a useful structural question,
not a cross-carrier quantitative theorem.

### M. Ranked Experimental Hypothesis Portfolio

| Rank | Hypothesis and motivation | Evidence and counterevidence | Required new ingredient / disposition |
| --- | --- | --- | --- |
| 1 | A broader non-comparable-largest-factor packet can retain simultaneous donor capacity and cover more than the present near-equal-prime sources | HC2 proves one exact subfamily; HC4 proves its full coverage remains sublinear | New source bands and explicit donor-reservation theorem, with complete residual return. Revise, not scale the old census |
| 2 | Cofactor recovery is enough for collision-free union of the current separated maps | HC2 proof and 2051 exact dual-implementation cases; naive version fails at 87283 | Independent Referee review. Finite statement ready; no quantitative endpoint claim |
| 3 | Full three-edit graph achieves T3=|M(X)| | Morning finite evidence retained; HC1 only defeats a prescribed local assignment | Actual all-scale neighbor-capacity proof, which would still not bound M. Park, do not repeat the old scan |
| 4 | Repeated deeper cofactors in the present band can close by cardinality alone | HC4 proves the leading residual remains linear | Reject at this stated scope; seek signed remainder control or genuinely broader geometry |

### N. Next-Run Resume Capsule

```text
RUN: 20261106-census-2, scheduled 11:00:01 EST; RUN_ID_UNAVAILABLE.
MAIN: 4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a.
POLICY: NO_PIGEONHOLING_ROUTE_SELECTOR_V1 / SEARCH_BROAD.
TASK: MU-LIFT-HIGHER-DEPTH-DONOR-UNIQUENESS.
SOURCE: odd-boundary 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1;
  signed lift af69b4811cf9f523eb7c96fb0ca836b2cdbd1180.
RESUMED: 20261106-census-1/GM3 and its explicit higher-depth request.
HC1: first prescribed-lift collision X=87283, donor59109 shared by
  sources61183/68381, c17/c19; change first donor to71553 to repair.
  All lower X=4..87282 checked independently; not a general Hall failure.
HC2: require 16*c*Pplus(c)^2<=X; both endpoints recover c uniquely.
  Preserve P9 and qualified R14. c1 replaces GM3, never double-count it.
HC3: fixed 0<alpha<1/3, c<=X^alpha gives
  v_alpha~delta390*alpha/[50*(1-alpha)]*X/logX;
  alpha1/4 constant=13/(840*pi^2). Uniform PNT, not a finite fit.
HC4: all separated sources have top-two prime ratio<9/8;
  v_all=O(X/loglogX), final cardinality~157X/(84*pi^2).
  Pure absolute-remainder subcritical recurrence remains impossible.
HC5: 2051 cutoff rows byte-identical Python/C++; first-collision scan
  87280 cutoffs. Six extra depth5/6 pairs at X21445347, no full scan there.
FULL RETURN: M=S-S+Z; full square retained; S need not equal pair count.
REVIEW: new paper proofs SELF_AUDIT; independent Referee PENDING.
FORMAL: inherited #1096 merged-tree evidence verified; no new Lean proof.
NEXT SUPPORT ROUTE: prefer a concrete new NYMAN or FINITE-AC hypothesis,
  respecting broad support. Do not widen this completed matching scan.
NEXT MATCHING QUESTION: an explicit unequal-largest-factor packet with
  simultaneous donor capacity, not more cofactors inside the same band.
FIRST OPEN CONSUMER: full-prefix MU-LIFT signed recurrence, r<k and
  subpower loss on an unbounded covered chain, NOT just endpoint matching.
NET NEW ENDPOINT GAIN: UNKNOWN. Canonical VF and RH remain OPEN.
PUBLICATION: only today's own report on agent-reports; receipt follows.
```

### Reproducibility - This Invocation

Observed environment: Linux 6.18.57 x86_64, Python 3.12.14, g++ 13.3.0.
All inputs deterministic; no random seed, approximate primality or
floating-point sign decisions. Timings below are measured process durations,
not total invocation time. The main Python census took 1.735611256 seconds;
the independent C++ process reported 0.610854 seconds. The standalone
certificate script exited successfully; no separate runtime was recorded.

Executed commands, in a directory containing the code appended below:

```text
python cofactor_lift.py
g++ -std=c++17 -O2 -Wall -Wextra -pedantic cofactor_verify.cpp -o cofactor_verify
./cofactor_verify
cmp cofactor_rows.csv cofactor_cpp_rows.csv
python certificate_audit.py
sha256sum cofactor_lift.py cofactor_verify.cpp cofactor_rows.csv cofactor_cpp_rows.csv cofactor_result.json
sha256sum certificate_audit.py
```

Compilation completed without diagnostics; all checks exited 0.
`cmp` established exact equality of the full 2051-row, twelve-column tables.
The complete JSON is regenerated by the script; key exact certificates are
already displayed above. No separate experiment files are committed to the
repository: executable code is included only in this authorized report.

| Artifact | SHA256 |
| --- | --- |
| cofactor_lift.py | 815e550a53f6f664cd39456d66112a861f312b1022731ef2c6dd52b06ec1725f |
| cofactor_verify.cpp | f4b18d82c120ad6d470cef4bb35002bee48b66d459e5214d9e28f79ee8336fb4 |
| certificate_audit.py | 63ea697fdf60b1afb1e9b8a28315316555df8d2f4828cdff4d059450f3803d05 |
| Python and C++ complete row files, identical | 299ce4cb7c3a4903f66eb536f36394c619da217faad22b599d27ab4f6ad7b088 |
| cofactor_result.json, including measured elapsed time | e5e5d124e2632eb73f3a97e643b682a0625574c054f666fccfc6d4dea89c86ac |

The JSON hash includes elapsed time and is not expected to reproduce across
runs; the deterministic row hash and source hashes are the reproducibility
targets. The next sections preserve the exact executed source bytes.


### Executed Source - cofactor_lift.py

```python
"""Exact common-cofactor GM3 extension; all admission tests use integers."""

from bisect import bisect_right
from collections import Counter, defaultdict
from math import gcd, isqrt
from pathlib import Path
import hashlib
import json
import time


LIMIT = 1048575
DEVELOPMENT = list(range(4, 2049)) + [4095, 8191, 16383]
HELD_OUT = [65535, 262143, LIMIT]
P9 = (3, 5, 7, 11, 13, 17, 19, 23, 29)


def sieve(n):
    mu = [1] * (n + 1)
    mu[0] = 0
    largest = [1] * (n + 1)
    depth = [0] * (n + 1)
    primes = []
    for p in range(2, n + 1):
        if largest[p] != 1:
            continue
        primes.append(p)
        for k in range(p, n + 1, p):
            mu[k] = -mu[k]
            largest[k] = p
            depth[k] += 1
        for k in range(p * p, n + 1, p * p):
            mu[k] = 0
    return mu, largest, depth, primes


def bands(x, c, primes):
    jl = isqrt(16 * x // (25 * c))
    ju = isqrt(81 * x // (100 * c))
    kl = max(13, isqrt(x // (16 * c)))
    ku = isqrt(81 * x // (625 * c))
    j = primes[bisect_right(primes, jl):bisect_right(primes, ju)]
    k = primes[bisect_right(primes, kl):bisect_right(primes, ku)]
    return j, k


def records(x, mu, largest, primes, separated):
    out = []
    for c in range(1, 81 * x // (625 * 17 * 17) + 1):
        if not mu[c] or gcd(c, 390) != 1:
            continue
        if separated and 16 * c * largest[c] ** 2 > x:
            continue
        j, k = bands(x, c, primes)
        if len(j) < 2 or j[0] <= 29 or len(k) < len(j) - 1:
            continue
        for i, p in enumerate(j[:-1]):
            r = k[i]
            for q in j[i + 1:]:
                if gcd(c, p * q * r) != 1:
                    continue
                out.append((c, p, q, r, c * p * q, 3 * c * r * q))
    return out


def old_matching(x, mu, depth, primes):
    top = primes[bisect_right(primes, x // 2):bisect_right(primes, x)]
    partners = sorted(s * q for s in P9
                      for q in primes[bisect_right(primes, max(29, x // (2 * s))):
                                      bisect_right(primes, x // s)])
    assert len(partners) == len(set(partners))
    pairs = list(zip(top, partners))
    pairs += [(13 * c, 15 * c) for c in range(x // 26 + 1, x // 15 + 1)
              if mu[c] and gcd(c, 390) == 1 and depth[c] >= 2]
    endpoints = [n for pair in pairs for n in pair]
    assert len(endpoints) == len(set(endpoints))
    assert all(mu[a] == -mu[b] and x < 2 * a <= 2 * x and x < 2 * b <= 2 * x
               for a, b in pairs)
    return pairs, set(endpoints)


def trial_factors(n):
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def check_cutoff(x, mu, largest, depth, primes, mertens):
    rec = records(x, mu, largest, primes, True)
    used = set()
    old, old_sites = old_matching(x, mu, depth, primes)
    for c, p, q, r, a, b in rec:
        assert a not in used and b not in used and a != b
        assert a not in old_sites and b not in old_sites
        assert a % 2 == b % 2 == 1 and x < 2 * a <= 2 * x and x < 2 * b <= 2 * x
        assert mu[a] == mu[c] and mu[b] == -mu[c]
        assert largest[a] == largest[b] == q
        assert gcd(a, b) == c * q and a // gcd(a, b) == p and b // gcd(a, b) == 3 * r
        assert len(set(trial_factors(a)) ^ set(trial_factors(b))) == 3
        used.update((a, b))
    population = [n for n in range(x // 2 + 1, x + 1, 1) if n % 2 and mu[n]]
    remaining = [n for n in population if n not in old_sites and n not in used]
    assert sum(mu[n] for n in population) == mertens[x]
    assert sum(mu[n] for n in remaining) == mertens[x]
    assert len(remaining) == len(population) - 2 * len(old) - 2 * len(rec)
    s = sum(mu[a] for *_, a, b in rec)
    z = mertens[x]
    assert s * s + s * s + z * z - 2 * s * s + 2 * s * z - 2 * s * z == z * z
    assert (z * z - len(remaining)) % 2 == 0
    depths = Counter(depth[c] for c, *_ in rec)
    row = [x, len(population), mertens[x], len(old), len(rec),
           sum(c != 1 for c, *_ in rec), sum(c ** 4 <= x for c, *_ in rec),
           len({c for c, *_ in rec}), max(depths, default=0),
           len(remaining), (z * z - len(remaining)) // 2, s]
    return row, rec


def first_collision(mu, largest, primes):
    inspected = 0
    for x in range(4, 131072):
        rec = records(x, mu, largest, primes, False)
        seen = {}
        inspected += 1
        for e in rec:
            for endpoint in e[-2:]:
                if endpoint in seen:
                    return {"X": x, "endpoint": endpoint, "first": seen[endpoint],
                            "second": e, "cutoffs_checked": inspected,
                            "local_records": rec}
                seen[endpoint] = e
    return {"X": None, "cutoffs_checked": inspected}


def alternative_donors(x, rec, primes):
    # Supplementary test fixed before execution: is the collision a true capacity shortage?
    adj = defaultdict(set)
    for c, p, q, _, a, _ in rec:
        _, k = bands(x, c, primes)
        for r in k:
            if gcd(c, r) == 1:
                adj[a].add(3 * c * r * q)
    mates = {}

    def augment(a, seen):
        for b in sorted(adj[a]):
            if b in seen:
                continue
            seen.add(b)
            if b not in mates or augment(mates[b], seen):
                mates[b] = a
                return True
        return False

    for a in sorted(adj):
        augment(a, set())
    return {"sources": len(adj), "donors": len(set().union(*adj.values())),
            "matching_size": len(mates), "matching": sorted((a, b) for b, a in mates.items())}


def main():
    start = time.perf_counter()
    mu, largest, depth, primes = sieve(LIMIT)
    mertens = [0] * (LIMIT + 1)
    for n in range(1, LIMIT + 1):
        mertens[n] = mertens[n - 1] + mu[n]
    rows = []
    fixtures = {}
    for x in DEVELOPMENT + HELD_OUT:
        row, rec = check_cutoff(x, mu, largest, depth, primes, mertens)
        rows.append(row)
        if x in [145, 8191, 16383] + HELD_OUT:
            fixtures[x] = {"row": row, "depth_counts": dict(Counter(depth[c] for c, *_ in rec)),
                           "cofactor_counts": dict(Counter(c for c, *_ in rec)),
                           "first_high_depth": next((e for e in rec if depth[e[0]] >= 2), None),
                           "records": rec}
    collision = first_collision(mu, largest, primes)
    if collision["X"]:
        collision["alternative"] = alternative_donors(collision["X"], collision["local_records"], primes)
        for tag in ["first", "second"]:
            e = collision[tag]
            collision[tag + "_factors"] = [trial_factors(n) for n in e[-2:]]
    serial = "".join(",".join(map(str, row)) + "\n" for row in rows)
    Path("cofactor_rows.csv").write_text(serial)
    result = {"cutoffs": len(rows), "row_columns":
              "X,U,M,old_pairs,new_pairs,nonunit_c_pairs,quarter_pairs,cofactors,max_c_depth,residual,offdiag,source_signed_mass",
              "rows_sha256": hashlib.sha256(serial.encode()).hexdigest(),
              "fixture_rows": {x: d["row"] for x, d in fixtures.items()},
              "fixtures": fixtures, "collision": collision,
              "elapsed_seconds": time.perf_counter() - start}
    Path("cofactor_result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "fixtures"}, indent=2))


if __name__ == "__main__":
    main()
```


### Executed Source - cofactor_verify.cpp

```cpp
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <vector>

using I = long long;
using Record = std::array<I, 6>;
constexpr int LIMIT = 1048575;

struct Factor {
    int mu = 1;
    int omega = 0;
    int largest = 1;
};

Factor factor(int n) {
    Factor f;
    for (int d = 2; I(d) * d <= n; ++d) {
        if (n % d) continue;
        int e = 0;
        while (n % d == 0) { n /= d; ++e; }
        f.mu *= e == 1 ? -1 : 0;
        ++f.omega;
        f.largest = d;
    }
    if (n > 1) { f.mu *= -1; ++f.omega; f.largest = n; }
    return f;
}

std::pair<std::vector<int>, std::vector<int>> bands(I x, I c, const std::vector<int>& primes) {
    std::vector<int> j, k;
    for (I p : primes) {
        if (100 * c * p * p > 81 * x) break;
        if (25 * c * p * p > 16 * x) j.push_back(int(p));
        if (p > 13 && 16 * c * p * p > x && 625 * c * p * p <= 81 * x)
            k.push_back(int(p));
    }
    return {j, k};
}

std::vector<Record> records(I x, const std::vector<Factor>& f,
                            const std::vector<int>& primes, bool separated) {
    std::vector<Record> out;
    // A nonempty packet requires a donor prime at least 17.
    for (I c = 1; 625 * c * 17 * 17 <= 81 * x; ++c) {
        if (!f[c].mu || std::gcd(c, I(390)) != 1) continue;
        if (separated && 16 * c * f[c].largest * f[c].largest > x) continue;
        auto [j, k] = bands(x, c, primes);
        if (j.size() < 2 || j.front() <= 29 || k.size() + 1 < j.size()) continue;
        for (std::size_t i = 0; i + 1 < j.size(); ++i)
            for (std::size_t h = i + 1; h < j.size(); ++h) {
                I p = j[i], q = j[h], r = k[i];
                if (std::gcd(c, p * q * r) != 1) continue;
                out.push_back({c, p, q, r, c * p * q, 3 * c * r * q});
            }
    }
    return out;
}

std::set<I> old_sites(I x, const std::vector<Factor>& f, const std::vector<int>& primes) {
    std::vector<I> top, semis;
    for (I p : primes) {
        if (p > x) break;
        if (2 * p > x) top.push_back(p);
    }
    const std::set<int> small = {3, 5, 7, 11, 13, 17, 19, 23, 29};
    // Recover partners from physical sites, rather than multiplying prime tables.
    for (I n = x / 2 + 1; n <= x; ++n) {
        if (!(n % 2) || f[n].mu != 1 || f[n].omega != 2) continue;
        I q = f[n].largest;
        if (q > 29 && small.count(int(n / q))) semis.push_back(n);
    }
    std::set<I> used;
    for (std::size_t i = 0; i < std::min(top.size(), semis.size()); ++i) {
        assert(used.insert(top[i]).second);
        assert(used.insert(semis[i]).second);
    }
    for (I c = x / 26 + 1; 15 * c <= x; ++c)
        if (f[c].mu && f[c].omega >= 2 && std::gcd(c, I(390)) == 1) {
            assert(used.insert(13 * c).second);
            assert(used.insert(15 * c).second);
        }
    return used;
}

int main() {
    auto start = std::chrono::steady_clock::now();
    std::vector<Factor> f(LIMIT + 1);
    std::vector<int> primes;
    std::vector<I> mertens(LIMIT + 1);
    for (int n = 1; n <= LIMIT; ++n) {
        f[n] = factor(n);
        mertens[n] = mertens[n - 1] + f[n].mu;
        if (n >= 2 && f[n].largest == n) primes.push_back(n);
    }
    std::vector<I> cutoffs;
    for (int x = 4; x <= 2048; ++x) cutoffs.push_back(x);
    for (I x : {4095, 8191, 16383, 65535, 262143, LIMIT}) cutoffs.push_back(x);
    std::ofstream rows("cofactor_cpp_rows.csv");
    for (I x : cutoffs) {
        auto rec = records(x, f, primes, true);
        auto old = old_sites(x, f, primes);
        std::set<I> used, cofactors;
        I nonunit = 0, quarter = 0, maxdepth = 0, signed_source = 0, signed_donor = 0;
        for (auto e : rec) {
            auto [c, p, q, r, a, b] = e;
            assert(used.insert(a).second && used.insert(b).second);
            assert(!old.count(a) && !old.count(b));
            assert(a % 2 && b % 2 && 2 * a > x && 2 * b > x && a <= x && b <= x);
            assert(f[a].mu == f[c].mu && f[b].mu == -f[c].mu);
            assert(f[a].largest == q && f[b].largest == q);
            I d = std::gcd(a, b);
            assert(f[a].omega + f[b].omega - 2 * f[d].omega == 3);
            assert(d == c * q && a / d == p && b / d == 3 * r);
            cofactors.insert(c);
            nonunit += c != 1;
            quarter += c * c * c * c <= x;
            maxdepth = std::max(maxdepth, I(f[c].omega));
            signed_source += f[a].mu;
            signed_donor += f[b].mu;
        }
        I pop = 0, popsum = 0, residual = 0, total = 0, cross = 0;
        for (I n = x / 2 + 1; n <= x; ++n) {
            if (!(n % 2) || !f[n].mu) continue;
            ++pop;
            popsum += f[n].mu;
            if (old.count(n) || used.count(n)) continue;
            ++residual;
            cross += total * f[n].mu;
            total += f[n].mu;
        }
        assert(popsum == mertens[x] && total == mertens[x]);
        assert(residual + I(old.size()) + 2 * I(rec.size()) == pop);
        assert(residual + 2 * cross == total * total);
        assert(signed_source + signed_donor == 0);
        std::array<I, 3> groups = {signed_source, signed_donor, total};
        I full_square = 0;
        for (I a : groups) for (I b : groups) full_square += a * b;
        assert(full_square == mertens[x] * mertens[x]);
        std::array<I, 12> row = {x, pop, mertens[x], I(old.size() / 2), I(rec.size()),
                                nonunit, quarter, I(cofactors.size()), maxdepth,
                                residual, cross, signed_source};
        for (std::size_t i = 0; i < row.size(); ++i) rows << (i ? "," : "") << row[i];
        rows << '\n';
    }
    bool found = false;
    for (I x = 4; x <= 131071 && !found; ++x) {
        auto rec = records(x, f, primes, false);
        std::map<I, Record> seen;
        for (auto e : rec) {
            for (int k : {4, 5}) {
                auto it = seen.find(e[k]);
                if (it != seen.end()) {
                    std::cout << "FIRST_COLLISION " << x << ' ' << e[k] << '\n';
                    for (I z : it->second) std::cout << z << ' ';
                    std::cout << '\n';
                    for (I z : e) std::cout << z << ' ';
                    std::cout << '\n';
                    found = true;
                    break;
                }
                seen[e[k]] = e;
            }
            if (found) break;
        }
    }
    assert(found);
    auto sec = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    std::cout << "PASS " << cutoffs.size() << " cutoffs, independent trial factors, full cross sums\n";
    std::cout << "ELAPSED_SECONDS " << sec << '\n';
}
```


### Executed Source - certificate_audit.py

```python
"""Small standalone trial-division checks, with no imported sieve or census data."""

from fractions import Fraction
from itertools import combinations
from math import gcd
import json


def factor(n):
    out = []
    d = 2
    mu = 1
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            out.append(d)
            mu *= -1 if e == 1 else 0
        d += 1
    if n > 1:
        out.append(n)
        mu *= -1
    return out, mu


def bands(x, c):
    j, k = [], []
    for p in range(2, x + 1):
        if 100 * c * p * p > 81 * x:
            break
        if factor(p)[0] != [p]:
            continue
        if 25 * c * p * p > 16 * x:
            j.append(p)
        if p > 13 and 16 * c * p * p > x and 625 * c * p * p <= 81 * x:
            k.append(p)
    return j, k


def check_pair(x, c, p, q, r):
    a, b = c * p * q, 3 * c * r * q
    fa, ma = factor(a)
    fb, mb = factor(b)
    assert ma and ma == -mb
    assert x < 2 * a <= 2 * x and x < 2 * b <= 2 * x
    assert len(set(fa) ^ set(fb)) == 3
    assert max(fa) == max(fb) == q
    assert a % 13 and b % 13 and a % 15 and b % 15
    return {"endpoints": [a, b], "factors": [fa, fb], "signs": [ma, mb]}


def main():
    x = 87283
    assert bands(x, 17) == ([59, 61], [19, 23])
    assert bands(x, 19) == ([59, 61], [17, 19, 23])
    first = check_pair(x, 17, 59, 61, 19)
    second = check_pair(x, 19, 59, 61, 17)
    repair = check_pair(x, 17, 59, 61, 23)
    assert first["endpoints"][1] == second["endpoints"][1] == 59109
    assert repair["endpoints"][1] == 71553
    local = []
    for c in range(1, 81 * x // (625 * 17 ** 2) + 1):
        fc, mc = factor(c)
        if not mc or gcd(c, 390) != 1:
            continue
        j, k = bands(x, c)
        if len(j) < 2 or min(j) <= 29 or len(k) < len(j) - 1:
            continue
        for i, p in enumerate(j[:-1]):
            for q in j[i + 1:]:
                r = 23 if (c, p, q) == (17, 59, 61) else k[i]
                if gcd(c, p * q * r) != 1:
                    continue
                local.append(check_pair(x, c, p, q, r)["endpoints"])
    assert len(local) == 15 and len({n for e in local for n in e}) == 30
    high_c = 7 * 11 * 17
    high_x = high_c * 16383
    j, k = bands(high_x, high_c)
    assert (j, k) == ([103, 107, 109, 113], [37, 41, 43])
    assert 16 * high_c * max(factor(high_c)[0]) ** 2 <= high_x
    high = [check_pair(high_x, high_c, p, q, k[i])
            for i, p in enumerate(j[:-1]) for q in j[i + 1:]]
    assert len({n for e in high for n in e["endpoints"]}) == 12
    divisors = [d for d in range(1, 391) if 390 % d == 0]
    counts = {}
    for y in [1, 7, 11, 31, 468, 4095]:
        direct = sum(factor(n)[1] ** 2 for n in range(1, y + 1) if gcd(n, 390) == 1)
        inversion = sum(factor(d)[1] * sum(factor(e)[1] * (y // (d * d * e))
                                         for e in divisors)
                        for d in range(1, y + 1) if d * d <= y and gcd(d, 390) == 1)
        assert direct == inversion
        counts[y] = direct
    local_factor = Fraction(1)
    for p in [2, 3, 5, 13]:
        local_factor *= Fraction(p, p + 1)
    assert local_factor == Fraction(65, 168)
    # Multiplying by zeta(2)^(-1)=6/pi^2 leaves the displayed rational constants.
    delta_pi2 = local_factor * 6
    quarter_pairs_pi2 = delta_pi2 * Fraction(1, 4) / (50 * Fraction(3, 4))
    assert delta_pi2 == Fraction(65, 28)
    assert quarter_pairs_pi2 == Fraction(13, 840)
    print(json.dumps({"first": first, "second": second, "repair": repair,
                      "repaired_full_local_pairs": local, "high_depth_X": high_x,
                      "high_depth_c": high_c, "high_depth_pairs": high,
                      "squarefree_coprime_counts": counts,
                      "quarter_pair_constant_times_pi_squared": str(quarter_pairs_pi2)}, indent=2))


if __name__ == "__main__":
    main()
```


### Prepublication Freshness - 20261106-census-2

Observed at 2026-11-06 16:26:55 UTC: main is still
4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a. The agent-reports head is the
verified checkpoint commit 7c31c079056bc7b73400f2cf10aed6b1337cccb4;
therefore all other intake reports and the external inbox remain unchanged.
The sole open PR remains #1097 at bc727dc9f7dd655fdd2addc943b246ad70ef576d,
non-draft. No source dependency changed during this run.

### Verified Publication Receipt - 20261106-census-2

The complete new synthesis and all three executed source files were published
in commit **f71e32a087175113335a7b78c6aa465d021ec6b4**, content blob
**80c747ec40d8c654f2101d52cee1b76b8de373e2**. Commit inspection and
byte-identical pinned-file readback were complete by the observed clock
**2026-11-06 16:28:04 UTC (11:28:04 EST)**. The verified commit changes
ONLY research/agent_reports/2026-11-06/40-prime-census.md and preserves the
entire preexisting report and checkpoint. Its parent is the verified
checkpoint commit 7c31c079056bc7b73400f2cf10aed6b1337cccb4.

EXECUTION=COMPLETE; PUBLICATION=VERIFIED. HC1 is a scoped exact falsifier;
HC2-HC4 are PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING /
NOT_FORMALIZED; HC5 is FINITE_COMPUTATION. New net endpoint gain remains
UNKNOWN. No main, Lean source, other role report, policy, branch, PR, issue,
workflow, schedule, permission, merge or agent-launch action was taken.

### Finite Coverage Clarification - 20261106-census-2

The 2,051-row conservation table contains **five nonempty new separated
packets**, totaling **251 checked new pairs**; the other **2,046 cutoffs
have no new packet**. Empty cases test endpoint and full-source regressions,
not higher-depth cancellation evidence. The separate six-pair high-depth
fixture is additional and is not part of that table. These counts were
checked directly from the deterministic row file after publication.
The all-scale claims rely on the displayed paper proofs, not on treating
empty packet cases as substantive asymptotic evidence.


## Scheduled NYMAN Checkpoint - 20261106-census-3

Actual trigger: SCHEDULED 2026-11-06T19:00:01-05:00, America/New_York; RUN_ID_UNAVAILABLE. This is a third actual Census invocation, preserving the morning and midday histories. Status: PARTIAL / IN_PROGRESS. No new numerical result is asserted at this checkpoint.

Latest observed main: d4df133117c5b58f90979d2eb680167ef37995cf; intake reports head: 887aa0ff071229d5c6dc372fc2a6b822bf46a74a. Canonical VFCanonicalSquareVonKochStatement remains OPEN. AGENTS blob 48b2a58ab5fcd402321a4dace511c7d54bf688a1; contract blob 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c. baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1, policy blob 13d58dd12d90fbf1160812c7c93442dc5d0576ac; deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1. Existing native 7/8 and stronger strict-gap consequences are paid inputs, not new gains or missing reconstructions.

Selected independent route: NYMAN-FINITE-WINDOW-SIGNED-RETURN. Consume Coordinator 20261106-coordinator-1513/NS1-NS5, Analytic 20261106-analytic-2/RM1-RM6 and Referee 20261106-referee-7 through -11. Relevant same-day and preceding-day reports for all seven roles and the unchanged external inbox have been retrieved. All roles have a committed report today; no missing report is represented as a successful future execution. No open/draft PR was returned; #1099 is now merged. Current exact source blobs: NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean 2da630c1d5fb9302e2097ec1e170cf41c2b40609; NYMAN_FLAT_TAPER_RETURN_20261104.lean 2d23721027ecc44e85b7add02fc632b482f03352; NYMAN_MOMENT_NULL_OBSTRUCTION_20261106.lean 301d7286fc2151b5d33bdca9762a6a01c496ff87. No local Lean execution is permitted or planned.

### Preregistered Discriminator

For N=6K, H=floor(N^(4/5)) computed by integer fifth-root inequalities, 2<=H<=N/2, use every integer m in W_N=[K,3K). Let a_k=mu(k)log(H/k), f_k(m)=(m mod k)/k-(k-1)/(2k), S(m)=sum_(k<=H)a_k f_k(m), and mean_H=sum a_k(k-1)/(2k). The primitive reduced-denominator projector is

    P_d(m)=sum_(e|d) mu(d/e)*(e/d)*f_e(m).

The singleton band is L(m)=sum_(H/2<d<=H)mu(d)log(H/d)P_d(m); B(m)=S(m)-L(m). Retain Q(m)=m-psi(m)-log H-mean_H and the COMPLETE pre-correction numerator R(m)=Q(m)-L(m)-B(m). psi includes every prime power. The original energy is sum R(m)^2/[m(m+1)log(N/H)^2]. Also compute unweighted versions to distinguish normalization effects.

H-SPECTRAL: sum_W w(m)L(m)B(m)<=0 for every eligible N. Rival: finite-window phases allow either sign even though the two groups are orthogonal over complete periods.

H-PRIME: sum_W w(m)Q(m)S(m)>=0 for every eligible N. Rival: a favorable coefficient budget does not imply compensation with the actual prime residual. Test each with both w=1 and w=1/[m(m+1)]; a certified wrong sign refutes exactly that sign assertion, not a Nyman/RH theorem.

Development domain fixed before execution: all eligible multiples of six from 24 through 1536. Held-out N: 3072,6144,7776,8190,12288,24576,49152. Separate head cells m<=H from post-head cells; the late fixtures have H<K. Rank extremes without fitting an asymptotic exponent. Restore all six terms Q^2+L^2+B^2-2QL-2QB+2LB before interpreting energy. Check the full original residue family and all return terms on small anchors N=6,12,18,24 and H in {2,3,N/2}, with 1<=m<=3N, not only before correction admission. Complete-period orthogonality will be checked only on small exact periods, not used as a finite-window lower bound.

Implement a direct-modulo reference and a separately structured divisor-jump reconstruction; certify decision signs with outward enclosures or explicit rational log bounds, keeping floating diagnostics labeled. For important witnesses preserve source coefficients, endpoints and a standalone certificate. If the two reconstructions disagree, stop scaling and localize the first discrepancy. No conjectured universal sign or endpoint gain is assumed.
