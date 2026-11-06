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
