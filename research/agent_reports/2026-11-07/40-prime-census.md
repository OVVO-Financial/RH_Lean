# RH | Prime Census Laboratory - 2026-11-07

## Early Research Checkpoint - 20261107-census-1

Execution: PARTIAL / IN_PROGRESS. Actual scheduled trigger:
2026-11-07T03:11:01-05:00, America/New_York. RUN_ID_UNAVAILABLE.
No new mathematical result is claimed at this checkpoint.

### Authority And Continuity

Main: 1c057c1d65b6d4cb4d59d207f69a815c52353314; report intake: c5cadae097a0db84bfeda59cbec2320555814331.
AGENTS blob: 48b2a58ab5fcd402321a4dace511c7d54bf688a1.
CURRENT_PROOF_CONTRACT blob: 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c.
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1; policy blob
13d58dd12d90fbf1160812c7c93442dc5d0576ac.
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1; policy blob
ffd8f1c65cc4da656174956d4e03b48bea46768b.

Canonical target: VFCanonicalSquareVonKochStatement, exists C>=0 such
that for every integer R>=2, |pi(R^2)-VF_can(R^2)|<=C R log R.
The canonical bound remains open. Existing strict Mertens gains are
preserved. The selected matching experiment must improve an actual
source restriction; finite matching counts are not an exponent gain.

Retrieved both November 6 and all available November 7 role reports.
Today Owner SG, Analytic GL and Wheel DI are AVAILABLE; Coordinator,
Referee and Lean are TODAY=PENDING / YESTERDAY=CARRY_FORWARD. Today's
own report was absent. Equal November 6 Coordinator mirror blobs are
one source. External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52
contains no entry newer than October 18; historical routing is superseded.

Latest main human-merged #1100, Nyman radical increments. The sole open
PR at intake is policy proposal #1101, head
690477c55070aabafefbaff883880a5c37c44370; it is not main authority.

### Selected Question And Prior Work

Route: MU-LIFT, genuine oddSquarefreeUpper and greatest-prime fibers.
Resume 20261106-wheel-3/GF2-GF4 and the Coordinator's 23:09 continuation.
This diversifies from the completed Nyman sign census. Reuse the
X=145 and X=87283 obstructions without rerunning their scans.

Original source inspected:
research/MERTENS_ODD_BOUNDARY_PRIME_ESCAPE_20261105.lean,
blob 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1;
research/MERTENS_HEATH_BROWN_SIGNED.lean,
blob af69b4811cf9f523eb7c96fb0ca836b2cdbd1180;
research/oai_434/VF919NativeStrictMertens.lean,
blob b33a4883e1ddb0551b0f11f062bce46680d87450.

First independently reconstruct the requested X=9118,9215,9594
GF4 fixtures with genuine coefficients, all P9 and qualified 13c/15c
reservations. Then select and freeze a two-channel experiment before
its exhaustive scan. Potential channels use protected cofactors outside
P9. Record any exploratory selection separately from held-out tests.

### Competing Hypotheses

H1: physical endpoint disjointness plus individually favorable signed
label transfers suffices for additive improvement of the optimal
within-label absolute remainder Lambda.
H2: independently legal channels compete for the same signed label
surplus or demand even when their physical endpoints are distinct;
a simultaneous label-capacity condition is necessary.

Observable: exact Lambda before and after the union, actual net
cross-label flows, endpoint multiplicities, old reservations, and the
full original signed sum and square. Rejection: a fully admitted
endpoint-disjoint union whose improvement is smaller than the sum
of the independently measured improvements.

Methods planned: integer sieve and independent trial-factor/direct
enumeration; exact source sums and cross terms. Parameter ranges and
selected channel formulas will be recorded before the scan.
No floating sign decisions, fitting, artificial Mobius signs or local
Lean execution. Publication and independent acceptance remain pending.

### Complete Return And Next Step

The compiled odd-boundary sum equals M(X); the strict lift coefficient
bridge applies for X<B^k. Any new paired sites must preserve the complete
signed sum and ordered square, including all mixed terms. A small
labelwise remainder is still not the uniform subcritical recurrence
E(B^k)<=G E(B)^r, r<k, with subpower G and all-prefix coverage.

eta_gate=SEARCH_BROAD; net_endpoint_gain=UNKNOWN.
No other agent is launched. Only this own dated report will be written.

## Frozen Two-Channel Registration - 2026-11-07T08:18:05Z

Selection-stage disclosure: a direct trial-factor calculation of M(t) for
t<=222 was used to select explicit channels; it is exploratory, not
held-out confirmation. It gave M(94)=M(146)=1, M(95)=2,
M(43)=M(47)=-3. Protect the original P9={3,5,7,11,13,17,19,23,29}
prime/semiprime stage and all qualified 13c/15c pairs.

Freeze X>=147^2=21609. Let Q_m={q prime: m*q<=X<(m+1)*q}.
All source and donor greatest primes below are strictly above sqrt(X).
The original complete high-label mass is -M(m). Prior P9 removes only
eligible positive semiprimes; actual removed endpoints are retained.

D-demand test: independently pair increasing Q_146 and Q_47 by
93q <->31r (channel A), and 111q <->37r (channel B).
Both channels individually improve Lambda by two per edge. Test whether
the endpoint-disjoint union improves it by the sum of these gains.

D-supply test: pair Q_94 to Q_43 by 93q <->31r, and Q_146 to Q_43 by
111q <->37r. Use increasing lists independently, retaining actual
post-P9/R14 donor-label sums. Test the same additive claim.

Primary exhaustive range: every integer 21609<=X<=65535, with earliest
failure returned for each fixed rule. Held-out cutoffs: 65536,87283,
131071,262143. Do not change the rules after seeing failures.
Also independently reproduce GF4 at X=9118,9215,9594 and its changing
quotient boundary. No scan of the old X=145 or X=87283 counterexample
searches is requested.

Corrected candidate, fixed before the scan: joint per-label capacities.
For endpoint-disjoint directed edges from negative labels to positive
labels, conjecture the exact defect
  Lambda_after = Lambda_before - 2*edge_count
    + 2*sum_labels max(load(label)-abs(old_signed_mass(label)),0).
For a safe two-band construction, concatenate Q_94 then Q_146 and
assign distinct Q_43 labels, using 31r and 37r respectively, with
edge_count=min(|Q_94|+|Q_146|,|Q_43|).
Every Q_43 label has at least one positive unit after any permitted P9
spending. This construction REPLACES the GF4 stage on Q_94; it is not
added after those same 93q endpoints were spent.

Compute exact full-carrier Lambda and squares at material fixtures;
use the derived high-fiber representation for the exhaustive cutoff
scan and independently check it by trial-factor physical enumeration.
Capture complete signed return, residual diagonal, off-diagonal,
cross-label terms, exact factors, and old-reservation membership.
No claim about global matching impossibility or a new exponent follows.


## Final Research Synthesis - 20261107-census-1

This completes the scheduled 2026-11-07T03:11:01-05:00 invocation, America/New_York; RUN_ID_UNAVAILABLE. It is not an additional invocation. The checkpoint and preregistration above remain unchanged. New paper arguments are SELF_AUDIT, with independent Referee review PENDING and no new Lean formalization. Publication is verified separately after the actual write.

### A. Most Important Mathematical Discovery

**Disjoint physical endpoints do not imply additive improvement of the greatest-prime-label remainder. The scarce resource is signed surplus at each label, not the number of unused integers.** Both preregistered rules first fail at **X=21754**. Each component alone reduces the optimal within-label absolute remainder Lambda by two. Their four-endpoint union reduces it by only two, not four.

There are two distinct failures on genuine arithmetic. Removing two negative sites from the q=149 class overpays its one-unit negative imbalance. Removing two distinct positive sites from the r=499 class overuses its one-unit positive surplus. Neither failure duplicates a physical endpoint, violates a prime cutoff, nor reuses an old donor.

The complete accounting is

```text
Lambda_after = Lambda_before - 2*|E|
  + 2*sum_labels (load(label)-abs(old_signed_mass(label)))_+.
```

This formula applies to an endpoint-disjoint directed matching from negative labels to disjoint positive labels. It gives an exact necessary and sufficient capacity condition for the claimed full 2|E| improvement. A capacity-aware two-band construction restores that improvement, with every old reservation preserved. Its all-small-X full-coverage strengthening fails at X=22132; the correct theorem keeps the exact minimum of demand and available labels.

| Claim | Result | Mathematical status |
| --- | --- | --- |
| 20261107-census-1/SC1 | Earliest registered demand- and supply-overuse witnesses, both X=21754 | REFUTED additive assertion; FINITE_COMPUTATION |
| 20261107-census-1/SC2 | Exact overload formula; demand-overuse family with an X/log X-sized overcount | PAPER_PROOF; elementary accounting applied to this original carrier |
| 20261107-census-1/SC3 | Reserved, capacity-safe 94/146-to-43 transport; exact finite improvement and eventual fixed-band capacity | PAPER_PROOF |
| 20261107-census-1/SC4 | Independent GF4 reproduction, full signed-return checks, and identical two-language census | FINITE_COMPUTATION |
| 20261107-census-1/SC5 | Post-scan full-coverage obstruction at X=22132 | REFUTED all-small-X extension; FINITE_COMPUTATION |

No new Mertens exponent, canonical VF estimate, RH proof, or original clipped VF/NNS payment is established. Existing strict endpoint results remain established. eta_gate=SEARCH_BROAD; net_endpoint_gain=UNKNOWN.

### B. Current Authoritative Objective And Provenance

Pinned main: **1c057c1d65b6d4cb4d59d207f69a815c52353314**, observed after human merge of #1100. Report intake: **c5cadae097a0db84bfeda59cbec2320555814331**. Authority was fetched from the connected GitHub repository, not inferred from memory or reporting-branch policy copies.

The canonical theorem remains `VFCanonicalSquareVonKochStatement`: there exists C>=0 such that, for every integer R>=2, |pi(R^2)-VF_can(R^2)|<=C R log R. Its terminal classical interface retains `ClassicalVonKochRHCriterion` as an explicit argument. The canonical actual-prime bound remains open.

Established comparator: `native_mertens_fixed_strict_power` states an existing fixed strict improvement below 7/8, after spending part of the existing gap. The exact all-prefix signed energy consequence is not missing and is not reconstructed here. The matching certificate is a different sufficient approach: replacing the residual signed sum by its cardinality or labelwise l1 norm can be much weaker than the established envelope. Our improvement is an arithmetic allocation restriction, not a stronger exponent.

The selected original definitions were read: `oddSquarefreeUpper`, `semiprimeEscapePartners`, `sum_moebius_eq_oddSquarefreeUpper`, `prime_semiprime_residual_complete_square`, `heathBrownLift_sum_eq_prime_semiprime_residual`, `heathBrownLift`, and its strict prefix-exactness theorem. Source hashes are in the ledger below. No Lean source was modified or executed locally.

Formal evidence reused, not newly produced: at proof head **ecf701ff2fea1de52e505ee34048a2b3c220f0fc**, the live check collection returned 15 successful checks. The actual [odd-boundary audit job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42150511056/job/127672350630) was read. It checks synthetic merge **7783734bdc9960d3c2483af380759db85e87bc8f**, incorporating that head, with warning-fatal Lean and ten declaration/axiom audits. The terminal lists contain only propext, Classical.choice and Quot.sound; the static-partner lemma uses propext and Quot.sound. The main odd-boundary source equals the tested PR-head blob byte-for-byte. This supports the inherited finite interface, not SC1-SC5 or a new current-main build.

At intake, the only open PR was policy proposal #1101, head **690477c55070aabafefbaff883880a5c37c44370**. It was not used as merged authority. Recent accepted changes #1097, #1098, #1099 and #1100 concern CORR4 sampling, baseline instructions, the Nyman moment-null obstruction and radical increments. They do not supply the new matching-capacity estimate.

### C. Competing Hypotheses And Selection Discipline

The Coordinator's November 6 23:09 continuation requested independent GF4 fixtures and a source-defined two-band test. This run chose that mathematical opportunity rather than extending the already completed Nyman sign census.

H1 asserted additivity of individually favorable labelwise improvements when the physical edges are disjoint. H2 predicted coupled signed capacities at both source and donor labels. The observed discriminator was the exact Lambda change, not the number of pairs or a fitted exponent.

The constants were selected after an explicitly disclosed trial-factor exploration of M(t), t<=222. The exact rules, rejection criterion, exhaustive interval and held-out cutoffs were then committed in preregistration **020dd74d57f4fc95b811acc7e9d8ad81db905542**, blob **05e47b527586a8bff70a8223791c3f8d1278b95b**, before the main scan. Immutable readback matched. The later X=22132 capacity audit is labeled post-scan, not retroactively preregistered.

### D. Original Carrier And Experimental Methods

For integer X>=4, use unit genuine Mobius coefficients and the exact set

```text
U_X={n: 1<=n<=X, n odd, X<2n, mu(n)!=0}.
M(X)=sum_(n<=X) mu(n)=sum_(n in U_X) mu(n).
s_q(S)=sum_(n in S, Pplus(n)=q) mu(n),
Lambda(S)=sum_(q prime) |s_q(S)|.
```

Lambda is the sharp residual cardinality after unrestricted opposite-sign pairing WITHIN each greatest-prime label. It is a favorable relaxation of a restricted three-edit graph, not the complete global signed square or original zero-target NNS statistic.

The deterministic old stage sorts top-half primes and all eligible semiprimes s*q with s in P9={3,5,7,11,13,17,19,23,29}, q prime >29, X<2s*q<=2X; it pairs equal-ranked entries up to the shorter list. It also removes every qualified pair 13c/15c with X<26c, 15c<=X, mu(c)!=0, omega(c)>=2, gcd(c,390)=1. No earlier match is silently unfrozen.

All new endpoints have greatest prime greater than sqrt(X). Therefore any additional earlier matching confined to greatest primes at most sqrt(X), including a lawful separated HC2 packet, is disjoint and preserves all relevant high-label masses. It would also leave Lambda unchanged if it pairs opposite signs within each label. We did not rerun HC2's old collision search or certify a new implementation of it.

For q^2>X, t=floor(X/q), the exact full fiber is {q*c: c odd, t<2c<=2t, mu(c)!=0}, with mass -M(t). This is inherited arithmetic, not a new discovery. After the old stage, include the actual spent semiprime count; for quotient one also restore the removed negative top-prime contribution. The finite scan uses this exact representation. Material fixtures additionally enumerate the complete physical population directly.

Primary coverage: **every X from 21609 through 65535 inclusive**, 43927 cutoffs. Held out: **65536, 87283, 131071, 262143**, giving **43931** total rows. Strict endpoints are used throughout, including the exit at X=(m+1)q. Both source and donor primes exceed sqrt(X) on this domain.

Python builds genuine mu, largest-factor and depth tables by a multiplicative prime sieve. The separate C++ implementation obtains every integer's factorization by trial division and reconstructs label sums from actual odd cofactors, without reading Python tables or output. For full fixtures both enumerate integers and remove the original endpoints. The array bound is 262143; primality and factorization are deterministic and exact throughout. There is no probabilistic primality test, random seed, floating-point sign, logarithmic approximation or statistical fit.

### E. Executed Results

Both implementations produced **byte-identical 43931-row integer files**, SHA-256 **a40c5aa5b88a4a479022689d0505e507c5a1665cda367a30ee8e5074c0e11d91**. A separate comparison checked **62 complete physical-source statistic rows** field-for-field. Python performed 307566 local capacity-identity checks, 205003 legal-edge checks, 64652 directly reconstructed high fibers, 10000 sieve-versus-trial coefficient checks, and 46 independent endpoint-factor checks. Counts include repeated edges at different cutoffs and schemes, not 205003 distinct physical integers.

There were **33076 nonempty repaired rows**. Empty rows are included in the declared range rather than presented as positive evidence. The ordered convolution check independently reconstructed **195 coefficients** across (B,k)=(3,2),(4,3),(5,3), with strict X<B^k. This is coefficient-level validation retaining convolution multiplicity, not an enumeration of every raw binomial atom or a fresh proof of the compiled lift.

| X | M(X) | Old Lambda | Naive demand union gain | Naive supply union gain | Capacity-safe gain |
| --- | --- | --- | --- | --- | --- |
| 21609 | 7 | 791 | 0 | 0 | 2 |
| 21754 | 1 | 805 | 2, versus separately predicted 4 | 2, versus separately predicted 4 | 4 |
| 65535 | 14 | 2166 | 0 | 2 | 2 |
| 65536 | 14 | 2166 | 0 | 2 | 2 |
| 87283 | 34 | 2832 | 0 | 2 | 2 |
| 131071 | -20 | 4096 | 0 | 2 | 2 |
| 262143 | 24 | 7714 | 4, versus separately predicted 8 | 4, versus separately predicted 8 | 8 |

Requested GF4 fixtures were independently reproduced. At X=9118, Q94={97}, Q47={191,193}, the q=97 fiber has nine positive and ten negative sites, and 9021<->5921 changes Lambda 369->367 while M=3 and M^2=9 remain fixed. At X=9215, q=97 has moved to quotient 95, its fiber has nine positive and eleven negative sites, Q94 is empty, and M=-2. At X=9594, Q94={101}, Q47 is empty; no claimed all-X injection is available. These are verification of prior GF4 facts, not new findings.

### F. Exact Counterexamples And Boundary Cases

At **X=21754**, Q94={229}, Q146={149}, Q43={499,503}, Q47={457,461}. The last used sorted P9 donor is 19187. The old masses are s149=-1, s229=-1, s457=2, s499=s503=1. The old P9 stage has spent 29*457=13253, 23*499=11477, and 29*499=14471. These charges are indispensable: unspent positive sites do not recover their label's already spent surplus.

**Demand overuse (SC1-D).** The two individually favorable edges are

```text
13857 = 3*31*149  <-> 14167 = 31*457,
16539 = 3*37*149  <-> 16909 = 37*457.
```

All four sites are distinct and unspent. Each edge changes exactly three distinct prime factors and has signs (-1,+1). Separately each gives gain two. Together (s149,s457)=(-1,2) becomes (1,0), so the gain is only two. There is no physical donor collision; the negative label was overpaid.

**Supply overuse (SC1-S).** The two edges are

```text
21297 = 3*31*229  <-> 15469 = 31*499,
16539 = 3*37*149  <-> 18463 = 37*499.
```

Again all four sites are distinct and unspent. The masses (s229,s149,s499)=(-1,-1,1) become (0,0,-1). Their absolute sum falls from three to one, not by four. Two legal positive donor integers share only one unit of signed label surplus.

Both failures are first in the registered exhaustive range. In fact a high prime in Q146 requires q>146, so its smallest possible prime is 149 and X>=146*149=21754. Both mechanisms require that band. This explains the first admissible failure without extrapolation. At 21753 Q146 is empty; at 21755 the q=229 source leaves Q94. The exact moving boundary matters.

**A repair at the witness.** Keep 21297<->15469 and use 16539<->18611=37*503. The source labels 229 and 149 and the donor labels 499 and 503 are each used once. Lambda falls 805->801, the full predicted four units.

**Post-scan scope falsifier (SC5).** At X=22132, Q94={233}, Q146={151}, Q43={509}. The original residual masses are (-1,-1,+1). The two available donor sites 31*509=15779 and 37*509=18833 cannot both pay one unit of demand while retaining a two-per-edge Lambda improvement. A one-label reserved-capacity construction covers only one of the two sources. The scan found this as the first capacity shortage within its declared interval; standalone trial-factor enumeration verified it. This is not a Hall obstruction to every arithmetic matching or every other donor band.

### G. Hidden Variable And Complete Signed Reconstruction

The controlling variable is **remaining signed mass per greatest-prime label after old spending**. Endpoint-disjointness is necessary for a physical involution, but insufficient for additive improvement of Lambda. A source label's demand and a donor label's surplus are both capacities. Reserving an unused integer does not reserve an extra unit of its label's signed mass.

At X=21754 the complete post-old-stage source has 2057 unit entries, signed sum 1, unordered off-diagonal -1028, and square 1. Either two-edge union, and the capacity-safe two-edge repair, has 2053 entries and unordered off-diagonal -1026; the complete square remains 1 in every case.

| Source | Lambda | Sum of label squares | Ordered cross-label sum | Complete square |
| --- | --- | --- | --- | --- |
| Old residual | 805 | 5329 | -5328 | 1 |
| Demand-overuse union | 803 | 5325 | -5324 | 1 |
| Supply-overuse union | 803 | 5327 | -5326 | 1 |
| Capacity-safe repair | 801 | 5325 | -5324 | 1 |

Thus neither a smaller Lambda nor local opposite signs creates an extra reusable negative-square credit. If the selected negative endpoints sum to -e, positive endpoints sum to e, and all other entries sum to Z, then

```text
M(X)=-e+e+Z=Z,
M(X)^2=e^2+e^2+Z^2-2e^2-2eZ+2eZ=Z^2.
```

This is the complete signed square on the stated unit-weight carrier. It is not the masked/clipped #915 NNS source and supplies no weighted VF payment.

### H. Exact Capacity Law And Persistent Failure: SC2

Let S be a finite unit-sign arithmetic population. Let E be a physical endpoint-disjoint matching, all negative endpoints lying in labels with s_q(S)<0 and all positive endpoints in disjoint labels with s_r(S)>0. Let ell_v count the number of removed sites at label v. No label serves both roles. Then removing negative sites raises its signed mass by ell_v, while removing positive sites lowers it by ell_v. For a positive integer a,

```text
a-|a-ell| = ell-2*(ell-a)_+.
```

Apply this with a=|s_v(S)| at every touched label and use sum_v ell_v=2|E|. This proves the displayed SC2 identity. In particular the full 2|E| improvement holds **if and only if every load is at most its old signed capacity**. This elementary l1 calculation is not claimed as new generic combinatorics. Its explicit arithmetic application, the two missed resources and the fully admitted witnesses are the new contribution relative to the inspected handoffs.

For the registered demand rule, put N=min(|Q146|,|Q47|), at any X>=21609. Every selected q has old mass -M(146)=-1; no P9 cofactor can enter its upper-half fiber. Every selected r in Q47 has original mass three and loses at most the P9 cofactor 29, leaving at least two. Qualified 13c/15c pairs preserve these high labels and cannot use the displayed endpoints. Consequently each separate channel improves Lambda by 2N, whereas their union improves it by **exactly 2N**, not 4N. This is a paper proof for all such X, not an inference from the finite table.

For fixed quotient m, ordinary PNT gives |Q_m|~X/[m(m+1)log X]. Hence eventually N=|Q146|, since the donor/source density ratio is 21462/2256>1. The additive overcount is therefore

```text
2N ~ 2X/(21462 log X) = X/(10731 log X).
```

This is an X/log X-sized error in the proposed labelwise certificate, not a lower bound on |M(X)|. The asymptotic input is the established [prime number theorem, DLMF 27.2.3](https://dlmf.nist.gov/27.2#E3), not a short-interval conjecture. Only finitely many fixed relative endpoints are used; no growing-band uniformity or effective threshold is asserted.

### I. Capacity-Safe Two-Band Theorem: SC3

For every integer X>=21609, let Q94,Q146,Q43 be the exact prime bands above. Start from any permitted P9 prime/semiprime matching, all or any disjoint qualified 13c/15c pairs, and any previous opposite-sign low-greatest-prime matching. Reserve the new endpoints before any other arbitrary high-label matching. Set

```text
N=min(|Q94|+|Q146|, |Q43|).
```

List Q94 first and Q146 second; assign distinct Q43 labels to the first N sources. For q in Q94 use 93q<->31r; for q in Q146 use 111q<->37r. Then every edge is physically admitted, has opposite Mobius signs and changes exactly three prime factors; all endpoints are distinct and avoid the previous stages. The complete signed sum is unchanged and

```text
Lambda_after = Lambda_before - 2N.
```

Proof of the source facts: X>=147^2 and q>X/147 ensure every Q146 source is above sqrt(X); Q94 and Q43 satisfy stronger root-wall inequalities. The endpoints 93q and 111q lie strictly above X/2 and at most X in their respective bands. The same holds for 31r and 37r in Q43. All factors are distinct and the greatest prime is the displayed label. A source has three prime factors, a donor two. Within each side, unique factorization prevents a collision between the 31 and 37 channels.

Neither new endpoint is a top prime or an old P9 semiprime. None is divisible by 13 or 15. Low-label packets cannot reach them. Each source label has exact mass -1 because M(94)=M(146)=1 and its eligible cofactors exceed 29. A Q43 donor has mass three before P9; the only eligible P9 cofactors are 23 and 29, so its remaining mass is at least one. High-label 13/15 cancellation changes neither mass. Since each selected source and donor label is used only once, SC2 gives the exact improvement.

The fixed-band demand density is 1/8930+1/21462=7598/47913915. The supply density is 1/1892, with ratio **47913915/14375416>1**. PNT therefore proves complete coverage of these two source bands for all sufficiently large X, without an explicit threshold. The exact finite minimum is indispensable at X=22132.

This combined stage **replaces**, rather than follows, GF4 on the already-used Q94 endpoints. It is not claimed to extend every arbitrary frozen high-label matching. Its density improvement is a fixed-band component, not a subcritical MU-LIFT estimate.

### J. Proof Impact And First Missing Estimate

GF2's necessary favorable cross-label flow survives. SC1 shows that physical edge disjointness and individual positive improvement are not enough to realize the sum of those improvements. SC2 supplies the additional exact accounting; SC3 realizes one properly budgeted multi-band component.

The original complete quantitative target remains a genuine whole-prefix recurrence on a covered chain: fixed k>=2, fixed 1<=r<k, G_j>=1 with log G_j/log B_j->0, and E(B_j^k)<=G_j E(B_j)^r, where E(B)=max_(1<=n<B)|M(n)|/sqrt(n). For k=2 this must cover every B_j<=X<B_j^2 and all signed floor rows. The compiled coefficient bridge does not prove that norm inequality.

For this matching approach, the first missing structural step is a simultaneous growing collection of source and donor bands with both physical endpoint uniqueness and signed label capacities, plus a quantitative bound on the entire remaining signed source. Paying a necessary flow alone is not sufficient. The new finite capacity identity is not an assumption that the complete demand is feasible; the two fixed bands do not improve the existing exponent. A signed recurrence may bypass an absolute matching certificate entirely.

### K. Falsification, Independence And Execution Audit

The two central additive assertions are refuted on their exact registered original carrier. GF4 is confirmed at the requested finite fixtures, not newly proved by computation. The general capacity and safe-transport arguments are PAPER_PROOF, not Lean-certified. Separate implementations provide independent computational reconstruction; the author and paper self-review remain the same session, not independent Referee acceptance.

Environment observed: Python **3.12.14**, g++ **13.3.0**, Linux x86_64. The Python runtime version is the observed executable output, not the approximate environment description. C++ flags: `-std=c++17 -O2 -Wall -Wextra -Werror`; assertions remain enabled. Successful main Python elapsed time: **2.719475126 seconds**; C++ self-measured **1.01652 seconds**. These are measured individual runs, not total session time or comparative benchmarks. All arithmetic assertions are exact integers/rationals; timestamps and timings alone use ordinary clock values.

Two implementation events are retained. The first Python scan was deliberately interrupted to replace a linear-list membership check by set membership; no partial result from it was promoted. The next run's complete-carrier validation caught a missing quotient-one restoration for top primes removed by P9. That was a verifier-accounting bug, not a mathematical counterexample: it was corrected explicitly, followed by a complete rerun and independent physical-source comparison. The tested 43/47/94/146 bands were not changed, and no failed row was dropped.

The standalone post-scan audit uses only trial division and direct integer populations, checks the boundary neighbors 21753/21755, the spent P9 donors, cofactor lists, and X=22132. Its selection is transparently post-scan. No probabilistic significance, asymptotic fit, optimal universal constant, or absence of all other matching obstructions is inferred.

### L. Continuity And Specialist Handoffs

All available November 7 and all November 6 role reports were retrieved at the pinned report snapshot. Applicable summaries, handoffs, review state and the selected GF derivation were read. Unrelated executable appendices were not all rerun or certified. Today's Owner SG, Analytic GL and Wheel DI are available; Coordinator, Referee and Lean remain TODAY=PENDING with YESTERDAY=CARRY_FORWARD at intake. Their future scheduled times do not count as executed work.

Owner SG supplies a scoped large-GCD restriction, not a universal favorable sign. Analytic GL isolates a large-GCD support cost but retains the small-GCD signed complement. Wheel DI supplies genuine overlap/sign counterexamples and a proper divisor sector. None is identified with this MU-LIFT carrier. Yesterday's own GM/HC and FW results retain their exact scopes; old first-collision scans were not repeated. The latest Coordinator specifically requested the GF fixtures and a two-band test. Yesterday's Referee and Lean Nyman review/implementation are continuity, not acceptance of SC1-SC5.

The external inbox has no entry newer than October 18. Carry forward the source and cutoff safeguards of EXT-20261018-PNT-1, EXT-20261017-XCOORD-1 and EXT-20261014-5 at their original scopes. Their old routing/cadence wording does not override current main, and they provide no new matching-capacity supplier.

**Proof Architect:** replace endpoint-disjoint-only multi-band improvement with a two-sided signed-capacity requirement. SC1 is a decisive genuine-carrier falsifier; SC3 is a proper corrected component. Do not count it as VERIFIED_ETA or make it a team-wide single route.

**Finite Wheel:** independently audit the old P9 spending at r=499, the source overpayment at q=149, and the X=22132 finite shortage. Resume multi-band transport with capacities at both ends; do not add SC3 on top of already-spent GF4 endpoints.

**Adversarial Referee:** verify the exact four-site examples before relying on the proof, then test SC2's disjoint-role hypothesis, strict root walls, M(43)/M(146), R14 preservation and the PNT order of limits. No independent acceptance has been preassigned.

**Analytic Type II:** signed-label saturation is a bookkeeping restriction, not a new all-prefix bound. A genuinely signed global recurrence remains a distinct option; no OAI or CODIV transport is asserted.

**Owner Payment:** unused occurrence capacity and remaining signed-class surplus differ. The unit-weight result cannot pay a weighted/clipped VF source without an actual source map and restored terms.

**Lean Verification:** the existing #1096 interface is reused and unchanged. No proof branch or speculative formalization is requested. If independently accepted and useful to a live argument, the finite capacity-safe source theorem is the relevant new statement; a generic l1 wrapper alone is not an endpoint advance.

These handoffs are published in this own report only. No other agent was launched, and no issue, PR, branch, workflow, policy, schedule or other role's report was modified.

### M. Ranked Experimental Hypothesis Portfolio

| Candidate | Evidence and counterevidence | Independent ingredient / next discriminator | Disposition |
| --- | --- | --- | --- |
| Two-sided signed-capacity accounting on genuine label transfers | Exact SC2 identity; two first-failure witnesses; all declared checks pass | Genuine old signed masses, not vertex counts; audit growing overlapping band allocations | Promote as required local accounting, not a bound |
| Capacity-safe 94/146-to-43 source repair | Finite exact theorem plus fixed-endpoint PNT; X=22132 forbids all-small-X full coverage | Unspent 31/37 factors and Q43 remaining surplus; independently review the full finite statement | Continue at proper-component scope |
| Endpoint-disjoint component improvements add automatically | REFUTED twice at X=21754 and at held-out X=262143 | Source and donor loads can exceed their signed capacities without vertex collision | Reject precisely this assertion |
| Complete growing-band transport yields a subcritical norm recurrence | No proof; fixed-band improvements and necessary flow do not control the complete return | Uniform allocation with full residual and all-prefix losses; seek first capacity min-cut on a declared growing family | Open; do not assume |
| More Nyman favorable-sign samples or unchanged HC collision scans | Existing findings available; no new discriminator for this run | Need a changed weighted source or quantitative prediction first | Suspend repetition, preserve prior results |

### N. Next-Run Resume Capsule

```text
RUN: 20261107-census-1; scheduled 03:11:01 EST; RUN_ID_UNAVAILABLE.
MAIN: 1c057c1d65b6d4cb4d59d207f69a815c52353314.
REPORT_INTAKE: c5cadae097a0db84bfeda59cbec2320555814331.
BASELINE_ACK: PAID_BASELINE_EXACT_CONSUMER_V1.
DEPLOYMENT_ACK: NO_PIGEONHOLING_ROUTE_SELECTOR_V1.
ROUTE: MU-LIFT; original odd upper-half Mobius source and prime labels.
INHERITED: GF2-GF4, P9/R14 reservations, -M quotient law, strict lift bridge.
NEW: SC1 X=21754 demand/supply overuse with disjoint physical endpoints;
     SC2 exact overload penalty and persistent demand family;
     SC3 capacity-safe two-band replacement;
     SC5 X=22132 finite full-coverage shortage.
COMPLETED: 43931 identical rows; 62 identical full physical-source rows;
           GF4 fixtures; boundary and independent trial certificates.
ROW_SHA256: a40c5aa5b88a4a479022689d0505e507c5a1665cda367a30ee8e5074c0e11d91.
REVIEW: SELF_AUDIT; independent Referee PENDING; no new Lean theorem.
FIRST OPEN: capacity-faithful growing-band allocation plus complete
            signed residual control, not another fixed-band count.
NEXT DECISIVE EXPERIMENT: on a newly declared finite growing quotient
 family, compare maximum feasible directed flow with both label capacities
 against physical-site-only matching; preserve every old reservation.
 Return the first exact deficient label set or a checked capacity theorem,
 rather than extending today's fixed formulas to fit a power.
NEXT SUPPORT ROUTE: select from live ready SAT/CODIV/CORR4 hypotheses
 if more consequential; do not keep Census permanently on MU-LIFT.
ETA_GATE: SEARCH_BROAD; net_endpoint_gain=UNKNOWN.
NO NEW VERIFIED ENDPOINT GAIN; canonical VF and RH remain OPEN.
```

### Reproducibility

The following four scripts are the executed final sources. They are embedded because remote permissions permit only this report, not arbitrary experiment-file commits. The independent C++ process reads no Python data. The comparison script runs only after both reconstructions are complete.

```sh
python label_capacity.py
g++ -std=c++17 -O2 -Wall -Wextra -Werror label_capacity_reference.cpp -o label_capacity_reference
./label_capacity_reference
cmp capacity_rows.csv capacity_cpp_rows.csv
python compare_capacity.py
python certificate_audit.py
```

Generation uses integer tables of size O(LIMIT), plus 43931 compact result rows. The main scan evaluates only the fixed prime bands rather than rebuilding all O(X) populations for every X. Direct O(X) physical reconstruction is reserved for material fixtures. C++ trial factoring is a deliberately independent, bounded-domain reference. The scripts generate CSV/JSON scratch artifacts for verification; no spreadsheet analysis or fitted growth model is used.

### Material Source Ledger

Source files are pinned to main [1c057c1d65b6d4cb4d59d207f69a815c52353314](https://github.com/OVVO-Financial/RH_Lean/tree/1c057c1d65b6d4cb4d59d207f69a815c52353314). These are retrieved file blobs, not invented checksums or new build certificates.

| Source | Blob SHA |
| --- | --- |
| AGENTS.md | 48b2a58ab5fcd402321a4dace511c7d54bf688a1 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| docs/RHLEAN_PAID_BASELINE_EXACT_CONSUMER_20261106.md | 13d58dd12d90fbf1160812c7c93442dc5d0576ac |
| docs/RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md | ffd8f1c65cc4da656174956d4e03b48bea46768b |
| docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md | 973d3d549a52a1afe2f02bfdcf8cc35fb6a76515 |
| docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md | 8317f08996b65f2e4b32c00c91b31cb6d0c09718 |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 4775ee5fd95f279beab08a75d1e17127078b19a6 |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 6c1d1c10e2755017ffe9d7f40df8b9ae7692f23a |
| docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md | 53143573cd5b014178d11ded008dbfb1a7e6dcc5 |
| docs/DYNAMIC_RESEARCH_AGENTS.md | 23b6fae1d3b6b5a69155628df709d255aea7aeca |
| research/MERTENS_ODD_BOUNDARY_PRIME_ESCAPE_20261105.lean | 3cbc5159536d6b9e5000f74c5bd018bd2d62daf1 |
| research/MERTENS_HEATH_BROWN_SIGNED.lean | af69b4811cf9f523eb7c96fb0ca836b2cdbd1180 |
| research/MERTENS_FINITE_PREFIX_EXTENSION.lean | 131e9af86207a42d4bf6488e3f64c9ce4f97e5df |
| RHLean/Proof/RootWallCompleteFibre.lean | 054694c0aa125e6f542a3208d85d30c2d79fb320 |
| RHLean/Analysis/DyadicTransportCanonicalForm.lean | 90df0b8187f628b4f4e886a1271955955245b8a6 |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |

### Two-Day Report Ledger

Pinned intake: agent-reports@c5cadae097a0db84bfeda59cbec2320555814331. These are continuity sources, not blanket independent acceptance of their contents.

| Role | November 6 blob | November 7 intake blob / status |
| --- | --- | --- |
| 00-coordinator-am | 8812a90540fb511279b5f4ce08e108ef717d5ef1 | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |
| 10-owner-payment | 1856a96aaaa9d86a5ee2d59ffe50ced936443fa6 | 1006bb9f0c61a22ceeb7fab25d177a40dc24f25e |
| 20-analytic-type-ii | 7997620b6ab7eb0701296994734ee910df3c3ba1 | 6712040159ca37ef3257cf507ec8198fd26fbb91 |
| 30-finite-wheel | 3099558194a00358962ff1844bf283e625b9283d | b943f16b0fedbcefa53545f8a7c77482e688399e |
| 40-prime-census | c34ac074296e8b2e5b20dee3a2ce02518571206c | ABSENT before this invocation |
| 50-adversarial-referee | da3265467c799e9d21832ab25245617ba3b15a54 | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |
| 60-lean-verification | b8bfe3ce9c20d7903395364efb39bcec974c8a2f | TODAY=PENDING; YESTERDAY=CARRY_FORWARD |

The November 6 00/90 Coordinator mirror blobs both equal 8812a90540fb511279b5f4ce08e108ef717d5ef1. External inbox: 038018145c0fddb2f6306c0712373adf9cd1ea52. Latest applicable Coordinator synthesis is the actual 23:09 EST continuation, not the earlier partial checkpoint; Wheel GF is its actual 18:06 EST continuation. Prior Census runs were 03:11/11:00/19:00 EST on November 6, with FW3 subsequently implemented in merged #1100. Today Owner, Analytic and Wheel report completed publication receipts at 05:32:37Z, 06:26:05Z and 07:43:16Z respectively. Those are upstream recorded receipts, not new executions by this agent.

### Executed Source Manifest

| File | SHA-256 |
| --- | --- |
| label_capacity.py | d4fc5b86b01c4b7e64880e40e342361844a4ad1e83410ace8585042385275d28 |
| label_capacity_reference.cpp | 221bc73794507258ced8a580a768e356b20e5162c63aafaf88d6e758f93fb9da |
| compare_capacity.py | 2e75c1972f3f2698f5eddd706e0416d9d80036f26df69c66304891f908f5e178 |
| certificate_audit.py | fe6cc499bf0b53b0b092d8771fe688f1c1165251bbc9ca4c2666adb3d24626e5 |

#### label_capacity.py

```python
"""Exact, source-faithful two-channel MU-LIFT experiment. No fitted powers."""

from bisect import bisect_right
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from math import gcd, isqrt
from pathlib import Path
import json
import time

P9 = (3, 5, 7, 11, 13, 17, 19, 23, 29)
LOW, HIGH = 147**2, 65535
HELD = (65536, 87283, 131071, 262143)
LIMIT = max(HELD)


def sieve(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    largest = [1] * (limit + 1)
    omega = [0] * (limit + 1)
    primes = []
    for p in range(2, limit + 1):
        if largest[p] != 1:
            continue
        primes.append(p)
        for n in range(p, limit + 1, p):
            mu[n] = -mu[n]
            largest[n] = p
            omega[n] += 1
        for n in range(p * p, limit + 1, p * p):
            mu[n] = 0
    mertens = [0]
    for value in mu[1:]:
        mertens.append(mertens[-1] + value)
    return mu, largest, omega, primes, mertens


def trial(n):
    factors = []
    squareful = False
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            n //= d
            if n % d == 0:
                squareful = True
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return (0 if squareful else (-1) ** len(factors)), factors


def run():
    start = time.perf_counter()
    mu, largest, omega, primes, M = sieve(LIMIT)
    # The global ordered list permits exact moving P9 admission by two bisections.
    semis = sorted(s * q for s in P9 for q in primes if q > 29 and s * q <= LIMIT)
    assert len(semis) == len(set(semis))
    semi_set = set(semis)
    checks = Counter()
    for n in range(1, 10001):
        v, fs = trial(n)
        assert (v, fs[-1] if fs else 1) == (mu[n], largest[n])
        checks['trial_sieve_checks'] += 1

    def band(x, m):
        return primes[bisect_right(primes, x // (m + 1)):bisect_right(primes, x // m)]

    def old_threshold(x):
        a, b = bisect_right(semis, x // 2), bisect_right(semis, x)
        top_count = bisect_right(primes, x) - bisect_right(primes, x // 2)
        k = min(top_count, b - a)
        return semis[a + k - 1] if k else 0

    def mass(x, q, threshold):
        assert q * q > x
        value = -M[x // q] - sum(x < 2 * s * q and s * q <= min(x, threshold) for s in P9)
        if x < 2 * q:
            removed = bisect_right(semis, threshold) - bisect_right(semis, x // 2) if threshold else 0
            top_start = bisect_right(primes, x // 2)
            value += int(removed > 0 and q <= primes[top_start + removed - 1])
        return value

    def schemes(x):
        q94, q146, r43, r47 = (band(x, m) for m in (94, 146, 43, 47))
        da = [(93 * q, 31 * r, q, r) for q, r in zip(q146, r47)]
        db = [(111 * q, 37 * r, q, r) for q, r in zip(q146, r47)]
        sa = [(93 * q, 31 * r, q, r) for q, r in zip(q94, r43)]
        sb = [(111 * q, 37 * r, q, r) for q, r in zip(q146, r43)]
        assigned = [(q, 93, 31) for q in q94] + [(q, 111, 37) for q in q146]
        repair = [(a * q, b * r, q, r) for (q, a, b), r in zip(assigned, r43)]
        return {'demand_a': da, 'demand_b': db, 'demand_union': da + db,
                'supply_a': sa, 'supply_b': sb, 'supply_union': sa + sb,
                'repair': repair}, [len(q94), len(q146), len(r43), len(r47)]

    def local(x, edges, threshold):
        sites = [n for edge in edges for n in edge[:2]]
        assert len(sites) == len(set(sites))
        source, donor = Counter(e[2] for e in edges), Counter(e[3] for e in edges)
        assert not (source.keys() & donor.keys())
        old = {q: mass(x, q, threshold) for q in source.keys() | donor.keys()}
        assert all(old[q] < 0 for q in source) and all(old[r] > 0 for r in donor)
        new = {q: v + source[q] - donor[q] for q, v in old.items()}
        gain = sum(abs(v) for v in old.values()) - sum(abs(v) for v in new.values())
        overload = sum(max(source[q] + donor[q] - abs(v), 0) for q, v in old.items())
        assert gain == 2 * len(edges) - 2 * overload
        for a, b, q, r in edges:
            assert mu[a] == -1 and mu[b] == 1
            assert x < 2 * a <= 2 * x and x < 2 * b <= 2 * x
            assert largest[a] == q and largest[b] == r and q * q > x and r * r > x
            assert a not in semi_set and b not in semi_set
            assert all(n % 13 and n % 15 for n in (a, b))
            checks['legal_edges'] += 1
        checks['local_capacity_identities'] += 1
        return gain, overload, old, new

    first = {}
    rows = []
    for x in list(range(LOW, HIGH + 1)) + list(HELD):
        threshold = old_threshold(x)
        data, counts = schemes(x)
        results = {name: local(x, edges, threshold) for name, edges in data.items()}
        for name in ('demand', 'supply'):
            single_gain = results[name + '_a'][0] + results[name + '_b'][0]
            union_gain = results[name + '_union'][0]
            if union_gain != single_gain and name not in first:
                first[name] = {'X': x, 'counts_Q94_Q146_R43_R47': counts,
                               'separate_gain': single_gain, 'union_gain': union_gain,
                               'edges': data[name + '_union'], 'old': results[name + '_union'][2],
                               'new': results[name + '_union'][3], 'P9_threshold': threshold}
        assert results['repair'][0] == 2 * len(data['repair'])
        assert len(data['repair']) == min(counts[0] + counts[1], counts[2])
        rows.append([x, *counts, results['demand_union'][0], results['supply_union'][0],
                     results['repair'][0]])
    serial = ''.join(','.join(map(str, row)) + '\n' for row in rows)
    Path('capacity_rows.csv').write_text(serial)

    def direct_base(x):
        pop = {n for n in range(x // 2 + 1, x + 1) if n % 2 and mu[n]}
        assert sum(mu[n] for n in pop) == M[x]
        tops = [n for n in sorted(pop) if largest[n] == n]
        partners = [n for n in sorted(pop) if omega[n] == 2 and n // largest[n] in P9
                    and largest[n] > 29]
        pairs = list(zip(tops, partners))
        for c in range(x // 26 + 1, x // 15 + 1):
            if mu[c] and omega[c] >= 2 and gcd(c, 390) == 1:
                pairs.append((13 * c, 15 * c))
        remaining = set(pop)
        for a, b in pairs:
            assert a in remaining and b in remaining and a != b and mu[a] == -mu[b]
            remaining.remove(a)
            remaining.remove(b)
        assert sum(mu[n] for n in remaining) == M[x]
        sums = Counter()
        for n in remaining:
            sums[largest[n]] += mu[n]
        for q in primes:
            if q > x:
                break
            if q * q > x:
                assert sums[q] == mass(x, q, old_threshold(x))
                checks['direct_high_fibers'] += 1
        return remaining, sums, pairs

    def statistic(pop):
        running, cross = 0, 0
        tags = Counter()
        for n in sorted(pop):
            cross += running * mu[n]
            running += mu[n]
            tags[largest[n]] += mu[n]
        diagonal = len(pop)
        assert diagonal + 2 * cross == running * running
        tag_squares = sum(s * s for s in tags.values())
        return {'signed_sum': running, 'diagonal': diagonal, 'unordered_offdiagonal': cross,
                'square': running * running, 'label_absolute': sum(abs(s) for s in tags.values()),
                'tag_squares': tag_squares, 'ordered_cross_label': running * running - tag_squares}

    material = sorted(set([9118, 9215, 9594, 21609, HIGH, *HELD, *(v['X'] for v in first.values())]))
    fixtures = {}
    for x in material:
        base, tags, old_pairs = direct_base(x)
        base_stats = statistic(base)
        if x >= LOW:
            data, counts = schemes(x)
        else:
            qs, rs = band(x, 94), band(x, 47)
            data = {'gf4': [(93*q, 31*r, q, r) for q, r in zip(qs, rs)]}
            counts = [len(qs), len(rs)]
        item = {'M': M[x], 'old_pair_count': len(old_pairs), 'base': base_stats,
                'band_counts': counts, 'schemes': {}}
        for name, edges in data.items():
            actual = set(base)
            for a, b, q, r in edges:
                assert a in actual and b in actual
                va, fa = trial(a)
                vb, fb = trial(b)
                assert va == -1 and vb == 1 and len(set(fa) ^ set(fb)) == 3
                actual.remove(a)
                actual.remove(b)
                checks['independent_edge_trials'] += 1
            after = statistic(actual)
            assert after['signed_sum'] == M[x] and after['square'] == M[x]**2
            assert after['diagonal'] + 2 * len(edges) == base_stats['diagonal']
            if x >= LOW:
                assert base_stats['label_absolute'] - after['label_absolute'] == local(x, edges, old_threshold(x))[0]
            item['schemes'][name] = {'edges': edges, 'after': after,
                                      'gain': base_stats['label_absolute'] - after['label_absolute']}
            checks['complete_physical_returns'] += 1
        if x in (9118, 9215, 9594):
            q = 97 if x != 9594 else 101
            fiber = [n for n in range(x // 2 + 1, x + 1) if n % 2 and mu[n] and largest[n] == q]
            item['selected_fiber'] = {'q': q, 'quotient': x//q, 'positive': sum(mu[n]>0 for n in fiber),
                                      'negative': sum(mu[n]<0 for n in fiber), 'mass': sum(mu[n] for n in fiber)}
        fixtures[str(x)] = item

    # Original ordered binomial occurrences, computed independently of the matching arrays.
    from math import comb
    lift_checks = 0
    for B, k in ((3, 2), (4, 3), (5, 3)):
        bound = B**k - 1
        seed = [0] + [trial(n)[0] if n < B else 0 for n in range(1, bound+1)]
        ones = [0] + [1]*bound
        def convolution(a, b):
            out = [0]*(bound+1)
            for i in range(1, bound+1):
                for j in range(1, bound//i+1):
                    out[i*j] += a[i]*b[j]
            return out
        signed = [0]*(bound+1)
        term = seed[:]
        for j in range(1, k+1):
            if j > 1:
                term = convolution(convolution(term, seed), ones)
            for n in range(1, bound+1):
                signed[n] += (-1)**(j-1)*comb(k,j)*term[n]
        for n in range(1, bound+1):
            assert signed[n] == trial(n)[0]
            lift_checks += 1

    demand_density = Fraction(1,94*95) + Fraction(1,146*147)
    supply_density = Fraction(1,43*44)
    assert supply_density > demand_density
    payload = {'domain': {'exhaustive': [LOW, HIGH], 'held_out': HELD},
               'first': first, 'checks': dict(checks), 'lift_coefficients': lift_checks,
               'rows': len(rows), 'nonempty_repair_rows': sum(r[-1]>0 for r in rows),
               'rows_sha256': sha256(serial.encode()).hexdigest(), 'held_rows': rows[-len(HELD):],
               'fixtures': fixtures, 'demand_density': str(demand_density),
               'supply_density': str(supply_density), 'density_ratio': str(supply_density/demand_density)}
    Path('capacity_result.json').write_text(json.dumps(payload, indent=2, sort_keys=True)+'\n')
    summary = {k:v for k,v in payload.items() if k != 'fixtures'}
    summary['fixture_summaries'] = {x:{'M':v['M'], 'Lambda':v['base']['label_absolute'],
                                     'gains':{k:w['gain'] for k,w in v['schemes'].items()}}
                                      for x,v in fixtures.items()}
    summary['elapsed_seconds'] = time.perf_counter()-start
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == '__main__':
    run()
```

#### label_capacity_reference.cpp

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

using Edge = std::array<int, 4>;
const std::set<int> bank = {3,5,7,11,13,17,19,23,29};
struct Factor { int mu=1, largest=1, depth=0; };

Factor trial(int n) {
    Factor a;
    for (int p=2; p*p<=n; ++p) {
        if (n%p) continue;
        int exponent=0;
        while (n%p==0) { n/=p; ++exponent; }
        a.mu *= exponent==1 ? -1 : 0;
        a.largest=p;
        ++a.depth;
    }
    if (n>1) { a.mu=-a.mu; a.largest=n; ++a.depth; }
    return a;
}

int main() {
    const auto begin=std::chrono::steady_clock::now();
    constexpr int limit=262143;
    std::vector<Factor> f(limit+1);
    std::vector<int> primes, semis;
    for (int n=1; n<=limit; ++n) {
        f[n]=trial(n);
        if (n>1 && f[n].largest==n) primes.push_back(n);
        if (f[n].mu==1 && f[n].depth==2 && f[n].largest>29 &&
            bank.count(n/f[n].largest)) semis.push_back(n);
    }
    auto pi=[&](int x) { return int(std::upper_bound(primes.begin(),primes.end(),x)-primes.begin()); };
    auto bucket=[&](int x,int m) {
        std::vector<int> v;
        for (int n=x/(m+1)+1; n<=x/m; ++n)
            if (n>1 && f[n].largest==n) v.push_back(n);
        return v;
    };
    auto threshold=[&](int x) {
        auto lo=std::upper_bound(semis.begin(),semis.end(),x/2);
        auto hi=std::upper_bound(semis.begin(),semis.end(),x);
        int k=std::min(pi(x)-pi(x/2),int(hi-lo));
        return k ? *(lo+k-1) : 0;
    };
    // Reconstruct each complete fiber from its physical odd cofactors, not M(t).
    auto mass=[&](int x,int q,int cut) {
        assert(q*q>x);
        int total=0;
        for (int c=1; c*q<=x; c+=2) {
            if (2*c*q<=x) continue;
            total += trial(c*q).mu;
            if (bank.count(c) && c*q<=cut) --total;
        }
        return total;
    };
    auto scheme=[&](int x) {
        auto q94=bucket(x,94), q146=bucket(x,146), r43=bucket(x,43), r47=bucket(x,47);
        std::array<std::vector<Edge>,7> e;
        for (std::size_t i=0;i<std::min(q146.size(),r47.size());++i) {
            e[0].push_back({93*q146[i],31*r47[i],q146[i],r47[i]});
            e[1].push_back({111*q146[i],37*r47[i],q146[i],r47[i]});
        }
        for (std::size_t i=0;i<std::min(q94.size(),r43.size());++i)
            e[3].push_back({93*q94[i],31*r43[i],q94[i],r43[i]});
        for (std::size_t i=0;i<std::min(q146.size(),r43.size());++i)
            e[4].push_back({111*q146[i],37*r43[i],q146[i],r43[i]});
        e[2]=e[0]; e[2].insert(e[2].end(),e[1].begin(),e[1].end());
        e[5]=e[3]; e[5].insert(e[5].end(),e[4].begin(),e[4].end());
        std::size_t i=0;
        for (int q:q94) if (i<r43.size()) { int r=r43[i++]; e[6].push_back({93*q,31*r,q,r}); }
        for (int q:q146) if (i<r43.size()) { int r=r43[i++]; e[6].push_back({111*q,37*r,q,r}); }
        return e;
    };
    auto gain=[&](int x,const std::vector<Edge>& edges) {
        int cut=threshold(x);
        std::map<int,int> old,delta;
        std::set<int> sites;
        for (auto [a,b,q,r]:edges) {
            assert(sites.insert(a).second && sites.insert(b).second);
            assert(a%2 && b%2 && x<2*a && x<2*b && a<=x && b<=x);
            assert(f[a].mu==-1 && f[b].mu==1);
            assert(f[a].largest==q && f[b].largest==r);
            old[q]=mass(x,q,cut); old[r]=mass(x,r,cut);
            assert(old[q]<0 && old[r]>0);
            ++delta[q]; --delta[r];
        }
        int g=0;
        for (auto [q,s]:old) g+=std::abs(s)-std::abs(s+delta[q]);
        return g;
    };
    std::ofstream rows("capacity_cpp_rows.csv");
    int first_demand=0,first_supply=0,row_count=0;
    std::vector<int> cutoffs;
    for(int x=21609;x<=65535;++x) cutoffs.push_back(x);
    for(int x:{65536,87283,131071,262143}) cutoffs.push_back(x);
    for(int x:cutoffs) {
        auto e=scheme(x);
        std::array<int,7> g{};
        for(int k=0;k<7;++k) g[k]=gain(x,e[k]);
        if(!first_demand && g[0]+g[1]!=g[2]) first_demand=x;
        if(!first_supply && g[3]+g[4]!=g[5]) first_supply=x;
        assert(g[6]==2*int(e[6].size()));
        rows<<x;
        for(int m:{94,146,43,47}) rows<<','<<bucket(x,m).size();
        rows<<','<<g[2]<<','<<g[5]<<','<<g[6]<<'\n';
        ++row_count;
    }
    rows.close();
    std::cout<<"FIRST_DEMAND "<<first_demand<<"\nFIRST_SUPPLY "<<first_supply<<'\n';

    std::set<int> fixtures={9118,9215,9594,21609,first_demand,first_supply,
                           65535,65536,87283,131071,262143};
    std::ofstream physical("capacity_cpp_physical.csv");
    int returns=0;
    for(int x:fixtures) {
        std::set<int> base;
        std::vector<int> tops,partners;
        int M=0;
        for(int n=1;n<=x;++n) {
            M+=f[n].mu;
            if(n%2 && x<2*n && f[n].mu) {
                base.insert(n);
                if(f[n].largest==n) tops.push_back(n);
                if(f[n].depth==2 && f[n].mu==1 && f[n].largest>29 &&
                   bank.count(n/f[n].largest)) partners.push_back(n);
            }
        }
        for(std::size_t i=0;i<std::min(tops.size(),partners.size());++i) {
            assert(base.erase(tops[i])==1 && base.erase(partners[i])==1);
        }
        for(int c=1;15*c<=x;++c) if(x<26*c && f[c].mu && f[c].depth>=2 && std::gcd(c,390)==1) {
            assert(f[13*c].mu==-f[15*c].mu);
            assert(base.erase(13*c)==1 && base.erase(15*c)==1);
        }
        std::vector<std::pair<int,std::vector<Edge>>> scenarios;
        if(x>=21609) {
            auto e=scheme(x);
            for(int k=0;k<7;++k) scenarios.push_back({k,e[k]});
        } else {
            auto q=bucket(x,94),r=bucket(x,47);
            std::vector<Edge> es;
            for(std::size_t i=0;i<std::min(q.size(),r.size());++i)
                es.push_back({93*q[i],31*r[i],q[i],r[i]});
            scenarios.push_back({7,es});
        }
        scenarios.push_back({8,{}});
        for(auto [key,es]:scenarios) {
            auto pop=base;
            for(auto [a,b,q,r]:es) assert(pop.erase(a)==1 && pop.erase(b)==1);
            long long sum=0,cross=0,squares=0,lambda=0;
            std::map<int,int> tags;
            for(int n:pop) { cross+=sum*f[n].mu; sum+=f[n].mu; tags[f[n].largest]+=f[n].mu; }
            for(auto [q,s]:tags) { lambda+=std::abs(s); squares+=s*s; }
            assert(sum==M && (long long)pop.size()+2*cross==sum*sum);
            physical<<x<<','<<key<<','<<sum<<','<<pop.size()<<','<<cross<<','
                    <<sum*sum<<','<<lambda<<','<<squares<<','<<sum*sum-squares<<'\n';
            ++returns;
        }
    }
    std::cout<<"PASS rows="<<row_count<<" physical_returns="<<returns<<'\n';
    std::cout<<"ELAPSED_SECONDS "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()<<'\n';
}
```

#### compare_capacity.py

```python
"""Compare independent integer reconstructions and summarize exact witnesses."""

import csv
import json
from hashlib import sha256
from pathlib import Path


result = json.loads(Path('capacity_result.json').read_text())
left = Path('capacity_rows.csv').read_bytes()
right = Path('capacity_cpp_rows.csv').read_bytes()
assert left == right
names = ['demand_a', 'demand_b', 'demand_union', 'supply_a', 'supply_b', 'supply_union', 'repair', 'gf4', 'base']
fields = ['signed_sum', 'diagonal', 'unordered_offdiagonal', 'square',
          'label_absolute', 'tag_squares', 'ordered_cross_label']
compared = 0
with Path('capacity_cpp_physical.csv').open() as stream:
    for row in csv.reader(stream):
        x, key, *values = map(int, row)
        record = result['fixtures'][str(x)]
        stats = record['base'] if key == 8 else record['schemes'][names[key]]['after']
        assert values == [stats[field] for field in fields], (x, key)
        compared += 1

for s in range(1, 21):
    for k in range(0, 41):
        assert abs(s) - abs(s-k) == k - 2*max(k-s,0)
        assert abs(-s) - abs(-s+k) == k - 2*max(k-s,0)

rows = [[int(t) for t in line.split(',')] for line in left.decode().splitlines()]
deficiency = next((r for r in rows if r[1] + r[2] > r[3]), None)
f = result['fixtures']['21754']
for name in ('demand', 'supply'):
    assert result['first'][name]['X'] == 21754
    assert f['schemes'][name+'_a']['gain'] + f['schemes'][name+'_b']['gain'] == 4
    assert f['schemes'][name+'_union']['gain'] == 2
assert f['schemes']['repair']['gain'] == 4
assert f['base']['signed_sum'] == 1

summary = {'independent_rows_equal': len(rows), 'physical_rows_equal': compared,
           'rows_sha256': sha256(left).hexdigest(), 'first_failures': result['first'],
           'first_posthoc_full_capacity_failure': deficiency,
           'note': 'The capacity failure lookup is a post-scan scope audit, not a preregistered hypothesis.',
           'status': 'PASS'}
Path('comparison_result.json').write_text(json.dumps(summary, indent=2, sort_keys=True)+'\n')
print(json.dumps(summary, indent=2, sort_keys=True))
```

#### certificate_audit.py

```python
"""Standalone post-scan certificates: trial division and physical enumeration only."""

from collections import Counter
from math import gcd
import json


def factors(n):
    out = []
    sign = 1
    p = 2
    while p*p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            out.append(p)
            sign *= -1 if e == 1 else 0
        p += 1
    if n > 1:
        out.append(n)
        sign *= -1
    return sign, out


bank = {3,5,7,11,13,17,19,23,29}
table = [None] + [factors(n) for n in range(1, 22133)]
records = []
for X in (9118, 9215, 9594, 21753, 21754, 21755, 22132):
    pop = {n for n in range(X//2+1, X+1) if n%2 and table[n][0]}
    top = sorted(n for n in pop if len(table[n][1])==1)
    donors = sorted(n for n in pop if len(table[n][1])==2 and
                    table[n][1][0] in bank and table[n][1][-1]>29)
    old = list(zip(top, donors))
    for c in range(1, X//15+1):
        if X < 26*c and table[c][0] and len(table[c][1])>=2 and gcd(c,390)==1:
            old.append((13*c,15*c))
    remaining = set(pop)
    for a,b in old:
        assert a in remaining and b in remaining and table[a][0]==-table[b][0]
        remaining.difference_update((a,b))
    labels = Counter()
    for n in remaining:
        labels[table[n][1][-1]] += table[n][0]
    bands = {m:[q for q in range(X//(m+1)+1,X//m+1) if table[q][1]==[q]]
             for m in (43,47,94,95,146)}
    record = {'X':X,'M':sum(table[n][0] for n in range(1,X+1)),
              'Lambda':sum(abs(v) for v in labels.values()),'bands':bands}
    if X==21754:
        assert labels[149]==-1 and labels[229]==-1 and labels[457]==2
        assert labels[499]==labels[503]==1
        assert {11477,14471,13253}.isdisjoint(remaining)
        record['old_label_masses']={q:labels[q] for q in (149,229,457,499,503)}
        record['spent_donors']={n:table[n] for n in (11477,14471,13253)}
        edges=[(13857,14167),(16539,16909),(21297,15469),(16539,18463),(16539,18611)]
        record['edge_factors']=[{'a':a,'b':b,'factors_a':table[a][1],
                                 'factors_b':table[b][1]} for a,b in edges]
        for a,b in edges:
            assert a in remaining and b in remaining
            assert table[a][0]==-1 and table[b][0]==1
    if X==22132:
        assert bands[94]==[233] and bands[146]==[151] and bands[43]==[509]
        assert labels[233]==labels[151]==-1 and labels[509]==1
        record['capacity_witness']={'negative_labels':[233,151], 'positive_label':509,
                                    'positive_capacity':1, 'demand':2,
                                    'donor_sites':[31*509,37*509]}
    assert sum(table[n][0] for n in remaining)==record['M']
    records.append(record)

cofactor = {}
for t in (43,47,94,95,146):
    p=[c for c in range(t//2+1,t+1) if c%2 and table[c][0]==1]
    n=[c for c in range(t//2+1,t+1) if c%2 and table[c][0]==-1]
    M=sum(table[c][0] for c in range(1,t+1))
    assert len(p)-len(n)==M
    cofactor[t]={'positive':p,'negative':n,'M':M}
print(json.dumps({'status':'PASS','posthoc_trial_certificates':records,
                  'complete_odd_cofactor_certificates':cofactor},indent=2))
```

### Prepublication Freshness

At 2026-11-07T08:30:39Z, main remained 1c057c1d65b6d4cb4d59d207f69a815c52353314; #1101 remained open and unmerged at the same head. Today's three upstream report blobs were unchanged. No absent downstream report was inferred from a schedule. The early checkpoint commit 588ab2df5275eaceaf79a0291e209fc5a54e8fb3 and preregistration commit 020dd74d57f4fc95b811acc7e9d8ad81db905542 were both read back exactly. Final publication is established only by the later receipt, after a successful write and immutable readback. No background computation remains running.

### Verified Publication Receipt - 20261107-census-1

Execution/publication: **COMPLETED / PUBLISHED / IMMUTABLE_READBACK_VERIFIED**.

The substantive synthesis was committed on agent-reports at **9fac1c666414d087b93cbd3ad8d03ca5f01daca3**, 2026-11-07T08:32:43Z, with report blob **d2f52e19c4699ef1bdbee647e5cd86a45e078a81**. By **2026-11-07T08:32:55Z / 03:32:55 EST**, immutable readback matched all **65351 characters** exactly. Commit metadata confirmed that the only changed path was this authorized own report, with **916 additions and zero deletions**. The complete checkpoint and frozen registration are preserved as an unchanged prefix.

All A-N sections, 30 balanced code fences, source/report hashes, four exact executed code embeddings, and independent result comparisons passed validation. This receipt records the already verified substantive commit; it does not claim that its own later commit had previously been verified.

Mathematics remains **REFUTED / FINITE_COMPUTATION** for the specified additive assertions and **PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING** for the general capacity law and corrected component. No new Lean theorem or complete endpoint gain is asserted. Existing strict baseline results are preserved. No background computation remains running.


