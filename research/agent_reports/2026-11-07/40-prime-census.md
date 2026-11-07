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



## Scheduled Consumer-Certificate Checkpoint - 20261107-census-2

Trigger: 2026-11-07T11:00:01-05:00, America/New_York; RUN_ID_UNAVAILABLE.
Prepared: 2026-11-07 16:07:47 UTC. Execution IN_PROGRESS / PARTIAL; new mathematical claims PENDING.

### Authority And Resumption

main=aa10b310efb2a095fd4c69dc965e6bde0bd135d6; AGENTS blob 7d19591d69a141c2c094a81a7dff2569562ab892;
CURRENT_PROOF_CONTRACT blob 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c.
chain_ack=CANCELLATION_CHAIN_REUSE_V1, policy blob ef8d3ac76a893028f4de772c9a00d3bc261c8132.
baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1;
deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1.
All seven relevant reports for November 7 and November 6 were retrieved. TODAY=AVAILABLE;
YESTERDAY=CARRY_FORWARD, not a new certification of every archived claim.
EXTERNAL_HANDOFFS blob 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no November entry.
Earlier SC1-SC5 and yesterday's GM/HC/FW evidence remain preserved and are not rerun.

No open/draft PRs were returned at intake. #1101, #1102 and #1103 are merged.
The new #1103 source extension is the selected support task: original marked capacity
2*m+6*kappa*z<=1 with kappa>1/2, original full-family license
2*HeckeZeroSupremum.beta-1<=kappa, actual source profiles and unchanged HighData.
Dedicated exact-head run 42386987885/job128446349776 succeeded, and its terminal
axiom output was read. No local Lean or new Actions run is performed.

### Preregistered Question And Discriminator

Existing input: RetainedSlotDetector.source_batch_plain_marked_fine_half and
RetainedSlotFiberCount.plain_marked_count_half, plus unchanged inverse/unmarked branches.
Actual consumer: original DetectorRowCountOptimization.count_bound_of_source_branches,
DetectorRowCountEndpoint.balanced_endpoint_with_loss, and their downstream HIGH return.

Question: after retaining kappa in the original marked branch instead of widening
its capacity to 9/2, does the resulting crossing/balanced count improve on the
ENTIRE admitted parameter rectangle, or does a supply/endpoint constraint invalidate
the naive extension? A uniform positive improvement in every bin is a separate,
potentially false, assertion.

Preregistered exact closed diagnostic domain:
kappa in [1/2,3/4], delta in [0,5/6], x in [0,1/2], tstar in [1,3/2].
The kappa=1/2 face is arithmetic limiting diagnostics ONLY; the analytic supplier
requires strict kappa>1/2 and its full-family license. q=delta*x.
Keep inverse z<(1-r)/2, second inverse inequality, supply z<=7/37,
plain z=(1-2*m)/(6*kappa)-nu, zero-capacity fallback, original small
length/mesh/moment losses, and high-bin delta>=5/6 branch.
No artificial row is asserted to be an actual Hecke fiber.

Method: derive rational crossing and balanced formulas; exact boundary and
interior checks; clear only positive denominators; seek a finite polynomial
certificate valid over the whole rectangle, with independent integer/rational
verification. Exploratory grid and held-out grid will be recorded separately;
neither is the uniform proof. Search for equality faces, supply overruns,
incorrect strict-capacity use, and nonuniform-limit errors.
Stopping rule: stop at a decisive counterexample or a complete parameter certificate
and the exact first unsupported same-probe return. Do not fit a global exponent.

### Full Return And Status

Retain original rows, prime/exclusion masks, profile derivatives, external
real part 17/50, d>=1/200, rowNorm>=Z^(1/100), polynomial height cost,
all four moment fields, large/empty selections, principal, LOW, remote and
exceptional contributions. A detector-count improvement alone is not a new
Mertens/VF/RH endpoint. Strongest applicable strict baseline is retained.
NO_NEW_VERIFIED_ENDPOINT_GAIN; eta_gate=SEARCH_BROAD.

## Retained-Capacity Consumer Certificate - 20261107-census-2

### A. Most Important Mathematical Discovery

**The newly licensed marked capacity can be retained through the actual inverse/plain crossing and balanced detector count, with no extra supply loss. The resulting complete detector endpoint functional has the uniform certified margin**

```text
M(kappa) = 1/5000 + (3-4*kappa)/1600,
1/2 <= kappa <= 3/4.
```

This is a parameter-domain theorem for the ORIGINAL detector consumer, not a numerical fit, a new primitive cancellation estimate, or a new global zero-free exponent. At kappa=3/4 it already improves the existing sufficient detector margin 49/440640 to 1/5000; retaining smaller kappa gives the displayed additional margin. The bound is deliberately nonoptimal.

The subtlety is that the balanced row-count exponent does **not** improve strictly in every bin: it is unchanged at zero selected amplitude and at the long-branch endpoint. Those equality faces are not the worst cases of the complete detector endpoint functional. One must optimize the actual consumer, not assume a uniform per-bin saving.

The all-parameter certificate consists of 324 strictly positive rational Bernstein coefficients on nine boxes. Python coefficient conversion and an independently written JavaScript BigInt interpolation agree on every coefficient. The new count/consumer derivation is **PAPER_PROOF / SELF_AUDIT**, independent Referee review **PENDING**, and is **not** a new Lean theorem. The certificate calculations are **FINITE_COMPUTATION**; positivity of their explicitly specified polynomial certifies the whole real rectangle by the Bernstein identity, not by extrapolation from a grid.

This completes the scheduled invocation triggered at 2026-11-07T11:00:01-05:00, America/New_York; RUN_ID_UNAVAILABLE. Earlier same-day SC1-SC5, checkpoints, corrections and receipts remain unchanged. **NEW_VERIFIED_ENDPOINT_GAIN=NONE; eta_gate=SEARCH_BROAD.** The existing strict native baseline is preserved.

### B. Current Authoritative Objective

Authority pin: main **aa10b310efb2a095fd4c69dc965e6bde0bd135d6**, observed at 2026-11-07T16:00:43Z. Current instructions were read at that immutable revision, together with the updated selector, role prompts, complete-return, persistent-engine, breadth and paid-baseline contracts. The canonical target remains `VFCanonicalSquareVonKochStatement`: there is C>=0 such that for every integer R>=2, the actual prime-counting defect from vfCanonical at R^2 is at most C R log R. It remains OPEN.

Activation: `chain_ack=CANCELLATION_CHAIN_REUSE_V1`, policy blob ef8d3ac76a893028f4de772c9a00d3bc261c8132; `baseline_ack=PAID_BASELINE_EXACT_CONSUMER_V1`; `deployment_ack=NO_PIGEONHOLING_ROUTE_SELECTOR_V1`.

The preserved strongest explicit comparator is the live `native_beta_le_explicit_slot_count` statement, b_* = 7/8-g_*, g_* = 1/(288*explicitSlotCount)>0. No astronomical denominator was recomputed or optimized. This report improves a detector budget, not b_*.

Compact chain-consumer record:

| Item | Exact scope |
| --- | --- |
| Reused input | Merged #1103 `RetainedSlotMoments.source_moments_half` and `RetainedSlotFiberCount.plain_marked_count_half`; unchanged inverse and unmarked suppliers |
| Actual consumer | Original `count_from_raw_moments`, `fixed_amplitude_count_from_raw_moments`, `balanced_endpoint_with_loss`, and native `actual_high_probe_from_raw_moments_tilted` |
| Old loss | Compare marked capacity 6*kappa to 9/2, then pay Delta/4 and use the old crossing; this discards the newly available kappa dependence |
| Changed inference | Retain 6*kappa through the crossing and balance; prove the new rational endpoint budget over the entire rectangle |
| Return retained | Four moment fields, actual fibers and selected products, finite bins and dyadic multiplicities, mesh/height/moment costs, high-bin branch and all later source terms |
| First uncompleted return | Native complete HIGH transport must consume this parameterized count without substituting a negative physical Delta, and its below-7/8 comparison must be justified |
| Net endpoint | No new complete zero/Mertens/VF exponent established |

### C. Competing Hypotheses

**H-CAPACITY:** the wider marked capacity produces a valid improved crossing and balanced count while preserving all actual inverse and supply constraints. This survives, with the proof in H.

**H-RETURN:** retaining kappa necessarily overruns selected-slot supply or breaks the second inverse capacity at some legal parameter. This is excluded on the stated rectangle, including the full length-error allowance used below. It is not a claim about unexamined parameter extensions.

**H-UNIFORM-BIN:** for fixed kappa<3/4 there exists c(kappa)>0 such that the new balanced row exponent is at most the old one minus c(kappa) for every delta,x in the rectangle. This precisely quantified scalar assertion is REFUTED by x=0. No artificial parameter point is called a realized Hecke fiber or a counterexample to the canonical theorem.

**H-AUTOMATIC-ENDPOINT:** the supplier extension alone permits replacing Delta by (kappa-3/4)/2 throughout the old HIGH theorem and iterating the global boundary. The actual theorem hypotheses do not justify this inference. This is an identified unsupported use, not a mathematical impossibility theorem for feedback.

### D. Exact Experimental Carrier

The source is the pinned original OAI Hecke `Fiber`, not rational Mobius data. Preserve `F.rows`, its witness family and label, left/right dyadic lengths, actual row ideal coefficient relation and reverse flag, prime profiles, excluded-prime masks, fixed amplitude bins and physical selected product. The native generalized supplier keeps the same `HighData Delta`; only the `Moments` capacity index becomes `(kappa-3/4)/2`.

Write delta=2*a-1, q=F.q, x=q/delta, r=F.r, m=F.m, t=tstar. On the actual low-bin branch a>51/100, 0<delta<=5/6 and 0<=x<=1/2. The closed delta=0 face is included only to strengthen the scalar certificate; it does not use the undefined actual quotient q/delta there. The scalar expression is defined independently on that face.

The common source losses are retained. The raw branch exponents before their explicitly stated errors are

```text
I0 = max(1,(1+5*r)/6) - delta*r,
P0 = 1 - 2*delta*m,
I  = 1 - delta*r - 2*q*z,
P  = 1 - 2*delta*m - 2*q*z.
```

The inverse branch requires z>=0, z<=7/37, r+2z<1 and 2r+8z<3. The plain branch requires z>=0, z<=7/37 and 2m+6*kappa*z<=1. The original source supplies at least 7/37 total slot width; selection loses the same mesh term as before. No continuum selection substitutes for actual slots.

Registered domain: kappa in [1/2,3/4], delta in [0,5/6], x in [0,1/2], t in [1,3/2]. Analytic use is STRICTLY kappa>1/2 with `51/100<=HeckeZeroSupremum.beta`, `2*HeckeZeroSupremum.beta-1<=kappa`, and the genuine source fineness condition. Constants may depend on a fixed lower kappa0>1/2. Uniform polynomial inequalities down to 1/2 do not imply uniform analytic constants there.

The source field retains d>=1/200, d<=7/8 in the assembled moment interface, Z^(1/100)<=rowNorm, nonunit and residue masks, external real part 17/50, actual profile derivatives j+k<=2, height bounds and the same selected subsets. The sharper separate marked field has exponent 1+D.t/2; the four-field common record explicitly widens it to 1+D.t. This report does not claim to recover that separate half-loss too.

### E. Executed Results

The exploratory four-slice scan used ordinary floating point only to locate a difficult region near delta=31/80, x=1/2. It is not used for any certified sign, maximum or theorem. All final arithmetic uses Python `Fraction` or independent JavaScript normalized BigInt rationals; no rounding error, probable primality, random seed or transcendental approximation is involved.

| Check | Exact outcome |
| --- | --- |
| Rational parameter checks | 9,639 registered points: 9 kappa values, 21 delta values, 17 x values and three t values |
| Python held-out regime | 400 deterministic prime-denominator points, distinct from the exploratory grid |
| Independent JavaScript held-out regime | 401 differently generated rational points, with crossing and balance obtained by solving the two affine intersections |
| Uniform certificate | 324/324 Bernstein coefficients strictly positive, identical across both methods |
| Actual branch case-split stress | 3,000 rational length/error cases; 640 long, 438 inverse, 287 plain and 1,635 unmarked fallback cases |
| Syntax validation | Python byte compilation and Node syntax check passed |

The three uniform formulas and all capacity comparisons passed. The independent method does not import Python polynomials, coefficient tables or intermediate outputs: it evaluates the unexpanded rationally defined polynomial at interpolation nodes and inverts three small Bernstein evaluation matrices. The comparison program then checks all reconstructed coefficients against the Python result.

Exact fixtures at delta=3/8, x=1/2:

| kappa | A_kappa | Balanced t | Balanced row exponent | Endpoint functional |
| --- | --- | --- | --- | --- |
| 3/4 | 14/37 | 596/533 | 362/533 | -1/3936 |
| 2/3 | 3/8 | 257/230 | 1249/1840 | -49/88320 |
| 1/2 | 4/11 | 175/157 | 851/1256 | -95/60288 |

The kappa=2/3 row is an arithmetic fixture, NOT a presently licensed unconditional full-family choice: licensing it would require beta<=5/6. The kappa=1/2 row is a limiting diagnostic outside the analytic theorem.

Observed environment: Python 3.12.14, Node v24.22.1. The successful Python certificate run reported 1.125464596 seconds; terminal wall times were approximately 0.093 seconds for the Node verifier and 0.081 seconds for the coefficient/branch comparison. These are observed timings, not performance guarantees.

### F. Exceptional Cases And Corrections

1. At x=0, delta=3/8, every kappa in [1/2,3/4] has A=2/3, balanced t=20/17, row exponent 12/17 and endpoint -1/102. Thus H-UNIFORM-BIN is false. Equality also occurs when delta=0 or delta=5/6. These are parameter-domain equality certificates, not claimed arithmetic-row realizations.
2. Strict inverse admission cannot discard nu. At kappa=2/3, delta=3/8, x=1/2 and balanced t=257/230, the crossing is r=82/115. Choosing z=(1-r)/2=33/230 gives r+2z=1, not <1. The actual proof chooses z=(1-r)/2-nu with nu>0, and retains its loss. This is an inherited strictness regression, not a new obstruction discovery.
3. The first eight-box Bernstein attempt was inconclusive: the box delta in [3/8,2/5] had coefficient -79/150000. A negative Bernstein coefficient is not a counterexample to the polynomial. Splitting that interval once at 31/80 gave nine boxes and all-positive coefficients. The inequality and constant M(kappa) were not changed after that failure. No held-out check had run before the certificate was fixed.
4. The proposed C++ independent verifier could not compile because Boost multiprecision headers were absent. It produced no mathematical result. A separately written Node BigInt interpolation replaced it and ran successfully. SymPy was also unavailable, so the Python computation uses elementary exact polynomial dictionaries. No package installation, local Lean build, or hidden tool assumption was used.

### G. Hidden Variable And Classification

The explanatory variable is x=q/delta: the actual width-weighted selected-prime amplitude relative to the detector threshold. Smaller kappa has no leverage when that weighted amplitude is zero. The size of the gain also depends quadratically on the distance s=5/6-delta from the long-branch endpoint. This makes a blanket per-bin saving the wrong quantitative description.

For c=x/(3*kappa), set

```text
D_k = 3-x-2*c,
A_k = 2*(1-c)*(1-x)/D_k,
s = 5/6-delta.
```

For 1/2<=kappa<=3/4, 0<=x<=1/2, the exact difference is

```text
A_(3/4)-A_k
  = 2*x*(3-4*kappa)*(1-x)^2 / (9*kappa*D_(3/4)*D_k),

R_(3/4)-R_k
  = delta*s^2*(A_(3/4)-A_k)
      / (2*(s+delta*A_(3/4))*(s+delta*A_k)).
```

Every denominator is positive. These identities prove the improvement and its precise equality faces. They also explain why a joint complete consumer can improve even though some component bins do not.

### H. Mathematical Derivation

**RC1: generalized crossing and valid source capacities. PAPER_PROOF.** For all parameters in D, define

```text
r_k(x,t) = [c+(2-2*c)*t-x]/D_k,
I(r) = 1-delta*[x+(1-x)*r],
P_k(t,r) = 1-delta*[c+(2-2*c)*(t-r)],
S_k(delta,x,t) = 1-delta+delta*A_k*(3/2-t),
L(delta,t) = 1-delta+(5/6-delta)*(t-1).
```

Then I(r_k)=P_k(t,r_k)=S_k. The inverse exponent decreases in r and the plain exponent increases in r, so choose plain for r<=r_k and inverse for r>=r_k. Moreover

```text
D_k >= 11/6,
23/37 <= r_k <= 1,
1/3 <= t-r_k <= 1/2.
```

Here is a short proof including the boundary details. Multiply the crossing denominator by 3*kappa and put Dbar=9*kappa-3*kappa*x-2*x. It is at least 11/4. The crossing numerator is (6*kappa-2*x)*t+x*(1-3*kappa), increasing in t. At t=3/2 it equals Dbar. At t=1, 37*numerator-23*Dbar=15*kappa+9*x-42*kappa*x, nonnegative by its endpoint values in x and kappa. For the cofactor length, t-r_k is increasing in t, equals 1/2 at t=3/2, and at t=1 the inequality t-r_k>=1/3 reduces to x*(3*kappa-1)>=0.

With the original length error gamma<=1/12 and m>=t-r-gamma on the plain side, m>=1/4. Thus, whenever its requested capacity is positive,

```text
(1-2*m)/(6*kappa) <= 1/6 < 7/37,
7/37-1/6 = 5/222.
```

Subtracting nu>=0 preserves supply. On the inverse side r>=23/37 gives (1-r)/2<=7/37; with nu>0, both strict inverse inequalities hold, and the second has slack at least 9/37. These estimates concern the actual selection interface, not fractional arbitrary replacements for physical slots.

**RC2: changed actual fiber consumer and balanced bound. PAPER_PROOF, source-moment hypotheses retained.** Replace only the old moment capacity index by `(kappa-3/4)/2`. Under the other hypotheses of `count_from_raw_moments`, its conclusion becomes

```text
card(F.rows) <= fiberConstant(C,height,K0)
  * U^(max(S_k(delta,x,t),L(delta,t))
       +159*epsilon+epsilon_m+F.mesh+7*nu).
```

The previous extra Delta/4 is absent. No claim removes the 159*epsilon, epsilon_m, mesh or nu costs. The four branch suppliers and their constants are unchanged except for using the already-proved `plain_marked_count_half` at capacity 6*kappa.

Proof of the case split: for r>=1 use I0 and r<=t+gamma. For r<1 on the inverse side, use I unless `(1-r)/2<=nu`; then I0 is at most 1-delta+2*delta*nu. On the plain side, m>=1/2 gives P0<=1-delta. If its capacity is at most nu, P0<=1-delta+6*delta*kappa*nu<=1-delta+6*nu. Otherwise use RC1's admissible requested z. Replacing m by t-r costs at most 2*gamma because the slope is delta*(2-2*c) in [0,2]. All marked requested-z losses fit the original `commonLoss=154*epsilon+epsilon_m+mesh+nu`. The old conservative additional 5*gamma+6*nu remains sufficient. Setting gamma=epsilon gives exactly the displayed 159*epsilon+epsilon_m+mesh+7*nu.

The coefficient inequality follows from the original witnesses, common frequency, profiles, selected products and four moment estimates. Empty row sets are trivial; nonempty fibers retain the positive supply condition. No inverse or unmarked field requires positivity of the capacity-only Delta index. In contrast, downstream modules with a physical nonnegative Delta cannot simply be invoked at that negative index.

The new balanced choice and row exponent are

```text
t_k = 1 + delta*A_k/[2*(s+delta*A_k)],
R_k = 1-delta + s*delta*A_k/[2*(s+delta*A_k)].
```

Here s+delta*A_k>0, t_k in [1,3/2], and S_k(delta,x,t_k)=L(delta,t_k)=R_k. The genuine finite-bin aggregation remains multiplicative by `card(Label)*(dyadicLength U)^2*card(B.Bin)`. We do not drop this factor or claim its later costs vanish.

**RC3: full-rectangle detector endpoint certificate. PAPER_PROOF with FINITE_COMPUTATION certificate.** Define exactly the original endpoint functional

```text
E_k(delta,x) = -1/48 + (2/3)*delta + delta*x/6
                -(13/16)*(1-R_k).
```

Then, for every real 1/2<=kappa<=3/4, 0<=delta<=5/6, 0<=x<=1/2,

```text
E_k(delta,x) <= -1/5000-(3-4*kappa)/1600 = -M(kappa).
```

This is a universal algebraic assertion, not a finite-grid claim. Its exact certificate follows. Set v=3-4*kappa, Pbar=(6*kappa-2*x)*(1-x), J=s*Dbar+delta*Pbar. We have Pbar>=1 and J>=5/6. Clear only the positive denominator 96*J:

```text
H(delta,x,v) = [2+delta*(14-16*x)-96*(1/5000+v/1600)]*J
                -39*delta*s*Pbar
             = -96*J*(E_k+M(kappa)).
```

After substituting kappa=(3-v)/4, H has degree at most (2,3,2) in (delta,x,v). On each box below, affinely rescale to [0,1]^3 and expand in the tensor Bernstein basis of those degrees. Every basis function is nonnegative and their sum is one. Therefore the minimum coefficient bounds H below on that entire box. The following are the EXACT minima, independently reconstructed:

| delta interval | Minimum of its 36 Bernstein coefficients |
| --- | --- |
| [0,1/4] | 38353/60000 |
| [1/4,1/3] | 16771/120000 |
| [1/3,3/8] | 1729/120000 |
| [3/8,31/80] | 8329/1200000 |
| [31/80,2/5] | 17861/2400000 |
| [2/5,5/12] | 1231/75000 |
| [5/12,1/2] | 319/6000 |
| [1/2,2/3] | 7067/15000 |
| [2/3,5/6] | 69827/30000 |

Each box has the FULL x interval [0,1/2] and v interval [0,1]. Thus the boxes cover the complete parameter rectangle, including shared boundaries. The reproducible coefficient formula is: if the affinely transformed power coefficients are a_j, the Bernstein coefficient at i is `sum_(j<=i) a_j product_l binom(i_l,j_l)/binom(n_l,j_l)`, n=(2,3,2). The two executed implementations below reconstruct every a_j/b_i comparison without relying on a decimal sign.

**RC4: endpoint-with-loss and the other branch. PAPER_PROOF / CONDITIONAL at the unwired source return.** If the actual row exponent is at most R_k+loss, the same functional is at most `-M(kappa)+(13/16)*loss`. For 5/6<=delta<=1, the unchanged high-bin proof gives `-1/48-delta/16+(13/16)*loss`, at most `-7/96+(13/16)*loss`, stronger than this new margin. The high-bin complement is therefore not silently omitted.

At a licensed kappa=3/4-2*g with 0<g<1/8 and beta<=7/8-g, the parameter margin is `1/5000+g/200`. This is an additional detector budget, NOT a conclusion that beta decreases by that amount.

### I. Precise Theorem And Evidence Status

| Stable ID | Assertion | Status |
| --- | --- | --- |
| 20261107-census-2/RC1 | Generalized crossing, both inverse inequalities and genuine selection supply | PAPER_PROOF; SELF_AUDIT; independent review PENDING |
| RC2 | Source-qualified four-branch fiber count with kappa retained and no old Delta/4 widening | PAPER_PROOF; source-moment hypotheses explicit; not formalized |
| RC3 | Uniform complete detector functional margin M(kappa) on the entire real rectangle | PAPER_PROOF supported by independently checked exact FINITE_COMPUTATION certificate |
| RC4 | Loss propagation and unchanged high-bin return; complete-probe application still conditional | CONDITIONAL for the uncompleted complete HIGH integration |
| RC5 | H-UNIFORM-BIN is false on the stated parameter domain; equality-face and strict-capacity certificates | REFUTED / FINITE_COMPUTATION; no claimed actual-row realization |
| RC6 | Registered grids, held-out cases, exact cross-language coefficients and branch stress | FINITE_COMPUTATION |

The next theorem worth implementing, after independent review and utility assessment, is a kappa-parameterized `count_from_raw_moments` and its `fixed_amplitude_count_from_raw_moments` consumer with RC2's displayed loss. This is a smaller, source-backed inference, not a new signed-covariance assumption.

### J. Complete Return And Proof Impact

The actual native HIGH assembly charges

```text
(13/16)*(159*epsilon+epsilon_m+R_slot+7*nu)
 +2*zeta+(3/2)*mu
 +(26*e+(N+8)*eps+loss+mesh/6)
 +(logCost+heightCost+momentCost)+saving.
```

Its current sufficient cap is 49/440640. RC3 supplies the candidate replacement cap M(kappa) **after** RC2 has been wired through the actual batch/source consumer. The present report does not change any of these charges, ignore source thresholds or delete a term. Character constants and polynomial height costs remain those of the native supplied moments. The kappa-dependent analytic constants are fixed before the large-scale limit.

Two precise return limitations remain. First, `actual_high_probe_from_raw_moments_tilted` still takes a nonnegative physical Delta and downstream source hypotheses; the capacity-only negative index in `SourceMomentBoundAtKappa` is not a legal substitution for that physical parameter. Second, its current fixed comparison explicitly assumes `7/8<=HeckeZeroSupremum.beta`. The old declaration cannot simply be applied below 7/8 to license a feedback iteration. A generalized same-probe comparison must prove its own range and retain geometric, principal, floor, window, conductor, remote, exceptional and height budgets.

LOW remains `3/16-9*tilt+positive_loss`; the principal shift remains `-11/16-8*tilt`. Their difference is `7/8-tilt`, with the actual slot charge `24*tilt<=(7/8)*D.rmin`. This is reused existing structure. RC3 alone does not enlarge the allowed physical tilt or improve that difference. Original J=empty still has one outer tuple and zero outer cross Gram; no outer-pair saving is claimed. The future proof may consume the new margin jointly with other existing estimates, but it must exhibit that changed complete inference.

No sharp square-shell estimate, actual-prime VF payment or rational-to-Hecke identification is assumed. There is no new complete zero bound to transfer to Mertens; any eventual transfer must spend a stated positive loss before claiming a fixed no-loss power, and retain the actual squarefree diagonal and all signed pairs.

### K. Falsification, Independence And Formal Audit

The algebraic proof does not assume the desired endpoint. It changes a specified consumer of available moment estimates. The finite grid is diagnostic; the uniform inequality follows from the exact Bernstein certificate plus its elementary nonnegative-basis proof. The independent implementations validate arithmetic, not independent Referee acceptance of the full mathematical interpretation.

The #1103 PR body is an early work-in-progress description and is not treated as the final proof status. Live metadata says human-merged at 2026-11-07T15:44:29Z, head 06dde8d85985c86481680610b6c86c663be4e242. Dedicated workflow **42386987885**, job **128446349776**, completed successfully. Its tested synthetic merge e9e581ca346364dd6bfa0ec492cdf6ea2a7d7832 and current main have the identical full tree **31c33d2adcc24ac16d0e4e3655c54ed99cf6b9bb**. Its terminal outputs for the generalized band, marked source, four-field moments and row count list only propext, Classical.choice and Quot.sound. Generated sources were downloaded and inspected; their selected hashes match the artifact manifest.

The log also contains two upstream Wiener `sorry` warnings during its prerequisite build. They are not concealed or treated as proof of a target failure: the relevant terminal axiom checks subsequently show no sorryAx. No claim is made that every declaration in that prerequisite is certified. The new RC1-RC4 claims were not compiled, and receive no inherited Lean certification.

The proof artifact ZIP digest is 1e7455779f49942a7ce9d5d0ee00d17601ad83639d43541e5a7e9afd6dee5e1f, exactly matching GitHub artifact metadata. Artifact ID 13579504958. Original OAI source pin is 1581d4cbdd69a0faf34b2089614fe2a814316a6a. Source and artifact provenance are recorded below; no source-only inspection is described as a new Lean run.

### L. Continuity And Specialist Handoffs

Both Eastern dates' seven role files were retrieved in full, with relevant findings, continuation sections, exact selected derivations and correction history read. Unrelated code appendices were not all rerun. At this intake all TODAY reports are AVAILABLE, and YESTERDAY is CARRY_FORWARD. Older embedded TODAY=PENDING markers remain historically accurate for their original runs, not this one.

Continuity consumed: today's Coordinator PG signed-graph restriction; Owner SG and newer RS square-sampled reserve result; Analytic GL and newer FT complete Nyman norm return; Wheel DI and newer LR admitted three-row incidence; own SC signed-label capacities; Referee GL acceptance and NC/PF cutoff qualifications; Lean GL2 implementation. Yesterday's own GM/HC/FW, Coordinator NS/CS, Owner BT/RZ/DR/MS, Analytic FP/RM/AQ, Wheel CP/PB/GF, Referee CP/RM/spectral decisions and Lean sampling/null/increment results retain their scoped status. The newly merged consumer-reuse directive supersedes old mandatory source-cancellation tickets, not those results.

The external inbox has no entry newer than October 18. EXT-20261018-PNT-1, EXT-20261017-XCOORD-1 and EXT-20261014-5 remain source/cutoff/scope cautions, not suppliers for this Hecke detector. Their old cadence and routing language is not live authority.

- Proof Architect: register RC2-RC3 as a concrete post-#1103 consumer improvement, not a new endpoint. Keep the complete HIGH/LOW join and nine-route coverage explicit.
- Analytic: on the next OAI turn, the available small task is to propagate the genuine kappa record through the four-branch count, preserving RC2's exact errors. The existing weighted fourth moment needs no reproof. Other protected route work is not reset.
- Finite Wheel: independently check the physical selection interface, especially the universal 5/222 spare below 7/37 on the plain side, strict inverse nu, empty selections and finite-bin multiplicities. No additional prime census is needed for this scalar certificate.
- Owner: this is not a rational Mobius/VF transfer. Preserve SG/RS and the due JOH route; the complete-consumer method may be useful without identifying the carriers.
- Adversarial Referee: audit RC1's full rectangle, RC2's four fallbacks and loss accounting, the independent 324-coefficient proof, and the distinction between a capacity index and physical Delta. Challenge global bootstrap claims unless the real HIGH hypotheses have been generalized.
- Lean Verification: after independent qualification, the intended useful unit is the kappa-retaining count plus its immediate fixed-amplitude consumer, not a standalone constant lemma with no consumer. Reuse #1103's exact proof artifact and do not alter the original arithmetic suppliers or weaken audits. No branch, PR or launch is requested or performed here.

### M. Ranked Experimental Portfolio

1. **Promote RC2-RC3:** source-backed parameterized detector count and its full-domain certificate; first remaining work is actual downstream integration and independent review.
2. **Keep weighted marked averaging separate:** the 1+D.t/2 supplier is present, but common source assembly widens it; using that extra half-loss needs an explicit consuming branch, not double-credit with the present capacity gain.
3. **Reject H-UNIFORM-BIN; do not assert automatic bootstrap:** exact equality faces and current physical-Delta/beta hypotheses delimit these shortcuts. They do not rule out a different joint consumer.
4. **Carry forward SC capacity-safe transport and NYMAN FT:** no repeated fixed-band matching scan, unchanged prime cutoff, old spectral falsifier or external decimal leaderboard was substituted for new work.

### N. Next-Run Resume Capsule

```text
RUN: 20261107-census-2; scheduled 11:00:01 EST; RUN_ID_UNAVAILABLE.
AUTHORITY: main aa10b310efb2a095fd4c69dc965e6bde0bd135d6.
CHAIN_ACK: CANCELLATION_CHAIN_REUSE_V1.
SOURCE: #1103 generalized source moments and literal marked row count;
        original OAI 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
NEW: kappa-dependent crossing/balance; actual fiber exponent without
     old Delta/4 widening; full detector margin 1/5000+(3-4*kappa)/1600.
DOMAIN: kappa in [1/2,3/4], delta in [0,5/6], x in [0,1/2].
ANALYTIC: strict kappa>1/2, fixed lower floor before constants,
          full-family license, actual rows/profiles/heights/masks unchanged.
CERTIFICATE: 9 boxes, 324 positive rational coefficients; independently
             equal Python power conversion and Node interpolation.
FINITE: 9639 grid +400 Python held-out +401 Node held-out;
        3000 error/branch stress cases, all complete.
REVIEW: SELF_AUDIT; independent Referee PENDING; new claims NOT_FORMALIZED.
NEXT SINGLE TASK: carry RC2 through count_from_raw_moments and
 fixed_amplitude_count_from_raw_moments with the actual Moments record;
 then identify every remaining physical-Delta use before a HIGH extension.
DO NOT: reoptimize the tiny explicit slot denominator, infer a new beta
 from M(kappa), set kappa=1/2 analytically, or iterate the old beta>=7/8 theorem.
NO NEW GLOBAL EXPONENT; canonical VF/RH OPEN; SEARCH_BROAD.
```

All computational sessions finished. Only this authorized own daily report is changed remotely. No Lean source, another report, shared policy, issue/comment, proof branch/PR, workflow, schedule, permission or merge action was modified; no other agent was launched. Publication verification is appended only after actual commit and immutable readback.

### Prepublication Freshness

At 2026-11-07T16:21:43Z, main was re-fetched and remained aa10b310efb2a095fd4c69dc965e6bde0bd135d6. No open/draft PRs were returned. All seven same-day upstream report blobs remained unchanged from intake except this run's own already-verified checkpoint. No unfinished external invocation is presumed complete. The selected source definitions and policy therefore require no changed-dependency rerun.

### Reproducibility And Source Ledger

The code below is the actual successfully executed source, not proposed pseudocode. Run in one directory:

```bash
python consumer_explore.py
python consumer_certificate.py
node consumer_reference.mjs
python consumer_compare.py
python -m py_compile consumer_explore.py consumer_certificate.py consumer_compare.py
node --check consumer_reference.mjs
```

The scripts write their computational JSON outputs under /workspace. The report embeds the full exact coefficient construction and the independent reconstruction, so the durable research evidence does not depend on scratch-file persistence.

| Executed file | SHA-256 |
| --- | --- |
| consumer_explore.py | ffdafa462bd41d502d411a9c1d4b59c5c33c746f2f701a5886ec5f51aaceeaba |
| consumer_certificate.py | 2f1a306e0eda98e1f2f73bb5af3f7905f1cbe845d7d7b10b025a830989e9a3fd |
| consumer_reference.mjs | d3d2cdbef76d23d2f2e680330a237875d2be525d339d5d9e3bc3382a69f062f0 |
| consumer_compare.py | 6d0ed5c616f0f45dc843270f3337755fa6575f2e2ec0355e10ef70108f03206f |

The original executed Python diagnostic-row serialization has SHA-256 ee5e78a5a9ff6b53f8ffcd7dc3fdb7c3c2aed9d8669b2fe491895e5f4a90358e. No C++ execution success is claimed.


#### Main-Source Blobs

All paths in this table are at main aa10b310efb2a095fd4c69dc965e6bde0bd135d6.

| Path | Git blob SHA |
| --- | --- |
| AGENTS.md | 7d19591d69a141c2c094a81a7dff2569562ab892 |
| CURRENT_PROOF_CONTRACT.md | 7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c |
| docs/RHLEAN_REUSE_CANCELLATION_CHAIN_20261107.md | ef8d3ac76a893028f4de772c9a00d3bc261c8132 |
| docs/RHLEAN_PAID_BASELINE_EXACT_CONSUMER_20261106.md | 13d58dd12d90fbf1160812c7c93442dc5d0576ac |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| research/oai_434/RetainedSlotFeedback.lean | 51628cad59734f948224510f7ac94fd68efaacfb |
| research/oai_434/Feedback/Range.lean | 743ad5cca9aa500dcf3f34567cbc6e5f6fa89223 |
| research/oai_434/VF919NativeStrictSevenEighths.lean | efbf2780f0b453a702fb8847f2d360d8faf0fa66 |
| research/oai_434/VF919TiltedProbe.lean | 0f95d412bce773d50e71b1809ab9942653e66812 |
| research/oai_434/VF919TiltedHighAssembly.lean | 883141e0af896d4132bfc4ffa076e2d265ece5c9 |
| research/oai_434/VF919ExplicitFixedSourceSlotCount.lean | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |
| scripts/lean/retained_slot_feedback/prepare_moments.py | 22ee4a6445b242e8a096f54fc923c52d6616e2e0 |
| scripts/lean/retained_slot_feedback/prepare_detector.py | caedf4e83ab4f0890a1e90ad2ddee4eb92e48377 |

#### Original Analytic Source

Repository openai/math, immutable pin 1581d4cbdd69a0faf34b2089614fe2a814316a6a. All source files below were retrieved directly, not inferred from filenames.

| Path below lean/OAI/NumberTheory/DirichletL/ | Git blob SHA |
| --- | --- |
| Hecke/DetectorRawFiber.lean | ee826e81bbec1df5820f26aa15bce53bcb675cd6 |
| Hecke/DetectorRawBranches.lean | 16adf0ef89dafd510b98dd44e9a5461e3fbf351d |
| Hecke/DetectorBranchBudget.lean | 05e7948b9df4c2385d08db006fbdbae56f62b0c3 |
| Hecke/DetectorRowCountCrossing.lean | 43adea8cf7c2ec8639f5b3eb0403d240e4cc8115 |
| Hecke/DetectorRowCountOptimization.lean | 7aa80cdbfadcbf29c6b78199ec15674c99b161f4 |
| Hecke/DetectorRowCountEndpoint.lean | 24ec6bcdaf9e017c41a39c12bc503c86a28d5ef5 |
| Hecke/DetectorCountFromMoments.lean | 91a6e8aa5e0336d6006a5211e77a13f7f8aba348 |
| Hecke/DetectorFixedAmplitudeCount.lean | 0b83ce168a0dd8b82e3d50fb6c04b2f05d1b1d18 |
| Hecke/DetectorRowCount.lean | 27d8321e816fd7eac1369f44e125ee53466cd8d0 |
| Detector/DetectorPlainMarkedFineField.lean | d4b3e96991e97155c064df03b988a5787da3252a |

#### Generated, Compiled Source Evidence

These are artifact SHA-256 values, not Git blob SHAs. Each selected generated file was inspected and matched to its manifest.

| Generated module below research/oai_434/Feedback/ | SHA-256 |
| --- | --- |
| SourceFeedback.lean | 9c7abb4987d79df4489a7f8bcca176ab4427538b7260a0319f4268ceb54169df |
| SourceMoments.lean | 62e95892524f7b5938588985c216e87e9c19fa915291e9f932396c383eac2f67 |
| RowCount.lean | b4e7234e1c40281018455112992945f5677369ec5f373a2cba25e7d9e5c6709c |
| Applications.lean | 7df779842a3c605a322ad0eab20b2f70d54d395f62dd58ea78b20d2aeee637cd |

#### Two-Day Handoff Ledger

Initial agent-reports commit 6d68bdbd6e60d83c6e066ece7dcabb7de3855ee8. AM/PM Coordinator directory entries have identical blobs on each date; one substantive copy was read. TODAY=AVAILABLE for every listed role. YESTERDAY=CARRY_FORWARD. Retrieval and review do not certify every inherited paper claim.

| Role | November 6 blob | November 7 intake blob |
| --- | --- | --- |
| 00-coordinator-am.md | 8812a90540fb511279b5f4ce08e108ef717d5ef1 | 4a71edcce4c44a309640d36e9453d016e5b188a9 |
| 10-owner-payment.md | 1856a96aaaa9d86a5ee2d59ffe50ced936443fa6 | 432fc87602f97318fdac212002b52ac29f12a0e0 |
| 20-analytic-type-ii.md | 7997620b6ab7eb0701296994734ee910df3c3ba1 | 1315b3c9deba1148338d9023af349ee8a246dae7 |
| 30-finite-wheel.md | 3099558194a00358962ff1844bf283e625b9283d | b973552f1574e39afe6dbc165bde3635f12c9ead |
| 40-prime-census.md | c34ac074296e8b2e5b20dee3a2ce02518571206c | c9d78787ca4fca22f89bc9bcaf886e5ae74deda2 |
| 50-adversarial-referee.md | da3265467c799e9d21832ab25245617ba3b15a54 | 787a9030cc6d6f8f63fa89cd3a99d7cf54e25ea5 |
| 60-lean-verification.md | b8bfe3ce9c20d7903395364efb39bcec974c8a2f | 7df1e5d73bfe6cbbb2fa76d6380d7d456a938c11 |

EXTERNAL_HANDOFFS.md blob 038018145c0fddb2f6306c0712373adf9cd1ea52; no November entry. Current own checkpoint was published at 1a03aa3dd4944d85207fcbbcecfe25d2e8ebf568, blob d53e263c98f452691e54976029e4230596caaf53; immutable full readback matched and the commit changed only this report, 64 additions and zero deletions.

#### Executed Source: consumer_explore.py

```python
from fractions import Fraction as F
import json


def values(k, d, x):
    den = 9*k-3*k*x-2*x
    p = (6*k-2*x)*(1-x)
    s = F(5, 6)-d
    j = s*den+d*p
    a = p/den
    t = 1+d*p/(2*j)
    r = 1-d+s*d*p/(2*j)
    e = -F(1, 48)+F(2, 3)*d+d*x/6-F(13, 16)*(1-r)
    return a,t,r,e


if __name__ == '__main__':
    result = []
    for k in [F(1, 2), F(7, 12), F(2, 3), F(3, 4)]:
        best = max((values(float(k), i/240, j/160)[3], i, j)
                   for i in range(201) for j in range(81))
        d, x = F(best[1], 240), F(best[2], 160)
        result.append(dict(k=str(k), delta=str(d), x=str(x),
                           endpoint=str(values(k,d,x)[3]),
                           decimal=float(values(k,d,x)[3])))
    print(json.dumps(result, indent=2))
```

#### Executed Source: consumer_certificate.py

```python
"""Exact retained-capacity certificate; no Lean execution or source modification."""
from fractions import Fraction as F
from itertools import product
from math import comb
import hashlib
import json
import platform
import time

from consumer_explore import values


class Poly:
    def __init__(self, terms):
        self.terms = {a: F(v) for a, v in terms.items() if v}

    @staticmethod
    def cast(value):
        return value if isinstance(value, Poly) else Poly({(0, 0, 0): value})

    def __add__(self, other):
        out = self.terms.copy()
        for a, v in self.cast(other).terms.items():
            out[a] = out.get(a, F(0)) + v
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({a: -v for a, v in self.terms.items()})

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        out = {}
        for a, v in self.terms.items():
            for b, w in self.cast(other).terms.items():
                c = tuple(i+j for i, j in zip(a, b))
                out[c] = out.get(c, F(0)) + v*w
        return Poly(out)

    __rmul__ = __mul__

    def __truediv__(self, other):
        return self * (1/F(other))

    def eval(self, point):
        return sum(v * point[0]**a[0] * point[1]**a[1] * point[2]**a[2]
                   for a, v in self.terms.items())


def bernstein_on_box(poly, bounds, degree=(2, 3, 2)):
    # Exact affine substitution, then power-to-Bernstein basis conversion.
    local = {}
    for a, value in poly.terms.items():
        for j in product(*(range(i+1) for i in a)):
            v = value
            for n, b, (lo, hi) in zip(a, j, bounds):
                v *= comb(n, b)*lo**(n-b)*(hi-lo)**b
            local[j] = local.get(j, F(0)) + v
    answer = {}
    for i in product(*(range(n+1) for n in degree)):
        b = F(0)
        for j, v in local.items():
            if all(j[k] <= i[k] for k in range(3)):
                for k in range(3):
                    v *= F(comb(i[k], j[k]), comb(degree[k], j[k]))
                b += v
        answer[i] = b
    return answer


def certificate():
    d = Poly({(1, 0, 0): 1})
    x = Poly({(0, 1, 0): 1})
    v = Poly({(0, 0, 1): 1})
    k = (3-v)/4
    den = 9*k-3*k*x-2*x
    p = (6*k-2*x)*(1-x)
    s = F(5, 6)-d
    j = s*den+d*p
    margin = F(1, 5000)+v/1600
    h = (2+d*(14-16*x)-96*margin)*j-39*d*s*p
    # Freeze a small rational subdivision before the held-out evaluation.
    cuts = [F(0), F(1, 4), F(1, 3), F(3, 8), F(31, 80), F(2, 5), F(5, 12), F(1, 2), F(2, 3), F(5, 6)]
    boxes = []
    for lo, hi in zip(cuts, cuts[1:]):
        coeff = bernstein_on_box(h, [(lo, hi), (F(0), F(1, 2)), (F(0), F(1))])
        boxes.append(dict(delta=[str(lo), str(hi)], minimum=str(min(coeff.values())),
                          coefficients={','.join(map(str, a)): str(b) for a, b in coeff.items()}))
    return h, boxes


def crossing(k, x, t):
    c = x/(3*k)
    return (c+(2-2*c)*t-x)/(3-x-2*c)


def test_point(k, d, x, t):
    a, tb, rb, e = values(k, d, x)
    rc = crossing(k, x, t)
    mc = t-rc
    assert F(23, 37) <= rc <= 1
    assert F(1, 3) <= mc <= F(1, 2)
    assert 1 <= tb <= F(3, 2)
    assert (1-rc)/2 <= F(7, 37)
    assert 2*rc+8*((1-rc)/2) <= 3-F(9, 37)
    assert (1-2*(mc-F(1, 12)))/(6*k) <= F(1, 6) < F(7, 37)
    short = 1-d+d*a*(F(3, 2)-tb)
    long = 1-d+(F(5, 6)-d)*(tb-1)
    assert short == long == rb
    rcb = crossing(k, x, tb)
    inverse = 1-d*(x+(1-x)*rcb)
    plain = 1-d*(2*(tb-rcb)+x*(1-2*(tb-rcb))/(3*k))
    assert inverse == plain == rb
    old = values(F(3, 4), d, x)
    assert a <= old[0] and rb <= old[2]
    assert (rb == old[2]) == (k == F(3, 4) or d == 0 or d == F(5, 6) or x == 0)
    margin = F(1, 5000)+(3-4*k)/1600
    assert e <= -margin
    return e


def main():
    start = time.perf_counter()
    poly, boxes = certificate()
    out = dict(python=platform.python_version(), boxes=boxes,
               coefficients=len(boxes)*36,
               all_coefficients_positive=all(F(b['minimum']) > 0 for b in boxes))
    print(json.dumps({k: v for k, v in out.items() if k != 'boxes'}, indent=2))
    print('box_minima', [(b['delta'], b['minimum']) for b in boxes])
    assert out['all_coefficients_positive']
    counts = {'registered': 0, 'held_out': 0}
    points = []
    for ik, idelta, ix in product(range(9), range(21), range(17)):
        k, d, x = F(1, 2)+F(ik, 32), F(idelta, 24), F(ix, 32)
        for t in [F(1), F(5, 4), F(3, 2)]:
            e = test_point(k, d, x, t)
            points.append((str(k), str(d), str(x), str(t), str(e)))
            counts['registered'] += 1
    for i in range(1, 401):
        k = F(1, 2)+F((i*37) % 997, 4*997)
        d = F(5, 6)*F((i*53) % 991, 991)
        x = F((i*71) % 983, 2*983)
        t = 1+F((i*89) % 977, 2*977)
        e = test_point(k, d, x, t)
        vv = 3-4*k
        den = 9*k-3*k*x-2*x
        p = (6*k-2*x)*(1-x)
        j = (F(5, 6)-d)*den+d*p
        assert poly.eval((d, x, vv)) == -96*j*(e+F(1, 5000)+vv/1600)
        points.append((str(k), str(d), str(x), str(t), str(e)))
        counts['held_out'] += 1
    out.update(counts=counts, rows_sha256=hashlib.sha256(json.dumps(points).encode()).hexdigest(),
               elapsed_seconds=time.perf_counter()-start)
    with open('/workspace/consumer-certificate.json', 'w') as stream:
        json.dump(out, stream, indent=2)
    print(json.dumps({k: v for k, v in out.items() if k != 'boxes'}, indent=2))
    for k in [F(3, 4), F(2, 3), F(1, 2)]:
        d, x = F(3, 8), F(1, 2)
        print('fixture', str(k), *(str(v) for v in values(k, d, x)),
              'crossing', str(crossing(k,x,values(k,d,x)[1])))


if __name__ == '__main__':
    main()
```

#### Executed Source: consumer_reference.mjs

```javascript
// Independent certificate reconstruction by rational interpolation.
import fs from 'node:fs';
import assert from 'node:assert/strict';

function gcd(a,b) { a=a<0n?-a:a; b=b<0n?-b:b; while(b) [a,b]=[b,a%b]; return a; }
class Q {
  constructor(n,d=1n) {
    n=BigInt(n); d=BigInt(d); assert(d!==0n);
    if(d<0n) { n=-n; d=-d; }
    const g=gcd(n,d); this.n=n/g; this.d=d/g;
  }
  add(b) { b=q(b); return new Q(this.n*b.d+b.n*this.d,this.d*b.d); }
  neg() { return new Q(-this.n,this.d); }
  mul(b) { b=q(b); return new Q(this.n*b.n,this.d*b.d); }
  div(b) { b=q(b); return new Q(this.n*b.d,this.d*b.n); }
  cmp(b) { b=q(b); const n=this.n*b.d-b.n*this.d; return n<0n?-1:n>0n?1:0; }
  toString() { return this.d===1n?`${this.n}`:`${this.n}/${this.d}`; }
}
const q=(a,b=1)=>a instanceof Q?a:new Q(a,b);
const add=(...a)=>a.reduce((s,v)=>s.add(v),q(0));
const mul=(...a)=>a.reduce((s,v)=>s.mul(v),q(1));
const sub=(a,b)=>q(a).add(q(b).neg());
const div=(a,b)=>q(a).div(b);
const pow=(a,n)=>Array.from({length:n}).reduce(s=>s.mul(a),q(1));
const eq=(a,b)=>assert.equal(q(a).toString(),q(b).toString());
function choose(n,k) { let a=1; for(let j=1;j<=k;j++) a=a*(n+1-j)/j; return a; }
eq(add(q(1,3),q(1,6)),q(1,2)); eq(q(-2,-6),q(1,3));

function inverseMatrix(degree) {
  const n=degree+1;
  const a=Array.from({length:n},(_,i)=>[
    ...Array.from({length:n},(_,j)=>mul(choose(degree,j),pow(q(i,degree),j),pow(sub(1,q(i,degree)),degree-j))),
    ...Array.from({length:n},(_,j)=>q(i===j?1:0))]);
  for(let j=0;j<n;j++) {
    let pivot=j; while(a[pivot][j].n===0n) pivot++;
    [a[pivot],a[j]]=[a[j],a[pivot]];
    const scale=a[j][j]; a[j]=a[j].map(x=>div(x,scale));
    for(let i=0;i<n;i++) if(i!==j) {
      const c=a[i][j]; a[i]=a[i].map((x,k)=>sub(x,mul(c,a[j][k])));
    }
  }
  return a.map(row=>row.slice(n));
}

function hvalue(d,x,v) {
  const k=div(sub(3,v),4), s=sub(q(5,6),d);
  const den=sub(sub(mul(9,k),mul(3,k,x)),mul(2,x));
  const p=mul(sub(mul(6,k),mul(2,x)),sub(1,x));
  const j=add(mul(s,den),mul(d,p));
  const margin=add(q(1,5000),div(v,1600));
  return sub(mul(sub(add(2,mul(d,sub(14,mul(16,x)))),mul(96,margin)),j),mul(39,d,s,p));
}

const inverse=(d,x,r)=>sub(sub(1,mul(d,r)),mul(d,x,sub(1,r)));
const plain=(k,d,x,m)=>sub(sub(1,mul(2,d,m)),div(mul(2,d,x,sub(1,mul(2,m))),mul(6,k)));
function crossing(k,x,t) {
  const i0=inverse(q(1),x,q(0)),i1=inverse(q(1),x,q(1));
  const p0=plain(k,q(1),x,t),p1=plain(k,q(1),x,sub(t,1));
  return div(sub(i0,p0),sub(sub(p1,p0),sub(i1,i0)));
}
const short=(k,d,x,t)=>inverse(d,x,crossing(k,x,t));
const long=(d,t)=>add(sub(1,d),mul(sub(q(5,6),d),sub(t,1)));
const cuts=[q(0),q(1,4),q(1,3),q(3,8),q(31,80),q(2,5),q(5,12),q(1,2),q(2,3),q(5,6)];
const degrees=[2,3,2], matrices=degrees.map(inverseMatrix);
const indices=[];
for(let i=0;i<3;i++) for(let j=0;j<4;j++) for(let k=0;k<3;k++) indices.push([i,j,k]);
const key=idx=>idx.join(',');
const boxes=[];
for(let box=0;box<9;box++) {
  let grid=Object.fromEntries(indices.map(([i,j,k])=>[
    key([i,j,k]),hvalue(add(cuts[box],mul(sub(cuts[box+1],cuts[box]),q(i,2))),q(j,6),q(k,2))]));
  for(let axis=0;axis<3;axis++) {
    const next={};
    for(const idx of indices) {
      let v=q(0);
      for(let l=0;l<=degrees[axis];l++) {
        const src=[...idx]; src[axis]=l;
        v=add(v,mul(matrices[axis][idx[axis]][l],grid[key(src)]));
      }
      next[key(idx)]=v;
    }
    grid=next;
  }
  let minimum=grid['0,0,0'];
  for(const b of Object.values(grid)) { assert(b.cmp(0)>0); if(b.cmp(minimum)<0) minimum=b; }
  boxes.push({delta:[cuts[box].toString(),cuts[box+1].toString()],minimum:minimum.toString(),
    coefficients:Object.fromEntries(Object.entries(grid).map(([i,v])=>[i,v.toString()]))});
}
for(let i=1;i<=401;i++) {
  const k=add(q(1,2),q((i*29)%1009,4*1009));
  const d=mul(q(5,6),q((i*43)%1013,1013)), x=q((i*61)%1019,2*1019);
  const f0=sub(short(k,d,x,q(1)),long(d,q(1)));
  const f1=sub(short(k,d,x,q(3,2)),long(d,q(3,2)));
  const t=add(1,mul(q(1,2),div(f0,sub(f0,f1))));
  const row=short(k,d,x,t); eq(row,long(d,t));
  const endpoint=sub(add(q(-1,48),mul(q(2,3),d),div(mul(d,x),6)),mul(q(13,16),sub(1,row)));
  assert(endpoint.cmp(sub(q(-1,5000),div(sub(3,mul(4,k)),1600)))<=0);
}
const out={node:process.version,boxes,coefficients:324,held_out:401};
fs.writeFileSync('/workspace/consumer-reference.json',JSON.stringify(out,null,2));
console.log(JSON.stringify({node:out.node,coefficients:324,held_out:401,
  minima:boxes.map(b=>b.minimum),status:'PASS'},null,2));
```

#### Executed Source: consumer_compare.py

```python
import json
from fractions import Fraction as F
from consumer_explore import values
from consumer_certificate import crossing

with open('/workspace/consumer-certificate.json') as stream:
    python = json.load(stream)
with open('/workspace/consumer-reference.json') as stream:
    node = json.load(stream)
assert python['boxes'] == node['boxes']

checked = 0
paths = {key: 0 for key in ['long', 'inverse', 'plain', 'unmarked']}
for i in range(1, 3001):
    k = F(1, 2)+F((i*29) % 1009, 4*1009)
    d = F(5, 6)*F((i*43) % 1013, 1013)
    x = F((i*61) % 1019, 2*1019)
    t = 1+F((i*79) % 1021, 2*1021)
    gamma = F((i*97) % 1031, 12*1031)
    nu = F(1+(i*107) % 1033, 1200*1033)
    r = (t+gamma)*F((i*109) % 1039, 1039)
    m = max(F(0), t-r-gamma)
    a = values(k, d, x)[0]
    target = max(1-d+d*a*(F(3, 2)-t), 1-d+(F(5, 6)-d)*(t-1))+6*nu+5*gamma
    i0 = max(F(1), (1+5*r)/6)-d*r
    p0 = 1-2*d*m
    rc = crossing(k, x, t)
    if r >= 1:
        choice = i0
        paths['long'] += 1
    elif r >= rc:
        if (1-r)/2 <= nu:
            choice = i0
            paths['unmarked'] += 1
        else:
            z = (1-r)/2-nu
            assert 0 <= z <= F(7, 37) and r+2*z < 1 and 2*r+8*z < 3
            choice = 1-d*r-2*d*x*z
            paths['inverse'] += 1
    elif m >= F(1, 2) or (1-2*m)/(6*k) <= nu:
        choice = p0
        paths['unmarked'] += 1
    else:
        z = (1-2*m)/(6*k)-nu
        assert 0 <= z <= F(7, 37) and 2*m+6*k*z <= 1
        choice = 1-2*d*m-2*d*x*z
        paths['plain'] += 1
    assert choice <= target
    checked += 1
print('PASS: all 324 coefficients agree exactly; branch stress',checked,paths)
```


### Verified Publication Receipt - 20261107-census-2

Observed at 2026-11-07T16:24:51Z: substantive research commit `aa09c2e8f16416677877bd3bf3c61b84240c2dcc`, report blob `2f5786742d542eca625479f33b03ab3845e98c7b`. The immutable full-file readback matched all 118,822 characters of the submitted report. Commit metadata and diff show only `research/agent_reports/2026-11-07/40-prime-census.md` changed, with 778 additions and zero deletions. Prior daily content and the early checkpoint are preserved exactly.

The report validator passed A-N section structure, balanced code fences, the four byte-exact executed source listings and their hashes, and scope/provenance safeguards. This receipt records the already verified substantive commit; its own subsequent save is checked separately. RC1-RC3 remain paper-level, with exact computational certificates, independent Referee review pending and no new Lean certification or global endpoint gain.
