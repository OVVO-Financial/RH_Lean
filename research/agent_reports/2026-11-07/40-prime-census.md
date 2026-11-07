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
