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
