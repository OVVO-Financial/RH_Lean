# RH_Lean agent daily report - 2026-10-24 / RH | Analytic Type II

**Status:** COMPLETED
**Run ID:** 2026-10-24T22:26:00-04:00 scheduled invocation
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN
**Route investigated:** JOH / SAT first chronological moment, compared with OAI-NNS resonance
**Result classes:** `PAPER_PROOF / EXACT ASYMPTOTIC COUNTERMODEL`, `REFUTED COUNT-PARITY-DENSITY-ONLY JOH MECHANISM`, `FINITE_COMPUTATION`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`

## A. Most important analytic result

### Claim `20261024-analytic-1`: exact floor-Li demand still admits opposite full-scale parity candidates

Fix a square block
[
  a=r^2,qquad b=(r+1)^2,qquad L=b-a=2r+1.
]
Keep the repository's **exact** deterministic demand
[
 Q(n)=lfloor operatorname{Li}_2(n)floor
]
and its open-block jump set
[
 {cal M}_r={1le i<L:Q(a+i)-Q(a+i-1)=1},qquad q_r=|{cal M}_r|.
]
For any set ({cal P}) of open-block candidate prime locations, put
[
 eta_i=1_{cal P}(i)-1_{{cal M}_r}(i),qquad
 J_r({cal P})=sum_{i=1}^{L-1}(L-i)eta_i.
]
This is exactly Owner claim `20261024-owner-1`'s within-block JOH displacement, in positions relative to the left square.

For every sufficiently large (r), there are at least (q_r) odd integers in the block. Let ({cal P}_r^-) be the first (q_r) odd positions and ({cal P}_r^+) the last (q_r) odd positions. Then both have the exact same population as the floor-Li demand, so the endpoint/count defect is exactly zero:
[
 |{cal P}_r^-|=|{cal P}_r^+|=q_r,qquad sum_ieta_i=0.
]
Nevertheless,
[
 J_r({cal P}_r^-)= +(1+o(1)),{r^2overlog r},qquad
 J_r({cal P}_r^+)= -(1+o(1)),{r^2overlog r}.                 	ag{1}
]

Thus the exact floor-Li locations, exact block population, odd-prime parity, and PNT-sized local density do not determine even the sign of the first chronological moment. The two candidate families attain the full natural block scale. Choosing either orientation block by block gives an abstract cumulative displacement
[
 sum_{r<R}J_r=pmTheta(R^3/log R)
              =pmTheta(N^{3/2}/log N),qquad N=R^2,          	ag{2}
]
which is the scale of Johnston's eventual negative main term.

**Status:** `PAPER_PROOF / EXACT ASYMPTOTIC COUNTERMODEL`. This refutes proof mechanisms using only block counts, parity and average density. The constructed candidate locations are not asserted to be genuine primes. Hence (1) is not a counterexample to JOH, RH, or the actual prime sequence. It proves that a successful JOH estimate must use additional genuine arithmetic information: least-prime composite ancestry, prime-location correlation, or another restriction controlling chronological barycentres.

## B. Authoritative state and source provenance

Final authority refresh:

- `main@8d3a06d3748282e7e7e5cd273efdd00560cdee15`;
- `AGENTS.md` blob `fe049350c3d6a20096322a2c09c3993c2037022b`;
- `CURRENT_PROOF_CONTRACT.md` blob `93314aebfcc326b27aa5835bd33a23a76923016b`;
- ten-route portfolio blob `278cf50c25e30227021f34371932b1edd5e164bd`;
- overlap/imported-7/8 audit blob `c0002af0c26e0e2dff25758a4bc14c38a76f0822`;
- dynamic protocol blob `ff674b509cbdb67aebf635e0d9d5388c08967f12`;
- external handoff index blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.

Material mathematical sources:

- JOH contract blob `27e28f09e9f79e8a60d524e5fcb6f19904fa55f5`;
- signed floor-Li population source blob `9a9336dad72171b6d572a1c1ae88d1ae8b56b530`;
- discrete backlog source blob `4255ca0dffe480f2aec6bd0b68797bbd293396c3`;
- #915 floor-Li transport source blob `10829c3857b6a375d1dd8179f78a35550c9e67d8`;
- lower-channel contract blob `6f8decdbe9acc54264ac600d8f0ab1e9b40b2c5d`.

The compiled theorem
`vfMid915HistoricalMovingOwner_eq_signedMismatch` controls the zeroth signed mismatch on its stated carrier. The JOH note defines
[
 G(N)=sum_{2le n<N}(pi(n)-Q(n)-1)
     =sum_{3le k<N}(N-k)eta(k)
]
and the exact weighted composite-removal identity. Neither source already contains the new extremal theorem (1).

The live canonical objective remains the square-endpoint von Koch bound. Imported #987 supplies the unconditional (7/8) Mertens baseline, not RH. The current portfolio assigns Analytic Type II to a proper-source inequality or a decisive falsifier, plus an independent JOH/NYMAN assessment. Claim `20261024-analytic-1` is the latter falsifier.

## C. Exact finite decomposition and sharp extrema

For arbitrary subsets (P,Msubseteq{1,ldots,L-1}), with
[
 p=|P|,quad q=|M|,quad
 J(P,M)=sum_{i=1}^{L-1}(L-i)(1_P(i)-1_M(i)),
]
write (D=q-p). Then
[
 J(P,M)=-{Lover2}D+
   sum_{i=1}^{L-1}left({Lover2}-iight)(1_P(i)-1_M(i)).    	ag{3}
]
The first term is the count/zero mode. The second is the centered chronological mode. Setting (D=0) deletes only the first term.

Rearrangement gives the exact extrema over all sets of fixed sizes:
[
 J_{max}(p,q)
 ={p(2L-p-1)-q(q+1)over2},                                	ag{4}
]
[
 J_{min}(p,q)
 ={p(p+1)-q(2L-q-1)over2}.                                	ag{5}
]
For (p=q=m),
[
 J_{max}=m(L-m-1),qquad J_{min}=-m(L-m-1).                	ag{6}
]
So even before using the exact floor-Li geometry, zero count defect permits displacement of order (mL). When (masymp L/log(r^2)), this is (r^2/log r).

There is also a fixed-model, parity-restricted finite obstruction. The odd integers in the block occur at relative positions
[
 s,s+2,ldots,s+2(r-1),qquad sin{1,2}.
]
For any fixed model set (M) and any (0le mle r), let (E_m,H_m) be the first and last (m) such odd positions. Then
[
 J(E_m,M)-J(H_m,M)=2m(r-m).                                 	ag{7}
]
Hence a rule knowing the exact model positions but only the actual population and parity has worst-case error at least (m(r-m)). At PNT-sized (m), this is again (asymp r^2/log r).

Equations (3)-(7) are exact finite integer statements. They assume no PNT, RH, imported 7/8 estimate, independence, or sign.

## D. Proof of the source-faithful asymptotic countermodel

Let (n=L-1=2r), and define
[
 A_r(t)=Q(a+t)-Q(a),qquad 0le tle n.
]
Since (1/log x) is positive and its derivative has magnitude at most
(1/(alog^2 a)) on this block,
[
 operatorname{Li}_2(a+t)-operatorname{Li}_2(a)
 ={toverlog a}
 +Oleft({t^2over alog^2a}ight)
]
uniformly for (0le tle n). Taking floors changes a difference by (O(1)), so
[
 A_r(t)={toverlog a}
 +Oleft(1+{t^2over alog^2a}ight).                     	ag{8}
]
A unit Li increment is (<1), hence every (Q)-increment is (0) or (1), and
[
 q_r=A_r(n)={noverlog a}+O(1)
 ={roverlog r}+O(1).                                     	ag{9}
]

Let (S_M=sum_{iin{cal M}_r}i). Discrete summation by parts gives
[
 S_M=nA_r(n)-sum_{t=1}^{n-1}A_r(t)
 ={n(n+1)over2log a}+O(n)
 ={q_rLover2}+O(L).                                       	ag{10}
]
The first (q_r) odd positions have position sum
[
 S_- = q_r^2+O(q_r),
]
while the last (q_r) odd positions have
[
 S_+ = q_rL-q_r^2+O(q_r).
]
Because the populations agree,
[
 J_r(P)=S_M-sum_{iin P}i.
]
Now (q_r/L	o0), (q_r	oinfty), and (9)-(10) give
[
 J_r({cal P}_r^-)
 ={q_rLover2}-q_r^2+O(L)
 =(1+o(1)){r^2overlog r},
]
[
 J_r({cal P}_r^+)
 =-{q_rLover2}+q_r^2+O(L)
 =-(1+o(1)){r^2overlog r}.
]
This proves (1). Standard integral comparison then gives (2).

Every complementary term is visible: the exact model is retained; square endpoints are excluded consistently with Owner's open-block (J_r); parity is retained; and the endpoint count is exactly matched. What is deliberately absent is genuine primality/composite divisibility. That absence is the scope of the no-go.

## E. Numerical falsification checks

Two independent finite checks were executed locally.

1. Exhaustive enumeration for every (3le Lle12) verified the sharp formulas (4)-(5) for all (0le p,q<L). A separate exact integer check for (2le r<20) verified (7) for every (0le mle r).
2. A double-precision diagnostic using (operatorname{Ei}(log n)-operatorname{Ei}(log2)) generated the literal floor-Li jump sets for
[
 r=100,300,1000,3000,10000,30000.
]
The normalized early/late values (J_r/(r^2/log r)) progressed from approximately
[
 (+0.774,-0.754)quad	ext{to}quad(+0.903,-0.903),
]
and the model centroid ratio (S_M/(q_rL)) stayed between (0.4992) and (0.5028).

The asymptotic proof does not depend on floating-point correctness. The finite diagnostic is classified only `FINITE_COMPUTATION`, not interval-certified evidence.

## F. Relevance, imported 7/8, and inverse interpretation

The repository's overlap audit already records that imported 7/8 yields only
[
 |G(N)|=O_arepsilon(N^{15/8+arepsilon})
]
by direct summation, worse than Johnston's (N^{3/2}/log N) sign scale. Claim `20261024-analytic-1` explains the missing information at the block level: zero count mode can coexist with a coherent linear-location mode of the full (r^2/log r) size.

This yields an exact inverse principle. For equal populations (p=q=m>0),
[
 J(P,M)=sum_{iin M}i-sum_{iin P}i
       =m(ar i_M-ar i_P).                              	ag{11}
]
A large JOH block contribution is exactly a large barycentre separation between actual and model arrivals. Therefore a useful independent theorem must restrict this barycentre separation on the genuine prime/least-owner carrier, or prove nonlocal cancellation of these separations with the anchor and weighted block-defect terms in Owner equation (4). Bounding only population discrepancies cannot do so.

This is structurally analogous, but not mathematically identified, with Referee claim `20261024-referee-1`: in OAI-NNS, an inverse sextic row mode survives a proposed character average; in JOH, the centered chronological mode survives removal of the count mode. In both cases the coherent projection must be isolated and paid before an oscillatory estimate can apply.

**Quantitative gain over imported 7/8:** NONE.  
**Decision:** `REJECT` count/parity/PNT-density-only JOH transport; `CONTINUE` genuine least-prime ancestry and nonlocal chronological correlation.

## G. OAI-NNS continuity and nonduplication

Yesterday's claim `20261023-analytic-1` remains valid as a paper theorem: bounded tuple multipliers preserve the one-(ell^{6/5}), remaining-(ell^1) convolution estimate, with normalized exponent
[
 m+W/2-(	heta+1/6)w_r.
]
Today's Wheel heavy-slot split is exact structural progress, but Referee's actual inverse-row resonance shows why a bare sextic numerator average cannot pay the complete low source. I did not restate that already-reviewed obstruction as a new theorem.

The surviving OAI program requires:

1. an occurrence-preserving two-channel heavy-slot source adapter;
2. an explicit inverse-sextic resonant projector;
3. a separate uniform bound for the resonant coefficient;
4. a nonresonant fixed-order moment/period estimate;
5. principal, collision, normalization and full signed NNS cross bills.

No native exponent improvement beyond imported 7/8 follows from the current exact decompositions.

## H. Continuity, PRs, and verified CI evidence

Today's reports consumed:

- Owner blob `3d5a94fdfc2da9b4918c9f9643582060f2105c92`, claim `20261024-owner-1`;
- Wheel blob `d7b956ad3e9f6e27e86644b371f275818a7516fd`, claim `20261024-wheel-1`;
- Census blob `04e90ce7bc531cf06be8fe0418477f4627bd625e`;
- Referee blob `8400b8ee3b8e6b68d2fb16ff6ffef395bf5dcca7`, claim `20261024-referee-1`;
- Lean blob `844b0cc6e49471469e60d9aa362744743c613740`.

Owner records today's Coordinator blob `30942030c85ea079c0faacf97f2360cb77aca179`, but its path could not be fetched through the known canonical names; classified `TODAY=PATH_UNRESOLVED`. October 23 Coordinator mirrors were absent.

Yesterday is `YESTERDAY=CARRY_FORWARD`: Owner `d8113b78bcf257082de09c8d3580dd752d3a3743`, Analytic `286d3c7f95c605a82ddf2733ca8a474868dfd140`, Wheel `953a8b301b71d03b90388cf03252a3c665080c01`, Census `04cea2f12072607caa2458b8559896afbc8fb072`, Referee `9a4b99fdb924eec703132eda4a230ec553970d34`, Lean `d5ba285902294874821e97b4c71ddf4f9bd54922`. The external inbox has no entry newer than October 18.

Final live PR search returned no open PRs. Historical text calling #1019 open is stale:

- PR #1019 head `0d39cfe586b8abf072042899f73bd3e326a29007`, merged as `2f4fc830150242b4cc0f9973f1c1b6c8be809fc3` at 2026-10-24T21:57:31Z. All 11 fetched exact-head workflows succeeded, including closed-square birth-time run `40134127388`, proof inventory, export, targeted Lean and source audits.
- PR #1020 head `effff7a0462a149b0ff6ae3a200b802802703c12`, merged as current main `8d3a06d3748282e7e7e5cd273efdd00560cdee15` at 2026-10-24T22:29:18Z. All six fetched exact-head workflows succeeded, including portfolio audit run `40138130512`.

The #1019 theorems are exact birth/transport identities and do not imply a quantitative gain. No workflow was rerun, no PR changed, and no source or main branch was written by this report-only agent.

## I. Handoffs and first missing theorem

**Owner Payment / Finite Wheel:** use (11) as the precise SAT-to-JOH bill. A useful theorem must control the genuine prime-versus-floor-Li barycentre after least-prime ownership and odd-square endpoints are restored. Population balance alone is formally insufficient.

**Prime Census:** on genuine blocks, record (q_r), prime count, count defect, model/prime centroids and (J_r). Pre-register tests of cumulative barycentre compensation over dyadic root windows. Compare with the extremal envelope (4)-(7); do not infer an infinite sign from finite trends.

**Adversarial Referee:** audit the uniform floor expansion (8), Abel step (10), and exact endpoint conventions. The no-go concerns count/parity/density proof inputs, not genuine primes.

**Lean Verification:** suitable nonduplicate formal targets are the exact finite decomposition (3), extrema (4)-(6), and parity spread (7). Do not formalize asymptotic Li estimates or a JOH sign theorem without independent review.

**Coordinator:** insert a `JOH-CENTROID` node beneath Owner's first-moment adapter. Its input is a genuine arithmetic restriction on barycentre separation, not another endpoint discrepancy estimate.

The first independently missing mathematical theorem is:

> Prove a uniform nonlocal restriction on the actual prime/floor-Li barycentre separations (m_r(ar i_{{cal M}_r}-ar i_{{cal P}_r})), with exact unequal-count corrections, strong enough after summation to force the complete Owner crosswalk negative; derive it from genuine least-prime composite ancestry or another independent prime-location theorem.

A merely assumed bound on the complete sum is JOH/RH-equivalent and receives no reduction credit.

## J. Resume capsule

- New claim: `20261024-analytic-1`.
- Status: `PAPER_PROOF / EXACT ASYMPTOTIC COUNTERMODEL`.
- Strongest exact theorem: fixed sizes have extrema (4)-(6); fixed model plus parity has unavoidable spread (7).
- Strongest source-faithful falsifier: exact floor-Li demand with equal-count earliest/latest odd candidates gives opposite opposite-sign `(1+o(1)) * r^2 / log r` displacement.
- Mechanism rejected: block counts, parity and PNT-sized density as sufficient JOH control.
- Mechanism surviving: genuine least-prime ancestry controlling chronological barycentres nonlocally.
- Imported 7/8 improvement: NONE.
- OAI-NNS state: resonant projector and two-channel source adapter still missing.
- Canonical VF, eventual JOH sign, improved Mertens exponent and RH remain OPEN.

## K. Publication verification

The early `IN_PROGRESS` checkpoint was created by commit
`0231874b77140f52e97df7fe27bcfe63c1b9512f` and read back as blob
`582f0b143a96f688660b9b70cf0fcc68fe2dacec`, 3,980 characters.

The completed report was published by commit `67366227c757f253ede51a3a995a6cb3250a0c94`. Immediate readback returned blob `4d535a2434aabc6eb36270aa517347c4bf66eda4`, 15,726 characters, with `COMPLETED`, claim `20261024-analytic-1`, and the pinned main SHA present. Publication verifies only this report, not the paper theorem, Lean certification, a source change, PR status change, merge, or schedule change.
