# RH_Lean agent daily report - 2026-11-02 / RH | Owner Payment

## A. Most important mathematical development

**Completed scheduled run. New claim `20261102-owner-1`.**

**Classification:** `PAPER_PROOF / EXACT LEAST-OWNER RANK DECOMPOSITION`; `FINITE_COMPUTATION / FIXED-OWNER SIGN REVERSAL`; `REFUTED` for universal owner-sector sign payment; `IDENTITY_ONLY` for the modular restriction; `NO_FIXED_ETA_GAIN`; `NO_RH`.

The complete chronological JOH displacement can be partitioned by the least prime of each negative composite mismatch after the global positive and negative events are matched in rank order. This preserves the genuine prime/floor-Li event stream and both unequal-count tails.

The ancestry partition supplies two exact restrictions:

1. the total matched displacement is the sum of its owner sectors;
2. for owner (p), its sector displacement is congruent modulo (p) to the negative of the sum of the matched positive primes assigned to that sector. In particular, every singleton owner sector is nonzero.

It supplies no direction of payment. The same genuine owner (p=3) has sector displacement (+2) in square block (r=4) and (-2) in block (r=7). Thus unique least-prime ancestry cannot support any universal per-owner nonnegative or nonpositive JOH displacement theorem. Cross-owner compensation and the exact unmatched tails are unavoidable.

## B. Current authoritative objective

Final live main: `a33987e275f8a431641d3f475b71a24aa2b1437c`, the human merge of PR #1069.

Authority and material blobs:

- `AGENTS.md`: `9fa5e9519e2fb6dde22217aa2a18982dafef373a`.
- `CURRENT_PROOF_CONTRACT.md`: `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`.
- stable selector: `d05c327ae694ea54b599dab0a21032a056b521f1`.
- research engine: `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.
- `VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean`: `9a9336dad72171b6d572a1c1ae88d1ae8b56b530`.
- JOH weighted-composite contract: `27e28f09e9f79e8a60d524e5fcb6f19904fa55f5`.
- JOH coordinate record: `7a286f4bd30dd689281667746ca42d61e4a3a2bb`.
- exact falsifier script: `98c83e6dc5521d8c355cf5648dd5625f3a86c7fd`.

The canonical open objective remains
[
exists Cge0 \orall Rge2,qquad
 |pi(R^2)-VF_{m can}(R^2)|le C Rlog R.
]
For JOH, the external Johnston theorem plus the paper square-endpoint transfer makes eventual (G(R^2)<0) an RH-equivalent open sign condition. The all-route eta gate remains `SEARCH_BROAD`; net endpoint gain after complete return is `UNKNOWN`.

No open or draft PR was returned. Owner ran no Lean compiler, created no proof branch, and changed only this report.

## C. Structural hypothesis investigated

The due protected route was JOH, following the completed 2026-11-01 SAT and VF-LOW turns. The run resumed `20261031-owner-3`, which had proved the exact rank-transport identity and shown that zeroth-moment owner balance loses chronological displacement.

The tested stronger hypothesis was:

> after globally matching positive prime innovations to negative floor-Li composite demands in chronological rank order, grouping matched pairs by the negative event's unique least prime might force a one-sided sector law.

This is the most direct source-faithful least-prime ancestry interpretation because the negative event is an actual composite, while the positive event is an actual prime and has no composite owner. The hypothesis is false even for the fixed owner (p=3).

A weaker structural statement survives: owner sectors obey an exact modular restriction, and singleton sectors cannot vanish.

## D. Mathematical derivation

Use the contract's event coordinate
[
 eta(k)=1_{mathbb P}(k)-\bigl(Q(k)-Q(k-1)\bigr),
 qquad Q(k)=lfloor {m Li}_2(k)floor .
]
Above the proved ternary threshold, let
[
 a_1<cdots<a_P,qquad b_1<cdots<b_N
]
be respectively the locations where (eta=+1) and (eta=-1) in a finite interval with right endpoint (U). A positive location is prime. A negative location is not prime and is a floor-Li arrival, hence is composite on the genuine (kge4) carrier.

Put (m=min(P,N)), and define the chronological matched displacement
[
 D=sum_{i=1}^{m}(b_i-a_i).
]
The complete weighted first moment is
[
 J=sum_{k<U}(U-k)eta(k).
]
Finite rank Fubini gives the already established tail-preserving identity
[
 J=
 \begin{cases}
 D+sum_{i=N+1}^{P}(U-a_i),&Pge N,\
 D-sum_{i=P+1}^{N}(U-b_i),&N>P.
 end{cases}                                                    \tag{37}
]
Thus neither unequal-count tail may be dropped.

For every matched negative event, let (p_i=P^-(b_i)), and define
[
 D_p=sum_{substack{1le ile m\p_i=p}}(b_i-a_i).
]
Unique factor ancestry gives the exact partition
[
 D=sum_p D_p.                                                   \tag{38}
]
Because (pmid b_i),
[
 D_pequiv-sum_{substack{ile m\p_i=p}}a_ipmod p.            \tag{39}
]
If an owner sector contains exactly one matched pair, then
[
 D_p=b_i-a_i
e0,qquad |D_p|ge1.                               \tag{40}
]
Indeed (a_i) is prime and (b_i) is composite, so the two locations cannot agree. Equations (38)-(40) are independent exact restrictions, but none fixes the sign.

The accepted exact fixtures sharpen the falsification to a fixed owner.

For (r=4), on (16<k<25):
[
 (a_i)=(17,19,23),qquad(b_i)=(18,21,24).
]
The owner sequence is ((2,3,2)), hence
[
 D_2=(18-17)+(24-23)=2,qquad D_3=21-19=2,
]
and (J_4=4).

For (r=7), the prime list is ((53,59,61)) and the floor-Li arrival list is ((53,57,61)). The coincident events at (53) and (61) have (eta=0), leaving
[
 (a_1)=(59),qquad(b_1)=(57),qquad P^-(57)=3.
]
Therefore
[
 D_3=57-59=-2,qquad J_7=-2.                                    \tag{41}
]
So the same owner (3) has both displacement signs on the actual carrier.

Finally, least-prime ownership does not canonically allocate positive events before the chronological rank match. Changing a pairing can move displacement between owner sectors while leaving the total sum of matched positions invariant. Rank order removes this ambiguity, but (41) shows that even the canonical chronological allocation has no fixed owner sign.

## E. Quantitative consequence

The new quantitative content is deliberately modest:

- singleton owner sectors have (|D_p|ge1);
- the owner-3 sector assumes both (+2) and (-2) on exact genuine blocks.

These statements are uniform structural restrictions/no-gos, not an upper bound for (J), (G(R^2)), or the canonical VF defect. The modular law (39) can force a sector to be nonzero, but it cannot determine whether that sector pays or worsens the desired wall.

No exponent improves. Any useful JOH theorem must estimate the aggregate
[
 sum_p D_p
]
jointly across owners and then restore the appropriate unmatched tail in (37). Bounding (sum_p|D_p|) or imposing one sign owner by owner destroys the cross-owner cancellation that remains mathematically available.

## F. Falsification and circularity review

- **Actual carrier:** (eta) is the repository's prime-versus-floor-Li ternary stream; no Möbius surrogate was substituted.
- **Chronology:** the matching is global rank order, exactly as in `20261031-owner-3`.
- **Complete first moment:** both unequal-count tails remain in (37).
- **Ancestry:** every negative event is assigned once to its genuine least prime; no composite is cloned.
- **Fixed-owner falsifier:** (41) refutes both (D_3ge0) and (D_3le0) as universal statements.
- **Known fixtures, new consequence:** the (r=4,7) event lists were already accepted as `CE-JOH-R4-R7`; this run derives the sharper fixed-owner reversal rather than rerunning an unmotivated range scan.
- **Circularity:** no eventual sign, prime error bound, or RH-equivalent premise is assumed.
- **Scope:** the result refutes sectorwise sign payment, not every possible cross-owner interlacing theorem.
- **Indexing:** the derivation uses the contract's (k)-event convention. The compiled Lean primitive mismatch has the documented one-step convention and was not silently identified without the contract bridge.

Today's upstream files were absent at intake, so `TODAY=PENDING`. Yesterday was used as `YESTERDAY=CARRY_FORWARD`: Owner blob `40ad74dd7378834a48203153afc30618233f4b04`, Coordinator mirror `8f661bc144fd96ffd7a9a8cd084e74e3df05d1a8`, Lean `6aa7197c4169a70debed607e12f4639218cd21b6`, and the other specialist evidence recorded in those reports. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than 2026-10-18.

## G. Conceptual interpretation

Least-prime ancestry constrains divisibility of negative JOH events, but JOH is a transport problem between two different populations. Unique ownership of the destination does not control its position relative to the matched prime source.

The modular law makes this especially clear: ancestry can force a nonzero local displacement, yet the sign can reverse even for one fixed owner. Thus local owner rigidity creates bills that must be compensated globally; it does not itself supply the payment.

This is a sharper reason that zeroth-moment owner accounting cannot be lifted to the Johnston first moment. The missing mechanism is genuinely cross-owner and chronological.

## H. Competing mechanisms

- **Universal per-owner JOH sign:** abandon; fixed owner (3) has both signs.
- **Singleton owner cancellation:** abandon; (40) proves singleton sectors are necessarily nonzero.
- **Owner modular rigidity:** retain as an exact structural invariant, but classify `IDENTITY_ONLY`.
- **Cross-owner chronological compensation with tails:** continue. It is the only ancestry-based JOH mechanism surviving this test.
- **Count-only or density-only JOH transfer:** remains refuted by (r=4,7).
- **VF-LOW hybrid nonzero-shift covariance:** preserve from `20261101-owner-4`; this due JOH turn did not reopen it.
- **SAT bounded fixed-depth crossing:** remains target-equivalent after full restoration.

## I. Specialist handoffs

**Coordinator / Proof Architect:** register `20261102-owner-1` as a fixed-owner no-go. Do not route JOH through independent owner-sector sign bills. The surviving carrier is the aggregate (sum_pD_p) plus the exact tail from (37).

**Analytic Type II:** a viable estimate must retain cross-owner cancellation. An absolute owner sum is strictly stronger and discards the only surviving compensation mechanism.

**Finite Wheel & Incidence:** investigate joint ordering restrictions between different least-prime sectors, not a sign law within one sector. Equations (39)-(40) are exact regressions.

**Prime Census:** no larger aggregate scan is requested. A discriminating held-out test would tabulate (D_p), the unmatched tail, and cross-owner cancellations, with (p=3,r=4,7) frozen as mandatory regressions.

**Adversarial Referee:** audit the event-index convention, the claim that every negative event is composite, equations (37)-(40), and the owner-3 refinement of the accepted fixtures. Return separate verdicts on identity, fixed-owner falsifier, and quantitative relevance.

**Lean Verification:** only after Referee acceptance, the smallest formal target is a generic finite ordered-support rank/owner partition and modular corollary. The (r=4,7) arithmetic fixtures are low priority. No conjectural cross-owner bound should be formalized.

## J. First independently missing lemma

The first useful JOH ingredient must be a **cross-owner chronological compensation theorem** for the genuine rank-matched sectors, with the correct unmatched tail from (37). It must use more than unique factor ownership and must not take absolute values owner by owner.

No non-circular all-scale inequality of that kind was proved here. Requiring the complete aggregate to have the eventual sign needed for (G(R^2)<0) would be target-equivalent. The next research step is therefore to identify an independently checkable ordering restriction coupling at least two owner classes, and to test it immediately against the fixed (p=3) reversal.

## K. Next-run resume capsule

- Main: `a33987e275f8a431641d3f475b71a24aa2b1437c`.
- New claim: `20261102-owner-1`, equations (37)-(41).
- Status: exact paper derivation plus finite consequence of accepted fixtures; independent review pending; no Lean execution.
- Strongest result: exact least-owner rank partition, modular sector law, singleton nonvanishing, and fixed-owner (p=3) sign reversal.
- Retired mechanism: universal owner-sector sign payment.
- Surviving hypothesis: cross-owner chronological compensation with unequal-count tails.
- Route coverage: this invocation supplies the due JOH attempt; SAT and VF-LOW were substantively covered on 2026-11-01.
- `eta_gate: SEARCH_BROAD`.
- `net_endpoint_gain_after_complete_return: UNKNOWN`.
- Canonical VF theorem, JOH sign, complete shell eta, strict Mertens exponent below (7/8), and RH remain OPEN.

## Publication history

Early `IN_PROGRESS` checkpoint commit: `ce4d06ed905262fa6f8842c8fb5e971b4d159ae2`; checkpoint blob `4ec52d0aaa3cb781aa0b0a1e4c1428704af3b957`.

Final commit/readback verification is appended below.


### Publication verification

The completed synthesis was committed as `617cff97efd9329c12ea0842ce99fe9a704de4c3` and read back as blob `f2491c53b44e55193166185a6f507cceea058ce6` (12,960 characters). Claim `20261102-owner-1`, equations (37)-(41), the fixed-owner (p=3) sign reversal, exact source hashes, classifications, and resume capsule were present. This receipt records publication only and changes no mathematical claim.
