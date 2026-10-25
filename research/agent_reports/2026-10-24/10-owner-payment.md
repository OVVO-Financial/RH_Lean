# RH_Lean agent daily report - 2026-10-24 / RH | Owner Payment

**Status:** COMPLETED
**Run ID:** 2026-10-24T20:43:01-04:00 scheduled invocation
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN
**Live selector:** VF-LOW / SAT / JOH prime-side source ancestry
**Result classes:** `PAPER_PROOF / EXACT CROSS-CARRIER FIRST-MOMENT CONSERVATION`, `REFUTED LOCAL-SIGN AND COUNT-ONLY BRIDGE`, `FINITE_COMPUTATION`, `NO_NEW_GLOBAL QUANTITATIVE_BOUND`

## A. Most important mathematical development

### Claim `20261024-owner-1`: #915-to-JOH transport has an unavoidable first chronological moment

The floor-`Li_2) event stream admits an exact square-block conservation law that separates the information retained by the merged #915 transport boundary from the extra information required by Johnston's weighted statistic.

The #915 historical moving-owner correction records the **zeroth moment** of prime-versus-floor-`Li` arrivals: model demand minus actual prime supply in each square block. Johnston's `G) records a **first moment** of the same arrivals. On a block `[r^2,(r+1)^2)`, the missing term is a signed displacement between the actual prime locations and the deterministic floor-`Li) demand locations.

This is not only a formal distinction. Two genuine blocks have zero #915 block defect but nonzero displacement of opposite signs:

```text
r=4: actual prime arrivals {17,19,23},
     floor-Li arrivals    {18,21,24},
     net count defect 0, signed displacement +4.

r=7: actual prime arrivals {53,59,61},
     floor-Li arrivals    {53,57,61},
     net count defect 0, signed displacement -2.
```

Therefore neither endpoint mismatch counts nor an unsigned matched-population total can determine the JOH contribution. Also, no universal blockwise sign for the displacement survives the actual arithmetic. A valid bridge must retain chronological location, or prove a genuinely nonlocal signed displacement restriction.

## B. Current authoritative objective

Final authority refresh:

- `main@8d3a06d3748282e7e7e5cd273efdd00560cdee15`.
- `AGENTS.md`: `fe049350c3d6a20096322a2c09c3993c2037022b`.
- `CURRENT_PROOF_CONTRACT.md`: `93314aebfcc326b27aa5835bd33a23a76923016b`.
- Ten-route portfolio: `278cf50c25e30227021f34371932b1edd5e164bd`.
- Route-overlap / 7/8 audit: `c0002af0c26e0e2dff25758a4bc14c38a76f0822`.
- Dynamic protocol: `ff674b509cbdb67aebf635e0d9d5388c08967f12`.
- External handoffs: `038018145c0fddb2f6306c0712373adf9cd1ea52`.

Material source blobs:

- lower-channel contract: `6f8decdbe9acc54264ac600d8f0ab1e9b40b2c5d`;
- #915 source-payment status: `aefc7291179e016c995e33b32d4782de3bcca61b`;
- JOH weighted-composite contract: `27e28f09e9f79e8a60d524e5fcb6f19904fa55f5`;
- actual-prime first-bad Mobius trigger: `1163ae30b448b2fdd99fc4bfb4f13b36863a52a9`;
- #915 floor-Li transport boundary: `10829c3857b6a375d1dd8179f78a35550c9e67d8`;
- floor-Li discrete backlog: `4255ca0dffe480f2aec6bd0b68797bbd293396c3`;
- lower-run capacitor: `1318b459e3eabf1439d81f3c8423505425d371be`;
- merged closed-square birth source: `98b3b1a42bdd57152964051fb6f5a49571f03ba7`;
- merged moving transport source: `207c379337e239ef5ea84f8597d6858a2560955a`.

The exact public target is still

```text
exists C >= 0, forall R >= 2,
  |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C*R*log R.
```

The authorized one-sided gate is an eventual lower wall `pi(R^2)-VF_can(R^2) >= -K R log R`. Imported 7/8 gives only `O(R^(7/4+epsilon))), not this wall.

Live GitHub status was rechecked rather than inherited from stale text. There are no open PRs. PR #1019 is merged, not open: head `0d39cfe586b8abf072042899f73bd3e326a29007`, merge `2f4fc830150242b4cc0f9973f1c1b6c8be809fc3`, 2026-10-24T21:57:31Z. PR #1020 is merged as current main.

## C. Structural hypothesis investigated

**Initial hypothesis:** the signed mismatch population already exposed by
`vfMid915HistoricalMovingOwner_eq_signedMismatch` might transfer directly to JOH's weighted composite-removal carrier after once-only pairing.

**Corrected theorem:** it transfers only after adding a first chronological moment. The two carriers are related exactly, but their sufficient bounds are not equivalent.

Here is the source table.

| Carrier | Literal occurrence | Sign / coefficient | Weight and chronology | What is not carried by the scalar |
| --- | --- | --- | --- | --- |
| Floor-Li arrival stream | integer `k` where a genuine prime arrives or `Q(k)-Q(k-1)` jumps | `eta(k)=1_Prime(k)-(Q(k)-Q(k-1))` | located at `k` | none; this is the common linear event carrier |
| #915 moving-owner boundary | actual square-block prime supply versus floor-Li block demand | `D_r=model-actual=-sum eta` on the closed block increment | unit block count; aggregate history telescopes to endpoints | loses within-block locations; full #915 still has native VF weights, masks, clipping, historical anchor, restoration and NNS cross terms |
| JOH `G(N)` | every prime/model arrival below `N`, equivalently each odd composite once by least prime owner in `T(N)` | `eta(k)` or the exact `A-T-L` form | triangular weight `N-k`; odd square endpoints are separate owned occurrences | no #915 NNS normalization or physical seat weight |
| merged #1019 source | ordered Mobius factors `(a,b)` and root birth | `mu(a)mu(b) floor(X/(ab))`; birth `2mu(k)-mu(k)^2` | closed-square prefix and moving complement | not an occurrence map to prime/floor-Li events or the original weighted #915 source |

Thus merged #1019 is exact structure on a different signed carrier. It cannot pay the displacement term by renaming its birth bill.

## D. Mathematical derivation

Let

```text
Q(n)   = floor(Li_2(n)),
E(n)   = pi(n)-Q(n)-1,
eta(k) = E(k)-E(k-1)
       = 1_Prime(k)-(Q(k)-Q(k-1)).
```

The JOH definition is `G(N)=sum_(2<=n<N) E(n)`.

For integers `a<b`, finite Fubini gives the general identity

```text
sum_(n=a)^(b-1) E(n)
 = (b-a)E(a) + sum_(k=a+1)^(b-1) (b-k)eta(k).          (1)
```

Proof: write `E(n)=E(a)+sum_(a<k<=n)eta(k)). A fixed `eta(k)` occurs for exactly `b-k` values of `n).

Now set `a=r^2`, `b=(r+1)^2`, `L_r=2r+1`, and define

```text
J_r = sum_(r^2<k<(r+1)^2) ((r+1)^2-k) eta(k).          (2)
P_r = pi(r^2)-Q(r^2).
D_r = Q((r+1)^2)-Q(r^2)
      -(pi((r+1)^2)-pi(r^2)).
```

The compiled `vfMidFloorLiBlockPrimeDefect r` is exactly `D_r`, and

```text
D_r = P_r-P_(r+1),             E(r^2)=P_r-1.
```

Equation (1) becomes the block law

```text
sum_(r^2<=n<(r+1)^2) E(n) = (2r+1)(P_r-1)+J_r.         (3)
```

For `A<=B`, telescope the endpoint backlogs and reorder finite sums:

```text
G(B^2)-G(A^2)
 = (B^2-A^2)(P_A-1)
   - sum_(j=A)^(B-1) (B^2-(j+1)^2) D_j
   + sum_(r=A)^(B-1) J_r.                               (4)
```

The final coefficient of `D_(B-1)` is zero, as it must be: `G(B^2)` excludes the event at `B^2`. Equation (4) is the exact #915-boundary-to-JOH crosswalk. It preserves the starting historical anchor once, terminal weights on every block defect and the within-block displacement residual. It does not assert the #915 quadratic source payment.

There is also an occurrence-level conservation form. Let `Pset_r` be the multiset of actual prime arrivals in the open block and `Lset_r` the multiset of floor-Li jumps there. Pad the smaller multiset with copies of the right endpoint `(r+1)^2`; those copies have zero triangular weight. For any once-only bijection between the equally sized padded multisets,

```text
J_r = sum_over_pairs (model_location - prime_location).              (5)
```

This is independent of the chosen bijection because only the two sums of locations matter. Matched same-site occurrences cancel once, while unmatched occurrences are transported to the boundary once. There is no cloned history.

## E. Quantitative consequence

The result is structural, not a new RH-scale estimate.

A direct bound from (2) is

```text
|J_r| <= 2r * (# actual arrivals + # model arrivals in the block).
```

Summed to root `R`, PNT and the deterministic Li count give only

```text
sum_(r<R) |J_r| = O(R^3/log R)
                         = O(N^(3/2)/log N),  N=R^2.      (6)
```

This is the natural Johnston main scale, but it has no favorable sign or strict constant. It does not prove eventual `G(R^2)<0`. Inserting imported 7/8 into the complete cumulative discrepancy instead gives the already-audited `O(N^(15/8+epsilon))), not an improvement.

The advance is that the independently missing arithmetic information is now localized: a nonlocal signed restriction on the boundary-padded displacement in (5), together with the weighted block-defect and anchor terms in (4). Endpoint mismatch counts alone cannot supply it.

## F. Falsification and circularity review

1. **Count-only bridge:** refuted. At `r=7`, `D_7=0` but `J_7=-2`.
2. **Universal favorable local sign:** refuted in both directions. `J_4=+4` while `J_7=-2), both with zero net defect.
3. **Finite verification:** a direct Eratosthenes sieve and `Q(n)=floor(Ei(log n)-Ei(log 2))` evaluation gave the listed arrivals. On `16..25` the closest evaluated Li value was more than `0.139` from an integer; on `49..64` it was more than `0.064`. This is reproducible floating finite evidence, not interval-certified Lean arithmetic.
4. **Universal square-block capture:** remains refuted independently at `R=549`; nothing here revives it.
5. **Merged birth telescope:** exact but on Mobius pair occurrences, not the prime/model displacement carrier.
6. **Original #915 source:** equations (1)-(5) concern the linear moving-owner/floor-Li boundary only. They do not drop the physical VF weights, current/historical masks, clipping, protected high-prime star, squareful restoration, zero-target denominator, diagonal or off-diagonal NNS terms.
7. **Circularity:** (1)-(5) are finite identities and assume no PNT, 7/8, RH or source-payment premise. Any bound strong enough to force the sign of the complete right side of (4) must be justified independently; merely naming that bound would be target-equivalent.

## G. Conceptual interpretation

The prime-versus-model stream has a moment hierarchy.

- #915's compiled transport boundary controls a zeroth moment: how many signed mismatches survive.
- JOH asks for a first moment: how far those mismatches occur from the terminal boundary.
- The original #915 NNS payment asks for a quadratic interaction after native physical weighting and restoration.

These are not interchangeable. Prime ancestry becomes useful for JOH only when it constrains **where** least-prime-owned removals occur, not merely how many exist. Equation (5) gives the exact conservation object for that question: signed transport distance between deterministic model arrivals and actual prime arrivals.

## H. Competing mechanisms

- **PROMOTE:** boundary-padded displacement as the correct SAT-to-JOH source adapter. It is exact and falsifiable.
- **CONTINUE:** VF-LOW first-lower-escape on the native #915 carrier, separately retaining its quadratic restoration and NNS terms.
- **CONTINUE:** direct least-prime-owner analysis of the displacement pairs, seeking a nonlocal rather than blockwise sign restriction.
- **REJECT:** endpoint-count or unmatched-population totals as sufficient for JOH.
- **REJECT:** either universal local sign `J_r<=0` or `J_r>=0`.
- **KEEP DISTINCT:** merged #1019 Mobius birth/transport, CORR-A, OAI-NNS and NYMAN.

## I. Specialist handoffs

**Analytic Type II:** attack a signed displacement estimate for (5), not just a count discrepancy. Any proposed estimate must combine with every term in (4) and show its final sign or a strict quantitative gain.

**Finite Wheel:** express each model-demand occurrence that lands on an odd composite by its unique least-prime owner and preserve its location. Determine whether ancestry constrains aggregate displacement over adjacent blocks.

**Prime Census:** reproduce `r=4` and `r=7` with certified intervals for `Li_2), then search specifically for long runs with `D_r=0` and large positive/negative `J_r). Record first violators of every proposed displacement sign or sublinear-lag law.

**Adversarial Referee:** review equations (3)-(5), the endpoint convention and the claim that the new residual is not already another form of `G). Reject any quantitative claim that assumes the sign of the complete right side.

**Lean Verification:** a nonduplicate formal target is the finite Fubini identity (1), its square-block/global specialization (3)-(4), and boundary-padding invariance (5), instantiated with existing `eta`, `vfMidFloorLiBlockPrimeDefect` and `G). Do not formalize a sign theorem.

**Coordinator:** insert a first-moment node between the #915 boundary identity and JOH. The prime-side DAG is now: occurrence stream -> zeroth block defect + displacement -> weighted `G`; the original #915 quadratic payment branches separately.

## J. First independently missing lemma

Find a genuine least-prime-ancestry restriction on the boundary-padded transport pairs in (5) that is stronger than the trivial total-distance bound, survives the opposite-sign blocks `r=4,7`, and combines with the anchor and weighted `D_j` terms of (4) without assuming eventual `G<0`.

A decisive candidate should state its quantifiers and constant on an all-root or admissible first-lower-escape family. The smallest falsification test is a certified scan restricted to blocks with `D_r=0`, measuring signed and absolute padded displacement separately. A merely renamed upper bound for the complete right side of (4) is target-equivalent and should be rejected.

## K. Next-run resume capsule

Continuity consumed:

- Today: Coordinator `30942030c85ea079c0faacf97f2360cb77aca179`, Wheel `d7b956ad3e9f6e27e86644b371f275818a7516fd`, Census `04e90ce7bc531cf06be8fe0418477f4627bd625e`, Referee `8400b8ee3b8e6b68d2fb16ff6ffef395bf5dcca7`, Lean `844b0cc6e49471469e60d9aa362744743c613740`. Today's Analytic report is `TODAY=PENDING`.
- Yesterday is `YESTERDAY=CARRY_FORWARD`: Owner `d8113b78bcf257082de09c8d3580dd752d3a3743`, Analytic `286d3c7f95c605a82ddf2733ca8a474868dfd140`, Wheel `953a8b301b71d03b90388cf03252a3c665080c01`, Census `04cea2f12072607caa2458b8559896afbc8fb072`, Referee `9a4b99fdb924eec703132eda4a230ec553970d34`, Lean `d5ba285902294874821e97b4c71ddf4f9bd54922`; both Coordinator mirrors were absent.
- External inbox has no handoff newer than October 18.
- New claim: `20261024-owner-1`.
- Status: `PAPER_PROOF / EXACT CROSS-CARRIER FIRST-MOMENT CONSERVATION`; no Lean compilation was performed by this report-only agent.
- Strongest obstruction: zeroth-moment #915 mismatch does not determine first-moment JOH displacement, and the actual local displacement has both signs.
- First next action: certified displacement census on `D_r=0` blocks, then formulate an ancestry-based nonlocal restriction rather than a local sign.
- Canonical VF, original #915 payment, eventual JOH sign, independent improved exponent and RH remain OPEN.

## Publication verification

The initial `IN_PROGRESS` checkpoint was created by commit `b34c3b94a59c1586a316b75ec9d2688dc763f402` and read back as blob `a642ba0ad5f8fa1a30ad1f89112cdf8fc20cd9b5`, 4,742 characters, with status present. The completed report was published by commit `047acd3d4730b6d7e68f88ae124a46d6647bdfdb` and read back as blob `82fb60cd5e2921f2504926b725dfa3eb7f747422`, 15,227 characters, with claim `20261024-owner-1` and pinned main SHA present. This verifies report publication only; it does not promote the paper theorem to Lean, alter main, create a proof PR, merge source, or change any schedule.
