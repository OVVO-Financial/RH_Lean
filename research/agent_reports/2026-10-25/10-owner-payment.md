# RH_Lean agent daily report - 2026-10-25 / RH | Owner Payment

**Status:** COMPLETED  
**Invocation:** scheduled run begun 2026-10-25 20:43 America/New_York  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Primary route:** JOH weighted actual-prime/model displacement, continuing `20261024-owner-1`  
**Result classes:** `PAPER_PROOF / EXACT LEAST-OWNER BARYCENTRE CONSERVATION`, `FINITE_COMPUTATION / OWNER-COUNT SIGN FALSIFIER`, `IDENTITY_ONLY`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`

**Revision history.** The early `IN_PROGRESS` checkpoint surveyed the newly sharpened CORR4 remainder because it was the newest cross-specialist input. After reading the live portfolio and Owner row, this run returned to the authorized prime-side VF-LOW/SAT/JOH lane. The CORR4 calculation is retained below as a secondary comparison, not presented as the Owner lane's new global estimate.

## A. Most important mathematical development

### Claim `20261025-owner-1`: the missing JOH datum is an owner-resolved barycentre, not an owner population

Fix (rge2), (a=r^2), (b=(r+1)^2), and
[
 Q(n)=lfloor operatorname{Li}_2(n)floor,qquad
 delta(k)=Q(k)-Q(k-1),qquad
 eta(k)=1_{mathbb P}(k)-delta(k).
]
On the open block (a<k<b), put
[
 A_r={k:k	ext{ prime}, delta(k)=0},
]
and, for each prime (ple r),
[
 C_{r,p}={k:delta(k)=1, k	ext{ composite}, operatorname{minFac}(k)=p}.
]
Every model-only occurrence is in exactly one (C_{r,p}), including (p=2). No occurrence is cloned.

Let (a_r=|A_r|), (c_{r,p}=|C_{r,p}|), (c_r=sum_p c_{r,p}), and let
[
 J_r=sum_{a<k<b}(b-k)eta(k)
]
be yesterday's within-block chronological residual. Then the exact conservation law is
[
 J_r=b(a_r-c_r)-sum_{kin A_r}k+
       sum_{ple r}sum_{kin C_{r,p}}k.                 	ag{1}
]
The open-block count defect is (c_r-a_r). Hence, when that defect is zero and (m=a_r=c_r>0),
[
 J_r=mleft(
   rac1msum_{ple r}sum_{kin C_{r,p}}k
   -rac1msum_{kin A_r}kight).                      	ag{2}
]

Thus the local JOH sign is exactly the signed difference between the barycentre of once-owned model-only composites and the barycentre of actual-only primes. Least-prime owner counts, even resolved into owner classes, do not contain this positional moment.

## B. Current authoritative objective

Final authority:

- `main@8d3a06d3748282e7e7e5cd273efdd00560cdee15`, tree `5db0af43c7cd30d233daf5f28319ec863c1e6d4a`;
- `AGENTS.md` blob `fe049350c3d6a20096322a2c09c3993c2037022b`;
- `CURRENT_PROOF_CONTRACT.md` blob `93314aebfcc326b27aa5835bd33a23a76923016b`;
- portfolio blob `278cf50c25e30227021f34371932b1edd5e164bd`;
- overlap/imported-7/8 audit blob `c0002af0c26e0e2dff25758a4bc14c38a76f0822`;
- dynamic protocol blob `ff674b509cbdb67aebf635e0d9d5388c08967f12`;
- external handoff index blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.

Material prime-side sources:

- JOH contract blob `27e28f09e9f79e8a60d524e5fcb6f19904fa55f5`;
- floor-Li transport source blob `10829c3857b6a375d1dd8179f78a35550c9e67d8`;
- floor-Li backlog source blob `4255ca0dffe480f2aec6bd0b68797bbd293396c3`;
- merged square birth/transport sources recorded yesterday as `98b3b1a42bdd57152964051fb6f5a49571f03ba7` and `207c379337e239ef5ea84f8597d6858a2560955a`.

The public target remains
[
 exists Cge0, orall Rge2,quad
 |pi(R^2)-operatorname{vfMidFinishedMass}(R)-sqrt2|
 le C Rlog R.
]
It is open. Merged #987 is an imported unconditional (7/8) baseline, not RH. Literal universal square-block capture remains refuted at (R=549).

## C. Structural hypothesis investigated

The hypothesis was that yesterday's missing first moment might become controllable after assigning every model-only composite to its genuine least-prime ancestor.

The exact result is (1)-(2): ancestry gives a lawful, disjoint partition, but the sign lives in the owner-weighted positions, not the populations. A useful future theorem must therefore restrict owner barycentres across blocks or across scales. A wheel capacity theorem that only counts members of each owner fibre cannot determine (J_r).

The carrier is exact:

- actual-only primes retain their genuine integer positions;
- model-only events are actual jumps of (Q=lflooroperatorname{Li}_2floor);
- matched prime/model events cancel once;
- every remaining composite has one least-prime owner (ple r);
- square endpoints are excluded here and remain separate in the global JOH identity;
- no #915 physical weight, mask, clip, historical anchor or NNS term is claimed to be represented by (1).

## D. Mathematical derivation

For (kge3), (delta(k)in{0,1}). Partition the open block into four disjoint cases.

1. Prime and (delta=1): (eta=0), so the matched occurrence cancels.
2. Prime and (delta=0): (eta=1), giving (A_r).
3. Composite and (delta=1): (eta=-1), giving the union of the (C_{r,p}).
4. Composite and (delta=0): (eta=0).

For each composite (a<k<b), its least prime factor satisfies
[
 operatorname{minFac}(k)lesqrt{k}<r+1,
]
hence it is a prime at most (r). Unique factorization makes the (C_{r,p}) disjoint and exhaustive. Therefore
[
 J_r=sum_{kin A_r}(b-k)
      -sum_{ple r}sum_{kin C_{r,p}}(b-k),
]
which expands to (1). If (a_r=c_r=m), the boundary terms cancel and division by (m) gives (2).

Combining with `20261024-owner-1`, the exact all-block crosswalk is
[
 G(B^2)-G(A^2)
 =(B^2-A^2)(P_A-1)
 -sum_{j=A}^{B-1}(B^2-(j+1)^2)D_j
 +sum_{r=A}^{B-1}J_r.
]
Equations (1)-(2) now resolve the last term into genuine least-owner barycentres while preserving every chronological location.

### Secondary CORR4 comparison

On the PR #1021 scalar carrier, write
[
 C_R=M(R-1)-M(R^2-1),quad
 U_R=sum_q M(Y_q)/q,quad E_R=sum_q M(Y_q)^2,quad B_R=C_R-U_R.
]
With (a=9/4) and any (0<b<a), the exact identity is
[
 B_R^2-aE_R
 =rac{a}{a-b}C_R^2
 -aleft(E_R-rac{U_R^2}{b}ight)
 -rac{b}{a-b}left(C_R+rac{a-b}{b}U_Right)^2.       	ag{3}
]
At the on-main frame (b=211/900), this reproduces the optimized (2025/1814) endpoint coefficient and shows precisely which two nonnegative rebates Young's inequality discards. This is `IDENTITY_ONLY`: it does not prove the open physical-remainder premise.

If (b) is replaced by the exact owner mass (S_R=sum_q1/q^2), Lagrange's identity further gives
[
 E_R-rac{U_R^2}{S_R}
 =rac1{S_R}sum_{q<q'}
 left(rac{M(Y_q)}{q'}-rac{M(Y_{q'})}{q}ight)^2.    	ag{4}
]
This preserves all cross-owner interactions and isolates daughter dispersion, but no all-scale lower bound of the needed size was obtained.

## E. Quantitative consequence

No all-scale bound improved.

For JOH, (2) says that zero count defect reduces the problem to a barycentre comparison. Trivial position bounds still give only the natural (O(r^2/log r)) block scale and (O(R^3/log R)) cumulatively, with no favorable sign.

A direct finite falsifier strengthens the count-only warning. In both blocks below, the actual and model populations agree, there are nine unmatched occurrences on each side, and the model-only owner profile has seven even-owner occurrences plus two odd-owner occurrences:

- (r=39): owner histogram ({2:7,3:1,7:1}), (sum A_r=14041), (sum C_r=14056), so (J_{39}=+15).
- (r=44): owner histogram ({2:7,3:1,19:1}), (sum A_r=17923), (sum C_r=17840), so (J_{44}=-83).

Thus parity-resolved owner populations and exact matched count still permit opposite signs. This does not refute a theorem using the full owner labels and positions, nor any nonlocal aggregate law.

## F. Falsification and circularity review

The two finite blocks were recomputed independently with an 80-digit Decimal implementation of
[
 operatorname{Li}_2(n)=operatorname{Ei}(log n)-operatorname{Ei}(log2),
]
using the convergent positive-(x) series for (operatorname{Ei}), plus deterministic trial-division primality and least-factor checks.

For (r=39):
[
 A_r={1523,1543,1549,1553,1559,1567,1571,1579,1597},
]
[
 C_r={1524,1539,1546,1554,1561,1568,1576,1590,1598}.
]
The closest evaluated (operatorname{Li}_2(k)) to an integer on the closed block was more than (1.0358	imes10^{-4}).

For (r=44):
[
 A_r={1951,1973,1979,1993,1997,1999,2003,2011,2017},
]
[
 C_r={1942,1957,1964,1972,1980,1995,2002,2010,2018}.
]
The closest evaluated value was more than (5.8674	imes10^{-4}).

Classification is `FINITE_COMPUTATION`, not interval-certified Lean arithmetic. The exact theorem (1)-(2) is a finite paper proof independent of those witnesses.

Circularity checks:

- (1)-(2) assume neither JOH's eventual sign nor RH.
- They do not replace the global target by a renamed bound.
- Least-prime ownership is used once only.
- No local sign is asserted.
- The all-block criterion remains RH-equivalent through the external Johnston ingredient; the new result only identifies information that a prospective independent proof must use.
- The CORR4 identity (3) is explicitly not counted as a quantitative advance.

## G. Conceptual interpretation

The prime/model event stream has three distinct levels of information:

1. endpoint or owner populations: a zeroth moment;
2. owner-resolved barycentres: the first chronological moment governing JOH;
3. the original #915 physical NNS square: a separate weighted quadratic object with diagonals and all cross terms.

Least-prime ancestry is useful only after it retains location. Owner populations alone lose exactly the datum that changes sign in the two genuine blocks above.

Equation (4) gives the analogous lesson on the recursive Mertens side: the forward frame loses pairwise daughter dispersion. Both routes point to the same methodological rule without identifying their carriers: cancellation must be stated through a complete positional or pairwise invariant, not inferred from population density.

## H. Competing mechanisms

- **CONTINUE:** owner-resolved barycentre transport for JOH, but only as a nonlocal aggregate hypothesis.
- **CONTINUE:** VF-LOW first-lower-escape on the native #915 carrier, with root divisor, masks, anchors, squareful return and NNS restoration.
- **REVISE:** least-owner wheel counts; enrich them by first moments within each fibre.
- **REJECT:** exact block count, parity-resolved count, or owner-population count as sufficient to determine the JOH sign.
- **KEEP DISTINCT:** merged #1019 Möbius birth transport, CORR4, finite A/C, OAI-NNS and NYMAN.
- **CORR4 secondary:** equations (3)-(4) are useful exact accounting, but endpoint excursions observed by Census leave no proved uniform rebate.

## I. Specialist handoffs

**Analytic Type II:** seek a nonlocal estimate for
[
 sum_rleft(sum_psum_{kin C_{r,p}}k-sum_{kin A_r}kight)
]
together with the anchor and weighted block-defect terms, rather than a population estimate. Any claimed sign must survive (r=39,44).

**Finite Wheel & Incidence:** refine owner fibres by their first positional moments. Determine whether CRT/least-factor structure constrains the aggregate centroid over adjacent square blocks; raw fibre cardinalities are insufficient.

**Prime Census:** use (r=39,44) as regression fixtures. Search for two zero-defect blocks with the same complete least-owner histogram but opposite (J_r); that is the smallest decisive falsifier of histogram-only ancestry.

**Adversarial Referee:** review endpoint conventions and the (deltain{0,1}) premise, and reject any inference from (1) to a favorable sign without a separate barycentre theorem.

**Lean Verification:** a nonduplicate formal target is (1)-(2) on finite sets, instantiated with the existing floor-Li event stream and a unique least-factor partition. Do not formalize a sign claim.

**Coordinator:** add “owner-resolved barycentre” below the JOH first-moment node. This run does not discharge the assigned VF-LOW first-escape inequality; that native-weight task remains open.

## J. First independently missing lemma

A useful next lemma must be strictly more arithmetic than the JOH target itself:

> Prove a uniform nonlocal restriction on the owner-resolved barycentre residual
> [
> H_r=sum_{ple r}sum_{kin C_{r,p}}k-sum_{kin A_r}k
> ]
> over an explicitly stated adjacent-block or first-lower-escape family, derived from genuine least-factor incidence and combined with every anchor and weighted defect term in the global crosswalk.

The smallest decisive falsification test is equality of the complete owner histogram with opposite (J_r). A theorem only bounding the complete right side of the global identity by the desired sign is target-equivalent and should be rejected.

## K. Resume capsule

Continuity consumed:

- Today: Wheel blob `414415d53bfedd14ae9b72ed3cc55f65c1477a21`, claim `20261025-wheel-1`; Census blob `25dbde73e5b15bc8e028c69bb05809d2439da8af`, claim `20261025-census-1`; Referee blob `1cbc2e20d211523c926b9bb6a114e959ebbfded5`; Lean blob `a0eb1172c932fdfea9633b7e431a72a53b19e721`. Coordinator and Analytic were `TODAY=PENDING`.
- Yesterday: Coordinator blob `30942030c85ea079c0faacf97f2360cb77aca179`, Owner `3d5a94fdfc2da9b4918c9f9643582060f2105c92`, Analytic `c90beb4c1b5e2ad64e31ec8bc1dda6d36aede6d7`, plus Wheel/Census/Referee/Lean evidence recorded in today's reviewed reports.
- External inbox has no entry newer than 2026-10-18; `EXT-20261018-PNT-1/2` remain secondary.

Live PR/CI final audit:

- #1021 OPEN/non-draft, head `72d7e508ed138d3dbd8adb6f75b51bfef50264ee`: all 13 observed workflows completed successfully.
- #1022 OPEN/DRAFT, head `03f756a4e4954d4df388f26105785cc30e438a16`: all 12 observed workflows completed successfully.
- #1023 OPEN/non-draft, head `44fbcf3f2dcab39c849f8a52cec4202929a734ad`: all 11 observed workflows completed successfully.
- #1024 OPEN/non-draft, head `b74d470093627de6614e516badb70ce444be0398`: all 8 observed workflows completed successfully.

Green CI certifies only declarations at those exact heads. No PR was modified, reviewed or merged; no workflow was rerun; no schedule or permission changed.

New claim: `20261025-owner-1`. Final classification: exact structural paper theorem plus finite sign obstruction; no independent global quantitative restriction, no canonical VF closure and no RH proof.


## Publication verification

The initial `IN_PROGRESS` checkpoint was created by commit `80564e82ea5de6c2fbc03b484f5036da2fe28560`. The completed synthesis was published by commit `93fa82ac4c0f79f30608ad586826d976dd9bcd8a` and immediately read back as blob `00058161e1675ae43e8a400c45bff9cf31e8a1f3`, 13,998 characters, with `COMPLETED`, claim `20261025-owner-1`, and the pinned main SHA present. This verifies report publication only; it does not formalize the paper theorem, prove the missing barycentre restriction, alter main, merge a PR or change a schedule.
