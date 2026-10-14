# RH_Lean Adversarial Referee — 2026-10-14

## Provenance

- **Report date (America/New_York):** 2026-10-14
- **Agent / stage:** RH | Adversarial Referee / `50-adversarial-referee.md`
- **Run ID / sequence:** 2026-10-14T03:34:01-04:00 / first referee run observed today
- **Checkpoint time:** 2026-10-14T03:39:25-04:00
- **Previous own checkpoint:** NONE; today's assigned file returned GitHub 404
- **Observed `main` HEAD SHA:** `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`
- **Central contract fetched:** SUCCESS; `AGENTS.md` blob `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; `CURRENT_PROOF_CONTRACT.md` blob `f6e8dc6813ec63974489c26b0c383e34203f0aa9`
- **Report target:** `agent-reports:research/agent_reports/2026-10-14/50-adversarial-referee.md`
- **Upstream reports actually read:** `00-coordinator-am.md` PENDING (404); `10-owner-payment.md` PENDING (404); `20-analytic-type-ii.md` PENDING (404); `30-finite-wheel.md` blob `e86a066b5fe4488972f9b49400ebb77d76cab41b`; `40-prime-census.md` blob `fc25130ac028c2556f1754ac75ee494c440e3dbc`
- **Publication status:** INITIAL_CHECKPOINT / IN_PROGRESS
- **Lean status:** no compilation claimed

## Current central research objective

The sole public target is `VFCanonicalSquareVonKochStatement`: there exists a fixed `C >= 0` such that
`|pi(R^2) - vfMidFinishedMass R - sqrt(2)| <= C R log R` for every `R >= 2`.
The raw historical owner-payment coefficients remain unchanged. Any transfer to the canonical phase must use the exact raw/canonical bridge; finite A/C and CORR-4 remain sufficient alternatives, not established conclusions.

## Work in progress

The only substantive current-day submission is the wheel-30 late-owner fibre/run restriction and its independent census reproduction. The referee is checking the exact source declarations, strict endpoint conventions, residue table, summation direction, arithmetic multiplicities, counterexamples to stronger variants, and whether any claimed transfer reaches the signed historical source.

No recommendation in this checkpoint is final.

## Next-run resume capsule (non-authoritative)

- **Checkpoint:** 2026-10-14T03:39:25-04:00 on main `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`
- **Upstream consumed:** wheel Claims `20261014-wheel-1..4`; census Claims `20261014-census-1..5`; stages `00/10/20` PENDING
- **First unresolved task:** independently verify the source-level child carrier and exact wheel/run inequalities, then issue claim-by-claim ACCEPT/REVISE/REJECT verdicts
- **Avoid:** treating unsigned capacity or finite ratios as signed source payment or an all-scale discrepancy bound


---

## Completed referee update — 2026-10-14T03:41:35-04:00

- **Actual completion time:** 2026-10-14T03:41:35-04:00
- **Warm-start cache status:** no prior own mathematical result reused; current authority, source blobs, and current-day upstream blobs were freshly fetched
- **CI evidence:** combined-status and commit-workflow queries for current main returned no statuses/runs. Source declarations were inspected, but this run does not independently claim Lean compilation or axiom-check execution.
- **Execution environment/tools:** GitHub connector reads/writes; CPython 3.12 exact integer enumeration; no local Lean execution

## Upstream availability

| Stage | Result actually retrieved |
| --- | --- |
| `00-coordinator-am.md` | `PENDING` (GitHub 404) |
| `10-owner-payment.md` | `PENDING` (GitHub 404) |
| `20-analytic-type-ii.md` | `PENDING` (GitHub 404) |
| `30-finite-wheel.md` | blob `e86a066b5fe4488972f9b49400ebb77d76cab41b`; Claims `20261014-wheel-1..4` |
| `40-prime-census.md` | blob `fc25130ac028c2556f1754ac75ee494c440e3dbc`; Claims `20261014-census-1..5` |

No claim is inferred for a missing stage.

## Current central research objective

The sole public target on current `main` is `VFCanonicalSquareVonKochStatement`:

```text
exists C >= 0, forall R >= 2,
  |primeCounting(R^2) - vfMidFinishedMass(R) - sqrt(2)| <= C R log R.
```

The canonical phase is the fixed additive `sqrt(2)` translation. Original owner/FTA declarations remain in raw coordinates. A raw-to-canonical quadratic transfer must retain the correction `-2 sqrt(2) D_raw + 2`. Finite A/C and CORR-4 remain open sufficient alternatives. The genuine signed first-bad payment and RH remain open.

## Authoritative carrier and dependency audit

Relevant current-main declarations inspected:

- `research/VF_MID_DYADIC_OWNER_PARITY_TWO.lean`, blob `fb025b16bbbd6ca4bcf6288745c283aefa913218`: four-slot inclusion and the compiled-source two-slot parity theorem.
- `research/VF_MID_DYADIC_OWNER_EXACT.lean`, blob `95e7aa05b62861a19f0179aa529f817e3a402bba`: disjoint least-prime-owner partition, child primality on subdoubling runs, and `vfMidDyadicLateRemoval_eq_ownerCensus`.
- `research/VF_MID_DYADIC_PREFIX_OWNER.lean`, blob `6757501bfc343d51ddb34483f8195da4a2c84047`: `PrefixSupply`, `PrimeSupply`, and `LateRemoval = PrefixSupply - PrimeSupply`.
- `research/VF_MID_DIRECT_ROUGH_CHILD.lean`, blob `3da99cd7208ab97abb55d900c3703c65056bdea5`: genuine least-prime child carrier.
- `research/VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE.lean`, blob `8419a4b858440427ed819f92a852bcf722c1b5a8`: existing exact wheel-30 carrier and warning that the finite wheel alone does not prove the required signed bound.

For integers `5 <= A <= R < 2A` and prime late owner `p` with `A < p <= R`, the original population under review is

```text
F(A,R,p) = {n : R^2 < n < (R+1)^2,
                 n composite, minFac(n) = p}.
```

The source map is `n |-> q=n/p`. It preserves cardinality on this fibre. Source proves `q` prime, `p <= q`, and

```text
floor(R^2/p) < q <= floor(R^2/p) + 4.
```

This carrier has unit unsigned occurrence weights. It does not contain the raw VF seat coefficient, either channel wall, historical anchor, survivor/admission mask, clipping weight, returned-pair multiplicity, cross-owner term, or a complete lower-child historical run.

## Independent exact checks

An independent CPython 3.12 integer program regenerated

```text
W30(t) = #{j in {1,2,3,4} : gcd(t+j,30)=1}
```

for every residue modulo 30. It obtained:

```text
W30=0: 1,2,23,24
W30=2: 9,10,15,16,27,28
W30=1: the other 20 residues.
```

It then enumerated every unique `(R,p)` fibre induced by some admissible `5 <= A <= 5000`, `A <= R < 2A`: 2,958,534 fibres, 875,016 nonempty fibres, 587,288 capacity-two fibres, maximum actual fibre size two, and zero violations. Runtime was 4.000195 seconds in this run. The first lexicographic two-child fibre was independently confirmed as `(A,R,p,t)=(12,22,17,28)` with children `(29,31)`.

Independent exact aggregate reproduction:

| Run | Actual | Owners | Parity cap | Wheel cap | `(W0,W1,W2)` |
| --- | ---: | ---: | ---: | ---: | ---: |
| `[50,100)` | 131 | 268 | 536 | 282 | `(39,176,53)` |
| `[100,200)` | 463 | 1,033 | 2,066 | 1,091 | `(142,691,200)` |
| `[2634,5267)` | 125,272 | 426,984 | 853,968 | 454,679 | `(56,989,285,311,84,684)` |
| `[5000,10000)` | 385,553 | 1,411,740 | 2,823,480 | 1,504,048 | `(188,345,942,742,280,653)` |

The run also confirmed the zero-capacity witness `(9,16,11,23)`, repeated owner `p=7` at `77` and `91`, and repeated child/partner `q=13` at `91` and `143`. All decisions used integer arithmetic.

## Claim-by-claim verdicts

### `20261014-wheel-1` — proposing agent: Finite Wheel & Incidence

- **Exact statement:** for all naturals `A,R,p`, if `5 <= A <= R < 2A` and `p` is a genuine late least-prime owner, then `|F(A,R,p)| <= W30(floor(R^2/p))`.
- **Dependencies:** exact child-cardinality map; subdoubling child primality; four-slot inclusion; `p>A>=5`.
- **Independent proof:** every child `q` is prime and `q>=p>A>=5`, hence is divisible by none of `2,3,5`; therefore `gcd(q,30)=1`. The child carrier is a subset of the four stated slots, so its cardinality is at most their wheel-survivor count.
- **Hypothesis audit:** strict endpoints and the upper quotient `floor(((R+1)^2-1)/p)` are compatible with the source inclusion. No distribution, independence, signed cancellation, or RH premise is used.
- **Falsification:** zero failures in the exact range above; capacity two is attained at `(12,22,17)`.
- **First missing obligation:** a new Lean declaration for this exact wheel bound and verified CI/axiom output. The paper implication itself has no missing mathematical step.
- **Novelty:** a small carrier-specific corollary combining existing child and wheel facts; it is not a new source-payment estimate.
- **Recommendation:** **ACCEPT** at `PAPER_PROOF` scope. Not `PROVED_IN_LEAN` in this run.

### `20261014-wheel-2` — proposing agent: Finite Wheel & Incidence

- **Exact statement:** for all `5 <= A <= B <= 2A`, with
  `W(A,B)=sum_{R in [A,B)} sum_{p in LateOwners(A,R)} W30(floor(R^2/p))`,
  `LateRemoval(A,A,B) <= W(A,B)` and `PrefixSupply(A,A,B)-W(A,B) <= PrimeSupply(A,B)` (with natural sums cast to reals).
- **Dependency chain:** Claim 1 summed over the exact disjoint owner census; then `LateRemoval=PrefixSupply-PrimeSupply` and linear rearrangement.
- **Audit:** for every `R<B<=2A`, `R<2A`, so Claim 1 applies. Owner fibres are counted once by `minFac`; no cross-owner multiplicity is introduced. The second inequality direction is correct.
- **First missing obligation:** formal definition of `W30`, finite-sum coercions, and a Lean proof/CI run.
- **Novelty:** deterministic improvement of the unsigned parity budget, not an improvement of the signed source residual.
- **Recommendation:** **ACCEPT** at `PAPER_PROOF` scope, strictly as an unsigned run budget.

### `20261014-wheel-3` — proposing agent: Finite Wheel & Incidence

- **Exact submitted content:** a refutation of the universal one-child strengthening, plus zero-capacity, repeated-owner, and repeated-partner examples, followed by a warning about historical-charge reuse.
- **Confirmed counterexample:** `A=12,R=22,p=17`, with physical composites `17*29=493` and `17*31=527`, both strictly in `(22^2,23^2)`. Thus `|F|=2`; any theorem asserting `|F|<=1` under the same hypotheses is `REFUTED`.
- **Multiplicity diagnostics:** `p=7` occurs in distinct blocks; `q=13` occurs with distinct owners. These are exact arithmetic examples.
- **Scope failure:** the examples do not identify a particular original historical source tag or coefficient and therefore are not themselves counterexamples to a fully specified signed owner-payment theorem. They demonstrate the obstruction any such theorem must address.
- **Recommendation:** **REVISE** the compound claim into: (i) **REJECT / REFUTED** for the universal one-child theorem; (ii) **ACCEPT / FINITE_COMPUTATION** for the exact examples; (iii) retain the history-reuse conclusion only as a diagnostic until the source-tag bridge is stated.

### `20261014-wheel-4` — proposing agent: Finite Wheel & Incidence

- **Exact scope:** finite exact enumeration, including the residue table, selected run totals, and absence of wheel-cap violations in stated ranges.
- **Independent reproduction:** all reported selected totals above and the complete induced fibre scan through `A<=5000` agree exactly.
- **Limit:** finite enumeration neither proves the paper theorem nor an all-scale residue-dispersion estimate; the paper theorem is justified separately by Claim 1.
- **Recommendation:** **ACCEPT** as `FINITE_COMPUTATION` only.

### `20261014-census-1` — proposing agent: Prime Census Laboratory

- **Exact statement:** independent paper verification and finite falsification of `20261014-wheel-1` on the same genuine carrier.
- **Audit:** proof and table are correct; the finite coverage condition `max(5,floor(R/2)+1) <= A < p` correctly reduces all admissible `A<=5000` to unique `(R,p)` fibres.
- **Recommendation:** **ACCEPT** as `PAPER_PROOF` plus separately scoped `FINITE_COMPUTATION`.

### `20261014-census-2` — proposing agent: Prime Census Laboratory

- **Exact statement:** independent verification of the run inequality and exact aggregate totals.
- **Audit:** summation and inequality direction are correct; reproduced totals agree. No signed consequence follows.
- **Recommendation:** **ACCEPT** as `PAPER_PROOF` for the run inequality and `FINITE_COMPUTATION` for the values.

### `20261014-census-3` — proposing agent: Prime Census Laboratory

- **Exact statement:** lexicographic minimality of the saturation witness in the tested admissible domain and confirmation of the zero/repeated ancestry examples.
- **Audit:** exhaustive independent search through all smaller admissible `A` confirmed the first saturation. The arithmetic witnesses are exact.
- **Recommendation:** **ACCEPT** as `FINITE_COMPUTATION`; the one-child strengthening is `REFUTED`. Treat historical availability only as a diagnostic requirement, not as a proved statement about an unstated source ledger.

### `20261014-census-4` — proposing agent: Prime Census Laboratory

- **Exact statement:** a separate physical least-factor scan reconstructed every retained object as `n=pq` with distinct primes and found `mu(n)=+1`, with the reported conservation equalities.
- **Arithmetic audit:** on this carrier, `p<q` are distinct primes, so `mu(pq)=(-1)^2=+1` exactly. The reported strict-interior visit counts equal `B^2-A^2-(B-A)`: 20,800,700 and 74,995,000. The disclosed initial square-endpoint bug was correctly excluded from the final carrier.
- **Evidence limit:** this referee did not rerun the full C++ segmented implementation; the independent prime-pair totals and the mathematical Mobius sign implication agree with it.
- **Recommendation:** **ACCEPT** as `FINITE_COMPUTATION`, with no all-scale or signed-source inference.

### `20261014-census-5` — proposing agent: Prime Census Laboratory

- **Exact claim:** no adaptive residue-dispersion theorem or source-payment theorem was obtained; the displayed ratios are finite diagnostics only.
- **Audit:** correct. Near-20% frequency of capacity-two residues does not imply an all-scale bound below two because `floor(R^2/p) mod 30` is an adaptive prime-owner sequence.
- **Recommendation:** **ACCEPT** as `NO_NEW_RESULT` and as an accurate proof-strength limitation.

## Counterexamples and diagnostics

### Confirmed counterexample

The universal statement “every genuine late owner fibre has at most one child” is false under its intended hypotheses, by `(A,R,p)=(12,22,17)` and children `29,31`.

### Diagnostic examples, not counterexamples

- Repeated `p=7` and repeated `q=13` expose potential multiplicity errors, but do not refute a theorem that correctly retains separate occurrence tags and coefficients.
- The historical `K=0.019` narrow-wall event near `R=1031` was not used as a counterexample: none of today's accepted claims assumes the full global first-bad premises or transfers the unsigned wheel population to signed source payment.
- Off-critical oscillatory models are not germane to the finite carrier inclusions reviewed here.
- Failure to find a wheel-cap violation is not proof; the independent paper inclusion supplies the all-scale argument.

## Circularity, coefficient, and novelty findings

1. No circularity occurs in the wheel inclusion itself; it uses only exact FTA child structure and divisibility by `2,3,5`.
2. A circular or invalid step would occur if the unsigned bound were substituted for `VFMidDyadicSignedLateCorrectionStatement`, `VFMid915FirstBadSourcePaymentStatement`, actual-prime admissibility, or the canonical endpoint bound. None of those follows.
3. The wheel result counts unit occurrences. Original raw VF arithmetic has nontrivial seat weights, both walls, anchor terms, masks, clipped exits, cross-owner signs, returned-pair multiplicities, and complete historical lower-child runs. No coefficient-preserving bridge was supplied.
4. The canonical `sqrt(2)` translation changes the public discrepancy but not historical raw coefficients. No raw/canonical energy equality may be inferred without the exact correction term.
5. Wheel-30 is already present on current main as a fixed carrier. The genuinely new content is the small per-fibre four-slot capacity corollary and adaptive sum, not discovery of wheel-30 or a new signed estimate.

## Outstanding proof obligations

1. Formalize `W30` and Claims `20261014-wheel-1` and `-2`; obtain warning-fatal Lean and standard-axiom CI evidence on an authorized proof PR.
2. `SOURCE-SPLICE-1`: prove an exact occurrence-, coefficient-, sign-, mask-, clipping-, owner-, anchor-, cross-term-, and chronology-preserving equality from the actual first-bad source to the safe/sector-six ledger.
3. Prove history availability: each negative historical contribution may be spent no more often than separately tagged source occurrences permit.
4. If an aggregate constant below the parity cap is needed, prove `W30-RESIDUE-DISPERSION` for the adaptive actual owner residues; complete-period averages and finite ratios are insufficient.
5. Preserve the raw/canonical bridge and do not import the wheel budget as a bound on signed residuals.

## Lean Verification handoff

Claims `20261014-wheel-1` and `20261014-wheel-2` are suitable for a focused formalization as exact finite-carrier corollaries. Their proposed status remains `PAPER_PROOF` until actual PR CI and axiom evidence exist. No source-payment, canonical discrepancy, finite A/C, CORR-4, actual-prime admissibility, or RH closure should be opened from these results.

## Recommendation to the evening Coordinator

- Carry the two wheel claims as accepted supporting lemmas only.
- Record the one-child strengthening as refuted.
- Keep the three missing early stages `PENDING` rather than synthesizing absent owner or analytic progress.
- Prioritize `SOURCE-SPLICE-1` over further scans of the unchanged unsigned carrier.
- Do not repeat the `A<=5000` census unless source definitions, endpoints, or the proposed wheel predicate change.

## Final report summary

**Net-new accepted mathematical progress:** an exact paper-level wheel-30 fibre cap and its unsigned run corollary, plus independently reproduced finite data.

**Production proof status:** `NO_NEW_RESULT`. The signed source inlet, canonical endpoint bound, finite A/C, CORR-4, actual-prime admissibility, and RH remain open.

**Completeness:** DONE for all current-day claims actually published before this run.

**No RH-proof claim:** yes.

## Next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** 2026-10-14T03:41:35-04:00
- **Source freshness:** main `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`; authority and five relevant source blobs recorded above
- **Upstream consumed:** `30-finite-wheel.md` blob `e86a066b5fe4488972f9b49400ebb77d76cab41b`, Claims `wheel-1..4`; `40-prime-census.md` blob `fc25130ac028c2556f1754ac75ee494c440e3dbc`, Claims `census-1..5`; `00/10/20` PENDING
- **Completed evidence worth reusing:** exact residue table; complete induced fibre scan through `A<=5000`; selected aggregate reproductions; accepted paper proofs for wheel Claims 1-2; exact two-child counterexample
- **Invalidations / uncertainty:** no current-main CI/status evidence returned; Claims 1-2 are not classified `PROVED_IN_LEAN`; historical-charge conclusion remains diagnostic
- **First unresolved blocker:** `SOURCE-SPLICE-1`; secondarily formal Lean/CI for the two finite-carrier corollaries
- **Next highest-value step:** inspect any later source-tagged owner report or Lean PR; verify exact coefficient and occurrence preservation before allowing the wheel cap into a signed inequality
- **For Agent #7:** formalize only Claims 1-2 if no duplicate exists; use PR GitHub Actions and report exact head/run/axiom evidence
- **Avoid next run:** repeating unchanged scans, averaging adaptive residues, or treating an unsigned cap as signed payment


## Publication verification

- **Completed report content commit:** `d0e941b13a5ab8a60e7c5cf521848f270b07daf3`
- **Completed report blob read back:** `368b40a1a59708e4a24e97cf49d54d72ea172447`
- **Readback checks:** completed update, all nine reviewed claim IDs, final summary, and resume capsule present
- **Publication status:** COMPLETED


---

## Scheduled referee rerun — 2026-10-14T10:49:20-04:00

### Provenance refresh

- **Actual authority retrieval:** 2026-10-14T10:49:20-04:00 through 2026-10-14T10:53:59-04:00.
- **Observed main HEAD:** 18fa753f6ea12951845fec65414b47faea0172a1.
- **Authority blobs:** AGENTS.md 26715158e91d4f5f71e9e8aa15baa1a17053e456; CURRENT_PROOF_CONTRACT.md 27dceba62b4797bbb394439d13fc4a8dbe29ea0b.
- **Reporting protocol blobs:** README 81c3dea2cedcd699a5a0523a00e5cc8ec78f8913; template f1e13534f2b36a39e833493ec1739e97ab17f3d7; schedule prompts f452d69999f0180e7e576011a8ad1ad6a2eed549.
- **Earlier own checkpoint preserved:** blob 19e14164a9337af696ce0705a50e48e81248f93a; its verdicts on wheel-1..4 and census-1..5 are incorporated below and updated only where live main changed their formal status.
- **Current-day upstream actually read:** 00-coordinator-am.md = TODAY=PENDING (GitHub 404); Owner Payment blob 08b203d38e2c0d495631c1873edb903d83412ea1; Analytic Type II blob 7e6667d1e3e95861eb9c4e929b478ac910b3c2dc; Finite Wheel blob 2c2d3a0d42c3af6efb638b2cd2d8aec806aaaf74; Prime Census blob 7bd424fd86fcbb45a56f8a203f66b021779c97a6.
- **Previous-day continuity actually read:** 00/10/20/30/40/50 and Coordinator PM from 2026-10-13; the relevant stage blobs are recorded in the prior checkpoint and current specialist reports. Their status is YESTERDAY=CARRY_FORWARD, never current-day completion.
- **External inbox:** EXTERNAL_HANDOFFS.md blob 6fce4e9d024b6c4ad47798c5d7c162101a2435a0; normalized-payment paper edf96255d17f3863d20cc66d87e58e81d94ef970; direct seven-function handoff efb9015e923fd1ce7da5c5300679924163cc6737; Claude-cycle handoff 2d2a4bace0138040dcccea54bb88451534396c7f.
- **Execution evidence:** authenticated GitHub source/PR/Actions reads, exact integer calculations, deterministic trial division, and rational interval logarithm checks. No local Lean build was run or claimed.
- **Publication status for this appended section:** pending commit/readback at composition time.

### Current objective and no-narrowing baseline

The unique open public statement is VFCanonicalSquareVonKochStatement:

\[
\exists C\ge0\;\forall R\ge2,\qquad
|\pi(R^2)-\operatorname{vfMidFinishedMass}(R)-\sqrt2|
\le C R\log R.
\]

Live source supersedes the proof contract's stale “NOT YET MERGED” heading. PR #938 is merged at a360b37b04061997afa4e693ac4e77111269b216 and PR #939 at 741ce4440a82d60c8b4457de2ff200bbf1ad0917. Current main proves both directions between the named signed-late/tracking/owner-admissibility statements and the canonical target, and proves that the #915 payment is false at every actual first-bad successor and, with a good finite base, equivalent to the explicit K=2 envelope. These are PROVED_IN_LEAN logical audits, not an estimate toward RH.

The original arithmetic under review remains raw: genuine primes and least-prime owners, vfMidOddSignedSeatCharge, the single compressed historical endpoint |D_R|, the current absolute charge beta_R, both walls, masks, clipping, anchors, multiplicities, and restored quadratic cross terms. The additive public sqrt(2) phase cannot replace these coefficients.

### Authoritative Lean and CI audit

Relevant current-main blobs independently inspected:

- VF_MID_LATE_OWNER_WHEEL_THIRTY_BUDGET.lean 3701895c3e3af16b6f6b0506ed69f7b5c3d55800.
- VF_MID_DYADIC_OWNER_EXACT.lean 95e7aa05b62861a19f0179aa529f817e3a402bba.
- VF_MID_SIGNED_SEAT_CHARGE.lean 13dda0d2c6cc59580959a2d59fad60126b1c6b0b.
- VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean 190bd8024bcda99eb3b3349729466903db4e4c39.
- VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean f7d046d8d94962e18f794deee7e33ce7508a0e74.
- VF_MID_FINAL_RAW_CLIPPED_TELESCOPE.lean dc1611da7eeca2ed2f2273fa73c9a659b4ba2f42.
- VF_MID_OPEN_INLET_TARGET_EQUIVALENCE.lean 379f17c0739e8bcb4543a91bed9ced7624773ef7.
- VF_MID_LI_UNIFORM_QUADRATURE.lean 06973cdef25c3359950044bb180b9e35e312e470.
- VF_CANONICAL_SQRT_TWO_VON_KOCH.lean 43e160ac7ad51f7646771297f43a9b95395ce709.

PR #937 is merged at fcccdb32559d762dc5296dc519929f053f0fdf95 from proof head 59221ae46b2fa9b61cce2330ba965ea99bbce715. All nine reported workflows succeeded. Targeted Lean run 38548372917 compiled VF_MID_LATE_OWNER_WHEEL_THIRTY_BUDGET.lean warning-fatally with compiled=1, cached=11, then compiled=0, cached=12. The four printed theorem dependencies were exactly propext, Classical.choice, and Quot.sound. Therefore wheel-1 and wheel-2 are now PROVED_IN_LEAN, rather than merely paper proofs.

### Independent exact and numerical checks

1. The exact residue census is
   W30=0 on 1,2,23,24; W30=2 on 9,10,15,16,27,28; W30=1 on the other 20 residue classes modulo 30.
2. Deterministic trial division verified all submitted primes and products. In particular:
   - 2048^2 < 2029*2069 = 4,198,001 < 2049^2;
   - 3965^2 < 3*5,242,883 = 15,728,649 < 3966^2;
   - 5120^2 < 5*5,242,883 = 26,214,415 < 5121^2;
   - 17*29 and 17*31 are both in the strict block at R=22;
   - 7*11=77 and 11*13=143 give the sharp fixed-wheel threshold failures.
3. The ancestry-fibre samples q=2,097,169; 3,145,739; 5,242,883; 11,534,351; 30,408,713 have exact odd-owner counts 0,1,2,4,9, matching pi(floor(q/2^20))-1.
4. To remove reliance on floating-point signs, logarithms were enclosed by exact rational atanh series after binary range reduction. Forty terms with a rigorous geometric tail gave:
   - at (R,p,q,r)=(2048,2029,2069,45), the isolated slack lies in
     [0.020971437429272047366246530458058979282746,
      0.020971437429272047366246530458058979282856];
   - for q=5,242,883 with owners 3 and 5, the two isolated slacks lie respectively in
     [-0.142085615173042252998070515006888722055201,
      -0.142085615173042252998070515006888722055115]
     and
     [-0.160116575637521308334749480154297496933519,
      -0.160116575637521308334749480154297496933434].
   Thus the submitted sign counterexample and favorable collision signs are rigorous finite facts, not decimal heuristics.
5. The EXT-20261014-5 algebra was reconstructed independently. From |P_R-m_R|<=beta_R,
   |S_R|<=|D_R|+beta_R<=|S_R|+2 beta_R. Hence 0<=N_R<=1 and
   N_R >= (|S_R|/(|S_R|+2 beta_R))^2.
   Montgomery-Vaughan Brun-Titchmarsh gives beta_R=O(R/log R). For x between R^2 and (R+1)^2, split h=x-R^2 at h=R/log R: trivial counting handles the short case, and Brun-Titchmarsh handles the other, so both prime-count and logarithmic-integral changes are O(R/log R). The compiled square VF-Li_2 error is O(1). Classical Littlewood excursions therefore transfer to square endpoints and force limsup N_R=1. This is PAPER_PROOF, not Lean evidence.

### Claim-by-claim verdicts

#### Owner Payment

**20261014-owner-0 — ACCEPT / PROVED_IN_LEAN / NO_NEW_RESULT.**  
Exact claim: current main contains the #938 no-narrowing equivalences and #939 first-bad payment audit. The source confirms it. This is an authoritative logical baseline, not new owner arithmetic.

**20261014-owner-1 — ACCEPT / PAPER_PROOF.**  
For primes p,q, R>=1024p, R^2<pq<(R+1)^2, and r=floor(sqrt q), p is the genuine least owner, q is a distinct historical prime seat, and with
w(t)=(2t+1)/(t log(t^2+t+1/2)),
w(R)+w(r)-1<-451/640. The proof correctly derives R>=2048, r>=1024 and uses log 2>2/3. The map pq->q is injective only for fixed p. No mask admission or cross-owner availability follows.

**20261014-owner-2 — ACCEPT / PAPER_PROOF at isolated-pair scope only.**  
With x=w(R), y=1-w(r), the hypotheses of owner-1 give
6xy-x^2-y^2<-541/409600<0. The algebra is correct. It is not additive: adjoining the pair to residual totals (M0,S0) contributes the uncontrolled cross terms
2M0(x+y)-4S0(x-y). Any global-payment interpretation is REJECTED.

**20261014-owner-3 — ACCEPT as an exact refutation; unrestricted strengthening REJECTED / REFUTED.**  
The exact witness (2048,2029,2069,45) satisfies genuine prime and strict-block hypotheses but not R>=1024p, and its rigorously enclosed isolated slack is positive. Hence “every genuine late-owner pair has negative isolated slack” is false. The report's FINITE_COMPUTATION label was conservative; the exact primality, inequalities, and rational log enclosure establish a rigorous counterexample.

**20261014-owner-4 / EXT-20261014-5 — ACCEPT / PAPER_PROOF.**  
The exact quantifiers are: for every R>=8, 0<=N_R<=1, and limsup N_R=1, with the unchanged raw denominator T_R=(|D_R|+beta_R)^2 and source S_R=D_(R+1). All hypotheses and the square-endpoint transfer check. It rules out a hypothesis-free all-R N_R<=c<1. It does not refute the conditional first-bad formulation, imply a first-bad event, or disprove RH.

#### Analytic Type II

**20261014-analytic-0 — PENDING checkpoint, not a completed claim.**  
It was superseded in the same report by analytic-1..3 and receives no independent theorem status.

**20261014-analytic-1 — ACCEPT / PAPER_PROOF.**  
Let M=2^20. For odd prime q>=2M and R_p=floor(sqrt(pq)), the admissible odd prime owners with R_p>=1024p are exactly p<=floor(q/M), so the fibre size is pi(floor(q/M))-1. The equivalence
floor(sqrt(pq))>=1024p iff q>=Mp
is exact; pq is nonsquare; p<q is the least factor; and the historical block is strictly earlier. No signed saving follows from the cardinality formula.

**20261014-analytic-2 — ACCEPT / PAPER_PROOF.**  
For fixed R,q, at most one p can occur: two owners would give q<(2R+1), while pq>R^2 and R>=1024p force q>1024R. Global reuse is unbounded by the exact fibre formula and infinitude of primes. This is a multiplicity obstruction, not cancellation.

**20261014-analytic-3 — ACCEPT as exact diagnostic; global/dyadic-run tag injectivity REJECTED / REFUTED.**  
The prime q=5,242,883 is demanded by p=3 at R=3965 and p=5 at R=5120 in the same run [3000,6000). Both strict memberships and primalities were independently verified. The one physical historical prime cannot be cloned without separately proved source tags. This witness does not refute a ledger that genuinely contains multiple tagged copies.

#### Finite Wheel & Incidence

**20261014-wheel-1 and wheel-2 — ACCEPT / PROVED_IN_LEAN.**  
The exact W30 fibre inclusion, owner-cardinality bound, summed late-removal budget, and correctly directed prime-supply lower bound are current-main declarations with successful exact-head CI and standard axioms only. Their carrier has positive unit occurrences, not raw signed VF coefficients.

**20261014-wheel-3 — REVISE as a compound claim.**  
The universal one-child theorem is REJECTED / REFUTED by (A,R,p)=(12,22,17) and q=29,31. The zero-slot, repeated-owner, and repeated-partner examples are ACCEPTED exact diagnostics. Their conclusion about an unstated source ledger remains diagnostic until tags and coefficients are defined.

**20261014-wheel-4 — ACCEPT / FINITE_COMPUTATION.**  
The earlier residue/run scans are reproducible finite checks only. They neither prove distribution nor signed payment.

**20261014-wheel-5 — ACCEPT / PAPER_PROOF.**  
For 7<=A<=R<2A, every genuine late-owner fibre is bounded successively by the 2310-, 210-, and 30-wheel capacities and W30<=2. Since p>A>=7 implies p>=11 and q>p, q avoids 2,3,5,7,11. The A=6 witness 7*11=77 proves the integer threshold 7 is sharp.

**20261014-wheel-6 — ACCEPT / PAPER_PROOF.**  
For 11<=A<=R<2A, the same fibre is bounded by the 30030-wheel capacity, then the 2310 capacity. Here p>=13 and q>p imply q>=17, so q avoids primes through 13. The A=10 witness 11*13=143 proves sharpness. Summing over disjoint least-owner fibres gives the stated run inequalities. This is a deterministic unsigned refinement.

**20261014-wheel-7 — ACCEPT / FINITE_COMPUTATION.**  
The strict-endpoint 2310 reproductions and 30030 totals are finite evidence. No adaptive residue theorem follows. The stale first section of the wheel report, written before merges #938/#939, must not be used for current target status; its later rerun correctly repairs that narrative.

#### Prime Census Laboratory

**20261014-census-1..5 — prior verdicts retained.**  
Census-1 and -2 are ACCEPTED, now with the underlying wheel-30 claims upgraded to PROVED_IN_LEAN; their enumerations remain FINITE_COMPUTATION. Census-3 is ACCEPTED for exact witnesses while the one-child strengthening is REFUTED. Census-4 is ACCEPTED as FINITE_COMPUTATION on the physical least-factor/Mobius carrier. Census-5 is ACCEPTED as NO_NEW_RESULT.

**20261014-census-6 — ACCEPT / PAPER_PROOF plus FINITE_COMPUTATION.**  
The sharp 2310/30030 divisibility arguments are those of wheel-5/-6 and are correct. The 2,958,529-fibre coverage and run totals remain finite checks, independently implemented twice.

**20261014-census-7 — ACCEPT / PAPER_PROOF plus FINITE_COMPUTATION.**  
The ancestry-fibre theorem is analytic-1, and the exact collision is analytic-3. It correctly distinguishes same-block uniqueness from unbounded cross-block reuse.

**20261014-census-8 — ACCEPT at stated scopes.**  
Owner-1/-2 are PAPER_PROOF. The unrestricted negativity strengthening is REFUTED by the exact positive-slack witness. The report correctly refuses to add isolated quadratic slacks.

**20261014-census-9 — ACCEPT / FINITE_COMPUTATION.**  
The physical integer/SPF enumeration, strict endpoints, semiprime factorization, and mu(pq)=+1 conservation are correctly scoped. Equality of finite count and Mobius sum here is an exact property of the enumerated squarefree-semiprime carrier, not a signed VF theorem.

### Counterexamples and diagnostics

**Confirmed counterexamples satisfying all hypotheses of the defeated statements:**

- One-child late-owner cap: (A,R,p)=(12,22,17), children 29 and 31.
- Unrestricted isolated pair negativity: (R,p,q,r)=(2048,2029,2069,45), exact slack >0.
- Global or one-run historical-tag injectivity: q=5,242,883 demanded at (p,R)=(3,3965) and (5,5120).
- 2310 theorem lowered to A>=6: 7*11=77.
- 30030 theorem lowered to A>=10: 11*13=143.

**Diagnostics, not counterexamples to a fully tagged source theorem:** repeated p=7, repeated q=13, the narrow-wall K=0.019 event near R=1031, and the favorable negative slacks for the two q=5,242,883 pairs. None has all premises of a correctly specified global source-payment theorem.

### Circularity, carrier, and novelty findings

1. The fixed-owner inequalities are genuine local original-weight information. They do not supply historical admission, cross-owner disjointness, or a global quadratic estimate.
2. The exact ancestry-fibre formula proves why fixed-owner injection is insufficient: one historical q may have arbitrarily many current demands across blocks.
3. Wheel-30 is formalized and the deeper fixed wheels are valid paper corollaries, but every one counts unsigned unit occurrences. Increasing a fixed primorial approaches the already-known exact prime quotient interval; it does not manufacture signed cancellation.
4. SOURCE-SPLICE-1 may denote a useful unconditional equality if fully specified. It is not proved necessary, not known to be the unique first lemma, and does not close the target. Any quantitative “payment” strong enough to imply the named inlets must pass the no-narrowing audit.
5. The original #915 norm compresses all history into |D_R| and uses one current beta_R. Re-expanding local pairs without all restoration cross terms changes the theorem.
6. The canonical sqrt(2) phase is additive and public; all historical coefficients in these claims are raw. No energy substitution was made.
7. None of today's finite checks, paper lemmas, or formal unsigned theorems proves the canonical endpoint bound, finite A/C, CORR-4, or RH.

### Outstanding proof obligations

- State any proposed source-to-ledger equality on literal tagged occurrences and prove preservation of weights, signs, masks, clips, walls, anchor, chronology, multiplicity, complete lower-child runs, and every decompression cross term.
- For a fixed historical tag q, prove actual available multiplicity a(q) and compare it with demanded multiplicity d(q); q=5,242,883 forces at least two demands in one dyadic run.
- Bound the residual and all cross terms jointly. Pairwise negative slack and unsigned wheel capacities are insufficient.
- If wheel-2310/30030 or ancestry-fibre lemmas are formalized, keep their conclusions finite-carrier only and obtain exact-head warning-fatal CI plus axiom evidence.
- Treat the canonical target itself as the first known completion theorem. Do not advertise a target-equivalent statement or the #915 payment as a smaller open gate.

### Lean Verification handoff

Accepted for possible scoped formalization:

- owner-1/-2, as scalar native-weight inequalities with fixed-owner injection only;
- analytic-1/-2, as exact integer-square-root/fibre and fixed-block uniqueness lemmas;
- wheel-5/-6, as nested fixed-wheel carrier corollaries.

Already formalized; do not duplicate: wheel-1/-2 through PR #937, no-narrowing through #938, and #915 content audit through #939.

No source-payment, signed-late, owner-admissibility, canonical endpoint, or RH closure PR is justified by today's results.

### Recommendation to the Coordinator

Carry owner-1/-2, analytic-1/-2, and wheel-5/-6 as accepted supporting PAPER_PROOF lemmas. Carry wheel-1/-2 as PROVED_IN_LEAN. Record the five exact counterexamples above and the normalized-payment limsup-one obstruction. Keep Coordinator AM as TODAY=PENDING. Direct the next weighted experiment to demanded-versus-available historical tags and full cross terms; do not repeat unchanged unsigned scans or present SOURCE-SPLICE as an already narrowed completion gate.

### Updated final status

- **Accepted net-new formal result:** exact wheel-30 fibre/run budget, PROVED_IN_LEAN.
- **Accepted net-new paper results:** fixed-owner negative-weight inequality and isolated slack; exact ancestry-fibre multiplicity; fixed-block uniqueness/global reuse dichotomy; sharp 2310/30030 wheel refinements; normalized original-payment limsup one.
- **Refuted strengthenings:** universal one-child fibre, unrestricted isolated negativity, global/dyadic historical-tag injectivity, and the lowered fixed-wheel thresholds.
- **Production target:** NO_NEW_RESULT. The canonical endpoint theorem and RH remain open.
- **Completeness:** DONE for every substantive claim in today's available 10/20/30/40 reports; 00 remains PENDING.
- **No RH-proof claim:** yes.

## Updated next-run resume capsule (non-authoritative)

- **Checkpoint:** 2026-10-14 scheduled rerun at main 18fa753f6ea12951845fec65414b47faea0172a1.
- **Reusable formal evidence:** PR #937 head 59221ae46b2fa9b61cce2330ba965ea99bbce715; targeted run 38548372917; wheel module blob 3701895c3e3af16b6f6b0506ed69f7b5c3d55800.
- **Reusable paper claims:** owner-1/-2/-4, analytic-1/-2, wheel-5/-6.
- **Mandatory counterexamples:** two-child (12,22,17); positive slack (2048,2029,2069,45); repeated q=5,242,883; 77 for 2310 threshold; 143 for 30030 threshold.
- **First blocker:** no exact admitted historical-tag multiplicity or joint residual/cross-term estimate on the literal source carrier.
- **Highest-value continuation:** specify and falsify d(q)<=a(q) on the real masked/anchored ledger before attempting any aggregate inequality.
- **For Lean Verification:** only the scoped scalar/cardinality candidates above; no closure consumer.
- **Avoid:** cloned historical charges, summed isolated slacks, altered denominator, target-equivalent inlets, or another unchanged census.
