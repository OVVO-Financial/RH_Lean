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
