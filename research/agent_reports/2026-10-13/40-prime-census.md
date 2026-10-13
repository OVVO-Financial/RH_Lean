# RH_Lean agent daily report — 2026-10-13 / Prime Census Laboratory

## Provenance

- **Report date (America/New_York):** 2026-10-13
- **Agent / stage:** RH | Prime Census Laboratory / `40-prime-census.md`
- **Scheduled start:** 01:00 ET (second daily run / 03:00 AM referee preparation)
- **Run ID / sequence:** 2026-10-13T01:06:00-04:00 / first invocation observed for this date
- **Actual execution / checkpoint time:** 2026-10-13T01:07:31-04:00
- **Previous own checkpoint:** 2026-10-12 report PENDING (404)
- **Warm-start cache status:** Current authority refreshed. No same-day upstream claims exist yet. The 2026-10-12 finite-wheel claim set is historical carry-forward and is being independently tested against unchanged relevant source blob `95e7aa05b62861a19f0179aa529f817e3a402bba`.
- **Observed `main` HEAD SHA:** `7ff5ff9e5ef47fe7ece491af062578f9a9c48ef7`
- **Central contract fetched:** SUCCESS: `main:AGENTS.md` blob `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; `main:CURRENT_PROOF_CONTRACT.md` blob `f6e8dc6813ec63974489c26b0c383e34203f0aa9`
- **Report target:** `agent-reports:research/agent_reports/2026-10-13/40-prime-census.md`
- **Previous upstream reports actually read:** Today's `00-coordinator-am.md`, `10-owner-payment.md`, `20-analytic-type-ii.md`, and `30-finite-wheel.md`: all PENDING (404 at 2026-10-13T01:06 ET). Historical carry-forward: 2026-10-12 `30-finite-wheel.md`, blob `ffeff1fb8822c1b3b28fc079e8bf34958ed4aaa5`.
- **Execution environment/tools used:** GitHub connected reads/search; authorized GitHub write to this report only; local exact computation pending. No Lean build or CI.
- **Publication status:** INITIAL_CHECKPOINT / PARTIAL
- **Early durable checkpoint:** This section is the early checkpoint; commit and readback recorded in the next update.

## Current central research objective

Prove the canonical public square-endpoint bound
[
  |pi(R^2)-operatorname{vfMidFinishedMass}(R)-sqrt2| le C Rlog R
]
uniformly for (Rge2). The direct arithmetic seam remains the occurrence- and weight-preserving first-bad historical/current source payment, formalized as the still-open `VFMid915FirstBadSourcePaymentStatement`. The additive (sqrt2) phase does not alter the frozen raw owner coefficients. Exact finite-wheel restrictions may tighten the lower/composite safe capacity but cannot replace the original signed weighted splice.

## Work performed today

Authority, reporting protocol, current Lean declarations, report availability, and open PR state were refreshed. GitHub currently lists no open PRs. The exact source still proves the four-slot late-owner bound and prime-child theorem but contains no two-slot theorem. Independent Python and C++ tests of historical claims `20261012-wheel-1` through `-3` are in progress.

## Claims and evidence

### Claim 20261013-census-0

- **Exact quantified statement and original carrier:** The four requested same-day upstream reports do not exist on `agent-reports` as of 2026-10-13T01:06 ET.
- **Status:** PENDING
- **Evidence:** Four explicit GitHub content fetches returned 404.
- **Limit:** This is an operational status, not mathematics.

## Downstream handoff

- **Claims ready for independent referee:** PENDING computation.
- **Missing inputs or upstream stages:** All four requested same-day predecessors PENDING.
- **Next action / priority:** Independently reproduce the two-slot late-owner restriction, falsify weakened hypotheses, audit repeated-owner occurrences, and quantify run-envelope sharpness without identifying the unit census with the weighted first-bad source.

## Final report summary

**Net-new mathematical progress:** Pending.
**Completeness:** PARTIAL.
**No RH-proof claim:** yes.

## Meaningful-results update - 2026-10-13T01:11:34-04:00

- **Early checkpoint publication:** commit `b4801e85818b4894bf55d4f3dedec2ee76618fb9`, successfully read back.
- **Substantive-results publication:** commit `9b106031ddff1e3e6d5476b2638373fcdf779680`, successfully read back.
- **Relevant Lean source:** `research/VF_MID_DYADIC_OWNER_EXACT.lean`, blob `95e7aa05b62861a19f0179aa529f817e3a402bba`.
- **Open payment source:** `research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean`, blob `160194aa0bfccc8211264012fcc2ba018e936ab2`.
- **Actual weighted carrier:** `research/VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean`, blob `58b78186e4fd5b68179afe4be0b7b6e4761442d6`.
- **Open PR discovery:** no open PRs returned by GitHub during this run.

The current source proves an occurrence-preserving cardinality equality from each physical owner fibre to its child fibre, includes that child fibre in the four integers `t+1,...,t+4` for `t=floor(R^2/p)`, and separately proves every admitted subdoubling child prime.

### Claim 20261013-census-1

- **Statement:** For every natural `A,R,p`, if `3 <= A <= R < 2*A` and `p` belongs to `vfMidSquareBandLateOwnerPrimes A R`, then
  `card(vfMidSquareBandCompositeOwner R p) <= 2`.
- **Status:** PAPER_PROOF, supported independently by FINITE_COMPUTATION.
- **Proof:** Every child is one of four consecutive integers. The current prime-child theorem applies to every member. Because `p > A >= 3` and each child is at least `p`, every child is an odd prime at least 5. Four consecutive integers contain exactly two odd integers. The exact existing owner/child cardinality transport then gives the result.
- **Python reference run:** CPython 3.12.14 directly enumerated every integer in every open band `R^2 < n < (R+1)^2`, found its least prime factor by trial division, reconstructed `n=p*q`, and grouped by `(A,R,p)` for every `3 <= A <= 250`, `A <= R < 2*A`. It checked child primality, `p <= q`, exact reconstruction, and endpoints. Result: 187,853 descendant occurrences, maximum fibre 2, zero violations.
- **Independent C++ run:** g++ 13.3.0 with `-O3 -std=c++17 -Wall -Wextra -pedantic`. This implementation used a prime sieve and exact cofactor-slot intervals rather than the Python factorization loop. For every `3 <= A <= 100000`, `A <= R < 2*A`: 877,573,076 admissible owner checks, maximum fibre 2, zero violations, elapsed 16.0756 seconds.
- **Sharp example:** `A=12, R=22, p=17`, with `493=17*29` and `527=17*31`.
- **Source hashes:** Python `59815843bb68d062916cb4235b9be8c77f3caac101e327315d446121a99cea07`; C++ `cbe12c6e393d11908a41bbff46cde40036400ea502d47bfc2333305ff6a6b2a5`.
- **Limit:** No Lean proof was compiled. The first formal obligation is an odd-cardinality lemma for `Finset.Ioc t (t+4)` and its transport through the existing exact cardinality equality.

### Claim 20261013-census-2

- **Statement:** Under `3 <= A <= R < 2*A`,
  `card(vfMidSquareBandPrefixCompositeSurvivors A R) <= 2*(R-A)`.
  For `3 <= A <= B <= 2*A`, with `d=B-A`,
  `vfMidDyadicLateRemoval A A B <= d*(d-1)`.
  Consequently,
  `vfMidDyadicPrefixSupply A A B - d*(d-1) <= vfMidDyadicPrimeSupply A B`.
- **Status:** PAPER_PROOF with FINITE_COMPUTATION checks.
- **Proof:** Exact least-prime-owner Fubini partitions the late composites. At most `R-A` integers can own them, and Claim 1 permits at most two physical occurrences per owner. Summing over `R=A,...,B-1` gives `2*sum(k, k=0..d-1)=d*(d-1)`, including `d=0,1`.
- **Finite checks:** No block or run violation through `A=250` in the direct implementation. Among all partial runs, the largest observed ratio was `1/2` at `(A,B,T)=(4,6,1)`. For full runs `B=2*A`, both implementations independently found maximum ratio `1/6`, first at `A=3`; the C++ coverage was through `A=100000`.
- **Multiplicity audit:** The direct run retained occurrence tags. Historical owner `p=5` occurs at distinct descendants `35=5*7` in block `R=5` and `55=5*11` in block `R=7`. Both are separate physical occurrences; no negative contribution may be reused across them.
- **Limit:** This is an unsigned unit census of positive-Mobius late composites. It remains quadratic and does not control `vfMidOddSignedSeatCharge`, historical anchor, squareful restoring mass, survivor clipping, earlier-owner transport, or the squared absolute NNS denominator.

### Claim 20261013-census-3

- **Statement tested:** Delete `R < 2*A` from Claim 1.
- **Status:** REFUTED.
- **Smallest counterexample found in lexicographic `(A,R)` order over `3 <= A <= 250`, `A <= R <= 8*A`:** `A=3, R=18, p=5`, with sites `325=5*65`, `335=5*67`, and `355=5*71`.
- All three sites lie strictly in `(18^2,19^2)=(324,361)` and have least prime factor `5>A`, so the owner fibre has size 3. The composite child 65 identifies exactly where the prime-child mechanism fails.
- **Scope:** Minimality is only for the stated search order and range.

### Claim 20261013-census-4

- **Question:** Reproduce endpoint prime counts and verify the canonical coordinate map `D_can(R)=D_raw(R)-sqrt(2)`, with
  `F_R=sum((2*r+1)/log(r^2+r+1/2), r=2..R-1)`.
- **Status:** FINITE_COMPUTATION.

| R | pi(R^2) | P_R | D_raw | D_can |
| ---: | ---: | ---: | ---: | ---: |
| 1029 | 82755 | 141 | -119.5852052778932356360117966952305378601 | -120.9994188402663306848134854194402359387 |
| 1030 | 82896 | 134 | -126.9959636768471735540681370974296378349 | -128.4101772392202686028698258216393359135 |
| 1031 | 83030 | 160 | -141.5300914388765424094922264744874677054 | -142.9443050012496374582939151986971657839 |
| 1032 | 83190 | 144 | -130.1875742150175422145042362091043534131 | -131.6017877773906372633059249333140514917 |

Python `decimal` logarithm and square root were evaluated at 80 and 120 decimal digits; every displayed digit agreed. The 80-digit coordinate residual had magnitude `3e-78`. This is a precision-stability check, not a directed-rounding interval certificate. No claimed sign or inequality is close to numerical ambiguity.

Regression source hash: `42dd9c486df2e91611f52681a3897174000a4f70ddaa7848b198fe218f29e255`. The 120-digit result JSON hash is `e527b57b17b45d35afbaa0208e80b906eef1e1d720af741250b94be3d08b86ae`.

These four values prove no uniform bound. They confirm that the fixed additive phase changes endpoint defects while leaving prime events and owner occurrences unchanged. They do not promote the historical local `K=0.019` event to a global `K=2` first-bad configuration.

## Reproduction

Commands actually executed:

```text
python scratch/prime_census_20261013.py 250
g++ -O3 -std=c++17 -Wall -Wextra -pedantic \
  scratch/prime_census_20261013.cpp -o /tmp/prime_census_20261013
/tmp/prime_census_20261013 100000
python scratch/vf_regression_20261013.py 80
python scratch/vf_regression_20261013.py 120
```

The Python reference took 15.55 seconds; the C++ large scan took 16.08 seconds. Algorithms were deterministic, with no random seeds. The C++ memory requirement was linear in `A_max`; the Python reference used transient per-run dictionaries. These scratch programs were executed but not added to repository source.

## Invariants and falsification audit

- Open endpoints `R^2 < n < (R+1)^2` were enforced.
- Prime identity and descendant occurrence were stored separately.
- Least-prime-factor ownership reconstructed every physical site.
- Repeated owners across blocks were counted per occurrence.
- Every subdoubling Python child was checked prime and at least its owner.
- Removing subdoubling was actively falsified.
- Taking `R<A` cannot falsify the cardinality conclusion: a physical least owner satisfies `p<=R`, so no late owner can also satisfy `p>A`. No necessity claim is made for `A<=R`.
- No weighted-source, covariance, cancellation, first-bad, or owner-admissibility conclusion was inferred from the positive census.

## Remaining obligations

1. Formalize Claims 1 and 2 in Lean and obtain warning-fatal and axiom checks.
2. Prove the occurrence- and weight-preserving splice from the literal historical/current source `D_A - runPhysicalCharge - blockPhysicalCharge` to the compensated owner-cell ledger.
3. Retain the survivor mask, original seat weights, clipping, both walls, historical anchor, squareful restoring term, and repeated-owner multiplicity in that splice.
4. Only then test whether the improved `d*(d-1)` safe capacity can force a signed sector-six child run.
5. The canonical all-scale bound, actual-prime owner escape admissibility, `VFMid915FirstBadSourcePaymentStatement`, finite A/C, and RH remain open.

## Downstream handoff

- **Adversarial Referee:** review `20261013-census-1` and `-2`, especially exact cardinality transport, the odd-prime step, open endpoints, and occurrence versus owner identity.
- **Confirmed falsification:** `20261013-census-3`; subdoubling cannot be removed.
- **Lean-ready only after review:** the two-slot theorem and its block/run corollaries. No source change or Lean compilation occurred here.
- **Missing stages:** all four requested same-day upstream reports remained PENDING.
- **Next priority:** test any proposed weighted splice site by site on `vfMidOneBlockActivePhysicalCarrier`, including restoring and clipped/admitted terms.

## Final report summary

**Net-new mathematical progress:** PAPER_PROOF and independent finite validation of the factor-two physical owner-fibre restriction through `A=100000`; exact falsification without subdoubling; canonical endpoint regression.

**Completeness:** DONE for available claims; same-day predecessor stages PENDING.

**No RH-proof claim:** yes. The weighted source payment and all-scale closure remain open.

## Next-run resume capsule (non-authoritative)

- **Timestamp:** 2026-10-13T01:11:34-04:00.
- **Fresh sources:** main `7ff5ff9e5ef47fe7ece491af062578f9a9c48ef7`; AGENTS blob `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; contract blob `f6e8dc6813ec63974489c26b0c383e34203f0aa9`; dyadic-owner blob `95e7aa05b62861a19f0179aa529f817e3a402bba`.
- **Upstream:** 2026-10-13 predecessors PENDING; historical 2026-10-12 finite-wheel blob `ffeff1fb8822c1b3b28fc079e8bf34958ed4aaa5`, claims `20261012-wheel-1..3`.
- **Reusable evidence:** `20261013-census-1..4`, with commands, hashes, ranges, timings, counterexample, and numerical precision above.
- **Uncertainty:** no Lean compilation; paper-proof status only. Finite results stop at their stated ranges. High-precision values are stability-checked but lack directed interval certificates.
- **First blocker:** occurrence- and weight-preserving historical/current source splice into the compensated owner-cell ledger.
- **Next step:** test a genuine weighted splice when one is proposed; otherwise referee and formalize the two-slot lemma.
- **Avoid:** repeating the same unit census or treating `d*(d-1)` as a signed source payment.
