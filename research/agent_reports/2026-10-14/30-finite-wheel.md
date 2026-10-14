# Finite Wheel & Incidence — 2026-10-14

## Run metadata

- **Agent:** RH | Finite Wheel & Incidence
- **Run timestamp:** 2026-10-14T00:12:56-04:00 (America/New_York)
- **Repository / branch read:** `OVVO-Financial/RH_Lean`; authoritative mathematics from `main`
- **Actual main HEAD:** `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`
- **Authority blobs:** `AGENTS.md` `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; `CURRENT_PROOF_CONTRACT.md` `f6e8dc6813ec63974489c26b0c383e34203f0aa9`
- **Reporting protocol blobs:** README `6352109e25bff6dad702d1b9a4bb687bb5de3944`; template `71eb758b6dcd0945d5eda219422219d07721f37e`; prompts `ec91852f81ababe42dd17795809fb60c271919eb`
- **Relevant open/draft PRs:** none returned by live GitHub search
- **Overall status:** `PAPER_PROOF` for Claims `20261014-wheel-1` and `-2`; `REFUTED` for a universal one-slot strengthening; `FINITE_COMPUTATION` for Claim `-4`; `NO_NEW_RESULT` on the canonical endpoint bound and original source payment
- **Lean status:** no local Lean compilation and no new Lean theorem claimed

## Upstream reports actually retrieved

The three required current-day files were queried explicitly at `ref=agent-reports` and each returned GitHub 404, so they are:

- `2026-10-14/00-coordinator-am.md`: **PENDING**
- `2026-10-14/10-owner-payment.md`: **PENDING**
- `2026-10-14/20-analytic-type-ii.md`: **PENDING**

Fallback continuity was taken from the latest published prior-stage report
`2026-10-13/30-finite-wheel.md`, blob
`1c96431194038b2691f628bfce5736f7f0dcacd5`, especially Claims
`20261013-wheel-5` and `-6`. The latest prior analytic report was also
read, including the warning that local (3q) pair slack becomes negative and
that global cross terms and historical decompression cannot be discarded.
These reports are navigation only; current `main` source and the proof
contract remain authoritative.

## Current central mathematical objective

The public target is still
[
exists Cge0 orall Rge2,qquad
left|pi(R^2)-operatorname{vfMidFinishedMass}(R)-sqrt2ight|
 le C Rlog R,
]
formalized as `VFCanonicalSquareVonKochStatement`.

For the direct VF route, the current arithmetic inlet remains the exact
occurrence-, sign-, coefficient-, mask-, clipping-, owner-, and
ancestry-preserving reassembly of the actual first-bad historical/current
source onto the already-cancelled safe/sector-six ledger. The named scalar
interface `VFMidDyadicSignedLateCorrectionStatement` and the original
`VFMid915FirstBadSourcePaymentStatement` remain open. The present
investigation addresses only the genuine late least-prime-owner population
inside a strict subdoubling square run.

## Original arithmetic carrier inspected

Current-main source blobs inspected:

- `VF_MID_DIRECT_ROUGH_CHILD.lean` `3da99cd7208ab97abb55d900c3703c65056bdea5`
- `VF_MID_DIRECT_COMPOSITE_DESCENT.lean` `c91b98ece19a22b7e6dacc7f000b86473e6d7d28`
- `VF_MID_DYADIC_OWNER_EXACT.lean` `95e7aa05b62861a19f0179aa529f817e3a402bba`
- `VF_MID_DYADIC_OWNER_PARITY_TWO.lean` `fb025b16bbbd6ca4bcf6288745c283aefa913218`
- `VF_MID_DYADIC_PREFIX_OWNER.lean` `6757501bfc343d51ddb34483f8195da4a2c84047`
- `VF_MID_FIRST_BAD_SOURCE_TO_SECTOR_SIX_INLET.lean` `5d03f3080d014aba1e02485ae9c0b08988478c3c`
- `VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean` `160194aa0bfccc8211264012fcc2ba018e936ab2`

For (3le Ale R<2A) and a late owner
(pin	exttt{vfMidSquareBandLateOwnerPrimes} A R), the compiled source
identifies each physical owner occurrence (n) with a stripped rough child
(q=n/p). The child is prime, (ple q), and lies in the strict open square
band
[
R^2<pq<(R+1)^2.
]
The merged parity theorem places every such (q) in
[
left(leftlfloor R^2/pightfloor,,
       leftlfloor R^2/pightfloor+4ight]
]
and proves at most two children. Least-prime owner fibres are disjoint; every
physical occurrence has unit multiplicity in the late-removal census.

The original source-payment carrier is much richer: raw VF weights, both
walls, anchor, survivor/admission masks, clipped exits, returned-pair
multiplicities, historical ancestry, cross-owner interactions and complete
lower-child runs. None of those data is replaced by the population theorem
below.

## Exact research question

Can the newly compiled two-slot parity fibre cap be sharpened by an exact
finite wheel on the same genuine prime children, without assuming
equidistribution or spending any historical prime occurrence more than once?

## Claim 20261014-wheel-1 — exact wheel-30 late-owner fibre cap

**Status: `PAPER_PROOF`.**

Define the four-slot wheel census
[
W_{30}(t):=#{jin{1,2,3,4}:gcd(t+j,30)=1}.
]
For all natural (A,R,p), if
[
5le A,qquad Ale R<2A,qquad
pin	exttt{vfMidSquareBandLateOwnerPrimes} A R,
]
then, with (t=lfloor R^2/pfloor),
[
oxed{#
 	exttt{vfMidSquareBandCompositeOwner}(R,p)le W_{30}(t).}
]

**Derivation.** Stripping (p) is injective and the compiled rough-child
identity preserves cardinality. Every stripped child (q) is prime and lies
in ({t+1,t+2,t+3,t+4}). Also (qge p>Age5), so (q) is divisible by
none of (2,3,5); hence (gcd(q,30)=1). Inclusion in the displayed wheel
survivor set gives the cardinality bound. Strict square endpoints are
preserved through the use of (lfloor((R+1)^2-1)/pfloor).

The complete residue table for (tmod30) is:
[
egin{array}{c|l}
W_{30}(t)&tmod30\ hline
0&1,2,23,24\
1&0,3,4,5,6,7,8,11,12,13,14,17,18,19,20,21,22,25,26,29\
2&9,10,15,16,27,28.
end{array}
]

This is a deterministic inclusion-exclusion restriction on actual prime
children. It makes no independence or average-residue assumption.

## Claim 20261014-wheel-2 — exact wheel-30 run budget

**Status: `PAPER_PROOF`.**

For (5le Ale Ble2A), put
[
mathcal W_{30}(A,B)=
 sum_{R=A}^{B-1}
 sum_{substack{pin	exttt{vfMidSquareBandLateOwnerPrimes} A R}}
 W_{30}!left(leftlfloor R^2/pightflooright).
]
Then exact least-prime-owner partitioning and Claim 1 give
[
oxed{	exttt{vfMidDyadicLateRemoval}(A,A,B)
       le mathcal W_{30}(A,B),}
]
and the compiled identity
(	exttt{PrimeSupply}=	exttt{PrefixSupply}-	exttt{LateRemoval})
gives
[
oxed{	exttt{vfMidDyadicPrefixSupply}(A,A,B)
       -mathcal W_{30}(A,B)
       le	exttt{vfMidDyadicPrimeSupply}(A,B).}
]

Compared with the already compiled parity-owner cap
(2sum_R #{	ext{late owners at }R}), this replaces the constant two
for every owner occurrence by its exact (0/1/2) wheel capacity. It is
uniform and never weaker. No nontrivial uniform factor below two follows
without controlling the adaptive residues (lfloor R^2/pfloormod30);
that is the first unresolved arithmetic lemma on this branch.

## Claim 20261014-wheel-3 — sharpness and ancestry counterexamples

**Status: `REFUTED` for “every late fibre has at most one child”; exact
counterexamples retained.**

- Smallest saturation found in lexicographic scan order (A,R,p):
  (A=12,R=22,p=17), (t=28), with children (q=29,31). The physical
  composites are (493) and (527), both strictly between (22^2) and
  (23^2). Thus (W_{30}(28)=2) is attained.
- A genuine zero-capacity owner slot occurs at (A=9,R=16,p=11,t=23);
  its four positions contain no wheel-30 survivor and the fibre is empty.
- Repeated owner across blocks persists: for (A=5,p=7), the physical
  descendants (77=7cdot11) at (R=8) and (91=7cdot13) at (R=9)
  are distinct available occurrences. A per-block cap cannot be spent only
  once across a run.
- Repeated historical partner across owners persists: for (A=6,q=13),
  (91=7cdot13) at (R=9) and (143=11cdot13) at (R=11). A single
  historical (q)-charge cannot be assigned independently to both edges
  unless the original source supplies separately tagged occurrences.

The wheel theorem records every descendant and does not collapse either kind
of repetition.

## Claim 20261014-wheel-4 — exact computations

**Status: `FINITE_COMPUTATION`.**

Two independent CPython 3.12 methods were executed.

1. A prime-table/hyperbola scan checked every (5le Ale500),
   (Ale R<2A), and every prime late owner (A<ple R). It found no
   violation of Claim 1 and located the sharp and repeated-ancestry examples
   above.
2. An independent smallest-prime-factor enumeration visited every physical
   integer in all (45{,}140) blocks with (5le Ale300),
   (Ale R<2A). It checked (760{,}399) owner fibres and retained
   (304{,}673) physical late semiprime occurrences. No violation occurred.

Selected full-run ([A,2A)) censuses are:

| (A) | actual late occurrences | owner slots | parity cap | wheel-30 cap | saving |
|---:|---:|---:|---:|---:|---:|
| 50 | 131 | 268 | 536 | 282 | 254 |
| 100 | 463 | 1,033 | 2,066 | 1,091 | 975 |
| 500 | 6,587 | 18,409 | 36,818 | 19,573 | 17,245 |
| 1,000 | 22,627 | 69,077 | 138,154 | 73,432 | 64,722 |
| 5,000 | 385,553 | 1,411,740 | 2,823,480 | 1,504,048 | 1,319,432 |

For the previously documented run (A=2634,B=5267), the computation
reproduced (125{,}272) physical late occurrences. There were (426{,}984)
owner slots; the parity cap was (853{,}968), while the wheel-30 cap was
(454{,}679), a deterministic saving of (399{,}289). The wheel capacities
split into (56{,}989) zero, (285{,}311) one, and (84{,}684) two slots.

These finite scans support endpoint and implementation checks only; they do
not prove an all-scale residue distribution or signed inequality.

## Novelty and circularity audit

**Already known:** generic finite-wheel survivor counting, inclusion-exclusion,
the four-slot rough-child inclusion, prime-child theorem, owner partition,
parity-two fibre cap, semiprime hyperbola census, and repeated owner/partner
congestion.

**New here:** the exact carrier-specific wheel-30 fibre theorem and its
adaptive run budget on the newly compiled parity-two carrier, including the
zero-capacity residue classes and exact quantitative comparison with the
parity budget. Repository searches found no existing declaration applying
moduli (3) and (5) to this four-slot late-owner fibre.

**Independence:** the proof uses only primality, (q>Age5), exact four-slot
geometry, divisibility by (2,3,5), and injective least-prime ownership. It
does not assume RH, finite A/C, CORR-4, actual-prime admissibility, the signed
late-correction estimate, or source payment.

**Limit:** this remains an unsigned population restriction. It neither
produces nor consumes the raw VF coefficients, historical anchor, boundary
masks, clipping weights, pair Gram cross terms, or compression restoration.
Therefore it is not a restatement of the missing inequality, but it also does
not close it.

## Quantitative contribution to the current obligation

The trivial local cap from four sites is four; the compiled parity theorem
improves it to two. Claim 1 improves it exactly to (W_{30}(t)in{0,1,2}).
On (A=2634,B=5267), this cuts the proven aggregate cap from (853{,}968)
to (454{,}679), while the actual population is (125{,}272).

This may sharpen a lower/composite run-capacity certificate after an exact
source/reassembly splice. It does not control
`VFMidDyadicSignedLateCorrectionStatement` or
`VFMid915FirstBadSourcePaymentStatement`: taking absolute values before
signed reassembly would still destroy the interactions needed by the proof.

## First unresolved lemmas

1. **W30-RESIDUE-DISPERSION:** prove a deterministic all-scale upper bound
   strictly better than (2#	ext{owners}) for
   (sum W_{30}(lfloor R^2/pfloor)) on the actual threatening runs, or
   exhibit an admissible concentration obstruction. Complete-period wheel
   averages alone do not apply to this adaptive prime-owner sequence.
2. **SOURCE-SPLICE-1:** construct the exact original-weight source-to-safe/
   sector-six reassembly, preserving every occurrence, sign, coefficient,
   owner, mask, clipped exit, anchor, cross term, historical prime
   multiplicity and complete lower-child run. Only after this equality may
   the wheel capacity be tested as useful signed budget.
3. **HISTORY-AVAILABILITY:** prove any proposed historical charge is used at
   most as many times as separately tagged source occurrences; the repeated
   (q=13) witness forbids naive edgewise reuse.

## Explicit testable claims for the 1 AM Prime Census Laboratory

1. Independently reproduce `20261014-wheel-1` by physical-integer
   enumeration through at least (A=5000), retaining
   ((A,R,p,q,n,t,tmod30,W_{30}(t))).
2. Verify the full residue table and all strict endpoint conventions using
   (R^2<n<(R+1)^2) and ((R+1)^2-1) in integer division.
3. Confirm the saturation witness
   ((A,R,p,t;q_1,q_2)=(12,22,17,28;29,31)), the zero-capacity witness
   ((9,16,11,23)), repeated owner (p=7), and repeated partner (q=13).
4. Reproduce the (A=2634,B=5267) totals:
   actual (125272), owners (426984), parity cap (853968),
   wheel-30 cap (454679), capacity histogram
   ((56989,285311,84684)) for capacities (0,1,2).
5. Search actual threatening/first-bad runs for concentration of the
   exceptional two-slot residue classes (9,10,15,16,27,28mod30).
   Report maxima and counterexamples; do not infer uniformity from averages.
6. For any weighted experiment retain
   ((R,p,q,n,w_R,	ext{sourceTag},	ext{mask},	ext{historicalTag})) and
   verify edge-grouped and owner-grouped sums exactly before inequalities.
   Count a historical prime occurrence once unless distinct tags prove more
   availability.

## Claims requiring Adversarial Referee review

- `20261014-wheel-1`: the (Age5) threshold, child-prime import,
  four-slot inclusivity, and the wheel-30 table.
- `20261014-wheel-2`: exact direction of the prime-supply inequality and
  the distinction between an adaptive sum and a complete wheel period.
- `20261014-wheel-3`: minimality of the saturation example and the scope of
  repeated owner/partner obstructions.
- Reject any transfer from this unsigned late tail to the full historical
  source without `SOURCE-SPLICE-1`.

## Candidates potentially suitable for Lean Verification

After independent referee acceptance, Claims 1 and 2 are small corollaries of
the compiled four-slot and prime-child declarations. A focused formalization
could define (W_{30}), prove the fibre inclusion/cardinality theorem, and
sum it over the existing exact owner partition. No source-payment or RH
closure PR is warranted from this report.

## Final status

**Net-new progress:** exact wheel-30 restriction and adaptive run capacity on
the genuine late-owner carrier, with sharp counterexamples and finite
quantification.

**Production target:** `NO_NEW_RESULT`; the canonical bound, signed
late-correction statement, original source payment, finite A/C, CORR-4,
actual-prime admissibility and RH remain open.

**No completed-proof claim:** yes.

## Next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** 2026-10-14T00:12:56-04:00
- **Source freshness:** main `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`; central and relevant source blobs listed above
- **Upstream consumed:** today's 00/10/20 reports all `PENDING`; prior own report blob `1c96431194038b2691f628bfce5736f7f0dcacd5`
- **Completed evidence worth reusing:** Claims `20261014-wheel-1..4`; SPF scan through (A=300); prime-table scan through (A=500); exact production-run census
- **Invalidations / uncertain results:** no source change observed; no Lean compile; no all-scale adaptive residue bound
- **First unresolved mathematical blocker:** `W30-RESIDUE-DISPERSION` for the population branch and `SOURCE-SPLICE-1` for the production signed branch
- **Next highest-value step:** consume the 1 AM census and referee audit; test wheel-30 only on actual threatening runs while preserving full source tags
- **For Agent #7:** no open PR; Claims 1–2 are potential supporting lemmas only after independent review
- **Avoid next run:** wheel-average heuristics on adaptive floors, cross-block reuse of an owner cap, edgewise reuse of one historical prime charge, or substituting unsigned capacity for signed source payment
