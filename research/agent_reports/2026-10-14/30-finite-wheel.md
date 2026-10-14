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


---

## Scheduled rerun — 2026-10-14T10:00:44-04:00

### Provenance and authority refresh

- **Actual execution / completed time:** 2026-10-14T10:00:44-04:00 / 2026-10-14T10:11:40-04:00.
- **Observed current `main` HEAD:** `18fa753f6ea12951845fec65414b47faea0172a1`, retrieved immediately before publication.
- **Fresh authority blobs:** `AGENTS.md` `26715158e91d4f5f71e9e8aa15baa1a17053e456`; `CURRENT_PROOF_CONTRACT.md` `27dceba62b4797bbb394439d13fc4a8dbe29ea0b`.
- **Reporting protocol blobs:** README `81c3dea2cedcd699a5a0523a00e5cc8ec78f8913`; template `f1e13534f2b36a39e833493ec1739e97ab17f3d7`; prompts `f452d69999f0180e7e576011a8ad1ad6a2eed549`.
- **Previous own checkpoint:** this file, blob `e86a066b5fe4488972f9b49400ebb77d76cab41b`, run 2026-10-14T00:12:56-04:00. Its Claims `20261014-wheel-1..2` are now `PROVED_IN_LEAN` on live `main` through `VF_MID_LATE_OWNER_WHEEL_THIRTY_BUDGET.lean`, blob `3701895c3e3af16b6f6b0506ed69f7b5c3d55800`.
- **Today's required earlier stages:** `00-coordinator-am.md` = `TODAY=PENDING`; `10-owner-payment.md` retrieved at blob `08b203d38e2c0d495631c1873edb903d83412ea1`, Claims `20261014-owner-0..4`; `20-analytic-type-ii.md` = `TODAY=PENDING`.
- **Previous-day continuity:** `00-coordinator-am.md` blob `87a596f6f7bcb9bab6b2d29fc7c162c64ed544cb`, `10-owner-payment.md` blob `32f1574b8ade7dedc602b07b1b9257341320080a`, and `20-analytic-type-ii.md` blob `d9f73a0aab42e70ca30a17d16822a8281ca7afef`, all `YESTERDAY=CARRY_FORWARD` where today's stage is pending.
- **Later current-day continuity read because already committed:** Prime Census `fc25130ac028c2556f1754ac75ee494c440e3dbc`, Referee `19e14164a9337af696ce0705a50e48e81248f93a`, Lean Verification `cc3ec0fa23860573909c6492095c42fbaa17a20f`, and Coordinator PM `33709beb6d3dc3043c94a930f72fdd9f375e4fd7`.
- **External intake:** index blob `6fce4e9d024b6c4ad47798c5d7c162101a2435a0`; seven-function handoff blob `efb9015e923fd1ce7da5c5300679924163cc6737`; reproducer blob `4b308fde87a7b746ff7baff22a6f015b5bbf4c53`. This run independently audits `EXT-20261014-1`.
- **Tools actually used:** connected GitHub reads/writes and CPython 3.12 exact integer enumeration. No local Lean build and no web source were used.

### Current central mathematical objective

The unique open public theorem is still `VFCanonicalSquareVonKochStatement`:
there must exist a fixed (C\ge0) such that
[
  |\pi(R^2)-\operatorname{vfMidFinishedMass}(R)-\sqrt2|
  \le C R\log R\qquad(R\ge2).
]
Live `main` now compiles both directions showing that the named dyadic
signed-late correction and actual-prime owner-escape admissibility are
target-equivalent, not smaller arithmetic lemmas. The #915 content audit also
shows that its first-bad payment is equivalent, after the finite base window,
to the fixed (K=2) raw envelope. Consequently this run treats finite wheels
only as independently proved supporting restrictions and makes no closure
claim.

Relevant compiled declarations were inspected in
`VF_MID_FINAL_RAW_CLIPPED_TELESCOPE.lean` blob
`dc1611da7eeca2ed2f2273fa73c9a659b4ba2f42`,
`VF_MID_RECURSIVE_CHILD_INJECTIVE.lean` blob
`795be470bc796421d9a53e76f3eb21788f34e249`,
`VF_MID_OPEN_INLET_TARGET_EQUIVALENCE.lean` blob
`379f17c0739e8bcb4543a91bed9ced7624773ef7`, and
`VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean` blob
`f7d046d8d94962e18f794deee7e33ce7508a0e74`.

### Exact carrier and question

For (A\le R<2A) and a genuine late least-prime owner
(p\in\texttt{vfMidSquareBandLateOwnerPrimes}(A,R)), put
[
 t=\left\lfloor\frac{R^2}{p}\right\rfloor,qquad
 u=\left\lfloor\frac{(R+1)^2-1}{p}\right\rfloor.
]
Current main proves that stripping (p) is cardinality preserving and that
the child fibre is exactly the set of primes (q\in(t,u]). In particular
(p\le R), (q>p>A), every physical occurrence is (n=pq) with
(R^2<n<(R+1)^2), and (u\le t+4). Define
[
 C_M(R,p)=\#\{q\in\mathbb Z:t<q\le u, \gcd(q,M)=1\}.
]
The question was whether the external (M=2310) bound has the exact claimed
endpoints and hypotheses, and whether a strictly stronger deterministic wheel
restriction follows without residue-distribution assumptions.

### Claim 20261014-wheel-5 — corrected sharp-threshold audit of EXT-20261014-1

**Status: `PAPER_PROOF`; verdict `ACCEPT_WITH_SHARPENING`.**

For every (7\le A\le R<2A) and every genuine late owner (p),
[
 #\texttt{vfMidSquareBandCompositeOwner}(R,p)
 \le C_{2310}(R,p)\le C_{210}(R,p)\le C_{30}(R,p)
 \le W_{30}(t)\le2.
]

The submitted (A\ge11) statement is therefore correct, but (A\ge7) is
the sharp uniform threshold. Indeed (p>A\ge7) and primality give
(p\ge11). The strict quotient lower endpoint and (p\le R) give
(q>t\ge R\ge p), so (q>p\ge11). Thus the genuine prime child (q)
is divisible by none of (2,3,5,7,11), proving the (2310)-wheel inclusion.
Nested divisor sets give the middle inequalities, and (u\le t+4) gives the
last two.

Sharpness of the threshold is a genuine exact counterexample:
[
 (A,R,p,q,n,t,u)=(6,8,7,11,77,9,11).
]
Here (64<77<81), (p=7) is the least-prime owner, and the actual fibre
contains (q=11), but (C_{2310}(8,7)=0). Thus the same theorem with
(A\ge6) is false.

No sign, VF coefficient, historical mask, clipping weight, anchor, or source
tag is altered by this result; none is present in this unsigned child census.

### Claim 20261014-wheel-6 — a strictly stronger wheel-30030 capacity

**Status: `PAPER_PROOF`.**

For every (11\le A\le R<2A) and every genuine late owner (p),
[
 oxed{#\texttt{vfMidSquareBandCompositeOwner}(R,p)
 \le C_{30030}(R,p)\le C_{2310}(R,p).}
]
Here (30030=2\cdot3\cdot5\cdot7\cdot11\cdot13). Since
(p>A\ge11), one has (p\ge13), while the strict quotient inequality gives
the prime child (q>p), hence (q\ge17). Therefore
(gcd(q,30030)=1). The second inequality is the literal inclusion of
(30030)-survivors in (2310)-survivors.

The threshold is again sharp: at (A=10,R=11,p=11), the genuine child
(q=13) gives (143=11\cdot13) in the strict block (121<n<144), but
(13\mid30030).

Summing (C_{30030}) over the same owner/root carrier gives the exact unsigned
run consequences
[
 \texttt{LateRemoval}(A,A,B)\le W_{30030}(A,B),
]
[
 \texttt{PrefixSupply}(A,A,B)-W_{30030}(A,B)
 \le\texttt{PrimeSupply}(A,B)
]
for (11\le A\le B\le2A). This is a proper deterministic strengthening of
the fixed-(2310) submission, not an adaptive equidistribution assertion.

### Claim 20261014-wheel-7 — exact finite reproduction and falsification

**Status: `FINITE_COMPUTATION`.**

The external CPython algorithm was independently reimplemented with strict
upper endpoint (((R+1)^2-1)//p). Every listed (2310) total was reproduced,
and the new (30030) totals were:

| run | actual | (C_{2310}) | (C_{30030}) | saving vs (C_{2310}) |
|---|---:|---:|---:|---:|
| [50,100) | 131 | 133 | 131 | 2 |
| [100,200) | 463 | 532 | 481 | 51 |
| [500,1000) | 6,587 | 9,735 | 8,972 | 763 |
| [2634,5267) | 125,272 | 226,691 | 209,320 | 17,371 |
| [5000,10000) | 385,553 | 747,547 | 689,930 | 57,617 |

A separate scan of every (7\le A\le500), every (A\le R<2A), and every
prime (A<p\le R) found no violation of Claim 5. It also reproduced the
sharp (A=6) failure above. These computations establish only the stated
finite checks; Claims 5 and 6 rest on the paper derivations.

Repeated ancestry remains decisive. The same historical prime (q=13)
occurs as (91=7\cdot13) in block (R=9) and (143=11\cdot13) in block
(R=11). Current main proves same-block cross-owner child uniqueness, but it
does not make a historical (q)-charge reusable across blocks. Every proposed
weighted application must retain separate physical source tags and the full
global cross terms.

### Novelty, independence, and quantitative effect

Already known or now compiled: the exact prime quotient interval, generic
finite-wheel nesting, wheel-30 fibre/run bounds, same-block child uniqueness,
and the fact that a complete prefix wheel below its square cutoff identifies
primes exactly. None is relabeled new.

New in this rerun: the sharp (A\ge7) threshold for the external (2310)
carrier, its smallest threshold counterexample, and the stronger
(30030)-capacity theorem with sharp (A\ge11) threshold and exact run
totals. These use only genuine prime identity, strict square endpoints, and
divisibility by fixed small primes. They assume neither RH nor any endpoint
error estimate.

The numerical improvement is exact but modest: on ([2634,5267)),
(C_{30030}) lowers the proved unsigned cap from (226691) to (209320);
the actual population is (125272). The trivial four-site cap, parity cap,
wheel-30 cap, (2310) cap, and (30030) cap form a valid descending chain.
No member controls the signed raw source or its quadratic norm. Extending the
fixed modulus eventually reconstructs the already-known exact prime interval,
so this hierarchy does not by itself create an RH-scale cancellation estimate.

### First unresolved lemmas and no-narrowing result

- **Completion theorem:** the first unproved theorem that closes the program is
  still `VFCanonicalSquareVonKochStatement`; the named signed-late and
  owner-escape statements are target-equivalent.
- **Structural supporting problem:** an exact original-occurrence,
  coefficient, sign, owner, ancestry, mask, clip, anchor, multiplicity,
  chronology, and cross-term preserving source reassembly may still be useful,
  but an inequality strong enough to pay it is not supplied by Claims 5--6.
- **Finite-wheel limit:** a larger fixed primorial monotonically sharpens an
  unsigned local population cap; without an exact signed source identity and a
  new signed estimate, this is census refinement rather than target progress.

### Explicit 1 AM Prime Census Laboratory tests

1. Independently verify Claim 5 for every (7\le A\le5000), retaining
   ((A,R,p,q,n,t,u,C_{2310})), and confirm the sharp failure
   ((6,8,7,11,77,9,11)).
2. Reproduce all five (C_{30030}) totals in Claim 7 with an independent
   physical-integer/SPF implementation, not the quotient script.
3. Confirm the (A=10,R=11,p=11,q=13,n=143) sharp failure for the
   (30030) threshold and retain strict endpoint evidence.
4. Compare (C_{30030}) with the adaptive complete-prefix-wheel count on the
   actual threatening runs; report exact savings but do not infer residue
   independence or signed cancellation.
5. In every ancestry experiment retain
   ((R,p,q,n,w_R,\text{sourceTag},\text{mask},\text{historicalTag}));
   test repeated (q=13) and never spend one historical occurrence twice.

### Referee and Lean handoff

Adversarial Referee should check the deductions (t\ge R\), (q>p), the
two sharp threshold witnesses, the use of (((R+1)^2-1)//p), and the run
inequality direction. Lean Verification may formalize Claims 5 and 6 only as
supporting finite-carrier corollaries after independent acceptance. No source
payment, target-equivalent inlet, or RH closure PR is warranted.

### Updated final status

**Net-new mathematical progress:** `PAPER_PROOF` of the sharpened
wheel-2310 threshold and the strictly stronger wheel-30030 capacity;
`FINITE_COMPUTATION` reproduction and new exact totals.

**Production target:** `NO_NEW_RESULT`. No canonical endpoint bound, signed
source estimate, finite A/C, CORR-4, or RH theorem is proved.

**Completeness:** `DONE` for this scheduled research stage.

**No RH-proof claim:** yes.

## Updated next-run resume capsule (non-authoritative)

- **Checkpoint:** 2026-10-14T10:11:40-04:00 at main
  `18fa753f6ea12951845fec65414b47faea0172a1`.
- **Upstream consumed:** today's Owner Payment blob `08b203d3...`;
  today's `00/20` are `PENDING`; yesterday's `00/10/20` blobs and the
  already-committed current-day Census/Referee/Lean/Coordinator blobs listed
  above were read.
- **External claim consumed:** `EXT-20261014-1` =
  `ACCEPT_WITH_SHARPENING`.
- **Completed evidence:** Claims `20261014-wheel-5..7`; exact (2310)
  reproduction; (30030) table; sharp threshold counterexamples.
- **Uncertain or invalidated:** no theorem invalidated. The external
  (A\ge11) hypothesis was sufficient but nonsharp for (2310). No local
  Lean compilation was performed.
- **First unresolved blocker:** no independently proved signed estimate on the
  original weighted source; the completion theorem remains the canonical
  target itself.
- **Next action:** independent physical census and referee review of Claims
  5--6; formalize only after acceptance.
- **Avoid:** presenting deeper fixed wheels as signed cancellation, reusing a
  historical prime across descendants, or treating a target-equivalent inlet
  as a narrower lemma.


---

## Scheduled 4 PM run checkpoint — 2026-10-14T16:12:00-04:00

- **Status:** `IN_PROGRESS`; durable checkpoint before final derivation.
- **Observed current `main` HEAD:** `13c3aeab8f84fc2309175261948a17a50c8342f4`, fetched by explicit `fetch_commit(main)`.
- **Fresh authority:** `AGENTS.md` blob `26715158e91d4f5f71e9e8aa15baa1a17053e456`; `CURRENT_PROOF_CONTRACT.md` blob `27dceba62b4797bbb394439d13fc4a8dbe29ea0b`.
- **Current objective:** the unique public target remains `VFCanonicalSquareVonKochStatement`. The named signed-late and #915 payment propositions are target-equivalent or false on first-bad instances, so this run seeks an independently proved incidence restriction on the literal small-owner current/historical carrier.
- **Upstream intake:** today's `00-coordinator-am.md` is `TODAY=PENDING`; today's Owner Payment `a2ed7dc2...`, Analytic Type II `b8ee78df...`, Coordinator PM `d7229fa1...`, this report `2c2d3a0d42c3af6efb638b2cd2d8aec806aaaf74`, and external inbox `6fce4e9d...` were read. Yesterday's coordinator/owner/analytic/wheel reports were read as continuity.
- **Delta task:** prove and falsify a tag-wise root-spacing bound for all repeated descendants of one historical prime `q`, then test whether it yields a multiplicity-safe signed packet with the original VF weights. All current occurrences remain distinct; the historical `q` charge is counted once.
- **Checkpoint classification:** `NO_NEW_RESULT` at checkpoint; no canonical-bound or RH claim.


## Scheduled 4 PM run completed — 2026-10-14T16:18:00-04:00

### Provenance and two-day continuity

- **Report date / stage:** 2026-10-14, America/New_York / RH | Finite Wheel & Incidence.
- **Observed current `main` HEAD:** `13c3aeab8f84fc2309175261948a17a50c8342f4`; explicit `fetch_commit(main)` at 2026-10-14T16:08:55-04:00 returned merge commit #942.
- **Central authority:** `main:AGENTS.md` blob `26715158e91d4f5f71e9e8aa15baa1a17053e456`; `main:CURRENT_PROOF_CONTRACT.md` blob `27dceba62b4797bbb394439d13fc4a8dbe29ea0b`; both fetched successfully.
- **Current-day upstream actually read:** `00-coordinator-am.md` = `TODAY=PENDING` (verified 404); `10-owner-payment.md` blob `a2ed7dc27756393c49beb5bebae80971a2af6aff`, latest run 12:36:56 ET, Claims `20261014-owner-5/-6`; `20-analytic-type-ii.md` blob `b8ee78df90d9fccb4b1201c933720a70300d9d51`, latest run 12:54:35 ET, Claims `20261014-analytic-4/-5`; `90-coordinator-pm.md` blob `d7229fa116dfa7180fc941f18e5d8250dacf6714`, latest run 12:24:28 ET. The pre-run version of this report was blob `2c2d3a0d42c3af6efb638b2cd2d8aec806aaaf74`.
- **Previous-day continuity:** coordinator AM `87a596f6f7bcb9bab6b2d29fc7c162c64ed544cb`, coordinator PM `aab612c387de93a777c696bc54be128b210cb8b8`, Owner `32f1574b8ade7dedc602b07b1b9257341320080a`, Analytic `d9f73a0aab42e70ca30a17d16822a8281ca7afef`, and this stage `1c96431194038b2691f628bfce5736f7f0dcacd5` were read. These are historical continuity, not current authority.
- **External intake:** `EXTERNAL_HANDOFFS.md` blob `6fce4e9d024b6c4ad47798c5d7c162101a2435a0`. `EXT-20261014-1` is now subsumed by merged sharp primorial theorems; `EXT-20261014-5` remains `PAPER_PROOF` and is not used below.
- **Early checkpoint:** commit `fdf03ae1afea635a0c5c099c87035faaee6dc491`, verified readback blob `492260fc9d1f786befc3c12c637fb7c2d20f80be`.
- **Tools:** GitHub connector reads/writes and CPython 3.12 exact integer enumeration. No local Lean build, proof PR, web source, issue, branch, or source-file write.

### Current objective and changed formal baseline

The unique public target remains `VFCanonicalSquareVonKochStatement`:
\[
\exists C\ge 0\ \forall R\ge2,\qquad
|\pi(R^2)-\operatorname{vfMidFinishedMass}(R)-\sqrt2|
\le C R\log R.
\]
Current compiled main shows that the signed-late/admissibility interfaces are target-equivalent and that the old #915 payment is not an independently available first-bad premise. Therefore this result is not presented as a completion lemma.

The live baseline used here is:

- `VF_MID_HISTORICAL_PRIME_MULTIPLICITY.lean`, blob `fda6db056571191feffd08f2d1d6fe0fa02f0d8c`: exact owner threshold \(2^{20}\), global fibre, and same-block uniqueness;
- `VF_MID_OWNER_SIGNED_PAIR_BOUNDS.lean`, blob `e3cc17224469e24516390a8f20e590d5932dbfc1`: original current weight \(w_R<9/64\), historical weight \(w_r<99/640\), literal signed charges, and restored pair cross-term identity;
- `VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean`, blob `58b78186e4fd5b68179afe4be0b7b6e4761442d6`, and `VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE.lean`, blob `e61eb36301f650bfb41079bbd7367f9f45cf6d3e`: original physical sites, weights, masks, clipping, raw-parent sectors, residuals and cross terms;
- `VF_MID_932_ORIGINAL_VF_CARRIER_DISJOINT.lean`, blob `9dcd03a96ff44ba876fec2994a487441cd6f1d09`: the relevant carriers cannot be silently identified;
- `VF_MID_LATE_OWNER_SHARP_PRIMORIAL_BUDGET.lean`, blob `4925053b09acaa927f48c7fad8f13c0f4bf5ff71`: this report's earlier Claims 5/6 are now `PROVED_IN_LEAN`.

The new question is whether the threshold \(1024p\le\lfloor\sqrt{pq}\rfloor\) supplies a cross-block restriction that remains valid when the same historical prime \(q\) has many current descendants.

### Claim 20261014-wheel-8 — sharp 1024 root spacing for a repeated historical tag

**Status: `PAPER_PROOF`. No Lean compilation was performed.**

Let \(q\) be prime and let \(3\le p_1<p_2\) be primes. Put
\[
R_i=\lfloor\sqrt{p_iq}\rfloor.
\]
If \(1024p_2\le R_2\), then
\[
\boxed{R_2-R_1\ge1024.}
\]
Consequently, for \(A<B\) and any set \(S\) of eligible prime owners with
\(A\le R_p<B\),
\[
\boxed{|S|\le 1+\left\lfloor\frac{B-A-1}{1024}\right\rfloor}
\]
when \(S\ne\varnothing\). In particular, a half-open root interval of length at most 6144 contains at most six descendants of one historical tag.

**Derivation.** The compiled threshold equivalence gives
\(q\ge2^{20}p_2\). Since distinct odd primes differ by at least two,
\[
\sqrt{p_2q}-\sqrt{p_1q}
=\frac{q(p_2-p_1)}{\sqrt{p_2q}+\sqrt{p_1q}}
\ge\frac{p_2-p_1}{2}\sqrt{\frac q{p_2}}
\ge1024.
\]
Translation by the integer 1024 commutes with the floor, so the same lower bound holds for \(R_2-R_1\). Ordering the roots in \([A,B)\) gives the cardinality bound.

**Carrier audit.** Every occurrence remains the literal squarefree composite \(p q\), with genuine least-prime owner \(p\), strict walls
\(R_p^2<pq<(R_p+1)^2\), and unit occurrence multiplicity. Repeated \(q\) tags are retained. A mask may select any subset of these occurrences and cannot weaken the spacing bound. No assertion is made that the one historical \(q\) occurrence passes the source's admission/clipping masks.

**Independent ingredient and novelty.** The compiled exact fibre counts owners globally and proves only same-block uniqueness. Repository search found no quantitative separation theorem between different roots of one tag. The new ingredient is the threshold geometry combined with the parity gap between genuine odd primes. It is neither a wheel survivor census nor an inequality equivalent to the canonical endpoint bound.

### Claim 20261014-wheel-9 — multiplicity-safe six-block signed packet

**Status: `PAPER_PROOF`.**

Let \(q\) be prime, \(A<B\), and let \(S\ne\varnothing\) be any selected set of prime owners \(p\ge3\) satisfying
\[
R_p=\lfloor\sqrt{pq}\rfloor,\qquad
1024p\le R_p,\qquad A\le R_p<B,\qquad B-A\le6144.
\]
Put \(r=\lfloor\sqrt q\rfloor\). Count the historical prime occurrence \(q\) exactly once. Then the literal original signed seat charges satisfy
\[
\boxed{
\sum_{p\in S}\operatorname{charge}(R_p,pq)
+\operatorname{charge}(r,q)<-\frac1{640}.}
\]

**Proof.** Claim 8 gives \(|S|\le6\). Each current \(pq\) is composite and contributes exactly \(+w_{R_p}\). Since \(R_p\ge1024p\ge3072\), the compiled physical bound gives \(w_{R_p}<9/64\). The nonempty fibre and threshold imply \(r\ge1024\); the historical prime contributes exactly
\(-(1-w_r)\), with \(w_r<99/640\). Therefore
\[
\sum_{p\in S}w_{R_p}-(1-w_r)
<6\frac9{64}-\frac{541}{640}
=-\frac1{640}.
\]

This is a signed, original-coefficient statement and does not clone \(q\): all selected current occurrences are summed, while the historical charge occurs once. It remains valid after deleting current sites by a mask, provided the one stated historical occurrence is actually present. It does not restore the anchor, squareful terms, clipping coefficients, omitted sites, other historical tags, or quadratic cross terms.

**Quantitative contribution.** For a root window of length \(L\), the integer-population trivial bound is \(L\) current descendants and the uniform current-mass bound is \((9/64)L\). Claim 8 replaces these by
\[
1+\left\lfloor\frac{L-1}{1024}\right\rfloor
\quad\text{and}\quad
\frac9{64}\left(1+\left\lfloor\frac{L-1}{1024}\right\rfloor\right).
\]
At \(L\le6144\), this crosses the exact one-history sign threshold with strict margin \(1/640\). No density hypothesis, RH, finite A/C, #915 payment, or endpoint bound is assumed.

### Claim 20261014-wheel-10 — exact computation and falsification

**Status: `FINITE_COMPUTATION`; `REFUTED` for a 1025-spacing strengthening and for unrestricted one-history payment.**

1. A sieve through \(10^7\) checked all 438,030 prime \(q\) from \(3\cdot2^{20}\) through \(10^7\), with every eligible prime owner. No root gap below 1024 occurred; the smallest observed gap was 1110 at
\((q,p_1,p_2,R_1,R_2)=(7340033,5,7,6058,7168)\).
2. The stronger universal gap 1025 is false. Exact trial division certified the primality of
\[
p_1=10139,\quad p_2=10141,\quad q=10633609379.
\]
The corresponding data are
\[
R_1=10383360,\quad R_2=10384384,\quad R_2-R_1=1024.
\]
The products are \(107814165493681\) and \(107835432712439\); both have strict positive lower and upper square gaps. Threshold slacks \(R_i-1024p_i\) are respectively 1024 and 0. Thus the constant in Claim 8 is sharp on genuine primes and physical descendants.
3. The current Owner witness \(q=1000000007\), \(A=488109\) was independently re-enumerated: 111 selected prime owners, roots 488876 through 976217, minimum adjacent root gap 1064. Claim 8 gives the honest capacity 477. Hence it records repeated ancestry but does not falsely force a one-slot fibre.
4. The same 111-descendant witness, with upstream's rigorous \(X>111/14>1>y\), refutes extending Claim 9 to an arbitrary half-run. A single historical charge cannot be reused in successive 6144-windows.

**Algorithms actually executed.** CPython 3.12 used an Eratosthenes byte sieve, `math.isqrt`, exact product/square-gap checks, and deterministic 64-bit Miller-Rabin followed by complete trial division through \(\lfloor\sqrt q\rfloor=103119\) for the sharpness witness. The \(q=1000000007\) reproduction sieved owners through 953 and retained every \((p,R_p)\). No floating calculation is used in Claims 8 or 9.

### Falsification, circularity and source limits

- Small endpoint cases, threshold equality, strict square walls, repeated historical tags, and a production-style half-run overload were tested.
- The theorem permits arbitrarily many descendants globally; it only spaces them. It does not infer historical availability from current demand.
- Claim 9 spends one historical \(q\) once. Partitioning a long run into short windows and paying every window with that same \(q\) is explicitly invalid.
- The signed linear packet is not the global NNS quadratic. The exact merged cross-term identity shows that residual/anchor cross terms remain.
- The original active masks and clipping are not replaced by a larger carrier. The result applies to an admitted subset only after an exact source theorem proves which current and historical tags are present.
- No implication to `VFCanonicalSquareVonKochStatement` has been proved. The production target remains `NO_NEW_RESULT`.

### First unresolved lemma

Define on the literal first-bad active carrier, for each historical tag \(q\), its actually admitted current descendants and its admitted historical supply \(a(q)\). Prove an order-independent disjoint decomposition that may allocate the unique historical \(q\) to at most one root window of length 6144, leaves every other descendant in a multiplicity residual, and preserves masks, clipping, anchor, squareful restoration, chronology and all quadratic cross terms. Then bound the joint residual without reusing \(q\).

This route-specific lemma, provisionally `TAG-PACKET-DISJOINT-1`, is not known to be sufficient for the canonical target.

### Explicit 1 AM Prime Census Laboratory tests

1. Independently verify Claim 8 over genuine tuples \((q,p,R_p)\), including threshold equality and both strict square gaps. Confirm the exact 1024-gap witness above.
2. Search for the maximum tag degree in every half-open window of lengths 1024, 2048, ..., 6144. Retain owner primes and roots; do not deduplicate \(q\).
3. Test whether prime-wheel restrictions improve the six-slot cap, especially the minimum root span supporting seven prime owners. Treat any finite improvement as finite evidence until an all-scale residue proof is supplied.
4. On actual masked first-bad carriers, emit tuples
\((q,p,R,pq,w_R,\text{currentTag},\text{historicalTag},\text{mask},\text{clip})\).
Verify Claim 9 only when the single historical \(q\) tag is present, and count it once.
5. Reproduce \(q=1000000007,A=488109\): 111 descendants, minimum root gap 1064, spacing capacity 477, exact current-weight sum and one historical magnitude. This is the adversarial long-run control.
6. Measure how many disjoint 6144-windows are occupied by each \(q\), and report the residual after choosing at most one packet per actually available historical tag. Do not infer a global signed bound from packet counts alone.

### Review and formalization handoff

- **Adversarial Referee:** check the floor transfer, use of the odd-prime gap, the \(B-A-1\) endpoint, the inference \(r\ge1024\), the exact \(-1/640\) arithmetic, and the mask/availability limitation. Independently trial-divide the sharp witness.
- **Potential Lean Verification candidate after acceptance:** formalize Claim 8 against `vfMidHistoricalPrimeOwnerFibre`, then Claim 9 using the existing literal signed-charge bounds. The theorem must state one historical occurrence, a selected finite current set, and \(B-A\le6144\); it must not claim a global payment or source inclusion.
- **Prime Census:** Claims 8-10 and the six tests above are explicit and reproducible.

### Final classification

**Net-new mathematical progress:** `PAPER_PROOF` of sharp cross-block 1024 spacing and the multiplicity-safe original-weight six-block signed packet; `FINITE_COMPUTATION` sharpness and repeated-tag tests.

**Trivial versus improved bound:** \(L\) current sites versus
\(1+\lfloor(L-1)/1024\rfloor\); for \(L\le6144\), an exact signed margin below \(-1/640\) after using one historical \(q\) once.

**Canonical/RH status:** `NO_NEW_RESULT`. No claim that RH, finite A/C, CORR-4, a target-equivalent inlet, or the old #915 payment is proved.

### Updated next-run resume capsule — 2026-10-14T16:18:00-04:00

- **Source freshness:** main `13c3aeab8f84fc2309175261948a17a50c8342f4`; central blobs `26715158...`, `27dceba6...`; multiplicity `fda6db05...`; signed pairs `e3cc1722...`; physical Fubini `58b78186...`; raw-parent splice `e61eb363...`.
- **Upstream consumed:** today AM coordinator `PENDING`; Owner `a2ed7dc2...`, Analytic `b8ee78df...`, Coordinator PM `d7229fa1...`; yesterday coordinator/owner/analytic/wheel blobs listed above; external inbox `6fce4e9d...`.
- **Reusable new claims:** `20261014-wheel-8` sharp 1024 tag-root spacing; `20261014-wheel-9` one-history, at-most-six-current original-weight packet \(<-1/640\); `20261014-wheel-10` finite verification and 1025 refutation.
- **Computation:** 438,030 prime \(q\le10^7\) scanned; exact sharp witness \((10139,10141,10633609379)\); \(q=1000000007\) half-run independently reproduced.
- **First unresolved blocker:** `TAG-PACKET-DISJOINT-1`, the exact mask/clip/anchor/cross-term preserving allocation and multiplicity residual.
- **Next action:** independent Census and Referee review; request Lean formalization only if accepted.
- **For Agent #7:** no PR exists or is requested in this run; no local Lean or CI evidence.
- **Avoid next run:** reusing one \(q\) in multiple windows, converting the linear packet to a global NNS conclusion without cross terms, or repeating the unchanged fixed-primorial scans.
