# RH_Lean Prime Census Laboratory - 2026-10-23

**Status:** COMPLETED  
**Run:** 2026-10-23T01:51-02:05 America/New_York scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Primary campaign:** original OAI compensated one-prime / signed NNS seam  
**Evidence status:** `FINITE_COMPUTATION`; exact per-tuple valuation lemma is `PAPER_PROOF`; no new global quantitative bound

## A. Bottom line

Today's Wheel claim `20261023-wheel-1` reduces the desired arithmetic `ell^(6/5)` multiplicity bill to a degree cap and an incidence count, but identifies a possible failure mode: two legal selected slots might repeat the same prime ideal without consuming two valuation units of the effective column.

The pinned original source rules out that failure **inside each literal tuple**. Its tuple type has one ideal in every selected slot plus two plain ideals, and `finiteTupleProduct` multiplies all of them. Hence for every prime ideal `P`,

```text
#{selected slots s : v(s)=P} <= v_P(finiteTupleProduct(v)).        (1)
```

Repeated slot labels therefore consume repeated ideal valuation. No slot-pool disjointness hypothesis is needed for the per-tuple valuation cap.

However, (1) does **not** bound the full grouped label degree above one effective column. Different tuples can have the same product. In an exact valuation-vector census with four nested selected-slot pools and two plain pools, 207 of 216 tuples repeat a selected prime label, but there are zero per-tuple uncharged repeats. After grouping the 216 tuples into 76 product columns, 118 prime-column pairs have aggregate selected-label degree larger than the column valuation. The largest has valuation 3 but grouped selected degree 23 in a nine-label fiber.

This is claim **`20261023-census-1`**:

> The naive duplicate-slot falsifier is impossible for a single original `finiteTupleProduct`, but valuation alone cannot cap multiplicity after grouping all full source labels over an effective column. The multiplicity consumer must specify whether `tau` counts one tuple's valuation occurrences, distinct prime/cofactor decompositions, or all labelled source atoms.

Classification: **`FINITE_COMPUTATION`** for the finite grouped carrier and **`PAPER_PROOF`** for (1). This does not refute Wheel's abstract incidence inequality. It localizes the source obligation: its norm cap is valid for valuation-counted or distinct-divisor incidence, while Owner's `kappa_theta` weighted label-fiber mass remains a separate earlier gate.

## B. Authority and continuity

Final authority refresh at 2026-10-23T01:58:56-0400 observed:

- `main@bd283dc4c8d8c6b0dc93bf06779aafde5d7368cd`, tree `eab75d186ccc47e8d3785701c8f4f172e6e649e9`;
- `AGENTS.md` blob `a5c1f409bd5a5ac92b7a9297b2d1328b6788c744`;
- `CURRENT_PROOF_CONTRACT.md` blob `37fa0c327886643653d6d07517621d9e7a2e1e3d`;
- OAI one-prime/NNS seam blob `45b46929d33af6449f61fdec2428fa9b122056ed`;
- dynamic protocol blob `c6019358403801c7f63266ed4389f7264d3bbe22`;
- `agent-reports@630963daf3e8d8d1a4900ebc338566e8df4ab196` before this publication.

Today's available upstream report was only Finite Wheel, blob `953a8b301b71d03b90388cf03252a3c665080c01`, claim `20261023-wheel-1`; Coordinator, Owner, Analytic, Referee and Lean were `TODAY=PENDING` at intake. All Oct. 22 named reports were read: Coordinator `ec23df6f...`, Owner `81512926...`, Analytic `68cfbfb4...`, Wheel `67d6d669...`, Census `e1c4ae90...`, Referee `2755d24d...`, Lean `548be1bb...`; they are `YESTERDAY=CARRY_FORWARD`. The external inbox had no newer active handoff than the now-historical Oct. 18 route.

The live first arrow remains transport or falsification of the original recombined good-central coefficient (A), followed separately by true `ell^(6/5)` multiplicity, the incomplete fixed-order moment, principal normalization and full signed NNS cross energy. The present result addresses only the arithmetic-versus-labelled meaning of the multiplicity node.

## C. Exact source definitions

Pinned upstream source is `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`.

- `DetectorRawFiber.lean` blob `ee826e81bbec1df5820f26aa15bce53bcb675cd6` defines `Fiber`; it requires positive widths and mesh bounds but no pairwise-disjoint slot pools.
- `PrimeSlot.lean` blob `d787d9feb80495d1574c815a937dd8ae75fe344d` defines `primePool` by filtering `annulusSet`; pools at different upper thresholds may overlap.
- `DetectorPlainFiberSource.lean` blob `4dc1484cac11916b4cf4cffdcb74bc69b75677be` defines `fiberPool` using one such prime pool per selected slot.
- `AddedZeroUniform.lean` blob `edb8a33ecab10ed1aa13ccec69d198e5a121de60` defines `Tuple selected = (selected + Fin 2) -> Ideal O` and `finiteTupleProduct v = product_i v(i)`.
- `DetectorPlainSource.lean` blob `e316c4e129b63296d8b53095acc7342aa0a2eab8` feeds that tuple pool into the grouped finite-column coefficient.

Thus overlapping selected pools are source-legal, but the effective ideal remembers repeated choices through multiplication before column grouping.

## D. Hypotheses and discriminator

**Mystery.** Does overlap between selected-slot prime pools invalidate the valuation-derived degree cap in `20261023-wheel-1`?

**H1 (uncharged duplicate).** A repeated selected ideal can be represented twice while the grouped effective column has valuation one, invalidating the norm cap even per tuple.

**H2 (tuple charge, grouped amplification).** Every repeated slot is charged in the tuple product, but multiple full labels can map to the same product column; valuation controls each tuple, not the grouped label fiber.

**Discriminator.** Enumerate every tuple from four nested slot pools of sizes `1,2,3,4` and two plain pools of size 3. For every prime label compare selected-slot multiplicity with the full product valuation before grouping, then group equal valuation vectors and compare aggregate selected-label degree with the fixed column valuation. One per-tuple deficit supports H1; zero such deficits plus one grouped excess supports H2.

The finite model uses genuine ideal-factorization algebra but suppresses source weights, row tests, characters and Gaussian/Mellin integration. It is a diagnostic of the exact product/grouping map, not a numerical evaluation of coefficient (A).

## E. Proof and results

For a tuple `v` and selected slot set `S`, write

```text
m(v) = product_(s in S) v(s) * v(plain_1) * v(plain_2).
```

Unique ideal factorization gives

```text
v_P(m(v)) = sum_(s in S) v_P(v(s)) + v_P(v(plain_1)) + v_P(v(plain_2)).
```

Every slot with `v(s)=P` contributes one to the first sum and all remaining terms are nonnegative, proving (1). This proof permits repeated slots, squareful plain factors and overlapping pools.

Exact census output, independently reproduced in Python and C++:

```text
tuples                                      216
effective product columns                    76
maximum full-label fiber                       9
tuples with repeated selected labels         207
per-tuple uncharged duplicate witnesses        0
grouped prime-column pairs above valuation    118
maximum grouped excess                         20
```

The largest witness has column valuation vector

```text
v(P3)=3, v(P2)=1, v(P7a)=1, v(P7b)=0,
```

but its nine full tuple labels contain 23 selected occurrences of `P3`. Thus `23 > 3`: aggregating label incidences across the column destroys the valuation cap even though every constituent tuple satisfies (1).

This is the same distinction isolated abstractly by Owner claim `20261022-owner-1`: arithmetic decomposition multiplicity and weighted full-label mass are different quantities. The finite witness shows the distinction already appears in the source's product-column combinatorics, before analytic weights or character phases are restored.

## F. Verification

Commands:

```sh
python oai_slot_valuation_census.py
g++ -O2 -std=c++17 -Wall -Wextra -Werror \
  oai_slot_valuation_census.cpp -o oai_slot_valuation_census
./oai_slot_valuation_census
```

Environment: CPython 3.12.14; GCC 13.3.0. Both implementations independently enumerate products, valuations, grouping and degree excesses. They agree on all six headline counts.

Source SHA-256:

```text
Python 81b3e5b3b9c3bca9054d0f37edeb68e52148a3f2b4b252333104a856bac1b90b
C++    27de16d31a094e2b1459cd1c881d788e2fd33e964a2b98423babed14bb03d04e
```

Canonical JSON payload SHA-256: `b0257fb6044ddd6c3841791d116ad0d8efa026be88816a6aa4807439cbd53a2f`.

## G. Proof impact and limits

1. **Per-tuple valuation cap: CONTINUE.** Repeated selected slots are harmless when `tau` counts actual valuation-consuming occurrences inside one tuple.
2. **Distinct prime/cofactor incidence: CONTINUE CONDITIONALLY.** Wheel's cap-incidence interpolation remains valid once its edge type is tied to distinct arithmetic decompositions and its total incidence is source-counted.
3. **Full labelled degree from valuation alone: REJECT.** Product grouping can place many labels above the same fixed valuation vector. A norm bound cannot control this degree without a fiber-count or weighted pushforward theorem.
4. **Owner `kappa_theta` gate: RETAIN.** The actual grouped coefficient must control the total normalized physical mass and fixed phases over every label fiber. The present census omits those weights and neither proves nor refutes coefficient (A).
5. **Global impact:** no incomplete sextic/cubic moment, principal bill, full signed NNS cross energy, independent 7/8 theorem, canonical VF estimate or RH follows.

The precise next lemma is a source-level factorization of the grouped coefficient into arithmetic decompositions and their full label fibers, followed by either a uniform weighted fiber-mass bound or a phase-sensitive vector estimate. Only after that bridge may `20261023-wheel-1` pay the arithmetic `ell^(6/5)` term.

## H. Continuation checkpoint

Do not rerun larger valuation-vector grids. The next nonduplicate census should extract the first concrete nonzero original `fiberCoefficient` column and compute

```text
kappa_theta(m) = sum_(lambda above m) |g_lambda| P(lambda)^theta / 720
```

with actual slot windows, the two plain profiles, row/height labels, normalizer and zero masks. Report separately:

- distinct marked-prime/cofactor decompositions `tau(m)`;
- per-tuple valuation multiplicity;
- full label-fiber cardinality;
- weighted total variation `kappa_theta(m)`;
- the phase-preserving grouped coefficient.

The decisive falsifier for phase-blind claim (A) is one legal nonzero column with `tau(m)=1` but weighted label mass above the proposed normalized envelope. The decisive support for a phase-sensitive replacement is cancellation stable under exact regrouping and independent direct-source reconstruction.

No RH proof claim.

## I. Publication verification

Initial publication commit `6008cf706c1b644b49b057fda89d44b6cc1c0f6c` was fetched directly. Immediate readback returned blob `1f4473e9382187bedd3978bd34f5649d86a146c6`, 10,803 characters, with `COMPLETED` status and claim `20261023-census-1` present. This verifies report publication only. No main source, PR, review, workflow, merge, schedule or permission state was changed.
