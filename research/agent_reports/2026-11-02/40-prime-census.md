# RH_Lean agent daily report - 2026-11-02 / RH | Prime Census Laboratory

## Scheduled run - claim `20261102-census-1` - 2026-11-02 03:22 EST (-0500)

**Status:** COMPLETED / exact signed held-out affine-cell census and independent reconstruction.  
**Evidence classes:** `FINITE_COMPUTATION`; `INDEPENDENT_VERIFICATION` of the published squarefree population counts; `FINITE_SURVIVAL` of a preregistered square-root-scale discriminator; `CONJECTURE` for all-scale signed affine cancellation; `NO COMPLETE SOURCE BOUND`; `NO FIXED ETA GAIN`; `NO RH`.

### A. Authority, provenance, and continuity

Final observed main was commit `a33987e275f8a431641d3f475b71a24aa2b1437c`, the human merge of PR #1069. Retrieval and computation occurred 2026-11-02 03:11-03:22 EST on Linux x86_64, Python 3.12.14, and g++ 13.3.0.

Live authority and source blobs:

- `AGENTS.md`: `9fa5e9519e2fb6dde22217aa2a18982dafef373a`;
- `CURRENT_PROOF_CONTRACT.md`: `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`;
- selector: `d05c327ae694ea54b599dab0a21032a056b521f1`;
- broad-search policy: `b5c063c51556ba57c4b25bcc380a606fa8daa207`;
- complete-return contract: `16838f7f3c8724b970f8b8ece0bceaab9418066d`;
- research engine: `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`;
- original `eulerFractionOffQ`: `research/EULER_FRACTIONAL_COUPLED_20261027.lean`, blob `e6c4b1690e497760d366e36b28a1f7aa60e19f85`;
- original moving product rows and activation: `research/EULER_PHYSICAL_COMPLETE_PACKET_20261030.lean`, blob `8084af7fa50fb5b8361a64f05eb658f08b529ca7`;
- literal lower historical envelope: `RHLean/Proof/SquareRootLegalAncestryGramReduction.lean`, blob `1270d4d91c53b50b110d10014f223f427fb7a575`;
- finite-A endpoint statement: `RHLean/Proof/SquareRootMertensEndpointAmplification.lean`, blob `7793d7bfd842348facf62a7ad856bc802ffcd15c`.

The canonical open objective remains the actual-prime square von Koch bound
[
  exists Cge0 orall Rge2,qquad
  |pi(R^2)-VF_{m can}(R^2)|le C Rlog R.
]
The nearer native benchmark remains a complete signed square-shell gain
[
 sum_{Hle R<2H}|Delta_R|^2
 ll_arepsilon H^{5/2-eta+arepsilon}
]
for one fixed (eta>0), with every principal, diagonal, high, mixed, activation, reciprocal, and interpolation cost restored. It is OPEN.

Open/draft PR search returned none. Today Owner, Analytic, and Wheel reports were available at blobs `3110b464e623430dd07c7fc81d3421b3caffa824`, `54c30c65ea6d9923bc9b25c01f02adbbefaf991b`, and `f3457205aa4a8c2bf9696b30501e89598fd10fc2`. Today Coordinator, Referee, Lean, and prior Census were `TODAY=PENDING`. Their 2026-11-01 reports were carried forward as `YESTERDAY=CARRY_FORWARD` at blobs `8f661bc144fd96ffd7a9a8cd084e74e3df05d1a8`, `fbf6dfc995e7d38b1ec07754e4d368a91112ecec`, `6aa7197c4169a70debed607e12f4639218cd21b6`, and `8724bbebf07365ffc5364b411caea7c6d804d468`. External handoffs remained blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than 2026-10-18.

### B. Why this experiment was selected

The stable NEXT-CENSUS FINITE-AC discriminator was already completed yesterday in claims `20261101-census-1,3`; repeating or merely enlarging it would violate the no-rescan instruction. The newest Coordinator assignment instead requested a shift-resolved signed test, and today's Wheel claim `20261102-wheel-1` supplied an exact legal fixed cell that saturates the unsigned incidence bound.

Wheel proved on paper that
[
 m_t=14+25t,qquad n_t=5+9t,
]
[
 x_t=9m_t=126+225t,qquad y_t=25n_t=125+225t,
]
so (x_t-y_t=1). Whenever (m_t,n_t) are squarefree, the pair is a genuine daughter-daughter occurrence in the one fixed cell
[
 (h,r,q,p)=(1,2,3,5)
]
with absolute coefficient (1/15). The unsigned population has positive density. The unresolved discriminator is whether the actual sign (mu(m_t)mu(n_t)) is coherent or cancels.

This experiment retains that genuine coefficient sign. It does not substitute an independent-sign model, and it does not claim to reconstruct the other cells or the complete (Xi_H).

### C. Preregistered hypotheses and frozen ranges

For
[
 I_H={tge0:H^2le126+225t<4H^2},
]
define the exact eligible population and signed sum
[
 N_H=#{tin I_H:mu(m_t)mu(n_t)
e0},
]
[
 S_H=sum_{tin I_H}mu(m_t)mu(n_t).
]

Competing mechanisms were fixed before inspecting the held-out values:

1. **coherent-cell hypothesis:** the fixed gap, owner, and lift primes create a stable signed bias, so (|S_H|) is a visible positive fraction of (N_H);
2. **signed-cancellation hypothesis:** unsigned incidence saturates, but Möbius parity cancels at approximately square-root scale.

The finite rejection rule for the second mechanism was
[
 |S_H|>6sqrt{N_Hlog H}
]
at any held-out block. This is a finite discriminator only, not a proposed all-scale theorem. Development blocks (H=64,128,256,512,1024,2048) were reserved only to verify Wheel's published counts. Held-out blocks were frozen as
[
 H=4096, 8192, 16384.
]

A residue-conditioned probe over moduli (2le dle100), a lag probe over (1leellle100), and maximum internal prefix excursions were designated exceptional-behavior diagnostics. Because the best residue and lag were selected after inspection, those maxima are post hoc and carry a multiple-testing warning.

### D. Exact computation and independent checks

The primary C++ implementation factored each affine progression directly. For every prime (p) up to the square root of the largest affine value, it solved the unique root of each affine form modulo (p), flipped the Möbius sign on that progression, divided out the full (p)-power, and zeroed the unique progression modulo (p^2). Remaining factors larger than the square root were then accounted for exactly. All sums and classifications used integer arithmetic.

The independent implementation used a full linear least-prime-factor Möbius sieve through the largest value needed for (H=4096), then performed direct table lookup at (14+25t) and (5+9t). It shares neither the affine congruence traversal nor the residual-factor logic of the primary method.

Commands:

```text
g++ -Wall -Wextra -Werror -O3 -std=c++17 affine_signed_cell.cpp -o affine_signed_cell
./affine_signed_cell > affine_signed_cell.csv
g++ -Wall -Wextra -Werror -O3 -std=c++17 affine_signed_reference.cpp -o affine_signed_reference
./affine_signed_reference
```

Primary elapsed time was 1.73 seconds; independent reference time was 0.054 seconds. No floating computation controlled membership, Möbius signs, counts, or signed sums. Floating displays occur only in normalized diagnostics.

Artifact hashes:

```text
ab8c8e199ac2e0974be2af138490161960aba678025cadc35c15ceb889c7e0d1  affine_signed_cell.cpp
3e3d1b61bad0d623d402d35da2dbda6e12174ee9fb6b488bbd4d67cc4204323c  affine_signed_reference.cpp
9afde4d2a8770b3dfe024121e518783505fc739f376e0c28bbef99ab407973c6  affine_signed_cell.csv
```

The development counts were exactly
[
 21,81,343,1340,5379,21528,
]
matching Wheel's independently reported values for all six blocks. At (H=4096), the separate linear sieve returned exactly (N_H=86049, S_H=-33), agreeing with the affine implementation.

### E. Held-out results

| (H) | (t)-interval ([L,U)) | (N_H) | (S_H) | (|S_H|/sqrt{N_H}) | (|S_H|/sqrt{N_Hlog H}) | largest internal prefix |
|---:|:---|---:|---:|---:|---:|---:|
| 4096 | [74565, 298262) | 86049 | -33 | 0.1125 | 0.0390 | -383 |
| 8192 | [298262, 1193046) | 344275 | -117 | 0.1994 | 0.0664 | -366 |
| 16384 | [1193046, 4772186) | 1377117 | 225 | 0.1917 | 0.0615 | -1415 |

All three held-out blocks survive the preregistered threshold by factors exceeding 90. The signs reverse across the three blocks, and
[
 |S_H|/N_H=
 0.0003835ldots, 0.0003399ldots, 0.0001634ldots.
]
Thus the exact unsigned saturated cell does not display finite coherent sign accumulation on the frozen blocks.

The internal path is also noncoherent at this scale. The largest absolute prefix excursions divided by (sqrt{N_H}) are approximately (1.31,0.62,1.21).

The strongest post hoc residue z-scores among every residue of every modulus (2le dle100) were (4.41,3.62,3.78). The strongest lag z-scores for (1leellle100) were (2.93,2.54,2.65). These scans select their own maxima and therefore do not establish anomalous arithmetic structure. They do rule out an obvious small-modulus or short-lag explanation for the aggregate cancellation in these blocks.

### F. Mathematical interpretation

The experiment distinguishes two facts that must not be conflated:

- Wheel's theorem shows that the fixed physical cell has (Omega(H^2)) eligible affine parameters in a dyadic (H)-block, hence (Omega(H^2)) unsigned population and (Omega(R)) unsigned mass in some root.
- The genuine signed sum on the same cell is tiny in the three preregistered held-out blocks.

The hidden-variable conclusion is negative but useful: fixed gap (h=1), first owner (r=2), lift primes ({3,5}), and simultaneous squarefreeness do not by themselves create observed sign coherence. Any obstruction must use a subtler arithmetic variable or arise only after aggregation with other cells, root, activation, or boundary terms.

A precise surviving conjecture is
[
 sum_{Tle t<2T}mu(14+25t)mu(5+9t)
   =O_arepsilon(T^{1/2+arepsilon}).
]
A weaker theorem (o(T)) would already prove qualitative cancellation in this saturated cell. Both are `CONJECTURE`; the finite data do not establish either, and the statement is a difficult two-linear-form Möbius correlation rather than a complete CORR4 theorem.

This result does not bound the full
[
 Xi_H=2sum_R N_R-2sum_Rmu(R)W_R+2sum_R W_RK_R.
]
Outer-outer, outer-daughter, same-(q) daughters, every other cross-(q) cell, root, activation, moving cutoff, and cross-shift interactions remain outside this experiment. No global square-shell estimate follows.

### G. Evidence status, proof impact, and continuation

**Evidence status:** `FINITE_COMPUTATION` on three preregistered held-out dyadic blocks, with exact integer reconstruction; `INDEPENDENT_VERIFICATION` of Wheel's six published eligible-population counts and of the first held-out signed result; `FINITE_SURVIVAL` of the preregistered square-root-scale discriminator. The all-scale affine cancellation statement is `CONJECTURE`.

The result retires no signed theorem. It does retire the finite explanation that Wheel's saturated unsigned cell is already a visibly coherent signed obstruction on these scales. Analytically, the first missing lemma remains a uniform signed two-linear-form correlation estimate, followed by aggregation over the complete original cell decomposition without taking absolute values cellwise.

Continuation checkpoint:

1. do not enlarge the same affine table without a new analytic prediction;
2. independently review Wheel's density proof and the exact cell admission before transferring this finite evidence into any paper theorem;
3. derive a source-faithful decomposition of the complete daughter-daughter term by ((h,r,q,p)), then preregister a finite test of how much the ((1,2,3,5)) cell contributes to the *signed* total and to its cross-cell compensation;
4. retain root, activation, outer, and moving-boundary terms before claiming any complete (Xi_H) consequence.

`eta_gate: SEARCH_BROAD`  
`primary_route_and_original_carrier: CORR4 hybrid daughter-daughter fixed shift/owner cell with genuine Möbius products`  
`actual_new_lemma_or_first_unresolved_inequality: finite noncoherence in one saturated exact cell; unresolved uniform signed affine correlation and complete-cell aggregation`  
`independent_reviewer_and_formal_evidence: PENDING; no Lean theorem claimed`  
`net_endpoint_gain_after_complete_return: UNKNOWN`

Complete shell estimate OPEN; strict exponent below (7/8) NOT PROVED; canonical VF theorem OPEN; RH OPEN.


---

## Continuation - claim 20261102-census-2 - 2026-11-02 11:04 EST (-0500)

**Status:** COMPLETED / exact weighted multi-cell census with independent carrier reconstruction.

**Evidence classes:** FINITE_COMPUTATION; INDEPENDENT_VERIFICATION at H=128; PAPER_PROOF for consecutive-cell boundary self-admission; REFUTED for the preregistered exceptional-cell-dominance discriminator; CONJECTURE for diffuse aggregate signed cancellation; NO COMPLETE SOURCE BOUND; NO FIXED ETA GAIN; NO RH.

### H. Fresh authority and task selection

This continuation refreshed live main after the earlier report. Final observed main is 7790fb9f5ddda6eb9823899f2694d691756cd248, the human merge of PR #1070. Open/draft PR search returned none. The authoritative blobs remain:

- AGENTS.md 9fa5e9519e2fb6dde22217aa2a18982dafef373a;
- CURRENT_PROOF_CONTRACT.md 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a;
- selector d05c327ae694ea54b599dab0a21032a056b521f1;
- broad-search policy b5c063c51556ba57c4b25bcc380a606fa8daa207;
- complete-return contract 16838f7f3c8724b970f8b8ece0bceaab9418066d;
- research engine 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55;
- external inbox 038018145c0fddb2f6306c0712373adf9cd1ea52.

The inspected source declarations were original eulerFractionOffQ, blob e6c4b1690e497760d366e36b28a1f7aa60e19f85; the moving physical packet, blob 8084af7fa50fb5b8361a64f05eb658f08b529ca7; the literal FINITE-AC endpoint and legal ancestry sources, blobs 7793d7bfd842348facf62a7ad856bc802ffcd15c and 1270d4d91c53b50b110d10014f223f427fb7a575; and the newly merged lifted-address carrier, blob 61f98a8997d86ddbb07404284d12aebd36a67955.

All 2026-11-02 specialist reports and the complete 2026-11-01 set were consumed. The newest Coordinator assignment explicitly replaced enlargement of the single determinant-one table by a weighted aggregate test over multiple (h,q,p) cells with boundary deletions recorded. This is the selected NEXT-CENSUS continuation. Earlier claim 20261102-census-1 is preserved above unchanged.

The canonical actual-prime VF bound, complete shell-energy gain, every strict Mertens exponent below 7/8, and RH remain open. eta_gate remains SEARCH_BROAD.

### I. Frozen carrier and competing hypotheses

Let P={3,5,7,11}. For H in {128,256,512,1024,2048,4096}, q<p in P and 1<=|h|<=64, define the literal admitted cell

C_H(q,p,h) = {(R,m,n):
  H<=R<2H,
  R^2<=q^2 m<(R+1)^2,
  R^2<=p^2 n<(R+1)^2,
  q^2 m-p^2 n=h,
  mu(m)mu(n) != 0}.

Every occurrence retains its actual daughter-daughter coefficient mu(m)mu(n)/(pq). Put

N_H(q,p,h)=#C_H(q,p,h),
S_H(q,p,h)=sum_C mu(m)mu(n),

A_H=sum N_H(q,p,h)/(pq),
T_H=sum S_H(q,p,h)/(pq),
L_H=sum |S_H(q,p,h)|/(pq).

The 768-cell family, owner weights, shift cutoff, scale sequence and dominance rejection rule were frozen before scanning. The development scale was H=128; H=256 through 4096 were held-out continuations.

Competing explanations were:

1. exceptional-cell dominance: a small resonance set controls aggregate signed behavior;
2. diffuse compensation: many admitted cells contribute and cancel after original weights.

The preregistered exceptional-set falsifier was that the largest ceil(0.01*768)=8 cells account for at least one half of L_H. Failure at every held-out scale rejects this finite version of exceptional-cell dominance. It does not rule out exceptional cells outside the frozen owner/shift window or at other scales.

A second carrier question compared the literal same-shell cells against the simpler broad-address congruence population. Every candidate crossing a square boundary was recorded before applying Mobius zeros. This tests whether broad dyadic address enumeration can silently replace original square-shell admission.

### J. Methods and independent verification

The primary C++ implementation used an exact linear Mobius sieve. For each (q,p,h), it solved

x=0 mod q^2,  x=h mod p^2

by CRT, traversed the resulting single progression modulo q^2 p^2 in [H^2,4H^2), set y=x-h, and then applied exact integer square roots, same-shell admission, and mu(x/q^2)mu(y/p^2). All classifications and weighted totals were integers. Since every pq divides 1155, the program stored A_H, T_H, L_H and the boundary correction as exact integer numerators over 1155.

The independent Python reference reconstructed every admitted daughter occurrence separately in each shell, grouped it by owner, and nested the actual q/p occurrence lists before selecting |h|<=64. It uses an Eratosthenes-style prime toggle/square-zero Mobius sieve rather than the primary linear sieve and does not use CRT. At H=128 it agreed cell-by-cell on all 708 nonempty cells, 19,533 eligible occurrences, and every signed sum. Mismatches: zero.

Final warning-fatal command sequence:

    g++ -Wall -Wextra -Werror -O3 -std=c++17 aggregate_affine_cells.cpp -o aggregate_affine_cells
    ./aggregate_affine_cells H
    python aggregate_affine_reference.py 128

The final compile, six primary scales, and reference run completed in approximately 2.3 seconds wall time in the execution wrapper. Environment: Linux 6.18.57 x86_64, g++ 13.3.0, Python 3.12.14. No random seed or floating value controlled a membership, sign, total, or verdict. The displayed top-share decimal is computed from exact integers.

Artifact hashes:

    2614256a585b81d9ebbd6da32a35acb15fcb462bf55332f20e353e97938d6f29  aggregate_affine_cells.cpp
    88c6c02d74571b47265549123b652555fd6f3ecaf42e6486d6da85573647ae38  aggregate_affine_reference.py
    097616ae3b7e6c1fb6679d8b9b88075df6804217443149db2c99b687c0c2ee75  aggregate_128.txt
    0c64c2d61e61b39b908cfa914891f41ca8559e820c5471dfe064f4e559c5b3c7  aggregate_256.txt
    194333cc4dc4eeb1aceaef0f145cae532de348fc83c694af894e858285ec08b7  aggregate_512.txt
    b226a45062386bc69dd0d66fddde5c544fbceffdfe952155b76368b63a1a7290  aggregate_1024.txt
    9d0126f3dc01a299497b4747c8544a5baa7356e204f338b43c88eb1cdfd491c1  aggregate_2048.txt
    6dc31a8f531dd8adea452376a4d6eebae60d3315be5f27adb899dcdfa066088c  aggregate_4096.txt

### K. Exact results

The numerators in the next table have common denominator 1155.

| H | admitted occurrences | A_H numerator | T_H numerator | L_H numerator | top 8 share of L_H |
|---:|---:|---:|---:|---:|---:|
| 128 | 19,533 | 1,168,621 | 11,597 | 128,901 | 0.088665 |
| 256 | 81,245 | 4,863,275 | 4,385 | 274,081 | 0.092148 |
| 512 | 331,740 | 19,853,822 | -43,980 | 513,768 | 0.100115 |
| 1024 | 1,339,508 | 80,181,048 | -154,110 | 1,045,096 | 0.092613 |
| 2048 | 5,384,068 | 322,289,516 | -403,864 | 2,270,668 | 0.107972 |
| 4096 | 21,586,536 | 1,292,201,162 | 39,670 | 4,125,662 | 0.097219 |

Thus the top 1% contribution is always below 10.8%, far below the frozen 50% dominance threshold. The aggregate signed total changes sign twice. Its ratio |T_H|/L_H is respectively 0.0900, 0.0160, 0.0856, 0.1475, 0.1779 and 0.00962. At H=4096 cross-cell compensation reduces the cellwise signed L1 mass by a factor greater than 100.

The smallest-owner pair (q,p)=(3,5) contributes between 46.5% and 52.7% of L_H across these scales. This is substantial but consistent with its much larger population and weight; it is not a stable small-cell concentration. At H=4096 the eight largest individual cells are all (3,5) cells, but together they still contribute only 9.72% of L_H.

The boundary audit is also exact:

| H | raw boundary crossings | squarefree crossings deleted | weighted signed deletion numerator / 1155 |
|---:|---:|---:|---:|
| 128 | 4,834 | 1,560 | -2,358 / 1155 |
| 256 | 9,748 | 3,189 | -1,191 / 1155 |
| 512 | 19,443 | 6,421 | -10,065 / 1155 |
| 1024 | 38,975 | 12,843 | 10,679 / 1155 |
| 2048 | 77,879 | 25,630 | 2,644 / 1155 |
| 4096 | 156,010 | 51,436 | 15,542 / 1155 |

Therefore broad-address congruence enumeration is not exactly the original same-shell carrier for general |h|<=64. The signed correction is nonzero and changes sign. It must be retained in a complete theorem even though its observed size is lower order in this fixed-shift experiment.

### L. New exact invariant: consecutive cells self-enforce shell admission

The determinant-one cell from claim 20261102-census-1 is exceptional in a useful exact way.

Suppose q^2 m-p^2 n=1, both physical addresses lie in [H^2,4H^2), and q^2<R at the candidate root scale. If the consecutive integers q^2m and p^2n lie in different square shells, the larger integer q^2m is a perfect square, say s^2. Since q is prime and q^2 divides s^2, q divides s, so m=(s/q)^2. The activation condition q^2<R together with q^2m>=R^2 excludes m=1. Hence m has a nontrivial square factor and mu(m)=0, contradicting eligibility. The h=-1 case is symmetric with n.

Consequently every nonzero-Mobius h=+/-1 cross-lift candidate is automatically same-shell admitted. The primary data independently show zero squarefree boundary deletion in the (3,5,1) cell at every tested H. In particular the earlier counts

    81, 343, 1340, 5379, 21528, 86049

at H=128 through 4096 are literal admitted counts, despite the earlier report's simplified interval definition omitting the redundant same-shell predicate. This is PAPER_PROOF, not merely a finite observation. It is a source-faithful structural lemma, but it supplies no cancellation.

### M. Interpretation and proof impact

The finite exceptional-cell-dominance mechanism is refuted on the frozen family and scales. Cancellation is genuinely visible only after summing many signed cells with their physical 1/(pq) weights. This strengthens the Coordinator's reason to seek an aggregate shifted-Elliott theorem rather than 768 separate absolute or fixed-cell estimates.

The boundary result cuts both ways:

- general fixed shifts require an explicit square-shell boundary term; approximately one third of raw boundary crossings survive squarefreeness in this experiment;
- consecutive h=+/-1 cells have an exact Mobius-zero self-admission law, so they are unusually clean analytic test cells.

A precise theorem candidate suggested by the computation is a joint, not cellwise, estimate for the frozen owner family:

    sum_{q<p in P} (1/(pq))
      sum_{1<=|h|<=64} S_H(q,p,h)
      = O_epsilon(H^(1+epsilon)).

Status: CONJECTURE. The tested values are compatible with this scale, but the family has fixed owners and shifts and is only a partial daughter-daughter source. Even proving it would not control growing owners, all physical shifts, outer sectors, root, activation or moving-boundary terms. It is not a complete CORR4 estimate and yields no endpoint exponent by itself.

The first missing analytic statement remains a power-rate aggregate correlation over the full moving (q,p,h) family with original masks and weights, followed by exact restoration or absorption of outer, root and activation terms. Componentwise absolute bounds remain power-sharp.

### N. Evidence status and continuation checkpoint

**Evidence status:** FINITE_COMPUTATION for the six exact weighted 768-cell censuses; INDEPENDENT_VERIFICATION at H=128; REFUTED for the stated finite top-1%-dominance discriminator; PAPER_PROOF for h=+/-1 boundary self-admission; CONJECTURE for aggregate H^(1+epsilon) cancellation. No complete source estimate is proved.

Continuation:

1. do not enlarge the fixed h=+/-1 determinant-one table;
2. send the consecutive-cell boundary lemma and the general nonzero boundary correction to independent Referee review;
3. derive the complete finite identity separating admitted aggregate, square-boundary deletion, and the remaining shifts when |h| grows with R;
4. in a future Census run, use a new analytic prediction to freeze a growing-shift window or test a full Xi_H reconstruction including outer, root and activation terms;
5. retain the exact hashes above; the local artifacts are reproducibility evidence, not repository proof authority.

eta_gate: SEARCH_BROAD  
primary_route_and_original_carrier: CORR4 literal cross-lift daughter cells on merged liftedMobiusDaughterCarrier with 1/(pq) weights and same-shell masks  
actual_new_lemma_or_first_unresolved_inequality: consecutive h=+/-1 boundary self-admission; finite refutation of small exceptional-cell dominance; open full moving-family signed aggregate estimate  
independent_reviewer_and_formal_evidence: PENDING for the new lemma; merged #1070 proves only address injectivity/disjointness  
net_endpoint_gain_after_complete_return: UNKNOWN

Complete shell estimate OPEN; strict exponent below 7/8 NOT PROVED; canonical VF theorem OPEN; RH OPEN.


---

## Scheduled continuation - claim \`20261102-census-3\` - 2026-11-02 19:06 EST (-0500)

**Status:** COMPLETED / exact FINITE-AC square-block inverse census with two independent reconstructions.  
**Evidence classes:** \`FINITE_COMPUTATION\`; \`REFUTED ON FROZEN SAMPLE / SQRT-BURST\`; \`FINITE_SURVIVAL / 1.06-SQRT BURST\`; \`CONJECTURE / SQUARE-ROOT-TIME INVERSE\`; \`NO COMPLETE SOURCE BOUND\`; \`NO FIXED ETA GAIN\`; \`NO RH\`.

### O. Authority, continuity, and selected task

This run began from live \`main@8e5d64ae689b39dabd2a4f6eb33efe4d5d192015\`, the human merge of PR #1072. Retrieval and exact computation occurred 2026-11-02 19:00-19:06 EST on Linux 6.18.57 x86_64, g++ 13.3.0, and Python 3.12.14.

Live authority and source provenance:

- \`AGENTS.md\`: blob \`9fa5e9519e2fb6dde22217aa2a18982dafef373a\`;
- \`CURRENT_PROOF_CONTRACT.md\`: blob \`88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a\`;
- selector: \`d05c327ae694ea54b599dab0a21032a056b521f1\`;
- breadth policy: \`b5c063c51556ba57c4b25bcc380a606fa8daa207\`;
- complete-return contract: \`16838f7f3c8724b970f8b8ece0bceaab9418066d\`;
- research engine and exact NEXT-CENSUS ticket: \`6fce99c61efb5b2a73c0cb1f1464f09b351fcd55\`;
- literal historical envelope: \`RHLean/Proof/SquareRootLegalAncestryGramReduction.lean\`, blob \`1270d4d91c53b50b110d10014f223f427fb7a575\`;
- endpoint amplification statement: \`RHLean/Proof/SquareRootMertensEndpointAmplification.lean\`, blob \`7793d7bfd842348facf62a7ad856bc802ffcd15c\`;
- original double Mobius floor source: \`research/EULER_HYBRID_ABEL_GRAM_20261027.lean\`, blob \`2a94dd8fd56fc03e95f732fb44b778a8d4f83e26\`;
- exact floor-to-endpoint bridge: \`research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean\`, blob \`e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73\`.

The complete 2026-11-02 reports were consumed at blobs Coordinator \`1f8b6897897fc6e8d76fdc9a541bebea68ef52fc\`, Owner \`abfe546d72b151f4cd200fc61de3197efe23a65c\`, Analytic \`8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73\`, Wheel \`abf8ac8c22a708886183849552c90dd62787ac8d\`, prior Census \`6e8070f78688c63824ed6586dc8bad78f04f1f11\`, Referee \`73a4e272393964d06a3fced63a1eea546ac9dd8d\`, and Lean \`f4616a722c6a2b79e253207ab2352a66751f4624\`. The relevant 2026-11-01 carry-forward set was also consumed, including Coordinator \`8f661bc144fd96ffd7a9a8cd084e74e3df05d1a8\`, Owner \`40ad74dd7378834a48203153afc30618233f4b04\`, prior Census \`8724bbebf07365ffc5364b411caea7c6d804d468\`, Referee \`fbf6dfc995e7d38b1ec07754e4d368a91112ecec\`, and Lean \`6aa7197c4169a70debed607e12f4639218cd21b6\`. External handoffs remain unchanged after 2026-10-18.

Draft PR #1073 is the sole open PR at intake, based on this main. It proposes a strict finite-slot gain but explicitly labels its terminal chain unverified. It is \`CANDIDATE_ETA / DRAFT / NOT CONSUMED AS A THEOREM\`. The live gate remains \`SEARCH_BROAD\`.

The earlier affine-cell assignments were completed by claims \`20261102-census-1,2\`; enlarging those scans was therefore rejected. This continuation resumes the still-live FINITE-AC square-block inverse from \`20261101-census-1\` and Coordinator's reserve mechanism: determine whether large literal normalized \(Q_R\) excursions are fresh square-time bursts or inherited cumulative drift while the historical envelope remains anchored.

### P. Frozen carrier, competing hypotheses, and rejection rule

For \(R\ge2\), use the exact original carrier

\[
 X_R=R^2-1,\qquad
 Q_R=\sum_{1\le a,b<R}\mu(a)\mu(b)\left\lfloor{X_R\over ab}\right\rfloor
     =2M(R-1)-M(X_R),
\]

and the least historical envelope

\[
 K_R=\max_{0\le y<R}{(M(y)-1)^2\over y+1}.
\]

Rank roots by the exact rational statistic

\[
 C_R^2={Q_R^2\over R^2K_R}.
\]

The holdout \(16001\le R\le20000\) and the top-eight rule were frozen in the previous report, before this run. For each selected root define \(L_R\) to be the least positive integer \(L\) such that

\[
 \Delta_L(R)=M(R^2-1)-M((R-L)^2-1)
\]

has the sign of \(M(R^2-1)\) and satisfies
\[
 2|\Delta_L(R)|\ge |M(R^2-1)|.
\]

The finite operational hypothesis was preregistered before scanning:

\[
 \texttt{SQRT-BURST}:\qquad L_R\le\lfloor\sqrt R\rfloor
\]

for every one of the frozen top eight. One legal failure rejects it. The rival cumulative mechanism predicts a stopping length visibly proportional to \(R\), rather than square-root sized. Observations between these two regimes were permitted to reveal a third mechanism.

### Q. Exact methods and independent checks

The primary C++ program performed a segmented exact factorization through \(20000^2-1=399999999\). Within each block it divided every integer by each prime factor, flipped parity once per distinct prime, and set the Mobius coefficient to zero on repeated prime factors. It accumulated \(M(n)\) exactly, recorded every \(M(R^2-1)\), formed \(K_R\) by exact rational comparison, selected the top eight by cross multiplication in signed 128-bit integers, and located each \(L_R\) by exact integer inequalities.

A structurally independent reference used the quotient-grouped identity

\[
 M(n)=1-\sum_{l=2}^{n}(r-l+1)M(\lfloor n/l\rfloor),
 \qquad r=\left\lfloor {n\over\lfloor n/l\rfloor}\right\rfloor,
\]

with an independent linear Mobius prefix only through \(5\,000\,000\) and memoization above that threshold. It recomputed every selected endpoint and every candidate stopping point without using the segmented table. Agreement was exact on all displayed fields.

A third source check used an independent linear Mobius sieve and directly evaluated the original double floor sum at \(R=5,53,317,1027\). It agreed with \(2M(R-1)-M(R^2-1)\) exactly:

| \(R\) | \(M(R-1)\) | \(M(R^2-1)\) | endpoint \(Q_R\) | direct floor sum |
|---:|---:|---:|---:|---:|
| 5 | -1 | -2 | 0 | 0 |
| 53 | -2 | -24 | 20 | 20 |
| 317 | -3 | -28 | 22 | 22 |
| 1027 | -4 | 367 | -375 | -375 |

Warning-fatal commands:

\`\`\`text
g++ -Wall -Wextra -Werror -O3 -std=c++17 finite_ac_burst_census.cpp -o finite_ac_burst_census
./finite_ac_burst_census 16001 20000 8
g++ -Wall -Wextra -Werror -O3 -std=c++17 mertens_dujiao_reference.cpp -o mertens_dujiao_reference
./mertens_dujiao_reference
\`\`\`

Elapsed times were 7.69 seconds for the complete primary census and 0.62 seconds for the independent selected-root reference. No floating value controlled membership, ranking, signs, stopping lengths, or verdicts. Decimals below are displays of exact integers/rationals.

Artifact hashes:

\`\`\`text
6a7bd21f3fabb16e9de1609bf8be887ec10c671359aca2657113be6d840fa70b  finite_ac_burst_census.cpp
17f9084464dd1e19aca9efdb56f46b529ad29f45d0829f21929a46c5af394c76  finite_ac_burst_results.csv
155bb39d811f686f5718c06b32c6d161a08dacd31214748679abe4b0241a9d86  mertens_dujiao_reference.cpp
7929c9d66fba63bbebb7732d2f0f59f66fa51858de89910c999ef1bef8463b06  mertens_dujiao_results.csv
\`\`\`

### R. Exact held-out results and falsifier

At every selected root, \(K_R=9/6=3/2\), with least maximizer \(y=5\). Thus none is a new historical-envelope corner.

| \(R\) | \(M(R-1)\) | \(M(R^2-1)\) | \(Q_R\) | \(C_R^2\) | \(L_R\) | \(L_R/\sqrt R\) | \(L_R/R\) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 18993 | 39 | 6602 | -6524 | 0.0786592 | 140 | 1.01585 | 0.007371 |
| 18994 | 38 | 6570 | -6494 | 0.0779292 | 141 | 1.02308 | 0.007423 |
| 18986 | 37 | 6413 | -6339 | 0.0743162 | 135 | 0.97975 | 0.007111 |
| 18987 | 36 | 6351 | -6279 | 0.0729083 | 136 | 0.98699 | 0.007163 |
| 18989 | 37 | 6303 | -6229 | 0.0717367 | 139 | 1.00870 | 0.007320 |
| 18992 | 39 | 6304 | -6226 | 0.0716449 | 142 | 1.03039 | 0.007477 |
| 18988 | 37 | 6296 | -6222 | 0.0715831 | 138 | 1.00147 | 0.007268 |
| 18996 | 38 | 6240 | -6164 | 0.0701956 | 146 | 1.05931 | 0.007686 |

\`SQRT-BURST\` is refuted on the frozen sample. The smallest selected failing root is \(R=18988\): \(\lfloor\sqrt{18988}\rfloor=137\), but \(L_R=138\). Six of eight selected roots fail the literal cutoff.

The failure is narrow and discriminating. All eight roots lie in one excursion cluster, every \(L_R\) lies in
\[
 0.9797\sqrt R\le L_R\le1.0594\sqrt R,
\]
and every \(L_R/R<0.0077\). Thus the rival proportional-to-\(R\) cumulative mechanism is not visible either. The data expose a third finite pattern: a square-root-time burst sitting on an ancient, unchanged historical envelope.

The root-prefix correction is also small: \(2|M(R-1)|/|Q_R|<0.0127\) throughout the sample, and \(\operatorname{sign}(Q_R)=-\operatorname{sign}(M(R^2-1))\). These are exact finite observations, not an all-scale inverse theorem.

### S. Interpretation, conjecture, and proof impact

The precise failed inference is now stronger than the earlier fresh-corner no-go: a high normalized literal \(Q_R\) excursion need not renew \(K_R\), and even its least half-amplitude square-block history need not fit inside one literal \(\sqrt R\) window. However, the observed stopping length remains remarkably close to \(\sqrt R\), not proportional to \(R\).

Exploratory theorem candidate:

> **SQUARE-ROOT-TIME INVERSE.** There exist universal constants \(C,R_0\) such that every sufficiently large root satisfying a fixed high-\(C_R\) threshold and \(K_R=3/2\) has \(L_R\le C\sqrt R\).

Status: \`CONJECTURE\`. The finite sample only shows survival with \(C=1.06\) on one selected cluster. The threshold must be fixed independently, and \(K_R=3/2\) is not known for all scales. No optimal constant is inferred.

Even such an inverse statement would not prove finite A/C. The next missing theorem would have to control the number or total energy of square-root-length coherent Mobius square-block bursts strongly enough to bound the complete literal \(Q_R\) source. A location theorem without an energy/frequency restriction merely relocates the endpoint bill.

Draft PR #1073 is not changed by this result. Its proposed finite-slot gain lies on a different native analytic carrier and remains unverified. This census neither supports nor refutes its complete-return argument.

### T. Evidence status and continuation checkpoint

**Evidence status:** \`FINITE_COMPUTATION\` on every root \(16001\le R\le20000\), with exact rational ranking and two independent selected-root reconstructions; \`REFUTED ON FROZEN SAMPLE\` for \`SQRT-BURST\`; \`FINITE_SURVIVAL\` for the post hoc \(1.06\sqrt R\) envelope on the selected cluster; \`CONJECTURE\` for any all-scale square-root-time inverse. No complete source estimate is proved.

Continuation:

1. freeze this top-eight sample and do not tune the constant against it;
2. ask Wheel/Referee to derive and audit the exact relation between \(L_R\), the block increments \(Q_t-Q_{t-1}=2\mu(t-1)-[M(t^2-1)-M((t-1)^2-1)]\), and any candidate burst-energy inequality;
3. test the fixed constant and a fixed \(C_R\) threshold only on a new disjoint range if that analytic inequality identifies a genuine consequence;
4. preserve the \(R=53,317,1027\) direct-source regressions and the \(R=18988\) cutoff falsifier;
5. do not infer finite A/C, a strict exponent below \(7/8\), or complete-return gain from the finite square-root scale.

\`eta_gate: SEARCH_BROAD\`  
\`primary_route_and_original_carrier: FINITE-AC / literal Euler self-dual Q_R, least historical K_R, and genuine square-block Mertens increments\`  
\`actual_new_lemma_or_first_unresolved_inequality: finite sqrt-cutoff falsifier at R=18988; unresolved square-root-time burst frequency/energy theorem\`  
\`independent_reviewer_and_formal_evidence: PENDING; exact computations only, no Lean theorem\`  
\`net_endpoint_gain_after_complete_return: UNKNOWN\`

Complete shell estimate OPEN; strict exponent below \(7/8\) NOT PROVED; finite A/C OPEN; canonical VF theorem OPEN; RH OPEN.
