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
