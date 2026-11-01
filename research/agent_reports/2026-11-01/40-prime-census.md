# RH_Lean agent daily report - 2026-11-01 / RH | Prime Census Laboratory

## Scheduled invocation checkpoint - 2026-11-01 03:15 EST (-0500)

**Status:** IN_PROGRESS / exact computation and independent reconstruction completed; final synthesis and publication readback pending.  
**Run ID:** `20261101-census-1`.  
**Deployment ack:** first actual Prime Census consumption of the seven-agent research engine at `main@5b232a4fa633fad5e73a9b7ebfb76572ecb1dbb0`; selected `NEXT-CENSUS: FINITE-AC discriminator, not a larger scan` from policy blob `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.

### A. Authority and continuity

Repository retrieval began 2026-11-01 03:11 EST. Live authority was:

- `AGENTS.md` blob `9fa5e9519e2fb6dde22217aa2a18982dafef373a`;
- `CURRENT_PROOF_CONTRACT.md` blob `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`;
- task selector blob `d05c327ae694ea54b599dab0a21032a056b521f1`;
- broad-search policy blob `b5c063c51556ba57c4b25bcc380a606fa8daa207`;
- complete-return contract blob `16838f7f3c8724b970f8b8ece0bceaab9418066d`;
- research-engine blob `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.

There were no open/draft PRs in the refreshed query. Today's Coordinator, Census, Referee and Lean reports were `TODAY=PENDING`; today's Owner blob `4604617532db0ab8b1e5d5da495f2e698e1aa575`, Analytic blob `411159fdab234c02f66df812c2eae2ef17487ace`, and Wheel blob `38d69518d7e30769798637920cfcaecaa4e09c2a` were consumed. Yesterday's complete Coordinator/Census/Referee findings were carried forward from blobs `6af6829827ecff25bac0dc2728f56a2a3eca049e`, `46f6923fa188e5ed6036d6097b23360c32088fc0`, and `0d923f611ab8cb00f83f0dbd34605f447855c838`. External handoffs blob: `038018145c0fddb2f6306c0712373adf9cd1ea52`.

The eta gate remains `SEARCH_BROAD`. Finite A/C, the canonical VF estimate, a strict exponent below `7/8`, and RH remain open.

### B. Frozen carrier and preregistered discriminator

The literal FINITE-AC carrier is

```
X_R = R^2 - 1,
Q_R = sum_{1<=a,b<R} mu(a)mu(b) floor(X_R/(ab))
    = 2M(R-1) - M(X_R),
K_R = max_{0<=y<R} (M(y)-1)^2/(y+1).
```

The original Lean sources inspected were `SquareRootMertensEndpointAmplification.lean` blob `7793d7bfd842348facf62a7ad856bc802ffcd15c` and `SquareRootLegalAncestryGramReduction.lean` blob `1270d4d91c53b50b110d10014f223f427fb7a575`. The exact self-dual endpoint source was checked in blob `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73`. No VF quantity or surrogate denominator is substituted.

Before examining the new census, the following inverse hypothesis was frozen for `R>=31`. Let `y*_R` be the least index attaining `K_R` and

```
C_R^2 = Q_R^2/(R^2 K_R).
```

`CORNER-LOCK(3/10)`: if `C_R^2 >= 9/100`, then `2y*_R >= R`.

Competing explanations were: (H1) high normalized amplification requires a fresh historical-envelope corner; (H2) it is driven by the square-endpoint Mertens excursion while the historical normalizer stays fixed at a tiny old index. Exact rejection required one root with

```
100 Q_R^2 den(K_R) >= 9 R^2 num(K_R),  and  2y*_R < R.
```

Reference/training range was `31..6000`, matching the prior census horizon; the disjoint holdout was frozen as `6001..12000`. Required anchors `317,1027`, near-record/boundary roots, and the smallest violation were retained.

### C. Checkpoint result

`CORNER-LOCK(3/10)` is refuted. The smallest violation in the admissible range is `R=53`:

```
M(52)=-2, M(2808)=-24, Q_53=20,
K_53=9/6=3/2 attained first at y*=5,
C_53^2=800/8427 > 9/100, while 2y*=10<53.
```

The exact positive rejection margin is `100*800 - 9*8427 = 4157`.

The stronger finite observation is that the historical maximizer is frozen at `y*=5`, `K_R=3/2`, for every `6<=R<=12000`. Thus every one of the 94 threshold exceedances in `31..6000` and every one of the 62 exceedances in the held-out `6001..12000` range violates the proposed fresh-corner condition. This agrees with, and extends for the present discriminator, earlier repository warnings that the empirical lower envelope is governed by the small-`y` value `3/2`; it is not promoted as a new all-scale fact.

Final methods, cross-checks, exceptional clusters, scope, proof impact and continuation capsule will be appended after this checkpoint's commit/readback.

## Final synthesis - claim `20261101-census-1` - 2026-11-01 03:16 EST (-0500)

**Status:** COMPLETED.  
**Evidence classes:** `REFUTED / CORNER-LOCK(3/10)`; `FINITE_COMPUTATION / EXACT INTEGER-RATIONAL CENSUS`; `FINITE_COMPUTATION / INDEPENDENT LITERAL FLOOR RECONSTRUCTION`; `CONJECTURE / ENDPOINT-DOMINANCE INVERSE CLASS`; `NO COMPLETE SOURCE BOUND`; `NO FIXED ETA GAIN`; `NO RH`.

### D. Methods and validation

Implementation 1 is a segmented exact Mobius sieve through `12000^2-1=143999999`. It maintains integer Mertens prefixes, records every square endpoint, and compares envelope and threshold ratios by cross multiplication in signed 128-bit integers. No decimal value controls a classification. Command:

```
g++ -Wall -Wextra -Werror -O3 -std=c++17 finite_ac_corner_census.cpp -o finite_ac_corner_census
./finite_ac_corner_census 12000 > finite_ac_corner_12000.csv
```

Implementation 2 uses an independent linear Mobius sieve only below each root and evaluates the literal original source by the nested floor sum over all `a,b<R`. It reconstructed all 163 threshold-exceeding roots in `2..12000`, not only selected favorable cases. Every value agreed with Implementation 1's endpoint expression; mismatches: zero. Command form:

```
./finite_ac_floor_reconstruct R_1 ... R_163
```

Small fixtures exposed and corrected a snapshot-order defect at `R=6` before the final run: the strict envelope includes `y=5` when `R=6`. The entire census was rerun after correction. Warning-fatal compilation passed. Runtime for the corrected segmented census was about 4.0 seconds; the 163 direct floor reconstructions took about 5.7 seconds. Environment: `g++ 13.3.0`, Python `3.12.14`, Linux x86_64. No random seed or approximate arithmetic was used.

Artifact hashes:

```
a2136b27dc18e11b579112ad3f4ebad81dd295cb4450aa4fd251f3092d7ebb23  finite_ac_corner_census.cpp
0212b0550482d3af675fdcfe6cd6667f2761f32ac853cdccede665cf6c4567c4  finite_ac_floor_reconstruct.cpp
9934e2a51fd3133690c3d7d47864f2bc5ec49e8708f699bc2e5609c3a5361adc  finite_ac_corner_12000.csv
1066093d075314554c64d2b5e0fb0ad5bc73de964ac9a004692740fc06359c49  finite_ac_floor_high.txt
```

These local artifacts are reproducibility evidence for this run; they are not committed mathematical authority.

### E. Exact results and exceptional behavior

The required anchors and principal extrema are:

| `R` | `M(R-1)` | `M(R^2-1)` | `Q_R` | `C_R^2` | `C_R` diagnostic |
|---:|---:|---:|---:|---:|---:|
| 53 | -2 | -24 | 20 | `800/8427` | 0.3081119173 |
| 317 | -3 | -28 | 22 | `968/301467` | 0.0566653779 |
| 1027 | -4 | 367 | -375 | `93750/1054729` | 0.2981365315 |
| 5561 | 5 | -2544 | 2554 | `13045832/92774163` | 0.3749923157 |
| 6074 | -1 | 2256 | -2258 | `2549282/27670107` | 0.3035313269 |
| 8719 | 19 | -3402 | 3440 | `23667200/228062883` | 0.3221410986 |
| 10493 | -22 | -4601 | 4557 | `282534/2247001` | 0.3545959134 |

`R=5561` remains the maximum on `31..6000`. The held-out maximum is `R=10493`. The 62 held-out exceedances occur in twelve short clusters:

```
6074-6080, 6105-6112, 8717-8719, 8722, 8725, 8730,
10481-10497, 10514, 10516-10531, 10539-10541, 10543-10545, 10547.
```

At all 62 held-out exceedances, `sign(Q_R)=-sign(M(R^2-1))`; the root-prefix correction has

```
max |2M(R-1)|/|Q_R| = 56/3879
```

at `R=10541`, below 1.5 percent. Across all 156 exceedances in `31..12000`, the same sign relation holds; the largest correction ratio is `1/5`, at the smallest counterexample `R=53`. Thus the observed high statistic is a clustered square-endpoint excursion with a small root-prefix correction, while the denominator is the same ancient `y=5` envelope throughout. This supports H2 and rejects H1 on the exact tested domain.

### F. Mathematical scope and conjecture

The finite theorem established by computation is only:

```
for every integer 6<=R<=12000,
K_R=3/2 with least maximizer y*=5;
and for every 31<=R<=12000 with C_R^2>=9/100,
CORNER-LOCK(3/10) fails.
```

It does not imply that `K_R=3/2` forever, that `C_R` is uniformly bounded, or that finite A/C holds. The small-`y` `3/2` phenomenon was already visible in repository diagnostics; the new result is the preregistered falsification and held-out inverse classification, not rediscovery of the constant.

Exploratory replacement conjecture, frozen only for future falsification:

`ENDPOINT-DOMINANCE(3/10)`: beyond a specified onset, whenever `K_R=3/2` and `C_R^2>=9/100`, `sign(Q_R)=-sign(M(R^2-1))` and `|2M(R-1)|<=|Q_R|/50`.

This survives `6001..12000` but is only `CONJECTURE`. Its stated `1/50` correction is much stronger than the immediate historical-envelope inequality and may itself require difficult Mertens information. It is not proposed as an accepted proof route without an analytic premise.

### G. Proof impact and cross-route audit

The failed inference is precise: large finite-C normalization cannot be forced to coincide with renewal of the historical envelope, even at the first nontrivial threshold. A proof based on paying `Q_R` only when `K_R` acquires a recent maximizer misses every observed large event after `R=31`. The strict historical normalizer is not a dynamic detector in this range.

This does not alter Wheel claim `20261101-wheel-1`, Owner claims `20261101-owner-1,2`, or Analytic claim `20261101-analytic-1`; none supplies a uniform original-source `Q_R` estimate. It also does not transfer to CORR4 merely because both use `K_R`. The useful restriction for FINITE-AC must address the signed endpoint source or a complete decomposition of its clustered square-block excursions, rather than a fresh-corner condition.

### H. Continuation checkpoint

Do not enlarge this aggregate scan without a new premise. The next discriminating experiment should resolve the clusters by genuine square-block increments. For each high root define the least backward block length `L_R` for which the signed increment

```
M(R^2-1) - M((R-L_R)^2-1)
```

has the endpoint sign and magnitude at least `|M(R^2-1)|/2`. Preregister rival mechanisms: a short recent burst (`L_R=o(R)` on exceptional roots) versus inherited cumulative coherence (`L_R` proportional to `R`). Reconstruct the complete block increments exactly and test the fixed rule first on the twelve held-out clusters above, then on a new disjoint range. A theorem-level consequence would require an independent uniform bound on the frequency or total energy of short coherent runs; finite concentration alone is not a source estimate.

**Evidence status:** `REFUTED` for `CORNER-LOCK(3/10)` by the exact smallest admissible witness `R=53`; `FINITE_COMPUTATION` for every root `2..12000` and independent direct-floor reconstruction of every threshold exceedance. Complete finite C/A, a strict Mertens exponent below `7/8`, canonical VF, and RH remain OPEN.
