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


## Scheduled continuation - claim `20261101-census-2` - 2026-11-01 11:04 EST (-0500)

**Status:** COMPLETED / exact mixed-owner census and held-out falsification.  
**Live main:** `417cb62ee8ca65c82dd3aad1263c7529e94668eb`.  
**Evidence classes:** `REFUTED / MIXED-OWNER-3/4`; `REFUTED ON TESTED SET / UNIVERSAL COMPENSATING SIGN`; `FINITE_COMPUTATION / EXACT RATIONAL THROUGH R=3304`; `FINITE_COMPUTATION / FLOAT DIAGNOSTIC AT R=5561,6074`; `CONJECTURE / POST HOC OWNER-SHELL`; `NO COMPLETE SOURCE BOUND`; `NO FIXED ETA GAIN`; `NO RH`.

### I. Authority, continuity, and selected handoff

This continuation consumed the current completed 2026-11-01 reports at blobs Coordinator `c23d71084b9103d22e0ade268535dbcab18fc229`, Owner `d57ca6c383884e0b2b9ef38809d589b60b355a42`, Analytic `97ebebec389bdafaa6c8e49afdde1b06f682779e`, Wheel `3c9752a5a580bcce27ca0af4b3281c1fbdac4dd8`, this report `fca27fe912377722ad6acaaf193b4841284b67fb`, Referee `01f2f9b84e28e985eef5a168bb86b944cca7924a`, and Lean `a43d35c4534d3c1473e3fe9f910b481ec96e3429`. The full 2026-10-31 carry-forward set was also retrieved; external handoffs remain blob `038018145c0fddb2f6306c0712373adf9cd1ea52` with no entry newer than October 18. Open/draft PR refresh returned none.

The earlier `NEXT-CENSUS` FINITE-AC ticket was completed by claim `20261101-census-1`. Wheel claim `20261101-wheel-2` then proved the exact half-amplitude inverse and refuted square-root spreading at `R=53`. The newest Coordinator assignment was therefore selected: test claim `20261101-coordinator-1` on the literal mixed common-clock owner fibres, including the diagonal and the adverse `R=2002` regression.

Material main blobs were:

- `GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean` `f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8`;
- `GLOBAL_RETURNED_CORE_Q2_DAUGHTER_FIRST_OWNER_GRAM.lean` `b57a3e9030445262ec847ca0e20a60bc35ff127c`;
- `CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026.lean` `a4abeb13653076bedd8e1173c933ee3324bfea26`;
- `LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT.lean` `72d66f61b3eeb000117ecdac393572558bb7c378`;
- `EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean` `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73`.

### J. Frozen carrier and preregistered hypotheses

Put `X=R^2-1`,
```text
G_R = M(X) - M(R-1),
U_R = sum_(q odd prime, q^2<R) M(floor(X/q^2)) / q.
```
For `1<=n<=X`, put
```text
h_R(n) = 1 if n>=R, otherwise 0,
W_R(n) = sum_(q^2<R) 1_(n<=floor(X/q^2)) / q.
```
For squarefree `m<n`, the chronological owner `p(m,n)` is the least prime in the symmetric difference of their complete prime-factor sets, exactly the repository predicate `IsSquarefreePairFreshPrimeOwner`. Define
```text
J_R(p) = sum_(m<n, p(m,n)=p)
  [h_R(m) W_R(n) + h_R(n) W_R(m)] mu(m) mu(n).
```
The exact reconstruction target was
```text
G_R U_R = D_R + sum_p J_R(p),
D_R = sum_n h_R(n) W_R(n) mu(n)^2.  (20)
```

Before computing, two exploratory assertions were frozen.

1. `MIXED-OWNER-3/4`: owners `p<=floor(sqrt R)` carry at least three quarters of `sum_p |J_R(p)|`, and their signed sum has the sign of the complete off-diagonal.
2. `MIXED-COMP-SIGN`: `G_R U_R<=0`.

The mechanism hypothesis was that the same small primes indexing the q-squared column organize the mixed compensation. The rival was that first-separation mass is diffuse or concentrated at a larger hidden owner scale. Rejection of (1) required an exact absolute-mass fraction below `3/4`; rejection of (2) required a positive exact product. Roots `317,1027,2002`, excursion root `5561`, and later-cluster holdout `6074` were fixed, with `53,64` as direct-pair fixtures and `3304` as the prior CORR4 exceptional regression.

### K. Exact owner algorithm and independent checks

For each prime `p` in increasing order, squarefree integers were partitioned by their common membership signature at primes below `p`. Within every signature cell, the `p`-divisible and `p`-indivisible halves have aggregates
```text
(H_1,V_1), (H_0,V_0),
```
where `H=sum h_R(n)mu(n)` and `V=sum W_R(n)mu(n)`. The cell contributes exactly
```text
H_1V_0+H_0V_1
```
to `J_R(p)`; the cell is then split and the scan continues. Each squarefree integer moves only at its actual prime factors. This is an exact finite implementation of the least-symmetric-difference owner, not a random or independent-sign model.

The primary C++ implementation used a linear Möbius sieve and a common denominator `prod_(q^2<R, q odd prime) q`. Every owner fibre, diagonal, and recombination is exact signed `__int128` arithmetic through `R=3304`. It also directly enumerated every pair at `R=53,64` and agreed fibre by fibre.

The independent Python implementation used an Eratosthenes-style multiplicative Möbius sieve, direct factor sets, and direct pair enumeration at `R=53`. It independently reproduced `G,U,D` at `R=53,317,1027,2002`; every displayed exact value agreed. At `R=53` its complete direct fibre sum is `-1920/105`, exactly matching the partition algorithm.

For `R=5561,6074`, the same discrete partition used IEEE double weights. Exact integer Möbius signs, cutoffs, and owner membership were retained. Equation (20) recombined with relative errors `9.31e-7` and `1.10e-6`, respectively. These two rows are diagnostics, not certified rational inequalities; their distance from the frozen `0.75` threshold exceeds `0.71`.

Commands and artifact hashes:

```text
g++ -Wall -Wextra -Werror -O3 -std=c++17 mixed_owner_census.cpp -o mixed_owner_census
./mixed_owner_census 53 64 317 1027 2002 3304
python mixed_owner_reference.py 53 317 1027 2002
g++ -Wall -Wextra -Werror -O3 -std=c++17 mixed_owner_census_float.cpp -o mixed_owner_census_float
./mixed_owner_census_float 5561 6074

8e8abf8fa3583c90826a4acdf3bc4c59c2e982d56ee3a51a92453d5c5f89eb02  mixed_owner_census.cpp
39944200e7bcb3905b82b9207c900e5870f02a807710c489664c7b185b11a3d7  mixed_owner_reference.py
19f1e833774ec1105e513856fd2c1f4d4032e47f4bc58307916f3b8c36b861de  mixed_owner_census_float.cpp
```

Environment: `g++ 13.3.0`, Python `3.12.14`, Linux x86_64. No random seed was used.

### L. Results and decisive falsifiers

| `R` | `G_R U_R` sign | `sum_(p<=sqrt R) |J_p| / sum_p |J_p|` | largest-|J_p| owner | arithmetic status |
|---:|:---:|---:|---:|:---|
| 53 | positive | 0.337029 | 5 | exact |
| 64 | positive | 0.276709 | 7 | exact/direct fixture |
| 317 | positive | 0.115604 | 19 | exact |
| 1027 | positive | 0.0687366 | 43 | exact |
| 2002 | negative | 0.0493755 | 73 | exact/adverse regression |
| 3304 | negative | 0.0351277 | 113 | exact |
| 5561 | positive | 0.0336762 | 113 | floating diagnostic |
| 6074 | positive | 0.0301159 | 113 | floating diagnostic/holdout |

Thus `MIXED-OWNER-3/4` is refuted already at `R=53`, with exact fraction
```text
795440/2360156<3/4.
```
At the mandatory adverse root `R=2002`, with denominator
```text
D=6541380665835015,
```
the exact values are
```text
G=208,quad DU=-233438518043839321,
```
```text
D(GU)=-48555211753118578768,quad
DD_R=783232374097529448961,
```
```text
D * sum_p J_p = -831787585850648027729.
```
The small-owner absolute fraction is exactly
```text
4984273164924969701965498/
100946205396697419458315471<0.05.
```
Hence the negative mixed product at `R=2002` is real, but it is not organized by concentration in the q-squared low-owner sector.

The second assertion is also refuted on the fixed test set. The smallest tested witness is `R=53`, where
```text
D(GU)=4488>0.
```
It also fails exactly at `R=317,1027` and diagnostically at `R=5561,6074`. Therefore no universal favorable sign may be assigned to the complete mixed product.

The most important exceptional behavior is cancellation scale. At `R=2002`,
```text
D * sum_p |J_p|
=100946205396697419458315471,
```
more than `1.2e5` times the magnitude of the final off-diagonal. At `R=317` the ratio is already above `6.1e3`. A componentwise absolute owner estimate therefore destroys the observed cancellation by several orders of magnitude.

### M. Mathematical interpretation and new post hoc hypothesis

The hidden variable exposed by this experiment is the **first-separation owner scale**, which is not the q-squared daughter-owner scale. At `R=317,1027,2002,3304,5561,6074`, the largest fibre occurs at
```text
p=19,43,73,113,113,113,
```
respectively, always between `sqrt(R)` and `2 sqrt(R)`. This suggests the post hoc exploratory statement:

`OWNER-SHELL`: at exceptional mixed roots beyond a specified onset, the largest chronological fibre lies in `sqrt(R) < p < 2 sqrt(R)`.

This was discovered after examining the data and is only `CONJECTURE`; `R=53,64` show that it is false without an onset or exception. Its value is as a new discriminator: a fresh held-out census should freeze an onset and test the full band mass, not merely the largest fibre. Even if true, an owner-shell location law alone would not bound the signed sum.

The exact finite conclusion is negative but useful. Claim `20261101-coordinator-1` identifies the correct signed incidence carrier, yet the natural same-small-owner concentration and universal-sign mechanisms fail. Any viable theorem must preserve cancellation across many chronological owners, especially the medium owner shell, rather than take ownerwise absolute values or charge only `p<=sqrt R`.

### N. Proof impact and continuation checkpoint

No complete CORR4 payment, finite A/C estimate, fixed positive eta, strict exponent below `7/8`, canonical VF theorem, or RH follows. The diagonal and every owner fibre in the mixed product were retained, but the remaining physical owner-two, renewal, terminal, root-correction, and other complement terms were not reconstructed in this experiment; no claim about their complete signed sum is made.

**Continuation:** do not enlarge the same aggregate table without a fixed new hypothesis. The next owner experiment should preregister an onset and a band statement for
```text
sqrt(R) < p < 2 sqrt(R),
```
then test both its signed and absolute mass on roots not used here. More valuable analytically is an exact cellwise involution or telescoping law pairing medium-owner fibres across adjacent primes while retaining `K_R(m,n)`; an ownerwise norm cannot exploit the cancellations measured above.

**Evidence status:** `REFUTED` for `MIXED-OWNER-3/4` by exact `R=53`; `REFUTED ON TESTED SET` for universal `G_RU_R<=0`; `FINITE_COMPUTATION` for the exact owner decomposition through `R=3304` and two extended diagnostics. The fixed eta gate remains `SEARCH_BROAD`.


## Scheduled continuation - claim \`20261101-census-3\` - 2026-11-01 19:05 EST (-0500)

**Status:** COMPLETED / exact held-out trichotomy census and independent reconstruction.  
**Live main:** \`a33987e275f8a431641d3f475b71a24aa2b1437c\`.  
**Evidence classes:** \`FINITE_COMPUTATION / EXACT RATIONAL\`; \`REFUTED ON FROZEN SAMPLE / HISTORICAL-ENDPOINT BRANCH\`; \`REFUTED ON FROZEN SAMPLE / ENDPOINT PHYSICAL-SMALL OPPOSITION\`; \`CONJECTURE / INCREMENT-ENERGY OPPOSITION\`; \`NO COMPLETE SOURCE BOUND\`; \`NO FIXED ETA GAIN\`; \`NO RH\`.

### O. Authority, continuity, and selected task

This continuation selected the newest Coordinator assignment, claim \`20261101-coordinator-2\`: test the exact historical/physical/small-owner inverse localization on held-out square-endpoint excursions. The earlier FINITE-AC bootstrap and mixed-owner tasks were already completed by claims \`20261101-census-1,2\`.

Authority remained \`AGENTS.md\` blob \`9fa5e9519e2fb6dde22217aa2a18982dafef373a\`, proof contract blob \`88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a\`, selector blob \`d05c327ae694ea54b599dab0a21032a056b521f1\`, broad-search blob \`b5c063c51556ba57c4b25bcc380a606fa8daa207\`, complete-return blob \`16838f7f3c8724b970f8b8ece0bceaab9418066d\`, and research-engine blob \`6fce99c61efb5b2a73c0cb1f1464f09b351fcd55\`.

The current November 1 reports were consumed at Coordinator \`23c2f940a766874436841c632be2eab4fe7efd8e\`, Owner \`40ad74dd7378834a48203153afc30618233f4b04\`, Analytic \`b2edb45e5843a5c9358756006b011cc6daf7300a\`, Wheel \`707a31ba0fa7b4a04266730236a9e79d4947e91a\`, prior Census \`b752c3393c6846b52abd11dd9ac40d9ccf6d1e99\`, Referee \`9b1bc0a75842d14bcdfdce6e85b4ff92fe8d1b23\`, and Lean \`9e509fcb84d2d927049c1fee08b4ab2fcce88383\`. The complete October 31 set was carried forward at the blobs recorded above in this report. External handoffs remain blob \`038018145c0fddb2f6306c0712373adf9cd1ea52\`, with no entry newer than October 18. The final open/draft PR query returned none.

Material source blobs were:

- exact physical remainder: \`LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE.lean\` \`73447e8c73ea60affec36a25b9f4794862331359\`;
- exact small/large reciprocal split: \`OAI78_CORR4_OWNER_TAIL_PAID_20261028.lean\` \`03c05e38fb2415105de9cccd3680b03c21c4be5c\`;
- compiled large-owner payment: \`OAI78CORR4PaidOriginalLargeOwner.lean\` \`06626af8cd8abfbf8f6da238f8a3d9af0893b686\`;
- literal FINITE-AC endpoint: \`EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean\` \`e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73\`.

### P. Frozen carrier and preregistered discriminator

For every root \(u\), the exact tested carrier was

\[
E_u=M(u^2-1),\qquad H_u=M(u-1),
\]
\[
C_u=\sum_{\substack{q\ {\rm odd\ prime}\\q^2<u}}
 {M(\lfloor(u^2-1)/q^2\rfloor)\over q},\qquad
A_u=H_u-E_u-C_u.
\]

For a selected endpoint \(R\), put \(T_R=\lfloor R^{1/8}\rfloor\) by exact integer comparison and retain the fixed-threshold column

\[
C_u^{\rm small}(R)=
 \sum_{\substack{q^2<u\\q<T_R^2}}
 {M(\lfloor(u^2-1)/q^2\rfloor)\over q}.
\]

Let \(L_R\) be Wheel's least integer \(1\le L\le R-1\) with
\(2|E_R-E_{R-L}|\ge |E_R|\), and set \(S=R-L_R\). The tested endpoint vector was

\[
(\Delta H,\Delta A,\Delta C_{\rm small})
=(H_R-H_S,A_R-A_S,C_R^{\rm small}(R)-C_S^{\rm small}(R)).
\]

The full increment Gram matrix retained every cross term:

\[
G_{ij}(R)=\sum_{S\le u<R}
 (X_i(u+1)-X_i(u))(X_j(u+1)-X_j(u)),
\quad (X_1,X_2,X_3)=(H,A,C_{\rm small}(R)).
\]

Before inspecting the new values, the holdout was frozen as \(12001\le R\le16000\), disjoint from claim \`20261101-census-1\`'s range. The sample rule was the eight roots with largest \(|E_R|\), ties by smaller \(R\). The endpoint branch threshold was exactly \(|E_R|/16\). Competing assertions were:

1. \`HISTORICAL-ENDPOINT\`: every selected excursion is paid by \(|\Delta H|\ge|E_R|/16\).
2. \`ENDPOINT-OPPOSITION\`: when physical and small-owner increments are compared, \(\Delta A\Delta C_{\rm small}\le0\).
3. The distinct pathwise alternative \`INCREMENT-OPPOSITION\`: \(G_{A,C_{\rm small}}<0\).

One exact failure rejects either universal assertion. The third assertion was recorded separately because endpoint sign and pathwise covariance are not interchangeable.

### Q. Exact computation and independent checks

The primary C++ implementation used a linear least-prime sieve through
\(16000^2-1=255999999\), exact integer Mertens prefixes at every queried endpoint/cutoff, and exact integer selection of the holdout roots and \(L_R\). Python \`Fraction\` arithmetic reconstructed every reciprocal column, endpoint delta, and Gram entry exactly.

A genuinely independent C++ implementation used segmented factorization of each block, with no least-prime table from the primary run. It rebuilt all 867 rows \(S\le u\le R\), including every displayed \(M(u^2-1)\), \(M(u-1)\), and every active q-squared child cutoff. The normalized row files agreed byte-for-byte; mismatches: zero. Telescoping each increment vector reproduced its endpoint delta exactly.

Commands:

\`\`\`text
g++ -Wall -Wextra -Werror -O3 -std=c++17 trichotomy_census.cpp -o trichotomy_census
./trichotomy_census 12001 16000 8 > trichotomy_raw.txt
python trichotomy_exact.py trichotomy_raw.txt > trichotomy_exact.txt
g++ -Wall -Wextra -Werror -O3 -std=c++17 trichotomy_reference.cpp -o trichotomy_reference
./trichotomy_reference 13306:13411 13331:13412 13331:13413 13331:13414 \
  13306:13415 13306:13416 14700:14841 14953:15101 > trichotomy_reference.txt
diff -u trichotomy_primary_rows.txt trichotomy_reference.txt
\`\`\`

Primary elapsed time was 4.891 seconds; independent segmented reconstruction was 5.986 seconds. Environment: \`g++ 13.3.0\`, Python \`3.12.14\`, Linux x86_64. No randomness or floating arithmetic controlled a classification.

Artifact hashes:

\`\`\`text
e9af6bad31963c25dfea584370f696fc764798f2820058feb83b34f578288c96  trichotomy_census.cpp
cf736261a796a99131de0fa65bb3f58bc0355c4b2c4979bbf21832bc9ac6cb72  trichotomy_reference.cpp
e44c3386a96ebd0192fb9c70c7242bd4239564ddd788b0506532962eaad928fc  trichotomy_exact.py
5f916a6e5bd85009ed16fa1f9181a75079220a3f67c018b735f8e28a7ad8cffa  trichotomy_raw.txt
a46d033ab9cbada6681f09d8a452f69888c04ff05f5d9d4c81db708ca96421ce  trichotomy_exact.txt
b5ad248eec4eb0ae2074d0dba70a86d2d206dbf177f6e0ad7fcd7bb89f4bee93  trichotomy_reference.txt
\`\`\`

### R. Results: endpoint localization and energy geometry disagree

Here \(h,a,c\) denote the exact ratios
\(16|\Delta H|/|E_R|,\ 16|\Delta A|/|E_R|,\ 16|\Delta C_{\rm small}|/|E_R|\).
The last three columns are the exact Gram diagonal entries normalized by
\(|E_R|^2/(256L_R)\); decimals are displays of exact rationals.

| \(R\) | \(S\) | \(L_R\) | \(E_R\) | \((h,a,c)\) | normalized \((G_{HH},G_{AA},G_{CC})\) |
|---:|---:|---:|---:|:---|:---|
| 13411 | 13306 | 105 | -5927 | (0.0351, 8.4620, 0.1359) | (0.0482, 1166.84, 15.87) |
| 13412 | 13331 | 81 | -6061 | (0.0238, 8.1840, 0.1424) | (0.0277, 682.28, 9.45) |
| 13413 | 13331 | 82 | -6077 | (0.0237, 8.2278, 0.1661) | (0.0279, 687.42, 9.56) |
| 13414 | 13331 | 83 | -6136 | (0.0209, 8.3348, 0.1948) | (0.0282, 685.36, 9.57) |
| 13415 | 13306 | 109 | -5875 | (0.0272, 8.3994, 0.1555) | (0.0534, 1317.56, 17.29) |
| 13416 | 13306 | 110 | -5865 | (0.0300, 8.4114, 0.1745) | (0.0548, 1334.19, 17.54) |
| 14841 | 14700 | 141 | 5890 | (0.0489, 7.9007, 0.6933) | (0.0874, 2548.36, 39.47) |
| 15101 | 14953 | 148 | 5863 | (0.0628, 8.3249, 0.1803) | (0.1025, 3488.04, 40.34) |

The endpoint verdict is exact and uniform on the frozen sample:

- \(|\Delta A|\ge|E_R|/16\) at all eight roots;
- \(|\Delta H|<|E_R|/16\) at all eight;
- \(|\Delta C_{\rm small}|<|E_R|/16\) at all eight.

Thus the complete physical remainder is the unique endpoint branch in every selected case. At the first selected root \(R=13411\),

\[
16|\Delta H|=208<5927,
\]
\[
16|\Delta C_{\rm small}|=84544/105<5927,
\]
while
\[
\Delta A=
{49542948686098023275496403315613535939760158153376
 \over15805027320208803894072603145771831246637343495}
\]
has \(16|\Delta A|>|E_R|\). The minimum physical threshold margin over all eight roots is still \(7.9006\ldots\) times the required threshold, at \(R=14841\).

\`HISTORICAL-ENDPOINT\` is therefore refuted on the frozen sample. The endpoint opposition assertion is also refuted: at \(R=14841\),

\[
\Delta A=
-{9193583208645708335187509279561015460964593554122
 \over3161005464041760778814520629154366249327468699},
\qquad
\Delta C_{\rm small}=-5360/21,
\]
so their product is positive.

The Gram matrices expose a different phenomenon. At every one of the eight roots,

\[
G_{A,C_{\rm small}}<0.
\]

For the endpoint-opposition counterexample \(R=14841\), the exact cross entry is

\[
G_{A,C_{\rm small}}=
-{66421001915292822981334865712955910174492898729373366
 \over1659527868621924408877623330306042280896921066975}<0.
\]

Hence same-sign endpoint displacement can coexist with negative pathwise physical/small-owner covariance. Moreover, although the small-owner endpoint never reaches the \(1/16\) threshold, its increment energy exceeds the Cauchy scale by factors from \(9.45\) to \(40.34\). The physical increment energy exceeds it by factors from \(682.28\) to \(3488.04\). Historical energy remains below that scale at every root. Large internal small-owner oscillation is therefore hidden by its endpoint cancellation.

### S. Scope, conjecture, and proof impact

This is not a verification of Coordinator premise (C6). The constant \(K\) in the absorbed large-owner estimate is existential and not numerically specified, so the census does not assert that these finite roots satisfy
\(|E_R|\ge16KR^{53/32}\). The computation instead tests the exact branch geometry that would occur after choosing \(R,S,T_R\). It neither proves nor refutes claims (C3)-(C8).

The new structural observation is that endpoint localization and increment-energy localization can select different carriers. Taking only endpoint deltas hides a large oscillatory small-owner component; taking diagonal energies alone hides its consistently negative cross term with the complete physical remainder. Any proposed joint bound must retain \(G_{A,C_{\rm small}}\), not add the two diagonal energies as independent costs.

Exploratory held-out conjecture:

> \`INCREMENT-OPPOSITION\`: on sufficiently large absolute square-endpoint record/excursion roots, with \(S\) the least half-amplitude comparison root and \(T_R=\lfloor R^{1/8}\rfloor\), one has
> \[
> \sum_{S\le u<R}\Delta A_u\,\Delta C_u^{\rm small}(R)<0.
> \]

Status: \`CONJECTURE\`. It survives eight selected roots but was tested on one finite range and six roots belong to one cluster. Negative covariance alone is not a bound, and its observed cancellation removes only about 3.2 to 5.7 percent of \(G_{AA}+G_{CC}\). No endpoint exponent follows.

**Evidence status:** \`FINITE_COMPUTATION\` on the eight preregistered held-out extrema, with exact rational reconstruction and a fully independent segmented check of every input row. \`HISTORICAL-ENDPOINT\` and universal endpoint physical/small opposition are \`REFUTED ON THE FROZEN SAMPLE\`; pathwise increment opposition is \`CONJECTURE\`. The complete shell bound, strict Mertens exponent below \(7/8\), finite A/C, canonical VF theorem, and RH remain OPEN.

### T. Continuation checkpoint

Do not rescan \(12001\le R\le16000\). Freeze the disjoint range \(16001\le R\le20000\) and test \`INCREMENT-OPPOSITION\` on the same top-eight rule, plus the \(R=64,q=5\) activation regression where applicable. More valuable analytically is an exact decomposition of \(G_{A,C_{\rm small}}\) by q-owner and activation/threshold-change terms. The next theorem candidate must explain the negative cross energy on genuine occurrences and quantify it relative to both diagonals; a sign table alone cannot close the route.

\`eta_gate: SEARCH_BROAD\`  
\`primary_route_and_original_carrier: FINITE-AC/VF-LOW/OAI bridge on literal Mertens endpoints, complete physical remainder, and q-squared reciprocal column\`  
\`actual_new_lemma_or_first_unresolved_inequality: finite physical-only endpoint localization plus pathwise negative physical/small covariance; unresolved uniform source-faithful cross-energy inequality\`  
\`independent_reviewer_and_formal_evidence: PENDING; no Lean theorem claimed\`  
\`net_endpoint_gain_after_complete_return: UNKNOWN\`
