# RH_Lean Prime Census Laboratory - 2026-10-21

**Status:** COMPLETED  
**Run:** 2026-10-21T01:51-04:00 scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Campaign status:** `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`  
**Evidence:** `FINITE_COMPUTATION` (two independent exact implementations), `REFUTED` (either sign of shellwise complete-residue moment excess), `NO_NEW_QUANTITATIVE_BOUND`

## A. Bottom line

This run replaced yesterday's settled unweighted four-fiber scan by an exact once-owner square-shell census. The carrier consists of every physical integer

```text
n = p*k in [R^2,(R+1)^2),  k<R<p,
p and k distinct rational primes, p == k == 1 (mod 3).
```

Each rational owner is counted once. Its two primary Eisenstein generators and both prime ideals above the selected high prime are retained until the four labelled sextic phases are formed. If the first primary generator has phase exponents `(e,f)`, the other has `(-f,-e)`, and the exact four-label trace is

```text
T = tau(e)+tau(f),  tau(0..5)=(2,1,-1,-2,-1,1).
```

The exact complete-residue benchmarks are `E(T^2)=4` and `E(T^4)=36`. The new decisive finding is that the shellwise excess has **both signs** on this genuine physical subcarrier:

```text
R=317:  W=25, sum T^2=61  < 4W=100,
                sum T^4=445 < 36W=900.

R=1027: W=62, sum T^2=294  > 4W=248,
                 sum T^4=2526 > 36W=2232.
```

Thus any proposed theorem that every selected-prime square shell has moment at most the complete-residue moment is false, and the reverse inequality is also false. This is claim `20261021-census-1`, classified `FINITE_COMPUTATION / EXACT COUNTEREXAMPLES`. It does not refute an averaged moving-ray-class theorem and supplies no detector saving.

On preregistered disjoint ranges, aggregate buckets move closer to the complete-residue law:

| roots | owners W | sum T^2 | sum T^4 | T2-4W | T4-36W | normalized 36-bucket L1 discrepancy |
|---|---:|---:|---:|---:|---:|---:|
| 50..800 development | 20,196 | 79,660 | 709,948 | -1,124 | -17,108 | 0.0407011 |
| 801..2000 held-out | 102,387 | 408,558 | 3,662,874 | -990 | -23,058 | 0.0136834 |

The held-out averages are `3.9903308` and `35.7747956`. This near-uniformity is finite evidence only. Shellwise extrema remain large and sign-changing; no rate, monotonicity, equidistribution, or uniform detector theorem is claimed.

## B. Authority and provenance

Final refresh: 2026-10-21T05:57:55Z.

- `main@57862f8a6ba0a45430a25f363ba2a0aeca23552b`.
- `agent-reports@8c8b756e9f545ef66fcb9dcbe263de752be34ea6` before publication.
- `AGENTS.md` blob `20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6`.
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- Native replication protocol blob `53194dc3ae106be363bc22cf85a88bac4a3b2e6e`.
- Dynamic protocol blob `bd1189617c069565a881c2a5c5dbd9a138bc48c1`.
- External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.
- Native ideal-fiber source blob `cc99bbb2d02b700ff9cf2e555861208430f42acc`.
- Owner projection source blob `3b957ea0ab1b53e2d6e79599329fb234f6e4561c`.
- Full fibre-Fubini/Gram source blob `2483ec0aef923ba9a85c3f5d8a7fe6d5ac400461`.
- OAI actual sharp norm-fiber bridge blob `4f8500d5887be6e039c5587b9dbc79e8449a18f8`.
- OAI actual compensated sharp source blob `c864e2bf304a32e7492e935faa9d6a01411a5ad4`.

At intake and final pre-publication check, the 2026-10-21 report directory and this path were absent: all today's upstream stages are `TODAY=PENDING`; no execution is inferred.

The complete 2026-10-20 reports were consumed as `YESTERDAY=CARRY_FORWARD`: Coordinator `a39601d4a6774db98e533ab63daa7c82e7b483be`, Owner `6381decdb075f728386e709aa19758e07a39d2ee`, Analytic `1c0c7e1c6561a95fc0c0ca8c3c6e99a829693051`, Wheel `16519e3f2bb2ee0da08ae843f5b3311c2fb5276c`, Census `3d8b87747418bb4db86fe191f01a78801623a643`, Referee `bebdcfdf3490b82ea907af7eb5403f7a17b950dc`, and Lean `7511adca99ef29b13b7f54d9f2efe48c60570b15`.

Relevant live drafts observed: #987 at head `a5271548202e004dab4f872962dd7fedbb94bac1`, open/draft/mergeable, and #992 at head `1b35f8057bbf3930790f2fe003ca51fbfcd30a1a`, open/draft/mergeable. Neither was merged or altered here. #992 assembles LOW/HIGH/common-probe closure from pinned proved OAI intermediate inputs; it is not an independent reconstruction of those analytic inputs. The direct sharp source moment remains separate and open.

## C. Mathematical question and preregistration

**Mystery.** Yesterday proved that complete four-label traces have exact uniform moments 4 and 36 on the full residue carrier, while coherent `T=+/-4` fibres occur infinitely often. Does the actual once-owner square-shell semiprime carrier have a one-sided moment bias that could provide deterministic local payment?

**H1.** Every shell has `sum T^2 <= 4W` and `sum T^4 <= 36W`; actual prime/cofactor incidence suppresses coherent buckets.

**H2.** Every shell has the reverse bias; actual incidence concentrates coherent buckets.

**H3.** Bias changes sign shell by shell; only a nonlocal weighted moment or ray-class discrepancy theorem can save.

**Discriminator.** Enumerate the exact 36 phase buckets for each shell, preserving ideal labels until trace formation but counting the physical owner once. A strict example of each sign refutes H1 and H2. Development roots were fixed as `50..800`; the untouched validation range was `801..2000`, containing required root 1027.

This is a sharp square-shell semiprime subcarrier with unit local branches. It does **not** include the OAI smooth annular detector weights, arbitrary selected subsets, `p|u` one/zero-active branches, principal row, ramified prime, local Euler error slots, or cross-shell Gram. Those omissions prohibit transfer to Stage III.

## D. Exact reconstruction

For each integer in the shell, an SPF sieve accepts it only when it has exactly two distinct prime factors, both split modulo 3, with the smaller `k<R` and larger `p>R`. For each accepted `k`, both primary coordinates satisfying

```text
a^2-a*b+b^2=k, a==1 (mod 3), b==0 (mod 3)
```

are enumerated. For each selected `p`, the two nontrivial cube roots solve `r^2+r+1=0 mod p`. The phase exponent is the unique `e in Z/6Z` satisfying

```text
(1+r)^e = (a+b*r)^((p-1)/6) mod p.
```

Every accepted owner passed the exact conjugation check `(e',f')=(-f,-e)`. This independently reconstructs the definitions in `vf919SplitSexticResidue` and the owner projection, without using the prior phase tables.

The 36-bucket discrepancy is

```text
D1 = sum_(e,f) |w(e,f)/W - 1/36|
   = [sum_(e,f) |36*w(e,f)-W|] / (36W).
```

No floating arithmetic enters carrier admission, phases, traces, moments, or discrepancy numerator.

## E. Computation and independent check

Python and C++ use separate sieve, factor-admission, generator, root, and phase implementations. They agree exactly on all aggregate counts, all 36 buckets, all nine trace counts, moments, coherent certificates, and shell ranges.

Commands:

```sh
python sextic_shell_bucket_census.py
g++ -O3 -std=c++17 -Wall -Wextra -Werror \
  sextic_shell_bucket_census.cpp -o sextic_shell_bucket_census_cpp
./sextic_shell_bucket_census_cpp
```

Environment: CPython 3.12.14; GCC 13.3.0.

Source SHA-256:

```text
Python a174b371a1a2c592bb48406503e129cb842b21843a9cab931658f65e8fc43e3d
C++    5dbd6ecb0c698a83d4751a48f7e95624ececf5c530ab269975c3c332c4cfadd8
```

Canonical Python JSON payload SHA-256:
`680942292518f77c05a42cd8c0244ac4219149ae9270b2f7021c004e0d4d04ad`.

Small coherent certificates include `R=53,n=2869=151*19,(e,f)=(0,0),T=4` and `R=54,n=2947=421*7,(3,3),T=-4`. In the held-out range, `R=802` already contains both signs: `643837=17401*37` gives `T=4`, while `643393=17389*37` gives `T=-4`.

Shellwise sign changes occur immediately in both registered ranges: roots 50/51 have negative/positive excesses, and held-out roots 801/802 have negative/positive excesses for both moments. Adverse held-out extrema include:

```text
T2-4W:  min -158 at R=1669; max +148 at R=1545.
T4-36W: min -1838 at R=1669; max +2040 at R=1190.
```

## F. Proof impact

1. `20261021-census-1`: deterministic one-sided shell moment bias on this carrier is `REFUTED` in both directions. Complete-residue moments are a center, not a pointwise shell inequality.
2. The held-out aggregate is close to uniform but shell extrema do not shrink monotonically. A proof must average with the actual detector measure or establish nonlocal compensation; it cannot charge each shell separately by a favorable sign.
3. The exact 36-bucket discrepancy remains the right observable for a moving-ray-class theorem. The finite decrease from 0.0407 to 0.0137 motivates, but does not establish, a rate.
4. Same-owner ideal labels were not spent as four physical sites. They were combined into `T` before the one physical owner received weight one, consistent with the fibre-Fubini warning.
5. The experiment does not instantiate the complete OAI source. In particular, it omits the zero-extension branches and actual smooth detector decorations, so it cannot verify the inverse-second/plain-fourth moment hypotheses.
6. Stage I 11/12, genuine Stage III moments, full marked-minus-rescaled error accounting, independent native 7/8, canonical VF, and RH remain OPEN.

## G. Continuation checkpoint

Do not enlarge this unweighted square-shell census unchanged. The next nonduplicate experiment is to extract from the actual upstream `DetectorPlainStateDictionary` / selected-slot source a finite explicit nonnegative energy weight and apply it to the same 36 buckets, with separate tables for:

1. two-active unit fibres;
2. one-active primitive `p|u` rows;
3. zero-active content-divisible rows;
4. principal and ramified restoration;
5. each marked-minus-rescaled local error slot.

The acceptance test is coefficientwise reconstruction of the full finite weighted source before moments, followed by independent agreement of direct Euler expansion and labelled subset expansion. The decisive falsifier is any duplicated rational owner, omitted zero branch, or sign-changing weighted excess incompatible with the claimed uniform collision margin.

No RH proof claim.
