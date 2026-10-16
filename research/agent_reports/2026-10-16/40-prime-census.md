# RH_Lean Prime Census Laboratory - 2026-10-16

**Status:** PARTIAL / IN_PROGRESS  
**Run ID:** 2026-10-16T01:51:02-04:00, scheduled invocation  
**Checkpoint:** 2026-10-16T01:55:51-04:00

## Early checkpoint

Live authority was refreshed at `main@68bc4aaae65c9f505202a22df446c0fb40e4d040`. The canonical target remains `VFCanonicalSquareVonKochStatement`. Authority blobs: `AGENTS.md` `cbc234051834f971929d82972ba6a157b2129d32`; `CURRENT_PROOF_CONTRACT.md` `dc73babe5eb7b8f9fb83272a27cd2468dbdcb7f2`; factor-depth brief `1a5f94bb81aa7d50b7c118f823a14c9ec644f947`; dynamic protocol `61f7e4dd90200c2f3426fce1e96f9779f40238dc`.

Today's Wheel report, blob `9af028f5ce10cf9a06280d47ae6b0795c5974b8b`, proves that every positive raw residual occurrence has the exact form `n=a*q`, with `q=P+(n)`, odd composite `a>=9`, and `q<R^2/9`. This forces compensation with the macro negative tail to be cross-tag.

The active experiment tests whether the positive residual is concentrated in a bounded collection of small cofactor layers or is genuinely multiscale. It directly enumerates raw physical seats and independently reconstructs the same carrier from `(a,q)` incidence. The first exact structural candidate exposed is a cofactor-depth staircase: for `X=R^2`, if `a^(j+1)>=X^j`, then `Omega(n)>=j+2`. A proof and finite falsification audit are in progress. No endpoint bound or RH claim is made.

Today Coordinator, Owner, Analytic, Referee and Lean reports were absent at initial refresh and are recorded `TODAY=PENDING`; 2026-10-15 is being used as `YESTERDAY=CARRY_FORWARD`. The external inbox blob remains `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c`.


---

## Completion update - 2026-10-16T01:58:36-04:00

**Status:** COMPLETED  
**Result classes:** `PAPER_PROOF`, `FINITE_COMPUTATION`, exact mechanism restriction, `NO_NEW_RESULT` on the canonical bound

## A. Mathematical mystery and rival predictions

Write `X=R^2`. By Wheel Claim `20261016-wheel-1`, every occurrence in the positive raw residual `H_R` is represented uniquely as

```text
n = a*q < X,
q = P+(n),
a odd composite, a >= 9,
```

with its original physical weight `w_floor(sqrt(n))`.

The question was whether the forced cross-tag compensation can be routed through a bounded collection of small composite cofactors.

- **H_fixed:** a fixed finite cofactor backbone, such as `a=9,15,21,...`, carries a nonvanishing fraction of `H_R`.
- **H_multiscale:** every fixed finite cofactor set becomes negligible; any successful transport must use cofactors whose range grows with `R`.
- **Discriminator:** reconstruct `H_R` directly and independently by `(a,q)`, then measure fixed layers, logarithmic cofactor bands, and total prime-factor multiplicity `Omega(n)`.
- **Failure criterion for H_fixed:** prove `H_R(A)/H_R -> 0` for every fixed finite set `A`, rather than infer it from a finite trend.
- **Unexpected third possibility:** a support law could force large cofactors into sharply higher factor depth even if no size estimate follows.

Both the H_fixed falsification and the third structural law occurred.

## B. Claim `20261016-census-1` - exact cofactor-depth staircase

**Status: `PAPER_PROOF`.**

Let `n=a*q<X=R^2` be an `H_R` occurrence, with `q=P+(n)`, and let `k=Omega(n)`. Then

```text
a^k < X^(k-1),
equivalently a < X^((k-1)/k).
```

Consequently, for every integer `j>=1`,

```text
a^(j+1) >= X^j  ==>  Omega(n) >= j+2.
```

**Proof.** The cofactor `a` contains exactly `k-1` prime factors counted with multiplicity. Every one is at most the greatest prime factor `q), hence `a<=q^(k-1)`. Therefore

```text
a^k <= (a*q)^(k-1) = n^(k-1) < X^(k-1).
```

If `k<=j+1`, then `(k-1)/k<=j/(j+1)`, contradicting `a^(j+1)>=X^j`. This proves the staircase.

The exponent walls are asymptotically sharp on the underlying nonsquare carrier. Odd depths use prime powers `p^k`; even depths use `p^(k-1)q` with `p<q` and `q/p->1`. Taking `R=floor(sqrt(n))+1` places these nonsquares in the strict raw carrier, and the cofactor exponent approaches `(k-1)/k`.

This is an inverse structural restriction, not an estimate for the mass in a depth layer and not a bridge to the clipped returned-cell source.

## C. Claim `20261016-census-2` - no fixed cofactor backbone

**Status: `PAPER_PROOF`.**

For a fixed finite set `A` of odd composite cofactors, let `H_R(A)` be the total native weight of `H_R) occurrences whose exact greatest-prime cofactor lies in `A`. Then

```text
H_R(A) / H_R -> 0  as R -> infinity.
```

**Lower bound for the denominator.** In `[X/2,X)`, every odd multiple of 9 that is not a square is a squareful `H_R` occurrence. There are `X/36+O(sqrt(X))` such integers. For every raw block `r<R`,

```text
w_r = (2+1/r)/log(r^2+r+1/2) > 2/log X.
```

Thus `H_R >> X/log X`.

**Upper bound for one fixed cofactor.** Relax the greatest-prime condition and sum over every prime `q<X/a`. The part with `aq<sqrt(X)` has `O_a(sqrt(X))` bounded-weight terms. On `aq>=sqrt(X)`, the native weight is `O(1/log X)`; Chebyshev's prime-count upper bound gives `O_a(X/log X)` candidate primes. Hence

```text
H_R({a}) = O_a(X/log^2 X + sqrt(X)).
```

Summing over fixed finite `A` and dividing by the lower bound proves the claim.

Therefore the already-forced cross-tag transport is also forced to be **growing-cofactor and multiscale**. Any mechanism using only finitely many cofactor channels is rejected as a complete explanation. This conclusion is independent of the endpoint mismatch and does not assume cancellation.

## D. Claim `20261016-census-3` - direct and incidence reconstructions

**Status: `FINITE_COMPUTATION`.**

The direct C++ implementation sieved smallest prime factors, enumerated every odd nonsquare physical seat below `X`, classified prime/distinct-semiprime/`H_R`, and then recorded `a=n/P+(n)`, `Omega(n)`, and native weight. The independent Python implementation enumerated composite cofactors `a`, independently factored `a`, selected primes `q>=P+(a)` with `aq<X`, and reconstructed the occurrence.

At `R=500` and `R=1000`, both methods agreed exactly on every band count and on total `H_R` occurrence counts (58,608 and 252,673). Their weighted totals agreed within `9e-11` and `8e-9`, respectively. Python arbitrary integers performed the staircase threshold comparisons exactly; there were zero violations for `j=1,...,7`. The direct scan also found zero violations over every tested occurrence through `R=5000`.

Prior endpoints `500,1000,3162` reproduce Claim `20261015-census-3`; new endpoints `4096,5000` test a power-of-two boundary and a larger round cutoff.

| R | H occurrences | H mass | share a<=R | top 15 a share | share a>=X^(2/3) | share a>=X^(3/4) |
|---:|---:|---:|---:|---:|---:|---:|
| 500 | 58,608 | 10,294.849002 | 0.687187 | 0.275735 | 0.025589 | 0.002515 |
| 1,000 | 252,673 | 39,556.245779 | 0.687967 | 0.218252 | 0.025389 | 0.002212 |
| 3,162 | 2,777,959 | 368,388.745489 | 0.686474 | 0.158875 | 0.025713 | 0.001879 |
| 4,096 | 4,744,205 | 608,233.562737 | 0.685537 | 0.149384 | 0.025798 | 0.001823 |
| 5,000 | 7,160,321 | 895,082.571879 | 0.685185 | 0.142740 | 0.025994 | 0.001779 |

At `R=5000`, logarithmic cofactor bands `X^[b/8,(b+1)/8)` carry fractions

```text
b=1..7:
0.147103, 0.226287, 0.311795, 0.252383,
0.060654, 0.001777, 0.00000146.
```

The three central bands `X^(1/4)<=a<X^(5/8)` carry 79.05% of `H_R`; the largest individual layer, `a=9`, carries only 2.845%. By multiplicity, `Omega=3,4,5` carry 51.53%, 29.71%, and 12.48% of the mass. These decimals are ordinary long-double diagnostics, not certified enclosures and not asymptotic theorems.

The finite profile is consistent with Claim 2: mass is spread across a growing cofactor population. Claim 2, rather than the trend, supplies the all-scale rejection of H_fixed.

## E. Reproducibility and error control

Environment:

```text
Python 3.12.14
g++ 13.3.0
compile: g++ -O3 -std=c++20 cofactor_layers.cpp -o cofactor_layers
runs: ./cofactor_layers 500 1000 3162 4096 5000
cross-checks: python cofactor_crosscheck.py 500
              python cofactor_crosscheck.py 1000
```

Final source hashes:

```text
685ba334e9058070bfd1b464f67881e34bfa3e2341c05f96ff20fb5bb0c97b42  cofactor_layers.cpp
89f0a7b83271a02daec86c87ac899a3f054653533d0f73070a2ef03198401b69  cofactor_crosscheck.py
```

All primality, factorization, occurrence, multiplicity, and threshold comparisons in the Python cross-check are exact integers. The direct program's threshold selector uses long-double logarithms, but its zero-violation outcome is only a regression: Claim 1 is proved algebraically, and Python checked the finite thresholds with exact powers. Weighted sums use standard `log`/`long double`; no near-zero weighted sign is used for a theorem.

Repository novelty searches for the staircase and fixed-cofactor mass law found related cofactor infrastructure but no equivalent statement on this raw greatest-prime `H_R` carrier. Search results are navigation, not proof evidence.

## F. Authority, continuity, and source state

Final live refresh:

- `main`: `68bc4aaae65c9f505202a22df446c0fb40e4d040`.
- `AGENTS.md`: `cbc234051834f971929d82972ba6a157b2129d32`.
- `CURRENT_PROOF_CONTRACT.md`: `dc73babe5eb7b8f9fb83272a27cd2468dbdcb7f2`.
- Factor-depth brief: `1a5f94bb81aa7d50b7c118f823a14c9ec644f947`.
- Dynamic protocol: `61f7e4dd90200c2f3426fce1e96f9779f40238dc`.
- Amplification budget: `3beff1f789646d59237744379ff8e578bb1042a0`.
- Canonical definition: `research/VF_CANONICAL_SQRT_TWO.lean`, blob `b504704070b193cea835713d697ba0d980704c7a`.
- Canonical theorem: `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean`, blob `43e160ac7ad51f7646771297f43a9b95395ce709`.
- Original signed-seat source: `research/VF_MID_SIGNED_SEAT_CHARGE.lean`, blob `13dda0d2c6cc59580959a2d59fad60126b1c6b0b`.
- New merged Nyman note: blob `b2775c892edffe920a101651eef6f3581c73c9d4`; it is a distinct positive Hilbert carrier and does not alter this experiment's raw source.
- Live open PR search: none. PR #957 is merged in the current main head.

At final refresh, today's Coordinator, Owner, Analytic, Referee and Lean reports remained absent: `TODAY=PENDING`. Today's Wheel blob `9af028f5ce10cf9a06280d47ae6b0795c5974b8b` was consumed. Yesterday's reports were carried forward: Coordinator `0f9e254738e1bc3d01cfd0a3b114d99b7478b08a`; Owner `01fb928be14c1004b3124fb25101f369ad7e8611`; Analytic `fda92df0cd94cb997f213eddf4e6a5427b6dd03f`; Wheel `6d451c35eef4021fcff78253bed609d193c249c1`; Census `2e3c1cf95cd11669d57d2ce1f7216916736ff095`; Referee `cf0db85f6b04c56527bc9a26a1b6741ae196435a`; Lean `a11eddb6f78c927b8ec838426f94d72e63cda123`. External inbox blob `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c` supplied no later claim changing this carrier.

## G. Proof impact and mechanism decisions

- **Fixed finite cofactor backbone:** `REJECT`. Claim 2 proves it carries vanishing relative `H_R` mass.
- **Greatest-tag-preserving transport:** remains `REJECT` by Wheel Claim `20261016-wheel-3`.
- **Growing multiscale cross-tag transport:** `CONTINUE / REVISE`. It is now a necessary shape, not a proved cancellation mechanism.
- **Cofactor-depth staircase:** `CONTINUE` as an exact inverse classifier. Large cofactor exponent forces high `Omega`, but no sufficiently strong bound on the corresponding weighted mass or its signed partner is yet proved.
- **Canonical endpoint estimate:** `NO_NEW_RESULT`. Neither claim bounds `T_R+H_R`, preserves a full signed pairing with the negative macro tail, or bridges to the masked/clipped first-bad returned carrier or compressed #915 norm.

The independent fact learned is that the positive compensator cannot be explained by a finite list of low-depth cofactor channels. A valid factor-depth mechanism must couple a growing hierarchy of cofactor layers across disjoint greatest-prime sectors while preserving native weights and the full cross term.

## H. Handoffs and continuation checkpoint

- **Owner:** any proposed transition from the macro negative tail into `H_R` must use unbounded cofactor support. A finite family `a=9,15,...` is asymptotically negligible. Preserve the staircase `a^k<X^(k-1)` and all boundary/weight defects.
- **Wheel:** the one-ninth support law and this fixed-cofactor no-go combine into a two-axis obstruction: transport must change greatest-prime tag and expand cofactor scale.
- **Referee:** audit the denominator lower bound using nonsquare odd multiples of 9, the fixed-layer Chebyshev upper bound, and the asymptotic sharpness qualification.
- **Lean:** after referee acceptance, the algebraic core `a<=q^(k-1) -> a^k<(R^2)^(k-1)` is a small formalization candidate. The asymptotic Claim 2 requires existing prime-count upper-bound infrastructure and is not requested as an immediate PR.

**Next decisive experiment:** condition the complete signed complement `B_R` simultaneously by cofactor exponent and `Omega`, then test a predeclared cross-tag transport kernel against the macro tail `A_R`. Do not merely refine the positive `H_R` histogram: the next observable must include the negative partner and recombine exactly to `L_R`.

Reusable evidence: the two source hashes above, exact counts through `R=5000`, the `R=500/1000` independent incidence reconstructions, and the staircase regression. Do not rerun them unless definitions, cutoffs, or the proposed kernel change.

No canonical endpoint, #915 payment, finite A/C, CORR-4, MU-LIFT gain, or RH proof is claimed.

## I. Publication verification

- Early checkpoint commit: `696b94604a13297cd47cbc51b631729b8fce9caa`.
- Verified checkpoint blob: `349595c9608bf9ab13197cae9477017bb9687361`.
- Substantive completion commit: `2b2049d3e4f619282d6eb67332fef398ab54cfe8`.
- Verified substantive blob: `196707ebaa47da197b9275aa5d0d5980cbc35f1e`.
- A final metadata-only correction records these identifiers; its resulting blob is verified externally because a file cannot contain its own Git blob hash.
