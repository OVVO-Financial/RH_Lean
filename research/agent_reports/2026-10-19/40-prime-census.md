# RH_Lean Prime Census Laboratory - 2026-10-19

**Status:** COMPLETED  
**Run:** 2026-10-19T01:51-04:00 scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Evidence:** `FINITE_COMPUTATION`, exact finite identity regression, finite mechanism falsification; `NO_NEW_QUANTITATIVE_RESULT`

## A. Bottom line

This run independently tested the proposed moving-owner endpoint formula `(MOVING)` from draft PR #982 on its literal genuine-prime, genuine-Mobius carrier, with every partial length `0 <= K <= H`. The formula survived 145,609 exhaustive exact tests for `3 <= H <= 60`, every admissible translation `|t| <= H-2`, and every `K`. It also agreed with a structurally separate prime-product enumeration of all translated occurrences at designated and adversarial roots.

For `T = floor(0.8 H)`, define

```text
G(H,K,t) =
  sum_{H <= r < H+K} sum_{c <= r} mu(c)
    #{prime p > r : r^2+t < p*c <= (r+1)^2+t}.
```

The tested endpoint identity is

```text
G(H,K,t) =
  sum_{1 <= c < H+K} mu(c) *
    [pi(floor(((H+K)^2+t)/c))
     - pi(max(c, floor((H^2+t)/c)))].
```

The strict lower wall and the lower cutoff `p>c` are both load-bearing.

The new finite mechanism result is negative but useful: the balanced band `c>T` has no stable sign and does not predict the complete translated response. Its completed-block numerator is positive at `H=25,166,5561` and negative at `H=317,1000,1027,6000`. At `H=1027` it is already negative at the largest positive complete-prefix excursion, while the full response is positive. The lower high-owner band `c<=T`, including the prime-only `c=1` mode, remains load-bearing; the separate root-smooth compensator was not reconstructed in this experiment and remains required.

Thus `(MOVING)` is strongly supported as an exact finite reindexing, but neither the balanced triangle by itself nor a completed-block sign is the missing uniform signed estimate. No `5/6` Mertens bound, shell-energy improvement, original #915 source payment, canonical VF estimate, or RH result is claimed.

## B. Authority, provenance, and continuity

Final source authority was refreshed at 2026-10-19T05:59:52Z:

- `main@28a270195167530615c2b182f8c9ffd86855b1f6`, merge of PR #981.
- `AGENTS.md` blob `4c66a1d462df98c84deebf0069ad11f904039858`.
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- PNT-first contract blob `e8acbeff24942d1f8ee0079f715afff2ddda2c33`.
- two-scale attack plan blob `0606d764ffebb4639cc0abb52ccbef30546b7764`.
- dynamic protocol blob `bd1189617c069565a881c2a5c5dbd9a138bc48c1`.
- external inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52`; `EXT-20261018-PNT-1..3` were consumed with their original classifications.
- merged localized moving-window report blob `c17798891f475fd78a2f51cbddd5d585f81d3eb2` and frozen `H=8192` data blob `c27cb99c2f170942fdbf483332300510051bf9c8`.
- compiled carriers inspected: `BlockCovarianceDecomposition.lean` blob `42dd692634a0c44855803f8bc33df4d5f6e4e413`, `SquareRootMatchedTransport.lean` blob `e9ab3bff6b8819182c39721f92859679d250002e`, `SquareBlockSmoothTransportGram.lean` blob `09f5e0108eb254a2f20fa2fd694d69cb455b2857`, and canonical interface blob `b504704070b193cea835713d697ba0d980704c7a`.

Draft PR #982 was inspected at head `83b2992e1eabde67fbaaecb4911ff55fb71d8a61`. Its long-lag note is blob `451824604acc988dfb848bc602a26478d0679d44`, source-guided 317/1027 note blob `1947f96a731a38f12fef57de6d40f9c80c30aee0`, and census source blob `e0277d926f1b96843e7cffa75ee728d20348bf77`. PR #982 remains draft and its independent small-gcd long-lag estimate is OPEN. Open draft PRs #983 and #984 were observed; neither changes the current canonical theorem.

At intake, every named 2026-10-19 upstream report was absent: `TODAY=PENDING`. The applicable 2026-10-18 set was used as `YESTERDAY=CARRY_FORWARD`: Owner `84fdf8ec488848eb033e7ac3d882ec43051d5b88`, Analytic `fd182e0de5e703aa62738a426b80db483dfc967c`, Wheel `62da494755501409879e894779d026aed70835f8`, Census `701b74c281d01f6727669808566d76b1e8758b26`, Referee `c0360eaa56c34198f21f9387113fd565a19b542f`, and Lean `bff111a9448b17061f4dc2be760ea8422245a3f6`. Coordinator continuity was recovered from immutable blob references recorded by those reports; its named path was absent when fetched, so no scheduled execution was inferred.

## C. Preregistered question

**Mystery.** PR #982 converts the moving condition `p>r, c<=r` into fixed factor order `p>c`, suggesting a balanced Type II triangle when `T` is comparable to `H`. Is the endpoint formula exact at every strict boundary, and does `c>T` explain the uniform partial-prefix response?

**H1 (balanced-band mechanism).** After exact reindexing, `c>T` has a stable compensating sign or controls the sign of the full translated response uniformly in `K`.

**H2 (complete compensation).** The formula is exact, but `c>T` changes sign and the `c<=T` complement is comparable or dominant; only a joint signed estimate with the separately restored smooth source can work.

**Failure criteria.**

1. Any direct-occurrence/endpoint mismatch refutes `(MOVING)` as stated.
2. Opposite signs between `c>T` and the full source, or sign changes across roots, refute H1.
3. Completed-block agreement without uniform-prefix control is insufficient; every `K` is scanned.

The original #915 weights, masks, anchor, clipping, and NNS denominator are absent. This is the genuine scalar Möbius source assigned by #982, not a claimed original-VF bridge.

## D. Methods and validation

### D.1 Exhaustive endpoint audit

A C++17 linear sieve supplied exact `mu(c)`, primality, and `pi(x)`. The left side was calculated shell-by-shell from literal `c<=r`, `p>r`, and `r^2+t < p*c <= (r+1)^2+t`. The right side was calculated independently by cofactor endpoint counts.

Coverage:

```text
3 <= H <= 60
-(H-2) <= t <= H-2
0 <= K <= H
```

All 145,609 cases agreed exactly.

Command:

```sh
g++ -O3 -std=c++17 -Wall -Wextra -Werror moving_formula_check.cpp -o moving_formula_check
./moving_formula_check
```

Output: `PASS tests=145609`. Source SHA-256: `7d63ba4f278911ea679f79606f91e38722a42a9eeee6398e5f91a174f572c154`.

### D.2 Independent translated occurrence enumeration

For the larger runs, the primary implementation enumerated primes `p` and products `p*c` in the expanded interval. Each occurrence received the exact integer multiplicity

```text
#{t in [-T,T] : r^2+t < p*c <= (r+1)^2+t}.
```

This avoids summing prime-count endpoint differences translation by translation. Endpoint sums were recomputed separately at maximizing, minimizing, and completed prefixes; every check agreed.

Compiler: GCC 13.3.0, warning-fatal flags above. Source SHA-256: `c66da9fc42e5a1723ae6040a5cc96f3d6ca689da8eeb40e26263c5225a57b3d1`. The combined `H=5561,6000` run took 11.2 seconds wall time. All decisions are integer exact; displayed averages are numerator divided by `2T+1`.

### D.3 Quotient-clock cross-check

A separate Python prime-multiple Möbius sieve checked

```text
2 * sum_{sqrt(x) < p <= x} (1 - M(floor(x/p)))
 =
2 * sum_{k <= sqrt(x)} (1 - M(k)) * N_x(k),
```

where

```text
N_x(k) = pi(floor(x/k))
         - pi(max(floor(sqrt(x)), floor(x/(k+1)))).
```

Direct prime enumeration and quotient buckets agreed exactly at `x=317,1027,9215,100488`.

## E. Claim `20261019-census-1`

For the translation average `Gbar(H,K) = sum_t G(H,K,t)/(2T+1)`:

| H | T | completed average | positive K | maximum average @ K | c>T completed numerator | c<=T completed numerator |
|---:|---:|---:|---:|---:|---:|---:|
| 25 | 20 | -35.7805 | 1 | +5.02439 @ 1 | +995 | -2,462 |
| 166 | 132 | -739.853 | 5 | +21.1472 @ 4 | +27,981 | -224,042 |
| 317 | 253 | -2,067.50 | 1 | +16.2485 @ 3 | -24,448 | -1,023,774 |
| 1000 | 800 | -15,382.8 | 4 | +18.2792 @ 11 | -2,550,938 | -22,076,889 |
| 1027 | 821 | -15,961.1 | 1 | +1.80767 @ 1 | -3,363,232 | -22,860,793 |
| 5561 | 4448 | -309,552 | 0 | -57.1175 @ 1 | +89,191,477 | -2,843,278,102 |
| 6000 | 4800 | -346,933 | 9 | +173.256 @ 2 | -244,525,639 | -3,086,381,144 |

At `H=1027,K=1`, the total translated numerator is `+2,970`, but `c>T` contributes `-16,236`; `c<=T` contributes `+19,206`. At `H=5561`, the balanced completed band is positive while the full response is negative for every `K`. These are exact counterexamples to a balanced-band sign/dominance surrogate.

The `mu(c)>0` and `mu(c)<0` populations are individually enormous. At `H=6000`, their completed translated numerators are `+246,531,474,139` and `-249,862,380,922`, leaving `-3,330,906,783`. A norm-first treatment discards cancellation by roughly two orders of magnitude.

**Classification:** `FINITE_COMPUTATION`. `(MOVING)` is verified only on the finite domains above. H1 is `REFUTED` as a universal sign or standalone dominance mechanism. H2 survives.

## F. Quotient-clock counterexamples

| x | root | positive prime events | zero | negative | total update |
|---:|---:|---:|---:|---:|---:|
| 317 | 17 | 30 | 29 | 0 | +116 |
| 1027 | 32 | 86 | 75 | 0 | +340 |
| 9215 | 95 | 598 | 519 | 1 | +2452 |
| 100488 | 316 | 5068 | 4489 | 9 | +20912 |

The negative event at `x=9215` is `p=97, k=95, M(k)=2`, update `-2`. At `x=100488`, the assigned witness is reproduced exactly: `p=439, k=228, M(k)=3`, update `-4`. Further negative events occur at `p=443,449,457,461,463,1039,1049,...`. Pointwise post-root restoration is therefore unusable as an all-scale law.

## G. Proof impact and portfolio

1. **Verified finite carrier:** the strict lower endpoint and `max(c,floor((H^2+t)/c))` cutoff match literal occurrences throughout the tested domain.
2. **Rejected mechanism:** `c>T` alone has neither a fixed sign nor reliable control of the complete prefix.
3. **Highest-ranked survivor:** a source-independent upper bound for the complete compensated endpoint field, uniform in `K`, retaining `c=1`, every `c<=T` band, exact prime discrepancy, root-smooth complement, and distinct-owner cross terms before norms.
4. **Exact theorem candidate:** formalize `(MOVING)` for all `H>=3`, `T<=H-2`, `|t|<=T`, and `0<=K<=H`, including half-open walls and squareful `mu(c)=0`. This would be structural only, with no signed bound.
5. The canonical VF theorem and original #915 masked source remain separate.

## H. Continuation checkpoint

Do not rerun this identity or these completed tables unchanged. Next reconstruct the **joint** translated smooth/high source on the same `H,K,t` carrier. Decompose its exact mixed term by `c<=T` versus `c>T`, shared versus coprime owner ancestry, and endpoint birth/death. Freeze the candidate on a development root and test a held-out root at every `K`.

A useful falsifiable inverse candidate is: after adding the exact smooth compensator, positive excursions force concentration in a reciprocal-quotient set defined independently of the target amplitude. The complete complement must remain in the test. Failure would point back to a genuinely global mixed-moment theorem rather than a bounded exceptional-class argument.

No RH proof claim.
