# RH_Lean Prime Census Laboratory — 2026-10-15

## Provenance

- **Report date / run:** 2026-10-15, America/New_York; completed 2026-10-15T01:59:37-04:00.
- **Repository:** `OVVO-Financial/RH_Lean`.
- **Observed `main` HEAD:** `2ad3ee9a980cd73995a481cb9b2a9f58ea955108` (fresh at start and before publication).
- **Authority blobs:** `AGENTS.md` `32754063ff1540f966e576efe9c6df2ed9ac8543`; `CURRENT_PROOF_CONTRACT.md` `90510f021cf3dda5ab981fed22e7747306fa80be`; dynamic protocol `d7bde2d363338f5c9f357a47a8d57d5928f6c7f2`.
- **Formal source blobs inspected:** canonical target `43e160ac7ad51f7646771297f43a9b95395ce709`; signed seat source `13dda0d2c6cc59580959a2d59fad60126b1c6b0b`; one-block squarefree/squareful inlet `898942fd62457ed186c0b482ebceafe0f69fe4c0`; weighted active carrier `58b78186e4fd5b68179afe4be0b7b6e4761442d6`; active residual ledger `5fb512eceae989be6cd95c22c09e788c26c9d0ea`; restoring decomposition `41ca385cb2bd0706db21007e19cd2b0b1aaa4b3e`; historical multiplicity `fda6db056571191feffd08f2d1d6fe0fa02f0d8c`; sharp packet `134163c9d752ee767f2c4971da46cba2c1a58fff`; signed-pair bounds `e3cc17224469e24516390a8f20e590d5932dbfc1`.
- **Two-day continuity:** today Coordinator/Owner/Analytic/Referee/Lean were `TODAY=PENDING`; today Wheel blob `6d451c35eef4021fcff78253bed609d193c249c1` was consumed. Yesterday Coordinator `bf05965ed6adcac8ee9ae7d6066e047485baf945`, Owner `4f39c1690ee4cee0a00d4ebd0d08323f06d6c75d`, Analytic `3a6932d9c5e1474adf1f34374310c7b73eb71fc2`, Wheel `476d1af0f2624f615e7cdcb017812633dbd232f0`, Census `5cfe80753bbfa0374da9eace00b3a137aeaf43b8`, Referee `d4e0a25917843660a8010bc88558b73eb8d243ee`, and Lean `d6b39eee3a942f3c655d44c1c11e7f6433df9a68` were used as `YESTERDAY=CARRY_FORWARD`.
- **External inbox:** `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c`; EXT-20261014-1..5 were consumed at their stated scopes. No settled wheel or local-packet scan was repeated.
- **PR state:** draft PR #948, head `6316afbe4d7f1d982a409a36b56807865abb26f6`, base `2ad3ee9a...`, proposes the distinct Mertens-exponent-to-zero-strip route. At final refresh documentation CI was green while the dedicated exponent workflow and source audits were still in progress. It is not authority on `main` and no claim from it is used below.
- **Environment:** CPython 3.12.14; g++ 13.3.0; no Lean command executed.

## Current objective and exact carrier

The unique public target remains `VFCanonicalSquareVonKochStatement`:

```text
exists C >= 0, forall R >= 2,
  |vfCanonicalSquareDefect R| <= C * R * log R.
```

For this experiment, fix a natural endpoint root `R >= 3`. The exact raw odd-seat carrier is

```text
C_R = {(r,n): 2 <= r < R, r^2 < n < (r+1)^2, n odd}.
```

Each block contains exactly `r` seats and each seat has the compiled charge

```text
c(r,n) = w_r - 1_{n prime},
w_r = (2r+1) / (r * log(r^2+r+1/2)).
```

Thus `L_R = sum_(C_R) c(r,n)` is exactly the accumulated compiled odd-seat block source `sum_(2<=r<R)(vfMidBandMass r - P_r)`. It is not silently identified here with a differently normalized public defect. All squareful and higher-factor seats remain present.

## Mathematical mystery and competing hypotheses

Today’s Wheel report proves that one historical prime tag cannot be cloned and that every fixed local packet capacity has unbounded deficiency on the broad ancestry fibre. The unresolved question was whether literal source admission removes that obstruction.

- **H1 (fixed-capacity admission):** the actual raw source masks reduce per-tag demand enough that a once-only cap-four allocation could cover it.
- **H2 (factor-depth compensation):** many semiprime descendants are genuinely admitted; local tag packets leave a large residual, and the observed endpoint cancellation occurs mainly between factor-depth layers rather than within bounded tag packets.
- **Discriminator:** reconstruct the complete raw carrier, allocate every distinct semiprime `p*q` once to its larger historical prime `q`, retain the historical prime charge once, and restore every non-semiprime composite as a separate residual. Exact recombination must recover `L_R`.
- **Falsifier for H1:** any endpoint with source-admitted `d_R(q)>4`, while counting the historical prime once.
- **Unexpected third outcome:** a failed partition or nonzero conservation defect would expose a carrier/endpoint error.

## Claim 20261015-census-1 — exact no-cloning greatest-prime tag identity

**Status: PAPER_PROOF (elementary exact partition, not separately formalized).**

Let `P_R` be the odd primes `5 <= q < R^2`. For `q in P_R`, define

```text
X_R(q) = sum w_floor(sqrt(p*q))
```

over odd primes `p<q` with `p*q<R^2`, and

```text
Y(q) = 1 - w_floor(sqrt(q)),   G_R(q)=X_R(q)-Y(q).
```

Let `H_R` be the positive `w_r`-mass of every odd composite seat in `C_R` which is not a product of two distinct primes. Then

```text
L_R = sum_(q in P_R) G_R(q) + H_R.                 (TAG-DEPTH)
```

Proof: every prime seat contributes exactly `-Y(q)` once. Unique factorization assigns every squarefree semiprime `p*q`, `p<q`, to exactly one larger prime `q`. The remaining odd composites are precisely the squarefree factor-depth-at-least-three and squareful seats. These three classes are disjoint and exhaust `C_R`. No historical prime is cloned, and all diagonal/off-diagonal interactions can be restored by squaring the displayed complete sum; this identity itself asserts no quadratic bound.

The identity is a literal raw-seat admission result, but not an equality to the later clipped/admitted returned-pair carrier `vfMidActiveReturnedPairCarrier`; the latter still depends on first-owner cells and `sig`.

## Claim 20261015-census-2 — fixed cap four is refuted on the raw admitted source

**Status: REFUTED for H1 on `C_R`; not a refutation of a fully specified first-bad returned-cell theorem.**

At held-out `R=3162`, `X=9,998,244`, there are 1,555,106 source-admitted distinct semiprimes. The maximum tag demand is

```text
d_R(3187)=445.
```

There are 61,662 tags with `d_R(q)>4`; after allowing four descendants per once-only history, the exact unmatched occurrence count is

```text
sum_q max(d_R(q)-4,0) = 986,104.
```

At `R=3000`, the corresponding values are maximum 429 at `q=3001`, 55,971 deficient tags, and 888,339 unmatched occurrences. These are exact integer results. Hence source admission to the raw signed odd-seat carrier does not rescue bounded-capacity allocation. Masks/clips in a proposed returned-cell theorem would need an additional proved bridge and must carry the unmatched weighted residual and all cross terms.

## Claim 20261015-census-3 — factor-depth compensation is the dominant observed mode

**Status: FINITE_COMPUTATION.**

The table gives ordinary floating diagnostics; discrete populations are exact. `Tag` is prime plus distinct-semiprime mass, `Residual` is squarefree depth at least three plus squareful mass, and `Total=Tag+Residual`.

| R | prime seats | distinct semiprimes | depth>=3 squarefree | squareful | Tag | Residual | Total |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 500 | 22,042 | 44,099 | 35,175 | 23,433 | -10,245.977954 | 10,294.849002 | 48.871048 |
| 1,000 | 78,496 | 168,330 | 158,458 | 94,215 | -39,427.841772 | 39,556.245779 | 128.404007 |
| 2,000 | 283,144 | 641,751 | 696,248 | 377,856 | -151,458.416954 | 151,663.525159 | 205.108205 |
| 3,000 | 602,487 | 1,404,506 | 1,640,552 | 850,954 | -332,537.788683 | 332,723.895477 | 186.106794 |
| 3,162 held out | 664,475 | 1,555,106 | 1,832,580 | 945,379 | -368,057.434014 | 368,388.745488 | 331.311475 |

At `R=3162`, positive tag groups total `117,543.795270` and negative groups total `-485,601.229284`; the tag diagonal `sum G(q)^2` is about `2.527e6`, whereas `(sum G(q))^2` is about `1.355e11`. Thus neither favorable local signs nor a sum of tag squares represents the global signed statistic. The residual is numerically the leading compensator.

The near equality `Residual ~= -Tag` is not promoted to an independent RH-scale conjecture: bounding their mismatch by `O(R log R)` is the original endpoint difficulty in these coordinates. The useful new conclusion is negative and structural: bounded local tag packets omit the dominant compensating layer.

## Claim 20261015-census-4 — a sharp tag-sign boundary is a candidate inverse classifier

**Status: CONJECTURE supported by FINITE_COMPUTATION.**

For every tested endpoint `R in {500,1000,2000,3000,3162}`, the primes with `G_R(q)>0` form one initial prime segment; exactly one sign change occurs. Counts of positive tags were respectively 2,178; 5,946; 19,414; 39,512; and 43,538. At `R=2000`, the closest tested negative margin occurs at `q=217643`:

```text
X_R(q) = 0.83708160503731456674922758629865909727776973175197
Y(q)   = 0.83709831800397494964607835811336062912083385861722
G_R(q) = -0.000016712966660382896850771814701531843064126865254510.
```

This was recomputed with Python `Decimal` precision 80. It is a high-precision approximation, not a certified interval. A plausible theorem candidate is that for fixed `R`, `G_R(q)` is nonincreasing on prime tags `q>=R`; monotonicity of the admissible smaller-prime set and of `w_floor(sqrt(pq))` suggests an elementary proof. Even if proved, it is an inverse classification of coherent tags, not an endpoint bound.

## Methods and independent checks

The transparent Python reference used a smallest-prime-factor sieve, enumerated every odd seat in every strict open square block, factored each integer, and classified it as prime, distinct semiprime, squarefree depth at least three, or squareful. It checked exactly that every block contains `r` odd seats and that the four populations sum to `R(R-1)/2-1`.

The independent C++ program did not factor physical seats. It sieved primes, enumerated unordered distinct prime pairs `p<q` with `p*q<R^2`, reconstructed semiprime weights from `floor(sqrt(p*q))`, and inferred the residual from exact per-block candidate and prime counts. The implementations agreed exactly on every discrete count at `R=500,1000,2000,3000,3162`, including positive-tag and zero-descendant counts. At the held-out endpoint, double versus long-double weighted components differed by less than `1e-6`, while recombined totals differed by less than `4e-10`.

Executed commands:

```bash
python census_tag_ledger.py 500
python census_tag_ledger.py 1000
python census_tag_ledger.py 2000
python census_tag_ledger.py 3000
python census_tag_ledger.py 3162
g++ -O3 -std=c++20 census_tag_ledger.cpp -o census_tag_ledger
./census_tag_ledger 500
./census_tag_ledger 1000
./census_tag_ledger 2000
./census_tag_ledger 3000
./census_tag_ledger 3162
```

Final executed source hashes:

```text
915664d10d37650c25aec2535010ff3a0aef361da9b23c5836c646624b993f9d  census_tag_ledger.py
74be35fc10ba311244ae1907289af1d9434f94a0207aba6909597ff972e59581  census_tag_ledger.cpp
```

All discrete claims are exact. Logarithmic weights are numerical diagnostics; the only close sign was independently recomputed at 80 decimal digits. No finite result is an all-scale theorem.

## Mechanism portfolio and proof impact

- **Greatest-prime tag/depth identity:** CONTINUE as a clean exact reconstruction lemma. It exposes the correct once-only multiplicity and a complete residual; it is not a quantitative estimate.
- **Fixed-capacity Hall/packet allocation:** REJECT on the raw source. The held-out exact deficiency is large, and the all-scale ancestry obstruction from `20261015-wheel-2` remains decisive.
- **Factor-depth compensation:** REVISE. It is the dominant finite mode, but an `O(R log R)` mismatch theorem would be target-strength unless it uses a genuinely independent arithmetic input. The next useful question is whether a weaker provable transform identity couples the tag deficit to depth-at-least-three mass without restating the endpoint sum.
- **Tag-sign inverse classifier:** CONTINUE at low priority as an elementary theorem candidate; useful for locating coherent modes, insufficient for closure.
- **Draft Mertens exponent route #948:** DEFER to Referee/Lean CI. It is genuinely distinct, draft-only, and did not affect this experiment.

**Evidence classification for the run:** `FINITE_COMPUTATION`, with Claim 1 separately `PAPER_PROOF` and H1 `REFUTED` on the stated raw carrier. No canonical endpoint or RH proof claim.

## Downstream handoff

- **Owner / Analytic:** use `(TAG-DEPTH)` if pursuing signed tag arguments. Any bound must include `H_R` and the full cross term `2 H_R sum_q G_R(q)` after squaring; the local tag diagonal is not the global energy.
- **Finite Wheel:** raw source admission does not imply `d(q)<=4a(q)`; at `R=3162` it fails for 61,662 tags with 986,104 excess occurrences. Any surviving cap-four theorem must name the later clipped/admitted returned-cell carrier and prove its bridge.
- **Referee:** audit Claim 1’s scope distinction between raw odd seats and returned pair cells, and the exact cap-four falsifier.
- **Lean Verification:** Claim 1 is a possible exact Finset partition lemma only after Referee novelty review. Do not formalize the finite balance as an estimate or infer source payment.

## Next-run resume capsule

- Refresh `main`, PR #948, today/yesterday reports, and external inbox.
- Reuse the exact populations and code hashes above; do not rerun them unless definitions or endpoints change.
- First unresolved experimental question: derive and test a non-tautological transform relating `sum_q G_R(q)` to the depth-at-least-three/squareful residual, then attempt to falsify it on held-out endpoints and boundary-selected `R`.
- Preserve strict open-square endpoints, the complete odd carrier, one historical prime occurrence per tag, every distinct semiprime occurrence, squareful restoration, and all cross terms.
- Avoid presenting `Residual + Tag = O(R log R)` as a new smaller lemma; on this carrier it is the endpoint discrepancy in different coordinates.

## Final status

**Net-new result:** exact no-cloning tag/depth reconstruction, a raw-source cap-four counterexample at scale, and a reproducible factor-depth compensation diagnosis.

**Publication status:** initial report committed as `194562e8c111e658b432c5b10ec98240000f9b64` and read back byte-identical as blob `5ad0a19cd45af66d87d87f246cb76a6925a3875d` at 2026-10-15T02:02:13-04:00. This verification line is being appended in a final report-only commit and will be re-fetched.
