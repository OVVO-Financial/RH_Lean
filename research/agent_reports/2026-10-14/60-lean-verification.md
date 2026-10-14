# Lean Verification Report — 2026-10-14

## Run 1 — PARTIAL / IN_PROGRESS

- **Timestamp:** 2026-10-14T05:18:54-04:00 (America/New_York)
- **Invocation scope:** review-only for GitHub Lean source by direct user instruction; the only authorized write is this report.
- **Repository / branch authority:** `OVVO-Financial/RH_Lean` `main` commit `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`.
- **Authority reads:** `AGENTS.md` blob `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; `CURRENT_PROOF_CONTRACT.md` blob `f6e8dc6813ec63974489c26b0c383e34203f0aa9`.
- **Current objective:** audit supporting results against the canonical `VFCanonicalSquareVonKochStatement` route while preserving the raw signed VF carrier and the exact `sqrt(2)` phase correction. RH, finite A/C, CORR-4, and the genuine signed first-bad payment remain open.
- **Upstream reads currently available:** `30-finite-wheel.md` blob `e86a066b5fe4488972f9b49400ebb77d76cab41b`; `40-prime-census.md` blob `fc25130ac028c2556f1754ac75ee494c440e3dbc`; `50-adversarial-referee.md` blob `19e14164a9337af696ce0705a50e48e81248f93a`.
- **PENDING (GitHub 404 at refresh):** `00-coordinator-am.md`, `10-owner-payment.md`, `20-analytic-type-ii.md`.
- **Live PR queue:** no open pull requests returned.
- **Immediate task:** independently audit Claims `20261014-wheel-1..4` and `20261014-census-1..5`, the referee objections, the exact original carriers and source declarations, and whether any theorem remains both new and ready for formalization.
- **Current status:** `IN_PROGRESS`; no kernel-verification claim and no new theorem classification yet.


---

## Completed audit — 2026-10-14T05:24:07-04:00

### Final live-state refresh

- **Authority remains unchanged:** `main` commit `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`.
- **Central blobs:** `AGENTS.md` `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; `CURRENT_PROOF_CONTRACT.md` `f6e8dc6813ec63974489c26b0c383e34203f0aa9`.
- **Today's upstream reports read:** `30-finite-wheel.md` blob `e86a066b5fe4488972f9b49400ebb77d76cab41b`, Claims `20261014-wheel-1..4`; `40-prime-census.md` blob `fc25130ac028c2556f1754ac75ee494c440e3dbc`, Claims `20261014-census-0..5`; `50-adversarial-referee.md` blob `19e14164a9337af696ce0705a50e48e81248f93a`.
- **Still PENDING after a second explicit fetch:** today's `00-coordinator-am.md`, `10-owner-payment.md`, and `20-analytic-type-ii.md` each returned GitHub 404. No result is inferred for a missing stage.
- **Continuity read:** 2026-10-13 `00` blob `87a596f6f7bcb9bab6b2d29fc7c162c64ed544cb`, `10` blob `32f1574b8ade7dedc602b07b1b9257341320080a`, `20` blob `d9f73a0aab42e70ca30a17d16822a8281ca7afef`, and prior `60` blob `e3c413a3949ad685e5f8a344e934e0adc30c15ca`. These are navigation only.
- **Live open/draft PRs:** none.
- **Source-write scope:** direct user instruction forbids GitHub Lean-source, branch, issue, or PR modification in this invocation. No proof branch or PR was created.

### Current objective and exact open seam

The public target is `VFCanonicalSquareVonKochStatement`:

```text
exists C >= 0, forall R >= 2,
  |primeCounting(R^2) - vfMidFinishedMass(R) - sqrt(2)| <= C R log R.
```

The direct-VF arithmetic seam remains `VFMidDyadicSignedLateCorrectionStatement`, namely a uniform `O(A log A)` bound for

```text
lateRemoval(2,A,B) - lateReference(2,A,B),
2 <= A < B <= 2A.
```

The literal first-bad source-to-sector-six inlet and `VFMid915FirstBadSourcePaymentStatement` remain open. Finite A/C and CORR-4 remain sufficient alternatives, not proved inputs. The canonical `sqrt(2)` phase changes endpoint coordinates but not raw historical coefficients; any quadratic transfer must retain `-2*sqrt(2)*D_raw + 2`.

### Exact current-main carrier and dependencies audited

Relevant source blobs were fetched and inspected:

- `research/VF_MID_DYADIC_OWNER_PARITY_TWO.lean` `fb025b16bbbd6ca4bcf6288745c283aefa913218`;
- `research/VF_MID_DYADIC_OWNER_EXACT.lean` `95e7aa05b62861a19f0179aa529f817e3a402bba`;
- `research/VF_MID_DYADIC_PREFIX_OWNER.lean` `6757501bfc343d51ddb34483f8195da4a2c84047`;
- `research/VF_MID_DIRECT_ROUGH_CHILD.lean` `3da99cd7208ab97abb55d900c3703c65056bdea5`;
- `research/VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE.lean` `8419a4b858440427ed819f92a852bcf722c1b5a8`;
- `research/VF_MID_FIRST_BAD_SOURCE_TO_SECTOR_SIX_INLET.lean` `5d03f3080d014aba1e02485ae9c0b08988478c3c`;
- pinned `lean-toolchain` blob `c00a53503cc3cc776c290056ed21ce7e5d80b083`: `leanprover/lean4:v4.24.0`;
- `lake-manifest.json` blob `e7198c2f87e3cc2947190fca647deb93a6137b5a`.

For naturals `5 <= A <= R < 2A` and
`p ∈ vfMidSquareBandLateOwnerPrimes A R`, the physical fibre is exactly

```text
F(A,R,p) = {n : R^2 < n < (R+1)^2,
                 not n.Prime, n.minFac = p}.
```

The quotient carrier is
`vfMidSquareBandOwnerRoughChildren R p`. The existing exact bijective/cardinality bridge sends `n` to `q=n/p); the source proves `p <= q`, `q.Prime`, reconstruction `n=p*q`, and

```text
floor(R^2/p) < q <= floor(R^2/p)+4.
```

The strict physical endpoints come from `Finset.Ioo (R^2) ((R+1)^2)`; the quotient window is `Finset.Ioc`, so no square endpoint is silently included. The owner census partitions by `n.minFac`, hence physical occurrences are counted once. The run identity is

```text
lateRemoval(z,A,B)
 = sum_{R in [A,B)} sum_{p in LateOwners(z,R)} card(F(z,R,p)).
```

This is a positive unit-occurrence cardinality identity. It is not the raw signed historical source ledger.

### Independent proof audit: wheel-30 fibre cap

Define

```text
W30(t) = #{j in {1,2,3,4} : gcd(t+j,30)=1}.
```

For `t=floor(R^2/p)`, every quotient child `q` lies among `t+1,...,t+4`. Since `q >= p > A >= 5` and `q` is prime, it is divisible by none of `2,3,5), so `gcd(q,30)=1`. The quotient map is injective and preserves fibre cardinality. Therefore

```text
card(vfMidSquareBandCompositeOwner R p) <= W30(floor(R^2/p)).
```

No RH, finite A/C, CORR-4, signed-late-correction, source-payment, independence, density, or equidistribution premise occurs. The proof is mathematically complete.

For `5 <= A <= B <= 2A`, every `R ∈ [A,B)` satisfies `R<2A`. Summing the fibre bound through the exact disjoint owner census gives

```text
lateRemoval(A,A,B)
 <= sum_{R in [A,B)} sum_{p in LateOwners(A,R)}
      W30(floor(R^2/p)).
```

Using the definitional identity
`lateRemoval = prefixSupply - primeSupply` gives the correctly directed corollary

```text
prefixSupply(A,A,B) - wheelBudget(A,B) <= primeSupply(A,B).
```

This second argument also has no missing mathematical step.

### Proposed exact Lean declarations

A focused future proof PR may define a natural-valued four-slot capacity, then target statements equivalent to:

```lean
theorem vfMidSquareBandLateOwner_card_le_wheelThirty
    {A R p : ℕ} (hA : 5 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    (vfMidSquareBandCompositeOwner R p).card ≤
      vfMidFourSlotWheelThirtyCapacity (R ^ 2 / p)

theorem vfMidDyadicLateRemoval_start_le_wheelThirtyBudget
    {A B : ℕ} (hA : 5 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicLateRemoval A A B ≤
      ∑ r ∈ Finset.Ico A B,
        ∑ p ∈ vfMidSquareBandLateOwnerPrimes A r,
          (vfMidFourSlotWheelThirtyCapacity (r ^ 2 / p) : ℝ)

theorem vfMidDyadicPrimeSupply_ge_startPrefix_sub_wheelThirtyBudget
    {A B : ℕ} (hA : 5 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSupply A A B -
        ∑ r ∈ Finset.Ico A B,
          ∑ p ∈ vfMidSquareBandLateOwnerPrimes A r,
            (vfMidFourSlotWheelThirtyCapacity (r ^ 2 / p) : ℝ) ≤
      vfMidDyadicPrimeSupply A B
```

Names are proposals, not declarations on `main`. The mathematical status is `PAPER_PROOF`, not `PROVED_IN_LEAN`.

### Independent finite checks

Executed with CPython 3.12 using only integer arithmetic:

```text
W30 classes:
  0 -> [1,2,23,24]
  1 -> [0,3,4,5,6,7,8,11,12,13,14,17,18,19,20,21,22,25,26,29]
  2 -> [9,10,15,16,27,28]

(A,R,p)=(12,22,17): t=28, W30=2,
children=[29,31], products=[493,527], bound=True

(A,R,p)=(9,16,11): t=23, W30=0,
children=[], bound=True

repeated owner p=7: 77 and 91
repeated partner q=13: 91 and 143
```

This independently confirms the residue table, sharp two-child witness, zero-capacity witness, and multiplicity diagnostics. The unchanged large census through `A<=5000` and aggregate tables were reused from the independently reproduced referee result rather than rerun.

### Hidden-assumption and coefficient audit

1. **No circularity in Claims wheel-1/2.** They use only exact FTA ownership, proved child primality, four-slot geometry, and elementary divisibility.
2. **Unsigned/signed mismatch:** the wheel budget counts each physical composite with weight one. It does not contain the raw VF seat coefficient, current/historical sign, both walls, anchor, survivor/admission mask, clipping, returned-pair multiplicity, cross-owner term, or cumulative lower-child run.
3. **Cutoff mismatch:** `lateRemoval(A,A,B)` is the starting-prefix late tail. The production inlet uses cutoff `2` and the centered expression `lateRemoval(2,A,B)-lateReference(2,A,B)`. The wheel theorem cannot be substituted for it.
4. **No adaptive-average transfer:** the residues `floor(R^2/p) mod 30` form an owner-dependent sequence. Complete-period averages and finite observed ratios do not yield a uniform constant below two.
5. **History reuse remains unproved:** repeated owner and partner examples show why an edgewise use of a historical prime can duplicate payment. The examples are diagnostics until a source-tagged theorem is stated.
6. **No RH-equivalent premise is hidden in the accepted wheel proof.** Conversely, any claimed use of the wheel cap to prove the signed source payment without an exact coefficient-preserving splice would insert the missing RH-strength cancellation by hand.
7. **Existing wheel-30 novelty boundary:** current main already has the fixed physical `gcd(n,30)=1` carrier and exact run identities. The new content is the quotient-child four-slot capacity and its adaptive owner sum, not wheel-30 itself.

### Claim-by-claim recommendations

- **`20261014-wheel-1`: ACCEPT — `PAPER_PROOF`.** Exact all-scale fibre theorem on the genuine unit-weight owner carrier. Ready for formalization, not compiled.
- **`20261014-wheel-2`: ACCEPT — `PAPER_PROOF`.** Exact unsigned run budget and correctly directed prime-supply corollary. Ready for formalization, not compiled.
- **`20261014-wheel-3`: REVISE.** Split the compound submission. **REJECT / `REFUTED`** the universal one-child strengthening; **ACCEPT / `FINITE_COMPUTATION`** the exact two-child, zero-capacity, repeated-owner and repeated-partner examples; retain historical-reuse language as a diagnostic, not a proved source-ledger theorem.
- **`20261014-wheel-4`: ACCEPT — `FINITE_COMPUTATION` only.** The finite ranges and totals are not an all-scale distribution theorem.
- **`20261014-census-1`: ACCEPT — `PAPER_PROOF` plus separately scoped `FINITE_COMPUTATION`.**
- **`20261014-census-2`: ACCEPT — `PAPER_PROOF` for the summed inequality and `FINITE_COMPUTATION` for reported totals.**
- **`20261014-census-3`: ACCEPT — `FINITE_COMPUTATION`; REJECT the one-child strengthening.** Historical availability remains diagnostic.
- **`20261014-census-4`: ACCEPT — `FINITE_COMPUTATION`.** On the stated carrier `n=pq` with distinct primes, so `μ(n)=+1`; no signed-source conclusion follows. This run did not rerun the full C++ segmented implementation.
- **`20261014-census-5`: ACCEPT — `NO_NEW_RESULT`.** It correctly refuses an all-scale residue-dispersion or source-payment inference.

### Actual Lean/CI evidence and non-evidence

No new Lean source was created and the wheel declarations above were not compiled. Therefore there is **no** new command output, PR head, workflow run, warning audit, or axiom result for Claims wheel-1/2.

The immediate parity-two dependency is already on `main` and has exact historical CI evidence:

- merged PR #936; proof head `36a5a89900aefcccabcc7f5a913c88316001a6b0`; Actions checked PR merge ref `8f573bdf2028a42cc9e99be5e590219a21fb439c`;
- targeted run `38392575578`, job `115279722711`, success;
- command: `RHLEAN_RESEARCH_TARGETS=research/VF_MID_DYADIC_OWNER_PARITY_TWO.lean BUILD_LIBRARY=true python3 scripts/compile_research_import_closure.py`;
- output: `Build completed successfully (7486 jobs)`, `compiled=1 cached=10`; cache smoke test `compiled=0 cached=11`;
- printed axioms for the four public parity/triangular declarations: exactly `[propext, Classical.choice, Quot.sound]`;
- full source-audit run `38392575562`, hosted build job `115279722875`, success;
- command: `lake build RHLean > lean-build.log 2>&1`;
- output: `Build completed successfully (8199 jobs)`; `No RHLean-owned Lean warnings found.`

These results verify the unchanged parity dependency only. They do not kernel-verify the new wheel theorem.

### Mathematical classification and implementation status

- **Net-new accepted result:** Claims wheel-1 and wheel-2, `PAPER_PROOF`.
- **Formalization readiness:** YES; exact supporting theorem statements and complete proofs are available.
- **Kernel verification:** NO for the wheel claims.
- **GitHub workflow status:** no proof PR; no CI run for the wheel claims.
- **Production target:** `NO_NEW_RESULT`. The signed source inlet, source payment, canonical endpoint estimate, finite A/C, CORR-4, actual-prime admissibility, and RH remain open.
- **Why no implementation:** the direct user scope for this invocation forbids modifying GitHub Lean source, branches, issues, or pull requests. GitHub Actions is the only authorized Lean execution environment, and using it for a new theorem requires a proof PR; that action was out of scope.

### Remaining obligations for the 07:00 Coordinator

1. Carry Claims wheel-1/2 as accepted supporting lemmas at `PAPER_PROOF`, not as `PROVED_IN_LEAN` and not as production closure.
2. Preserve the refutation of the universal one-child strengthening.
3. Keep today's `00/10/20` stages `PENDING` unless they are actually published before the Coordinator refresh.
4. Highest-value structural obligation: `SOURCE-SPLICE-1`, an exact occurrence-, coefficient-, sign-, mask-, clipping-, owner-, anchor-, cross-term-, and chronology-preserving equality from the actual first-bad source to the compensated ledger.
5. Prove `HISTORY-AVAILABILITY`: separately tag source occurrences so no negative historical contribution is spent more often than supplied.
6. If an aggregate improvement below the parity constant is required, prove `W30-RESIDUE-DISPERSION` on the adaptive actual owner residues; averages and finite ratios are insufficient.
7. On a later source-write-authorized invocation, formalize the three proposed declarations in one focused proof PR and require targeted warning-fatal compilation, full source audits, no-holes checks, and explicit axiom output.

## Next-run resume capsule

- **Checkpoint:** 2026-10-14T05:24:07-04:00.
- **Authority:** main `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`; `AGENTS.md` `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; contract `f6e8dc6813ec63974489c26b0c383e34203f0aa9`.
- **Upstream consumed:** wheel blob `e86a066b5fe4488972f9b49400ebb77d76cab41b`, census blob `fc25130ac028c2556f1754ac75ee494c440e3dbc`, referee blob `19e14164a9337af696ce0705a50e48e81248f93a`; today's `00/10/20` PENDING.
- **Accepted new claims:** `20261014-wheel-1` and `-2`, `PAPER_PROOF`, exact statements above.
- **Rejected/revised:** universal one-child bound `REFUTED`; historical-reuse inference remains diagnostic without source tags.
- **Reused evidence:** unchanged main/source blobs; referee's exact `A<=5000` scan; PR #936 dependency CI at head `36a5a899...`.
- **New local check:** exact W30 residue table and the four named witnesses reproduced with CPython 3.12.
- **Open PRs:** none.
- **First unresolved production premise:** `SOURCE-SPLICE-1`, followed by history availability and the signed late-correction/source-payment estimate.
- **Next action:** if source writes are authorized, formalize the wheel fibre and run lemmas on `agent/lean-verification/YYYYMMDD-short-topic`; otherwise audit any newly published owner/analytic report for an exact weighted bridge.
- **Avoid:** treating unit-weight capacity as signed payment, using cutoff `A` as cutoff `2`, averaging adaptive residues, or claiming kernel verification for the uncompiled wheel claims.


## Publication verification

- **Completed audit content commit:** `8469f35e341d8aebaa273db456093a6695a3d596`.
- **Completed audit blob read back:** `d55c9a8d9bb85a17bafdae86fb39b699886c3bbd`.
- **Readback:** exact 16,408-character match; completed audit and final resume capsule present.
- **Publication status:** `COMPLETED`.
