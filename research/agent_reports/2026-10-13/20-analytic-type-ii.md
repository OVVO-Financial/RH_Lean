# RH_Lean agent daily report — 2026-10-13 / RH | Analytic Type II

## Provenance

- **Report date (America/New_York):** 2026-10-13
- **Agent / stage:** RH | Analytic Type II / `20-analytic-type-ii.md`
- **Scheduled start:** 09:00 ET
- **Run ID / sequence:** 2026-10-13T09:07:17-04:00 / first run of this date
- **Actual execution / completed time:** IN_PROGRESS
- **Previous own checkpoint:** 2026-10-12 report absent; PENDING
- **Warm-start cache status:** central authority refreshed; prior specialist checkpoint absent; owner-fibre claims require revalidation at the fresh main merge
- **Observed `main` HEAD SHA:** `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`
- **Central contract fetched:** SUCCESS: `main:AGENTS.md` blob `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; `main:CURRENT_PROOF_CONTRACT.md` blob `f6e8dc6813ec63974489c26b0c383e34203f0aa9`
- **Report target:** `agent-reports:research/agent_reports/2026-10-13/20-analytic-type-ii.md`
- **Previous upstream reports actually read:** `2026-10-13/00-coordinator-am.md`; `2026-10-13/10-owner-payment.md` blob `d60ca9e416c70faa1a4bce60291c73daf82d0366`; prior own report PENDING
- **Execution environment/tools used:** GitHub connector read/write; local arithmetic computation available; web/literature review pending; no Lean execution
- **Publication status:** INITIAL_CHECKPOINT
- **Early durable checkpoint:** this commit, subject to immediate readback verification

## Current central research objective

Prove `VFCanonicalSquareVonKochStatement`, equivalently a uniform bound
`|vfCanonicalSquareDefect R| <= C * R * log R`. The assigned analytic seam is the exact chronological-owner proposition `VFMidDyadicSignedLateCorrectionStatement`: uniformly for `2 <= A < B <= 2*A`, bound
`|vfMidDyadicLateRemoval 2 A B - vfMidDyadicLateReference 2 A B|`
by `C*A*log A`, or isolate a rigorous obstruction on its literal carrier.

## Work performed today

Authority and reporting protocol were refreshed. Current main includes merged PR #936 (parity-two late-owner fibres). No open/draft PR exists. The investigation will recover the exact coefficient definitions and compare the literal centered prefix-wheel carrier with the owner report's unsigned fibre restrictions; it will not infer a signed estimate from unit counts.

## Claims and evidence

### Claim 20261013-analytic-0

- **Exact quantified statement and original carrier:** research in progress on the exact `vfMidDyadicLateRemoval 2 A B - vfMidDyadicLateReference 2 A B` carrier.
- **Status:** PENDING
- **Independent mathematical ingredient:** none claimed at checkpoint.
- **Precise first unproved lemma or limit:** exact coefficient-preserving decomposition and identification of any coherent mode exceeding the required `A log A` scale.
- **What changed relative to current known baseline:** fresh main merged the two-slot late-owner fibre theorem; its relevance to the centered signed inlet remains unproved.

## Downstream handoff

- **Claims ready for census:** pending exact quantified candidate.
- **Claims ready for independent referee:** pending.
- **Claims ready for Lean:** none.
- **Missing inputs or upstream stages:** prior own report PENDING.
- **Next action / priority:** inspect exact Lean definitions, derive/falsify a sharp analytic restriction, and append a completed report.

## Final report summary

**Net-new mathematical progress:** NONE at initial checkpoint  
**Completeness:** PARTIAL  
**No RH-proof claim:** yes


---

## Completed analytic update - 2026-10-13T09:13:00-04:00

### Provenance refresh and exact declarations

The final audit rechecked `main` at `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`; it remained unchanged. Relevant blobs are:

- `research/VF_MID_DYADIC_PREFIX_OWNER.lean`: `6757501bfc343d51ddb34483f8195da4a2c84047`.
- `research/VF_MID_DYADIC_OWNER_EXACT.lean`: `95e7aa05b62861a19f0179aa529f817e3a402bba`.
- `research/VF_MID_DYADIC_OWNER_PARITY_TWO.lean`: `fb025b16bbbd6ca4bcf6288745c283aefa913218`.
- `research/VF_CANONICAL_ALL_REAL_LI_O_ONE.lean`: `f7c1cf3890e99acc6629084574c0e38bc2f60959`.
- `research/VF_CANONICAL_SQRT_TWO.lean`: `b504704070b193cea835713d697ba0d980704c7a`.

The coordinator report (blob `87a596f6f7bcb9bab6b2d29fc7c162c64ed544cb`) used the previous main head `7ff5ff9e...`; its assignment remains consistent with the unchanged contract, but declaration claims were rechecked on the newer head. The owner report (blob `d60ca9e416c70faa1a4bce60291c73daf82d0366`) supplied claims `20261013-owner-2` and `-3`; they were treated as reports requiring independent checking. No open/draft PR was found.

### Exact arithmetic carrier, endpoints, coefficients, and target

For natural `2 <= A < B <= 2*A`, write

```text
T_2(A,B) = vfMidDyadicLateRemoval 2 A B
H_2(A,B) = vfMidDyadicLateReference 2 A B
Delta(A,B) = T_2(A,B) - H_2(A,B).
```

The physical carrier is exactly

```text
T_2(A,B)
 = sum_{A <= r < B} sum_{p in LateOwnerPrimes(2,r)}
     card(CompositeOwner(r,p)).
```

Each occurrence is an integer `n` with `r^2 < n < (r+1)^2), surviving the prefix prime 2, and owned once by its least prime factor `p>2`; the coefficient is the unit multiplicity `+1). Square endpoints are excluded in the owner blocks; prime supply is `pi(B^2)-pi(A^2)), and the endpoints are composite for `A,B>=2).

The exact parity identities on current main give

```text
PrefixSupply(2,A,B) = (1/2) * InteriorLength(A,B),
density(2) = 1/2,
Delta(A,B) = VFMass(A,B) - PrimeSupply(A,B)
           = -(primeError(B^2)-primeError(A^2)).
```

Thus all sign information in the inlet is the centering of a positive once-owned composite census by the VF reference. There is no additive exponential phase. Any Vaughan/Heath-Brown expansion of the equivalent prime sum has the sharp hyperbolic cutoff `A^2 < mn <= B^2`; Type I/II cancellation must come from arithmetic coefficients such as `mu(m)`, not from phase variation. Near either hyperbola wall the cutoff is stationary and coherently signed, so a formal bilinear decomposition is not itself a saving.

An elementary exact trivial estimate is

```text
|Delta(A,B)| <= VFMass(A,B) + PrimeSupply(A,B)
             <= 2*(B^2-A^2) <= 6*A^2.
```

Here each VF block mass is `(2r+1)/log(r^2+r+1/2) <= 2r+1` for `r>=2), and prime supply is at most the number of integer sites. The required `C*A*log A` is therefore a power-scale improvement by a factor comparable to `A/log A`.

### Claim 20261013-analytic-1 - unconditional zero-free-region benchmark

- **Status:** `PAPER_PROOF` (transfer from a standard unconditional PNT theorem; not formalized here).
- **Exact quantified statement:** There exist absolute constants `A0>=3`, `K>0`, and `c>0` such that for every natural `A,B` with `A0<=A<B<=2*A`,
  ```text
  |Delta(A,B)| <=
    K*A^2*exp(-c*(log A)^(3/5)*(log log A)^(-1/5)).
  ```
- **Proof:** Put `L(x)=int_2^x dt/log t` and `e_R=vfMidFinishedMass R-L(R^2)`. The compiled all-real quadrature theorem gives `|e_R|<=Q` for one absolute `Q`. The exact carrier identity gives
  ```text
  Delta(A,B)
   = (L(B^2)-pi(B^2))-(L(A^2)-pi(A^2))+(e_B-e_A).
  ```
  Apply the Vinogradov-Korobov prime-number-theorem error separately at `A^2` and `B^2`; use `B^2<=4A^2`, decrease `c` if needed, and absorb `2Q` and the finite initial range into `K`.
- **Literature actually inspected:** D. Platt and T. Trudgian, *The error term in the prime number theorem*, Math. Comp. 90 (2021), arXiv:1809.03134, Corollary 2 gives the explicit direct bound `|pi(x)-li(x)| <= 235 x (log x)^0.52 exp(-0.8 sqrt(log x))` for `log x>=2000`; their discussion after Corollary 2 records the sharper Vinogradov-Korobov asymptotic shape used above: https://arxiv.org/abs/1809.03134. The zero-free-region provenance was cross-checked in H. Montgomery and R. Vaughan, *Multiplicative Number Theory I*, Chapter 6, especially the historical discussion around (6.24): https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/10.0_pp_168_198_The_Prime_Number_Theorem.pdf. A recent stronger constant-level preprint was inspected but is not needed for this claim: C. Bellotti, arXiv:2508.02041, Theorem 1.2 and equations (1.3)-(1.4): https://arxiv.org/abs/2508.02041.
- **Saving and mismatch:** This is a super-logarithmic saving over `A^2`, but not a power saving. Since
  ```text
  A^2 exp(-c(log A)^(3/5)/(log log A)^(1/5)) / (A log A) -> infinity,
  ```
  it remains asymptotically much larger than the required bound.
- **Dependencies/uniformity:** Absolute constants; sharp endpoints are allowed because the PNT theorem concerns the unsmoothed counting function. No coefficient-norm, modulus, or short-interval transfer is being hidden. The proof uses two endpoint estimates, so it is uniform in every `B` in the required range.
- **Novelty/circularity:** This is a benchmark on the exact carrier, not a new PNT theorem. It is unconditional and noncircular, but quantitatively insufficient.

### Claim 20261013-analytic-2 - exact cutoff partition and short-run restriction

- **Status:** `PAPER_PROOF`.
- **Definitions:** For `A>=3` define the early-owner unit census
  ```text
  E_early(A,B) =
    sum_{A <= r < B}
      sum_{p in LateOwnerPrimes(2,r), p<=A}
        card(CompositeOwner(r,p)).
  ```
  Put `d=B-A`.
- **Exact quantified statement:** For every `3<=A<=B<=2*A`,
  ```text
  T_2(A,B) = E_early(A,B) + T_A(A,B)
  ```
  with literal preservation of every integer occurrence and its least-prime owner. Consequently,
  ```text
  |Delta(A,B)|
    <= |E_early(A,B)-H_2(A,B)| + d*(d-1).
  ```
  In particular, if `d^2<=A*log A`, the entire `p>A` tail is already affordable:
  ```text
  |Delta(A,B)| <= |E_early(A,B)-H_2(A,B)| + A*log A.
  ```
- **Proof:** For every owner prime `p>2), exactly one of `p<=A` and `p>A` holds. This is a disjoint signed reindexing of the existing least-prime-owner sum, not a change of carrier. The second term is exactly `vfMidDyadicLateRemoval A A B`. It is nonnegative and the merged current-main theorem `vfMidDyadicLateRemoval_start_le_two_triangular` proves `T_A(A,B)<=d(d-1)`. Apply the triangle inequality; under `d^2<=A log A`, use `d(d-1)<=d^2`.
- **What it improves:** It precisely localizes the hard carrier on short runs to the early owners `2<p<=A`. It does not assert cancellation there and does not solve long runs where `d` is comparable to `A`.
- **Boundary audit:** `p=A` belongs to the early piece; the tail is strictly `p>A`. The square-block and run endpoints remain those of the original `Ico A B` owner census. There is no smoothing or truncation error.

### Claim 20261013-analytic-3 - one-block falsification of a late-tail-only proof

- **Status:** `REFUTED` for the proposed implication "control of `p>A` fibres alone controls `Delta`".
- **Exact statement:** For every `A>=3`, `T_A(A,A+1)=0), because Claim 2 has `d(d-1)=0` and the census is nonnegative. Nevertheless
  ```text
  Delta(A,A+1)
   = (2A+1)/log(A^2+A+1/2)
     - (pi((A+1)^2)-pi(A^2)),
  ```
  which is not identically zero.
- **Exact counterexample:** At `A=3,B=4`, prime supply is two (`11,13`) and
  `Delta=7/log(25/2)-2>0`. Indeed `log(25/2)<7/2): the exponential series gives `exp(7/2)>1+7/2+(7/2)^2/2+(7/2)^3/6>25/2`. Thus the target is nonzero while the entire `p>A` carrier is empty.
- **Consequence:** PR #936's two-slot bound and any residue refinement of that tail cannot by themselves establish even the one-block instance of the signed inlet. The early-owner centered discrepancy is unavoidable.

### Type I/II and sharp-cutoff assessment

A Vaughan or Heath-Brown identity can rewrite a log-weighted prime increment as Type I and Type II sums, schematically
```text
sum_{A^2<n<=B^2} Lambda(n)
 = sum_{mn in (A^2,B^2]} alpha_m beta_n + Type-I terms,
```
with Möbius/logarithmic coefficients and exact sharp walls. There is no oscillatory factor `e(alpha mn)`; fixing `m` produces one ordinary interval in `n`. Cauchy-Schwarz and divisor-norm estimates alone therefore recover at best generic square-root estimates for already oscillatory coefficient families, while the diagonal/coherent zero-frequency mode is exactly the prime-number-theorem error. Removing that mode to size `O(A log^2 A)` in the Chebyshev currency would be RH-scale input, not an independently available Type II theorem.

The merged fibre cap concerns only `T_A`, an unsigned subcarrier. Taking absolute values before combining it with `E_early-H_2` loses the very signed centering required by `Delta`. Smooth averages, Bombieri-Vinogradov averages over moduli, and generic large-sieve bounds do not transfer to this fixed sharp no-modulus carrier without a new theorem; none was used.

### Falsification and finite diagnostics

A Python 3.12 SPF/sieve calculation enumerated exact primes through `4,000,001` and evaluated the literal one-block formula for all `3<=A<2000`. Representative `(A, primeSupply, VFmass, Delta)` values were:

| A | prime supply | VF mass | Delta |
|---:|---:|---:|---:|
| 3 | 2 | 2.771477456921 | 0.771477456921 |
| 5 | 2 | 3.218513654922 | 1.218513654922 |
| 22 | 7 | 7.225985425513 | 0.225985425513 |
| 100 | 23 | 21.799629460214 | -1.200370539786 |
| 1000 | 152 | 144.826726808433 | -7.173273191567 |

The maximum observed `|Delta|/(A log A)` on this finite range was about `0.23407635` at `A=3`. These numbers are `FINITE_COMPUTATION` diagnostics only. They falsify neither the target nor an all-scale constant and are not used in Claims 1-3.

### Explicit bridge to the original arithmetic

1. **Exact equality:** `Delta=T_2-H_2` by definition.
2. **Exact equality:** `T_2` is the chronological, once-owned least-prime-factor census with unit coefficients.
3. **Exact equality:** parity prefix cancellation gives `Delta=VFMass-PrimeSupply`.
4. **Signed reindexing:** Claim 2 partitions every physical occurrence into `2<p<=A` or `p>A), retaining signs (all `+1` before centering), owner multiplicity, both square walls, and the complete historical order `A<=r<B`.
5. **Inequality:** only the `p>A` piece is replaced by the triangular upper bound.
6. **Unproved transfer lemma:** No equality has been established from this scalar unit census to `vfMidFirstBadDecompressedHistoricalSource` or the #903 pair ledger. The latter contains raw VF weights, historical parent/child occurrence tags, survivor/admission masks, clipping at both walls, anchor terms, cross terms, and cumulative lower-child runs. None appears in `Delta)'s unit census. Therefore Claims 1-3 do not prove `VFMid915FirstBadSourcePaymentStatement` and cannot be substituted for an occurrence- and coefficient-preserving source splice.

### Established / not established / first missing lemma

**Established:**

- `20261013-analytic-1`: an unconditional sharp-carrier PNT benchmark with Vinogradov-Korobov shape.
- `20261013-analytic-2`: exact early/late owner partition and the short-run restriction `d^2<=A log A`.
- `20261013-analytic-3`: a rigorous `A=3,B=4` counterexample to every late-tail-only control of the signed inlet.
- Exact identification of the zero-frequency/coherent mode that a Type I/II proof must control.

**Not established:**

- The required `O(A log A)` signed late correction.
- Any power saving over the unconditional PNT error.
- An ownerwise deterministic reference whose early and late pieces separately retain the necessary cancellation.
- Any bridge to #915's weighted historical source, clipping, cross terms, or sector-six pair ledger.
- RH, finite A/C, CORR-4, or actual-prime owner admissibility.

**First missing lemma:** On the exact cutoff partition, construct an ownerwise centered reference
`H_2=H_early+H_late+O(A)` by a proved equality/controlled endpoint error, with no duplicated occurrence, and prove a genuinely new joint signed estimate
```text
|(E_early-H_early)+(T_A-H_late)| <= C*A*log A
```
uniformly for `2<=A<B<=2A`. The analytic input must be independent of the desired prime-versus-VF bound. Without this reference split, applying Type I/II machinery to a surrogate Möbius form has no verified transfer back to the original carrier.

### Downstream handoff

- **Prime Census Laboratory (1 PM):** Reproduce Claim 3 at `A=3`; enumerate the exact partition `T_2=E_early+T_A` for all `3<=A<=R<2A` through a declared larger range; record `E_early-H_2`, `T_A`, and `Delta` separately for every contiguous `[A,B)). Focus on the transition `d^2=A log A`, worst normalized short-run residuals, and any endpoint mismatch at `p=A`. Preserve integer occurrence multiplicity before aggregating.
- **Adversarial Referee (3 PM):** Check the cutoff partition, the use of the merged triangular theorem, the exact `A=3` exponential inequality, normalization of `Li_2`, and the PNT transfer's monotonic-envelope step. Reject any claim that the short-run reduction supplies early-owner cancellation or that an averaged/smoothed Type II theorem applies to the sharp carrier.
- **Lean Verification (5 PM):** Claim 2 is suitable as a small exact partition/short-run lemma on existing owner declarations if independently accepted. Claim 3's structural zero-tail theorem is already an immediate consequence of the triangular theorem; no proof PR is requested by this agent.
- **Coordinator:** Preserve the distinction between the unsigned late tail and the centered whole inlet. The new two-slot theorem narrows one subcarrier but leaves a demonstrably nonzero target when that subcarrier is empty.

## Updated final report summary

**Net-new mathematical progress:** exact short-run owner restriction and a rigorous one-block obstruction; unconditional PNT benchmark on the literal carrier.  
**Completeness:** DONE_NO_NEW_RESULT for the required `O(A log A)` theorem; useful `PAPER_PROOF` restrictions and `REFUTED` shortcut.  
**No RH-proof claim:** yes.

## Next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** 2026-10-13T09:13:00-04:00.
- **Source freshness:** main `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`; contract blob `f6e8dc6813ec63974489c26b0c383e34203f0aa9`; prefix-owner `6757501b...`; owner exact `95e7aa05...`; parity-two `fb025b16...`.
- **Upstream consumed:** coordinator blob `87a596f6...` (older head but compatible assignment); owner blob `d60ca9e...`, especially claims owner-2/-3; previous own report PENDING.
- **Completed evidence worth reusing:** claims `20261013-analytic-1` through `-3`; exact `A=3,B=4` counterexample; finite one-block scan `3<=A<2000`.
- **Invalidations / uncertain results:** Bellotti 2025 is a recent preprint and was not needed; the PNT benchmark is not formalized in Lean. No source bridge to #915 exists.
- **First unresolved blocker:** ownerwise reference split and a noncircular signed early-plus-late estimate on the exact occurrence carrier.
- **Next highest-value step:** consume the independent census/referee verdicts, then test whether an exact Boolean-face/Mobius expansion supplies an ownerwise reference without sharp-boundary loss.
- **For Agent #7:** no open/draft PR; only the exact partition/short-run lemma is potentially formalization-ready after review.
- **Avoid next run:** reusing the two-slot fibre cap as whole-carrier cancellation, repeating the one-block scan without a larger or differently targeted range, or importing a PNT/RH-scale Type II estimate under a new name.
+
---

## Continuation - 2026-10-13T09:16:37-04:00

### Freshness and correction

Immediately before this continuation, authority was re-fetched successfully at unchanged
`main` HEAD `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`:
`AGENTS.md` blob `709ad61bf4555fe4f2c92af3fd42f3994798c8bf` and
`CURRENT_PROOF_CONTRACT.md` blob
`f6e8dc6813ec63974489c26b0c383e34203f0aa9`. This section preserves all
earlier material. There were still no open or draft PRs.

The earlier bound `|Delta(A,B)| <= 6*A^2` is valid but unnecessarily loose.
Because both `VFMass(A,B)` and `PrimeSupply(A,B)` lie in
`[0,B^2-A^2]`, the exact identity
`Delta=VFMass-PrimeSupply` gives the sharper elementary bound

```text
|Delta(A,B)| <= B^2-A^2 <= 3*A^2
```

for `2<=A<B<=2*A`. For the VF term, use
`(2r+1)/log(r^2+r+1/2) <= 2r+1` for `r>=2` and telescope
`sum_(A<=r<B)(2r+1)=B^2-A^2`. This correction changes no earlier verdict.

### Claim 20261013-analytic-4 - a quadratic-over-log-squared late-tail obstruction

- **Status:** `PAPER_PROOF`, with a separate `FINITE_COMPUTATION` diagnostic.
- **Exact carrier:** the literal positive unit-occurrence tail
  
  ```text
  T_A(A,2A) = sum_(A<=r<2A) sum_(p in LateOwnerPrimes(A,r))
                card(CompositeOwner(r,p)).
  ```
  
  Every summand retains its physical integer, square block, least-prime owner,
  and multiplicity one.
- **Exact quantified statement:** There is an absolute integer `A0` such that
  for every integer `A>=A0`,
  
  ```text
  T_A(A,2A) >= A^2 / (1000*(log A)^2).
  ```
  
  Consequently, any proof which takes absolute values of the `p>A` owner
  fibres before installing a matching signed decomposition of the reference
  has variation at least this large. Its ratio to the required `A log A`
  scale is at least `A/(1000*(log A)^3)`, which tends to infinity.
- **Injection proof:** Let
  
  ```text
  P_A = {p prime : 6A/5 < p <= 5A/4},
  Q_A = {q prime : 3A/2 < q <= 8A/5}.
  ```
  
  For every `(p,q) in P_A x Q_A`, the integer `n=pq` has least prime
  factor `p>A`, the factors are distinct, and
  
  ```text
  A^2 < (9/5)*A^2 < n <= 2*A^2 < 4*A^2.
  ```
  
  Hence `n` is not a square and lies in exactly one open physical block
  `r^2<n<(r+1)^2` with `A<=r<2A`; it is one occurrence in the displayed
  late-owner carrier. Unique factorization makes the map `(p,q) -> n`
  injective. The prime number theorem in fixed proportional intervals gives
  `#P_A ~ A/(20 log A)` and `#Q_A ~ A/(10 log A)`. For all sufficiently
  large `A`, these are at least `A/(40 log A)` and
  `A/(20 log A)`, respectively, so their product is at least
  `A^2/(800*(log A)^2)`, which implies the stated conservative constant.
- **Endpoint and phase audit:** The products are strictly above `A^2`,
  strictly below `(2A)^2`, and cannot hit an intermediate square. The owner
  cutoff is strict `p>A`. No smoothing, dyadic overlap, additive phase,
  omitted diagonal, or endpoint error occurs.
- **Literature actually examined for the only asymptotic input:** NIST DLMF
  section 27.12, equation 27.12.6 records the Vinogradov-Korobov PNT error
  
  ```text
  |pi(x)-li(x)| = O(x*exp(-d*(log x)^(3/5)*(log log x)^(-1/5))),
  ```
  
  citing Korobov (1958) and Vinogradov (1958):
  https://dlmf.nist.gov/27.12#E6. This is more than sufficient for the two
  fixed-interval prime asymptotics. Platt-Trudgian, *The error term in the
  prime number theorem*, Math. Comp. 90 (2021), Theorem 1 and Corollary 1,
  was also inspected at https://arxiv.org/abs/1809.03134; its explicit
  Chebyshev bounds are not needed for the existential `A0`.
- **Attempted falsification:** A Python 3.12 Eratosthenes sieve enumerated all
  pairs in the two boxes and verified, for each pair, `p<q`,
  `A<p<=floor(sqrt(pq))<2A`, strict square-band placement, and injectivity.
  Results were:

  | A | #P | #Q | injected occurrences | normalized count `N log^2(A)/A^2` |
  |---:|---:|---:|---:|---:|
  | 500 | 5 | 7 | 35 | 0.00540699 |
  | 1,000 | 8 | 12 | 96 | 0.00458084 |
  | 5,000 | 29 | 57 | 1,653 | 0.00479652 |
  | 10,000 | 54 | 108 | 5,832 | 0.00494731 |

  The executed algorithm was a bytearray sieve through `2A`, followed by
  the literal rational endpoint tests `5p>6A, 4p<=5A, 2q>3A, 5q<=8A`
  and `math.isqrt(pq)` square-wall checks. The finite table is diagnostic
  only; the proof is the injection plus PNT.
- **Meaning and limit:** This does not refute the signed
  `O(A log A)` target. It proves that the merged two-slot theorem cannot be
  summed by absolute values to reach that target, even after its constant is
  improved: there are genuinely too many positive physical occurrences.
  Cancellation must pair this population with an exact ownerwise share of
  `H_2`, or occur in a joint early-plus-late signed identity before norms.

### Original-source bridge audit for Claim 4

1. **Signed subcarrier inclusion:** each injected `pq` is a literal
   `+1` occurrence in `T_A(A,2A)`, hence in the exact partition of
   `T_2(A,2A)`. Least-prime ownership prevents duplication.
2. **Exact scalar reassembly:** `Delta=T_2-H_2=VFMass-PrimeSupply`; the
   canonical `sqrt(2)` phase cancels between endpoints.
3. **No transfer asserted:** the injection carries no raw VF seat weight,
   historical parent/child tag, survivor/admission mask, clipped exit,
   anchor cross term, pair interaction, or lower-child run. Therefore it
   cannot be charged directly to the #903 safe/sector-six ledger and does
   not prove `VFMid915FirstBadSourcePaymentStatement`.
4. **First missing lemma:** before any Type I/II norm, construct an exact
   owner-indexed decomposition of `H_2` and of the weighted original source
   on the same occurrences, including both clipping walls and all historical
   multiplicities/cross terms, so that the two prime boxes above are canceled
   or descended without ownerwise absolute values.

### Updated downstream requests

- **Prime Census Laboratory:** independently reproduce the two-box injection,
  then measure what fraction of `T_A(A,2A)` it captures through a declared
  range. For every injected `pq`, retain `(A,r,p,q,n)` and test any
  proposed ownerwise reference/source map for exact multiplicity and weight.
  Search especially for endpoint mistakes caused by rational rounding.
- **Adversarial Referee:** verify the fixed-box PNT constants, strict open-wall
  placement, unique-factorization injection, and the logical scope: the claim
  obstructs termwise absolute values but does not lower-bound
  `|T_2-H_2|`.
- **Lean Verification:** the finite injection can be stated elementarily on
  the current owner carrier, but its PNT cardinality lower bound requires
  analytic infrastructure not presently identified in the repository. No
  proof PR is requested.
- **Research Coordinator:** treat Claim 4 as a method obstruction and carrier
  stress test, not as progress toward the signed target itself.

## Final continuation summary

**Established:** `PAPER_PROOF` that the genuine late-owner tail contains
`>= A^2/(1000 log^2 A)` physical occurrences for all sufficiently large
`A`, and the sharper trivial whole-correction bound `3A^2`.

**Not established:** cancellation of those occurrences against the VF
reference; the required `O(A log A)` estimate; the weighted source splice;
source payment; owner admissibility; finite A/C; CORR-4; or RH.

**First missing lemma:** an occurrence- and coefficient-preserving ownerwise
reference/source decomposition that keeps the prime-box population inside a
joint signed sum until after cancellation or strict lower-run descent.

## Updated next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** 2026-10-13T09:16:37-04:00.
- **Source freshness:** unchanged main
  `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`; central blobs
  `709ad61b...` and `f6e8dc68...`; exact carrier blobs unchanged.
- **Upstream consumed:** coordinator `87a596f6...`; owner
  `d60ca9e...`; prior own report absent; continuation appended to report blob `dfbd8546ac7550ed2c39cfcb629bc644f8b48cd4`.
- **Completed evidence worth reusing:** Claims
  `20261013-analytic-1` through `-4`; especially the exact cutoff
  partition, one-block late-tail counterexample, and two-prime-box injection.
- **Invalidations / uncertain results:** no source invalidation. The
  asymptotic threshold `A0` is existential, not computed. The lower bound
  concerns total variation, not the centered correction.
- **First unresolved blocker:** exact ownerwise reference plus weighted
  historical-source splice before absolute values.
- **Next highest-value step:** test a literal Boolean-face/Mobius
  owner-indexed reference on the injected prime boxes and demand exact
  equality before estimating it.
- **For Agent #7:** no open/draft PR and no formalization request.
- **Avoid next run:** summing fibre caps absolutely, interpreting the late-tail
  lower bound as a lower bound for `|Delta|`, or rerunning the same finite
  table without testing a concrete source/reference map.

