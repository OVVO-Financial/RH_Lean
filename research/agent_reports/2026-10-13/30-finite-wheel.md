# RH_Lean agent daily report — 2026-10-13 / RH | Finite Wheel & Incidence

## Provenance

- **Report date (America/New_York):** 2026-10-13
- **Agent / stage:** RH | Finite Wheel & Incidence / 30-finite-wheel.md
- **Scheduled start:** 10:00 ET
- **Run ID / sequence:** 2026-10-13T10:03:01-04:00 / first run of this date
- **Actual execution / completed time:** 2026-10-13T10:10:44-04:00
- **Previous own checkpoint:** NONE; the assigned dated path returned 404 before publication.
- **Warm-start cache status:** no mathematical result was accepted from memory. Authority, upstream reports, and all relevant declarations were re-fetched. The merged parity-two source was checked at the observed main commit.
- **Observed main HEAD SHA:** 52babf6eb87a7c6f80316ceb952667ad65cb2aa3, retrieved 2026-10-13T10:04:00-04:00 and unchanged on the pre-publication refresh at 2026-10-13T10:10:34-04:00.
- **Central contract fetched:** SUCCESS: main:AGENTS.md blob 709ad61bf4555fe4f2c92af3fd42f3994798c8bf and main:CURRENT_PROOF_CONTRACT.md blob f6e8dc6813ec63974489c26b0c383e34203f0aa9.
- **Report target:** agent-reports:research/agent_reports/2026-10-13/30-finite-wheel.md
- **Previous upstream reports actually read:** 00-coordinator-am.md blob 87a596f6f7bcb9bab6b2d29fc7c162c64ed544cb; 10-owner-payment.md blob d60ca9e416c70faa1a4bce60291c73daf82d0366; 20-analytic-type-ii.md blob f503ac5ce9e04219c4928defc8d74c7f40c02ea0.
- **Execution environment/tools used:** GitHub read/write connector; local Python 3.12 exact integer sieve/enumeration. No web search and no local Lean checkout or Lean compilation.
- **Publication status:** COMPLETED; commit SHA is recorded after the write and re-fetch below.
- **Early durable checkpoint:** NOT_PUBLISHED; the completed report is the first write.

## Current central research objective

Prove the public canonical square-endpoint estimate

\[
\exists C\ge0\ \forall R\ge2,\qquad
|\pi(R^2)-\operatorname{vfMidFinishedMass}(R)-\sqrt2|
\le C R\log R,
\]

formalized as VFCanonicalSquareVonKochStatement. On the direct route, the open arithmetic inlet is the occurrence-preserving signed first-bad actual-VF source/reassembly bridge into the already-cancelled owner-cell ledger. The present assignment is narrower: turn exact prefix-wheel/composite incidence into a correctly directed lower-run restriction without treating an upper prime capacity as a vacuum-length bound.

The live declarations inspected were:

- vfMidSquareBandPrefixCompositeSurvivors, vfMidSquareBandLateOwnerPrimes, vfMidSquareBandCompositeOwner and vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards in VF_MID_DYADIC_OWNER_EXACT.lean, blob 95e7aa05b62861a19f0179aa529f817e3a402bba;
- vfMidSquareBandLateOwner_card_le_two_of_subdoubling, vfMidSquareBandPrefixComposite_start_card_le_two_mul_gap, vfMidDyadicLateRemoval_start_le_two_triangular and vfMidDyadicPrimeSupply_ge_startPrefix_sub_two_triangular in VF_MID_DYADIC_OWNER_PARITY_TWO.lean, blob fb025b16bbbd6ca4bcf6288745c283aefa913218;
- vfMidDyadicPrimeSupply, vfMidDyadicPrefixSupply and vfMidDyadicLateRemoval;
- vfMidOddCandidateSeats, vfMidOddFractionalPrimeSeatWeight and vfMidOddSignedSeatCharge;
- vfMidRecursiveResidual_lt_neg_of_safeFloor and vfMidRecursiveResidual_lt_neg_of_uniformVacuumFloor;
- the original weighted source and recursive-complement declarations in VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean and VF_MID_RECURSIVE_REMAINDER_BOUND.lean.

The canonical additive sqrt(2) phase does not enter any run increment below. No historical coefficient was replaced by a canonical one.

## Work performed today

The merged theorem bounds each genuine late-owner fibre by two but then replaces the number of available prime owners by the coarse integer count R-A. I retained the primality of the owner labels and counted the available owners exactly by \(\pi(R)-\pi(A)\). This yields a uniformly sharper block and run bound, an improved lower bound for actual prime supply, and a signed upper bound for the literal VF-minus-prime tracking defect.

I then enumerated every physical open-square occurrence for all \(3\le A\le500\) and every \(A<B\le2A\), using a smallest-prime-factor sieve through \(10^6\). The scan checked 125,247 runs. It preserved each integer occurrence and least-prime owner before aggregation.

## Claims and evidence

### Claim 20261013-wheel-1 — prime-owner availability sharpens the two-slot late-composite cap

- **Exact quantified statement and original carrier:** Let \(A,R\in\mathbb N\) satisfy \(3\le A\le R<2A\). Put
  \[
  C_A(R)=
  |\operatorname{vfMidSquareBandPrefixCompositeSurvivors}(A,R)|.
  \]
  This is the actual set of composite integers \(n\) in the strictly open block
  \(R^2<n<(R+1)^2\) whose least prime factor is greater than \(A\). Then
  \[
  \boxed{C_A(R)\le 2\bigl(\pi(R)-\pi(A)\bigr).}
  \]
- **Status:** PAPER_PROOF. The constituent exact partition and two-slot fibre theorem are PROVED_IN_LEAN at main HEAD; this sharper corollary was not compiled during this run.
- **Lean declaration or theorem reference, if any:** vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards and vfMidSquareBandLateOwner_card_le_two_of_subdoubling.
- **Independent mathematical ingredient:** retain the actual primality of each least-prime owner. The live proof of the triangular theorem only uses
  \(|\operatorname{LateOwnerPrimes}(A,R)|\le R-A\). Here
  \[
  \operatorname{LateOwnerPrimes}(A,R)
  \subseteq\{p:\ p\text{ prime},\ A<p\le R\},
  \]
  whose exact cardinality is \(\pi(R)-\pi(A)\). This is strictly stronger whenever \((A,R]\) contains a composite root.
- **Proof:** Exact least-prime Fubini gives
  \[
  C_A(R)=\sum_{p\in L_A(R)}
       |\operatorname{CompositeOwner}(R,p)|.
  \]
  The merged parity theorem bounds each summand by 2. The displayed prime-owner inclusion bounds the number of summands by \(\pi(R)-\pi(A)\). Multiplication gives the result. Every physical composite occurs in exactly one fibre; no owner or occurrence is duplicated.
- **Boundary/sign/multiplicity audit:** both square walls are strict. Owners satisfy \(A<p\le R\). This claim is an unsigned population restriction, but it is applied below only inside the exact signed scalar identity. Reuse of the same owner in different blocks is allowed and counted separately.
- **Attempted falsification / counterexamples:** exact enumeration for every \(3\le A\le500\), \(A\le R<2A\), found no failure. The minimum cap-minus-population margin was 0, so equality cases occur and constants cannot be reduced merely from this proof.
- **Precise first unproved lemma or limit:** no cross-block uniqueness follows. A stronger claim charging only two occurrences to each owner over the complete run is false; see Claim 3.
- **What changed relative to current known baseline:** the factor \(2(R-A)\) is replaced by \(2(\pi(R)-\pi(A))\), with no new assumption.

### Claim 20261013-wheel-2 — refined run capacity and signed tracking bound

- **Exact quantified statement and original carrier:** Let \(3\le A\le B\le2A\), and define
  \[
  K(A,B)=2\sum_{r=A}^{B-1}\bigl(\pi(r)-\pi(A)\bigr).
  \]
  Then
  \[
  \boxed{\operatorname{LateRemoval}(A,A,B)\le K(A,B)}
  \]
  and, using the exact prefix partition,
  \[
  \boxed{\operatorname{PrimeSupply}(A,B)\ge
  \operatorname{PrefixSupply}(A,A,B)-K(A,B).}
  \]
  Consequently the literal signed VF-minus-prime run charge satisfies
  \[
  \boxed{\operatorname{VFTrackingDefect}(A,B)\le
  \operatorname{VFMass}(A,B)-\operatorname{PrefixSupply}(A,A,B)+K(A,B).}
  \]
- **Status:** PAPER_PROOF; FINITE_COMPUTATION for the numerical table.
- **Proof:** Sum Claim 1 blockwise. Exact occurrence Fubini gives
  \(\operatorname{PrefixSupply}=\operatorname{PrimeSupply}+\operatorname{LateRemoval}\).
  The compiled identity
  \(\operatorname{VFTrackingDefect}=\operatorname{VFMass}-\operatorname{PrimeSupply}\)
  then gives the signed inequality without taking an absolute value of the whole source.
- **Comparison with the compiled triangular cap:** since
  \(\pi(r)-\pi(A)\le r-A\),
  \[
  K(A,B)\le 2\sum_{r=A}^{B-1}(r-A)
  =(B-A)(B-A-1).
  \]
  Thus the new bound dominates today's merged triangular theorem at every admissible run.
- **Vacuum certificate:** if
  \[
  \operatorname{PrefixSupply}(A,A,B)>K(A,B),
  \]
  then \(\operatorname{PrimeSupply}(A,B)>0\); hence the run cannot consist entirely of zero-prime blocks. Conversely, a zero-prime run necessarily has prefix survivor population at most \(K(A,B)\). This is a lower-run obstruction, not an upper-capacity-to-vacuum inversion.
- **Exact finite computation:** Python 3.12 built an Eratosthenes smallest-prime-factor table through \(10^6\). For every physical integer \(R^2<n<(R+1)^2\), it retained \(n\), its primality, and minFac(n), then aggregated only after checking minFac(n)>A. Across 125,247 runs with \(3\le A\le500\), all exact partitions and inequalities passed. There were 100,413 runs where the refined certificate was positive while the triangular certificate was nonpositive.
- **Full dyadic examples \(B=2A\):**

| A | prefix survivors | actual primes | late composites | refined cap K | triangular cap | certified prime lower bound |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 18 | 16 | 2 | 6 | 20 | 12 |
| 10 | 65 | 53 | 12 | 40 | 90 | 25 |
| 50 | 993 | 862 | 131 | 536 | 2,450 | 457 |
| 100 | 3,437 | 2,974 | 463 | 2,066 | 9,900 | 1,371 |
| 500 | 63,041 | 56,454 | 6,587 | 36,818 | 249,500 | 26,223 |

  At \(A=500\), the cap improves by 212,682 occurrences; the old lower certificate is \(-186,459\), while the refined certificate is \(26,223\).
- **Novelty/circularity:** this does not assume the desired \(O(A\log A)\) estimate, finite A/C, or a density heuristic. It uses exact prime-owner availability at roots \(p\le R\), a lower-scale arithmetic input. It is not itself an all-scale lower bound on PrefixSupply, so it does not close the target.
- **Precise first unproved lemma or limit:** obtain an independently justified all-scale lower census for PrefixSupply strong enough to beat \(K(A,B)\) on the threatening run, or splice the resulting signed upper bound into the exact #903 safe/sector-six ledger with original weights and masks.

### Claim 20261013-wheel-3 — cross-block two-slot charging is false

- **Exact proposed claim refuted:** replacing the blockwise cap by
  \[
  \sum_{r=A}^{B-1}C_A(r)
  \le2\bigl(\pi(B-1)-\pi(A)\bigr)
  \]
  would assert that each prime owner can be charged only twice over the whole run.
- **Status:** REFUTED by exact finite counterexample.
- **Smallest counterexample in the declared scan order:** \(A=6,B=11\). The only available late owner is \(p=7\), so the proposed right side is 2. Yet the three distinct physical descendants
  \[
  77=7\cdot11\quad(R=8),\qquad
  91=7\cdot13\quad(R=9),\qquad
  119=7\cdot17\quad(R=10)
  \]
  all survive the prefix and have least-prime owner 7. The left side is 3.
- **Interpretation:** same-block fibre size remains at most two, but one historical prime identity may recur in multiple square blocks. Each occurrence above is mathematically separate. No single historical negative source may be reused to pay all three without an exact source decomposition supplying three charges.
- **First remaining lemma:** any stronger run cap must exploit cofactor progression or signed cross-block cancellation; owner identity alone is insufficient.

### Claim 20261013-wheel-4 — exact vacuum charge is preserved, but not yet source-spliced

- **Exact statement:** if every block \(r\in[A,B)\) has zero actual prime supply, then every one of the \(r\) odd candidate seats is composite and has signed seat charge
  \(+w_r\), where \(w_r=\operatorname{vfMidBandMass}(r)/r\). Therefore
  \[
  \sum_{r=A}^{B-1}\sum_{n\in\operatorname{OddCandidateSeats}(r)}
  \operatorname{SignedSeatCharge}(r,n)
  =\sum_{r=A}^{B-1}\operatorname{vfMidBandMass}(r).
  \]
  Least-prime Fubini reindexes the same positive occurrences without changing the total.
- **Status:** PAPER_PROOF, but this is an exact corollary of existing seat identities, not claimed as the new quantitative ingredient.
- **Signs and coefficients:** composites carry \(+w_r\); prime seats would carry \(-(1-w_r)\), but the vacuum hypothesis removes them. The additive canonical sqrt(2) cancels from the run increment. Strict block walls and all occurrence multiplicities are preserved.
- **Limit:** the odd-seat current-run charge has not been identified with the original #915 historical/current source, clipped survivor mask, anchor cross term, NNS denominator, or sector-six pair ledger. Therefore this identity cannot yet instantiate vfMidRecursiveResidual_lt_neg_of_safeFloor for the production source.

## Counterexample and novelty audit

- The refined cap was tested against small roots, strict endpoints, equality cases, and repeated owner identities.
- The false cross-block uniqueness shortcut fails already at \(A=6\).
- No claim of historical uniqueness, independent local payment, or signed cancellation is made.
- Claim 1 is new relative to the compiled theorem because it preserves the primality of owner labels instead of forgetting them into all integer root slots.
- Claim 2 is a genuine stronger deterministic restriction, but its finite positive certificates do not prove an all-scale statement.
- Claim 4 is useful bookkeeping only and is not presented as new cancellation.
- No generic wheel density was transferred to the adaptive prefix without a proved lower-discrepancy lemma.

## Quantitative effect on the original proof obligation

The trivial merged late-removal cap is
\((B-A)(B-A-1)\). The proved paper bound replaces it by
\(K(A,B)=2\sum_{r=A}^{B-1}(\pi(r)-\pi(A))\), uniformly for
\(3\le A\le B\le2A\). This directly improves the current scalar lower-run carrier and can exclude a zero-prime run whenever the exact prefix census exceeds \(K\).

It does not control the original physical source payment
VFMid915FirstBadSourcePaymentStatement. In particular, it contains no clipping weights, historical anchor coefficient, returned-pair multiplicity, boundary mask, or sector-six source identification. The first production gap remains an occurrence- and coefficient-preserving splice of the actual first-bad source onto the already-cancelled ledger.

## Downstream handoff

- **Claims ready for census:** independently reproduce Claims 1–3. Extend the exact scan to at least \(A=5000\) with a segmented SPF or least-factor sieve. For every run record PrefixSupply, actual PrimeSupply, late composite total, \(K(A,B)\), the triangular cap, and both certified lower bounds.
- **Explicit 1 PM tests:**
  1. Verify the \(A=6,B=11\) repeated-owner counterexample and retain tuples \((R,n,p,n/p)\).
  2. Search equality cases in Claim 1 and classify whether saturated fibres are the twin-cofactor packets identified by Owner Payment.
  3. Measure the minimum and distribution of
     \(\operatorname{PrefixSupply}-K\) over every \(A<B\le2A\), not only full dyadic runs.
  4. Compare the first run length at which the refined certificate becomes nonpositive with vfMidRadialLowerCompositeRunBill for selected \((K,A)\).
  5. Preserve blockwise owner multiplicity; do not collapse repeated p across blocks.
- **Claims ready for independent referee:** the owner-set cardinality \(\pi(R)-\pi(A)\), all endpoint conventions, the signed direction in Claim 2, and the scope of the vacuum corollary.
- **Claims ready for Lean (ONLY independently proved):** Claim 1 and the summed inequalities in Claim 2 are suitable small corollaries of the two cited compiled declarations. No source-payment theorem is ready.
- **Missing inputs or upstream stages:** an all-scale prefix-wheel lower census; the original weighted source-to-#903 ledger splice; independent review.
- **Next action / priority:** formalize Claim 1 after referee approval, then test whether its signed Claim 2 bound is strong on the actual threatening lower-bill runs rather than on arbitrary dyadic runs.

## Final report summary

**Net-new mathematical progress:** PAPER_PROOF of the exact prime-owner-refined two-slot cap
\(C_A(R)\le2(\pi(R)-\pi(A))\), its run-level signed consequence, and a decisive repeated-owner counterexample to cross-block two-slot reuse.
**Completeness:** DONE for this research stage; the canonical proof remains open.
**No RH-proof claim:** yes.

## Next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** 2026-10-13T10:10:44-04:00.
- **Source freshness:** main 52babf6eb87a7c6f80316ceb952667ad65cb2aa3; central blobs 709ad61b... and f6e8dc68...; owner exact 95e7aa05...; parity-two fb025b16....
- **Upstream consumed:** coordinator 87a596f6...; owner d60ca9e... including exact cutoff and twin-cofactor claims; analytic f503ac5c... including the triangular cap and late-tail obstruction.
- **Completed evidence worth reusing:** Claims 20261013-wheel-1 through -4; exact scan \(3\le A\le500\), 125,247 runs; repeated-owner counterexample \(A=6,B=11\).
- **Invalidations / uncertain results:** no source invalidation. No local Lean compile. Finite positivity through \(A=500\) has no all-scale force.
- **First unresolved mathematical/CI blocker:** exact original-weight source/reassembly splice into the #903 safe/sector-six ledger, plus an all-scale prefix lower census if the refined capacity route is pursued.
- **Next highest-value step:** Prime Census Laboratory extension and Adversarial Referee verification of Claims 1–3.
- **For Agent #7:** no PR requested; Claim 1 is formalization-ready only after independent review. No local Lean execution or CI evidence.
- **Avoid next run:** charging an owner only twice across a whole run, interpreting finite positive certificates as a uniform theorem, or substituting the current odd-seat scalar charge for the historical #915 source.
