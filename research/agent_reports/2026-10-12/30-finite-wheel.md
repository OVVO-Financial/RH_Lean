# RH_Lean agent daily report — 2026-10-12 / Finite Wheel & Incidence

## Provenance

- **Report date (America/New_York):** 2026-10-12
- **Agent / stage:** RH | Finite Wheel & Incidence / `30-finite-wheel.md`
- **Scheduled start:** 10:00 ET
- **Actual execution / completed time:** 2026-10-12T22:35:38-04:00 (late scheduled invocation)
- **Observed `main` HEAD SHA:** `0672dad401f425558bac5253ebe5f6024bec95bb`
- **Central contract fetched:** SUCCESS: `main:AGENTS.md` (blob `1a967423dc2203221ff768b704870b0bb5d2b5ef`) and `main:CURRENT_PROOF_CONTRACT.md` (blob `f6e8dc6813ec63974489c26b0c383e34203f0aa9`).
- **Report target:** `agent-reports:research/agent_reports/2026-10-12/30-finite-wheel.md`
- **Previous upstream reports actually read:** `00-coordinator-am.md` PENDING (404); `10-owner-payment.md` PENDING (404); `20-analytic-type-ii.md` PENDING (404), all checked on `agent-reports`.
- **Execution environment/tools used:** authenticated GitHub read/search and authorized report-file write; CPython 3 exact integer enumeration. No Lean build or CI was run.
- **Publication status:** PUBLISHED. Initial report commit: `710ca9d74cebbb878767f36a2a841c4c9dfe0679`; this metadata update is verified by a subsequent readback.

## Current central research objective

The public goal is the canonical square-endpoint estimate
[
  |pi(R^2)-operatorname{vfMidFinishedMass}(R)-sqrt2|le C Rlog R
]
for all (Rge2). The additive (sqrt2) phase does not change the frozen raw owner arithmetic. The direct route's current seam is actual-prime owner escape admissibility: splice the literal first-bad historical/current source, with original weights, signs, survivor masks, clipping, both walls, owner multiplicities and cumulative child runs, into the already-proved no-persistence/sector-six descent. The explicit historical payment target remains the open `VFMid915FirstBadSourcePaymentStatement`.

The contract specifically identifies the lower/composite run side as unfinished. This report studies the exact starting-wheel late-composite carrier without substituting it for the original weighted first-bad source.

## Original definitions and carrier inspected

At main SHA `0672dad...`:

- `vfMidSquareWheelSites R = Finset.Ioo (R^2) ((R+1)^2)`; endpoints are strictly excluded.
- `vfMidSquareBandPrefixCompositeSurvivors A R` consists of composite sites in that open block surviving every prime coordinate through (A).
- `vfMidSquareBandLateOwnerPrimes A R` consists of genuine least-prime owners (p>A).
- `vfMidSquareBandCompositeOwner R p` is the physical least-prime-owner fibre; the compiled owner Fubini theorem preserves every occurrence and multiplicity.
- `vfMidDyadicLateRemoval A A B` is exactly the cumulative (unit-weight, nonnegative) late-composite owner census over (Ale r<B).
- On (3le Ale R<2A), existing Lean proves every survivor is (pq), where (p,q) are distinct primes, (A<ple q), hence its Möbius sign is (+1). Actual prime survivors have sign (-1).
- The literal first-bad source is instead
  [
  D_{A}-	ext{vfMidFrozenAffineRunPhysicalCharge}(A,R)
       -	ext{vfMidFrozenAffineBlockPhysicalCharge}(A,R),
  quad A=lfloor R/2floor+1,
  ]
  with `vfMidOneBlockActivePhysicalSite` retaining the original site-dependent `vfMidOddSignedSeatCharge`. No equality between that weighted source and the unit owner census is assumed here.

## Work performed today

I sharpened the existing per-owner bound by combining two already-compiled facts that had not been combined in the repository search results:

1. the rough-child interval used in `vfMidSquareBandLateOwner_card_le_four_of_subdoubling` contains four consecutive integers; and
2. the later theorem `vfMidSquareBandLateOwnerRoughChild_prime_of_subdoubling` makes every such child an odd prime.

Only two integers in any four-consecutive-integer interval have the required odd parity. This gives a factor-two fibre bound and, after exact summation, a factor-four improvement in the published quadratic run envelope.

## Claims and evidence

### Claim 20261012-wheel-1

- **Exact quantified statement and original carrier:** For all natural (A,R,p), if (3le A), (Ale R), (R<2A), and
  (pin	exttt{vfMidSquareBandLateOwnerPrimes} A R), then
  [
  #	exttt{vfMidSquareBandCompositeOwner}(R,p)le2.
  ]
- **Status:** PAPER_PROOF.
- **Lean declaration or theorem reference, if any:** New proposed theorem `vfMidSquareBandLateOwner_card_le_two_of_subdoubling`; not formalized or compiled. It strengthens existing `..._card_le_four_of_subdoubling`.
- **Independent mathematical ingredient:** parity of the genuine prime child. This is not a density assumption, target inequality, or algebraic restatement. The old cardinality proof used only multiple spacing and retained four consecutive possible cofactors; the new step removes the two even positions using the actual-prime child theorem.
- **Proof:** Put (t=lfloor R^2/pfloor). The existing proof gives an occurrence-preserving cardinality identification with the rough-child fibre and inclusion
  [
  	ext{roughChildren}(R,p)subseteq(t,t+4].
  ]
  The existing subdoubling rank theorem says every member (q) of this rough-child fibre is prime. The fibre definition also has (ple q), while (p>Age3); hence (qge5), so (q) is odd. The four integers (t+1,t+2,t+3,t+4) contain exactly two odd integers. Therefore the child fibre, and hence the physical owner fibre, has cardinality at most two.
- **Endpoint/boundary audit:** The physical band is open. A square (p^2) is not admitted at its root; no endpoint atom was added. The auxiliary interval is `Ioc`, exactly as in the existing proof.
- **Attempted falsification / counterexamples:** Exhaustive exact enumeration for every (3le Ale800), every (Ale R<2A), and all genuine prime owner/child pairs found maximum fibre size 2 and no violation. Sharp example: (A=12,R=22,p=17), with (17cdot29=493) and (17cdot31=527) both in ((484,529)). Dropping subdoubling is false: (A=3,R=18,p=5) owns (325,335,355), so the fibre has size 3.
- **Precise first unproved lemma or limit:** A Lean lemma that the odd members of `Finset.Ioc t (t+4)` have cardinality two, followed by the subset/cardinality transport. No Lean execution was performed.
- **What changed relative to current known baseline:** exact per-owner capacity (4	o2).

### Claim 20261012-wheel-2

- **Exact quantified statement and original carrier:** Under (3le Ale R<2A),
  [
  #	exttt{vfMidSquareBandPrefixCompositeSurvivors}(A,R)
  le2(R-A).
  ]
  If (3le Ale Ble2A), writing (d=B-A),
  [
  	exttt{vfMidDyadicLateRemoval}(A,A,B)le d(d-1).
  ]
- **Status:** PAPER_PROOF.
- **Lean declaration or theorem reference, if any:** Proposed strengthenings of `vfMidSquareBandPrefixComposite_start_card_le_four_mul_gap` and `vfMidDyadicLateRemoval_start_le_four_mul_gap_sq`; not compiled.
- **Independent mathematical ingredient:** Claim 1 plus the exact least-prime-owner Fubini partition. No owner charge is reused.
- **Proof:** Late owners are genuine primes in ((A,R]), so there are at most (R-A) of them. Exact owner Fubini and Claim 1 give the block bound. Summing over (r=A,ldots,B-1) gives
  [
  2sum_{r=A}^{B-1}(r-A)=2sum_{k=0}^{d-1}k=d(d-1).
  ]
  Every descendant occurrence is counted in its own physical block.
- **Signs and multiplicities:** Existing Lean proves every counted late survivor has (mu=+1); actual primes have (mu=-1) in the signed decoder. The claim preserves least-prime owner identity and occurrence multiplicity. It does not deduplicate an owner across blocks.
- **Repeated historical-prime test:** For (A=4), the same owner (p=5) has child (7) at site (35) in block (R=5), and child (11) at site (55) in block (R=7). Both are counted separately. Thus this theorem supplies no historical uniqueness and does not authorize reusing one negative charge for both descendants.
- **Numerical evidence:** The same exhaustive (Ale800) scan found no fibre violation. For full runs (B=2A), the largest observed ratio of actual late-composite count to (A(A-1)) was (1/6), at (A=3); this is diagnostic only.
- **Precise first unproved lemma or limit:** Lean formalization of Claim 1 and the finite arithmetic sum. The deeper limit is that this is a positive unit-weight census, not the original signed weighted source.
- **What changed relative to current known baseline:** block envelope (4(R-A)	o2(R-A)); run envelope (4d^2	o d(d-1)). The saving against the existing run bound is exactly (3d^2+d).

### Claim 20261012-wheel-3

- **Exact quantified statement and original carrier:** Under the hypotheses of Claim 2,
  [
  	exttt{vfMidDyadicPrefixSupply}(A,A,B)-d(d-1)
  le	exttt{vfMidDyadicPrimeSupply}(A,B).
  ]
- **Status:** PAPER_PROOF, immediate corollary of Claim 2 and the existing exact identity
  (	ext{lateRemoval}=	ext{prefixSupply}-	ext{primeSupply}).
- **Independent mathematical ingredient:** none beyond Claims 1–2; this is a consumer corollary, not separately novel.
- **Attempted falsification / counterexamples:** Same exact scan and endpoint convention. No violation through (A=800).
- **Precise first unproved lemma or limit:** Even for (dasymp A), the error is (O(A^2)), still a full factor about (A/log A) above the desired (O(Alog A)) defect scale. It is unsigned and cannot pay the original squared first-bad source.
- **What changed relative to current known baseline:** a strictly sharper deterministic lower prime-supply capacity for the contract's lower/composite branch.

## Reproducible finite computation

Executed with CPython 3.12 using an Eratosthenes sieve. For each (A=3,ldots,800), the program enumerated primes (p>A), primes (qge p), formed (n=pq), set (R=lfloorsqrt nfloor), rejected exact squares, and retained precisely (Ale R<2A) and (ple R). It grouped occurrences by ((R,p)), checked fibre size, and retained owner tags across blocks.

Observed:

- maximum fibre size: 2;
- violations of Claim 1: 0;
- first sharp fibre: (A=12,R=22,p=17), children 29 and 31;
- first repeated owner across distinct blocks: (A=4,p=5), occurrences ((R,q,n)=(5,7,35),(7,11,55));
- smallest searched counterexample after deleting (R<2A): (A=3,R=18,p=5), sites (325,335,355).

This computation is evidence and falsification support, not an all-scale proof.

## Novelty and circularity audit

Repository searches found the exact factor-four owner theorem, rank-two prime-child theorem, positive Möbius sign theorem, owner Fubini, and (4d^2) run bound, but no `card_le_two` or (d(d-1)) result. The novelty is the parity intersection of the four-slot cofactor window with the independently established genuine-prime child carrier.

This does not assume RH, finite A/C, signed cancellation, owner admissibility, or the source-payment inequality. It is not an inclusion-exclusion restatement: it removes two arithmetically impossible cofactor positions from each exact owner fibre. Claim 3 is only a corollary and is not separately novel.

## Quantitative contribution to the current obligation

- **Trivial/existing bound:** 4 descendants per late owner, (4(R-A)) late composites per block, and (4d^2) over a run.
- **Improved bound:** 2 descendants per late owner, (2(R-A)) per block, and exactly (d(d-1)) as a uniform run envelope.
- **Range:** (3le Ale Ble2A); for each block (Ale R<B).
- **Uniformity:** all natural parameters in that range; exact constants.
- **Sign:** the late-composite contribution is genuinely (+1) in Möbius currency, but the estimate itself is a positive census.
- **Boundary:** open square blocks; no square endpoints.
- **Original-source effect:** narrows the deterministic lower/composite safe capacity, but does not control `vfMidOneBlockActivePhysicalSite`, the historical affine weights, clipped/admitted cross terms, both walls, or `vfMidFirstBadZeroTargetTotalMass`.
- **Conclusion:** useful finite arithmetic tightening, not closure. It remains (O(d^2)), and no transfer to the original source-payment inequality has been proved.

## Exact remaining mathematical gap

The first global unresolved lemma is an occurrence- and weight-preserving run splice from the literal historical/current source
[
D_A-	ext{runPhysicalCharge}-	ext{blockPhysicalCharge}
]
onto the compensated owner-cell ledger, with the active survivor mask, original `vfMidOddSignedSeatCharge`, clipping, both walls, earlier-owner/second-contact transfers, and repeated-owner multiplicity retained. Only after this signed reassembly may Claim 2 be used as a safe-capacity term. Bounding the unit late-removal census alone cannot prove `VFMid915FirstBadSourcePaymentStatement`.

## Existing related Lean theorems

- `vfMidSquareBandLateOwner_card_le_four_of_subdoubling`
- `vfMidSquareBandLateOwnerRoughChild_prime_of_subdoubling`
- `vfMidSquareBandPrefixComposite_survivor_eq_two_primes_of_subdoubling`
- `vfMidSquareBandPrefixComposite_moebius_eq_one_of_subdoubling`
- `vfMidSquareBandPrefixComposite_card_eq_sum_lateOwnerCards`
- `vfMidSquareBandPrefixComposite_start_card_le_four_mul_gap`
- `vfMidDyadicLateRemoval_start_le_four_mul_gap_sq`
- `vfMidDyadicPrimeSupply_ge_startPrefix_sub_four_mul_gap_sq`
- `vfMidDyadicVFTrackingDefect_eq_vfMass_sub_primeSupply`
- `VFMid915FirstBadSourcePaymentStatement` (OPEN)

## Downstream handoff

- **Claims ready for census:** `20261012-wheel-1`, `20261012-wheel-2`, `20261012-wheel-3`.
- **Explicit 1 PM tests:**
  1. reproduce max fibre 2 to at least (A=10^5), preserving open endpoints and least-prime ownership;
  2. independently verify the sharp tuple ((12,22,17;29,31));
  3. search for the smallest counterexample when each hypothesis is removed separately;
  4. compute exact ratios (T_A(A,B)/[d(d-1)]) for all (Ble2A);
  5. preserve repeated-owner tags and confirm ((A,p)=(4,5)) has distinct descendants in blocks 5 and 7;
  6. compare the unit owner carrier with `vfMidOneBlockActivePhysicalCarrier` without asserting an equality; report omitted squareful/restoring and clipped sites explicitly.
- **Claims ready for independent referee:** all three, especially whether the rough-child four-slot inclusion plus primality really gives an occurrence-preserving two-slot subset.
- **Claims ready for Lean (ONLY independently proved):** `20261012-wheel-1` and its arithmetic consequences, subject to referee confirmation. Suggested scope is one localized strengthening module or additions to `VF_MID_DYADIC_OWNER_EXACT.lean`; no source change was made.
- **Missing inputs or upstream stages:** all three earlier reports PENDING.
- **Next action / priority:** formal referee check of Claim 1, then exact Lean proof; separately pursue the weighted historical-run splice, since the improved census does not supply it.

## Claims requiring Adversarial Referee review

1. The four-slot `Ioc` child interval is transported through the exact existing owner/child cardinality equality with no loss.
2. The prime-child theorem applies to every member used in the fibre bound and forces oddness via (qge p>Age3).
3. The run sum is (d(d-1)), including (d=0,1), with no endpoint block at (B).
4. The result must not be promoted from unit-weight positive late removal to the original weighted signed payment without a new exact bridge.

## Final report summary

**Net-new mathematical progress:** PAPER_PROOF of a sharp factor-two late-owner fibre bound and resulting (d(d-1)) run capacity, improving the existing (4d^2) envelope.

**Completeness:** DONE, with upstream stages PENDING and Lean formalization not executed.

**No RH-proof claim:** yes. RH, actual-prime owner admissibility, the source-payment inequality, and the historical weighted run splice remain open.
