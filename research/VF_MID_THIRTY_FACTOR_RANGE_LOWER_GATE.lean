import Mathlib
import «research.VF_MID_ODD_FRACTIONAL_CLUSTER»
import «research.VF_MID_ALIGNED_STEP_GRAPH»

/-!
# Pure factor-range formulation of the one-sided VF lower-channel gate

Everything on the source side is deterministic divisibility on integer seats.
Remove the exact 2-3-5 wheel first (residue classes 1,7,11,13,17,19,23,29
modulo 30); from the remaining candidates, charge each covered seat only once
if SOME divisor in [7,R] divides it.

For n strictly between R² and (R+1)², FTA proves that the uncovered sites
are precisely the actual prime seats. That theorem is the ONLY bridge back
to prime counting: neither the carrier nor the quantitative factor-coverage
barrier requires a prime-count function or a fantasy surrogate.

Crucial warning: an additional 3-5 sieve improves bookkeeping but CANNOT
by itself prove the needed upper bound on the remaining factor coverage.
The condition that would exclude a first lower-channel escape is stated
exactly and remains the mathematical open obligation.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- Candidate integers after deleting every factor 2, 3, or 5.  This is
a pure gcd condition: no Nat.Prime or primeCounting in its definition. -/
def vfMidThirtyCandidates (R : ℕ) : Finset ℕ :=
  (vfMidSquareWheelSites R).filter (fun n => (30 : ℕ).Coprime n)

/-- The finite prime-prefix modulus through 5 is literally 2*3*5. -/
theorem vfMidPrefixWheelModulus_five_eq_thirty :
    vfMidPrefixWheelModulus 5 = 30 := by
  decide

/-- The modular wheel-30 candidates are EXACTLY the existing cutoff-5
factor-wheel carrier.  This also preserves all its original owner metadata. -/
theorem vfMidThirtyCandidates_eq_prefixFive (R : ℕ) :
    vfMidThirtyCandidates R = vfMidSquarePrefixWheelSurvivors 5 R := by
  classical
  ext n
  simp only [vfMidThirtyCandidates, vfMidSquarePrefixWheelSurvivors,
    Finset.mem_filter]
  constructor
  · rintro ⟨hn, hcop⟩
    refine ⟨hn, ?_⟩
    apply (lowWheelHighSurvivor_iff_coprime_prefixWheel 5 n).2
    simpa only [vfMidPrefixWheelModulus_five_eq_thirty] using hcop
  · rintro ⟨hn, hsurv⟩
    refine ⟨hn, ?_⟩
    have hcop := (lowWheelHighSurvivor_iff_coprime_prefixWheel 5 n).1 hsurv
    simpa only [vfMidPrefixWheelModulus_five_eq_thirty] using hcop

/-- In particular, EVERY odd integer ending in 5 is excluded.
The exceptional prime 5 lies below all blocks with R >= 5. -/
theorem vfMidThirtyCandidates_not_lastDigitFive
    {R n : ℕ} (hn : n ∈ vfMidThirtyCandidates R) :
    n % 10 ≠ 5 := by
  have hsurv : lowWheelHighSurvivor 5 n := by
    have hm := vfMidThirtyCandidates_eq_prefixFive R
    have hmem : n ∈ vfMidSquarePrefixWheelSurvivors 5 R := by
      rw [← hm]
      exact hn
    exact (Finset.mem_filter.mp hmem).2
  have hfive : 5 ∈ primesUpTo 5 :=
    mem_primesUpTo.mpr ⟨by norm_num, by omega⟩
  have hnot : ¬ 5 ∣ n := hsurv 5 hfive
  intro hlast
  have hdiv : 5 ∣ n := by
    refine ⟨2 * (n / 10) + 1, ?_⟩
    omega
  exact hnot hdiv

/-- The pure divisor-range-covered population.  The range starts at 7
because factors 2,3,5 have already been removed by coprimality to 30.
No prime indicator, least-prime predicate, or pi in this definition.
Each covered integer is counted exactly ONCE, regardless of the
number of divisors or least-prime-factor owner presentations. -/
def vfMidThirtyFactorCovered (R : ℕ) : Finset ℕ :=
  (vfMidThirtyCandidates R).filter
    (fun n => ∃ d ∈ Finset.Icc 7 R, d ∣ n)

/-- A candidate has a factor in [7,R] precisely when it is rejected
by the complete factor wheel through R.  This is pure finite
divisibility; FTA only appears in the standard implementation of
the existing "primesUpTo" wheel when selecting prime coordinates. -/
theorem vfMidThirtyFactorCovered_mem_iff_not_fullWheel
    {R n : ℕ} (hR : 5 ≤ R) (hn : n ∈ vfMidThirtyCandidates R) :
    n ∈ vfMidThirtyFactorCovered R ↔
      n ∉ vfMidSquarePrefixWheelSurvivors R R := by
  classical
  have hnFive : n ∈ vfMidSquarePrefixWheelSurvivors 5 R := by
    rw [← vfMidThirtyCandidates_eq_prefixFive R]
    exact hn
  have hnSite : n ∈ vfMidSquareWheelSites R :=
    (Finset.mem_filter.mp hnFive).1
  have hnSurvFive : lowWheelHighSurvivor 5 n :=
    (Finset.mem_filter.mp hnFive).2
  have hnOne : n ≠ 1 := by
    have hnBand := Finset.mem_Ioo.mp hnSite
    change R ^ 2 < n ∧ n < (R + 1) ^ 2 at hnBand
    nlinarith
  constructor
  · intro hcovered
    obtain ⟨_hn, d, hdIcc, hdDvd⟩ :=
      Finset.mem_filter.mp hcovered
    have hd : 2 ≤ d := by
      have hdi := Finset.mem_Icc.mp hdIcc
      omega
    have hp : n.minFac.Prime := Nat.minFac_prime hnOne
    have hpDvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hpLeD : n.minFac ≤ d :=
      Nat.minFac_le_of_dvd hd hdDvd
    have hpR : n.minFac ≤ R :=
      hpLeD.trans (Finset.mem_Icc.mp hdIcc).2
    have hpMem : n.minFac ∈ primesUpTo R :=
      mem_primesUpTo.mpr ⟨hp, hpR⟩
    intro hfull
    have hsurvR : lowWheelHighSurvivor R n :=
      (Finset.mem_filter.mp hfull).2
    exact (hsurvR n.minFac hpMem) hpDvd
  · intro hnotFull
    have hnotSurv : ¬ lowWheelHighSurvivor R n := by
      intro hsurv
      exact hnotFull (Finset.mem_filter.mpr ⟨hnSite, hsurv⟩)
    unfold lowWheelHighSurvivor at hnotSurv
    push_neg at hnotSurv
    obtain ⟨p, hpMem, hpDvd⟩ := hnotSurv
    have hpPrime : p.Prime := prime_of_mem_primesUpTo hpMem
    have hpLe : p ≤ R := (mem_primesUpTo.mp hpMem).2
    have hpFive : 5 < p := by
      by_contra h
      have hsmall : p ≤ 5 := Nat.le_of_not_gt h
      have hmem5 : p ∈ primesUpTo 5 :=
        mem_primesUpTo.mpr ⟨hpPrime, hsmall⟩
      exact (hnSurvFive p hmem5) hpDvd
    have hpSeven : 7 ≤ p := by
      have hpNe6 : p ≠ 6 := by
        intro hp6
        rw [hp6] at hpPrime
        norm_num at hpPrime
      omega
    exact Finset.mem_filter.mpr
      ⟨hn, ⟨p, Finset.mem_Icc.mpr ⟨hpSeven, hpLe⟩, hpDvd⟩⟩

/-- Pure divisor-range factor coverage equals the difference between
the cutoff-5 and the full cutoff-R survivor sets. -/
theorem vfMidThirtyFactorCovered_eq_prefixFive_sdiff_full
    (R : ℕ) (hR : 5 ≤ R) :
    vfMidThirtyFactorCovered R =
      vfMidThirtyCandidates R \
        vfMidSquarePrefixWheelSurvivors R R := by
  classical
  ext n
  constructor
  · intro hn
    have hnCand := (Finset.mem_filter.mp hn).1
    exact Finset.mem_sdiff.mpr ⟨hnCand,
      (vfMidThirtyFactorCovered_mem_iff_not_fullWheel hR hnCand).1 hn⟩
  · intro hn
    obtain ⟨hnCand, hnNotFull⟩ := Finset.mem_sdiff.mp hn
    exact (vfMidThirtyFactorCovered_mem_iff_not_fullWheel hR hnCand).2 hnNotFull

/-- The full FTA survivor set is contained in the fixed wheel-30
candidate set. This is an exact finite-set inclusion, not a density
or independence assertion. -/
theorem vfMidFullWheel_subset_thirtyCandidates
    (R : ℕ) (hR : 5 ≤ R) :
    vfMidSquarePrefixWheelSurvivors R R ⊆
      vfMidThirtyCandidates R := by
  rw [vfMidThirtyCandidates_eq_prefixFive]
  exact vfMidSquarePrefixWheelSurvivors_mono (by omega : 5 ≤ R)

/-- Exact finite cardinal partition.  The actual prime population is
used here ONLY as a consequence of full-wheel FTA equivalence.
The source-side populations involve only the gcd-30 filter and
divisor-range coverage through R. -/
theorem vfMidThirtyCovered_add_actualPrimeSupply_eq_candidates
    (R : ℕ) (hR : 5 ≤ R) :
    (vfMidThirtyFactorCovered R).card +
      vfMidIntegerBlockPrimeSupply R =
        (vfMidThirtyCandidates R).card := by
  have hpartition :=
    Finset.card_sdiff_add_card_eq_card
      (vfMidFullWheel_subset_thirtyCandidates R hR)
  rw [← vfMidThirtyFactorCovered_eq_prefixFive_sdiff_full R hR] at hpartition
  rw [← vfMidIntegerBlockPrimeSupply_eq_fullPrefixWheelCard R
    (by omega : 2 ≤ R)] at hpartition
  exact hpartition

/-- The difference between actual factor-range coverage and the VF
reference on precisely the SAME wheel-30 candidate carrier. -/
def vfMidThirtyFactorCoverageExcess (R : ℕ) : ℝ :=
  ((vfMidThirtyFactorCovered R).card : ℝ) -
    (((vfMidThirtyCandidates R).card : ℝ) - vfMidBandMass R)

/-- The factor-range-centered excess is exactly V_R - P_R.  Tightening
the fixed wheel changes both the candidate population and the
composite reference by the SAME amount; it does not create
an unearned improvement to the native signed Sector Six payment. -/
theorem vfMidThirtyFactorCoverageExcess_eq_vfMass_sub_actualSupply
    (R : ℕ) (hR : 5 ≤ R) :
    vfMidThirtyFactorCoverageExcess R =
      vfMidBandMass R - (vfMidIntegerBlockPrimeSupply R : ℝ) := by
  have hnat := vfMidThirtyCovered_add_actualPrimeSupply_eq_candidates R hR
  have hreal :
      ((vfMidThirtyFactorCovered R).card : ℝ) +
        (vfMidIntegerBlockPrimeSupply R : ℝ) =
          ((vfMidThirtyCandidates R).card : ℝ) := by
    exact_mod_cast hnat
  unfold vfMidThirtyFactorCoverageExcess
  linarith

/-- Wheel-30 processing leaves the ORIGINAL parity owner-census defect
unchanged: it only moves the deterministic 3,5 composite owners from
the later ledger into the base carrier. -/
theorem vfMidThirtyFactorCoverageExcess_eq_oddOwnerDefect
    (R : ℕ) (hR : 5 ≤ R) :
    vfMidThirtyFactorCoverageExcess R =
      vfMidOddCompositeTrackingDefect R := by
  rw [vfMidThirtyFactorCoverageExcess_eq_vfMass_sub_actualSupply R hR,
    vfMidOddCompositeTrackingDefect_eq_neg_bandError R (by omega)]
  unfold vfMidSquareBandError
  rw [vfMidSquareBandPrimes_card_eq_integerBlockPrimeSupply R]
  ring

/-- The full history of factor-range coverage, with NO prime count in
the expression.  Positive excess is precisely the cumulative shortage
of full-wheel survivors relative to the unchanged VF mass. -/
def vfMidThirtyAccumulatedFactorExcess (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 5 R, vfMidThirtyFactorCoverageExcess r

/-- Exact factor-range telescope.  Prime counting is an OUTPUT via FTA,
not a definition used to build the source-side factor excess. -/
theorem vfMidThirtyAccumulatedFactorExcess_eq_endpointDefect
    (R : ℕ) (hR : 5 ≤ R) :
    vfMidThirtyAccumulatedFactorExcess R =
      vfMidSquareEndpointError 5 - vfMidSquareEndpointError R := by
  unfold vfMidThirtyAccumulatedFactorExcess
  have hterms :
      (∑ r ∈ Finset.Ico 5 R, vfMidThirtyFactorCoverageExcess r) =
        ∑ r ∈ Finset.Ico 5 R,
          -(vfMidSquareEndpointError (r + 1) -
              vfMidSquareEndpointError r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrFive : 5 ≤ r := (Finset.mem_Ico.mp hr).1
    rw [vfMidThirtyFactorCoverageExcess_eq_vfMass_sub_actualSupply r hrFive]
    rw [vfMidSquareEndpointError_succ r (by omega : 2 ≤ r)]
    unfold vfMidSquareBandError
    rw [vfMidSquareBandPrimes_card_eq_integerBlockPrimeSupply r]
    ring
  rw [hterms, ← Finset.sum_neg_distrib]
  rw [Finset.sum_Ico_sub vfMidSquareEndpointError hR]
  ring

/-- Finite initial count is explicit and contains the exceptional
small primes 2,3,5; all later data are factor ranges above 5. -/
theorem vfMidPrimeCounting_twentyFive :
    Nat.primeCounting 25 = 9 := by decide

/-- Quantitative factor-only lower-channel barrier.  It is the
ONE mathematical statement still to prove, and does not mention
Nat.Prime, Nat.primeCounting, or Li anywhere in its DEFINITION. -/
def VFMidThirtyLowerFactorSafe (K : ℝ) (R : ℕ) : Prop :=
  vfMidThirtyAccumulatedFactorExcess R ≤
    (9 : ℝ) - vfMidFinishedMass 5 +
      K * (R : ℝ) * Real.log (R : ℝ)

/-- Exact FTA transfer from the factor-only barrier to the
genuine prime lower-channel inequality, without assuming
PNT, RH, or a particular prime distribution. -/
theorem vfMidThirtyLowerFactorSafe_iff_actualLowerChannel
    (K : ℝ) (R : ℕ) (hR : 5 ≤ R) :
    VFMidThirtyLowerFactorSafe K R ↔
      -(K * (R : ℝ) * Real.log (R : ℝ)) ≤
        vfMidSquareEndpointError R := by
  have htel := vfMidThirtyAccumulatedFactorExcess_eq_endpointDefect R hR
  have hbase :
      vfMidSquareEndpointError 5 =
        (9 : ℝ) - vfMidFinishedMass 5 := by
    unfold vfMidSquareEndpointError
    norm_num [vfMidPrimeCounting_twentyFive]
  unfold VFMidThirtyLowerFactorSafe
  rw [htel, hbase]
  constructor <;> intro h <;> linarith

/-- This exact horizontal-lag criterion is phrased on factor-range
coverage. The target VF level is the literal floor at the
chosen sqrt(2) vertical phase, at ANY shifted root L. -/
def VFMidThirtyHorizontalCoverageSafe (L R : ℕ) : Prop :=
  vfMidThirtyAccumulatedFactorExcess R ≤
    (9 : ℝ) - vfMidFinishedMass 5 + vfMidFinishedMass R -
      (vfMidAlignedIntegerBlockLevel (Real.sqrt 2) L : ℝ)

/-- A complete finite equivalence: lower VF horizontal alignment at
square root R is EXACTLY a divisor-coverage upper bound; the
prime staircase is recovered only on the conclusion side. -/
theorem vfMidThirtyHorizontalCoverageSafe_iff_actualLowerHorizontal
    (L R : ℕ) (hR : 5 ≤ R) :
    VFMidThirtyHorizontalCoverageSafe L R ↔
      vfMidAlignedIntegerBlockLevel (Real.sqrt 2) L ≤
        Nat.primeCounting (R ^ 2) := by
  have htel := vfMidThirtyAccumulatedFactorExcess_eq_endpointDefect R hR
  have hbase :
      vfMidSquareEndpointError 5 =
        (9 : ℝ) - vfMidFinishedMass 5 := by
    unfold vfMidSquareEndpointError
    norm_num [vfMidPrimeCounting_twentyFive]
  unfold VFMidThirtyHorizontalCoverageSafe
  rw [htel, hbase]
  unfold vfMidSquareEndpointError
  constructor
  · intro h
    have hreal :
        (vfMidAlignedIntegerBlockLevel (Real.sqrt 2) L : ℝ) ≤
          (Nat.primeCounting (R ^ 2) : ℝ) := by
      linarith
    exact_mod_cast hreal
  · intro h
    have hreal :
        (vfMidAlignedIntegerBlockLevel (Real.sqrt 2) L : ℝ) ≤
          (Nat.primeCounting (R ^ 2) : ℝ) := by
      exact_mod_cast h
    linarith

/-- Factor-only historical lower slack.  This retains the OLD margin,
so the first-bad argument cannot discard its largest source of
protective capacity. -/
def vfMidThirtyLowerHistoricalSlack (K : ℝ) (A : ℕ) : ℝ :=
  (9 : ℝ) - vfMidFinishedMass 5 +
    K * (A : ℝ) * Real.log (A : ℝ) -
    vfMidThirtyAccumulatedFactorExcess A

/-- An invalid lower barrier at B after a safe A requires a STRICT
overrun of the available historical slack plus the entire movement
of the lower wall.  There are only factor-range counts in the
hypotheses and the CONCLUSION. No false cancellation theorem
is smuggled in. -/
theorem vfMidThirtyFirstLowerBreach_forces_factorRunOverrun
    (K : ℝ) {A B : ℕ} (hA : 5 ≤ A) (hAB : A ≤ B)
    (hgood : VFMidThirtyLowerFactorSafe K A)
    (hbad : ¬ VFMidThirtyLowerFactorSafe K B) :
    vfMidThirtyAccumulatedFactorExcess B -
        vfMidThirtyAccumulatedFactorExcess A >
      vfMidThirtyLowerHistoricalSlack K A +
        K * ((B : ℝ) * Real.log (B : ℝ) -
          (A : ℝ) * Real.log (A : ℝ)) := by
  unfold VFMidThirtyLowerFactorSafe at hgood hbad
  unfold vfMidThirtyLowerHistoricalSlack
  push_neg at hbad
  linarith

end RHLean.Analysis
