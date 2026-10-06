import Mathlib
import «research.VF_MID_FIRST_BAD_RESTORING_DECOMPOSITION»
import «research.VF_MID_OWNER_FIBER_DEGREE_NORMALIZATION»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONTINUATION»
import «research.VF_MID_FINAL_SIGNED_RANK_CONTRACTION»
import «research.ZERO_TARGET_MELLIN_COMPLETE_POST_ROOT_CUBES»
import «research.VF_MID_PHYSICAL_FORCING_MOBIUS_DECODER»
import «research.VF_MID_LI_UNIFORM_QUADRATURE»
import «research.VF_MID_FULL_AFFINE_PAIR_CLASSIFIER»
import «research.VF_MID_FIRST_BAD_HISTORY_COMPRESSION»

/-!
# First-bad correlation descent

Finite logic for the terminal normalized-covariance contradiction.

The signed observable is the zero-target excess `Co - Div`. Along a genuine
greatest-owner descent the Mobius pair excess reverses sign exactly. A scalar
retained on the raw parent is carried unchanged through that descent, so its
square does not alter the reversal. Terminal pairs and complete post-root
families remain nonpositive after the same retained scaling.

The finite averaging selector records the logical core: if a partitioned signed
numerator exceeds one half of its matching denominator, then some component
does too. Once the actual VF first-bad source is identified with the exhaustive
greatest-owner continuation, a positive global half-excess must therefore
select a strictly lower-rank recursive child unless it exits through a sector
already controlled by zero or by the one-half gate.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- **Exact historical-anchor decompression.**

On every subdoubling frozen run, the accumulated endpoint defect at B is the
earlier anchor defect at A minus the complete literal survivor-plus-processed
physical run.  This is an identity; it is not packet-to-full-scale
inheritance. -/
theorem vfMidActualPrimeEndpointDefect_eq_anchor_sub_frozenAffineRun
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidActualPrimeEndpointDefect B =
      vfMidActualPrimeEndpointDefect A -
        vfMidFrozenAffineRunPhysicalCharge A B := by
  rw [vfMidFrozenAffineRunPhysicalCharge_eq_oddRunSeatMass hA hAB hBA]
  have hrun :=
    vfMidOddRunSeatMass_eq_neg_endpointError_increment
      A B (by omega : 2 ≤ A) hAB
  rw [vfMidActualPrimeEndpointDefect_eq_squareEndpointError
      (R := A) (by omega : 2 ≤ A),
    vfMidActualPrimeEndpointDefect_eq_squareEndpointError
      (R := B) (by omega : 2 ≤ B)]
  linarith

/-- First badness written directly on the decompressed historical physical run.
The residual anchor is a genuine earlier endpoint and is therefore controlled
by the first-bad prior-good wall. -/
theorem vfMidActualPrimeFirstBadAt_forces_frozenAffineRun_depthAware
    {K : ℝ} {A B : ℕ}
    (hfirst : VFMidActualPrimeFirstBadAt K B)
    (hA : 3 ≤ A) (hABlt : A < B) (hBA : B ≤ 2 * A) :
    K * vfMidSyntheticRadialScale B -
        |vfMidActualPrimeEndpointDefect A| <
      |vfMidFrozenAffineRunPhysicalCharge A B| := by
  have htrigger :=
    vfMidActualPrimeFirstBadAt_forces_depthAwareTwoSectorAbsTrigger
      hfirst hA hABlt hBA
  have hrun :=
    vfMidFrozenAffineRunPhysicalCharge_eq_oddRunSeatMass
      hA hABlt.le hBA
  have htwo :=
    vfMidOddRunSeatMass_eq_frozenSurvivor_add_processedOwnerCharge
      hA hBA
  rw [hrun]
  rw [htwo]
  exact htrigger

/-- **A first-bad successor forces normalized correlation above one half.**

This is the exact "correlation explosion" direction.  The first-bad endpoint
lies strictly outside the next K=2 radial wall, while one half of the complete
anchored Co+Div mass already fits inside that same wall.  Since the normalized
numerator times total mass is exactly the next endpoint defect squared, the
normalized coefficient must be strictly larger than one half. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    (1 / 2 : ℝ) < vfMidFirstBadNNSNormalizedCovariance R := by
  have hhalfRad :=
    vfMidActualPrimeFirstBadAt_two_succ_half_totalMass_le_radial hR hfirst
  have hendpoint :=
    vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq
      (by omega : 3 ≤ R)
  have hbad :
      ((2 : ℝ) * vfMidSyntheticRadialScale (R + 1)) ^ 2 <
        vfMidActualPrimeEndpointDefect (R + 1) ^ 2 := by
    have hbreach := hfirst.1
    unfold VFMidSyntheticBadAt at hbreach
    have hscale :
        0 < vfMidSyntheticRadialScale (R + 1) :=
      vfMidSyntheticRadialScale_pos (by omega : 2 ≤ R + 1)
    have hwall0 :
        0 ≤ (2 : ℝ) * vfMidSyntheticRadialScale (R + 1) :=
      mul_nonneg (by norm_num) hscale.le
    have habs0 :
        0 ≤ |vfMidActualPrimeEndpointDefect (R + 1)| := abs_nonneg _
    have habsPos :
        0 < |vfMidActualPrimeEndpointDefect (R + 1)| := by
      linarith
    have hsumPos :
        0 <
          |vfMidActualPrimeEndpointDefect (R + 1)| +
            (2 : ℝ) * vfMidSyntheticRadialScale (R + 1) :=
      add_pos_of_pos_of_nonneg habsPos hwall0
    have hprodPos :
        0 <
          (|vfMidActualPrimeEndpointDefect (R + 1)| -
            (2 : ℝ) * vfMidSyntheticRadialScale (R + 1)) *
          (|vfMidActualPrimeEndpointDefect (R + 1)| +
            (2 : ℝ) * vfMidSyntheticRadialScale (R + 1)) :=
      mul_pos (sub_pos.mpr hbreach) hsumPos
    rw [← sq_abs (vfMidActualPrimeEndpointDefect (R + 1))]
    nlinarith
  have hprod :
      (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R <
        vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R := by
    rw [hendpoint]
    exact hhalfRad.trans_lt hbad
  have htotal0 : 0 ≤ vfMidFirstBadZeroTargetTotalMass R := by
    rw [vfMidFirstBadZeroTargetTotalMass_eq]
    positivity
  by_cases htotalZero : vfMidFirstBadZeroTargetTotalMass R = 0
  · rw [htotalZero] at hprod
    norm_num at hprod
  · have htotalPos : 0 < vfMidFirstBadZeroTargetTotalMass R :=
      lt_of_le_of_ne htotal0 (Ne.symm htotalZero)
    exact (mul_lt_mul_iff_left₀ htotalPos).mp (by
      simpa [mul_assoc] using hprod)

/-- Deterministic affine center of one VF odd-seat field. -/
def vfMidCubeSeatAffineCenter (R : ℕ) : ℝ :=
  vfMidOddFractionalPrimeSeatWeight R - (1 / 2 : ℝ)

/-- On a frozen cubic-depth survivor carrier, the literal VF-minus-prime seat
charge is its deterministic affine center plus exactly one half of the physical
Mobius sign. -/
theorem vfMidOddSignedSeatCharge_eq_affineCenter_add_half_moebius_of_cube
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    vfMidOddSignedSeatCharge R n =
      vfMidCubeSeatAffineCenter R +
        (1 / 2 : ℝ) * realMoebiusStep n := by
  by_cases hp : n.Prime
  · rw [vfMidOddSignedSeatCharge_of_prime R n hp,
      realMoebiusStep]
    rw [ArithmeticFunction.moebius_apply_prime hp]
    unfold vfMidCubeSeatAffineCenter
    norm_num
    ring
  · have hsplit :=
      vfMidSquarePrefixWheelSurvivors_eq_prime_union_prefixComposite
        (A := A) (R := R) (by omega : 2 ≤ R) hAR
    have hmem :
        n ∈ vfMidSquareWheelPrimes R ∪
          vfMidSquareBandPrefixCompositeSurvivors A R := by
      rw [← hsplit]
      exact hn
    have hnComp :
        n ∈ vfMidSquareBandPrefixCompositeSurvivors A R := by
      rcases Finset.mem_union.mp hmem with hnPrime | hnComp
      · exact (hp (Finset.mem_filter.mp hnPrime).2).elim
      · exact hnComp
    have hmu :=
      vfMidSquareBandPrefixComposite_moebius_eq_one_of_cube
        hA hAR hcube hnComp
    rw [vfMidOddSignedSeatCharge_of_not_prime R n hp,
      realMoebiusStep, hmu]
    unfold vfMidCubeSeatAffineCenter
    norm_num

/-- The centered VF seat field is literally one half of the physical Mobius
field on the same cubic-depth survivor carrier. -/
theorem vfMidOddSignedSeatCharge_sub_affineCenter_eq_half_moebius_of_cube
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    vfMidOddSignedSeatCharge R n - vfMidCubeSeatAffineCenter R =
      (1 / 2 : ℝ) * realMoebiusStep n := by
  rw [vfMidOddSignedSeatCharge_eq_affineCenter_add_half_moebius_of_cube
    hA hAR hcube hn]
  ring

/-- **Actual VF / zero-target covariance dictionary in real currency.**

After removing only the deterministic VF affine center, one literal VF pair is
exactly one quarter of the owner-descending zero-target excess. -/
theorem vfMidCenteredSeatPair_eq_quarter_zeroTargetExcess_of_cube
    {A R S n m : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hAS : A ≤ S)
    (hcubeR : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hcubeS : (S + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R)
    (hm : m ∈ vfMidSquarePrefixWheelSurvivors A S) :
    (vfMidOddSignedSeatCharge R n - vfMidCubeSeatAffineCenter R) *
        (vfMidOddSignedSeatCharge S m - vfMidCubeSeatAffineCenter S) =
      (1 / 4 : ℝ) * postRootZeroTargetPairExcess (n, m) := by
  rw [vfMidOddSignedSeatCharge_sub_affineCenter_eq_half_moebius_of_cube
      hA hAR hcubeR hn,
    vfMidOddSignedSeatCharge_sub_affineCenter_eq_half_moebius_of_cube
      hA hAS hcubeS hm,
    postRootZeroTargetPairExcess_eq_weight]
  ring

/-- Retained scaling preserves the exact greatest-owner zero-target sign
reversal. -/
theorem descendingGreatestOwner_retained_zeroTargetExcess_flip
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    coefficient ^ 2 * postRootZeroTargetPairExcess (m, n) =
      -(coefficient ^ 2 * postRootZeroTargetPairExcess (um, un)) := by
  have hdesc := descendingGreatestOwner_reciprocal_descent hp hcross
  dsimp only at hdesc ⊢
  rw [postRootZeroTargetPairExcess_eq_weight,
    postRootZeroTargetPairExcess_eq_weight,
    hdesc.2.1]
  ring

/-- Retaining an arbitrary raw-parent scalar cannot turn a terminal zero-target
sector positive. -/
theorem vfMidRetainedFinalRankTerminalPair_zeroTarget_nonpos
    {W : ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈ postRootCovarianceRemainderTerminalPairCarrier W)
    (coefficient : ℝ) :
    coefficient ^ 2 * postRootZeroTargetPairExcess mn ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg coefficient)
    (vfMidFinalRankTerminalPair_zeroTarget_nonpos hmn)

/-- A constant retained scalar on one complete post-root family preserves its
nonpositivity. -/
theorem sum_zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_retained_nonpos
    {W p : ℕ} {r coefficient : ℝ}
    (hr0 : 0 ≤ r) (hr2 : r ≤ 2)
    (hp : p ∈ postRootPrimeFamilySet W) :
    coefficient ^ 2 *
      (∑ mn ∈ mertensPositivePhysicalPairCarrier (W / p),
        zeroTargetMellinPhysicalSuperLcmFourCorner W p r mn.1 mn.2) ≤ 0 := by
  exact mul_nonpos_of_nonneg_of_nonpos
    (sq_nonneg coefficient)
    (sum_zeroTargetMellinPhysicalSuperLcmFourCorner_postRoot_nonpos
      hr0 hr2 hp)

/-- **Finite half-excess selector.** If a finite numerator exceeds one half of
its matching denominator, some component has the same strict half-excess. -/
theorem exists_half_excess_of_sum_gt_half
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (num den : ι → ℝ)
    (h :
      (1 / 2 : ℝ) * (∑ i ∈ s, den i) <
        ∑ i ∈ s, num i) :
    ∃ i ∈ s, (1 / 2 : ℝ) * den i < num i := by
  by_contra hnone
  push_neg at hnone
  have hle :
      (∑ i ∈ s, num i) ≤
        ∑ i ∈ s, (1 / 2 : ℝ) * den i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hnone i hi
  have hfactor :
      (∑ i ∈ s, (1 / 2 : ℝ) * den i) =
        (1 / 2 : ℝ) * (∑ i ∈ s, den i) := by
    rw [Finset.mul_sum]
  rw [hfactor] at hle
  linarith

/-- If every stopped component is already below the half gate, a global strict
half-excess must occur in the designated recursive subcarrier. -/
theorem exists_recursive_half_excess_of_sum_gt_half
    {ι : Type*} [DecidableEq ι]
    (s recursive : Finset ι) (num den : ι → ℝ)
    (_hrecursive : recursive ⊆ s)
    (hstopped :
      ∀ i ∈ s, i ∉ recursive →
        num i ≤ (1 / 2 : ℝ) * den i)
    (h :
      (1 / 2 : ℝ) * (∑ i ∈ s, den i) <
        ∑ i ∈ s, num i) :
    ∃ i ∈ recursive, (1 / 2 : ℝ) * den i < num i := by
  obtain ⟨i, hi, hihalf⟩ :=
    exists_half_excess_of_sum_gt_half s num den h
  by_cases hir : i ∈ recursive
  · exact ⟨i, hir, hihalf⟩
  · have hstop := hstopped i hi hir
    linarith

/-- **Well-founded half-excess kill switch.**

A bad state cannot exist if every bad state selects another bad state of
strictly smaller natural-number rank.  This is the pure logical endgame of the
owner descent; all arithmetic content belongs in the selector theorem. -/
theorem no_bad_of_strict_rank_descent
    {ι : Type*}
    (rank : ι → ℕ) (bad : ι → Prop)
    (hdesc :
      ∀ x : ι, bad x →
        ∃ y : ι, rank y < rank x ∧ bad y) :
    ∀ x : ι, ¬ bad x := by
  intro x
  induction hx : rank x using Nat.strong_induction_on generalizing x with
  | h k ih =>
      intro hbad
      obtain ⟨y, hyrank, hybad⟩ := hdesc x hbad
      have hylt : rank y < k := by simpa [hx] using hyrank
      exact (ih (rank y) hylt y rfl) hybad

/-- A nonpositive stopped sector with nonnegative denominator cannot be the
strict half-excess selector. -/
theorem not_half_excess_of_nonpos_of_den_nonneg
    {num den : ℝ} (hnum : num ≤ 0) (hden : 0 ≤ den) :
    ¬ ((1 / 2 : ℝ) * den < num) := by
  intro h
  nlinarith

/-- A sector already satisfying the half gate cannot be the strict selector. -/
theorem not_half_excess_of_le_half
    {num den : ℝ}
    (hhalf : num ≤ (1 / 2 : ℝ) * den) :
    ¬ ((1 / 2 : ℝ) * den < num) := by
  linarith

end RHLean.Analysis
