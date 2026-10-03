import Mathlib
import «research.VF_MID_DYADIC_OWNER_EXACT»
import «research.VF_MID_SIGNED_SEAT_CHARGE»
import «research.VF_MID_LI_UNIFORM_QUADRATURE»
import RHLean.Arithmetic.PrimeSquareCollisionPrefix

/-!
# Subdoubling VF / Mobius dictionary on the exact square-wheel carrier

On a subdoubling square run, after freezing the starting wheel through A, every
surviving site in a later block A <= R < 2A is either an actual prime or a
late rank-two semiprime. The existing depth-two theorems give Mobius value
-1 on the prime seats and +1 on the surviving semiprime seats.

Hence the native VF seat charge has the exact pointwise form

  w_R - 1_Prime(n) = (1/2) mu(n) + (w_R - 1/2).

This records that physical dictionary before any square or norm is taken.
The imported finite-period and midpoint-curvature modules keep the two
deterministic rigidity mechanisms on the same proof branch.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

def vfMidSquareBandPrefixSurvivorMobiusMassReal (A R : ℕ) : ℝ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R, (((μ n : ℤ) : ℝ))

theorem vfMidSquareBandPrefixSurvivorMobiusMassReal_eq_cast
    (A R : ℕ) :
    vfMidSquareBandPrefixSurvivorMobiusMassReal A R =
      ((vfMidSquareBandPrefixSurvivorMobiusMass A R : ℤ) : ℝ) := by
  unfold vfMidSquareBandPrefixSurvivorMobiusMassReal
    vfMidSquareBandPrefixSurvivorMobiusMass
  push_cast
  rfl

theorem vfMidSubdoublingPrefixSurvivorSeatCharge_eq_affineMoebius
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A)
    (hn : n ∈ vfMidSquarePrefixWheelSurvivors A R) :
    vfMidOddSignedSeatCharge R n =
      (1 / 2 : ℝ) * (((μ n : ℤ) : ℝ)) +
        (vfMidOddFractionalPrimeSeatWeight R - (1 / 2 : ℝ)) := by
  by_cases hp : n.Prime
  · rw [vfMidOddSignedSeatCharge_of_prime R n hp,
      ArithmeticFunction.moebius_apply_prime hp]
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
      vfMidSquareBandPrefixComposite_moebius_eq_one_of_subdoubling
        hA hAR hRlt hnComp
    rw [vfMidOddSignedSeatCharge_of_not_prime R n hp, hmu]
    norm_num
    ring

def vfMidSubdoublingPrefixSurvivorChargeSum (A R : ℕ) : ℝ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
    vfMidOddSignedSeatCharge R n

theorem vfMidSubdoublingPrefixSurvivorChargeSum_eq_affineMoebius
    {A R : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A) :
    vfMidSubdoublingPrefixSurvivorChargeSum A R =
      (1 / 2 : ℝ) * vfMidSquareBandPrefixSurvivorMobiusMassReal A R +
        ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ) *
          (vfMidOddFractionalPrimeSeatWeight R - (1 / 2 : ℝ)) := by
  unfold vfMidSubdoublingPrefixSurvivorChargeSum
  calc
    (∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
        vfMidOddSignedSeatCharge R n) =
      ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
        ((1 / 2 : ℝ) * (((μ n : ℤ) : ℝ)) +
          (vfMidOddFractionalPrimeSeatWeight R - (1 / 2 : ℝ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact
              vfMidSubdoublingPrefixSurvivorSeatCharge_eq_affineMoebius
                hA hAR hRlt hn
    _ =
      (1 / 2 : ℝ) *
          (∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
            (((μ n : ℤ) : ℝ))) +
        ∑ _n ∈ vfMidSquarePrefixWheelSurvivors A R,
          (vfMidOddFractionalPrimeSeatWeight R - (1 / 2 : ℝ)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ =
      (1 / 2 : ℝ) * vfMidSquareBandPrefixSurvivorMobiusMassReal A R +
        ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ) *
          (vfMidOddFractionalPrimeSeatWeight R - (1 / 2 : ℝ)) := by
            unfold vfMidSquareBandPrefixSurvivorMobiusMassReal
            rw [Finset.sum_const, nsmul_eq_mul]
            ring

theorem vfMidOddCompositeTrackingDefect_eq_frozenWheel_add_half_moebius
    {A R : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hRlt : R < 2 * A) :
    vfMidOddCompositeTrackingDefect R =
      vfMidBandMass R -
        (1 / 2 : ℝ) * ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ) +
        (1 / 2 : ℝ) * vfMidSquareBandPrefixSurvivorMobiusMassReal A R := by
  have hdecodeZ :=
    two_mul_vfMidIntegerBlockPrimeSupply_eq_prefixSurvivors_sub_mobiusMass
      hA hAR hRlt
  have hdecode :
      2 * (vfMidIntegerBlockPrimeSupply R : ℝ) =
        ((vfMidSquarePrefixWheelSurvivors A R).card : ℝ) -
          vfMidSquareBandPrefixSurvivorMobiusMassReal A R := by
    rw [vfMidSquareBandPrefixSurvivorMobiusMassReal_eq_cast]
    exact_mod_cast hdecodeZ
  have hdef :=
    vfMidOddCompositeTrackingDefect_eq_neg_bandError
      R (by omega : 2 ≤ R)
  unfold vfMidSquareBandError at hdef
  rw [vfMidSquareBandPrimes_card_eq_integerBlockPrimeSupply R] at hdef
  linarith

private theorem sum_vfMidBandMass_Ico_eq_dyadicVFMass
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    (∑ r ∈ Finset.Ico A B, vfMidBandMass r) =
      vfMidDyadicVFMass A B := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp [vfMidDyadicVFMass]
  | succ B hAB ih =>
      rw [Finset.sum_Ico_succ_top hAB, ih]
      unfold vfMidDyadicVFMass
      rw [vfMidFinishedMass_succ (hA.trans hAB)]
      ring

def vfMidDyadicPrefixSurvivorMobiusMassReal (A B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico A B,
    vfMidSquareBandPrefixSurvivorMobiusMassReal A r

theorem vfMidDyadicVFTrackingDefect_eq_frozenWheel_add_half_moebius
    {A B : ℕ}
    (hA : 3 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicVFTrackingDefect A B =
      vfMidDyadicVFMass A B -
        (1 / 2 : ℝ) * vfMidDyadicPrefixSupply A A B +
        (1 / 2 : ℝ) * vfMidDyadicPrefixSurvivorMobiusMassReal A B := by
  have htrack :=
    vfMidOddDyadicCompositeTrackingDefect_eq_vfTrackingDefect
      (A := A) (B := B) (by omega : 2 ≤ A)
      (by omega : 2 ≤ B) hAB
  calc
    vfMidDyadicVFTrackingDefect A B =
        ∑ r ∈ Finset.Ico A B, vfMidOddCompositeTrackingDefect r := by
          symm
          simpa [vfMidOddDyadicCompositeTrackingDefect] using htrack
    _ = ∑ r ∈ Finset.Ico A B,
          (vfMidBandMass r -
            (1 / 2 : ℝ) *
              ((vfMidSquarePrefixWheelSurvivors A r).card : ℝ) +
            (1 / 2 : ℝ) *
              vfMidSquareBandPrefixSurvivorMobiusMassReal A r) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
          have hrB : r < B := (Finset.mem_Ico.mp hr).2
          exact
            vfMidOddCompositeTrackingDefect_eq_frozenWheel_add_half_moebius
              hA hAr (hrB.trans_le hBA)
    _ =
        (∑ r ∈ Finset.Ico A B, vfMidBandMass r) -
          (1 / 2 : ℝ) *
            (∑ r ∈ Finset.Ico A B,
              ((vfMidSquarePrefixWheelSurvivors A r).card : ℝ)) +
          (1 / 2 : ℝ) *
            vfMidDyadicPrefixSurvivorMobiusMassReal A B := by
          unfold vfMidDyadicPrefixSurvivorMobiusMassReal
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, ← Finset.mul_sum]
          ring
    _ = vfMidDyadicVFMass A B -
          (1 / 2 : ℝ) * vfMidDyadicPrefixSupply A A B +
          (1 / 2 : ℝ) * vfMidDyadicPrefixSurvivorMobiusMassReal A B := by
          rw [sum_vfMidBandMass_Ico_eq_dyadicVFMass (by omega) hAB,
            vfMidDyadicPrefixSupply_eq_sum_prefixWheelCards A A B hAB]

end RHLean.Analysis
