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

/-- Cubic-depth rank-two form of every frozen-wheel composite survivor.

The existing owner theorem already proves that when the square wall lies below
the cubic completion threshold, the stripped rough child of every late owner
is prime. Thus every unresolved composite is a product of exactly two primes
above the frozen cutoff. -/
theorem vfMidSquareBandPrefixComposite_survivor_eq_two_primes_of_cube
    {A R n : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquareBandPrefixCompositeSurvivors A R) :
    ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ A < p ∧ p ≤ q ∧ n = p * q := by
  have hR3 : 3 ≤ R := hA.trans hAR
  rcases Finset.mem_filter.mp hn with ⟨hnComp, hnSurv⟩
  let p := n.minFac
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    vfMidSquareBandComposite_minFac_mem_ownerPrimes (by omega) hnComp
  have hpGtA : A < p :=
    (vfMidSquareBandComposite_survives_prefix_iff_minFac_gt
      (by omega) hnComp).1 hnSurv
  have hpLate : p ∈ vfMidSquareBandLateOwnerPrimes A R :=
    mem_vfMidSquareBandLateOwnerPrimes.mpr ⟨hpOwner, hpGtA⟩
  have hnOwner : n ∈ vfMidSquareBandCompositeOwner R p :=
    Finset.mem_filter.mpr ⟨hnComp, rfl⟩
  have hchild : n / p ∈ vfMidSquareBandCompositeOwnerChildren R p := by
    unfold vfMidSquareBandCompositeOwnerChildren
    exact Finset.mem_image.mpr ⟨n, hnOwner, rfl⟩
  have hrough : n / p ∈ vfMidSquareBandOwnerRoughChildren R p := by
    rw [← vfMidSquareBandCompositeOwnerChildren_eq_rough hR3 hpOwner]
    exact hchild
  have hqPrime : (n / p).Prime :=
    vfMidSquareBandLateOwnerRoughChild_prime_of_cube hpLate hrough hcube
  have hpPrime : p.Prime :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpOwner).1
  have hpLeQ : p ≤ n / p := by
    have hmIcc := (Finset.mem_filter.mp hrough).1
    exact (Finset.mem_Icc.mp hmIcc).1
  have hmul := vfMidSquareBandCompositeOwner_mul_div hnOwner
  refine ⟨p, n / p, hpPrime, hqPrime, hpGtA, hpLeQ, ?_⟩
  exact hmul.symm

/-- On the same cubic-depth carrier every unresolved composite has positive
Mobius sign. The two prime factors are distinct because no nontrivial square
lies strictly between consecutive squares. -/
theorem vfMidSquareBandPrefixComposite_moebius_eq_one_of_cube
    {A R n : ℕ} (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hn : n ∈ vfMidSquareBandPrefixCompositeSurvivors A R) :
    μ n = 1 := by
  rcases vfMidSquareBandPrefixComposite_survivor_eq_two_primes_of_cube
      hA hAR hcube hn with ⟨p, q, hp, hq, _hAp, _hpq, hnEq⟩
  have hnComp := (Finset.mem_filter.mp hn).1
  have hnSite := (Finset.mem_filter.mp hnComp).1
  have hband : R ^ 2 < n ∧ n < (R + 1) ^ 2 := by
    simpa [vfMidSquareBandSites] using hnSite
  have hpqNe : p ≠ q := by
    intro hpqEq
    subst q
    rw [hnEq] at hband
    have hRp : R < p := by
      by_contra hnot
      have hpR : p ≤ R := Nat.le_of_not_gt hnot
      have hsquare : p ^ 2 ≤ R ^ 2 :=
        Nat.pow_le_pow_left hpR 2
      nlinarith
    have hR1p : R + 1 ≤ p := by omega
    have hsquare : (R + 1) ^ 2 ≤ p ^ 2 :=
      Nat.pow_le_pow_left hR1p 2
    nlinarith
  have hcop : Nat.Coprime p q :=
    (Nat.coprime_primes hp hq).2 hpqNe
  rw [hnEq, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hq]
  norm_num

/-- Pointwise affine VF/Mobius dictionary under the full cubic depth-two
condition. This is the form that allows the frozen prefix to be much smaller
than the physical square root. -/
theorem vfMidCubePrefixSurvivorSeatCharge_eq_affineMoebius
    {A R n : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R)
    (hcube : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
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
    have hnComp : n ∈ vfMidSquareBandPrefixCompositeSurvivors A R := by
      rcases Finset.mem_union.mp hmem with hnPrime | hnComp
      · exact (hp (Finset.mem_filter.mp hnPrime).2).elim
      · exact hnComp
    have hmu :=
      vfMidSquareBandPrefixComposite_moebius_eq_one_of_cube
        hA hAR hcube hnComp
    rw [vfMidOddSignedSeatCharge_of_not_prime R n hp, hmu]
    norm_num
    ring

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
