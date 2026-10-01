import Mathlib
import «research.VF_MID_PHI_ODD_LI_TRANSFER»

/-!
# Diagonal transfer identity for the VF-mid dyadic increment

After the parity prefix is aligned, the cutoff telescope removes the artificial
prefix-rounding layer completely.

For one square block, odd-Li removal from cutoff 2 through cutoff r is

  I_oddLi(r,2) - I_oddLi(r,r).

At cutoff two, I_oddLi is exactly the physical parity-prefix survivor count.
Summing over r therefore gives

  oddLiRemoval(A,B)
    = prefixSupply_2(A,B) - oddLiDiagonal(A,B).

Substituting this into the exact #843 identity makes the prefix supply and its
density reference cancel algebraically.  The actual VF endpoint increment is

  D_B - D_A
    = (oddLiDiagonal(A,B) - VFmass(A,B))
      + oddDisplacementDiagonal(A,B).

Thus the remaining transfer problem is exposed directly on two diagonal
quantities.  No prefix error, ownerwise absolute value, or hidden transport
remainder remains.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Odd-prefixed Li diagonal square-interval aggregate across a dyadic range. -/
def vfMidDyadicOddLiDiagonalAggregate
    (L : ℕ → ℕ → ℂ) (A B : ℕ) : ℂ :=
  ∑ r ∈ Finset.Ico A B,
    vfMidOddLiSquareInterval L r r

/-- At cutoff two, one odd-Li square interval is literally the physical
parity-prefix survivor population of that open square block. -/
theorem vfMidOddLiSquareInterval_two_eq_prefixWheelCard
    {L : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L)
    (R : ℕ) :
    vfMidOddLiSquareInterval L R 2 =
      ((vfMidSquarePrefixWheelSurvivors 2 R).card : ℂ) := by
  let U : ℕ := (R + 1) ^ 2 - 1
  have hRU : R ^ 2 ≤ U := by
    dsimp [U]
    have hexp : (R + 1) ^ 2 = R ^ 2 + 2 * R + 1 := by ring
    rw [hexp]
    omega
  have hset :
      ((Finset.Ioc (R ^ 2) U).filter (lowWheelHighSurvivor 2)) =
        vfMidSquarePrefixWheelSurvivors 2 R := by
    unfold vfMidSquarePrefixWheelSurvivors vfMidSquareWheelSites
    dsimp [U]
    ext n
    simp
    omega
  have hsplit :=
    vfMidPrefixWheelCounting_add_intervalCounting
      2 (R ^ 2) U hRU
  have hinterval :
      vfMidPrefixWheelIntervalCounting 2 (R ^ 2) U =
        (vfMidSquarePrefixWheelSurvivors 2 R).card := by
    unfold vfMidPrefixWheelIntervalCounting
    rw [hset]
  have hsplitC :
      (vfMidPrefixWheelCounting 2 (R ^ 2) : ℂ) +
          ((vfMidSquarePrefixWheelSurvivors 2 R).card : ℂ) =
        (vfMidPrefixWheelCounting 2 U : ℂ) := by
    rw [← hinterval]
    exact_mod_cast hsplit
  unfold vfMidOddLiSquareInterval
  rw [vfMidOddLiCumulativeTransform_two_eq_prefixWheelCounting hL,
    vfMidOddLiCumulativeTransform_two_eq_prefixWheelCounting hL]
  dsimp [U] at hsplitC ⊢
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using hsplitC.symm

/-- Summing the cutoff-two odd-Li intervals reproduces the exact #843 prefix
supply. -/
theorem sum_vfMidOddLiSquareInterval_two_eq_dyadicPrefixSupply
    {L : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L)
    (A B : ℕ) (hAB : A ≤ B) :
    (∑ r ∈ Finset.Ico A B,
        vfMidOddLiSquareInterval L r 2) =
      (vfMidDyadicPrefixSupply 2 A B : ℂ) := by
  have hprefix :=
    vfMidDyadicPrefixSupply_eq_sum_prefixWheelCards
      2 A B hAB
  have hprefixC :
      (vfMidDyadicPrefixSupply 2 A B : ℂ) =
        ∑ r ∈ Finset.Ico A B,
          ((vfMidSquarePrefixWheelSurvivors 2 r).card : ℂ) := by
    exact_mod_cast hprefix
  rw [hprefixC]
  apply Finset.sum_congr rfl
  intro r _hr
  exact vfMidOddLiSquareInterval_two_eq_prefixWheelCard hL r

/-- The complete odd-Li late removal is prefix supply minus the diagonal
odd-Li square-interval aggregate. -/
theorem vfMidDyadicOddLiWeightedRemoval_eq_prefixSupply_sub_diagonal
    {L : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L)
    (A B : ℕ) (hA : 2 ≤ A) (hAB : A ≤ B) :
    vfMidDyadicOddLiWeightedRemoval L A B =
      (vfMidDyadicPrefixSupply 2 A B : ℂ) -
        vfMidDyadicOddLiDiagonalAggregate L A B := by
  unfold vfMidDyadicOddLiWeightedRemoval
    vfMidDyadicOddLiDiagonalAggregate
  calc
    (∑ r ∈ Finset.Ico A B,
        vfMidOddLiWeightedCutoffRemoval L r 2 r) =
      ∑ r ∈ Finset.Ico A B,
        (vfMidOddLiSquareInterval L r 2 -
          vfMidOddLiSquareInterval L r r) := by
            apply Finset.sum_congr rfl
            intro r hr
            have hAr : A ≤ r := (Finset.mem_Ico.mp hr).1
            have hr2 : 2 ≤ r := hA.trans hAr
            exact
              vfMidOddLiWeightedCutoffRemoval_eq_interval_sub
                hL r 2 r (by norm_num) hr2
    _ = (∑ r ∈ Finset.Ico A B,
          vfMidOddLiSquareInterval L r 2) -
        ∑ r ∈ Finset.Ico A B,
          vfMidOddLiSquareInterval L r r := by
            rw [Finset.sum_sub_distrib]
    _ = (vfMidDyadicPrefixSupply 2 A B : ℂ) -
        ∑ r ∈ Finset.Ico A B,
          vfMidOddLiSquareInterval L r r := by
            rw [sum_vfMidOddLiSquareInterval_two_eq_dyadicPrefixSupply
              hL A B hAB]

/-- **Exact diagonal transfer identity.**
For A>=3, the complete dyadic VF square-endpoint increment is exactly the
odd-prefixed Li diagonal tracking error plus the upper-boundary transformed
actual-minus-model displacement. -/
theorem vfMidPrimeError_sq_sub_sq_cast_eq_oddLiDiagonalError_add_displacement
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    {A B : ℕ} (hA : 3 ≤ A) (hAB : A ≤ B) :
    ((vfMidPrimeError ((B : ℝ) ^ 2) -
        vfMidPrimeError ((A : ℝ) ^ 2) : ℝ) : ℂ) =
      (vfMidDyadicOddLiDiagonalAggregate L A B -
        (vfMidDyadicVFMass A B : ℂ)) +
      vfMidDyadicOddLiDisplacementBoundary Actual L A B := by
  have hA2 : 2 ≤ A := by omega
  have hB2 : 2 ≤ B := hA2.trans hAB
  have herr :=
    vfMidPrimeError_sq_sub_sq_eq_prefixError_sub_lateCorrection
      2 hA2 hB2
  have herrC :=
    congrArg (fun x : ℝ => (x : ℂ)) herr
  have hlate :=
    vfMidDyadicLateCorrection_cast_eq_oddLiCorrection_sub_displacement
      hActual hL hA hAB
  have hodd :=
    vfMidDyadicOddLiWeightedRemoval_eq_prefixSupply_sub_diagonal
      hL A B hA2 hAB
  have hlate' :
      (vfMidDyadicLateRemoval 2 A B : ℂ) -
          (vfMidDyadicLateReference 2 A B : ℂ) =
        (vfMidDyadicOddLiWeightedRemoval L A B -
          (vfMidDyadicLateReference 2 A B : ℂ)) -
        vfMidDyadicOddLiDisplacementBoundary Actual L A B := by
    simpa only [map_sub] using hlate
  push_cast at herrC
  rw [hlate', hodd] at herrC
  unfold vfMidDyadicLateReference at herrC
  push_cast at herrC
  unfold vfMidDyadicVFMass at herrC ⊢
  push_cast at herrC ⊢
  ring_nf at herrC ⊢
  exact herrC

end RHLean.Analysis
