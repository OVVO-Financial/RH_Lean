import Mathlib
import «research.VF_MID_EXISTING_BOUNDARY_OPTIMAL_BASE»
import «research.VF_MID_UNIFORMITY_BIAS_CORRELATION»
import «research.VF_MID_ENDPOINT_TRIGGER_DICTIONARY»
import «research.VF_MID_PHYSICAL_FORCING_MOBIUS_DECODER»

/-!
# Optimal-base first-crossing Lyapunov trigger

This file localizes an escape from the already-solved optimal-base radial
channel into the exact one-block VF dynamics.

If the actual prime optimal base is inside the solved radial walls at R^2 and
lies above the upper wall at (R+1)^2, then the direct VF endpoint error must
pay both:

* a linear block bill:
    e_R > W_(R+1) - W_R,

* a quadratic Lyapunov bill:
    D_(R+1)^2 - D_R^2 > W_(R+1)^2 - W_R^2,

where D_R = pi(R^2)-VF(R^2), e_R = D_(R+1)-D_R, and
W_R = K R log R.

The latter is immediately rewritten by the compiled VF energy identity as

  2 D_R e_R + e_R^2 > W_(R+1)^2 - W_R^2.

The second section aggregates the already-proved physical-forcing /
zero-target pair dictionary over a frozen cubic-depth carrier.  Thus the
centered actual-minus-Li forcing Gram is exactly one quarter of the same
zero-target Mobius Gram used by the owner descent.

The final elementary theorem records the #878 dissipation handoff: because the
identified same-parent diagonal is nonpositive, any positive NNS cross excess
needed to pay an escape bill forces the unresolved cross-parent remainder to be
at least as large.

What is deliberately NOT asserted here is the remaining aggregate carrier
identification between the VF first-crossing energy bill and the #878 literal
one-block NNS cross excess.  This file isolates that exact seam without
applying the reciprocal 79/81 contraction to an unnormalized raw remainder.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Width of the normalized solved radial channel at square root R. -/
def vfMidRadialWallWidth (K : ℝ) (R : ℕ) : ℝ :=
  K * (R : ℝ) * Real.log (R : ℝ)

/-- The existing radial count walls are exactly VF plus/minus the named wall
width. -/
theorem vfMidSolvedFantasyRadialLowerCount_eq
    (K : ℝ) (R : ℕ) :
    vfMidSolvedFantasyRadialLowerCount K R =
      vfMid ((R : ℝ) ^ 2) - vfMidRadialWallWidth K R := by
  rfl

theorem vfMidSolvedFantasyRadialUpperCount_eq
    (K : ℝ) (R : ℕ) :
    vfMidSolvedFantasyRadialUpperCount K R =
      vfMid ((R : ℝ) ^ 2) + vfMidRadialWallWidth K R := by
  rfl

/-- Being inside the optimal-base radial walls at R^2 is exactly the direct VF
endpoint-error bound at that square endpoint. -/
theorem abs_vfMidSquareEndpointError_le_of_optimalBase_radial_inside
    {K : ℝ} {R : ℕ} (hR : 2 ≤ R)
    (hinside :
      vfMidSolvedFantasyRadialLowerOptimalBase K R ≤
          optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ∧
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ≤
          vfMidSolvedFantasyRadialUpperOptimalBase K R) :
    |vfMidSquareEndpointError R| ≤ vfMidRadialWallWidth K R := by
  have hcone :=
    (actualPrimeOptimalBase_between_solvedRadialWalls_iff hR).1 hinside
  have hbound :=
    (vfMidSolvedFantasyRadialConeAt_iff hR).1 hcone
  have heq :
      vfMidSquareEndpointError R =
        vfMidPrimeError ((R : ℝ) ^ 2) := by
    change vfMidDirectSquareEndpointError R =
      vfMidPrimeError ((R : ℝ) ^ 2)
    exact vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR
  rw [heq]
  simpa [vfMidRadialWallWidth, vfMidPrimeError] using hbound

/-- Crossing above the upper optimal-base wall is exactly a strict positive
count-space error beyond that radial wall. -/
theorem vfMidSquareEndpointError_gt_of_optimalBase_above_upper
    {K : ℝ} {R : ℕ} (hR : 2 ≤ R)
    (habove :
      vfMidSolvedFantasyRadialUpperOptimalBase K R <
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2)) :
    vfMidRadialWallWidth K R < vfMidSquareEndpointError R := by
  have hRreal : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hx : (1 : ℝ) < (R : ℝ) ^ 2 := by nlinarith
  have hcount :
      vfMidSolvedFantasyRadialUpperCount K R <
        vfMidPrimeCount ((R : ℝ) ^ 2) := by
    unfold vfMidSolvedFantasyRadialUpperOptimalBase at habove
    rw [optimalLogBase_eq_value] at habove
    by_contra hnot
    have hle :
        vfMidPrimeCount ((R : ℝ) ^ 2) ≤
          vfMidSolvedFantasyRadialUpperCount K R :=
      le_of_not_gt hnot
    have hbase :
        optimalLogBaseValue
            (vfMidPrimeCount ((R : ℝ) ^ 2)) ((R : ℝ) ^ 2) ≤
          optimalLogBaseValue
            (vfMidSolvedFantasyRadialUpperCount K R) ((R : ℝ) ^ 2) :=
      (optimalLogBaseValue_le_iff hx).2 hle
    exact (not_le_of_gt habove) hbase
  have herr :
      vfMidRadialWallWidth K R <
        vfMidPrimeError ((R : ℝ) ^ 2) := by
    unfold vfMidSolvedFantasyRadialUpperCount at hcount
    unfold vfMidPrimeError
    unfold vfMidRadialWallWidth
    linarith
  have heq :
      vfMidSquareEndpointError R =
        vfMidPrimeError ((R : ℝ) ^ 2) := by
    change vfMidDirectSquareEndpointError R =
      vfMidPrimeError ((R : ℝ) ^ 2)
    exact vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR
  rwa [heq]

/-- **Linear first-crossing bill.**

If R is still inside the solved optimal-base radial channel but R+1 is above
its upper wall, the new square block must supply more direct VF error than the
increase in the wall itself. -/
theorem vfMidOptimalBase_upperFirstEscape_forces_bandError
    {K : ℝ} (R : ℕ) (hR : 2 ≤ R)
    (hinside :
      vfMidSolvedFantasyRadialLowerOptimalBase K R ≤
          optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ∧
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ≤
          vfMidSolvedFantasyRadialUpperOptimalBase K R)
    (habove :
      vfMidSolvedFantasyRadialUpperOptimalBase K (R + 1) <
        optimalLogBase vfMidPrimeCount (((R + 1 : ℕ) : ℝ) ^ 2)) :
    vfMidRadialWallWidth K (R + 1) -
        vfMidRadialWallWidth K R <
      vfMidSquareBandError R := by
  have hprev :=
    abs_vfMidSquareEndpointError_le_of_optimalBase_radial_inside
      hR hinside
  have hprevUpper :
      vfMidSquareEndpointError R ≤ vfMidRadialWallWidth K R :=
    (le_abs_self _).trans hprev
  have hnext :=
    vfMidSquareEndpointError_gt_of_optimalBase_above_upper
      (K := K) (R := R + 1) (by omega) habove
  have hstep := vfMidSquareEndpointError_succ R hR
  linarith

/-- The same first crossing forces the one-block owner tracking defect to be
strictly negative by at least the wall increment. -/
theorem vfMidOptimalBase_upperFirstEscape_forces_trackingDefect
    {K : ℝ} (R : ℕ) (hR : 2 ≤ R)
    (hinside :
      vfMidSolvedFantasyRadialLowerOptimalBase K R ≤
          optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ∧
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ≤
          vfMidSolvedFantasyRadialUpperOptimalBase K R)
    (habove :
      vfMidSolvedFantasyRadialUpperOptimalBase K (R + 1) <
        optimalLogBase vfMidPrimeCount (((R + 1 : ℕ) : ℝ) ^ 2)) :
    vfMidDyadicVFTrackingDefect R (R + 1) <
      vfMidRadialWallWidth K R -
        vfMidRadialWallWidth K (R + 1) := by
  have hband :=
    vfMidOptimalBase_upperFirstEscape_forces_bandError R hR hinside habove
  have htrack :=
    vfMidDyadicVFTrackingDefect_eq_neg_primeError_increment
      hR (by omega : 2 ≤ R + 1) (Nat.le_succ R)
  have hRerr :
      vfMidPrimeError ((R : ℝ) ^ 2) =
        vfMidSquareEndpointError R := by
    symm
    change vfMidDirectSquareEndpointError R =
      vfMidPrimeError ((R : ℝ) ^ 2)
    exact vfMidDirectSquareEndpointError_eq_vfMidPrimeError hR
  have hR1err :
      vfMidPrimeError (((R + 1 : ℕ) : ℝ) ^ 2) =
        vfMidSquareEndpointError (R + 1) := by
    symm
    change vfMidDirectSquareEndpointError (R + 1) =
      vfMidPrimeError (((R + 1 : ℕ) : ℝ) ^ 2)
    exact vfMidDirectSquareEndpointError_eq_vfMidPrimeError (by omega)
  rw [hRerr, hR1err, vfMidSquareEndpointError_succ R hR] at htrack
  nlinarith

/-- **Quadratic first-crossing Lyapunov bill.**

A first escape above the upper optimal-base radial wall forces endpoint-error
energy to grow by more than the increase in squared wall radius. -/
theorem vfMidOptimalBase_upperFirstEscape_forces_energy
    {K : ℝ} (hK : 0 ≤ K)
    (R : ℕ) (hR : 2 ≤ R)
    (hinside :
      vfMidSolvedFantasyRadialLowerOptimalBase K R ≤
          optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ∧
        optimalLogBase vfMidPrimeCount ((R : ℝ) ^ 2) ≤
          vfMidSolvedFantasyRadialUpperOptimalBase K R)
    (habove :
      vfMidSolvedFantasyRadialUpperOptimalBase K (R + 1) <
        optimalLogBase vfMidPrimeCount (((R + 1 : ℕ) : ℝ) ^ 2)) :
    vfMidRadialWallWidth K (R + 1) ^ 2 -
        vfMidRadialWallWidth K R ^ 2 <
      2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 := by
  have hprev :=
    abs_vfMidSquareEndpointError_le_of_optimalBase_radial_inside
      hR hinside
  have hnext :=
    vfMidSquareEndpointError_gt_of_optimalBase_above_upper
      (K := K) (R := R + 1) (by omega) habove
  have hRge1 : (1 : ℝ) ≤ (R : ℝ) := by
    exact_mod_cast (show 1 ≤ R by omega)
  have hR1ge1 : (1 : ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ R + 1 by omega)
  have hlogR0 : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg hRge1
  have hlogR10 : 0 ≤ Real.log ((R + 1 : ℕ) : ℝ) :=
    Real.log_nonneg hR1ge1
  have hW0 : 0 ≤ vfMidRadialWallWidth K R := by
    unfold vfMidRadialWallWidth
    positivity
  have hW10 : 0 ≤ vfMidRadialWallWidth K (R + 1) := by
    unfold vfMidRadialWallWidth
    positivity
  have hprevSq :
      vfMidSquareEndpointError R ^ 2 ≤
        vfMidRadialWallWidth K R ^ 2 := by
    have hs :
        |vfMidSquareEndpointError R| ^ 2 ≤
          vfMidRadialWallWidth K R ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hW0).2 hprev
    simpa [sq_abs] using hs
  have hnext0 :
      0 ≤ vfMidSquareEndpointError (R + 1) :=
    hW10.trans (le_of_lt hnext)
  have hnextSq :
      vfMidRadialWallWidth K (R + 1) ^ 2 <
        vfMidSquareEndpointError (R + 1) ^ 2 :=
    (sq_lt_sq₀ hW10 hnext0).2 hnext
  have henergy :=
    vfMidSquareEndpointError_sq_succ_eq_correlation R hR
  nlinarith

/-! ## Aggregate physical-forcing / zero-target Gram dictionary -/

/-- Centered actual-minus-Li forcing Gram on two frozen-wheel physical
survivor blocks. -/
def vfMidActualLiCenteredCrossGram
    (A R S : ℕ) : ℂ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
    ∑ m ∈ vfMidSquarePrefixWheelSurvivors A S,
      (vfMidActualLiForcingAtom n - vfMidActualLiAffineTarget n) *
        (vfMidActualLiForcingAtom m - vfMidActualLiAffineTarget m)

/-- The same finite carrier written directly in zero-target Mobius excess
currency. -/
def vfMidZeroTargetCubeCrossGram
    (A R S : ℕ) : ℂ :=
  ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
    ∑ m ∈ vfMidSquarePrefixWheelSurvivors A S,
      ((postRootZeroTargetPairExcess (n, m) : ℝ) : ℂ)

/-- **Aggregate physical forcing / zero-target dictionary.**

On the full frozen cubic-depth carrier, the centered actual-minus-Li forcing
Gram is exactly one quarter of the owner-descending zero-target Gram. -/
theorem vfMidActualLiCenteredCrossGram_eq_quarter_zeroTarget
    {A R S : ℕ}
    (hA : 3 ≤ A) (hAR : A ≤ R) (hAS : A ≤ S)
    (hcubeR : (R + 1) ^ 2 ≤ (A + 1) ^ 3)
    (hcubeS : (S + 1) ^ 2 ≤ (A + 1) ^ 3) :
    vfMidActualLiCenteredCrossGram A R S =
      (1 / 4 : ℂ) * vfMidZeroTargetCubeCrossGram A R S := by
  unfold vfMidActualLiCenteredCrossGram vfMidZeroTargetCubeCrossGram
  calc
    (∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
      ∑ m ∈ vfMidSquarePrefixWheelSurvivors A S,
        (vfMidActualLiForcingAtom n - vfMidActualLiAffineTarget n) *
          (vfMidActualLiForcingAtom m - vfMidActualLiAffineTarget m)) =
      ∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
        ∑ m ∈ vfMidSquarePrefixWheelSurvivors A S,
          (1 / 4 : ℂ) *
            ((postRootZeroTargetPairExcess (n, m) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      simpa using
        (vfMidActualLiCenteredPair_eq_quarter_zeroTargetExcess_of_cube
          hA hAR hAS hcubeR hcubeS hn hm)
    _ =
      (1 / 4 : ℂ) *
        (∑ n ∈ vfMidSquarePrefixWheelSurvivors A R,
          ∑ m ∈ vfMidSquarePrefixWheelSurvivors A S,
            ((postRootZeroTargetPairExcess (n, m) : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.mul_sum]

end RHLean.Analysis
