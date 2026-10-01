import Mathlib
import «research.VF_MID_DYADIC_SUMMATION_TRANSFER»

/-!
# Phi cutoff telescope for the VF chronological-owner transfer

The owner-level decomposition can be compressed further.

For a frequency state S, put

  I_S(R,y) =
    Phi_S((R+1)^2-1,y) - Phi_S(R^2,y).

The transformed cutoff recurrence implies

  I_S(R,q)
    = I_S(R,q-1) - w(q) C_S(R,q),

where C_S(R,q) is exactly the two cofactor-endpoint difference occurring in
one owner fibre.  Summing in q telescopes.

Consequently the difference between the actual-prime weighted owner removal
and the Li-weighted removal is not a sum of uncontrolled owner errors: it is
an exact difference of transformed displacement boundary values.

This file records that exact compression.  No quantitative displacement bound
is asserted.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Parent square-interval difference of one transformed frequency state at
cutoff y. -/
def vfMidPhiSquareInterval
    (S : ℕ → ℕ → ℂ) (R y : ℕ) : ℂ :=
  primeFrequencyCumulativeTransform S ((R + 1) ^ 2 - 1) y -
    primeFrequencyCumulativeTransform S (R ^ 2) y

/-- The child/cofactor endpoint interval attached to owner site q. -/
def vfMidPhiOwnerChildInterval
    (S : ℕ → ℕ → ℂ) (R q : ℕ) : ℂ :=
  primeFrequencyCumulativeTransform S
      (((R + 1) ^ 2 - 1) / q) (q - 1) -
    primeFrequencyCumulativeTransform S
      (R ^ 2 / q) (q - 1)

/-- The transformed square interval inherits the exact one-site cutoff
recurrence. -/
theorem vfMidPhiSquareInterval_cutoff_step
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    (R q : ℕ) (hq : 2 ≤ q) :
    vfMidPhiSquareInterval S R q =
      vfMidPhiSquareInterval S R (q - 1) -
        w q * vfMidPhiOwnerChildInterval S R q := by
  unfold vfMidPhiSquareInterval vfMidPhiOwnerChildInterval
  rw [primeFrequencyCumulativeTransform_cutoff_step
        hS ((R + 1) ^ 2 - 1) q hq,
      primeFrequencyCumulativeTransform_cutoff_step
        hS (R ^ 2) q hq]
  ring

/-- Weighted removal accumulated while the cutoff moves from z to y. -/
def vfMidPhiWeightedCutoffRemoval
    (w : ℕ → ℂ) (S : ℕ → ℕ → ℂ)
    (R z y : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc z y,
    w q * vfMidPhiOwnerChildInterval S R q

/-- **Exact cutoff telescope.**
The complete weighted child removal is exactly the drop of the parent
square-interval transformed state. -/
theorem vfMidPhiWeightedCutoffRemoval_eq_interval_sub
    {w : ℕ → ℂ} {S : ℕ → ℕ → ℂ}
    (hS : IsPrimeFrequencyState w S)
    (R z y : ℕ) (hz : 1 ≤ z) (hzy : z ≤ y) :
    vfMidPhiWeightedCutoffRemoval w S R z y =
      vfMidPhiSquareInterval S R z -
        vfMidPhiSquareInterval S R y := by
  induction y with
  | zero =>
      have : z = 0 := by omega
      omega
  | succ y ih =>
      by_cases h : z ≤ y
      · rw [vfMidPhiWeightedCutoffRemoval,
          Finset.sum_Ioc_succ_top h]
        have hi := ih h
        rw [vfMidPhiWeightedCutoffRemoval] at hi
        rw [hi]
        have hstep :=
          vfMidPhiSquareInterval_cutoff_step
            hS R (y + 1) (by omega : 2 ≤ y + 1)
        simp only [Nat.add_sub_cancel] at hstep
        rw [hstep]
        ring
      · have heq : z = y + 1 := by omega
        subst z
        simp [vfMidPhiWeightedCutoffRemoval]

/-- Parent square-interval difference of the transformed actual-minus-Li
displacement. -/
def vfMidPhiSquareDisplacementInterval
    (Actual L : ℕ → ℕ → ℂ) (R y : ℕ) : ℂ :=
  primeFrequencyCumulativeDisplacement Actual L ((R + 1) ^ 2 - 1) y -
    primeFrequencyCumulativeDisplacement Actual L (R ^ 2) y

theorem vfMidPhiSquareDisplacementInterval_eq_actual_sub_li
    (Actual L : ℕ → ℕ → ℂ) (R y : ℕ) :
    vfMidPhiSquareDisplacementInterval Actual L R y =
      vfMidPhiSquareInterval Actual R y -
        vfMidPhiSquareInterval L R y := by
  unfold vfMidPhiSquareDisplacementInterval
    vfMidPhiSquareInterval
    primeFrequencyCumulativeDisplacement
  ring

/-- **Displacement telescope.**
Actual weighted removals minus Li-weighted removals collapse exactly to the
two displacement boundary cutoffs z and y. -/
theorem vfMidPhiActual_sub_liWeightedRemoval_eq_displacementBoundaries
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    (R z y : ℕ) (hz : 1 ≤ z) (hzy : z ≤ y) :
    vfMidPhiWeightedCutoffRemoval
        primeSievePrimeIndicator Actual R z y -
      vfMidPhiWeightedCutoffRemoval
        primeSievePNTDensity L R z y =
      vfMidPhiSquareDisplacementInterval Actual L R z -
        vfMidPhiSquareDisplacementInterval Actual L R y := by
  have hA :=
    vfMidPhiWeightedCutoffRemoval_eq_interval_sub
      (w := primeSievePrimeIndicator) hActual R z y hz hzy
  have hLi :=
    vfMidPhiWeightedCutoffRemoval_eq_interval_sub
      (w := primeSievePNTDensity) hL R z y hz hzy
  rw [hA, hLi,
    vfMidPhiSquareDisplacementInterval_eq_actual_sub_li,
    vfMidPhiSquareDisplacementInterval_eq_actual_sub_li]
  ring

/-- For z >= 2, the late-owner carrier is exactly the prime-filtered integer
cutoff interval (z,R]. -/
theorem vfMidSquareBandLateOwnerPrimes_eq_Ioc_filter_prime
    (z R : ℕ) :
    vfMidSquareBandLateOwnerPrimes z R =
      (Finset.Ioc z R).filter Nat.Prime := by
  ext p
  simp only [mem_vfMidSquareBandLateOwnerPrimes,
    mem_vfMidSquareBandOwnerPrimes,
    Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hp, hpR⟩, hzp⟩
    exact ⟨⟨hzp, hpR⟩, hp⟩
  · rintro ⟨⟨hzp, hpR⟩, hp⟩
    exact ⟨⟨hp, hpR⟩, hzp⟩

/-- The physical owner census of one square block is exactly the
prime-indicator weighted Phi child-removal sum. -/
theorem vfMidSquareBandLateOwnerCards_cast_eq_actualWeightedPhiRemoval
    {Actual : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    {z R : ℕ} (hR : 3 ≤ R) :
    ((∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
        (vfMidSquareBandCompositeOwner R p).card : ℕ) : ℂ) =
      vfMidPhiWeightedCutoffRemoval
        primeSievePrimeIndicator Actual R z R := by
  rw [vfMidSquareBandLateOwnerPrimes_eq_Ioc_filter_prime z R]
  unfold vfMidPhiWeightedCutoffRemoval
  rw [Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hp : q.Prime
  · have hqR : q ≤ R := (Finset.mem_Ioc.mp hq).2
    have hqOwner :
        q ∈ vfMidSquareBandOwnerPrimes R :=
      mem_vfMidSquareBandOwnerPrimes.mpr ⟨hp, hqR⟩
    have howner :=
      vfMidSquareBandCompositeOwner_card_eq_actualPhiDifference
        hActual hR hqOwner
    simp only [hp, if_true, primeSievePrimeIndicator]
    simpa [vfMidPhiOwnerChildInterval] using howner
  · simp [hp, primeSievePrimeIndicator]

/-- **One-block transfer compression.**
The physical actual-prime owner census equals the pure Li weighted removal
plus only two transformed displacement boundary terms. -/
theorem vfMidSquareBandLateOwnerCards_cast_eq_liRemoval_add_displacementBoundary
    {Actual L : ℕ → ℕ → ℂ}
    (hActual : IsAllScaleActualPrimeState Actual)
    (hL : IsAllScaleLiState L)
    {z R : ℕ} (hz : 2 ≤ z) (hzR : z ≤ R) (hR : 3 ≤ R) :
    ((∑ p ∈ vfMidSquareBandLateOwnerPrimes z R,
        (vfMidSquareBandCompositeOwner R p).card : ℕ) : ℂ) =
      vfMidPhiWeightedCutoffRemoval
          primeSievePNTDensity L R z R +
        (vfMidPhiSquareDisplacementInterval Actual L R z -
          vfMidPhiSquareDisplacementInterval Actual L R R) := by
  rw [vfMidSquareBandLateOwnerCards_cast_eq_actualWeightedPhiRemoval
      hActual hR]
  have hdisp :=
    vfMidPhiActual_sub_liWeightedRemoval_eq_displacementBoundaries
      hActual hL R z R (by omega) hzR
  linear_combination hdisp

/-- The Li weighted owner removal itself is a pure cutoff boundary difference. -/
theorem vfMidPhiLiWeightedRemoval_eq_interval_sub
    {L : ℕ → ℕ → ℂ}
    (hL : IsAllScaleLiState L)
    (R z y : ℕ) (hz : 1 ≤ z) (hzy : z ≤ y) :
    vfMidPhiWeightedCutoffRemoval
        primeSievePNTDensity L R z y =
      vfMidPhiSquareInterval L R z -
        vfMidPhiSquareInterval L R y :=
  vfMidPhiWeightedCutoffRemoval_eq_interval_sub
    hL R z y hz hzy

end RHLean.Analysis
