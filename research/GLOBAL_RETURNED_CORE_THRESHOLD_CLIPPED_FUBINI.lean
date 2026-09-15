import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_INCIDENCE_CLOSURE»
import «research.ZERO_TARGET_CLIPPED_OWNER_ENERGY_CONTRACTION»

/-!
# Second-owner threshold residual is a finite sum of clipped edges

The current first-owner incidence uses the half-open threshold crossing

  chi_p(n,y) = 1_{n <= y < p*n}.

For a second owner `r`, multiplicative incidences commute pointwise:

  chi_p(n,y) - chi_p(r*n,y)
    = chi_r(n,y) - chi_r(p*n,y).

Therefore, after integrating against the *finite* AMP threshold measure

  nu_R = sum_q (1/q) delta_{Y_q} - delta_{R-1},

the entire second-owner difference is a signed Fubini sum of literal
`r`-clipped edges at the sampled endpoints.  There is no abstract spectral
remainder here.

The final lemmas identify a nonzero threshold crossing with the exact geometric
predicate used by `postRootCovarianceCriticalClippedOwnerFactor`: when the
crossing is active, the owner factor is literally `(1-1/r)^2`.

No norm or magnitude estimate is introduced.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Difference of two literal r-clipped threshold edges, at a site and its
current p-child. -/
def lowOwnerThresholdClippedDifference
    (p r n y : ℕ) : ℝ :=
  lowOwnerThresholdCrossingIndicator r n y -
    lowOwnerThresholdCrossingIndicator r (p * n) y

/-- Current p-incidence written directly against the finite threshold measure. -/
theorem lowOwnerThresholdOwnerIncidenceWeight_eq_finiteThresholdEval
    {R p n : ℕ} (hR : 1 ≤ R) (hp : 1 ≤ p) :
    lowOwnerThresholdOwnerIncidenceWeight R p n =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerThresholdCrossingIndicator
            p n (rawQ2ChildCutoff R q)) -
        lowOwnerThresholdCrossingIndicator p n (R - 1) := by
  rw [lowOwnerThresholdOwnerIncidenceWeight_eq_crossing hp,
    lowOwnerDaughterCrossingWeight_eq_threshold_sum,
    lowOwnerRootCrossingIndicator_eq_threshold_R_sub_one hR]

/-- **Finite clipped Fubini.**  The next-owner difference of the current
threshold incidence is exactly the signed finite sum of r-clipped edge
differences at the q^2 daughter thresholds and the root threshold. -/
theorem lowOwnerThresholdSecondOwnerDifference_eq_clippedFubini
    {R p r n : ℕ} (hR : 1 ≤ R) (hp : 1 ≤ p) (hr : 1 ≤ r) :
    lowOwnerThresholdSecondOwnerDifference R p r n =
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (1 / (q : ℝ)) *
          lowOwnerThresholdClippedDifference
            p r n (rawQ2ChildCutoff R q)) -
        lowOwnerThresholdClippedDifference p r n (R - 1) := by
  unfold lowOwnerThresholdSecondOwnerDifference
  rw [lowOwnerThresholdOwnerIncidenceWeight_eq_finiteThresholdEval hR hp,
    lowOwnerThresholdOwnerIncidenceWeight_eq_finiteThresholdEval hR hp]
  rw [← Finset.sum_sub_distrib]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro q _hq
    unfold lowOwnerThresholdClippedDifference
    rw [lowOwnerThresholdCrossing_secondIncidence_comm hp hr]
    ring
  · unfold lowOwnerThresholdClippedDifference
    rw [lowOwnerThresholdCrossing_secondIncidence_comm hp hr]

/-- Active threshold crossing is exactly the one-coordinate clipped geometry. -/
theorem lowOwnerThresholdCrossingIndicator_eq_one_iff
    {r n y : ℕ} :
    lowOwnerThresholdCrossingIndicator r n y = 1 ↔
      n ≤ y ∧ y < r * n := by
  unfold lowOwnerThresholdCrossingIndicator
  by_cases h : n ≤ y ∧ y < r * n <;> simp [h]

/-- Vanishing/nonvanishing dichotomy for one threshold crossing. -/
theorem lowOwnerThresholdCrossingIndicator_eq_zero_or_one
    (r n y : ℕ) :
    lowOwnerThresholdCrossingIndicator r n y = 0 ∨
      lowOwnerThresholdCrossingIndicator r n y = 1 := by
  unfold lowOwnerThresholdCrossingIndicator
  split <;> simp

/-- An active r-threshold edge turns on exactly the geometric clipped-owner
factor used by the reciprocal covariance energy. -/
theorem criticalClippedOwnerFactor_eq_of_thresholdCrossing
    {r n y a : ℕ}
    (hcross : lowOwnerThresholdCrossingIndicator r n y = 1) :
    postRootCovarianceCriticalClippedOwnerFactor y (a, n) r =
      (1 - 1 / (r : ℝ)) ^ 2 := by
  have hgeom :=
    (lowOwnerThresholdCrossingIndicator_eq_one_iff.mp hcross).2
  simp [postRootCovarianceCriticalClippedOwnerFactor, hgeom]

/-- Conversely, an inactive crossing with no r-clipping gives zero clipped-owner
factor. -/
theorem criticalClippedOwnerFactor_eq_zero_of_not_crossing_upper
    {r n y a : ℕ} (hnot : ¬ y < r * n) :
    postRootCovarianceCriticalClippedOwnerFactor y (a, n) r = 0 := by
  simp [postRootCovarianceCriticalClippedOwnerFactor, hnot]

end RHLean.Proof
