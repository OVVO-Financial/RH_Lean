import Mathlib
import «research.VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION»

/-!
# Unconditional close of the exact first-bad budget

This PR is stacked on #914. It assumes the exact #914 signed-boundary/heat
normal form compiles and attacks only the unconditional inequality

  vfMidFirstBadAnchoredCoDivExcess R <= 0

under a genuine K=2 first-bad hypothesis.

There is no budget proposition, no conditional budget consumer, and no new
analytic hypothesis in this module.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- The greatest-owner sign reversal remains exact for an arbitrary retained
scalar, not only a square coefficient. This is the form needed when the
active VF source contributes a parentwise retained multiplier which is not
naturally presented as a square. -/
theorem descendingGreatestOwner_retainedScalar_zeroTargetExcess_flip
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    coefficient * postRootZeroTargetPairExcess (m, n) =
      -(coefficient * postRootZeroTargetPairExcess (um, un)) := by
  have hdesc := descendingGreatestOwner_reciprocal_descent hp hcross
  dsimp only at hdesc ⊢
  rw [postRootZeroTargetPairExcess_eq_weight,
    postRootZeroTargetPairExcess_eq_weight,
    hdesc.2.1]
  ring

/-- Exact Co/Div heat for the same arbitrary retained scalar. -/
theorem descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_eq_heat
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    vfMidPointwiseCoDivExcess
        (coefficient * postRootZeroTargetPairExcess (m, n)) +
      vfMidPointwiseCoDivExcess
        (coefficient * postRootZeroTargetPairExcess (um, un)) =
      -4 * |coefficient * postRootZeroTargetPairExcess (m, n)| := by
  have hflip :=
    descendingGreatestOwner_retainedScalar_zeroTargetExcess_flip
      hp hcross coefficient
  dsimp only at hflip ⊢
  rw [hflip, abs_neg]
  simpa only [add_comm] using
    (vfMidPointwiseCoDivExcess_add_neg
      (coefficient *
        postRootZeroTargetPairExcess
          (squarefreePrimeFamilyParent p m,
            squarefreePrimeFamilyParent p n)))

/-- The arbitrary-retained owner pair is therefore cooling in the exact
Co/Div currency. -/
theorem descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_nonpos
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    vfMidPointwiseCoDivExcess
        (coefficient * postRootZeroTargetPairExcess (m, n)) +
      vfMidPointwiseCoDivExcess
        (coefficient * postRootZeroTargetPairExcess (um, un)) ≤ 0 := by
  dsimp only
  rw [descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_eq_heat
    hp hcross coefficient]
  have hnonneg :
      0 ≤ |coefficient * postRootZeroTargetPairExcess (m, n)| :=
    abs_nonneg _
  nlinarith

/-- Production target: unconditional exact first-bad budget close.

The proof starts from the endpoint-sign restoring decomposition while retaining
all already-compiled cooling. The remaining unsolved goals are therefore the
source-side owner-orbit inequalities themselves, not another conditional
interface. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_activeExcess_nonpos
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
  have h3 : 3 ≤ R := by omega
  by_cases hB : 0 ≤ vfMidActualPrimeEndpointDefect (R + 1)
  · rw [vfMidFirstBadAnchoredCoDivExcess_eq_upper_restoring_slack h3]
    have hcool :=
      vfMidFirstBadUpperRestoringAnchorSlack_nonpos h3 hfirst hB
    nlinarith
  · have hB' : vfMidActualPrimeEndpointDefect (R + 1) ≤ 0 :=
      le_of_not_ge hB
    rw [vfMidFirstBadAnchoredCoDivExcess_eq_lower_restoring_slack h3]
    have hcool :=
      vfMidFirstBadLowerRestoringAnchorSlack_nonpos h3 hfirst hB'
    nlinarith

end RHLean.Analysis
