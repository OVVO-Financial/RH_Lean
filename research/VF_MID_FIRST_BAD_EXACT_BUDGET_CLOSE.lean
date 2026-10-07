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

/-- The literal #914 returned weight is a retained scalar times the bare
zero-target Mobius pair excess.  Naming the scalar makes it possible to carry
the *actual* VF coefficient unchanged through greatest-owner stripping instead
of replacing it by a square or an absolute majorant. -/
def vfMidActiveReturnedPairRetainedScalar
    (R p : ℕ) (sig : Finset ℕ) (ab : ℕ × ℕ) : ℝ :=
  if ab ∈ vfMidActiveReturnedPairCarrier R p sig then
    (vfMidActiveMobiusScale R ab.1 *
      vfMidActiveMobiusScale R (p * ab.2)) *
      (lowOwnerDirichletIncidenceCoefficient (R + 1) p ab.1 *
          lowOwnerDirichletIncidenceCoefficient (R + 1) p ab.2 -
        lowOwnerDirichletBaseCoefficient (R + 1) ab.1 *
          lowOwnerDirichletBaseCoefficient (R + 1) ab.2 -
        lowOwnerDirichletReturnedCoefficient (R + 1) p ab.1 *
          lowOwnerDirichletReturnedCoefficient (R + 1) p ab.2)
  else 0

theorem vfMidActiveReturnedPairWeight_eq_retainedScalar_mul_zeroTarget
    (R p : ℕ) (sig : Finset ℕ) (ab : ℕ × ℕ) :
    vfMidActiveReturnedPairWeight R p sig ab =
      vfMidActiveReturnedPairRetainedScalar R p sig ab *
        postRootZeroTargetPairExcess ab := by
  by_cases hmem : ab ∈ vfMidActiveReturnedPairCarrier R p sig
  · rw [vfMidActiveReturnedPairWeight, if_pos hmem,
      vfMidActiveReturnedPairRetainedScalar, if_pos hmem,
      lowOwnerFirstOwnerDirichletPolarizationAtom_eq_scalar,
      postRootZeroTargetPairExcess_eq_weight]
    ring
  · simp [vfMidActiveReturnedPairWeight,
      vfMidActiveReturnedPairRetainedScalar, hmem]

theorem vfMidActiveReturnedPairCoDivExcess_eq_retainedScalar
    (R p : ℕ) (sig : Finset ℕ) (ab : ℕ × ℕ) :
    vfMidActiveReturnedPairCoDivExcess R p sig ab =
      vfMidPointwiseCoDivExcess
        (vfMidActiveReturnedPairRetainedScalar R p sig ab *
          postRootZeroTargetPairExcess ab) := by
  unfold vfMidActiveReturnedPairCoDivExcess
  rw [vfMidActiveReturnedPairWeight_eq_retainedScalar_mul_zeroTarget]

/-- Every child in a fixed polarization raw-parent fibre is already on the
legal descending greatest-owner carrier for that raw parent owner. -/
theorem lowOwnerFirstOwnerPolarizationFixedRawParentFiber_mem_descendingCross
    {R p r : ℕ} {sig : Finset ℕ} {parent child : ℕ × ℕ}
    (hr : r.Prime)
    (hchild : child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        R p sig r parent) :
    child ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R r) r := by
  have hgreat :
      child ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber
        R p sig r :=
    (Finset.mem_filter.mp hchild).1
  have hoff :
      child ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier R p sig :=
    (Finset.mem_filter.mp hgreat).1
  have hprod :
      child ∈
        (lowOwnerFirstOwnerBaseFiber R p sig).product
          (lowOwnerFirstOwnerBaseFiber R p sig) :=
    (Finset.mem_filter.mp hoff).1
  rcases Finset.mem_product.mp hprod with ⟨ha, hb⟩
  have haCar : child.1 ∈ lowOwnerNonzeroMobiusCarrier R :=
    (Finset.mem_filter.mp ha).1
  have hbCar : child.2 ∈ lowOwnerNonzeroMobiusCarrier R :=
    (Finset.mem_filter.mp hb).1
  have howner : IsSquarefreePairGreatestFreshPrimeOwner r child.1 child.2 :=
    (Finset.mem_filter.mp hgreat).2
  exact
    (mem_descendingCrossPair_iff_greatestFreshOwner hr).2
      ⟨haCar, hbCar, howner⟩

/-- **Actual-weight local owner heat.**

For a literal #914 returned child, retain its exact VF scalar and transport that
same scalar to the stripped greatest-owner parent.  The pair is nonpositive in
the production Co/Div observable.  No reciprocal norm and no coefficient
replacement is used. -/
theorem vfMidActiveReturnedPairCoDivExcess_add_strippedParent_nonpos
    {R p r : ℕ} {sig : Finset ℕ} {parent child : ℕ × ℕ}
    (hr : r.Prime)
    (hchild : child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        (R + 1) p sig r parent) :
    vfMidActiveReturnedPairCoDivExcess R p sig child +
      vfMidPointwiseCoDivExcess
        (vfMidActiveReturnedPairRetainedScalar R p sig child *
          postRootZeroTargetPairExcess
            (squarefreePrimeFamilyParent r child.1,
              squarefreePrimeFamilyParent r child.2)) ≤ 0 := by
  rw [vfMidActiveReturnedPairCoDivExcess_eq_retainedScalar]
  exact
    descendingGreatestOwner_retainedScalar_pointwiseCoDivExcess_pair_nonpos
      hr
      (lowOwnerFirstOwnerPolarizationFixedRawParentFiber_mem_descendingCross
        hr hchild)
      (vfMidActiveReturnedPairRetainedScalar R p sig child)

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
