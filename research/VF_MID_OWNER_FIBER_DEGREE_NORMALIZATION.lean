import Mathlib
import «research.NNS_EQUAL_ABS_DEGREE_NORMALIZATION»
import «research.RECIPROCAL_COVARIANCE_PAIR_AMPLITUDE_CONTRACTION»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONGESTION»

/-!
# Owner-fibre degree-one / degree-two normalization splice

On one fixed owner / fixed stripped-parent fibre, every reciprocal pair
amplitude has one common absolute magnitude.  Therefore the generic NNS
equal-absolute-value lemma identifies the degree-one normalized signed ratio
with the degree-two normalized signed ratio exactly.

The degree-two denominator is then literally the already-compiled reciprocal
pair energy sum, so the normalized PM coordinate and the owner L2 currency meet
without an inequality.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Every member of one fixed-owner / fixed-parent fibre has the same absolute
reciprocal amplitude. -/
theorem postRootCovarianceFixedOwnerChild_abs_amplitude_eq
    {W p : ℕ} {parent mn : ℕ × ℕ}
    (hmn : mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p) :
    |postRootCovarianceReciprocalPairAmplitude mn| =
      |(1 / (p : ℝ)) *
        postRootCovarianceReciprocalPairAmplitude parent| := by
  have hE :=
    postRootCovarianceFixedOwnerChild_energy_eq hmn
  unfold postRootCovarianceReciprocalPairEnergy at hE
  have hsq :
      |postRootCovarianceReciprocalPairAmplitude mn| ^ 2 =
        |(1 / (p : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent| ^ 2 := by
    calc
      |postRootCovarianceReciprocalPairAmplitude mn| ^ 2 =
          postRootCovarianceReciprocalPairAmplitude mn ^ 2 := by
            exact sq_abs _
      _ =
          (1 / (p : ℝ) ^ 2) *
            postRootCovarianceReciprocalPairAmplitude parent ^ 2 := hE
      _ =
          ((1 / (p : ℝ)) *
            postRootCovarianceReciprocalPairAmplitude parent) ^ 2 := by
            simp only [one_div, inv_pow, mul_pow]
      _ =
          |(1 / (p : ℝ)) *
            postRootCovarianceReciprocalPairAmplitude parent| ^ 2 := by
            symm
            exact sq_abs _
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hsame | hneg
  · exact hsame
  · have hleft :
        0 ≤ |postRootCovarianceReciprocalPairAmplitude mn| :=
      abs_nonneg _
    have hright :
        0 ≤ |(1 / (p : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent| :=
      abs_nonneg _
    nlinarith

/-- On each homogeneous owner fibre, normalized degree one and normalized
degree two are exactly the same signed coefficient. -/
theorem postRootCovarianceFixedOwner_normalizedDegreeOne_eq_degreeTwo
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        postRootCovarianceReciprocalPairAmplitude mn) /
      (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        |postRootCovarianceReciprocalPairAmplitude mn|) =
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        postRootCovarianceReciprocalPairAmplitude mn *
          |postRootCovarianceReciprocalPairAmplitude mn|) /
      (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        |postRootCovarianceReciprocalPairAmplitude mn| ^ 2) := by
  apply zeroTargetNormalizedDegreeOne_eq_degreeTwo_of_eqAbs
    (s := postRootCovarianceFixedOwnerChildFiber W parent p)
    (f := postRootCovarianceReciprocalPairAmplitude)
    (c :=
      |(1 / (p : ℝ)) *
        postRootCovarianceReciprocalPairAmplitude parent|)
  intro mn hmn
  exact postRootCovarianceFixedOwnerChild_abs_amplitude_eq hmn

/-- The degree-two PM denominator on one fixed owner fibre is literally the
reciprocal owner-energy denominator already consumed by the contraction tree. -/
theorem postRootCovarianceFixedOwner_degreeTwoDenominator_eq_energy
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        |postRootCovarianceReciprocalPairAmplitude mn| ^ 2) =
      ∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        postRootCovarianceReciprocalPairEnergy mn := by
  apply Finset.sum_congr rfl
  intro mn _hmn
  unfold postRootCovarianceReciprocalPairEnergy
  exact sq_abs _

/-- Hence the degree-two PM denominator inherits the exact compiled
multiplicity/p^2 owner formula. -/
theorem postRootCovarianceFixedOwner_degreeTwoDenominator_eq
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        |postRootCovarianceReciprocalPairAmplitude mn| ^ 2) =
      (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
          (p : ℝ) ^ 2 *
        postRootCovarianceReciprocalPairEnergy parent := by
  rw [postRootCovarianceFixedOwner_degreeTwoDenominator_eq_energy]
  exact sum_postRootCovarianceFixedOwnerChild_energy_eq W parent p


/-- Multiplying a homogeneous owner fibre by one retained scalar preserves the
common-absolute-value hypothesis needed by the degree converter. -/
theorem postRootCovarianceFixedOwnerChild_abs_retainedAmplitude_eq
    {W p : ℕ} {parent mn : ℕ × ℕ} (coefficient : ℝ)
    (hmn : mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p) :
    |coefficient * postRootCovarianceReciprocalPairAmplitude mn| =
      |coefficient *
        ((1 / (p : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent)| := by
  rw [abs_mul, abs_mul]
  rw [postRootCovarianceFixedOwnerChild_abs_amplitude_eq hmn]

/-- **Retained-coefficient degree invariance.**

This is the form consumed by the #888/#891 API: on a fixed owner/fixed parent
fibre, any one scalar retained on all children has the same normalized degree-1
and degree-2 signed ratio. -/
theorem postRootCovarianceFixedOwner_retained_normalizedDegreeOne_eq_degreeTwo
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) (coefficient : ℝ) :
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        coefficient * postRootCovarianceReciprocalPairAmplitude mn) /
      (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        |coefficient * postRootCovarianceReciprocalPairAmplitude mn|) =
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        (coefficient * postRootCovarianceReciprocalPairAmplitude mn) *
          |coefficient * postRootCovarianceReciprocalPairAmplitude mn|) /
      (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        |coefficient * postRootCovarianceReciprocalPairAmplitude mn| ^ 2) := by
  apply zeroTargetNormalizedDegreeOne_eq_degreeTwo_of_eqAbs
    (s := postRootCovarianceFixedOwnerChildFiber W parent p)
    (f := fun mn =>
      coefficient * postRootCovarianceReciprocalPairAmplitude mn)
    (c :=
      |coefficient *
        ((1 / (p : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent)|)
  intro mn hmn
  exact
    postRootCovarianceFixedOwnerChild_abs_retainedAmplitude_eq
      coefficient hmn

/-- The retained-coefficient degree-two denominator is exactly the retained
scalar square times the literal reciprocal child-energy sum. -/
theorem postRootCovarianceFixedOwner_retained_degreeTwoDenominator_eq_energy
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) (coefficient : ℝ) :
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        |coefficient * postRootCovarianceReciprocalPairAmplitude mn| ^ 2) =
      coefficient ^ 2 *
        (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
          postRootCovarianceReciprocalPairEnergy mn) := by
  calc
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        |coefficient * postRootCovarianceReciprocalPairAmplitude mn| ^ 2) =
      ∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        coefficient ^ 2 * postRootCovarianceReciprocalPairEnergy mn := by
          apply Finset.sum_congr rfl
          intro mn _hmn
          unfold postRootCovarianceReciprocalPairEnergy
          rw [sq_abs]
          ring
    _ = coefficient ^ 2 *
        (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
          postRootCovarianceReciprocalPairEnergy mn) := by
          rw [Finset.mul_sum]

/-- Therefore the retained degree-two PM denominator is already in the exact
multiplicity/p^2 parent-energy currency of the owner contraction. -/
theorem postRootCovarianceFixedOwner_retained_degreeTwoDenominator_eq
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) (coefficient : ℝ) :
    (∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        |coefficient * postRootCovarianceReciprocalPairAmplitude mn| ^ 2) =
      coefficient ^ 2 *
        ((postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
          (p : ℝ) ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent) := by
  rw [postRootCovarianceFixedOwner_retained_degreeTwoDenominator_eq_energy]
  rw [sum_postRootCovarianceFixedOwnerChild_energy_eq]


/-! ## Greatest-owner fibre used by the final clipped tree -/

/-- The final greatest-owner child fibre has the same constant-absolute
reciprocal amplitude property as the least-owner fibre. -/
theorem lowOwnerGreatestOwnerFixedParentChild_abs_amplitude_eq
    {R r : ℕ} {parent child : ℕ × ℕ}
    (hr : r.Prime)
    (hchild : child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r) :
    |postRootCovarianceReciprocalPairAmplitude child| =
      |(1 / (r : ℝ)) *
        postRootCovarianceReciprocalPairAmplitude parent| := by
  have hE := lowOwnerGreatestOwnerFixedParentChild_energy_eq hr hchild
  unfold postRootCovarianceReciprocalPairEnergy at hE
  have hsq :
      |postRootCovarianceReciprocalPairAmplitude child| ^ 2 =
        |(1 / (r : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent| ^ 2 := by
    calc
      |postRootCovarianceReciprocalPairAmplitude child| ^ 2 =
          postRootCovarianceReciprocalPairAmplitude child ^ 2 := sq_abs _
      _ = (1 / (r : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairAmplitude parent ^ 2 := hE
      _ = ((1 / (r : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent) ^ 2 := by
            simp only [one_div, inv_pow, mul_pow]
      _ = |(1 / (r : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent| ^ 2 := by
            symm
            exact sq_abs _
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hsame | hneg
  · exact hsame
  · have hleft :
        0 ≤ |postRootCovarianceReciprocalPairAmplitude child| := abs_nonneg _
    have hright :
        0 ≤ |(1 / (r : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent| := abs_nonneg _
    nlinarith

/-- Multiplying the final greatest-owner fibre by one retained scalar preserves
the equal-absolute-value hypothesis. -/
theorem lowOwnerGreatestOwnerFixedParentChild_abs_retainedAmplitude_eq
    {R r : ℕ} {parent child : ℕ × ℕ} (coefficient : ℝ)
    (hr : r.Prime)
    (hchild : child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r) :
    |coefficient * postRootCovarianceReciprocalPairAmplitude child| =
      |coefficient *
        ((1 / (r : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent)| := by
  rw [abs_mul, abs_mul]
  rw [lowOwnerGreatestOwnerFixedParentChild_abs_amplitude_eq hr hchild]

/-- **Final-tree retained-coefficient degree invariance.**

This is the exact homogeneous fibre used by #891. -/
theorem lowOwnerGreatestOwnerFixedParent_retained_normalizedDegreeOne_eq_degreeTwo
    {R r : ℕ} (hr : r.Prime)
    (parent : ℕ × ℕ) (coefficient : ℝ) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        coefficient * postRootCovarianceReciprocalPairAmplitude child) /
      (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        |coefficient * postRootCovarianceReciprocalPairAmplitude child|) =
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        (coefficient * postRootCovarianceReciprocalPairAmplitude child) *
          |coefficient * postRootCovarianceReciprocalPairAmplitude child|) /
      (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        |coefficient * postRootCovarianceReciprocalPairAmplitude child| ^ 2) := by
  apply zeroTargetNormalizedDegreeOne_eq_degreeTwo_of_eqAbs
    (s := lowOwnerGreatestOwnerFixedParentChildFiber R parent r)
    (f := fun child =>
      coefficient * postRootCovarianceReciprocalPairAmplitude child)
    (c :=
      |coefficient *
        ((1 / (r : ℝ)) *
          postRootCovarianceReciprocalPairAmplitude parent)|)
  intro child hchild
  exact lowOwnerGreatestOwnerFixedParentChild_abs_retainedAmplitude_eq
    coefficient hr hchild

/-- The final-tree degree-two denominator is exactly the retained-coefficient
child energy already consumed by the #891 tree. -/
theorem lowOwnerGreatestOwnerFixedParent_retained_degreeTwoDenominator_eq_energy
    (R r : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        |coefficient * postRootCovarianceReciprocalPairAmplitude child| ^ 2) =
      coefficient ^ 2 *
        (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
          postRootCovarianceReciprocalPairEnergy child) := by
  calc
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        |coefficient * postRootCovarianceReciprocalPairAmplitude child| ^ 2) =
      ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        coefficient ^ 2 * postRootCovarianceReciprocalPairEnergy child := by
          apply Finset.sum_congr rfl
          intro child _hchild
          unfold postRootCovarianceReciprocalPairEnergy
          rw [sq_abs]
          ring
    _ = coefficient ^ 2 *
        (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
          postRootCovarianceReciprocalPairEnergy child) := by
          rw [Finset.mul_sum]

/-- With a genuine greatest owner, the same denominator is the exact
multiplicity/r^2 retained parent energy. -/
theorem lowOwnerGreatestOwnerFixedParent_retained_degreeTwoDenominator_eq
    {R r : ℕ} (hr : r.Prime)
    (parent : ℕ × ℕ) (coefficient : ℝ) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
        |coefficient * postRootCovarianceReciprocalPairAmplitude child| ^ 2) =
      coefficient ^ 2 *
        ((lowOwnerGreatestOwnerFixedParentChildMultiplicity
            R parent r : ℝ) / (r : ℝ) ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent) := by
  rw [lowOwnerGreatestOwnerFixedParent_retained_degreeTwoDenominator_eq_energy]
  rw [sum_lowOwnerGreatestOwnerFixedParentChild_energy_eq hr]

end RHLean.Proof
