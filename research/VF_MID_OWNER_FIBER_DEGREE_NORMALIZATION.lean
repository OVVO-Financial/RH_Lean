import Mathlib
import «research.NNS_EQUAL_ABS_DEGREE_NORMALIZATION»
import «research.RECIPROCAL_COVARIANCE_PAIR_AMPLITUDE_CONTRACTION»

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

end RHLean.Proof
