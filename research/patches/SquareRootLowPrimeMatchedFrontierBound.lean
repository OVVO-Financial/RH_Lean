import Mathlib
import RHLean.Proof.SquareRootLowPrimeQuantitativeEnergyReduction
import RHLean.Proof.SquareRootLowPrimeSignedResponseMatching

/-!
# Real deep-increment bound by the complete matched frontier

The complete signed response-child carrier has undergone every available
fresh-prime matching. The actual real increment on `(K,U]` is therefore bounded
by the cardinality of the single remaining matching frontier.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Arithmetic
open RHLean.Analysis

attribute [local instance] Classical.propDecidable

theorem squareRootLowPrimeOwnedResponseChildren_realWeightSum_eq_intCast
    (R K U : ℕ) :
    (∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
      (canonicalMoebiusWeight n).re) =
      ((∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n : ℤ) : ℝ) := by
  calc
    (∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
      (canonicalMoebiusWeight n).re) =
      ∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, (μ n : ℝ) := by
        apply Finset.sum_congr rfl
        intro n _hn
        simp [canonicalMoebiusWeight]
    _ = ((∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n : ℤ) : ℝ) := by
      push_cast
      rfl

theorem squareRootLowPrimeOwnedResponseChildren_realWeightSum_eq_matchingFrontier
    (R K U : ℕ) :
    (∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
      (canonicalMoebiusWeight n).re) =
      ∑ n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U,
        (μ n : ℝ) := by
  have hInt :=
    squareRootLowPrimeOwnedResponseChildren_moebiusSum_eq_matchingFrontier
      R K U
  have hReal := congrArg (fun z : ℤ => (z : ℝ)) hInt
  calc
    (∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
      (canonicalMoebiusWeight n).re) =
      ((∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U, μ n : ℤ) : ℝ) :=
        squareRootLowPrimeOwnedResponseChildren_realWeightSum_eq_intCast R K U
    _ = ((∑ n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U,
          μ n : ℤ) : ℝ) := hReal
    _ = ∑ n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U,
          (μ n : ℝ) := by
      push_cast
      rfl

theorem abs_squareRootLowPrimeOwnedResponseChildren_realWeightSum_le_frontierCard
    (R K U : ℕ) :
    |∑ n ∈ squareRootLowPrimeOwnedResponseChildren R K U,
      (canonicalMoebiusWeight n).re| ≤
      ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) := by
  rw [squareRootLowPrimeOwnedResponseChildren_realWeightSum_eq_matchingFrontier]
  calc
    |∑ n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U,
        (μ n : ℝ)| ≤
      ∑ n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U,
        |(μ n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ squareRootLowPrimeOwnedResponseMatchingFrontier R K U,
        (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    _ = ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) := by
      simp

theorem abs_squareRootLowPrimeFreshIncrementReal_sum_le_matchingFrontierCard
    {R K j U : ℕ} (hR : 2 ≤ R) (hUR : U < R) :
    |∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrementReal R K j p| ≤
      ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) := by
  rw [squareRootLowPrimeFreshIncrementReal_sum_eq_neg_ownedResponseChildrenMass
    hR hUR, abs_neg]
  exact
    abs_squareRootLowPrimeOwnedResponseChildren_realWeightSum_le_frontierCard
      R K U

theorem abs_squareRootLowPrimeFreshIncrementReal_sum_le_of_frontierCard
    {R K j U : ℕ} (B : ℝ)
    (hR : 2 ≤ R) (hUR : U < R)
    (hfrontier :
      ((squareRootLowPrimeOwnedResponseMatchingFrontier R K U).card : ℝ) ≤ B) :
    |∑ p ∈ squareRootLowPrimeFreshPrimeSet K U,
      squareRootLowPrimeFreshIncrementReal R K j p| ≤ B := by
  exact
    (abs_squareRootLowPrimeFreshIncrementReal_sum_le_matchingFrontierCard
      (R := R) (K := K) (j := j) (U := U) hR hUR).trans hfrontier

end RHLean.Proof
