import Mathlib
import «research.EULER_HYBRID_TRIANGULAR_GRAM_20261027»
import RHLean.Analysis.NativePNTMertens

/-!
# Exact original Möbius fractional Euler bilinear and divisor-row subtraction

X_R = R^2 - 1. We use rational fractional parts to retain the exact
integer root corner without analytic approximations. The original floor
bilinear, its continuous rank-one part, and its fractional signed source
are finite arithmetic objects. No estimate on the signed off-diagonal
source, finite-C hypothesis, improved exponent or RH is asserted.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- The **actual** integer Möbius coefficient, embedded in rationals. -/
def eulerMuQ (n : ℕ) : ℚ := ((μ n : ℤ) : ℚ)

/-- Historical reciprocal Möbius prefix. -/
def eulerReciprocalHistoricalQ (R : ℕ) : ℚ :=
  ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a / (a : ℚ)

/-- Full self-dual original floor kernel, at the exact integer cutoff. -/
def eulerFloorQ (R a b : ℕ) : ℚ :=
  ((squareRootEndpoint R / (a * b) : ℕ) : ℚ)

/-- Its complete continuous kernel, *before* replacing floors. -/
def eulerContinuousQ (R a b : ℕ) : ℚ :=
  (squareRootEndpoint R : ℚ) / ((a : ℚ) * (b : ℚ))

/-- The exact sawtooth difference; on positive a,b it is {X/(ab)}. -/
def eulerFractionQ (R a b : ℕ) : ℚ :=
  eulerContinuousQ R a b - eulerFloorQ R a b

/-- The original double Möbius bilinear, with rational rather than complex coefficients. -/
def eulerFloorBilinearQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * eulerFloorQ R a b

/-- The signed continuous rank-one double source. -/
def eulerContinuousBilinearQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * eulerContinuousQ R a b

/-- The **complete** original signed fractional double source; no absolute values. -/
def eulerFractionBilinearQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (R - 1), eulerMuQ a * eulerFractionQ R a b

/-- Fractional diagonal, with original Möbius squarefree zero coefficients. -/
def eulerFractionDiagonalQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    eulerMuQ b ^ 2 * eulerFractionQ R b b

/-- Original strict signed off-diagonal fractional Gram; no arbitrary weights. -/
def eulerFractionOffQ (R : ℕ) : ℚ :=
  ∑ b ∈ Finset.Icc 1 (R - 1), eulerMuQ b *
    ∑ a ∈ Finset.Icc 1 (b - 1), eulerMuQ a * eulerFractionQ R a b

/-- One exact finite-mode decomposition; neither source is bounded separately. -/
theorem eulerFloorBilinearQ_eq_continuous_sub_fractional (R : ℕ) :
    eulerFloorBilinearQ R =
      eulerContinuousBilinearQ R - eulerFractionBilinearQ R := by
  unfold eulerFloorBilinearQ eulerContinuousBilinearQ eulerFractionBilinearQ
  calc
    (∑ b ∈ Finset.Icc 1 (R - 1),
      eulerMuQ b * ∑ a ∈ Finset.Icc 1 (R - 1),
        eulerMuQ a * eulerFloorQ R a b) =
      ∑ b ∈ Finset.Icc 1 (R - 1),
        eulerMuQ b * ∑ a ∈ Finset.Icc 1 (R - 1),
          eulerMuQ a * (eulerContinuousQ R a b - eulerFractionQ R a b) := by
            apply Finset.sum_congr rfl
            intro b _hb
            congr 1
            apply Finset.sum_congr rfl
            intro a _ha
            unfold eulerFractionQ
            ring
    _ = (∑ b ∈ Finset.Icc 1 (R - 1),
          eulerMuQ b * ∑ a ∈ Finset.Icc 1 (R - 1),
            eulerMuQ a * eulerContinuousQ R a b) -
        (∑ b ∈ Finset.Icc 1 (R - 1),
          eulerMuQ b * ∑ a ∈ Finset.Icc 1 (R - 1),
            eulerMuQ a * eulerFractionQ R a b) := by
          simp_rw [mul_sub, Finset.sum_sub_distrib]
          simp_rw [mul_sub, Finset.sum_sub_distrib]

/-- The continuous bilinear is an *exact rank-one square*. -/
theorem eulerContinuousBilinearQ_eq_reciprocal_square (R : ℕ) :
    eulerContinuousBilinearQ R =
      (squareRootEndpoint R : ℚ) * eulerReciprocalHistoricalQ R ^ 2 := by
  unfold eulerContinuousBilinearQ eulerReciprocalHistoricalQ
  let S := Finset.Icc 1 (R - 1)
  have hterm (a b : ℕ) :
      eulerMuQ b * (eulerMuQ a * eulerContinuousQ R a b) =
        ((squareRootEndpoint R : ℚ) * (eulerMuQ b / (b : ℚ))) *
          (eulerMuQ a / (a : ℚ)) := by
    unfold eulerContinuousQ
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  calc
    (∑ b ∈ S, eulerMuQ b * ∑ a ∈ S,
      eulerMuQ a * eulerContinuousQ R a b) =
      ∑ b ∈ S, ((squareRootEndpoint R : ℚ) * (eulerMuQ b / (b : ℚ))) *
        ∑ a ∈ S, eulerMuQ a / (a : ℚ) := by
          apply Finset.sum_congr rfl
          intro b _hb
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _ha
          exact hterm a b
    _ = (squareRootEndpoint R : ℚ) *
        (∑ n ∈ S, eulerMuQ n / (n : ℚ)) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          ring

/-- The original rational floor form is literally the #1034 complex source. -/
theorem eulerFloorBilinearQ_cast_eq_original (R : ℕ) :
    ((eulerFloorBilinearQ R : ℚ) : ℂ) = eulerSelfDualBilinear R := by
  unfold eulerFloorBilinearQ eulerSelfDualBilinear
  simp [eulerMuQ, eulerFloorQ, eulerSelfDualFloor, Rat.cast_sum, Rat.cast_mul]

#print axioms eulerFloorBilinearQ_eq_continuous_sub_fractional
#print axioms eulerContinuousBilinearQ_eq_reciprocal_square

end RHLean.Proof
