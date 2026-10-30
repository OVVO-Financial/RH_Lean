import Mathlib
import «research.COVARIANCE_RECIPROCAL_OWNER_CONGESTION»

/-!
# A genuine positive exponent margin in the original owner congestion

The physical fixed-owner multiplicities are the existing arithmetic fibres,
not replacement coefficients. Their 79/81 reciprocal-square bound has a
UNIFORM open interval of exponents below two. This is a local weighted
statement. It does not assert that sum of energies controls the square of a
signed sum, or that a positive exponent survives the complete unweighted return.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic

/-- Original owner multiplicities with a general reciprocal exponent. -/
def postRootOwnerPowerCongestion
    (W : ℕ) (parent : ℕ × ℕ) (s : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo W,
    (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) *
      (p : ℝ) ^ (-s)

/-- The exact original rational congestion theorem at exponent two. -/
theorem postRootOwnerPowerCongestion_two_le
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootOwnerPowerCongestion W parent 2 ≤ (79 / 81 : ℝ) := by
  have h := postRootCovarianceReciprocalOwnerCongestion_le_79_over_81 W parent
  unfold postRootCovarianceReciprocalOwnerCongestion at h
  have hr : (∑ p ∈ primesUpTo W,
      (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
        (p : ℝ) ^ 2) ≤ (79 / 81 : ℝ) := by
    exact_mod_cast h
  simpa [postRootOwnerPowerCongestion, Real.rpow_neg,
    Real.rpow_two, div_eq_mul_inv] using hr

private def ownerThreeHalvesMajorant : ℝ :=
  2 * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))

private theorem ownerThreeHalvesMajorant_nonneg :
    0 ≤ ownerThreeHalvesMajorant := by
  unfold ownerThreeHalvesMajorant
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun n =>
    Real.rpow_nonneg (Nat.cast_nonneg n) _))

private theorem ownerCongestion_three_halves_le
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootOwnerPowerCongestion W parent (3 / 2) ≤
      ownerThreeHalvesMajorant := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  unfold postRootOwnerPowerCongestion ownerThreeHalvesMajorant
  calc
    (∑ p ∈ primesUpTo W,
      (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) *
        (p : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      ∑ p ∈ primesUpTo W, 2 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro p _hp
        have hk : (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) ≤ 2 := by
          exact_mod_cast postRootCovarianceFixedOwnerChildMultiplicity_le_two W parent p
        exact mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ = 2 * ∑ p ∈ primesUpTo W, (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Summable.sum_le_tsum _ (fun n _ =>
        Real.rpow_nonneg (Nat.cast_nonneg n) _) hs

/-- Elementary weighted AM-GM preserves a strict reciprocal exponent window.
The new constant is independent of W and the actual parent. -/
theorem postRootOwnerPowerCongestion_interpolate
    (W : ℕ) (parent : ℕ × ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    postRootOwnerPowerCongestion W parent (2 - t / 2) ≤
      (1 - t) * postRootOwnerPowerCongestion W parent 2 +
        t * postRootOwnerPowerCongestion W parent (3 / 2) := by
  have hpwise (p : ℕ) (hp : p ∈ primesUpTo W) :
      (p : ℝ) ^ (-(2 - t / 2)) ≤
        (1 - t) * (p : ℝ) ^ (-(2 : ℝ)) +
          t * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (mem_primesUpTo.mp hp).1.pos
    have hg := Real.geom_mean_le_arith_mean2_weighted
      (w₁ := 1 - t) (w₂ := t)
      (p₁ := (p : ℝ) ^ (-(2 : ℝ)))
      (p₂ := (p : ℝ) ^ (-(3 / 2 : ℝ)))
      (by linarith) ht
      (Real.rpow_nonneg hp0.le _) (Real.rpow_nonneg hp0.le _)
      (by ring)
    calc
      (p : ℝ) ^ (-(2 - t / 2)) =
          ((p : ℝ) ^ (-(2 : ℝ))) ^ (1 - t) *
            ((p : ℝ) ^ (-(3 / 2 : ℝ))) ^ t := by
        rw [← Real.rpow_mul hp0.le, ← Real.rpow_mul hp0.le,
          ← Real.rpow_add hp0]
        congr 1
        ring
      _ ≤ _ := hg
  unfold postRootOwnerPowerCongestion
  calc
    (∑ p ∈ primesUpTo W,
      (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) *
        (p : ℝ) ^ (-(2 - t / 2))) ≤
      ∑ p ∈ primesUpTo W,
        (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) *
          ((1 - t) * (p : ℝ) ^ (-(2 : ℝ)) +
            t * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hpwise p hp) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro p _hp <;> ring

/-- There really IS some positive uniform reciprocal exponent slack.
This theorem is unconditional, but its conclusion is WEIGHTED CONGESTION,
not an improved Mertens exponent or a bound on the full signed return. -/
theorem exists_positive_owner_reciprocal_exponent_slack :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 2 ∧
      ∀ (W : ℕ) (parent : ℕ × ℕ),
        postRootOwnerPowerCongestion W parent (2 - τ) ≤ (53 / 54 : ℝ) := by
  let B := ownerThreeHalvesMajorant
  let t : ℝ := 1 / (162 * (B + 1))
  have hB : 0 ≤ B := ownerThreeHalvesMajorant_nonneg
  have hB1 : B + 1 ≠ 0 := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have htprod : t * (B + 1) = 1 / 162 := by
    dsimp [t]
    field_simp [hB1]
    ring
  have htB : 0 ≤ t * B := mul_nonneg ht.le hB
  have ht1 : t < 1 := by nlinarith
  refine ⟨t / 2, by positivity, by linarith, ?_⟩
  intro W parent
  have hi := postRootOwnerPowerCongestion_interpolate W parent t ht.le ht1.le
  have h2 := postRootOwnerPowerCongestion_two_le W parent
  have h3 : postRootOwnerPowerCongestion W parent (3 / 2) ≤ B :=
    ownerCongestion_three_halves_le W parent
  have hx := add_le_add
    (mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1 - t))
    (mul_le_mul_of_nonneg_left h3 ht.le)
  have htop : (1 - t) * (79 / 81 : ℝ) + t * B ≤ 53 / 54 := by
    nlinarith
  exact hi.trans (hx.trans htop)

#print axioms exists_positive_owner_reciprocal_exponent_slack

end RHLean.Proof
