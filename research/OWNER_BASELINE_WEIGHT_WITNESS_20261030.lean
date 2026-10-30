import Mathlib
import «research.OWNER_RECIPROCAL_EXPONENT_SLACK_20261030»
import «research.OWNER_COMPLETE_SIGNED_RETURN_20261030»

/-!
# Actual local obstruction at the imported 7/8 energy exponent

For amplitude (mn)^(-7/8), the child energy multiplier is p^(-7/4).
The original parent (1,7), W=35, has two children for each p=2,3,5.
Their reciprocal 7/4 congestion exceeds 1. This rules out extending the
unsigned local-congestion proof directly to the 7/8 weight, not a new
GLOBAL cross-parent/terminal cancellation theorem on the complete source.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Proof
open RHLean.Analysis RHLean.Arithmetic

private theorem ownerBaseline_three_multiplicities :
    postRootCovarianceFixedOwnerChildMultiplicity 35 (1, 7) 2 = 2 ∧
    postRootCovarianceFixedOwnerChildMultiplicity 35 (1, 7) 3 = 2 ∧
    postRootCovarianceFixedOwnerChildMultiplicity 35 (1, 7) 5 = 2 := by
  have h (p : ℕ) : postRootCovarianceFixedOwnerChildMultiplicity 35 (1, 7) p =
      (({(1, 14), (1, 21), (1, 35), (2, 7), (3, 7), (5, 7)} : Finset (ℕ × ℕ)).filter
        (fun mn => squarefreePairFreshPrimeOwner mn.1 mn.2 = p)).card := by
    unfold postRootCovarianceFixedOwnerChildMultiplicity
    rw [← postRootCovarianceFixedParentChildFiber_filter_owner_eq,
      ownerReturn_parent_one_seven_at_35]
  rw [h 2, h 3, h 5]
  rcases ownerReturn_owner_values with ⟨_h7,h14,h21,h35,h2,h3,h5⟩
  norm_num [Finset.filter_insert,Finset.filter_singleton,h14,h21,h35,h2,h3,h5]

private theorem inverseSevenFourths_fourth_power
    (x : ℝ) (hx : 0 < x) :
    (x ^ (-(7 / 4 : ℝ))) ^ 4 * x ^ 7 = 1 := by
  have he : (x ^ (-(7 / 4 : ℝ))) ^ 4 = x ^ (-(7 : ℝ)) := by
    calc
      (x ^ (-(7 / 4 : ℝ))) ^ 4 =
          (x ^ (-(7 / 4 : ℝ))) ^ (4 : ℝ) :=
            (Real.rpow_natCast (x ^ (-(7 / 4 : ℝ))) 4).symm
      _ = x ^ ((-(7 / 4 : ℝ)) * 4) := (Real.rpow_mul hx.le _ _).symm
      _ = x ^ (-(7 : ℝ)) := by norm_num
  have h7 : x ^ (7 : ℝ) = x ^ (7 : ℕ) := Real.rpow_natCast x 7
  rw [he, Real.rpow_neg hx.le, h7]
  exact inv_mul_cancel₀ (pow_ne_zero 7 (ne_of_gt hx))

private theorem inverseSevenFourths_gt_of_fourth_certificate
    (x r : ℝ) (hx : 0 < x)
    (hcert : r ^ 4 * x ^ 7 < 1) :
    r < x ^ (-(7 / 4 : ℝ)) := by
  by_contra! h
  have hpow : (x ^ (-(7 / 4 : ℝ))) ^ 4 ≤ r ^ 4 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hx.le _) h 4
  have hm := mul_le_mul_of_nonneg_right hpow (pow_nonneg hx.le 7)
  rw [inverseSevenFourths_fourth_power x hx] at hm
  linarith

/-- Three actual prime fibres obstruct a local contraction at s=7/4.
All numerical inequalities use rational fourth-power certificates. -/
theorem ownerBaseline_seven_fourths_congestion_gt_one :
    (1 : ℝ) < postRootOwnerPowerCongestion 35 (1, 7) (7 / 4) := by
  rcases ownerBaseline_three_multiplicities with ⟨hk2,hk3,hk5⟩
  have hl2 : (19 / 64 : ℝ) < (2 : ℝ) ^ (-(7 / 4 : ℝ)) :=
    inverseSevenFourths_gt_of_fourth_certificate 2 (19 / 64)
      (by norm_num) (by norm_num)
  have hl3 : (7 / 48 : ℝ) < (3 : ℝ) ^ (-(7 / 4 : ℝ)) :=
    inverseSevenFourths_gt_of_fourth_certificate 3 (7 / 48)
      (by norm_num) (by norm_num)
  have hl5 : (1 / 17 : ℝ) < (5 : ℝ) ^ (-(7 / 4 : ℝ)) :=
    inverseSevenFourths_gt_of_fourth_certificate 5 (1 / 17)
      (by norm_num) (by norm_num)
  have hsub : ({2,3,5} : Finset ℕ) ⊆ primesUpTo 35 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num [mem_primesUpTo]
  have hsum :
      (∑ p ∈ ({2,3,5} : Finset ℕ),
        (postRootCovarianceFixedOwnerChildMultiplicity 35 (1, 7) p : ℝ) *
          (p : ℝ) ^ (-(7 / 4 : ℝ))) ≤
        postRootOwnerPowerCongestion 35 (1, 7) (7 / 4) := by
    unfold postRootOwnerPowerCongestion
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro p _hp _hnot
      positivity)
  have heq :
      (∑ p ∈ ({2,3,5} : Finset ℕ),
        (postRootCovarianceFixedOwnerChildMultiplicity 35 (1, 7) p : ℝ) *
          (p : ℝ) ^ (-(7 / 4 : ℝ))) =
        2 * ((2 : ℝ) ^ (-(7 / 4 : ℝ)) +
          (3 : ℝ) ^ (-(7 / 4 : ℝ)) + (5 : ℝ) ^ (-(7 / 4 : ℝ))) := by
    norm_num [hk2,hk3,hk5]
    ring
  rw [heq] at hsum
  linarith

#print axioms ownerBaseline_seven_fourths_congestion_gt_one

end RHLean.Proof
