import RHLean.Analysis.K2RecipMomentRateScratch

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace RHLean.Analysis

/-- The positive logarithmic Abel weight appearing in the classical K2
closure. -/
def k2LogCenteredWeightSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 N,
    k2r n *
      (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))

/-- The logarithmic weighted sum is exactly the endpoint term minus the cubic
reciprocal moment. -/
theorem k2LogCenteredWeightSum_eq (N : ℕ) (hN : 1 ≤ N) :
    k2LogCenteredWeightSum N =
      k2r N * Real.log (N : ℝ) - k2C3 N := by
  have hC := k2C3_centered_abel N hN
  unfold k2LogCenteredWeightSum
  calc
    (∑ n ∈ Finset.Ico 1 N,
        k2r n *
          (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))) =
        ∑ n ∈ Finset.Ico 1 N,
          -(k2r n *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = -(∑ n ∈ Finset.Ico 1 N,
          k2r n *
            (Real.log (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ))) := by
      rw [Finset.sum_neg_distrib]
    _ = k2r N * Real.log (N : ℝ) - k2C3 N := by
      rw [hC]
      ring

/-- The logarithmic K2 comparison sum converges under precisely the three
moment hypotheses recorded by `K2ClassicalMomentInput`. -/
theorem k2LogCenteredWeightSum_tendsto (h : K2ClassicalMomentInput) :
    ∃ ell : ℝ, Tendsto k2LogCenteredWeightSum atTop (𝓝 ell) := by
  rcases h.c3_tendsto with ⟨ell, hell⟩
  refine ⟨-ell, ?_⟩
  have hlim := h.r_mul_log_tendsto_zero.sub hell
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (k2LogCenteredWeightSum_eq N hN).symm

end RHLean.Analysis
