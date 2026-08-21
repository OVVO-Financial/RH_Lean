import RHLean.Analysis.K2RecipMomentRateScratch

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace RHLean.Analysis

local notation "gammaE" => Real.eulerMascheroniConstant

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
  have hlim :
      Tendsto
        (fun N : ℕ => k2r N * Real.log (N : ℝ) - k2C3 N)
        atTop (𝓝 (-ell)) := by
    simpa using h.r_mul_log_tendsto_zero.sub hell
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (k2LogCenteredWeightSum_eq N hN).symm

/-- Euler's harmonic remainder after subtracting `log n + gamma`. -/
def k2HarmonicError (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log (n : ℝ) - gammaE

/-- The harmonic remainder is nonnegative. -/
theorem k2HarmonicError_nonneg (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ k2HarmonicError n := by
  have hn0 : n ≠ 0 := by omega
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp [Real.eulerMascheroniSeq', hn0] at h
  unfold k2HarmonicError
  linarith

/-- The harmonic remainder is bounded by one logarithmic mesh step. -/
theorem k2HarmonicError_le_log_step (n : ℕ) (hn : 1 ≤ n) :
    k2HarmonicError n ≤
      Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  simp [Real.eulerMascheroniSeq] at h
  unfold k2HarmonicError
  linarith

/-- The harmonic remainder has the elementary reciprocal bound `E_n ≤ 1/n`. -/
theorem k2HarmonicError_le_inv (n : ℕ) (hn : 1 ≤ n) :
    k2HarmonicError n ≤ 1 / (n : ℝ) := by
  have hnposNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
  have hnp1pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    k2HarmonicError n
        ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) :=
      k2HarmonicError_le_log_step n hn
    _ = Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hnp1pos.ne' hnpos.ne']
    _ ≤ (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hnp1pos hnpos)
    _ = 1 / (n : ℝ) := by
      field_simp [hnpos.ne']

end RHLean.Analysis
