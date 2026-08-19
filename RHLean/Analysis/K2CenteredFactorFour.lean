import Mathlib
import RHLean.Analysis.K2CenteredFinite
import RHLean.Analysis.NativePNTSignedSecondSelbergDepthFourShell

/-!
# Factor-four corollary of centered reciprocal K2 convergence

This file is independent of how centered K2 convergence is obtained.  Once

`F(N) + 2 * gamma * log N -> L`,

the exact shell identity

`K2((N/4,N]) = F(N) - F(N/4)`

forces the limiting factor-four mass to be `-2 * gamma * log 4`; the unknown
centered constant cancels.  A global uniform bound is then obtained by combining
the eventual bound from convergence with the finite initial segment.
-/

noncomputable section

open Filter Finset Topology

namespace RHLean.Analysis

local notation "γE" => Real.eulerMascheroniConstant

/-- The centered reciprocal K2 prefix. -/
def k2CenteredRecipValue (N : ℕ) : ℝ :=
  nativePNTSignedSecondSelbergKernelRecipMass N +
    2 * γE * Real.log (N : ℝ)

/-- Centered convergence to a specified finite constant.  The analytic interface
packages existence of such a constant separately. -/
def K2CenteredConvergesTo (L : ℝ) : Prop :=
  Tendsto k2CenteredRecipValue atTop (𝓝 L)

/-- Division by the fixed positive integer four preserves escape to infinity. -/
theorem k2_tendsto_nat_div_four_atTop :
    Tendsto (fun N : ℕ => N / 4) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (4 * b)] with N hN
  omega

/-- The real quotient `N / floor(N/4)` tends to four. -/
theorem k2_tendsto_div_four_ratio :
    Tendsto
      (fun N : ℕ => (N : ℝ) / ((N / 4 : ℕ) : ℝ))
      atTop (𝓝 4) := by
  have hq :
      Tendsto (fun N : ℕ => ((N / 4 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp k2_tendsto_nat_div_four_atTop
  have hinv :
      Tendsto (fun N : ℕ => (((N / 4 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hq
  have hrem :
      Tendsto
        (fun N : ℕ => ((N % 4 : ℕ) : ℝ) * (((N / 4 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun N => mul_nonneg (by positivity) (by positivity)
    · filter_upwards [eventually_ge_atTop 4] with N hN
      have hmodNat : N % 4 ≤ 3 := by omega
      have hmod : ((N % 4 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hmodNat
      exact mul_le_mul_of_nonneg_right hmod (inv_nonneg.mpr (by positivity))
    · simpa using (tendsto_const_nhds.mul hinv :
        Tendsto (fun N : ℕ => (3 : ℝ) * (((N / 4 : ℕ) : ℝ))⁻¹)
          atTop (𝓝 ((3 : ℝ) * 0)))
  have heq :
      (fun N : ℕ => (N : ℝ) / ((N / 4 : ℕ) : ℝ)) =ᶠ[atTop]
        (fun N : ℕ => 4 +
          ((N % 4 : ℕ) : ℝ) * (((N / 4 : ℕ) : ℝ))⁻¹) := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    have hqpos : 0 < N / 4 := by omega
    have hq0 : (((N / 4 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hnat : N = 4 * (N / 4) + N % 4 := by omega
    rw [hnat]
    push_cast
    field_simp [hq0]
    ring
  apply heq.tendsto_iff.mpr
  simpa using (tendsto_const_nhds.add hrem :
    Tendsto
      (fun N : ℕ => (4 : ℝ) +
        ((N % 4 : ℕ) : ℝ) * (((N / 4 : ℕ) : ℝ))⁻¹)
      atTop (𝓝 ((4 : ℝ) + 0)))

/-- The logarithmic scale difference between `N` and `floor(N/4)` tends to
`log 4`. -/
theorem k2_tendsto_log_sub_log_div_four :
    Tendsto
      (fun N : ℕ =>
        Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ))
      atTop (𝓝 (Real.log 4)) := by
  have hlog :
      Tendsto
        (fun N : ℕ =>
          Real.log ((N : ℝ) / ((N / 4 : ℕ) : ℝ)))
        atTop (𝓝 (Real.log 4)) :=
    k2_tendsto_div_four_ratio.log (by norm_num)
  have heq :
      (fun N : ℕ =>
        Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ)) =ᶠ[atTop]
      (fun N : ℕ =>
        Real.log ((N : ℝ) / ((N / 4 : ℕ) : ℝ))) := by
    filter_upwards [eventually_ge_atTop 4] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    have hq0 : (((N / 4 : ℕ) : ℝ)) ≠ 0 := by
      have : 0 < N / 4 := by omega
      positivity
    rw [Real.log_div hN0 hq0]
  exact heq.tendsto_iff.mpr hlog

/-- Exact algebraic expression of the factor-four shell through centered
prefixes. -/
theorem nativePNTSignedK2RecipInterval_four_eq_centered
    (N : ℕ) :
    nativePNTSignedK2RecipInterval N 4 =
      (k2CenteredRecipValue N - k2CenteredRecipValue (N / 4)) -
        2 * γE *
          (Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ)) := by
  rw [nativePNTSignedK2RecipInterval_four_eq_prefix_sub]
  unfold k2CenteredRecipValue
  ring

/-- Any centered K2 prefix limit yields the exact factor-four shell limit.  The
unknown centered constant cancels from the difference. -/
theorem nativePNTSignedK2RecipInterval_four_tendsto_of_tendsto
    (L : ℝ) (h : K2CenteredConvergesTo L) :
    Tendsto
      (fun N : ℕ => nativePNTSignedK2RecipInterval N 4)
      atTop
      (𝓝 (-2 * γE * Real.log 4)) := by
  have hL4 :
      Tendsto (fun N : ℕ => k2CenteredRecipValue (N / 4)) atTop (𝓝 L) :=
    h.comp k2_tendsto_nat_div_four_atTop
  have hdiff :
      Tendsto
        (fun N : ℕ =>
          k2CenteredRecipValue N - k2CenteredRecipValue (N / 4))
        atTop (𝓝 0) := by
    simpa using h.sub hL4
  have hlog :
      Tendsto
        (fun N : ℕ =>
          2 * γE *
            (Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ)))
        atTop (𝓝 (2 * γE * Real.log 4)) := by
    simpa using
      (tendsto_const_nhds.mul k2_tendsto_log_sub_log_div_four :
        Tendsto
          (fun N : ℕ =>
            (2 * γE) *
              (Real.log (N : ℝ) - Real.log ((N / 4 : ℕ) : ℝ)))
          atTop (𝓝 ((2 * γE) * Real.log 4)))
  have hsub := hdiff.sub hlog
  simpa [nativePNTSignedK2RecipInterval_four_eq_centered] using hsub

/-- The factor-four reciprocal shell is uniformly bounded once centered K2
convergence is available.  This is a global bound, including the finite initial
segment, not merely an eventual `O(1)` statement. -/
theorem nativePNTSignedK2RecipInterval_four_uniform_bound_of_tendsto
    (Lcenter : ℝ) (hcenter : K2CenteredConvergesTo Lcenter) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, |nativePNTSignedK2RecipInterval N 4| ≤ C := by
  have hconv :
      Tendsto
        (fun N : ℕ => nativePNTSignedK2RecipInterval N 4)
        atTop (𝓝 (-2 * γE * Real.log 4)) :=
    nativePNTSignedK2RecipInterval_four_tendsto_of_tendsto Lcenter hcenter
  let L : ℝ := -2 * γE * Real.log 4
  have hnear :
      ∀ᶠ N : ℕ in atTop,
        nativePNTSignedK2RecipInterval N 4 ∈ Metric.ball L 1 := by
    exact hconv.eventually (Metric.ball_mem_nhds L (by norm_num))
  have hlarge :
      ∀ᶠ N : ℕ in atTop,
        |nativePNTSignedK2RecipInterval N 4| ≤ |L| + 1 := by
    filter_upwards [hnear] with N hN
    have hd : |nativePNTSignedK2RecipInterval N 4 - L| < 1 := by
      simpa [Real.dist_eq] using hN
    calc
      |nativePNTSignedK2RecipInterval N 4| =
          |(nativePNTSignedK2RecipInterval N 4 - L) + L| := by ring_nf
      _ ≤ |nativePNTSignedK2RecipInterval N 4 - L| + |L| := abs_add _ _
      _ ≤ |L| + 1 := by linarith
  rcases eventually_atTop.1 hlarge with ⟨M, hM⟩
  let S : ℝ :=
    ∑ n ∈ Finset.range M, |nativePNTSignedK2RecipInterval n 4|
  refine ⟨|L| + 1 + S, ?_, ?_⟩
  · have hS : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  · intro N
    by_cases hMN : M ≤ N
    · have htail := hM N hMN
      have hS : 0 ≤ S := by
        dsimp [S]
        exact Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    · have hNM : N < M := Nat.lt_of_not_ge hMN
      have hsingle :
          |nativePNTSignedK2RecipInterval N 4| ≤ S := by
        dsimp [S]
        exact Finset.single_le_sum
          (fun n _ => abs_nonneg (nativePNTSignedK2RecipInterval n 4))
          (Finset.mem_range.2 hNM)
      have hbase : 0 ≤ |L| + 1 := by positivity
      linarith

end RHLean.Analysis
