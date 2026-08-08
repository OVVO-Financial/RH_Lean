import Mathlib
import RHLean.Analysis.MertensStepFunction

/-!
# Power growth of the Mertens step function

The pointwise `r > 1/2` Mertens bound is converted into the Landau form used by
Abel summation and Mellin transforms.  We first absorb the harmless `n + 1`
shift on the natural summatory function, then compose with the natural floor.
Near zero the step function vanishes identically.
-/

noncomputable section

namespace RHLean.Analysis

open Filter Asymptotics Set

/-- The Mertens summatory function is `O(n^r)` on the naturals for every
`r > 1/2`. -/
theorem mertensSummatory_isBigO_rpow
    (hM : MertensEnergyBoundedStatement) {r : ℝ}
    (hr : (1 : ℝ) / 2 < r) :
    (fun n : ℕ => mertensSummatory n) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
  rcases mertensPowerGrowth_of_energy hM hr with ⟨K, hK, hbound⟩
  have hr0 : 0 ≤ r := by linarith
  refine IsBigO.of_bound (K * Real.rpow (2 : ℝ) r) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hshift : (((n + 1 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hrpow :
      Real.rpow (((n + 1 : ℕ) : ℝ)) r ≤
        Real.rpow (2 * (n : ℝ)) r :=
    Real.rpow_le_rpow (by positivity) hshift hr0
  have hmul :
      K * Real.rpow (((n + 1 : ℕ) : ℝ)) r ≤
        K * Real.rpow (2 * (n : ℝ)) r :=
    mul_le_mul_of_nonneg_left hrpow hK
  have hfactor :
      Real.rpow (2 * (n : ℝ)) r =
        Real.rpow (2 : ℝ) r * Real.rpow (n : ℝ) r :=
    Real.mul_rpow (by positivity) (by positivity)
  calc
    ‖mertensSummatory n‖ ≤
        K * Real.rpow (((n + 1 : ℕ) : ℝ)) r := hbound n
    _ ≤ K * Real.rpow (2 * (n : ℝ)) r := hmul
    _ = (K * Real.rpow (2 : ℝ) r) * Real.rpow (n : ℝ) r := by
      rw [hfactor]
      ring
    _ = (K * Real.rpow (2 : ℝ) r) * ‖Real.rpow (n : ℝ) r‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) r)]

/-- The real floor-step Mertens function inherits the same power growth at
infinity. -/
theorem mertensStep_isBigO_rpow_atTop
    (hM : MertensEnergyBoundedStatement) {r : ℝ}
    (hr : (1 : ℝ) / 2 < r) :
    mertensStep =O[atTop] (fun t : ℝ => t ^ r) := by
  have hr0 : 0 ≤ r := by linarith
  have h :=
    (mertensSummatory_isBigO_rpow hM hr).comp_tendsto
      tendsto_nat_floor_atTop
  have h' := h.trans <|
    isEquivalent_nat_floor.isBigO.rpow hr0 (eventually_ge_atTop (0 : ℝ))
  simpa only [mertensStep_eq_mertensSummatory_floor] using h'

/-- Near zero the Mertens step function is zero, hence it is `O(t^a)` for every
real exponent `a`. -/
theorem mertensStep_isBigO_rpow_zero (a : ℝ) :
    mertensStep =O[𝓝[>] 0] (fun t : ℝ => t ^ a) := by
  refine IsBigO.of_bound 0 ?_
  have hIio : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds
  have hIio' : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds hIio
  filter_upwards [hIio'] with t ht
  rw [mertensStep_eq_zero_of_lt_one ht]
  simp

end RHLean.Analysis
