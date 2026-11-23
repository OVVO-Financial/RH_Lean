import RHLean.Analysis.AlpogeLandau.LandauZeroFreeCriterion

/-!
# Reconstructed analytic window dependency

Mathematical source: Levent Alpöge (with Claude), src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauKernelMax.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauKernelMax.lean

This local proof reconstruction changes the module/namespace boundary and is
checked against RH_Lean's Lean/Mathlib versions. It imports no upstream compiled
artifact or terminal RH theorem. The source archive/mirror states no license;
this provenance notice does not assign a new license to that source material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000


open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHLean.Analysis.AlpogeLandau

theorem landau_kernel_max (k : ℕ) {a u : ℝ} (ha : 0 < a) (hu : 0 ≤ u) :
    u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) ≤ 1 / a ^ k := by
  have h := Real.pow_div_factorial_le_exp (a * u) (mul_nonneg ha.le hu) k
  have hak : 0 < a ^ k := pow_pos ha k
  rw [le_div_iff₀ hak]
  calc u ^ k * Real.exp (-a * u) / (k.factorial : ℝ) * a ^ k
      = (a * u) ^ k / (k.factorial : ℝ) * Real.exp (-(a * u)) := by
        rw [mul_pow, neg_mul]; ring
    _ ≤ Real.exp (a * u) * Real.exp (-(a * u)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

end RHLean.Analysis.AlpogeLandau

end

