import Mathlib

/-!
# Quantitative payment for the constructed descent maps

The map count, the collective square norm, the generator height and the rank
defect remain separate. These arithmetic lemmas reconstruct the actual budget
calculations in `MapsBoundOfDeepGood`, `HtMapLeOfPoints`, and
`LowerBoundOfAllEstimates`, by Levent Alpoge (with Claude), at source pin
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

They pay the cubic map-count factor; they do not replace it by a square or
construct the cusp family. The geometric inputs to the slope comparison are
explicit, so this file does not assert an unconditional arithmetic source bound.
-/

set_option autoImplicit false

noncomputable section

namespace RHLean.Geometry

/-- The actual `q^3 B^2` collective map bill, with `B = exp(C z^9)`, is
absorbed by `exp(2b)` in the original size regime. No map-count factor is
discarded. The natural map count can be cast to the real variable `q`. -/
theorem nativeDescent_collectiveNormBudget {q C z b : ℝ}
    (hq : 0 < q) (hC : 0 ≤ C) (hqz : Real.log q ≤ 45 * z ^ 2)
    (hz : 2 * C + 200 ≤ z) (hb : z ^ 12 ≤ b) :
    q ^ 3 * Real.exp (C * z ^ 9) ^ 2 ≤ Real.exp (2 * b) := by
  have hz1 : 1 ≤ z := by linarith
  have hq3 : q ^ 3 ≤ Real.exp (135 * z ^ 2) := by
    rw [← Real.exp_log (pow_pos hq 3), Real.log_pow]
    exact Real.exp_le_exp.mpr (by norm_num; linarith)
  have he : Real.exp (C * z ^ 9) ^ 2 = Real.exp (2 * C * z ^ 9) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  calc
    q ^ 3 * Real.exp (2 * C * z ^ 9) ≤
        Real.exp (135 * z ^ 2) * Real.exp (2 * C * z ^ 9) :=
      mul_le_mul_of_nonneg_right hq3 (Real.exp_pos _).le
    _ = Real.exp (135 * z ^ 2 + 2 * C * z ^ 9) := by rw [← Real.exp_add]
    _ ≤ Real.exp (2 * b) := by
      apply Real.exp_le_exp.mpr
      have h29 : z ^ 2 ≤ z ^ 9 := pow_le_pow_right₀ hz1 (by norm_num)
      have h1012 : z ^ 10 ≤ z ^ 12 := pow_le_pow_right₀ hz1 (by norm_num)
      have hz9 : 0 ≤ z ^ 9 := pow_nonneg (by linarith) _
      have hcost : (135 + 2 * C) * z ^ 9 ≤ z * z ^ 9 :=
        mul_le_mul_of_nonneg_right (by linarith) hz9
      have hid : z * z ^ 9 = z ^ 10 := by ring
      nlinarith

/-- Attach the paid collective factor to the same source norm square. -/
theorem nativeDescent_jointEnergy_le {q C z b E J : ℝ}
    (hq : 0 < q) (hC : 0 ≤ C) (hqz : Real.log q ≤ 45 * z ^ 2)
    (hz : 2 * C + 200 ≤ z) (hb : z ^ 12 ≤ b) (hE : 0 ≤ E)
    (hJ : J ≤ q ^ 3 * Real.exp (C * z ^ 9) ^ 2 * E) :
    J ≤ Real.exp (2 * b) * E :=
  hJ.trans (mul_le_mul_of_nonneg_right
    (nativeDescent_collectiveNormBudget hq hC hqz hz hb) hE)

/-- Numeric consequence of the actual determinant/slope descent comparison.
`a` is the source rank, `N` is the rank of the joint target, and `height` is
the squared operator-height cost. The rank defect pays the generator height. -/
theorem nativeDescent_slopeBudget {a N μ μA height μmin P Λ δ t : ℝ}
    (ha : 0 < a) (haN : a ≤ N) (hN : N ≤ (1 + δ) * a)
    (hΛ : 0 ≤ Λ) (_hδ : 0 ≤ δ) (hheight : height ≤ 2 * P)
    (hmin : -(2 * Λ) ≤ μmin) (ht : t ≤ μA - 2 * P)
    (hdescent : a * (μA - height) + (N - a) * μmin ≤ N * μ) :
    t - δ * (|t| + 2 * Λ) ≤ μ := by
  have hN0 : 0 < N := ha.trans_le haN
  have h1 : a * t ≤ a * (μA - height) :=
    mul_le_mul_of_nonneg_left (by linarith) ha.le
  have h2 : (N - a) * (-(2 * Λ)) ≤ (N - a) * μmin :=
    mul_le_mul_of_nonneg_left hmin (by linarith)
  have h3 : (N - a) * t ≤ (N - a) * |t| :=
    mul_le_mul_of_nonneg_left (le_abs_self t) (by linarith)
  have h4 : N - a ≤ δ * N := by nlinarith
  have h5 : (N - a) * (|t| + 2 * Λ) ≤ δ * N * (|t| + 2 * Λ) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  refine le_of_mul_le_mul_left ?_ hN0
  nlinarith

/-- In the application `K = PP * kappa` is positive. The choice `delta=b/K`
pays the full twice-generator-height term exactly, without a limiting argument. -/
theorem nativeDescent_rankDefectCost (b K : ℝ) (hK : K ≠ 0) :
    b / K * (2 * K) = 2 * b := by
  rw [mul_comm 2 K, ← mul_assoc, div_mul_cancel₀ b hK]
  ring

/-- The lower-slope comparison with its original main term. This combines
the source slope, generator/rank payment and the final ring transfer cost. -/
theorem nativeDescent_mainTermPayment {M E b K C μB μ0 : ℝ}
    (hb : 0 ≤ b) (hbE : b ≤ E) (hbK : b ≤ K) (hMK : |M| ≤ K)
    (hC : 0 ≤ C)
    (hdescent : (-M - C * E - 2 * b) -
      b / K * (|-M - C * E - 2 * b| + 2 * K) ≤ μB)
    (hreturn : μB - 2 * b ≤ μ0) :
    -M - (2 * C + 9) * E ≤ μ0 := by
  have hK : 0 < K ∨ b = 0 := by
    rcases eq_or_lt_of_le hb with h0 | h0
    · exact Or.inr h0.symm
    · exact Or.inl (h0.trans_le hbK)
  have hE : 0 ≤ E := hb.trans hbE
  have hCE : 0 ≤ C * E := mul_nonneg hC hE
  have ht : |-M - C * E - 2 * b| ≤ |M| + C * E + 2 * b := by
    have h1 := abs_sub (-M - C * E) (2 * b)
    have h2 := abs_sub (-M) (C * E)
    rw [abs_neg, abs_of_nonneg hCE] at h2
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * b)] at h1
    linarith
  rcases hK with hK | hb0
  · let δ := b / K
    have hδ0 : 0 ≤ δ := div_nonneg hb hK.le
    have hδ1 : δ ≤ 1 := (div_le_one hK).mpr hbK
    have hδK : δ * K = b := div_mul_cancel₀ b hK.ne'
    have h1 : δ * |-M - C * E - 2 * b| ≤
        δ * |M| + δ * (C * E + 2 * b) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith) hδ0
    have h2 : δ * |M| ≤ b := by
      calc
        δ * |M| ≤ δ * K := mul_le_mul_of_nonneg_left hMK hδ0
        _ = b := hδK
    have h3 : δ * (C * E + 2 * b) ≤ C * E + 2 * b := by
      have hn : 0 ≤ C * E + 2 * b := by linarith
      nlinarith
    have h4 : δ * (|-M - C * E - 2 * b| + 2 * K) =
        δ * |-M - C * E - 2 * b| + 2 * b := by
      rw [mul_add, ← hδK]
      ring
    change (-M - C * E - 2 * b) -
      δ * (|-M - C * E - 2 * b| + 2 * K) ≤ μB at hdescent
    rw [h4] at hdescent
    nlinarith
  · subst b
    simp only [zero_div, zero_mul, sub_zero, mul_zero] at hdescent hreturn
    nlinarith

end RHLean.Geometry
