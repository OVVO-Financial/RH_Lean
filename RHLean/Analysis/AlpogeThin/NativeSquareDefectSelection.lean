import RHLean.Analysis.AlpogeThin.NativeDyadicHostWindows

/-! Summation of the local defect on the same native square-clock host. The
factor `(x^ε + 1)` pays the exceptional-prime indicator and the retained
defect. The factor `u*(2+u)`, `u=x^(ε/3)`, is the upstream upper bound on
the sum of the weights `log(p)/p`. -/

namespace RHLean.Analysis.AlpogeThin

/-- The scalar total in the community defect selection at the actual top
cardinality and multiplicity. The threshold is uniform in `ε`, the selected
dyadic exponent, and the top set. The per-orbit estimate `Nv * x⁻¹²` and
its realization on the physical source are separate inputs to selection. -/
theorem squareClock_defectSelection_total (R e : ℕ) (hR : 2 ≤ R)
    (ε : ℝ) (hε : 0 < ε) (hε52 : ε < 1 / 52) (TT : Finset (AlpogeNativeDyadicH e))
    (hPage : UpperTheory.Top.PageN ε ((R ^ 2 - 1 : ℕ) : ℝ) e)
    (hscale : (96 : ℝ) ^ (4 : ℕ) ≤ ((R ^ 2 - 1 : ℕ) : ℝ)) :
    let x : ℝ := (R ^ 2 - 1 : ℕ)
    (x ^ ε + 1) * (R : ℝ) * (TT.card : ℝ) * x ^ (-12 : ℝ) *
        (x ^ (ε / 3) * (2 + x ^ (ε / 3))) ≤ x ^ (-9 : ℝ) / 4 := by
  let x : ℝ := (R ^ 2 - 1 : ℕ)
  change (x ^ ε + 1) * (R : ℝ) * (TT.card : ℝ) * x ^ (-12 : ℝ) *
      (x ^ (ε / 3) * (2 + x ^ (ε / 3))) ≤ x ^ (-9 : ℝ) / 4
  change UpperTheory.Top.PageN ε x e at hPage
  change (96 : ℝ) ^ (4 : ℕ) ≤ x at hscale
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 96 ^ (4 : ℕ)).trans hscale
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hxdef : x = (R : ℝ) ^ 2 - 1 := by
    dsimp [x]
    rw [Nat.cast_sub (by nlinarith : 1 ≤ R ^ 2), Nat.cast_pow, Nat.cast_one]
  have hr : (R : ℝ) ≤ 2 * x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    apply (sq_le_sq₀ (Nat.cast_nonneg R) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hx0.le]
    nlinarith only [hxdef, hx1]
  have hcard : (Fintype.card (AlpogeNativeDyadicH e) : ℝ) ≤ 2 * x ^ (2 + 8 * ε) := by
    rw [alpogeNativeDyadicH_card, Nat.cast_pow, Nat.cast_ofNat]
    exact hPage.2
  have hT : (TT.card : ℝ) ≤ 2 * x ^ (2 + 8 * ε) :=
    (Nat.cast_le.mpr (Finset.card_le_univ TT)).trans hcard
  have he : x ^ ε + 1 ≤ 2 * x ^ ε := by linarith only [Real.one_le_rpow hx1 hε.le]
  have hu : 2 + x ^ (ε / 3) ≤ 3 * x ^ (ε / 3) := by
    linarith only [Real.one_le_rpow hx1 (show 0 ≤ ε / 3 by linarith)]
  have hthreshold : (96 : ℝ) ≤ x ^ ((1 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 96 ^ (4 : ℕ)) hscale
      (by norm_num : 0 ≤ (1 : ℝ) / 4)
    rwa [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 96),
      show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one] at h
  calc
    _ ≤ (2 * x ^ ε) * (2 * x ^ ((1 : ℝ) / 2)) * (2 * x ^ (2 + 8 * ε)) *
          x ^ (-12 : ℝ) * (x ^ (ε / 3) * (3 * x ^ (ε / 3))) := by
      have h1 := mul_le_mul he hr (Nat.cast_nonneg (α := ℝ) R)
        (show 0 ≤ 2 * x ^ ε by positivity)
      have h2 := mul_le_mul h1 hT (Nat.cast_nonneg (α := ℝ) TT.card)
        (show 0 ≤ (2 * x ^ ε) * (2 * x ^ ((1 : ℝ) / 2)) by positivity)
      have h3 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hx0.le (-12 : ℝ))
      have h4 := mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hx0.le (ε / 3))
      exact mul_le_mul h3 h4 (by positivity) (by positivity)
    _ = 24 * x ^ (ε + (1 : ℝ) / 2 + (2 + 8 * ε) + (-12) + ε / 3 + ε / 3) := by
      simp only [Real.rpow_add hx0]
      ring
    _ ≤ 24 * x ^ (-(37 : ℝ) / 4) := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
        (by norm_num)
    _ ≤ x ^ ((1 : ℝ) / 4) * x ^ (-(37 : ℝ) / 4) / 4 := by
      linarith only [mul_le_mul_of_nonneg_right hthreshold (Real.rpow_nonneg hx0.le (-(37 : ℝ) / 4))]
    _ = x ^ (-9 : ℝ) / 4 := by
      rw [← Real.rpow_add hx0, show (1 : ℝ) / 4 + -(37 : ℝ) / 4 = -9 by norm_num]

end RHLean.Analysis.AlpogeThin
