import «research.MERTENS_CONVERSE_RECIPROCAL»

/-!
# Unconditional growth inputs for the Mertens converse

The bounds in this file are elementary analytic bounds, not the desired
Mertens estimate. We use the classical absolutely convergent zeta series on
the right and the already proved Euler-summation integral on Re(s)>0.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set MeasureTheory
open scoped Topology LSeries.notation
local notation "I" => Complex.I

/-- Zeta is uniformly bounded on any closed half-plane strictly right of one. -/
theorem zeta_bounded_right_halfPlane {u : ℝ} (hu : 1 < u) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℂ, u ≤ s.re → ‖riemannZeta s‖ ≤ C := by
  have hU : LSeriesSummable (1 : ℕ → ℂ) (u : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun _n _hn => by simp) (by simpa using! hu)
  let C : ℝ := (∑' n, ‖LSeries.term (1 : ℕ → ℂ) (u : ℂ) n‖) + 1
  have hC : 1 ≤ C := by
    have hnonneg : 0 ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (u : ℂ) n‖ :=
      tsum_nonneg (fun _ => norm_nonneg _)
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro s hs
  have hs1 : 1 < s.re := hu.trans_le hs
  have hS : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun _n _hn => by simp) hs1
  rw [← LSeries_one_eq_riemannZeta hs1]
  calc
    ‖LSeries (1 : ℕ → ℂ) s‖ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
      norm_tsum_le_tsum_norm hS.norm
    _ ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (u : ℂ) n‖ :=
      Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simpa using! hs) n)
        hS.norm hU.norm
    _ ≤ C := by dsimp [C]; linarith

/-- A coarse polynomial zeta bound on every closed positive-real strip.
It is intentionally much weaker than standard convexity estimates. -/
theorem zeta_norm_le_positive_strip {b : ℝ} (hb : 0 < b) {s : ℂ}
    (hbs : b ≤ s.re) (hs4 : s.re ≤ 4) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ (4 + 4 / b) * (1 + |s.im|) := by
  have hspos : 0 < s.re := hb.trans_le hbs
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hspos
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at ht
  let J : ℂ := ∫ x in Set.Ioi (1 : ℝ),
    (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
  have hJ : ‖J‖ ≤ 1 / s.re := by
    have h := ZetaBnd_aux1b 1 (by norm_num) (σ := s.re) (t := s.im) hspos
    simpa only [Nat.cast_one, Real.one_rpow, Complex.re_add_im] using! h
  have hrepr : riemannZeta s =
      (1 : ℂ) + (-1) / (1 - s) + (-1) / 2 + s * J := by
    rw [← Zeta0EqZeta (N := 1) (by norm_num) hspos hs1]
    simp [riemannZeta0, Finset.sum_range_succ, hs0, J]
  have hden1 : 1 ≤ ‖(1 : ℂ) - s‖ := by
    have h := Complex.abs_im_le_norm ((1 : ℂ) - s)
    simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
    linarith
  have hden : ‖(-1 : ℂ) / (1 - s)‖ ≤ 1 := by
    rw [norm_div]
    norm_num only [norm_neg, norm_one]
    exact (div_le_iff₀ (by linarith : 0 < ‖(1 : ℂ) - s‖)).mpr (by simpa using! hden1)
  have hhalf : ‖(-1 : ℂ) / 2‖ ≤ 1 := by norm_num
  have hnorm : ‖s‖ ≤ 4 + |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hspos] at h
    linarith
  have hinv : 1 / s.re ≤ 1 / b := one_div_le_one_div_of_le hb hbs
  have hJb : ‖J‖ ≤ b⁻¹ := by simpa only [one_div] using! hJ.trans hinv
  have hprod : ‖s * J‖ ≤ (4 + |s.im|) / b := by
    rw [norm_mul, div_eq_mul_inv]
    exact mul_le_mul hnorm hJb (norm_nonneg J) (by positivity)
  have hrough : ‖riemannZeta s‖ ≤ 3 + (4 + |s.im|) / b := by
    rw [hrepr]
    have h1 := norm_add_le (1 : ℂ) ((-1 : ℂ) / (1 - s))
    have h2 := norm_add_le ((1 : ℂ) + (-1) / (1 - s)) ((-1 : ℂ) / 2)
    have h3 := norm_add_le ((1 : ℂ) + (-1) / (1 - s) + (-1) / 2) (s * J)
    norm_num only [norm_one] at h1
    linarith
  apply hrough.trans
  have hbInv : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have hterm : 0 ≤ |s.im| * b⁻¹ := mul_nonneg (abs_nonneg _) hbInv
  simp only [div_eq_mul_inv]
  nlinarith [abs_nonneg s.im]

/-- Affine disk coordinate centered at the absolutely convergent line Re=2. -/
def zetaDiscPoint (t : ℝ) (w : ℂ) : ℂ := 2 + (t : ℂ) * I + 4 * w

@[simp] theorem zetaDiscPoint_re (t : ℝ) (w : ℂ) :
    (zetaDiscPoint t w).re = 2 + 4 * w.re := by simp [zetaDiscPoint]

@[simp] theorem zetaDiscPoint_im (t : ℝ) (w : ℂ) :
    (zetaDiscPoint t w).im = t + 4 * w.im := by simp [zetaDiscPoint]

/-- The outer analytic disk stays away from the zeta pole at large height. -/
theorem zetaDiscPoint_ne_one {t : ℝ} (ht : 4 ≤ |t|) {w : ℂ}
    (hw : ‖w‖ ≤ 3 / 4) : zetaDiscPoint t w ≠ 1 := by
  intro heq
  have him := congrArg Complex.im heq
  simp only [zetaDiscPoint_im, Complex.one_im] at him
  have himBound := Complex.abs_im_le_norm w
  have htEq : t = -(4 * w.im) := by linarith
  rw [htEq, abs_neg, abs_mul] at ht
  norm_num at ht
  linarith

/-- The shifted-disk polynomial bound is uniform in its growing height. -/
theorem zeta_norm_le_on_shifted_disk {b : ℝ} (hb : 0 < b) {t : ℝ}
    (ht : 4 ≤ |t|) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2)
    (hbs : b ≤ (zetaDiscPoint t w).re) :
    ‖riemannZeta (zetaDiscPoint t w)‖ ≤ (8 + 8 / b) * |t| := by
  have hreBound := Complex.abs_re_le_norm w
  have himBound := Complex.abs_im_le_norm w
  have hre : (zetaDiscPoint t w).re ≤ 4 := by
    rw [zetaDiscPoint_re]
    have h := le_abs_self w.re
    linarith
  have hupper : |(zetaDiscPoint t w).im| ≤ |t| + 2 := by
    rw [zetaDiscPoint_im]
    have h := abs_add_le t (4 * w.im)
    rw [abs_mul] at h
    norm_num at h
    linarith
  have hlower : 2 ≤ |(zetaDiscPoint t w).im| := by
    have h := abs_sub_abs_le_abs_sub t (t + 4 * w.im)
    simp only [sub_add_cancel_left, abs_neg, abs_mul] at h
    norm_num at h
    rw [zetaDiscPoint_im]
    linarith
  have hZ := zeta_norm_le_positive_strip hb hbs hre hlower
  have hD : 0 ≤ 4 + 4 / b := by positivity
  calc
    ‖riemannZeta (zetaDiscPoint t w)‖ ≤
        (4 + 4 / b) * (1 + |(zetaDiscPoint t w).im|) := hZ
    _ ≤ (4 + 4 / b) * (2 * |t|) :=
      mul_le_mul_of_nonneg_left (by linarith) hD
    _ = (8 + 8 / b) * |t| := by ring

end RHLean.Analysis.MertensExponent
