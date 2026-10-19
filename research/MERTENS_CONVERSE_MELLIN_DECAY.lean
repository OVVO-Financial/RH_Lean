import Mathlib
import PrimeNumberTheoremAnd.MellinCalculus

/-!
# Mellin decay with a fractional smoothing loss

The elementary and integration-by-parts bounds are interpolated pointwise.
This avoids paying a full inverse smoothing parameter in the final Perron
estimate. The interpolation exponent can be any number between zero and one.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set MeasureTheory
open scoped Topology

/-- Compact support away from zero gives a height-uniform Mellin bound when
the real coordinate stays in [0,2]. No sign assumption on the function is used. -/
theorem mellin_compactSupport_bounded_positive_strip {ν : ℝ → ℝ}
    (hν : Continuous ν) (hsupp : Function.support ν ⊆ Set.Icc (1 / 2) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x => (ν x : ℂ)) s‖ ≤ C := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Set.Icc ((1 : ℝ) / 2) 2)).exists_bound_of_continuousOn
    hν.continuousOn
  let M : ℝ := |B| + 1
  have hM : 0 < M := by dsimp [M]; have := abs_nonneg B; linarith
  have hνB : ∀ x ∈ Set.Icc ((1 : ℝ) / 2) 2, ‖ν x‖ ≤ M := by
    intro x hx
    exact (hB x hx).trans (by dsimp [M]; have := le_abs_self B; linarith)
  refine ⟨12 * M, by positivity, ?_⟩
  intro s hs0 hs2
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * (ν x : ℂ)
  have hgsupp : Function.support g ⊆ Set.Icc ((1 : ℝ) / 2) 2 := by
    intro x hx
    have hne : ν x ≠ 0 := by
      intro hzero
      exact hx (by simp [g, hzero])
    exact hsupp hne
  have hgbound : ∀ x ∈ Set.Icc ((1 : ℝ) / 2) 2, ‖g x‖ ≤ 8 * M := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hxpow : x ^ s.re ≤ 4 := by
      calc
        x ^ s.re ≤ (2 : ℝ) ^ s.re := Real.rpow_le_rpow hxpos.le hx.2 hs0
        _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs2
        _ = 4 := by norm_num
    have hpow : x ^ (s.re - 1) ≤ 8 := by
      rw [Real.rpow_sub hxpos, Real.rpow_one]
      apply (div_le_iff₀ hxpos).mpr
      linarith [hx.1]
    dsimp [g]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
      Complex.sub_re, Complex.one_re, Complex.norm_real]
    exact mul_le_mul hpow (hνB x hx) (norm_nonneg _) (by norm_num)
  have heq : mellin (fun x => (ν x : ℂ)) s =
      ∫ x in Set.Icc ((1 : ℝ) / 2) 2, g x := by
    unfold mellin
    simp only [smul_eq_mul]
    exact SetIntegral.integral_eq_integral_inter_of_support_subset_Icc hgsupp
      (fun x hx => by
        change 0 < x
        linarith [hx.1])
  rw [heq, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) / 2 ≤ 2)]
  calc
    ‖∫ x in (1 : ℝ) / 2..2, g x‖ ≤ (8 * M) * |(2 : ℝ) - 1 / 2| :=
      intervalIntegral.norm_integral_le_of_norm_le_const' (by norm_num) hgbound
    _ = 12 * M := by
      rw [show |(2 : ℝ) - 1 / 2| = 3 / 2 by norm_num]
      ring

/-- The first Mellin bound is independent of the smoothing parameter. -/
theorem smoothingMellin_simple_decay {ν : ℝ → ℝ}
    (hdiff : ContDiff ℝ 1 ν) (hsupp : Function.support ν ⊆ Set.Icc (1 / 2) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ 2 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) s‖ ≤ C * ‖s‖⁻¹ := by
  obtain ⟨C, hC, hbound⟩ := mellin_compactSupport_bounded_positive_strip hdiff.continuous hsupp
  refine ⟨C, hC, ?_⟩
  intro s hs0 hs2 ε hε hε1
  have heps0 : 0 ≤ ((ε : ℂ) * s).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    positivity
  have heps2 : ((ε : ℂ) * s).re ≤ 2 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith
  rw [MellinOfSmooth1a hdiff hsupp hε hs0, norm_mul, norm_inv]
  calc
    ‖s‖⁻¹ * ‖mellin (fun x => (ν x : ℂ)) ((ε : ℂ) * s)‖ ≤ ‖s‖⁻¹ * C :=
      mul_le_mul_of_nonneg_left (hbound _ heps0 heps2) (by positivity)
    _ = C * ‖s‖⁻¹ := mul_comm _ _

/-- Pointwise interpolation of the simple and quadratic reciprocal bounds.
The common constant is preserved, and only a fractional power of epsilon
is lost. This is proved by splitting at epsilon*n = 1. -/
theorem interpolate_simple_and_quadratic_decay {y C ε n q : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) (hn : 0 < n) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h0 : y ≤ C * n⁻¹) (h1 : y ≤ C * (ε * n ^ 2)⁻¹) :
    y ≤ C * ε ^ (-q) * n ^ (-1 - q) := by
  have hepn : 0 < ε * n := mul_pos hε hn
  have hcoef : 0 ≤ C * n⁻¹ := mul_nonneg hC (inv_nonneg.mpr hn.le)
  have hbound : y ≤ C * n⁻¹ * (ε * n) ^ (-q) := by
    by_cases hsmall : ε * n ≤ 1
    · have hpow : 1 ≤ (ε * n) ^ (-q) := by
        simpa only [Real.one_rpow] using!
          Real.rpow_le_rpow_of_nonpos hepn hsmall (neg_nonpos.mpr hq0)
      exact h0.trans (le_mul_of_one_le_right hcoef hpow)
    · have hlarge : 1 ≤ ε * n := (lt_of_not_ge hsmall).le
      have hpow : (ε * n)⁻¹ ≤ (ε * n) ^ (-q) := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hlarge (by linarith)
      have heq : C * (ε * n ^ 2)⁻¹ = C * n⁻¹ * (ε * n)⁻¹ := by
        simp only [mul_inv, pow_two]
        ring
      exact (h1.trans_eq heq).trans (mul_le_mul_of_nonneg_left hpow hcoef)
  have hfactor : C * n⁻¹ * (ε * n) ^ (-q) = C * ε ^ (-q) * n ^ (-1 - q) := by
    rw [Real.mul_rpow hε.le hn.le]
    have hp : n ^ (-1 : ℝ) * n ^ (-q) = n ^ (-1 - q) := by
      simpa only [sub_eq_add_neg] using! (Real.rpow_add hn (-1) (-q)).symm
    calc
      C * n⁻¹ * (ε ^ (-q) * n ^ (-q)) =
          C * ε ^ (-q) * (n ^ (-1 : ℝ) * n ^ (-q)) := by
            rw [Real.rpow_neg_one]
            ring
      _ = _ := by rw [hp]
  exact hbound.trans_eq hfactor

/-- Fractional smoothing decay, uniform in the full positive strip up to 2. -/
theorem smoothingMellin_fractional_decay {ν : ℝ → ℝ}
    (hdiff : ContDiff ℝ 1 ν) (hsupp : Function.support ν ⊆ Set.Icc (1 / 2) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      ∀ s : ℂ, 0 < s.re → s.re ≤ 2 → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) s‖ ≤
          C * ε ^ (-q) * ‖s‖ ^ (-1 - q) := by
  obtain ⟨C₀, hC₀, hsimple⟩ := smoothingMellin_simple_decay hdiff hsupp
  obtain ⟨C₁, hC₁, hquadratic⟩ := MellinOfSmooth1b hdiff hsupp
  let C : ℝ := max C₀ C₁
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro q hq0 hq1 s hs0 hs2 ε hε hε1
  have hn : 0 < ‖s‖ := norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hs0)
  apply interpolate_simple_and_quadratic_decay hC.le hε hn hq0 hq1
  · exact (hsimple s hs0 hs2 ε hε hε1).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact (hquadratic s.re hs0 s le_rfl hs2 ε hε hε1).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end RHLean.Analysis.MertensExponent
