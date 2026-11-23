import Mathlib
import RHLean.Analysis.AlpogeThin.NativeRayQuadraticForm
import RHLean.Analysis.AlpogeThin.NativeRayShiftedTheta

/-!
# Native ray-lattice quantitative supplier

This reconstructs the finite Gaussian/counting supplier for the literal
`NativeRay.qForm`, before transporting it to actual ray-class ideal norms.
All shifts and the shear remain arbitrary. No zeta estimate, finished RH
theorem, geometric target premise, or external compiled proof is imported.

Source: Levent Alpöge's proof archive, pinned source declaration in
`src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ThetaQForm.lean`.
The inspected mirror pin is 7cbf7a0c32fca1badf05931879a37c3f8a2b03b4.
The mirror states no license; attribution is retained without assigning one.
-/

open Complex MeasureTheory Filter Topology
open scoped Classical

namespace RHLean.Analysis.AlpogeThin.NativeRay.LatticeBounds

theorem tsum_prod_weight_approx {ι κ : Type} (u : ι → κ → ℝ) (w : κ → ℝ) (A a C c : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hu0 : ∀ m k, 0 ≤ u m k) (hw0 : ∀ k, 0 ≤ w k)
    (hu : ∀ k, Summable (fun m => u m k) ∧ |∑' m, u m k - A| ≤ A * a)
    (hw : Summable w ∧ |∑' k, w k - C| ≤ C * c) :
    Summable (fun v : ι × κ => u v.1 v.2 * w v.2) ∧
      |∑' v : ι × κ, u v.1 v.2 * w v.2 - A * C| ≤ A * C * (a + c + a * c) := by
  have hin : ∀ k, ∑' m, u m k * w k = (∑' m, u m k) * w k := fun k => tsum_mul_right
  have hb : ∀ k, ‖(∑' m, u m k - A) * w k‖ ≤ A * a * w k := fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 k)]
    exact mul_le_mul_of_nonneg_right (hu k).2 (hw0 k)
  have hs1 : Summable (fun k => (∑' m, u m k - A) * w k) :=
    Summable.of_norm_bounded (hw.1.mul_left (A * a)) hb
  have hs2 : Summable (fun k => (∑' m, u m k) * w k) := by
    refine (hs1.add (hw.1.mul_left A)).congr fun k => ?_
    ring
  have hsw : Summable (fun v : κ × ι => u v.2 v.1 * w v.1) := by
    rw [summable_prod_of_nonneg (fun v => mul_nonneg (hu0 _ _) (hw0 _))]
    refine ⟨fun k => ?_, ?_⟩
    · exact (hu k).1.mul_right (w k)
    · exact hs2.congr fun k => (hin k).symm
  have hs : Summable (fun v : ι × κ => u v.1 v.2 * w v.2) :=
    hsw.prod_symm
  refine ⟨hs, ?_⟩
  have h1 : ∑' v : ι × κ, u v.1 v.2 * w v.2 = ∑' k, (∑' m, u m k) * w k := by
    rw [← (Equiv.prodComm κ ι).tsum_eq]
    have := hsw.tsum_prod
    simp only [hin] at this
    exact this
  have h2 : ∑' k, (∑' m, u m k) * w k = ∑' k, (∑' m, u m k - A) * w k + A * ∑' k, w k := by
    rw [← tsum_mul_left, ← hs1.tsum_add (hw.1.mul_left A)]
    exact tsum_congr fun k => by ring
  have h3 : |∑' k, (∑' m, u m k - A) * w k| ≤ A * a * ∑' k, w k := by
    have := tsum_of_norm_bounded (hw.1.hasSum.mul_left (A * a)) hb
    simpa using this
  rw [h1, h2]
  have h4 := abs_le.mp hw.2
  have h5 := abs_le.mp h3
  have h6 : A * a * ∑' k, w k ≤ A * a * (C + C * c) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA ha)
  have h7 : A * (∑' k, w k - C) ≤ A * (C * c) := mul_le_mul_of_nonneg_left h4.2 hA
  have h8 : A * (-(C * c)) ≤ A * (∑' k, w k - C) := mul_le_mul_of_nonneg_left h4.1 hA
  rw [abs_le]
  constructor <;> nlinarith

theorem theta_qForm : ∀ α γ l θ₁ θ₂ t : ℝ, 0 < α → 0 < γ → 0 < t → Summable (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ∧ |∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) - Real.pi / Real.sqrt (α * γ) / t| ≤ Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2) := by
  intro α γ l θ₁ θ₂ t hα hγ ht
  have h := tsum_prod_weight_approx
    (fun (m : ℤ) (k : ℤ) => Real.exp (-((α * t) * (m + (θ₁ + l * k)) ^ 2)))
    (fun k : ℤ => Real.exp (-((γ * t) * (k + θ₂) ^ 2)))
    (Real.sqrt (Real.pi / (α * t))) ((α * t) ^ 2) (Real.sqrt (Real.pi / (γ * t))) ((γ * t) ^ 2)
    (Real.sqrt_nonneg _) (sq_nonneg _) (fun _ _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    (fun k => RHLean.Analysis.AlpogeThin.NativeRay.ShiftedTheta.shifted_theta_bound (α * t) (θ₁ + l * k) (mul_pos hα ht))
    (RHLean.Analysis.AlpogeThin.NativeRay.ShiftedTheta.shifted_theta_bound (γ * t) θ₂ (mul_pos hγ ht))
  have e1 : (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) =
      fun v : ℤ × ℤ => Real.exp (-((α * t) * (v.1 + (θ₁ + l * v.2)) ^ 2)) *
        Real.exp (-((γ * t) * (v.2 + θ₂) ^ 2)) := by
    funext v
    rw [← Real.exp_add]
    congr 1
    unfold qForm
    ring
  have e2 : Real.pi / Real.sqrt (α * γ) / t =
      Real.sqrt (Real.pi / (α * t)) * Real.sqrt (Real.pi / (γ * t)) := by
    have hp := Real.pi_pos
    rw [← Real.sqrt_mul (by positivity)]
    symm
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have hs : Real.sqrt (α * γ) * Real.sqrt (α * γ) = α * γ := Real.mul_self_sqrt (by positivity)
    have hs0 : 0 < Real.sqrt (α * γ) := Real.sqrt_pos.mpr (by positivity)
    rw [div_div, div_mul_div_comm, div_mul_div_comm]
    congr 1
    linear_combination -t ^ 2 * hs
  rw [e1, e2]
  exact h


/-- A quadratic theta error linear in time on the entire positive axis.
For t≤1 this retains the exact Poisson normalizer. For t≥1 monotonicity
of the same positive Gaussian controls its full mass by its value at one.
No pointwise prime/character estimate enters this analytic statement. -/
theorem theta_qForm_all_time
    (α γ l θ₁ θ₂ t : ℝ) (hα : 1 ≤ α) (hγ : 1 ≤ γ)
    (hP : 2 ≤ α * γ) (ht : 0 < t) :
    Summable (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ∧
    |∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) -
      Real.pi / Real.sqrt (α * γ) / t| ≤
        3 * (Real.pi / Real.sqrt (α * γ)) * (α * γ) ^ 2 * t := by
  have hα0 : 0 < α := by linarith
  have hγ0 : 0 < γ := by linarith
  have h := theta_qForm α γ l θ₁ θ₂ t hα0 hγ0 ht
  refine ⟨h.1, ?_⟩
  have hC0 : 0 ≤ Real.pi / Real.sqrt (α * γ) := by positivity
  have hP2 : 2 ≤ (α * γ) ^ 2 := by nlinarith
  rcases le_total t 1 with ht1 | h1t
  · have hA : α ≤ α * γ := by nlinarith
    have hG : γ ≤ α * γ := by nlinarith
    have hpoly : α ^ 2 + γ ^ 2 + α ^ 2 * γ ^ 2 * t ^ 2 ≤
        3 * (α * γ) ^ 2 := by
      have e1 : α ^ 2 ≤ (α * γ) ^ 2 := pow_le_pow_left₀ hα0.le hA 2
      have e2 : γ ^ 2 ≤ (α * γ) ^ 2 := pow_le_pow_left₀ hγ0.le hG 2
      have ht2 : t ^ 2 ≤ 1 := by nlinarith
      have e3 : α ^ 2 * γ ^ 2 * t ^ 2 ≤ (α * γ) ^ 2 := by
        calc α ^ 2 * γ ^ 2 * t ^ 2 = (α * γ) ^ 2 * t ^ 2 := by ring
          _ ≤ (α * γ) ^ 2 * 1 := mul_le_mul_of_nonneg_left ht2 (by positivity)
          _ = (α * γ) ^ 2 := by ring
      linarith
    refine h.2.trans ?_
    calc Real.pi / Real.sqrt (α * γ) / t *
        ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2)
        = Real.pi / Real.sqrt (α * γ) * t *
            (α ^ 2 + γ ^ 2 + α ^ 2 * γ ^ 2 * t ^ 2) := by
          field_simp <;> ring
      _ ≤ Real.pi / Real.sqrt (α * γ) * t * (3 * (α * γ) ^ 2) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  · have hs1 := theta_qForm α γ l θ₁ θ₂ 1 hα0 hγ0 (by norm_num)
    have hq (v : ℤ × ℤ) : 0 ≤ qForm α γ l θ₁ θ₂ v := by
      exact add_nonneg (mul_nonneg hα0.le (sq_nonneg _))
        (mul_nonneg hγ0.le (sq_nonneg _))
    have hmono : (∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ≤
        ∑' v : ℤ × ℤ, Real.exp (-(1 * qForm α γ l θ₁ θ₂ v)) := by
      apply Summable.tsum_le_tsum _ h.1 hs1.1
      intro v
      rw [Real.exp_le_exp]
      nlinarith [mul_le_mul_of_nonneg_right h1t (hq v)]
    have hsqA : 0 ≤ α ^ 2 - 1 := by nlinarith
    have hsqG : 0 ≤ γ ^ 2 - 1 := by nlinarith
    have hcoef : 1 + (α ^ 2 + γ ^ 2 + α ^ 2 * γ ^ 2) ≤
        3 * (α * γ) ^ 2 := by
      nlinarith [mul_nonneg hsqA hsqG]
    have hscaled := mul_le_mul_of_nonneg_left hcoef hC0
    have hup := (abs_le.mp hs1.2).2
    simp only [mul_one, one_mul, div_one] at hup hmono
    have htheta1 : (∑' v : ℤ × ℤ, Real.exp (-(qForm α γ l θ₁ θ₂ v))) ≤
        3 * (Real.pi / Real.sqrt (α * γ)) * (α * γ) ^ 2 := by
      nlinarith
    have hnonneg : 0 ≤ ∑' v : ℤ × ℤ,
        Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) :=
      tsum_nonneg (fun _ => (Real.exp_pos _).le)
    have hmain0 : 0 ≤ Real.pi / Real.sqrt (α * γ) / t := div_nonneg hC0 ht.le
    have hmain : Real.pi / Real.sqrt (α * γ) / t ≤
        Real.pi / Real.sqrt (α * γ) := div_le_self hC0 h1t
    have hCbig : Real.pi / Real.sqrt (α * γ) ≤
        3 * (Real.pi / Real.sqrt (α * γ)) * (α * γ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hP2 hC0]
    have htime : 3 * (Real.pi / Real.sqrt (α * γ)) * (α * γ) ^ 2 ≤
        3 * (Real.pi / Real.sqrt (α * γ)) * (α * γ) ^ 2 * t := by
      exact le_mul_of_one_le_right (by positivity) h1t
    rw [abs_le]
    constructor <;> linarith

end RHLean.Analysis.AlpogeThin.NativeRay.LatticeBounds
