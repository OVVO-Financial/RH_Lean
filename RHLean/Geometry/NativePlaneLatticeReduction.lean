import Mathlib

/-!
# A reduced basis of the same integral plane lattice

An integral nearest-point row operation preserves the lattice and its area,
and halves the first squared norm whenever it exceeds twice that area.
Induction gives an actual basis of the same lattice with the required bound.
There is no reduced-basis or geometry-of-numbers estimate premise.

Reconstructed from Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/
PlaneLatticeShortBasisOfBoundPowTwo.lean, all three declarations.
The source mirror states no license; attribution is retained without assigning one.
The second generator's span-membership proof uses its explicit value after
case substitution, preserving the same elementary row operation.

Consumer: NativeRayQuadraticForm, where this bound supplies the lower
coefficient bound for the same actual ray-class lattice.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex

namespace RHLean.Geometry.NativePlaneLattice

theorem plane_lattice_reduction_step (e₁ e₂ : ℂ)
    (h : 2 * |((starRingEnd ℂ) e₁ * e₂).im| < ‖e₁‖ ^ 2) :
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      2 * ‖f₁‖ ^ 2 ≤ ‖e₁‖ ^ 2 := by
  have hN : 0 < ‖e₁‖ ^ 2 := lt_of_le_of_lt (by positivity) h
  set k : ℤ := round (((starRingEnd ℂ) e₁ * e₂).re / ‖e₁‖ ^ 2) with hk
  refine ⟨e₂ - k • e₁, e₁, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact Submodule.subset_span (by simp)
      · rw [hx]
        have hmem : (e₂ - k • e₁) + k • e₁ ∈
            Submodule.span ℤ {e₂ - k • e₁, e₁} :=
          Submodule.add_mem _ (Submodule.subset_span (by simp))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        simpa only [sub_add_cancel] using hmem
  · have : ((starRingEnd ℂ) (e₂ - k • e₁) * e₁).im = -((starRingEnd ℂ) e₁ * e₂).im := by
      simp
      ring
    rw [this, abs_neg]
  · have hr := abs_sub_round (((starRingEnd ℂ) e₁ * e₂).re / ‖e₁‖ ^ 2)
    rw [← hk] at hr
    have key : ‖e₁‖ ^ 2 * ‖e₂ - k • e₁‖ ^ 2 =
        (((starRingEnd ℂ) e₁ * e₂).re - k * ‖e₁‖ ^ 2) ^ 2 +
          ((starRingEnd ℂ) e₁ * e₂).im ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    generalize ((starRingEnd ℂ) e₁ * e₂).re = R at *
    generalize ((starRingEnd ℂ) e₁ * e₂).im = J at *
    generalize ‖e₁‖ ^ 2 = N at *
    generalize ‖e₂ - k • e₁‖ ^ 2 = M at *
    have h1 : (R - k * N) ^ 2 ≤ N ^ 2 / 4 := by
      have e : R - k * N = (R / N - k) * N := by field_simp
      have h2 : (R / N - k) ^ 2 ≤ 1 / 4 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (R / N - k)]
      rw [e, mul_pow]
      nlinarith [sq_nonneg N]
    have h3 : J ^ 2 ≤ N ^ 2 / 4 := by
      rw [← sq_abs J]
      nlinarith [abs_nonneg J]
    have h4 : N * (2 * M) ≤ N * N := by nlinarith
    exact le_of_mul_le_mul_left h4 hN

theorem plane_lattice_short_basis_of_bound_pow_two (n : ℕ) : ∀ e₁ e₂ : ℂ,
    ‖e₁‖ ^ 2 ≤ 2 ^ n * (2 * |((starRingEnd ℂ) e₁ * e₂).im|) →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by
  induction n with
  | zero =>
    intro e₁ e₂ h
    exact ⟨e₁, e₂, rfl, rfl, by simpa using h⟩
  | succ n ih =>
    intro e₁ e₂ h
    by_cases hc : ‖e₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im|
    · exact ⟨e₁, e₂, rfl, rfl, hc⟩
    · obtain ⟨g₁, g₂, hs, hi, hn⟩ := plane_lattice_reduction_step e₁ e₂ (not_le.mp hc)
      obtain ⟨f₁, f₂, hs', hi', hn'⟩ := ih g₁ g₂ (by
        rw [hi]
        rw [pow_succ (2 : ℝ) n] at h
        linarith)
      exact ⟨f₁, f₂, hs'.trans hs, hi'.trans hi, hi ▸ hn'⟩

theorem plane_lattice_short_basis : ∀ e₁ e₂ : ℂ, ((starRingEnd ℂ) e₁ * e₂).im ≠ 0 →
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      ‖f₁‖ ^ 2 ≤ 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by
  intro e₁ e₂ h
  have hD : 0 < 2 * |((starRingEnd ℂ) e₁ * e₂).im| := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt
    (‖e₁‖ ^ 2 / (2 * |((starRingEnd ℂ) e₁ * e₂).im|)) (one_lt_two (α := ℝ))
  exact plane_lattice_short_basis_of_bound_pow_two n e₁ e₂ ((div_lt_iff₀ hD).mp hn).le

end RHLean.Geometry.NativePlaneLattice

end
