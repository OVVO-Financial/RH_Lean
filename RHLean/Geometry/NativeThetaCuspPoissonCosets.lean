import RHLean.Geometry.NativeThetaCuspGaussianPoisson
import RHLean.Geometry.NativeThetaCuspFourierResidues

/-!
# Exact Poisson transformation on the actual rational cosets

The actual Gaussian integral supplies the row transformation constant. Its
square and the scaling by R are proved explicitly, and the two convergent
coset sums satisfy the original inversion formula.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/PoissonSummationThetaSeriesRowTermCoset.lean.
The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Matrix Complex
open scoped ComplexConjugate Real BigOperators Classical

namespace RHLean.Geometry.NativeTheta.Cusp.FourierJ.Row

variable {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem qv_smul (v : ι → ℚ) (r : ℚ) : qv (r • v) = (r : ℂ) • qv v := by
  ext i; simp [qv]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] in

theorem poisson_class : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (R : ℕ), 0 < R → ∀ τ ∈ RHLean.Geometry.NativeTheta.Cusp.Siegel ι, -τ⁻¹ ∈ RHLean.Geometry.NativeTheta.Cusp.Siegel ι →
    IsUnit τ.det → ∃ c : ℂ, c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det) = 1 ∧
    ∀ (a : ι → ℚ) (ζ : ι → ℂ),
    (Summable fun m : ι → ℤ => ‖RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs τ ζ (a + (R : ℚ) • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m)‖) ∧
    (Summable fun m : ι → ℤ =>
      ‖RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m)‖) ∧
    cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) *
      ∑' m : ι → ℤ, RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs τ ζ (a + (R : ℚ) • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m) =
    c * ∑' m : ι → ℤ, RHLean.Geometry.NativeTheta.Cusp.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m)) *
      RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m) := by
  intro ι _ _ R hR τ hτ hτ' hdet
  have hτS : RHLean.Geometry.NativeTheta.Cusp.Riemann.IsSiegel τ := hτ
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  set Ω : Matrix ι ι ℂ := ((R ^ 2 : ℕ) : ℂ) • τ with hΩdef
  have hΩ : RHLean.Geometry.NativeTheta.Cusp.Riemann.IsSiegel Ω := hτS.natCast_smul (pow_pos hR 2)
  have hΩinv : Ω⁻¹ = ((R : ℂ) ^ 2)⁻¹ • τ⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [hΩdef, smul_mul_smul_comm, Matrix.nonsing_inv_mul τ hdet]
    push_cast
    rw [inv_mul_cancel₀ (pow_ne_zero 2 hRc), one_smul]
  have T1 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs τ ζ (a + (R : ℚ) • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m) =
      RHLean.Geometry.NativeTheta.Cusp.Riemann.riemannThetaTerm (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) m := by
    intro a ζ m
    have hv : RHLean.Geometry.NativeTheta.Cusp.qv (a + (R : ℚ) • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m) =
        (R : ℂ) • fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ) := by
      funext i
      simp only [RHLean.Geometry.NativeTheta.Cusp.qv, RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      push_cast
      field_simp
      ring
    simp only [RHLean.Geometry.NativeTheta.Cusp.Riemann.riemannThetaTerm_def, RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs, hv, Pi.zero_apply, Complex.ofReal_zero,
      add_zero]
    generalize (fun i => ((m i : ℤ) : ℂ) + (((a i : ℝ) / R : ℝ) : ℂ)) = x
    congr 1
    simp only [hΩdef, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    push_cast
    ring
  have T2 : ∀ (a : ι → ℚ) (ζ : ι → ℂ) (m : ι → ℤ),
      RHLean.Geometry.NativeTheta.Cusp.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m)) *
        RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m) =
      RHLean.Geometry.NativeTheta.Cusp.Riemann.riemannThetaTerm 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) m := by
    intro a ζ m
    have hv : RHLean.Geometry.NativeTheta.Cusp.qv ((R : ℚ)⁻¹ • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m) =
        (R : ℂ)⁻¹ • fun i => ((m i : ℤ) : ℂ) := by
      funext i
      simp [RHLean.Geometry.NativeTheta.Cusp.qv, RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv]
    have hsymm : ζ ᵥ* τ⁻¹ = τ⁻¹ *ᵥ ζ := by
      rw [← Matrix.mulVec_transpose, hτS.isSymm.inv.eq]
    have hq : (((a ⬝ᵥ ((R : ℚ)⁻¹ • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m) : ℚ)) : ℂ) =
        (fun i => ((m i : ℤ) : ℂ)) ⬝ᵥ fun i => (((a i : ℝ) / R : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.smul_apply, RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv, smul_eq_mul]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by ring
    have hsplit : (fun i => (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) i + (((a i : ℝ) / R : ℝ) : ℂ)) =
        Ω⁻¹ *ᵥ ((R : ℂ) • ζ) + fun i => (((a i : ℝ) / R : ℝ) : ℂ) := rfl
    simp only [RHLean.Geometry.NativeTheta.Cusp.Riemann.riemannThetaTerm_def, Pi.zero_apply, Complex.ofReal_zero, add_zero, hsplit]
    rw [RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs, RHLean.Geometry.NativeTheta.Cusp.FourierJ.ech, ← Complex.exp_add, hv, hsymm, hq]
    generalize (fun i => ((m i : ℤ) : ℂ)) = x
    congr 1
    simp only [hΩinv, Matrix.neg_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul,
      smul_dotProduct, dotProduct_neg, dotProduct_add, smul_eq_mul]
    first | (field_simp; ring) | field_simp | ring
  refine ⟨RHLean.Geometry.NativeTheta.Cusp.Riemann.siegelGaussIntegral Ω, ?_, fun a ζ => ?_⟩
  · have h := hΩ.siegelGaussIntegral_sq_mul_det
    rw [hΩdef, smul_smul, Matrix.det_smul] at h
    rw [show ((-I) * (R : ℂ) ^ 2) = -I * ((R ^ 2 : ℕ) : ℂ) by push_cast; ring]
    exact h
  have hS1 := hΩ.summable_norm_riemannThetaTerm (fun i => (a i : ℝ) / R) 0 ((R : ℂ) • ζ)
  have hS2 := hΩ.neg_inv.summable_norm_riemannThetaTerm 0 (fun i => (a i : ℝ) / R)
    (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))
  refine ⟨?_, ?_, ?_⟩
  · exact hS1.congr fun m => by rw [T1]
  · refine hS2.congr fun m => ?_
    rw [← T2, norm_mul, RHLean.Geometry.NativeTheta.Cusp.FourierJ.norm_ech, one_mul]
  · have e1 : ∑' m : ι → ℤ, RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs τ ζ (a + (R : ℚ) • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m) =
        RHLean.Geometry.NativeTheta.Cusp.Riemann.riemannTheta (fun i => (a i : ℝ) / R) 0 Ω ((R : ℂ) • ζ) := by
      rw [RHLean.Geometry.NativeTheta.Cusp.Riemann.riemannTheta_def]
      exact tsum_congr fun m => T1 a ζ m
    have e2 : ∑' m : ι → ℤ, RHLean.Geometry.NativeTheta.Cusp.FourierJ.ech (a ⬝ᵥ ((R : ℚ)⁻¹ • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m)) *
        RHLean.Geometry.NativeTheta.Cusp.FourierJ.gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • RHLean.Geometry.NativeTheta.Cusp.FourierJ.zv m) =
        RHLean.Geometry.NativeTheta.Cusp.Riemann.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ)) := by
      rw [RHLean.Geometry.NativeTheta.Cusp.Riemann.riemannTheta_def]
      exact tsum_congr fun m => T2 a ζ m
    have hw : (R : ℂ) • ζ ⬝ᵥ Ω⁻¹ *ᵥ ((R : ℂ) • ζ) = ζ ⬝ᵥ τ⁻¹ *ᵥ ζ := by
      rw [hΩinv]
      simp only [Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
        smul_eq_mul]
      first | (field_simp; ring) | field_simp
    rw [e1, e2, hΩ.riemannTheta_eq_neg_inv, hw]
    have hexp : cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) * cexp (-(π * I) * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]
      congr 1
      ring
    linear_combination (RHLean.Geometry.NativeTheta.Cusp.Riemann.siegelGaussIntegral Ω *
      RHLean.Geometry.NativeTheta.Cusp.Riemann.riemannTheta 0 (fun i => (a i : ℝ) / R) (-Ω⁻¹) (Ω⁻¹ *ᵥ ((R : ℂ) • ζ))) * hexp


end RHLean.Geometry.NativeTheta.Cusp.FourierJ.Row
