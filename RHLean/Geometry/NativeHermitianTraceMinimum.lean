import RHLean.Geometry.NativeHermitianLatticeSpan
import RHLean.Geometry.NativeTraceDualDiscriminant

/-!
# Trace-dual minimum for the actual Hermitian lattice

The canonical Hermitian norm of a nonzero trace-dual vector has the original
lower bound in terms of the discriminant of the same CM field. Integral
self-duality of the same lattice supplies the inverse-different membership;
no short-vector or norm estimate is a hypothesis.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`EmbeddingHermSelf.lean`, `GlobalTheory.trace_dual_min` and its helpers.
The native trace-dual discriminant suppliers replace the original imports.
The source archive/mirror states no license; attribution is retained
without assigning a new license.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace RHLean.Geometry.NativeHermitianLattice

open NativeTheta.Paired NativeNumberFieldLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace TraceDualMin

theorem herm_smul_left {n : ℕ} (a : E) (x y : Fin n → E) :
    hermPairing E n (a • x) y = a * hermPairing E n x y := by
  simp [Finset.mul_sum, mul_assoc]

theorem herm_smul_right {n : ℕ} (a : E) (x y : Fin n → E) :
    hermPairing E n x (a • y) = cc a * hermPairing E n x y := by
  simp [Finset.mul_sum, cc, mul_left_comm]

theorem cc_cc (a : E) : cc (cc a) = a := by
  simp [cc]

theorem cc_herm_self {n : ℕ} (x : Fin n → E) : cc (hermPairing E n x x) = hermPairing E n x x := by
  simp [cc, mul_comm]

theorem trace_cc (a : E) : Algebra.trace ℚ E (cc a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a

theorem embedding_herm_self {n : ℕ} (σ : E →+* ℂ) (x : Fin n → E) :
    σ (hermPairing E n x x) = ((∑ k, ‖σ (x k)‖ ^ 2 : ℝ) : ℂ) := by
  simp [IsCMField.complexEmbedding_complexConj, Complex.mul_conj']

omit [IsCMField E] in

theorem mem_inv_different {x : E} (hx : ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (x * a) = k) :
    x ∈ (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one,
    Submodule.mem_traceDual]
  intro a ha
  obtain ⟨b, rfl⟩ := Submodule.mem_one.mp ha
  obtain ⟨k, hk⟩ := hx b
  exact ⟨k, by rw [Algebra.traceForm_apply]; simpa using hk.symm⟩

end TraceDualMin

open TraceDualMin in

theorem trace_dual_min {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (_hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y)) (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y)) → x ∈ Λ)
    (u : Fin n → E) (hu : u ≠ 0) (htr : ∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (hermPairing E n u y) = k) :
    2 * (halfDegree E : ℝ) / rootDiscr E ^ 2 ≤ ∑ σ : E →+* ℂ, ∑ k, ‖σ (u k)‖ ^ 2 := by
  set D : FractionalIdeal (𝓞 E)⁰ E := (differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr differentIdeal_ne_bot

  have h1 : ∀ y ∈ Λ, hermPairing E n u y ∈ D⁻¹ := by
    intro y hy
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem (⟨cc (a : E), isIntegral_cc a.isIntegral_coe⟩ : 𝓞 E) hy)
    refine ⟨k, ?_⟩
    rw [← hk]
    change _ = Algebra.trace ℚ E (hermPairing E n u (cc (a : E) • y))
    rw [herm_smul_right, cc_cc, mul_comm]
  have h2 : ∀ δ ∈ D, δ • u ∈ Λ := by
    intro δ hδ
    refine hdual _ fun y hy => ?_
    rw [herm_smul_left]
    have := FractionalIdeal.mul_mem_mul hδ (h1 y hy)
    rw [mul_inv_cancel₀ hD0] at this
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp this
    rw [← hb]
    exact b.isIntegral_coe
  have h3 : ∀ δ ∈ D, hermPairing E n u u * δ ∈ D⁻¹ := by
    intro δ hδ
    refine mem_inv_different fun a => ?_
    obtain ⟨k, hk⟩ := htr _ (Λ.smul_mem a (h2 δ hδ))
    refine ⟨k, ?_⟩
    rw [← hk, ← trace_cc]
    change _ = Algebra.trace ℚ E (hermPairing E n u ((a : E) • δ • u))
    rw [herm_smul_right, herm_smul_right]
    congr 1
    conv_rhs => rw [← cc_herm_self u]
    simp only [cc, map_mul]
    ring
  have h4 : hermPairing E n u u ∈ D⁻¹ * D⁻¹ := by
    rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hD0]
    exact h3
  have hnorm : ∀ σ : E →+* ℂ, ‖σ (hermPairing E n u u)‖ = ∑ k, ‖σ (u k)‖ ^ 2 := by
    intro σ
    rw [embedding_herm_self, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h0 : hermPairing E n u u ≠ 0 := by
    intro h
    obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := hnorm σ
    rw [h, map_zero, norm_zero, eq_comm,
      Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at this
    apply hu
    funext k
    simpa using this k (Finset.mem_univ k)
  have h5 := absNorm_le_abs_norm_of_mem h4 h0
  rw [map_mul, hD, absNorm_inv_differentIdeal] at h5
  have h6 : (|(discr E : ℝ)|)⁻¹ * (|(discr E : ℝ)|)⁻¹ ≤ |((Algebra.norm ℚ (hermPairing E n u u) : ℚ) : ℝ)| := by
    have h := (Rat.cast_le (K := ℝ)).mpr h5
    simpa using h
  have h7 := finrank_mul_abs_norm_rpow_le_sum (hermPairing E n u u)
  simp only [hnorm] at h7
  refine le_trans ?_ h7
  have hd : 0 ≤ |(discr E : ℝ)| := abs_nonneg _
  have hf : 2 * (halfDegree E : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Nat.mul_div_le (Module.finrank ℚ E) 2
  have h8 : (rootDiscr E ^ 2)⁻¹ = ((|(discr E : ℝ)|)⁻¹ * (|(discr E : ℝ)|)⁻¹) ^ ((Module.finrank ℚ E : ℝ)⁻¹) := by
    rw [Real.mul_rpow (inv_nonneg.mpr hd) (inv_nonneg.mpr hd), Real.inv_rpow hd, rootDiscr_def, sq,
      mul_inv]
    rw [Int.cast_abs]
  rw [div_eq_mul_inv, h8]
  gcongr


end RHLean.Geometry.NativeHermitianLattice

end
