import RHLean.Geometry.NativeThetaLatticeGridBounds

/-!
# The actual Hermitian lattice spans the ambient vector space

For the same integral lattice used by the theta polynomial constructor,
Hermitian self-duality and finite generation imply full span. The proof uses
the actual canonical CM conjugation and does not assume a spanning family.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`IsLocalizedModuleSubtype.lean`, namespace `GlobalTheory.DualFamily`,
through `span_eq_top`. The source archive/mirror states no license;
attribution is retained without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace RHLean.Geometry.NativeHermitianLattice

open NativeTheta.Paired

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/-- Exactly half the rational degree, as in the original CM-field estimate. -/
def halfDegree (E : Type) [Field E] [NumberField E] : ℕ := Module.finrank ℚ E / 2

def cc (x : E) : E := IsCMField.complexConj E x

theorem hermPairing_eq {n : ℕ} (x y : Fin n → E) :
    hermPairing E n x y = ∑ k, x k * cc (y k) := rfl

theorem hermPairing_symm {n : ℕ} (x y : Fin n → E) :
    hermPairing E n x y = cc (hermPairing E n y x) := by
  rw [hermPairing_eq, hermPairing_eq]
  unfold cc
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]

theorem isIntegral_cc {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (cc a) :=
  ha.map ((IsCMField.complexConj E).restrictScalars ℤ).toAlgHom

theorem exists_hermPairing_eq {n : ℕ} (f : (Fin n → E) →ₗ[E] E) :
    ∃ w : Fin n → E, ∀ u, f u = hermPairing E n u w := by
  refine ⟨fun a => cc (f fun b => if a = b then 1 else 0), fun u => ?_⟩
  rw [f.pi_apply_eq_sum_univ u, hermPairing_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold cc
  rw [IsCMField.complexConj_apply_apply, smul_eq_mul]

omit [IsCMField E] in
theorem eq_zero_of_line {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (w : Fin n → E) (hw : ∀ c : E, c • w ∈ Λ) : w = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  have htop : Λ.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) j) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ⟨(x / w j) • w, hw _, ?_⟩
    simp [div_mul_cancel₀ _ hj]
  have : Module.Finite (𝓞 E) E := ⟨by rw [← htop]; exact hfg.map _⟩
  have := Algebra.IsIntegral.of_finite (𝓞 E) E
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

/-- Self-duality supplies full span on the original lattice itself. -/
theorem span_eq_top {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (hermPairing E n x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨w, hw⟩ := exists_hermPairing_eq f
  have hline : ∀ c : E, c • w ∈ Λ := fun c => hdual _ fun y hy => by
    have hfy : f y = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hy))
    have hsmul : hermPairing E n (c • w) y = c * hermPairing E n w y := by
      simp only [hermPairing_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [hsmul, hermPairing_symm w y, ← hw, hfy]
    unfold cc
    rw [map_zero, mul_zero]
    exact isIntegral_zero
  have hw0 := eq_zero_of_line Λ hfg w hline
  exact hf0 (LinearMap.ext fun u => by simp [hw u, hw0])

end RHLean.Geometry.NativeHermitianLattice

end
