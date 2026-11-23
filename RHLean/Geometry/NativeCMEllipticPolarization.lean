import RHLean.Geometry.NativeCMEllipticSeed

/-!
# Perfect integral polarization of the native CM elliptic seed

The orientation of the actual complex embedding is retained. The integral
alternating form is derived from the explicit positive metric on the actual
quadratic order, proved perfect, and proved adjoint to CM conjugation. The
normalization is not a chosen equality of two unrelated scalar quantities.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`HermFormPrincipalDimOne.lean` and
`ExistsCmEllipticCurveIntegersWithPeriod.lean`. This explicit coordinate
construction uses RHLean's actual quadratic order. It does not assert an
integral elliptic scheme, arithmetic degree, or Chowla--Selberg formula.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped ComplexConjugate

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : NativeGeometricHost E) (τ : E →+* ℂ)

/-- Both possible signs of the actual chosen CM embedding are retained. -/
def orientation : ℤ := if 0 < (omega H τ).im then 1 else -1

theorem orientation_eq_one_or_neg_one :
    orientation H τ = 1 ∨ orientation H τ = -1 := by
  by_cases h : 0 < (omega H τ).im
  · exact Or.inl (by simp [orientation, h])
  · exact Or.inr (by simp [orientation, h])

theorem orientation_mul_abs :
    (orientation H τ : ℝ) * |(omega H τ).im| = (omega H τ).im := by
  by_cases h : 0 < (omega H τ).im
  · simp [orientation, h, abs_of_pos h]
  · have hn : (omega H τ).im < 0 := lt_of_le_of_ne (le_of_not_gt h)
      (omega_im_ne_zero H τ)
    simp [orientation, h, abs_of_neg hn]

theorem inv_abs_mul_im :
    |(omega H τ).im|⁻¹ * (omega H τ).im = (orientation H τ : ℝ) := by
  have h := orientation_mul_abs H τ
  have h0 : |(omega H τ).im| ≠ 0 := abs_ne_zero.2 (omega_im_ne_zero H τ)
  apply (mul_left_cancel₀ h0)
  calc
    |(omega H τ).im| * (|(omega H τ).im|⁻¹ * (omega H τ).im) = (omega H τ).im := by
      rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]
    _ = |(omega H τ).im| * (orientation H τ : ℝ) := by linarith [h]

/-- The original positive metric has an integral imaginary part, with
exactly the orientation of the original periods. -/
theorem hermitian_coordinates_im (x y : ℤ × ℤ) :
    (hermitian H τ (period H τ (coordEquiv H x))
      (period H τ (coordEquiv H y))).im =
      ((orientation H τ * (x.2 * y.1 - x.1 * y.2) : ℤ) : ℝ) := by
  rw [period_coordinates, period_coordinates]
  have hcalc :
      (hermitian H τ ((x.1 : ℂ) + (x.2 : ℂ) * omega H τ)
        ((y.1 : ℂ) + (y.2 : ℂ) * omega H τ)).im =
      (|(omega H τ).im|⁻¹ * (omega H τ).im) *
        ((x.2 : ℝ) * (y.1 : ℝ) - (x.1 : ℝ) * (y.2 : ℝ)) := by
    simp only [hermitian, Complex.mul_im, Complex.mul_re, Complex.add_re,
      Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im]
    ring
  rw [hcalc, inv_abs_mul_im]
  push_cast
  rfl

/-- The perfect determinant form in actual integral coordinates. -/
def coordinateForm (s : ℤ) : LinearMap.BilinForm ℤ (ℤ × ℤ) :=
  LinearMap.mk₂ ℤ (fun x y => s * (x.2 * y.1 - x.1 * y.2))
    (fun x x' y => by simp; ring)
    (fun c x y => by simp; ring)
    (fun x y y' => by simp; ring)
    (fun c x y => by simp; ring)

/-- Pull back along the explicit integral basis of the ACTUAL quadratic order. -/
def form : LinearMap.BilinForm ℤ (OK H) :=
  (coordinateForm (orientation H τ)).comp
    (coordEquiv H).symm.toLinearMap (coordEquiv H).symm.toLinearMap

theorem form_coordinates (x y : ℤ × ℤ) :
    form H τ (coordEquiv H x) (coordEquiv H y) =
      orientation H τ * (x.2 * y.1 - x.1 * y.2) := by
  change coordinateForm (orientation H τ)
    ((coordEquiv H).symm (coordEquiv H x))
    ((coordEquiv H).symm (coordEquiv H y)) = _
  rw [(coordEquiv H).symm_apply_apply, (coordEquiv H).symm_apply_apply]
  rfl

theorem form_alt (x : OK H) : form H τ x x = 0 := by
  obtain ⟨u, rfl⟩ := (coordEquiv H).surjective x
  rw [form_coordinates]
  ring

theorem coordinateForm_bijective (s : ℤ) (hs : s = 1 ∨ s = -1) :
    Function.Bijective (coordinateForm s) := by
  constructor
  · intro x y h
    have h1 := congrArg (fun f : (ℤ × ℤ) →ₗ[ℤ] ℤ => f (0, 1)) h
    have h2 := congrArg (fun f : (ℤ × ℤ) →ₗ[ℤ] ℤ => f (1, 0)) h
    apply Prod.ext
    · rcases hs with rfl | rfl <;> simpa [coordinateForm] using h1
    · rcases hs with rfl | rfl <;> simpa [coordinateForm] using h2
  · intro f
    refine ⟨(-s * f (0, 1), s * f (1, 0)), ?_⟩
    apply LinearMap.ext
    intro x
    have hx : x = x.1 • (1, 0) + x.2 • (0, 1) := by ext <;> simp
    have hf : f x = x.1 * f (1, 0) + x.2 * f (0, 1) := by
      conv_lhs => rw [hx]
      simp
    rcases hs with rfl | rfl <;> simp [coordinateForm, hf] <;> ring

/-- The polarization is principal on the original integral order. -/
theorem form_bijective : Function.Bijective (form H τ) := by
  let e := coordEquiv H
  have hcoord := coordinateForm_bijective (orientation H τ)
    (orientation_eq_one_or_neg_one H τ)
  constructor
  · intro x y h
    apply e.symm.injective
    apply hcoord.1
    apply LinearMap.ext
    intro z
    have hz := congrArg (fun f : OK H →ₗ[ℤ] ℤ => f (e z)) h
    change coordinateForm (orientation H τ) (e.symm x) (e.symm (e z)) =
      coordinateForm (orientation H τ) (e.symm y) (e.symm (e z)) at hz
    simpa only [e.symm_apply_apply] using hz
  · intro f
    obtain ⟨x, hx⟩ := hcoord.2 (f.comp e.toLinearMap)
    refine ⟨e x, ?_⟩
    apply LinearMap.ext
    intro y
    change coordinateForm (orientation H τ) (e.symm (e x)) (e.symm y) = f y
    rw [e.symm_apply_apply, hx]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

theorem form_eq_hermitian_im (x y : OK H) :
    (form H τ x y : ℝ) = (hermitian H τ (period H τ x) (period H τ y)).im := by
  obtain ⟨u, rfl⟩ := (coordEquiv H).surjective x
  obtain ⟨v, rfl⟩ := (coordEquiv H).surjective y
  rw [form_coordinates, hermitian_coordinates_im]

theorem embed_bar (a : OK H) : embed H τ (barOK H a) = conj (embed H τ a) := by
  change τ ((H.bar (a : 𝓞 E) : 𝓞 E) : E) = conj (τ ((a : 𝓞 E) : E))
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]

/-- Complex multiplication is adjoint to the actual CM conjugation for the
constructed principal polarization, at both embedding orientations. -/
theorem form_adjoint (a x y : OK H) :
    form H τ (a * x) y = form H τ x (barOK H a * y) := by
  apply Int.cast_injective (α := ℝ)
  rw [form_eq_hermitian_im, form_eq_hermitian_im]
  change (hermitian H τ (embed H τ (a * x)) (embed H τ y)).im =
    (hermitian H τ (embed H τ x) (embed H τ (barOK H a * y))).im
  rw [map_mul, map_mul, embed_bar]
  congr 1
  simp [hermitian]
  ring

/-- Complete constructed analytic seed polarization and exact period
normalization, without an assumed elliptic-curve or period-comparison object. -/
theorem constructed_polarized_seed :
    Function.Injective (period H τ) ∧
    DiscreteTopology (lattice H τ) ∧
    Submodule.span ℝ (lattice H τ : Set ℂ) = ⊤ ∧
    CompactSpace (Torus H τ) ∧
    Function.Bijective (form H τ) ∧
    (∀ x, form H τ x x = 0) ∧
    (∀ a x y, form H τ (a * x) y = form H τ x (barOK H a * y)) ∧
    (∀ z : ℂ, z ≠ 0 → 0 < (hermitian H τ z z).re) ∧
    (∀ x y, (form H τ x y : ℝ) = (hermitian H τ (period H τ x) (period H τ y)).im) ∧
    Real.pi * (hermitian H τ 1 1).re = 2 * Real.pi / Real.sqrt H.d := by
  exact ⟨period_injective H τ, lattice_discrete H τ, lattice_full H τ,
    torus_compact H τ, form_bijective H τ, form_alt H τ, form_adjoint H τ,
    fun _ hz => hermitian_pos H τ hz, form_eq_hermitian_im H τ, pi_hermitian_one H τ⟩

end RHLean.Geometry.NativeCM.EllipticSeed

end
