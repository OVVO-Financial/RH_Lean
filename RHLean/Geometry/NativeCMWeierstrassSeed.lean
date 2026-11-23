import RHLean.Geometry.NativeCMEllipticPolarization
import RHLean.Geometry.NativeCMWeierstrassCMIntegrality
import RHLean.Geometry.NativeCMWeierstrassFiniteModel

/-!
# An integral Weierstrass equation for the actual quadratic CM seed

The upper-half-plane period is chosen from the actual pair `1, tau(H.w0)`.
Its integral span is proved equal to the existing analytic seed lattice.
The modular invariant is the analytic function `E₄^3 / discriminant`;
its integrality is proved from this period's quadratic equation, using the
explicit modular-polynomial proof in `NativeCMWeierstrassCMIntegrality`.

The finite integral-model construction then gives an actual Weierstrass
equation over the integers of a number field containing the chosen image of
the native host. Its discriminant is exactly one and its `j`, `c₄`, and `c₆`
invariants are compared exactly with that same analytic modular invariant.
This is an equation construction. The scheme group law, origin polarization,
algebraic uniformization, and arithmetic tangent-period comparison are
subsequent obligations; none is asserted by the equation's existence.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsFieldCmCurvesUnitDiscriminant.lean`, declarations
`CMCurves.exists_integral_curve` and `exists_field_cm_curves_unit_discriminant`.
The latter is specialized here to the actual native seed, with its field and
period inclusions constructed explicitly. The seven supplying proof modules
contain the modular integrality and finite integral-model proofs themselves.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped UpperHalfPlane

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : NativeGeometricHost E) (τ : E →+* ℂ)

/-- Orient the actual quadratic period in the upper half plane. Replacing
`omega` by `1 - omega` preserves its integral lattice. -/
def upperPeriod : ℍ :=
  if h : 0 < (omega H τ).im then ⟨omega H τ, h⟩
  else ⟨1 - omega H τ, by
    have hn : (omega H τ).im < 0 :=
      (lt_or_gt_of_ne (omega_im_ne_zero H τ)).resolve_right h
    simpa using neg_pos.mpr hn⟩

theorem upperPeriod_eq_or :
    (upperPeriod H τ : ℂ) = omega H τ ∨
      (upperPeriod H τ : ℂ) = 1 - omega H τ := by
  by_cases h : 0 < (omega H τ).im <;> simp [upperPeriod, h]

theorem upperPeriod_re : (upperPeriod H τ).re = 1 / 2 := by
  change (upperPeriod H τ : ℂ).re = 1 / 2
  rcases upperPeriod_eq_or H τ with h | h
  · simpa only [h] using omega_re H τ
  · simp only [h, Complex.sub_re, Complex.one_re, omega_re]
    norm_num

theorem upperPeriod_im : (upperPeriod H τ).im = |(omega H τ).im| := by
  by_cases h : 0 < (omega H τ).im
  · simp [upperPeriod, h, abs_of_pos h]
  · have hn : (omega H τ).im < 0 :=
      (lt_or_gt_of_ne (omega_im_ne_zero H τ)).resolve_right h
    simp [upperPeriod, h, abs_of_neg hn]

theorem upperPeriod_im_exact : (upperPeriod H τ).im = Real.sqrt H.d / 2 :=
  (upperPeriod_im H τ).trans (abs_omega_im H τ)

theorem upperPeriod_sq_eq_neg :
    (2 * (upperPeriod H τ : ℂ) - 1) ^ 2 = -(H.d : ℂ) := by
  have hs : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    simpa using congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
  have hw : (2 * omega H τ - 1) ^ 2 = -(H.d : ℂ) := by
    rw [two_mul_omega]
    simpa using hs
  rcases upperPeriod_eq_or H τ with h | h
  · simpa only [h] using hw
  · rw [h]
    linear_combination hw

theorem mem_lattice_iff_coordinates (z : ℂ) :
    z ∈ lattice H τ ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * omega H τ := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := (coordEquiv H).surjective a
    exact ⟨x.1, x.2, period_coordinates H τ x⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨coordEquiv H (m, n), period_coordinates H τ (m, n)⟩

/-- The normalized upper period defines exactly the original lattice. -/
theorem lattice_eq_span_upperPeriod :
    lattice H τ = Submodule.span ℤ {(upperPeriod H τ : ℂ), 1} := by
  ext z
  rw [mem_lattice_iff_coordinates, Submodule.mem_span_pair]
  rcases upperPeriod_eq_or H τ with h | h
  · rw [h]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by simp [zsmul_eq_mul, add_comm]⟩
    · rintro ⟨m, n, hz⟩
      exact ⟨n, m, by simpa [zsmul_eq_mul, add_comm] using hz.symm⟩
  · rw [h]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨-n, m + n, ?_⟩
      simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_add, mul_one]
      ring
    · rintro ⟨m, n, hz⟩
      refine ⟨m + n, -m, ?_⟩
      rw [← hz]
      simp only [zsmul_eq_mul, Int.cast_neg, Int.cast_add, mul_one]
      ring

/-- The analytic modular invariant of this actual period is integral. -/
theorem isIntegral_modularJ_upperPeriod :
    IsIntegral ℤ (Weierstrass.modularJ (upperPeriod H τ)) := by
  apply Weierstrass.isIntegral_modularJ_of_sq_eq_neg (d := (H.d : ℤ))
  simpa using upperPeriod_sq_eq_neg H τ

end RHLean.Geometry.NativeCM.EllipticSeed

namespace RHLean.Geometry.NativeCM.Weierstrass

/-- Integral `j` yields an actual complex equation with integral coefficients
and discriminant one, through the finite 12-torsion integral-model proof. -/
theorem exists_complex_integral_curve {j : ℂ} (hj : IsIntegral ℤ j) :
    ∃ W : WeierstrassCurve ℂ, IsIntegral ℤ W.a₁ ∧ IsIntegral ℤ W.a₂ ∧
      IsIntegral ℤ W.a₃ ∧ IsIntegral ℤ W.a₄ ∧ IsIntegral ℤ W.a₆ ∧
      W.Δ = 1 ∧ W.c₄ ^ 3 = j := by
  classical
  have hjQ : IsIntegral ℚ j := hj.tower_top
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {j}
  have : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hjQ
  have : NumberField K := ⟨⟩
  let jK : K := ⟨j, IntermediateField.mem_adjoin_simple_self ℚ j⟩
  have hWj : (WeierstrassCurve.ofJ jK).j = jK := WeierstrassCurve.ofJ_j jK
  have hjK : IsIntegral ℤ (WeierstrassCurve.ofJ jK).j := by
    rw [hWj]
    exact (isIntegral_algHom_iff ((K.val : K →+* ℂ).toIntAlgHom) Subtype.val_injective).1 hj
  obtain ⟨M, hNF, -, C, W₀, hW, hΔ⟩ :=
    exists_finite_model_ringOfIntegers (WeierstrassCurve.ofJ jK) hjK
  have := hNF
  let ψ : M →ₐ[K] ℂ := (IsAlgClosed.lift : AlgebraicClosure K →ₐ[K] ℂ).comp M.val
  have : ((WeierstrassCurve.ofJ jK).baseChange M).IsElliptic :=
    ⟨by rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
        exact (WeierstrassCurve.isUnit_Δ _).map _⟩
  have : W₀.IsElliptic := ⟨by rw [hΔ]; exact isUnit_one⟩
  have hint : ∀ x : 𝓞 M, IsIntegral ℤ (ψ (x : M)) := fun x =>
    x.isIntegral_coe.map (ψ : M →+* ℂ).toIntAlgHom
  have h1 : (C • (WeierstrassCurve.ofJ jK).baseChange M).j = algebraMap K M jK := by
    rw [WeierstrassCurve.variableChange_j]
    erw [WeierstrassCurve.map_j, hWj]
  have h2 := (j_mul_Δ (C • (WeierstrassCurve.ofJ jK).baseChange M)).symm
  rw [h1, hW] at h2
  have hB : (W₀.baseChange M).Δ = 1 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, hΔ, map_one]
  refine ⟨(W₀.baseChange M).map (ψ : M →+* ℂ), hint _, hint _, hint _, hint _, hint _, ?_, ?_⟩
  · rw [WeierstrassCurve.map_Δ, hB, map_one]
  · rw [WeierstrassCurve.map_c₄, ← map_pow, h2, hB, mul_one]
    show ψ (algebraMap K M jK) = j
    rw [AlgHom.commutes]
    rfl

open EllipticSeed

/-- A number field containing the native host image and a discriminant-one
integral equation with the exact modular invariant of the native seed lattice.
The chosen integral CM generator is retained in the same field. -/
theorem exists_integral_equation_for_seed
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : NativeGeometricHost E) (τ : E →+* ℂ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
      (W : WeierstrassCurve (𝓞 M)) (w : 𝓞 M) (hΔ : W.Δ = 1),
      (∀ a : E, τ a ∈ M) ∧
      ((w : M) : ℂ) = omega H τ ∧
      (((W.c₄ : M) : ℂ)) ^ 3 = modularJ (upperPeriod H τ) ∧
      (((W.c₆ : M) : ℂ)) ^ 2 = modularJ (upperPeriod H τ) - 1728 ∧
      (let _ : W.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
       ((W.j : M) : ℂ) = modularJ (upperPeriod H τ)) := by
  classical
  obtain ⟨V, h1, h2, h3, h4, h6, hΔV, hc4V⟩ :=
    exists_complex_integral_curve (isIntegral_modularJ_upperPeriod H τ)
  let T : Set ℂ := {V.a₁, V.a₂, V.a₃, V.a₄, V.a₆}
  have hT : T.Finite := by dsimp [T]; simp
  have : Finite T := hT.to_subtype
  have hTint : ∀ z ∈ T, IsIntegral ℤ z := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
  let τ' : E →ₐ[ℚ] ℂ := τ.toRatAlgHom
  have : FiniteDimensional ℚ τ'.fieldRange :=
    (AlgEquiv.ofInjectiveField τ').toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (hTint z hz).tower_top
  let M : IntermediateField ℚ ℂ := τ'.fieldRange ⊔ IntermediateField.adjoin ℚ T
  have : NumberField M := ⟨⟩
  have hhost : ∀ a : E, τ a ∈ M := fun a =>
    (le_sup_left : τ'.fieldRange ≤ M) ⟨a, rfl⟩
  have hTM : ∀ z ∈ T, z ∈ M := fun z hz =>
    (le_sup_right : IntermediateField.adjoin ℚ T ≤ M) (IntermediateField.subset_adjoin ℚ T hz)
  have mk : ∀ z ∈ T, IsIntegral ℤ z → ∃ t : 𝓞 M, ((t : M) : ℂ) = z := fun z hz hi =>
    ⟨⟨⟨z, hTM z hz⟩, (isIntegral_algHom_iff ((M.val : M →+* ℂ).toIntAlgHom)
      Subtype.val_injective).1 hi⟩, rfl⟩
  obtain ⟨t1, ht1⟩ := mk _ (by simp [T]) h1
  obtain ⟨t2, ht2⟩ := mk _ (by simp [T]) h2
  obtain ⟨t3, ht3⟩ := mk _ (by simp [T]) h3
  obtain ⟨t4, ht4⟩ := mk _ (by simp [T]) h4
  obtain ⟨t6, ht6⟩ := mk _ (by simp [T]) h6
  let W : WeierstrassCurve (𝓞 M) := ⟨t1, t2, t3, t4, t6⟩
  let φ : 𝓞 M →+* ℂ := (M.val : M →+* ℂ).comp (algebraMap (𝓞 M) M)
  have hφ : Function.Injective φ :=
    Subtype.val_injective.comp RingOfIntegers.coe_injective
  have hWV : W.map φ = V := by
    ext
    · exact ht1
    · exact ht2
    · exact ht3
    · exact ht4
    · exact ht6
  have hWΔ : W.Δ = 1 := hφ (by rw [← WeierstrassCurve.map_Δ, hWV, hΔV, map_one])
  have hWc4 : ((W.c₄ : M) : ℂ) = V.c₄ := by
    rw [← hWV, WeierstrassCurve.map_c₄]
    rfl
  have hWc6 : ((W.c₆ : M) : ℂ) = V.c₆ := by
    rw [← hWV, WeierstrassCurve.map_c₆]
    rfl
  have hω : IsIntegral ℤ (τ (H.w0 : E)) :=
    H.w0.isIntegral_coe.map τ.toIntAlgHom
  let w : 𝓞 M := ⟨⟨τ (H.w0 : E), hhost (H.w0 : E)⟩,
    (isIntegral_algHom_iff ((M.val : M →+* ℂ).toIntAlgHom) Subtype.val_injective).1 hω⟩
  refine ⟨M, inferInstance, W, w, hWΔ, hhost, ?_, ?_, ?_, ?_⟩
  · simp [w, omega, embed_wK]
  · rw [hWc4]
    exact hc4V
  · rw [hWc6]
    have hrel := V.c_relation
    rw [hΔV, hc4V] at hrel
    linear_combination -hrel
  · let _ : W.IsElliptic := ⟨hWΔ ▸ isUnit_one⟩
    have hj : W.j = W.c₄ ^ 3 := by simpa [hWΔ] using j_mul_Δ W
    change ((W.j : M) : ℂ) = modularJ (upperPeriod H τ)
    rw [hj]
    simpa [hWc4] using hc4V

end RHLean.Geometry.NativeCM.Weierstrass

end
