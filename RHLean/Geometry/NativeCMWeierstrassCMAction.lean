import RHLean.Geometry.NativeCMWeierstrassIntegralSchemeSeed
import RHLean.Geometry.NativeCMWeierstrassTorsionAlgebraicity
import RHLean.Geometry.NativeCMWeierstrassPeriodScaling

/-!
# The actual CM point action has algebraic rational coordinates

The period pair is rescaled by the inverse of the same coordinate-change
unit u. Its invariants are exactly c4(W)/12 and c6(W)/216 for the original
integral equation W. The original quadratic generator acts on this lattice,
and its kernel is killed by the positive integer (1+d)/4.

The finite kernel coordinates are proved algebraic and adjoined to the same
number field. The resulting rational point formula retains leading
coefficient alpha^-2, derivative factor alpha^-1, and degree equal to the
actual kernel cardinality. The rescaled point equivalence identifies it
with the previously constructed CM action on W, including the original u.

The analytic suppliers are the attributed native rational-numerator,
isogeny, torsion-algebraicity and period-scaling proofs. No scheme morphism,
integral extension theorem, or polarization theorem is assumed or asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField PeriodPair Polynomial

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (C : WeierstrassCurve.VariableChange ℂ)

/-- The lattice in the actual integral tangent coordinate, retaining u. -/
def rescaledPeriods : PeriodPair :=
  Weierstrass.scalePeriods (periodPair G τ) (C.u : ℂ)⁻¹ (inv_ne_zero C.u.ne_zero)

theorem rescaledPeriods_mem (z : ℂ) :
    z ∈ (rescaledPeriods G τ C).lattice ↔ (C.u : ℂ) * z ∈ (periodPair G τ).lattice := by
  have h := Weierstrass.isHomothetic_scalePeriods (periodPair G τ)
    (C.u : ℂ)⁻¹ (inv_ne_zero C.u.ne_zero) ((C.u : ℂ) * z)
  simpa only [rescaledPeriods, inv_mul_cancel_left₀ C.u.ne_zero] using h

theorem rescaledPeriods_g₂ :
    (rescaledPeriods G τ C).g₂ = (C.u : ℂ) ^ 4 * (periodPair G τ).g₂ := by
  have h := (Weierstrass.isHomothetic_scalePeriods (periodPair G τ)
    (C.u : ℂ)⁻¹ (inv_ne_zero C.u.ne_zero)).g₂_eq
  simpa only [rescaledPeriods, inv_pow, inv_inv] using h

theorem rescaledPeriods_g₃ :
    (rescaledPeriods G τ C).g₃ = (C.u : ℂ) ^ 6 * (periodPair G τ).g₃ := by
  have h := (Weierstrass.isHomothetic_scalePeriods (periodPair G τ)
    (C.u : ℂ)⁻¹ (inv_ne_zero C.u.ne_zero)).g₃_eq
  simpa only [rescaledPeriods, inv_pow, inv_inv] using h

theorem rescaledPeriods_weierstrassP (z : ℂ) :
    (rescaledPeriods G τ C).weierstrassP z =
      (C.u : ℂ) ^ 2 * (periodPair G τ).weierstrassP ((C.u : ℂ) * z) := by
  have h := (Weierstrass.isHomothetic_scalePeriods (periodPair G τ)
    (C.u : ℂ)⁻¹ (inv_ne_zero C.u.ne_zero)).weierstrassP_mul ((C.u : ℂ) * z)
  simpa only [rescaledPeriods, inv_mul_cancel_left₀ C.u.ne_zero, inv_pow, inv_inv] using h

theorem rescaledPeriods_derivWeierstrassP (z : ℂ) :
    (rescaledPeriods G τ C).derivWeierstrassP z =
      (C.u : ℂ) ^ 3 * (periodPair G τ).derivWeierstrassP ((C.u : ℂ) * z) := by
  have h := (Weierstrass.isHomothetic_scalePeriods (periodPair G τ)
    (C.u : ℂ)⁻¹ (inv_ne_zero C.u.ne_zero)).derivWeierstrassP_mul ((C.u : ℂ) * z)
  simpa only [rescaledPeriods, inv_mul_cancel_left₀ C.u.ne_zero, inv_pow, inv_inv] using h

/-- The original order multiplication preserves the rescaled actual lattice. -/
theorem rescaledPeriods_multiplier (a : OK G) (z : ℂ)
    (hz : z ∈ (rescaledPeriods G τ C).lattice) :
    embed G τ a * z ∈ (rescaledPeriods G τ C).lattice := by
  rw [rescaledPeriods_mem] at hz ⊢
  rw [periodPair_lattice] at hz ⊢
  obtain ⟨b, hb⟩ := hz
  refine ⟨a * b, ?_⟩
  change embed G τ (a * b) = (C.u : ℂ) * (embed G τ a * z)
  change embed G τ b = (C.u : ℂ) * z at hb
  rw [map_mul, hb]
  ring

theorem omega_ne_zero : omega G τ ≠ 0 := by
  intro h
  exact omega_im_ne_zero G τ (by simp [h])

/-- The generator's actual norm, which kills its period kernel. -/
abbrev generatorNorm : ℕ := (1 + G.d) / 4

theorem generatorNorm_pos : 0 < generatorNorm G := by
  have h := G.d_mod
  dsimp [generatorNorm]
  omega

theorem generator_mul_conjugate :
    (1 - omega G τ) * omega G τ = (generatorNorm G : ℂ) := by
  linear_combination -(omega_quadratic G τ)

theorem cm_kernel_period_killed (z : ℂ)
    (hz : omega G τ * z ∈ (rescaledPeriods G τ C).lattice) :
    (generatorNorm G : ℂ) * z ∈ (rescaledPeriods G τ C).lattice := by
  have h := rescaledPeriods_multiplier G τ C (1 - wK G) (omega G τ * z) hz
  have he : embed G τ (1 - wK G) * omega G τ = (generatorNorm G : ℂ) := by
    rw [map_sub, map_one]
    exact generator_mul_conjugate G τ
  simpa only [← mul_assoc, he] using h

/-- Literal multiplication by the original CM generator on the rescaled curve. -/
def rescaledCMAction :
    (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point →+
      (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point :=
  Weierstrass.latticeIsogeny (omega G τ) (rescaledPeriods_multiplier G τ C (wK G))

@[simp] theorem rescaledCMAction_latticePoint (z : ℂ) :
    rescaledCMAction G τ C (Weierstrass.latticePoint (rescaledPeriods G τ C) z) =
      Weierstrass.latticePoint (rescaledPeriods G τ C) (omega G τ * z) :=
  Weierstrass.latticeIsogeny_latticePoint _ z

/-- This is the original quadratic relation on the actual point group. -/
theorem rescaledCMAction_quadratic
    (P : (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point) :
    rescaledCMAction G τ C (rescaledCMAction G τ C P) + generatorNorm G • P =
      rescaledCMAction G τ C P := by
  obtain ⟨z, rfl⟩ := Weierstrass.latticePoint_surjective (rescaledPeriods G τ C) P
  simp only [rescaledCMAction_latticePoint]
  have h : omega G τ * (omega G τ * z) + (generatorNorm G : ℂ) * z =
      omega G τ * z := by
    linear_combination z * omega_quadratic G τ
  have h' := congrArg (Weierstrass.latticePointHom (rescaledPeriods G τ C)) h
  simpa only [map_add, ← nsmul_eq_mul, map_nsmul,
    Weierstrass.latticePointHom_apply] using h'

/-- Homothety on the actual point groups, with both multipliers specified. -/
def rescaledPointEquiv :
    (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point ≃+
      (Weierstrass.latticeCurve (periodPair G τ)).toAffine.Point where
  toFun := Weierstrass.latticeIsogeny (C.u : ℂ)
    (fun z hz => (rescaledPeriods_mem G τ C z).1 hz)
  invFun := Weierstrass.latticeIsogeny (C.u : ℂ)⁻¹ (fun z hz =>
    (rescaledPeriods_mem G τ C _).2 (by simpa only [mul_inv_cancel_left₀ C.u.ne_zero] using hz))
  left_inv P := by
    obtain ⟨z, rfl⟩ := Weierstrass.latticePoint_surjective (rescaledPeriods G τ C) P
    rw [Weierstrass.latticeIsogeny_latticePoint, Weierstrass.latticeIsogeny_latticePoint,
      inv_mul_cancel_left₀ C.u.ne_zero]
  right_inv P := by
    obtain ⟨z, rfl⟩ := Weierstrass.latticePoint_surjective (periodPair G τ) P
    rw [Weierstrass.latticeIsogeny_latticePoint, Weierstrass.latticeIsogeny_latticePoint,
      mul_inv_cancel_left₀ C.u.ne_zero]
  map_add' P Q := map_add _ P Q

variable (W : WeierstrassCurve ℂ)
    (hC : C • W = Weierstrass.latticeCurve (periodPair G τ))

/-- The rescaled curve is compared with the same W through the original C. -/
def rescaledEquationPointEquiv :
    (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point ≃+ W.toAffine.Point :=
  (rescaledPointEquiv G τ C).trans (Weierstrass.variableChangePointEquiv C hC)

theorem rescaledEquationPointEquiv_latticePoint (z : ℂ) :
    rescaledEquationPointEquiv G τ C W hC
        (Weierstrass.latticePoint (rescaledPeriods G τ C) z) =
      equationExponential G τ W C hC ((C.u : ℂ) * z) := by
  change Weierstrass.variableChangePoint C hC
    (Weierstrass.latticeIsogeny (C.u : ℂ) _
      (Weierstrass.latticePoint (rescaledPeriods G τ C) z)) = _
  rw [Weierstrass.latticeIsogeny_latticePoint, equationExponential_apply]

/-- The rational point isogeny is the previously constructed actual action
on W, transported by the specified homothety and coordinate change. -/
theorem rescaledCMAction_equationCMAction
    (P : (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point) :
    rescaledEquationPointEquiv G τ C W hC (rescaledCMAction G τ C P) =
      equationCMAction G τ W C hC (wK G) (rescaledEquationPointEquiv G τ C W hC P) := by
  obtain ⟨z, rfl⟩ := Weierstrass.latticePoint_surjective (rescaledPeriods G τ C) P
  rw [rescaledCMAction_latticePoint, rescaledEquationPointEquiv_latticePoint,
    rescaledEquationPointEquiv_latticePoint, equationCMAction_exponential]
  simp only [omega]
  congr 1
  ring

include hC in
theorem rescaledPeriods_g₂_eq_invariant :
    (rescaledPeriods G τ C).g₂ = W.c₄ / 12 := by
  have h4 : (C.u : ℂ) ^ 4 * (Weierstrass.latticeCurve (periodPair G τ)).c₄ = W.c₄ := by
    rw [← hC, WeierstrassCurve.variableChange_c₄, ← mul_assoc, ← mul_pow]
    simp
  rw [Weierstrass.latticeCurve_c₄] at h4
  rw [rescaledPeriods_g₂]
  apply (eq_div_iff (by norm_num : (12 : ℂ) ≠ 0)).2
  linear_combination h4

include hC in
theorem rescaledPeriods_g₃_eq_invariant :
    (rescaledPeriods G τ C).g₃ = W.c₆ / 216 := by
  have h6 : (C.u : ℂ) ^ 6 * (Weierstrass.latticeCurve (periodPair G τ)).c₆ = W.c₆ := by
    rw [← hC, WeierstrassCurve.variableChange_c₆, ← mul_assoc, ← mul_pow]
    simp
  rw [Weierstrass.latticeCurve_c₆] at h6
  rw [rescaledPeriods_g₃]
  apply (eq_div_iff (by norm_num : (216 : ℂ) ≠ 0)).2
  linear_combination h6

end RHLean.Geometry.NativeCM.EllipticSeed

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed TorsionAlgebraicity

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W : WeierstrassCurve (𝓞 M)) (w : 𝓞 M)
    (C : WeierstrassCurve.VariableChange ℂ)
    (hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ))
    (hw : ((w : M) : ℂ) = omega G τ)

include hC in
theorem rescaledPeriods_g₂_mem_field : (rescaledPeriods G τ C).g₂ ∈ M := by
  rw [rescaledPeriods_g₂_eq_invariant G τ C (W.baseChange ℂ) hC,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄]
  change (((W.c₄ : M) : ℂ) / 12) ∈ M
  exact div_mem (W.c₄ : M).property (ofNat_mem M 12)

include hC in
theorem rescaledPeriods_g₃_mem_field : (rescaledPeriods G τ C).g₃ ∈ M := by
  rw [rescaledPeriods_g₃_eq_invariant G τ C (W.baseChange ℂ) hC,
    WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆]
  change (((W.c₆ : M) : ℂ) / 216) ∈ M
  exact div_mem (W.c₆ : M).property (ofNat_mem M 216)

/-- The actual finite kernel coordinates lie in a finite extension of the
same field of definition of W. -/
include hC in
theorem exists_kernel_coordinate_field :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F), M ≤ F ∧
      ∀ z ∉ (rescaledPeriods G τ C).lattice,
        omega G τ * z ∈ (rescaledPeriods G τ C).lattice →
          (rescaledPeriods G τ C).weierstrassP z ∈ F := by
  classical
  let L := rescaledPeriods G τ C
  have h₂ : L.g₂ ∈ M := rescaledPeriods_g₂_mem_field G τ M W C hC
  have h₃ : L.g₃ ∈ M := rescaledPeriods_g₃_mem_field G τ M W C hC
  have hMalg : ∀ z : ℂ, z ∈ M → z ∈ algebraicNumbers := fun z hz =>
    mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (⟨z, hz⟩ : M)).algHom M.val)
  obtain ⟨Q, _, _, r, -, hr₁, -, -, hr₄, hr₅⟩ :=
    exists_representatives (omega_ne_zero G τ) (rescaledPeriods_multiplier G τ C (wK G))
  let ι := {t : Q // t ≠ 0}
  let S : Set ℂ := Set.range (fun t : ι => L.weierstrassP (r t))
  have hS : S.Finite := Set.finite_range _
  have : Finite S := hS.to_subtype
  have hSint : ∀ z ∈ S, IsIntegral ℚ z := by
    rintro z ⟨t, rfl⟩
    have htz : r t ∉ L.lattice := (hr₄ t).not.mpr t.property
    have hct := cm_kernel_period_killed G τ C (r t) (hr₁ t)
    exact (mem_algebraicClosure_iff.mp
      (TorsionAlgebraicity.weierstrassP_mem L (hMalg _ h₂) (hMalg _ h₃)
        (generatorNorm_pos G) htz hct).1).isIntegral
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    IntermediateField.finiteDimensional_adjoin hSint
  let F : IntermediateField ℚ ℂ := M ⊔ IntermediateField.adjoin ℚ S
  have : NumberField F := ⟨⟩
  refine ⟨F, inferInstance, le_sup_left, ?_⟩
  intro z hz hαz
  obtain ⟨t, ht⟩ := hr₅ z hαz
  have ht0 : t ≠ 0 := by
    intro h0
    exact hz (by simpa using add_mem ht ((hr₄ t).mpr h0))
  have hrt : r t ∉ L.lattice := (hr₄ t).not.mpr ht0
  have he : L.weierstrassP z = L.weierstrassP (r t) :=
    (weierstrassP_eq_iff L hz hrt).mpr (.inl ht)
  rw [he]
  exact (le_sup_right : IntermediateField.adjoin ℚ S ≤ F)
    (IntermediateField.subset_adjoin ℚ S ⟨⟨t, ht0⟩, rfl⟩)

/-- The original CM generator has a rational point formula over a proved
number field containing the original field of W. Every scale and degree
factor is retained and the resulting action is matched to the original W. -/
include hw in
theorem exists_finite_field_rational_cm_action :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (A D : ℂ[X]),
      M ≤ F ∧
      (∀ i, A.coeff i ∈ F) ∧ (∀ i, D.coeff i ∈ F) ∧ D.Monic ∧
      A.leadingCoeff = (omega G τ ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = Nat.card (rescaledCMAction G τ C).ker ∧
      D.natDegree + 1 = A.natDegree ∧
      (∀ (x y : ℂ) (h : (latticeCurve (rescaledPeriods G τ C)).toAffine.Nonsingular x y),
        (D.eval x = 0 → rescaledCMAction G τ C (.some x y h) = 0) ∧
        (D.eval x ≠ 0 → ∃ h', rescaledCMAction G τ C (.some x y h) =
          .some (A.eval x / D.eval x)
            ((omega G τ)⁻¹ * ((derivative A * D - A * derivative D).eval x /
              D.eval x ^ 2) * y) h')) ∧
      ∀ P, rescaledEquationPointEquiv G τ C (W.baseChange ℂ) hC
          (rescaledCMAction G τ C P) =
        equationCMAction G τ (W.baseChange ℂ) C hC (wK G)
          (rescaledEquationPointEquiv G τ C (W.baseChange ℂ) hC P) := by
  obtain ⟨F, hF, hMF, hker⟩ := exists_kernel_coordinate_field G τ M W C hC
  let _ : NumberField F := hF
  have hω : omega G τ ∈ F := by
    rw [← hw]
    exact hMF (w : M).property
  obtain ⟨A, D, hA, hD, hm, hlc, hc, hdA, hdD, he⟩ :=
    exists_latticeIsogeny_eq_div (omega_ne_zero G τ)
      (rescaledPeriods_multiplier G τ C (wK G)) F.toSubfield
      (hMF (rescaledPeriods_g₂_mem_field G τ M W C hC))
      (hMF (rescaledPeriods_g₃_mem_field G τ M W C hC)) hω hker
  exact ⟨F, hF, A, D, hMF, hA, hD, hm, hlc, hc, hdA, hdD, he,
    rescaledCMAction_equationCMAction G τ C (W.baseChange ℂ) hC⟩

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassLie

/-- The field, integral group scheme, literal Lie basis and rational CM
point formula are chosen together. The coefficients are taken in a finite
extension of the same original field, without changing W or its scale. -/
theorem exists_integral_seed_with_rational_cm_action
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M)
      (W : WeierstrassCurve (𝓞 M)) (w : 𝓞 M)
      (C : WeierstrassCurve.VariableChange ℂ) (hΔ : W.Δ = 1),
      let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
      (∀ a : E, τ a ∈ M) ∧ ((w : M) : ℂ) = omega G τ ∧
      IsLieBasis ![integralVector W] ∧
      (C.u : ℂ) ^ 12 * (latticeCurve (periodPair G τ)).Δ = 1 ∧
      ∃ hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ),
        (rescaledPeriods G τ C).g₂ = ((W.c₄ : M) : ℂ) / 12 ∧
        (rescaledPeriods G τ C).g₃ = ((W.c₆ : M) : ℂ) / 216 ∧
        ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (A D : ℂ[X]),
          M ≤ F ∧
          (∀ i, A.coeff i ∈ F) ∧ (∀ i, D.coeff i ∈ F) ∧ D.Monic ∧
          A.leadingCoeff = (omega G τ ^ 2)⁻¹ ∧ IsCoprime A D ∧
          A.natDegree = Nat.card (rescaledCMAction G τ C).ker ∧
          D.natDegree + 1 = A.natDegree ∧
          (∀ (x y : ℂ) (h : (latticeCurve (rescaledPeriods G τ C)).toAffine.Nonsingular x y),
            (D.eval x = 0 → rescaledCMAction G τ C (.some x y h) = 0) ∧
            (D.eval x ≠ 0 → ∃ h', rescaledCMAction G τ C (.some x y h) =
              .some (A.eval x / D.eval x)
                ((omega G τ)⁻¹ * ((derivative A * D - A * derivative D).eval x /
                  D.eval x ^ 2) * y) h')) ∧
          ∀ P, rescaledEquationPointEquiv G τ C (W.baseChange ℂ) hC
              (rescaledCMAction G τ C P) =
            equationCMAction G τ (W.baseChange ℂ) C hC (wK G)
              (rescaledEquationPointEquiv G τ C (W.baseChange ℂ) hC P) := by
  obtain ⟨M, hM, W, w, C, hΔ, hhost, hw, -, -, -, -, hLie, -, hu, hC, -, -, -⟩ :=
    exists_integral_group_scheme_seed G τ
  let _ : NumberField M := hM
  let _ : W.IsElliptic := ⟨hΔ.symm ▸ isUnit_one⟩
  refine ⟨M, hM, W, w, C, hΔ, hhost, hw, hLie, hu, hC, ?_, ?_, ?_⟩
  · simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄] using
      rescaledPeriods_g₂_eq_invariant G τ C (W.baseChange ℂ) hC
  · simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₆] using
      rescaledPeriods_g₃_eq_invariant G τ C (W.baseChange ℂ) hC
  · exact exists_finite_field_rational_cm_action G τ M W w C hC hw

end RHLean.Geometry.NativeCM.Weierstrass

end
