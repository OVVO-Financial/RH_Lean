import RHLean.Geometry.NativeCMWeierstrassCMAction

/-!
# The rescaled CM curve and the original equation over the same number field

The actual comparison C sends the integral equation W to its analytic lattice
equation. After rescaling the lattice by u^-1, the remaining coordinate change
has unit one. Its three translations are forced by the coefficients of W:
s = -a1/2, r = -b2/12, and t = (a1*b2 - 12*a3)/24.

Consequently this normalized equation comparison is already defined over the
same number field as W; no algebraicity of the analytic period scale u is
required. The actual rescaled curve is the short equation with coefficients
-c4(W)/48 and -c6(W)/864. The final point comparison is identified with the
original u-dependent uniformization, so it is a usable join for the rational
CM point formula, rather than a second unrelated short equation.

The elementary coordinate calculation uses Mathlib's literal variable-change
formulas and the exact period comparison in `NativeCMWeierstrassCMAction`.
It does not assert that the rational CM point homomorphism has yet been
extended to a morphism of schemes or over the ring of integers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField PeriodPair

namespace RHLean.Geometry.NativeCM.Weierstrass

section Normalization

variable {K : Type*} [Field K] [CharZero K] (W : WeierstrassCurve K)

/-- The unique translation to a short equation with unchanged tangent scale. -/
def shortChange : WeierstrassCurve.VariableChange K :=
  ⟨1, -W.b₂ / 12, -W.a₁ / 2, (W.a₁ * W.b₂ - 12 * W.a₃) / 24⟩

/-- The short equation determined by the actual invariants of W. -/
def shortModel : WeierstrassCurve K :=
  ⟨0, 0, 0, -W.c₄ / 48, -W.c₆ / 864⟩

@[simp] theorem shortChange_u : (shortChange W).u = 1 := rfl

theorem shortChange_spec : shortChange W • W = shortModel W := by
  ext
  · rw [WeierstrassCurve.variableChange_a₁]
    dsimp [shortChange, shortModel]
    ring
  · rw [WeierstrassCurve.variableChange_a₂]
    dsimp [shortChange, shortModel, WeierstrassCurve.b₂]
    ring
  · rw [WeierstrassCurve.variableChange_a₃]
    dsimp [shortChange, shortModel]
    ring
  · rw [WeierstrassCurve.variableChange_a₄]
    dsimp [shortChange, shortModel, WeierstrassCurve.c₄,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  · rw [WeierstrassCurve.variableChange_a₆]
    dsimp [shortChange, shortModel, WeierstrassCurve.c₆,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    ring

variable {K' : Type*} [Field K'] [CharZero K'] (φ : K →+* K')

theorem shortChange_map : (shortChange W).map φ = shortChange (W.map φ) := by
  ext
  · change (Units.map φ (1 : Kˣ) : K') = 1
    exact map_one φ
  · change φ (-W.b₂ / 12) = -(W.map φ).b₂ / 12
    rw [map_div₀, map_neg, map_ofNat, WeierstrassCurve.map_b₂]
  · change φ (-W.a₁ / 2) = -φ W.a₁ / 2
    rw [map_div₀, map_neg, map_ofNat]
  · change φ ((W.a₁ * W.b₂ - 12 * W.a₃) / 24) =
      (φ W.a₁ * (W.map φ).b₂ - 12 * φ W.a₃) / 24
    rw [map_div₀, map_sub, map_mul, map_mul, map_ofNat, map_ofNat,
      WeierstrassCurve.map_b₂]

theorem shortModel_map : (shortModel W).map φ = shortModel (W.map φ) := by
  ext
  · exact map_zero φ
  · exact map_zero φ
  · exact map_zero φ
  · change φ (-W.c₄ / 48) = -(W.map φ).c₄ / 48
    rw [map_div₀, map_neg, map_ofNat, WeierstrassCurve.map_c₄]
  · change φ (-W.c₆ / 864) = -(W.map φ).c₆ / 864
    rw [map_div₀, map_neg, map_ofNat, WeierstrassCurve.map_c₆]

end Normalization

section ActualComparison

variable (W : WeierstrassCurve ℂ) (L : PeriodPair)
    (C : WeierstrassCurve.VariableChange ℂ) (hC : C • W = latticeCurve L)

include hC in
/-- The original comparison translations are forced by the same W. -/
theorem variableChange_translations :
    C.r = (shortChange W).r ∧ C.s = (shortChange W).s ∧
      C.t = (shortChange W).t := by
  have h₁ := congrArg WeierstrassCurve.a₁ hC
  have h₂ := congrArg WeierstrassCurve.a₂ hC
  have h₃ := congrArg WeierstrassCurve.a₃ hC
  change ((C.u⁻¹ : ℂˣ) : ℂ) * (W.a₁ + 2 * C.s) = 0 at h₁
  change ((C.u⁻¹ : ℂˣ) : ℂ) ^ 2 *
    (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) = 0 at h₂
  change ((C.u⁻¹ : ℂˣ) : ℂ) ^ 3 * (W.a₃ + C.r * W.a₁ + 2 * C.t) = 0 at h₃
  have hs₀ := (mul_eq_zero.mp h₁).resolve_left (Units.ne_zero (C.u⁻¹))
  have hr₀ := (mul_eq_zero.mp h₂).resolve_left (pow_ne_zero 2 (Units.ne_zero (C.u⁻¹)))
  have ht₀ := (mul_eq_zero.mp h₃).resolve_left (pow_ne_zero 3 (Units.ne_zero (C.u⁻¹)))
  have hs : C.s = -W.a₁ / 2 := by linear_combination hs₀ / 2
  have hr : C.r = -W.b₂ / 12 := by
    rw [hs] at hr₀
    rw [WeierstrassCurve.b₂]
    linear_combination hr₀ / 3
  have ht : C.t = (W.a₁ * W.b₂ - 12 * W.a₃) / 24 := by
    rw [hr] at ht₀
    linear_combination ht₀ / 2
  exact ⟨hr, hs, ht⟩

end ActualComparison

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM.EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (C : WeierstrassCurve.VariableChange ℂ) (W : WeierstrassCurve ℂ)
    (hC : C • W = Weierstrass.latticeCurve (periodPair G τ))

include hC in
theorem shortModel_eq_rescaled_latticeCurve :
    Weierstrass.shortModel W = Weierstrass.latticeCurve (rescaledPeriods G τ C) := by
  ext
  · rfl
  · rfl
  · rfl
  · change -W.c₄ / 48 = -(rescaledPeriods G τ C).g₂ / 4
    rw [rescaledPeriods_g₂_eq_invariant G τ C W hC]
    ring
  · change -W.c₆ / 864 = -(rescaledPeriods G τ C).g₃ / 4
    rw [rescaledPeriods_g₃_eq_invariant G τ C W hC]
    ring

include hC in
theorem shortChange_eq_rescaled_latticeCurve :
    Weierstrass.shortChange W • W = Weierstrass.latticeCurve (rescaledPeriods G τ C) :=
  (Weierstrass.shortChange_spec W).trans (shortModel_eq_rescaled_latticeCurve G τ C W hC)

/-- The normalized comparison is given by the translation already defined over M. -/
def normalizedEquationPointEquiv :
    (Weierstrass.latticeCurve (rescaledPeriods G τ C)).toAffine.Point ≃+ W.toAffine.Point :=
  Weierstrass.variableChangePointEquiv (Weierstrass.shortChange W)
    (shortChange_eq_rescaled_latticeCurve G τ C W hC)

/-- This finite-field equation comparison is exactly the original analytic one. -/
theorem normalizedEquationPointEquiv_eq :
    normalizedEquationPointEquiv G τ C W hC = rescaledEquationPointEquiv G τ C W hC := by
  apply AddEquiv.ext
  intro P
  obtain ⟨z, rfl⟩ := Weierstrass.latticePoint_surjective (rescaledPeriods G τ C) P
  by_cases hz : z ∈ (rescaledPeriods G τ C).lattice
  · rw [Weierstrass.latticePoint_of_mem _ hz, map_zero, map_zero]
  · have hz' : (C.u : ℂ) * z ∉ (periodPair G τ).lattice :=
      fun h => hz ((rescaledPeriods_mem G τ C z).2 h)
    obtain ⟨hr, hs, ht⟩ := Weierstrass.variableChange_translations W (periodPair G τ) C hC
    rw [rescaledEquationPointEquiv_latticePoint, equationExponential_apply]
    change Weierstrass.variableChangePoint (Weierstrass.shortChange W) _
      (Weierstrass.latticePoint (rescaledPeriods G τ C) z) =
        Weierstrass.variableChangePoint C hC
          (Weierstrass.latticePoint (periodPair G τ) ((C.u : ℂ) * z))
    rw [Weierstrass.latticePoint_of_notMem _ hz, Weierstrass.latticePoint_of_notMem _ hz',
      Weierstrass.variableChangePoint_some, Weierstrass.variableChangePoint_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    simp only [Weierstrass.shortChange_u, Units.val_one, one_pow, one_mul]
    rw [rescaledPeriods_weierstrassP, rescaledPeriods_derivWeierstrassP, ← hr, ← hs, ← ht]
    constructor
    · rfl
    · ring

end RHLean.Geometry.NativeCM.EllipticSeed

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W : WeierstrassCurve (𝓞 M)) (C : WeierstrassCurve.VariableChange ℂ)
    (hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ))

include hC in
/-- The actual rescaled equation is the base change of an equation over M. -/
theorem rescaled_model_defined_over_same_field :
    (shortModel (W.baseChange M)).baseChange ℂ =
      latticeCurve (rescaledPeriods G τ C) := by
  rw [WeierstrassCurve.baseChange, shortModel_map]
  change shortModel (W.baseChange ℂ) = _
  exact shortModel_eq_rescaled_latticeCurve G τ C (W.baseChange ℂ) hC

include hC in
/-- Its equation isomorphism back to W is also defined over M, with unit one. -/
theorem normalized_change_defined_over_same_field :
    (shortChange (W.baseChange M)).u = 1 ∧
      ((shortChange (W.baseChange M)).map (M.val : M →+* ℂ)).r = C.r ∧
      ((shortChange (W.baseChange M)).map (M.val : M →+* ℂ)).s = C.s ∧
      ((shortChange (W.baseChange M)).map (M.val : M →+* ℂ)).t = C.t ∧
      (((shortChange (W.baseChange M)).map (M.val : M →+* ℂ)) • W.baseChange ℂ) =
        latticeCurve (rescaledPeriods G τ C) := by
  have he : (shortChange (W.baseChange M)).map (M.val : M →+* ℂ) =
      shortChange (W.baseChange ℂ) := shortChange_map _ _
  obtain ⟨hr, hs, ht⟩ := variableChange_translations (W.baseChange ℂ) (periodPair G τ) C hC
  rw [he]
  exact ⟨rfl, hr.symm, hs.symm, ht.symm,
    shortChange_eq_rescaled_latticeCurve G τ C (W.baseChange ℂ) hC⟩

end RHLean.Geometry.NativeCM.Weierstrass

end
