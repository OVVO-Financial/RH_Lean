import RHLean.Geometry.NativeCMWeierstrassCMAction

/-!
# The polynomial equation satisfied by the actual rational CM formula

The existing rational point formula determines a literal polynomial identity.
It is proved on the infinitely many values of the actual Weierstrass function,
then descended along an injective coefficient map. This identity is the input
to the scheme morphism on the open set where the denominator is invertible.

The polynomial argument follows Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/HeightProofs/
ExistsWeierstrassPMulOde.lean, `exists_weierstrassP_mul_ode`.
Here it is applied to the already chosen A and D, preserving the actual
finite field, point homomorphism and scale instead of choosing new witnesses.
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Polynomial PeriodPair

namespace RHLean.Geometry.NativeCM.Weierstrass

section Algebra

variable {K : Type*} [Field K]

/-- The exact cleared equation for x ↦ A/D and
y ↦ alpha⁻¹ (A'D-AD') y / D² on a short Weierstrass curve. -/
def RationalIdentity (W : WeierstrassCurve K) (α : K) (A D : K[X]) : Prop :=
  C (α ^ 2) * D * (A ^ 3 + C W.a₄ * A * D ^ 2 + C W.a₆ * D ^ 3) =
    (derivative A * D - A * derivative D) ^ 2 * (X ^ 3 + C W.a₄ * X + C W.a₆)

theorem cubic_identity_of_rational_equation {α a d b x y c₄ c₆ : K}
    (hα : α ≠ 0) (hd : d ≠ 0) (hy : y ^ 2 = x ^ 3 + c₄ * x + c₆)
    (h : (α⁻¹ * (b / d ^ 2) * y) ^ 2 =
      (a / d) ^ 3 + c₄ * (a / d) + c₆) :
    α ^ 2 * d * (a ^ 3 + c₄ * a * d ^ 2 + c₆ * d ^ 3) =
      b ^ 2 * (x ^ 3 + c₄ * x + c₆) := by
  rw [← hy]
  have he := congrArg (fun z : K => α ^ 2 * d ^ 4 * z) h
  field_simp [hα, hd] at he
  linear_combination -he

/-- An injective coefficient map reflects the actual polynomial identity. -/
theorem rationalIdentity_of_map {K' : Type*} [Field K'] (f : K →+* K')
    (W : WeierstrassCurve K) (α : K) (A D : K[X])
    (h : RationalIdentity (W.map f) (f α) (A.map f) (D.map f)) :
    RationalIdentity W α A D := by
  unfold RationalIdentity at h ⊢
  apply Polynomial.map_injective f f.injective
  simpa only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, ← derivative_map,
    map_pow, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using! h

/-- The coefficients already proved to lie in a subfield supply an actual
polynomial over that subfield, with the same degree. -/
theorem exists_polynomial_over_subfield (F : Subfield K) (A : K[X])
    (hA : ∀ i, A.coeff i ∈ F) :
    ∃ A₀ : F[X], A₀.map F.subtype = A ∧ A₀.natDegree = A.natDegree :=
  Polynomial.exists_natDegree_eq_of_mem_lifts
    ((Polynomial.lifts_iff_coeff_lifts A).mpr fun i => ⟨⟨A.coeff i, hA i⟩, rfl⟩)

end Algebra

/-- The exact same A,D occurring in the actual point formula satisfy the
polynomial curve equation; no identity is added as a premise. -/
theorem rationalIdentity_of_point_formula (L : PeriodPair) {α : ℂ}
    (hα : α ≠ 0) (A D : ℂ[X]) (hD : D ≠ 0)
    (f : (latticeCurve L).toAffine.Point → (latticeCurve L).toAffine.Point)
    (hf : ∀ (x y : ℂ) (h : (latticeCurve L).toAffine.Nonsingular x y),
      D.eval x ≠ 0 → ∃ h', f (.some x y h) =
        .some (A.eval x / D.eval x)
          (α⁻¹ * ((derivative A * D - A * derivative D).eval x / D.eval x ^ 2) * y) h') :
    RationalIdentity (latticeCurve L) α A D := by
  unfold RationalIdentity
  apply Polynomial.eq_of_infinite_eval_eq
  have hfin : {x : ℂ | D.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hD
  refine hfin.infinite_compl.mono ?_
  intro x hx
  obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
  have hd : D.eval (L.weierstrassP z) ≠ 0 := hx
  obtain ⟨h', -⟩ := hf _ _ (latticeCurve_nonsingular L hz) hd
  have hy := (latticeCurve_nonsingular L hz).left
  have hy' := h'.left
  rw [WeierstrassCurve.Affine.equation_iff] at hy hy'
  simp only [latticeCurve, zero_mul, add_zero] at hy hy'
  simp only [eval_mul, eval_add, eval_pow, eval_C, eval_X]
  exact cubic_identity_of_rational_equation hα hd hy hy'

end RHLean.Geometry.NativeCM.Weierstrass

end
