import RHLean.Geometry.NativeCMWeierstrassRationalSchemeOpen

/-!
# The denominator-open scheme map for the same integral CM seed

The finite coefficient field and A,D are supplied by the actual CM lattice.
The short equation is the base change of the normalized original W; its
complex fibre is identified with the actual u⁻¹-scaled period lattice.
The chosen polynomials are descended to that finite field, their differential
identity is proved, and the literal localized scheme map is therefore defined
over that field. The original CM action formula is retained for these same
polynomials, including its kernel, degree and alpha⁻² leading coefficient.

No global scheme endomorphism or integral CM action is claimed by this file:
the open where D(x) vanishes and the origin still require extension patches.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Polynomial AlgebraicGeometry CategoryTheory

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed SchemeTheory
open SchemeTheory.WeierstrassCurve

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W : _root_.WeierstrassCurve (𝓞 M)) [W.IsElliptic] (w : 𝓞 M)
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ))
    (hw : ((w : M) : ℂ) = omega G τ)

include hC hw in
/-- The actual finite-field localized map, with its exact original CM point
formula, is constructed from the same W and the same analytic scale C.u. -/
theorem exists_cm_rational_scheme_open :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
      (V : _root_.WeierstrassCurve F) (α : F) (A D : F[X]) (hα : α ≠ 0)
      (hshort : V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0)
      (hID : RationalIdentity V α A D),
      V = shortModel ((W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom) ∧
      V.IsElliptic ∧ V.map (F.val : F →+* ℂ) = latticeCurve (rescaledPeriods G τ C) ∧
      (α : ℂ) = omega G τ ∧ D.Monic ∧
      (A.map (F.val : F →+* ℂ)).leadingCoeff = (omega G τ ^ 2)⁻¹ ∧
      IsCoprime (A.map (F.val : F →+* ℂ)) (D.map (F.val : F →+* ℂ)) ∧
      A.natDegree = Nat.card (rescaledCMAction G τ C).ker ∧
      D.natDegree + 1 = A.natDegree ∧
      IsOpenImmersion (rationalOpenIncl V D).left ∧
      (rationalOpenHom V α hα A D hshort hID).left ≫ toSpec V =
        Spec.map (CommRingCat.ofHom (algebraMap F (RationalOpenRing V D))) ∧
      ∀ (x y : ℂ) (h : (latticeCurve (rescaledPeriods G τ C)).toAffine.Nonsingular x y),
        ((D.map (F.val : F →+* ℂ)).eval x = 0 →
          rescaledCMAction G τ C (.some x y h) = 0) ∧
        ((D.map (F.val : F →+* ℂ)).eval x ≠ 0 →
          ∃ h', rescaledCMAction G τ C (.some x y h) =
            .some ((A.map (F.val : F →+* ℂ)).eval x / (D.map (F.val : F →+* ℂ)).eval x)
              ((omega G τ)⁻¹ *
                (((derivative A * D - A * derivative D).map (F.val : F →+* ℂ)).eval x /
                  (D.map (F.val : F →+* ℂ)).eval x ^ 2) * y) h') := by
  obtain ⟨F, hF, A', D', hMF, hA', hD', hm, hlc, hc, hdA, hdD, he, -⟩ :=
    exists_finite_field_rational_cm_action G τ M W w C hC hw
  let _ : NumberField F := hF
  obtain ⟨A, hAsub, hdegA⟩ := exists_polynomial_over_subfield F.toSubfield A' hA'
  obtain ⟨D, hDsub, hdegD⟩ := exists_polynomial_over_subfield F.toSubfield D' hD'
  have hA : A.map (F.val : F →+* ℂ) = A' := hAsub
  have hD : D.map (F.val : F →+* ℂ) = D' := hDsub
  have hω : omega G τ ∈ F := by
    rw [← hw]
    exact hMF (w : M).property
  let α : F := ⟨omega G τ, hω⟩
  have hα : α ≠ 0 := fun h => omega_ne_zero G τ (congrArg Subtype.val h)
  let V : _root_.WeierstrassCurve F :=
    shortModel ((W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom)
  have hV : V.IsElliptic := by
    dsimp [V]
    rw [← shortChange_spec]
    infer_instance
  have hVC : V.map (F.val : F →+* ℂ) = latticeCurve (rescaledPeriods G τ C) := by
    dsimp [V]
    rw [shortModel_map, _root_.WeierstrassCurve.map_map]
    change shortModel (W.baseChange ℂ) = _
    exact shortModel_eq_rescaled_latticeCurve G τ C (W.baseChange ℂ) hC
  have hshort : V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0 := ⟨rfl, rfl, rfl⟩
  have hID : RationalIdentity V α A D := by
    apply rationalIdentity_of_map (F.val : F →+* ℂ)
    rw [hVC, hA, hD]
    exact rationalIdentity_of_point_formula (rescaledPeriods G τ C) (omega_ne_zero G τ)
      A' D' hm.ne_zero (rescaledCMAction G τ C) fun x y h hd => (he x y h).2 hd
  have hmD : D.Monic := by
    apply Polynomial.monic_of_injective (F.val : F →+* ℂ).injective
    rwa [hD]
  refine ⟨F, hF, hMF, V, α, A, D, hα, hshort, hID, rfl, hV, hVC, rfl, hmD,
    ?_, ?_, hdegA.trans hdA, ?_, inferInstance, Over.w _, ?_⟩
  · rwa [hA]
  · rwa [hA, hD]
  · rw [hdegD, hdegA]
    exact hdD
  · intro x y h
    simpa only [Polynomial.map_sub, Polynomial.map_mul, ← derivative_map, hA, hD] using! he x y h

end RHLean.Geometry.NativeCM.Weierstrass

end
