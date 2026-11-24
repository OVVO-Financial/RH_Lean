import RHLean.Geometry.NativeCMWeierstrassRationalGlobal

/-!
# The actual CM generator as a morphism over a number field

The coefficient field of the already constructed rational CM formula is
enlarged by one algebraic translation point. The two explicit regular patches
then construct a global endomorphism of the normalized original equation.
The morphism is proved to have the actual rescaled CM point action, and its
quadratic relation is an equality of scheme morphisms over that number field.
The original integral equation, its normalization, the alpha factors, kernel
cardinality and nontrivial analytic scale remain the same witnesses.

This is a native continuation of the rational-numerator and torsion suppliers
already attributed in NativeCMWeierstrassCMAction. There is no generic or
integral extension theorem assumed here. Extension over the ring of integers
remains a separate obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField IntermediateField Polynomial AlgebraicGeometry CategoryTheory
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W : _root_.WeierstrassCurve (𝓞 M)) [W.IsElliptic] (w : 𝓞 M)
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ))
    (hw : ((w : M) : ℂ) = omega G τ)

include hC hw in
/-- The actual CM generator extends by two explicit regular formulas to a
global endomorphism over a proved finite extension of the same number field. -/
theorem exists_cm_scheme_generator :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
      (V : _root_.WeierstrassCurve F) (_ : V.IsElliptic)
      (α : F) (A D : F[X]) (hα : α ≠ 0)
      (hshort : V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0)
      (hID : RationalIdentity V α A D)
      (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
      (f : schemeOver V ⟶ schemeOver V),
      V = shortModel ((W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom) ∧
      (α : ℂ) = omega G τ ∧ D.Monic ∧
      (A.map (F.val : F →+* ℂ)).leadingCoeff = (omega G τ ^ 2)⁻¹ ∧
      IsCoprime (A.map (F.val : F →+* ℂ)) (D.map (F.val : F →+* ℂ)) ∧
      A.natDegree = Nat.card (rescaledCMAction G τ C).ker ∧
      D.natDegree + 1 = A.natDegree ∧ IsMonHom f ∧
      rationalOpenIncl V D ≫ f = rationalOpenHom V α hα A D hshort hID ∧
      (∀ P : (latticeCurve (rescaledPeriods G τ C)).toAffine.Point,
        ofAffinePoint V ℂ ((pointCongr hVC).symm P) ≫ f =
          ofAffinePoint V ℂ ((pointCongr hVC).symm (rescaledCMAction G τ C P))) ∧
      (f ≫ f) * (𝟙 (schemeOver V)) ^ generatorNorm G = f := by
  classical
  obtain ⟨F₀, hF₀, hMF₀, V₀, α₀, A₀, D₀, hα₀, hshort₀, hID₀,
    hV₀, hVe₀, hVC₀, hω₀, hm₀, hlc₀, hcp₀, hdA₀, hdD₀, -, -, he₀⟩ :=
    exists_cm_rational_scheme_open G τ M W w C hC hw
  let _ : NumberField F₀ := hF₀
  let _ : V₀.IsElliptic := hVe₀
  obtain ⟨F, hF, h₀F, x₀, y₀, hxy₀, hDxy₀⟩ :=
    exists_numberField_point_off_denominator F₀ V₀ hshort₀ D₀ hm₀.ne_zero
  let _ : NumberField F := hF
  let i : F₀ →ₐ[ℚ] F := IntermediateField.inclusion h₀F
  let V := V₀.map i.toRingHom
  let α := i α₀
  let A := A₀.map i.toRingHom
  let D := D₀.map i.toRingHom
  have hα : α ≠ 0 := fun h => hα₀ (i.injective (h.trans (map_zero i).symm))
  have hshort : V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0 := by
    simp only [V, _root_.WeierstrassCurve.map_a₁, _root_.WeierstrassCurve.map_a₂,
      _root_.WeierstrassCurve.map_a₃, hshort₀.1, hshort₀.2.1, hshort₀.2.2, map_zero,
      and_self]
  have hID : RationalIdentity V α A D := hID₀.map i.toRingHom
  have hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C) := by
    change (V₀.map i.toRingHom).map (F.val : F →+* ℂ) = _
    rw [_root_.WeierstrassCurve.map_map]
    exact hVC₀
  have hω : (α : ℂ) = omega G τ := hω₀
  have hA : A.map (F.val : F →+* ℂ) = A₀.map (F₀.val : F₀ →+* ℂ) := by
    change (A₀.map i.toRingHom).map (F.val : F →+* ℂ) = _
    rw [Polynomial.map_map]
    rfl
  have hD : D.map (F.val : F →+* ℂ) = D₀.map (F₀.val : F₀ →+* ℂ) := by
    change (D₀.map i.toRingHom).map (F.val : F →+* ℂ) = _
    rw [Polynomial.map_map]
    rfl
  have hB : (derivative A * D - A * derivative D).map (F.val : F →+* ℂ) =
      (derivative A₀ * D₀ - A₀ * derivative D₀).map (F₀.val : F₀ →+* ℂ) := by
    simp only [Polynomial.map_sub, Polynomial.map_mul, ← derivative_map, hA, hD]
  -- Work in the actual normalized point group; transfer coordinate
  -- equalities separately from the dependent nonsingularity witnesses.
  let φ := pointConjugate hVC (rescaledCMAction G τ C)
  have hφeq (P : (V.baseChange ℂ).toAffine.Point) :
      pointCongr hVC (φ P) = rescaledCMAction G τ C (pointCongr hVC P) :=
    pointCongr_pointConjugate hVC (rescaledCMAction G τ C) P
  have hφ : ∀ (x y : ℂ) (h : (V.baseChange ℂ).toAffine.Nonsingular x y),
      (aeval x D = 0 → φ (.some x y h) = 0) ∧
      (aeval x D ≠ 0 → ∃ h', φ (.some x y h) =
        .some (aeval x A / aeval x D)
          ((algebraMap F ℂ α)⁻¹ *
            (aeval x (derivative A * D - A * derivative D) / aeval x D ^ 2) * y) h') := by
    intro x y h
    have hp : (latticeCurve (rescaledPeriods G τ C)).toAffine.Nonsingular x y := hVC ▸ h
    have hd : aeval x D = (D₀.map (F₀.val : F₀ →+* ℂ)).eval x :=
      (show aeval x D = (D.map (F.val : F →+* ℂ)).eval x from
        (Polynomial.eval_map (F.val : F →+* ℂ) x).symm).trans
          (congrArg (fun p : ℂ[X] => p.eval x) hD)
    have ha : aeval x A = (A₀.map (F₀.val : F₀ →+* ℂ)).eval x :=
      (show aeval x A = (A.map (F.val : F →+* ℂ)).eval x from
        (Polynomial.eval_map (F.val : F →+* ℂ) x).symm).trans
          (congrArg (fun p : ℂ[X] => p.eval x) hA)
    have hb : aeval x (derivative A * D - A * derivative D) =
        ((derivative A₀ * D₀ - A₀ * derivative D₀).map (F₀.val : F₀ →+* ℂ)).eval x := by
      change (derivative A * D - A * derivative D).eval₂
        (F.val : F →+* ℂ) x = _
      rw [← Polynomial.eval_map, hB]
    have hαC : algebraMap F ℂ α = omega G τ := hω
    constructor
    · intro hx
      apply (pointCongr hVC).injective
      rw [hφeq, map_zero, pointCongr_some]
      exact (he₀ x y hp).1 (hd ▸ hx)
    · intro hx
      obtain ⟨hp', he⟩ := (he₀ x y hp).2 (hd ▸ hx)
      have hpa : (latticeCurve (rescaledPeriods G τ C)).toAffine.Nonsingular
          (aeval x A / aeval x D)
          ((algebraMap F ℂ α)⁻¹ *
            (aeval x (derivative A * D - A * derivative D) / aeval x D ^ 2) * y) := by
        rw [ha, hd, hb, hαC]
        exact hp'
      refine ⟨hVC.symm ▸ hpa, ?_⟩
      apply (pointCongr hVC).injective
      calc
        _ = rescaledCMAction G τ C (.some x y hp) :=
          (hφeq (.some x y h)).trans (congrArg (rescaledCMAction G τ C)
            (pointCongr_some hVC h))
        _ = .some ((A₀.map (F₀.val : F₀ →+* ℂ)).eval x /
              (D₀.map (F₀.val : F₀ →+* ℂ)).eval x)
            ((omega G τ)⁻¹ *
              (((derivative A₀ * D₀ - A₀ * derivative D₀).map
                (F₀.val : F₀ →+* ℂ)).eval x /
                (D₀.map (F₀.val : F₀ →+* ℂ)).eval x ^ 2) * y) hp' := he
        _ = _ := by
          simp only [pointCongr_some, ha, hd, hb, hαC]
  obtain ⟨f, hf, hopen, hfx⟩ := exists_global_hom_of_rational_point_map V α hα A D
    hshort hID φ hφ x₀ y₀ hxy₀ hDxy₀
  have hpoint : ∀ P : (latticeCurve (rescaledPeriods G τ C)).toAffine.Point,
      ofAffinePoint V ℂ ((pointCongr hVC).symm P) ≫ f =
        ofAffinePoint V ℂ ((pointCongr hVC).symm (rescaledCMAction G τ C P)) := by
    intro P
    rw [hfx]
    change ofAffinePoint V ℂ
      (pointConjugate hVC (rescaledCMAction G τ C) ((pointCongr hVC).symm P)) = _
    rw [pointConjugate_pointCongr_symm]
  have hquad : (f ≫ f) * (𝟙 (schemeOver V)) ^ generatorNorm G = f := by
    -- Supply the actual structural witness before detecting equality
    -- on the normalized point group.
    have : LocallyOfFiniteType (schemeOver V).hom :=
      inferInstanceAs (LocallyOfFiniteType (toSpec V))
    apply GeometricPoints.over_hom_ext_of_embedded_points (K := ℂ)
    intro x
    obtain ⟨P, rfl⟩ := (affinePointEquiv V ℂ).surjective x
    obtain ⟨Q, rfl⟩ := (pointCongr hVC).symm.surjective P
    change ofAffinePoint V ℂ ((pointCongr hVC).symm Q) ≫
      ((f ≫ f) * (𝟙 (schemeOver V)) ^ generatorNorm G) =
      ofAffinePoint V ℂ ((pointCongr hVC).symm Q) ≫ f
    rw [MonObj.comp_mul, ← Category.assoc, hpoint, hpoint,
      MonObj.comp_pow, Category.comp_id, hpoint]
    have hn : ofAffinePoint V ℂ ((pointCongr hVC).symm Q) ^ generatorNorm G =
        ofAffinePoint V ℂ ((pointCongr hVC).symm (generatorNorm G • Q)) := by
      have he : ofAffinePoint V ℂ (generatorNorm G • (pointCongr hVC).symm Q) =
          ofAffinePoint V ℂ ((pointCongr hVC).symm Q) ^ generatorNorm G :=
        (affinePointMulEquiv V ℂ).map_pow
          (Multiplicative.ofAdd ((pointCongr hVC).symm Q)) (generatorNorm G)
      exact he.symm.trans (congrArg (ofAffinePoint V ℂ)
        (map_nsmul (pointCongr hVC).symm Q (generatorNorm G)).symm)
    rw [hn, ← ofAffinePoint_add, ← map_add, rescaledCMAction_quadratic]
  have hV : V = shortModel
      ((W.baseChange M).map (IntermediateField.inclusion (hMF₀.trans h₀F)).toRingHom) := by
    change V₀.map i.toRingHom = _
    rw [hV₀, shortModel_map, _root_.WeierstrassCurve.map_map]
    rfl
  refine ⟨F, hF, hMF₀.trans h₀F, V, inferInstance, α, A, D, hα, hshort, hID,
    hVC, f, hV, hω, hm₀.map i.toRingHom, ?_, ?_, ?_, ?_, hf, hopen, hpoint, hquad⟩
  · rwa [hA]
  · rwa [hA, hD]
  · change (A₀.map i.toRingHom).natDegree = _
    rw [Polynomial.natDegree_map_eq_of_injective i.injective]
    exact hdA₀
  · change (D₀.map i.toRingHom).natDegree + 1 = (A₀.map i.toRingHom).natDegree
    rw [Polynomial.natDegree_map_eq_of_injective i.injective,
      Polynomial.natDegree_map_eq_of_injective i.injective]
    exact hdD₀

end RHLean.Geometry.NativeCM.Weierstrass

end
