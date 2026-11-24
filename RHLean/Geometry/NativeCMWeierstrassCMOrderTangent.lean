import RHLean.Geometry.NativeCMWeierstrassCMOrderAction
import RHLean.Geometry.NativeCMWeierstrassMorphismTangent

/-!
# Exact Lie action of the constructed finite-field CM order action

The already constructed scheme action, its same rescaled period parameter,
and the regular-section derivative comparison produce the actual order
embedding into the same finite field. Every scalar is proved integral, and
its action on the original epsilon generator is proved as an equality of
scheme morphisms. This supplies the Lie scalar law on the generic fibre.

No extension of the scheme action to the ring of integers is asserted. The
integral order embedding is constructed here; the integral scheme action
still requires the genuine good-reduction extension theorem.

The local derivative proof used here is reconstructed from Levent Alpöge
(with Claude), CocoSgt/riemann-hypothesis-lean@
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdealValDifferentEqOne.lean`.
All joins to the native order and original equation are native derivations.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped Classical

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie
open SchemeTheory.WeierstrassSectionJet SchemeTheory.WeierstrassMorphismTangent
open SerreScheme

section NormalizedExponential

variable {F : Type} [Field F] [Algebra F ℂ]
    (V : _root_.WeierstrassCurve F) (L : PeriodPair)
    (hV : V.baseChange ℂ = latticeCurve L)

def normalizedComparison :
    (1 : _root_.WeierstrassCurve.VariableChange ℂ) •
      (V.baseChange ℂ).baseChange ℂ = latticeCurve L := by
  change (1 : _root_.WeierstrassCurve.VariableChange ℂ) •
    ((V.baseChange ℂ).map (RingHom.id ℂ)) = latticeCurve L
  rw [_root_.WeierstrassCurve.map_id, one_smul]
  exact hV

/-- The normalized uniformization and the previously constructed finite-field
point formula use exactly the same scheme points and lattice parameter. -/
theorem normalized_expPoint (z : ℂ) :
    expPoint L (V.baseChange ℂ) 1 (normalizedComparison V L hV) z ≫
        mapHom V (algebraMap F ℂ) rfl =
      (ofAffinePoint V ℂ ((pointCongr hV).symm (latticePoint L z))).left := by
  rw [expPoint, AllPlaceTangentPeriod.exponential_apply]
  rcases hp : latticePoint L z with _ | ⟨x, y, hx⟩
  · rw [map_zero, map_zero, ofAffinePoint_zero, ofAffinePoint_zero,
      zeroOver_left, zeroOver_left]
    change (Spec.map (𝟙 (CommRingCat.of ℂ)) ≫ zero (V.baseChange ℂ)) ≫
      mapHom V (algebraMap F ℂ) rfl = _
    rw [Spec.map_id, Category.id_comp, zero_mapHom]
  · rw [variableChangePoint_some, pointCongr_symm_some]
    simp only [_root_.WeierstrassCurve.VariableChange.one_def, Units.val_one,
      one_pow, one_mul, mul_zero, add_zero]
    rw [ofAffinePoint_some, ofAffinePoint_some]
    change ptHom (V.baseChange ℂ) (RingHom.id ℂ) ![x, y, 1] _ ≫
      mapHom V (algebraMap F ℂ) rfl = ptHom V (algebraMap F ℂ) ![x, y, 1] _
    exact ptHom_mapHom V (algebraMap F ℂ) rfl (RingHom.id ℂ) ![x, y, 1] _

end NormalizedExponential

section ActualOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    {F : Type} [Field F] [NumberField F] [Algebra F ℂ]
    (V : _root_.WeierstrassCurve F) [V.IsElliptic]
    (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
    (a : OAct (OK G) (schemeOver V))
    (ha : ∀ b : OK G, ∀ z : ℂ,
      ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
          a.act b =
        ofAffinePoint V ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) (embed G τ b * z))))

include ha in
/-- The tangent scalars are forced by the actual morphisms, and form the
original order embedding into the same field. They are all integral. -/
theorem exists_integral_order_tangent :
    ∃ κ : OK G →+* 𝓞 F,
      (∀ b, algebraMap F ℂ (κ b : F) = embed G τ b) ∧
      (∀ b, (integralVector V).left ≫ (a.act b).left = vec V (κ b : F)) ∧
      ∀ b, IsLieComb ![(κ b : F)] ![integralVector V]
        (integralVector V ≫ a.act b) := by
  have ht : ∀ b : OK G, ∃ c : F,
      (integralVector V).left ≫ (a.act b).left = vec V c ∧ algebraMap F ℂ c = embed G τ b := by
    intro b
    let _ : IsMonHom (a.act b) := a.hom b
    apply exists_tangent_scalar V (rescaledPeriods G τ C) 1
      (normalizedComparison V _ hVC) (a.act b) (embed G τ b)
    intro z
    rw [← Category.assoc, normalized_expPoint, normalized_expPoint]
    exact congrArg Over.Hom.left (ha b z)
  choose c hc hσ using ht
  let κ₀ : OK G →+* F :=
    { toFun := c
      map_one' := (algebraMap F ℂ).injective (by simp only [hσ, map_one])
      map_mul' := fun b d => (algebraMap F ℂ).injective (by simp only [map_mul, hσ])
      map_zero' := (algebraMap F ℂ).injective (by simp only [hσ, map_zero])
      map_add' := fun b d => (algebraMap F ℂ).injective (by simp only [map_add, hσ]) }
  have hint (b : OK G) : IsIntegral ℤ (κ₀ b) := by
    have := finite_int_OK G
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) b).map κ₀.toIntAlgHom
  let κ : OK G →+* 𝓞 F :=
    { toFun := fun b => ⟨κ₀ b, hint b⟩
      map_one' := Subtype.ext κ₀.map_one
      map_mul' := fun b d => Subtype.ext (κ₀.map_mul b d)
      map_zero' := Subtype.ext κ₀.map_zero
      map_add' := fun b d => Subtype.ext (κ₀.map_add b d) }
  refine ⟨κ, hσ, hc, fun b => ?_⟩
  refine ⟨fun _ => integralVector V ≫ a.act b, fun i => ?_, by simp⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact (hc b).trans (scale_vec V (κ b : F)).symm

end ActualOrder

/-- One finite-field witness supplies the actual full order action and its
proved Lie scalar law on the normalized original integral equation. -/
theorem exists_cm_scheme_order_action_with_tangent
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W : _root_.WeierstrassCurve (𝓞 M)) [W.IsElliptic] (w : 𝓞 M)
    (hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ))
    (hw : ((w : M) : ℂ) = omega G τ) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
      (V : _root_.WeierstrassCurve F) (_ : V.IsElliptic)
      (hVC : V.baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
      (a : OAct (OK G) (schemeOver V)) (κ : OK G →+* 𝓞 F),
      V = shortModel ((W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom) ∧
      (∀ b : OK G, ∀ z : ℂ,
        ofAffinePoint V ℂ ((pointCongr hVC).symm (latticePoint (rescaledPeriods G τ C) z)) ≫
            a.act b =
          ofAffinePoint V ℂ ((pointCongr hVC).symm
            (latticePoint (rescaledPeriods G τ C) (embed G τ b * z)))) ∧
      (∀ b, algebraMap F ℂ (κ b : F) = embed G τ b) ∧
      (∀ b, (integralVector V).left ≫ (a.act b).left = vec V (κ b : F)) ∧
      ∀ b, IsLieComb ![(κ b : F)] ![integralVector V]
        (integralVector V ≫ a.act b) := by
  obtain ⟨F, hF, hMF, V, hV, hVC, a, hnorm, hpoint⟩ :=
    exists_cm_scheme_order_action G τ C M W w hC hw
  let _ : NumberField F := hF
  let _ : V.IsElliptic := hV
  obtain ⟨κ, hκ, hvec, hlie⟩ := exists_integral_order_tangent G τ C V hVC a hpoint
  exact ⟨F, hF, hMF, V, hV, hVC, a, κ, hnorm, hpoint, hκ, hvec, hlie⟩

end RHLean.Geometry.NativeCM.Weierstrass

end
