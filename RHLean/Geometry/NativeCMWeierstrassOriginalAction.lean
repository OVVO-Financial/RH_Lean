import RHLean.Geometry.NativeCMWeierstrassTranslationGroup
import RHLean.Geometry.NativeCMWeierstrassCMOrderTangent

/-!
# The constructed generic CM action on the original integral equation

The genuine finite-field action on the short model is conjugated by the
explicit triangular scheme isomorphism to the original equation. This is
an actual action by scheme morphisms on the same W_F. The original
epsilon vector is preserved, so its scalar remains the same integral
embedding of the literal quadratic order. The point formula retains the
original z parameter and the actual u^-1 rescaling.

This is a native same-witness derivation from the proved scheme, point and
regular-section constructors. It does not invoke an extension theorem or
assert that these generic morphisms extend over O_F. That extension remains
the next geometric step; the model and its tangent vector are now the
ones to which that extension must apply.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open NumberField AlgebraicGeometry CategoryTheory MonoidalCategory MonObj
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SerreScheme

variable {S : Scheme.{0}} {O : Type} [CommRing O]
    {A B : Over S} [GrpObj A] [GrpObj B]

/-- Conjugation by an actual group-scheme isomorphism preserves all scalar
laws as equalities of actual morphisms. -/
def OAct.transport (a : OAct O A) (e : A ≅ B) [IsMonHom e.hom] : OAct O B where
  act c := e.inv ≫ a.act c ≫ e.hom
  hom c := by
    have := a.hom c
    infer_instance
  one := by simp only [a.one, Category.id_comp, e.inv_hom_id]
  mul c d := by simp only [a.mul, Category.assoc, Iso.hom_inv_id_assoc]
  add c d := by
    simp only [a.add, MonObj.comp_mul, MonObj.mul_comp, Category.assoc]

theorem OAct.transport_intertwine (a : OAct O A) (e : A ≅ B) [IsMonHom e.hom]
    (c : O) : e.hom ≫ (a.transport e).act c = a.act c ≫ e.hom := by
  simp only [OAct.transport, Iso.hom_inv_id_assoc]

end RHLean.Geometry.NativeCM.SerreScheme

namespace RHLean.Geometry.NativeCM.Weierstrass

open EllipticSeed SchemeTheory SchemeTheory.WeierstrassCurve SchemeTheory.WeierstrassLie
open SerreScheme

section OriginalModel

variable {F : Type} [Field F] [CharZero F] (W : _root_.WeierstrassCurve F) [W.IsElliptic]
    {O : Type} [CommRing O] (a : OAct O (schemeOver (shortModel W)))

/-- The action on the original W_F, using the actual equation isomorphism. -/
def originalOrderAction : OAct O (schemeOver W) := a.transport (shortModelSchemeIso W)

theorem originalOrderAction_vector (κ : O →+* F)
    (ha : ∀ b, (integralVector (shortModel W)).left ≫ (a.act b).left =
      vec (shortModel W) (κ b)) (b : O) :
    (integralVector W).left ≫ ((originalOrderAction W a).act b).left = vec W (κ b) := by
  change vec W 1 ≫ (shortModelSchemeIso W).inv.left ≫
    (a.act b).left ≫ (shortModelSchemeIso W).hom.left = vec W (κ b)
  rw [← Category.assoc, vec_shortModelSchemeIso_inv,
    ← Category.assoc, ha, vec_shortModelSchemeIso]

theorem originalOrderAction_lieComb (κ : O →+* F)
    (ha : ∀ b, (integralVector (shortModel W)).left ≫ (a.act b).left =
      vec (shortModel W) (κ b)) (b : O) :
    IsLieComb ![κ b] ![integralVector W]
      (integralVector W ≫ (originalOrderAction W a).act b) := by
  refine ⟨fun _ => integralVector W ≫ (originalOrderAction W a).act b,
    fun i => ?_, by simp⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact (originalOrderAction_vector W a κ ha b).trans (scale_vec W (κ b)).symm

end OriginalModel

section Periods

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    {F : Type} [Field F] [CharZero F] [Algebra F ℂ]
    (W : _root_.WeierstrassCurve F)
    (hVC : (shortModel W).baseChange ℂ = latticeCurve (rescaledPeriods G τ C))

/-- This is an actual point of the original W_F. Its parameter is the
original z; the normalized lattice point has parameter u^-1 z. -/
def originalPeriodPoint (z : ℂ) : specOver F ℂ ⟶ schemeOver W :=
  ofAffinePoint (shortModel W) ℂ ((pointCongr hVC).symm
    (latticePoint (rescaledPeriods G τ C) ((C.u : ℂ)⁻¹ * z))) ≫
      (shortModelSchemeIso W).hom

variable [W.IsElliptic] (a : OAct (OK G) (schemeOver (shortModel W)))
    (ha : ∀ b : OK G, ∀ z : ℂ,
      ofAffinePoint (shortModel W) ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) z)) ≫ a.act b =
        ofAffinePoint (shortModel W) ℂ ((pointCongr hVC).symm
          (latticePoint (rescaledPeriods G τ C) (embed G τ b * z))))

/-- The original period parameter has the exact original scalar action. -/
include ha in
theorem originalOrderAction_period (b : OK G) (z : ℂ) :
    originalPeriodPoint G τ C W hVC z ≫ (originalOrderAction W a).act b =
      originalPeriodPoint G τ C W hVC (embed G τ b * z) := by
  change (_ ≫ (shortModelSchemeIso W).hom) ≫
    (a.transport (shortModelSchemeIso W)).act b = _
  rw [Category.assoc, OAct.transport_intertwine, ← Category.assoc, ha]
  have hz : embed G τ b * ((C.u : ℂ)⁻¹ * z) =
      (C.u : ℂ)⁻¹ * (embed G τ b * z) := by ring
  rw [hz]
  rfl

end Periods

/-- One actual finite extension supplies the complete quadratic-order
action on the original W_F, its integral tangent scalars, and the original
period formula. The scheme action is still a generic-fibre statement. -/
theorem exists_original_cm_scheme_action
    {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W : _root_.WeierstrassCurve (𝓞 M)) [W.IsElliptic] (w : 𝓞 M)
    (hC : C • W.baseChange ℂ = latticeCurve (periodPair G τ))
    (hw : ((w : M) : ℂ) = omega G τ) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F),
      let U := (W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom
      ∃ (hVC : (shortModel U).baseChange ℂ = latticeCurve (rescaledPeriods G τ C))
        (a : OAct (OK G) (schemeOver U)) (κ : OK G →+* 𝓞 F),
        (∀ b, algebraMap F ℂ (κ b : F) = embed G τ b) ∧
        (∀ b, (integralVector U).left ≫ (a.act b).left = vec U (κ b : F)) ∧
        (∀ b, IsLieComb ![(κ b : F)] ![integralVector U] (integralVector U ≫ a.act b)) ∧
        ∀ b z, originalPeriodPoint G τ C U hVC z ≫ a.act b =
          originalPeriodPoint G τ C U hVC (embed G τ b * z) := by
  obtain ⟨F, hF, hMF, V, hV, hVC, a, κ, hnorm, hpoint, hκ, hvec, -⟩ :=
    exists_cm_scheme_order_action_with_tangent G τ C M W w hC hw
  let _ : NumberField F := hF
  subst V
  let U := (W.baseChange M).map (IntermediateField.inclusion hMF).toRingHom
  let κ₀ : OK G →+* F := (algebraMap (𝓞 F) F).comp κ
  refine ⟨F, hF, hMF, hVC, originalOrderAction U a, κ, hκ, ?_, ?_, ?_⟩
  · exact originalOrderAction_vector U a κ₀ hvec
  · exact originalOrderAction_lieComb U a κ₀ hvec
  · exact originalOrderAction_period G τ C U hVC a hpoint

end RHLean.Geometry.NativeCM.Weierstrass

end
