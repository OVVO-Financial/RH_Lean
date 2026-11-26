import Mathlib
import RHLean.Geometry.NativeCMWeierstrassAdditionMorphism

/-!
# The actual Weierstrass group scheme over the integral CM base

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/`
`ExistsLiftAddOfIsReducedEq.lean`, through `isCommMonObj_of_isReduced`.
The source archive states no license; attribution is retained without
assigning one.

Only the reduced-base constructor is needed: the actual base O_M is a
Dedekind domain and its complex fibres are fields. The addition morphism
is constructed by gluing the original algebraic addition laws; its group
identities are proved on the actual reduced scheme. No group-law or
polarization existence hypothesis is assumed. The point equivalences below
identify this scheme's group law with Mathlib's existing elliptic points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

noncomputable section

namespace RHLean.Geometry.NativeCM.SchemeTheory

namespace WeierstrassCurve

open AddLaw

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

instance isSeparated_over_hom : IsSeparated (schemeOver W).hom :=
  inferInstanceAs (IsSeparated (toSpec W))

theorem isReduced_pullback_toSpec {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of R)) :
    IsReduced (pullback f (toSpec W)) := by
  have : ∀ i, IsReduced ((X.affineOpenCover.openCover.pullback₁
      (pullback.fst f (toSpec W))).X i) := fun i => by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.affineOpenCover.f i ≫ f)
    have : _root_.IsReduced (X.affineOpenCover.X i) :=
      (affine_isReduced_iff _).mp (@isReduced_of_isOpenImmersion _ _ _
        (X.affineOpenCover.map_prop i) _)
    have h := (IsPullback.of_hasPullback (pullback.fst f (toSpec W))
      (X.affineOpenCover.f i)).paste_horiz (IsPullback.of_hasPullback f (toSpec W)).flip
    rw [← hφ] at h
    have := isReduced_scheme (W.map φ.hom)
    let e : _ ≅ scheme (W.map φ.hom) := h.isoIsPullback _ _ (isPullback_mapHom W φ.hom rfl)
    exact @isReduced_of_isOpenImmersion _ _ e.hom (@IsOpenImmersion.of_isIso _ _ _ e.isIso_hom) _
  exact .of_openCover _ (X.affineOpenCover.openCover.pullback₁ (pullback.fst f (toSpec W)))

instance isReduced_tensor_left (T : Over (Spec (.of R))) [IsReduced T.left] :
    IsReduced (T ⊗ schemeOver W).left :=
  isReduced_pullback_toSpec W T.hom

instance isReduced_over_left [_root_.IsReduced R] : IsReduced (schemeOver W).left :=
  isReduced_scheme W

section Reduced

variable [_root_.IsReduced R] [W.IsElliptic]

def addOfIsReduced : schemeOver W ⊗ schemeOver W ⟶ schemeOver W :=
  (exists_sum W (fst (schemeOver W) (schemeOver W)) (snd _ _)).choose

theorem lift_addOfIsReduced (k : Type u) [Field k] [Algebra R k]
    (a b : specOver R k ⟶ schemeOver W) : lift a b ≫ addOfIsReduced W = fieldAdd W k a b := by
  have h := (exists_sum W (fst (schemeOver W) (schemeOver W)) (snd _ _)).choose_spec k (lift a b)
  rwa [lift_fst, lift_snd] at h

@[instance_reducible]
def grpObjOfIsReduced : GrpObj (schemeOver W) :=
  grpObjOfFieldPoints (zeroUnit W) (addOfIsReduced W) (negOver W) fun k _ _ =>
    ⟨(W.baseChange k).toProjective.Point, inferInstance, projectivePointEquiv W k,
      (toUnit_zeroUnit W k).trans (ofProjectivePoint_zero W k).symm,
      fun a b => by
        rw [lift_addOfIsReduced, fieldAdd, Equiv.symm_apply_apply, Equiv.symm_apply_apply],
      by
        rintro @⟨⟨P⟩, hP⟩
        exact ptOver_negOver W P (.of_nonsingular hP)⟩

theorem isCommMonObj_of_isReduced :
    letI := grpObjOfIsReduced W
    IsCommMonObj (schemeOver W) := by
  let := grpObjOfIsReduced W
  refine ⟨over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => ?_⟩
  rw [← lift_comp_fst_snd x, lift_braiding_hom_assoc]
  change lift _ _ ≫ addOfIsReduced W = lift _ _ ≫ addOfIsReduced W
  rw [lift_addOfIsReduced, lift_addOfIsReduced, fieldAdd, fieldAdd, add_comm]

/-- The actual reduced-base group object; in particular this applies to O_M. -/
instance grpObj : GrpObj (schemeOver W) := grpObjOfIsReduced W

instance isCommMonObj : IsCommMonObj (schemeOver W) :=
  isCommMonObj_of_isReduced W

@[simp] theorem one_left : η[schemeOver W].left = zero W := rfl

@[simp] theorem mul_eq_addOfIsReduced : μ[schemeOver W] = addOfIsReduced W := rfl

variable (k : Type u) [Field k] [Algebra R k]

/-- The scheme addition is the actual projective elliptic-curve addition. -/
theorem ofProjectivePoint_add (p q : (W.baseChange k).toProjective.Point) :
    ofProjectivePoint W k (p + q) = ofProjectivePoint W k p * ofProjectivePoint W k q := by
  rw [Hom.mul_def]
  change ofProjectivePoint W k (p + q) =
    lift (ofProjectivePoint W k p) (ofProjectivePoint W k q) ≫ addOfIsReduced W
  rw [lift_addOfIsReduced, fieldAdd]
  change (projectivePointEquiv W k) (p + q) =
    (projectivePointEquiv W k)
      ((projectivePointEquiv W k).symm ((projectivePointEquiv W k) p) +
        (projectivePointEquiv W k).symm ((projectivePointEquiv W k) q))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

def projectivePointMulEquiv :
    Multiplicative (W.baseChange k).toProjective.Point ≃* (specOver R k ⟶ schemeOver W) where
  toEquiv := Multiplicative.toAdd.trans (projectivePointEquiv W k)
  map_mul' p q := ofProjectivePoint_add W k p.toAdd q.toAdd

variable [DecidableEq k]

/-- The affine point group already used by the CM seed has the same group law. -/
theorem ofAffinePoint_add (p q : (W.baseChange k).toAffine.Point) :
    ofAffinePoint W k (p + q) = ofAffinePoint W k p * ofAffinePoint W k q :=
  (congrArg (ofProjectivePoint W k) (map_add (WeierstrassCurve.Projective.Point.toAffineAddEquiv
    (W.baseChange k).toProjective).symm p q)).trans (ofProjectivePoint_add W k _ _)

def affinePointMulEquiv :
    Multiplicative (W.baseChange k).toAffine.Point ≃* (specOver R k ⟶ schemeOver W) where
  toEquiv := Multiplicative.toAdd.trans (affinePointEquiv W k)
  map_mul' p q := ofAffinePoint_add W k p.toAdd q.toAdd

/-- An additive form of the actual affine/scheme point equivalence. -/
def affinePointAddEquiv :
    (W.baseChange k).toAffine.Point ≃+ Additive (specOver R k ⟶ schemeOver W) where
  toFun p := Additive.ofMul (ofAffinePoint W k p)
  invFun p := (affinePointEquiv W k).symm p.toMul
  left_inv p := (affinePointEquiv W k).symm_apply_apply p
  right_inv p := (affinePointEquiv W k).apply_symm_apply p.toMul
  map_add' p q := ofAffinePoint_add W k p q

end Reduced

end WeierstrassCurve

end RHLean.Geometry.NativeCM.SchemeTheory
