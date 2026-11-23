import RHLean.Geometry.NativeCMWeierstrassSmallTorsion

/-!
# The actual geometric-fibre points of the integral equation

The equivalence below uses the already constructed affine point groups
and the actual projective base-change morphism. Its underlying point map
is proved to be composition with that morphism. This permits the finite
elliptic-subgroup theorem to apply to a geometric fibre of the same
integral equation, without a group-pullback or model-identification
hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped Classical

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)
  (k : Type) [Field k] [Algebra R k]

theorem ofAffinePoint_baseChange_left (P : (W.baseChange k).toAffine.Point) :
    (ofAffinePoint W k P).left = (ofAffinePoint (W.baseChange k) k P).left ≫
      mapHom W (algebraMap R k) rfl := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [ofAffinePoint_zero, ofAffinePoint_zero, zeroOver_eq_ptOver, zeroOver_eq_ptOver]
    change ptHom W (algebraMap R k) ![0, 1, 0] _ =
      ptHom (W.baseChange k) (RingHom.id k) ![0, 1, 0] _ ≫
        mapHom W (algebraMap R k) rfl
    rw [ptHom_mapHom]
    rfl
  · change ptHom W (algebraMap R k) ![x, y, 1] _ =
      ptHom (W.baseChange k) (RingHom.id k) ![x, y, 1] _ ≫
        mapHom W (algebraMap R k) rfl
    rw [ptHom_mapHom]
    rfl

variable [_root_.IsReduced R] [W.IsElliptic]

/-- Actual geometric-fibre points and actual relative field points have
the same group law. -/
def relativePointMulEquiv :
    (𝟙_ (Over (Sp k)) ⟶ schemeOver (W.baseChange k)) ≃*
      (specOver R k ⟶ schemeOver W) :=
  ((affinePointMulEquiv (W.baseChange k) k).trans
    (selfSpecPointMulEquiv (W.baseChange k))).symm.trans (affinePointMulEquiv W k)

/-- The group equivalence is the actual scheme base-change map. -/
theorem relativePointMulEquiv_left (x : 𝟙_ (Over (Sp k)) ⟶ schemeOver (W.baseChange k)) :
    (relativePointMulEquiv W k x).left = x.left ≫ mapHom W (algebraMap R k) rfl := by
  let e := (affinePointMulEquiv (W.baseChange k) k).trans
    (selfSpecPointMulEquiv (W.baseChange k))
  obtain ⟨P, rfl⟩ := e.surjective x
  change ((affinePointMulEquiv W k) (e.symm (e P))).left =
    (ofAffinePoint (W.baseChange k) k P.toAdd).left ≫ mapHom W (algebraMap R k) rfl
  rw [e.symm_apply_apply]
  exact ofAffinePoint_baseChange_left W k P.toAdd

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

end
