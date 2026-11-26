import RHLean.Geometry.NativeCMWeierstrassSmallTorsion
import RHLean.Geometry.NativeCMWeierstrassPointBaseChange

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
open scoped Classical CategoryTheory.MonObj

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)
  (k : Type) [Field k] [Algebra R k]

variable [_root_.IsReduced R] [W.IsElliptic]

/-- Actual geometric-fibre points and actual relative field points have
the same group law. -/
def relativePointMulEquiv :
    (𝟙_ (Over (Spec (.of k))) ⟶ schemeOver (W.baseChange k)) ≃*
      (specOver R k ⟶ schemeOver W) :=
  ((affinePointMulEquiv (W.baseChange k) k).trans
    (selfSpecPointMulEquiv (W.baseChange k))).symm.trans (affinePointMulEquiv W k)

/-- The group equivalence is the actual scheme base-change map. -/
theorem relativePointMulEquiv_left (x : 𝟙_ (Over (Spec (.of k))) ⟶ schemeOver (W.baseChange k)) :
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
