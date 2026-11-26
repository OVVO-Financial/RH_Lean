import RHLean.Geometry.NativeCMWeierstrassSchemePointExt

/-!
# Base change of the actual Weierstrass affine-point morphism

This elementary functoriality lemma is independent of the finite-closed-set
and small-torsion theorems used later in the good-reduction extension.
It is relocated from NativeCMWeierstrassRelativePoints so both that
geometric-kernel consumer and the CM tangent comparison use one proof on
the original equation, without making the tangent construction import
the entire finite-subgroup argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)
  (k : Type) [Field k] [Algebra R k]

/-- Compare the same homogeneous triple using the already proved
functoriality of ptHom, before reducing any projective point definition. -/
private theorem ptOver_baseChange_left (P : Fin 3 → k)
    (hP : IsUnimodularSol ((W.baseChange k).baseChange k) P)
    (hQ : IsUnimodularSol (W.baseChange k) P) :
    (ptOver W P hQ).left =
      (ptOver (W.baseChange k) P hP).left ≫ mapHom W (algebraMap R k) rfl := by
  let U := W.baseChange k
  have hU : W.map (algebraMap R k) = U := rfl
  have hρ : (algebraMap k k).comp (algebraMap R k) = algebraMap R k :=
    RingHom.ext fun _ => rfl
  have hP' : IsUnimodularSol (U.map (algebraMap k k)) P := hP.of_baseChange
  have hQ' : IsUnimodularSol (W.map (algebraMap R k)) P := hQ.of_baseChange
  have hcomp := ptHom_mapHom W (algebraMap R k) hU (algebraMap k k) P hP'
  have heq := ptHom_congr W ((algebraMap k k).comp (algebraMap R k)) P
    (hP'.comp_of_map_eq hU) hρ rfl hQ'
  exact (hcomp.trans heq).symm

theorem ofAffinePoint_baseChange_left (P : (W.baseChange k).toAffine.Point) :
    (ofAffinePoint W k P).left = (ofAffinePoint (W.baseChange k) k P).left ≫
      mapHom W (algebraMap R k) rfl := by
  cases P with
  | zero =>
    change (ofAffinePoint W k (0 : (W.baseChange k).toAffine.Point)).left =
      (ofAffinePoint (W.baseChange k) k 0).left ≫ mapHom W (algebraMap R k) rfl
    simp only [ofAffinePoint_zero, zeroOver_eq_ptOver]
    exact ptOver_baseChange_left W k _ _ _
  | some x y h =>
    simp only [ofAffinePoint_some]
    exact ptOver_baseChange_left W k _ _ _

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

end
