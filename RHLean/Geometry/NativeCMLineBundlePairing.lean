import RHLean.Geometry.NativeCMLineBundleCube
import RHLean.Geometry.NativeCMLineBundlePullClass

/-!
# The actual cubical line-bundle pairing

The four-term pairing bundle and eight-term cube use the same original
scheme maps. Their actual chart generators give the bilinear pairing in
the quotient by genuinely trivialized pullbacks. A Rosati isomorphism is
an actual isomorphism of those four-term bundles, and its class-valued
adjoint law is derived by pullback along the pair of test points.

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/ModuliProofs/`
`ExistsPrimitiveNormalisation.lean`, the finite-difference declarations and
`diff₃_ptCls` / `diff₂_ptCls_adj`, together with `lamForm` from
`src/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/`
`ExistsTensorBundle.lean`.

The seed cube and adjoint isomorphisms remain geometric inputs. They are
not replaced by identities of the analytic Gram matrix. The source
archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical BigOperators

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory

namespace PullClasses

section Difference

variable {V U : Type} [CommGroup V] [CommGroup U]

def diff₂ (m : V → U) (x y : V) : U := m (x * y) * (m x)⁻¹ * (m y)⁻¹ * m 1

def diff₃ (m : V → U) (x y z : V) : U :=
  m (x * y * z) * (m (x * y))⁻¹ * (m (x * z))⁻¹ * (m (y * z))⁻¹ *
    m x * m y * m z * (m 1)⁻¹

variable {m : V → U}

theorem diff₂_comm (x y : V) : diff₂ m x y = diff₂ m y x := by
  rw [diff₂, diff₂, mul_comm x, mul_right_comm (m (y * x))]

theorem diff₂_mul_left_eq (x y z : V) :
    diff₂ m (x * y) z = diff₃ m x y z * (diff₂ m x z * diff₂ m y z) := by
  apply Additive.ofMul.injective
  simp only [diff₂, diff₃, ofMul_mul, ofMul_inv]
  abel

theorem diff₂_mul_left (hc : ∀ x y z, diff₃ m x y z = 1) (x y z : V) :
    diff₂ m (x * y) z = diff₂ m x z * diff₂ m y z := by
  rw [diff₂_mul_left_eq, hc, _root_.one_mul]

theorem diff₂_mul_right (hc : ∀ x y z, diff₃ m x y z = 1) (x y z : V) :
    diff₂ m x (y * z) = diff₂ m x y * diff₂ m x z := by
  rw [diff₂_comm, diff₂_mul_left hc, diff₂_comm y, diff₂_comm z]

end Difference

end PullClasses

variable {S : Scheme.{0}} {A G T U V : Over S}

def pairTerm [GrpObj A] (x y : T ⟶ A) : Fin 4 → (T ⟶ A) := ![x * y, x, y, 1]

def pairExponent : Fin 4 → ℤ := ![1, -1, -1, 1]

def pairBundle [GrpObj A] (L : LB A.left) (x y : T ⟶ A) : LB T.left :=
  LB.LinComb L (fun k => (pairTerm x y k).left) pairExponent

/-- Equality of polarization pairings means an actual isomorphism of
the four-term line bundles on the original product of test objects. -/
def LamEq [GrpObj A] [GrpObj G] (L : LB A.left) (f : U ⟶ A) (g : V ⟶ A)
    (M : LB G.left) (f' : U ⟶ G) (g' : V ⟶ G) : Prop :=
  LBIso (pairBundle L (fst U V ≫ f) (snd U V ≫ g))
    (pairBundle M (fst U V ≫ f') (snd U V ≫ g'))

theorem pairTerm_pre [GrpObj A] {T' : Over S} (r : T' ⟶ T)
    (x y : T ⟶ A) (k : Fin 4) :
    r ≫ pairTerm x y k = pairTerm (r ≫ x) (r ≫ y) k := by
  fin_cases k <;> simp [pairTerm, MonObj.comp_mul]

def pairChartPull [GrpObj A] (L : LB A.left) {T' : Over S} (r : T' ⟶ T)
    (x y : T ⟶ A) :
    ChartPull (pairBundle L (r ≫ x) (r ≫ y)) (pairBundle L x y) r.left :=
  chartPullSame L _ _ pairExponent r.left fun k =>
    (congrArg Over.Hom.left (pairTerm_pre r x y k)).symm

namespace PullClasses

variable [GrpObj A] [IsCommMonObj A]

abbrev ptCls (L : LB A.left) (T : Over S) : (T ⟶ A) → PullClass L T.left :=
  fun q => cls L q.left

theorem prod_pair (x y : T ⟶ A) {C : Type} [CommGroup C]
    (h : (T.left ⟶ A.left) → C) :
    ∏ k, h (pairTerm x y k).left ^ pairExponent k =
      diff₂ (fun q : T ⟶ A => h q.left) x y := by
  simp only [pairTerm, pairExponent, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, zpow_neg, zpow_one, _root_.mul_one, diff₂]
  ac_rfl

theorem prod_cube (x y z : T ⟶ A) {C : Type} [CommGroup C]
    (h : (T.left ⟶ A.left) → C) :
    ∏ k, h (cubeTerm x y z k).left ^ cubeExponent k =
      diff₃ (fun q : T ⟶ A => h q.left) x y z := by
  simp only [cubeTerm, cubeExponent, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, zpow_neg, zpow_one, _root_.mul_one, diff₃]
  ac_rfl

theorem diff₃_ptCls {L : LB A.left} (hL : L.IsLB) (hT : HasCubeGenerator A L)
    (x y z : T ⟶ A) : diff₃ (ptCls L T) x y z = 1 :=
  (prod_cube x y z (cls L)).symm.trans ((hasGen_iff hL _ _).1 (hT.at_triple x y z))

theorem diff₂_ptCls_adj {L : LB A.left} (hL : L.IsLB) {f g : A ⟶ A}
    (h : LamEq L f (𝟙 A) L (𝟙 A) g) (x y : T ⟶ A) :
    diff₂ (ptCls L T) (x ≫ f) y = diff₂ (ptCls L T) x (y ≫ g) := by
  have hp := LBIso.chartPull
    (pairChartPull L (lift x y) (fst A A ≫ f) (snd A A ≫ 𝟙 A))
    (pairChartPull L (lift x y) (fst A A ≫ 𝟙 A) (snd A A ≫ g))
    h
  simp only [Category.comp_id, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] at hp
  exact (prod_pair (x ≫ f) y (cls L)).symm.trans
    (((lbIso_iff hL _ _ _ _).1 hp).trans (prod_pair x (y ≫ g) (cls L)))

end PullClasses

namespace CubicalPairing

open SerreScheme PullClasses

variable {O : Type} [CommRing O] [GrpObj G] [IsCommMonObj G]
    {L : LB G.left}

/-- The bilinear form is derived from the genuine seed cube generator. -/
def lamForm (a : OAct O G) (hL : L.IsLB) (hT : HasCubeGenerator G L) (T : Over S) :
    Pts a T →+ Pts a T →+ Additive (PullClass L T.left) :=
  AddMonoidHom.mk' (fun x =>
    AddMonoidHom.mk' (fun y => Additive.ofMul (diff₂ (ptCls L T) (Pts.hom x) (Pts.hom y)))
      (fun y z => congrArg Additive.ofMul
        (diff₂_mul_right (diff₃_ptCls hL hT) (Pts.hom x) (Pts.hom y) (Pts.hom z))))
    (fun x y => AddMonoidHom.ext fun z => congrArg Additive.ofMul
      (diff₂_mul_left (diff₃_ptCls hL hT) (Pts.hom x) (Pts.hom y) (Pts.hom z)))

theorem lamForm_comm (a : OAct O G) (hL : L.IsLB) (hT : HasCubeGenerator G L)
    (T : Over S) (x y : Pts a T) :
    lamForm a hL hT T x y = lamForm a hL hT T y x :=
  congrArg Additive.ofMul (diff₂_comm (Pts.hom x) (Pts.hom y))

theorem lamForm_adj (a : OAct O G) (hL : L.IsLB) (hT : HasCubeGenerator G L)
    (br : O ≃+* O)
    (ha : ∀ c, LamEq L (a.act c) (𝟙 G) L (𝟙 G) (a.act (br c)))
    (T : Over S) (c : O) (x y : Pts a T) :
    lamForm a hL hT T (c • x) y = lamForm a hL hT T x (br c • y) :=
  congrArg Additive.ofMul (diff₂_ptCls_adj hL (ha c) (Pts.hom x) (Pts.hom y))

end CubicalPairing

end RHLean.Geometry.NativeCM.SchemeTheory

end
