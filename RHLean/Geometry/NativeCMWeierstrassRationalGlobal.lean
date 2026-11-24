import RHLean.Geometry.NativeCMWeierstrassOpenPoint
import RHLean.Geometry.NativeCMWeierstrassGeometricGlue

/-!
# From the actual rational point formula to a global scheme homomorphism

The localization map is extended across its finite kernel by the explicit
translated patch. Both the geometric kernel test and the value of the local
map are proved from the rational point formula. An actual section outside
the denominator is the only translation datum. The resulting morphism is
proved to preserve the group law by reduced geometric-point detection.

This is a native construction from the preceding explicit rational-map,
localization and two-patch lemmas. No global rational-map extension theorem,
scheme CM-action premise or integral extension premise occurs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

universe u

variable {F k : Type u} [Field F] [Field k] [Algebra F k]
    (W : _root_.WeierstrassCurve F) [W.IsElliptic]

private def multiplicativeHom {P Q : Type u} [AddMonoid P] [AddMonoid Q]
    (φ : P →+ Q) : Multiplicative P →* Multiplicative Q where
  toFun x := Multiplicative.ofAdd (φ x.toAdd)
  map_one' := φ.map_zero
  map_mul' x y := φ.map_add x.toAdd y.toAdd

variable [DecidableEq k]

/-- The same point action expressed on the actual scheme-valued points. -/
def schemePointAction (φ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point) :
    (specOver F k ⟶ schemeOver W) →* (specOver F k ⟶ schemeOver W) :=
  (affinePointMulEquiv W k).toMonoidHom.comp
    ((multiplicativeHom φ).comp (affinePointMulEquiv W k).symm.toMonoidHom)

theorem schemePointAction_ofAffinePoint
    (φ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point)
    (P : (W.baseChange k).toAffine.Point) :
    schemePointAction W φ (ofAffinePoint W k P) = ofAffinePoint W k (φ P) := by
  change (affinePointMulEquiv W k)
    (Multiplicative.ofAdd (φ ((affinePointMulEquiv W k).symm
      ((affinePointMulEquiv W k) (Multiplicative.ofAdd P))).toAdd)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

variable [IsAlgClosed k]

/-- An actual rational point homomorphism, its original formula, and one
point in the denominator open construct a global group-scheme morphism. -/
theorem exists_global_hom_of_rational_point_map
    (α : F) (hα : α ≠ 0) (A D : F[X])
    (hshort : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (hID : Weierstrass.RationalIdentity W α A D)
    (φ : (W.baseChange k).toAffine.Point →+ (W.baseChange k).toAffine.Point)
    (hφ : ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y),
      (aeval x D = 0 → φ (.some x y h) = 0) ∧
      (aeval x D ≠ 0 → ∃ h', φ (.some x y h) =
        .some (aeval x A / aeval x D)
          ((algebraMap F k α)⁻¹ *
            (aeval x (derivative A * D - A * derivative D) / aeval x D ^ 2) * y) h'))
    (x₀ y₀ : F) (h₀ : W.toAffine.Equation x₀ y₀) (hD₀ : D.eval x₀ ≠ 0) :
    ∃ f : schemeOver W ⟶ schemeOver W,
      IsMonHom f ∧ rationalOpenIncl W D ≫ f = rationalOpenHom W α hα A D hshort hID ∧
      ∀ P : (W.baseChange k).toAffine.Point,
        ofAffinePoint W k P ≫ f = ofAffinePoint W k (φ P) := by
  classical
  let Φ := schemePointAction W φ
  have hzero : ofAffinePoint W k (0 : (W.baseChange k).toAffine.Point) = 1 :=
    (affinePointMulEquiv W k).map_one
  have hU : ∀ x : specOver F k ⟶ schemeOver W,
      Φ x ≠ 1 ↔ ∃ z : specOver F k ⟶ specOver F (RationalOpenRing W D),
        z ≫ rationalOpenIncl W D = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨P, rfl⟩ := (affinePointEquiv W k).surjective x
      change schemePointAction W φ (ofAffinePoint W k P) ≠ 1 at hx
      rw [schemePointAction_ofAffinePoint] at hx
      cases P with
      | zero =>
          have hz : φ (0 : (W.baseChange k).toAffine.Point) = 0 := map_zero φ
          exact (hx ((congrArg (ofAffinePoint _ k) hz).trans hzero)).elim
      | some x y h =>
        have hd : aeval x D ≠ 0 := fun hd => hx (by rw [(hφ x y h).1 hd, hzero])
        exact ⟨specOverMap (rationalOpenPoint W D x y h.left hd),
          rationalOpenPoint_incl W D x y h.left hd h⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨g, rfl⟩ := exists_eq_specOverMap z
      obtain ⟨hx, hy, hinc, -⟩ :=
        rationalOpenHom_fieldPoint W α hα A D hshort hID g
      change schemePointAction W φ _ ≠ 1
      rw [hinc, schemePointAction_ofAffinePoint]
      obtain ⟨h', he⟩ := (hφ _ _ hx).2 (rationalOpen_map_denominator W D g).1
      intro hh
      have hh' : φ (.some _ _ hx) = 0 :=
        (affinePointEquiv W k).injective (hh.trans hzero.symm)
      rw [he] at hh'
      cases hh'
  have hfU : ∀ z : specOver F k ⟶ specOver F (RationalOpenRing W D),
      z ≫ rationalOpenHom W α hα A D hshort hID = Φ (z ≫ rationalOpenIncl W D) := by
    intro z
    obtain ⟨g, rfl⟩ := exists_eq_specOverMap z
    obtain ⟨hx, hy, hinc, hmap⟩ :=
      rationalOpenHom_fieldPoint W α hα A D hshort hID g
    change _ = schemePointAction W φ _
    rw [hinc, schemePointAction_ofAffinePoint, hmap]
    obtain ⟨h', he⟩ := (hφ _ _ hx).2 (rationalOpen_map_denominator W D g).1
    rw [he]
  have : LocallyOfFiniteType (schemeOver W).hom :=
    inferInstanceAs (LocallyOfFiniteType (toSpec W))
  obtain ⟨f, hjf, hf⟩ := GeometricPoints.exists_hom_of_kernel_open
    (rationalOpenIncl W D) (rationalOpenHom W α hα A D hshort hID)
    (rationalOpenSection W D x₀ y₀ h₀ hD₀) Φ hU hfU
  refine ⟨f, GeometricPoints.isMonHom_of_embedded_points f Φ hf, hjf, fun P => ?_⟩
  exact (hf (ofAffinePoint W k P)).trans (schemePointAction_ofAffinePoint W φ P)

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

universe v

/-- Package the existing two-patch and point-detection results while the
schemes and all their structural instances are abstract. In the concrete
application below the instances are supplied explicitly. -/
private theorem complete_kernel_open
    {F k : Type v} [Field F] [Field k] [IsAlgClosed k] [Algebra F k]
    {G H : Over (Spec (.of F))} [GrpObj G] [GrpObj H]
    [LocallyOfFiniteType G.hom] [IsReduced G.left] [IsSeparated H.hom]
    [IsReduced (G ⊗ G).left]
    {U : Over (Spec (.of F))} (j : U ⟶ G) [IsOpenImmersion j.left]
    (fU : U ⟶ H) (q : 𝟙_ (Over (Spec (.of F))) ⟶ U)
    (Φ : (specOver F k ⟶ G) →* (specOver F k ⟶ H))
    (hlift : ∀ x, Φ x ≠ 1 → ∃ z : specOver F k ⟶ U, z ≫ j = x)
    (hlocal : ∀ z : specOver F k ⟶ U, Φ (z ≫ j) ≠ 1 ∧ z ≫ fU = Φ (z ≫ j)) :
    ∃ f : G ⟶ H, IsMonHom f ∧ j ≫ f = fU ∧
      ∀ x : specOver F k ⟶ G, x ≫ f = Φ x := by
  have hU (x : specOver F k ⟶ G) :
      Φ x ≠ 1 ↔ ∃ z : specOver F k ⟶ U, z ≫ j = x := by
    refine ⟨hlift x, ?_⟩
    rintro ⟨z, hz⟩ he
    exact (hlocal z).1 ((congrArg Φ hz).trans he)
  obtain ⟨f, hjf, hf⟩ := GeometricPoints.exists_hom_of_kernel_open
    j fU q Φ hU (fun z => (hlocal z).2)
  exact ⟨f, GeometricPoints.isMonHom_of_embedded_points f Φ hf, hjf, hf⟩

variable {F k : Type v} [Field F] [Field k] [Algebra F k]
    (W V : _root_.WeierstrassCurve F) [W.IsElliptic] [V.IsElliptic]
    [DecidableEq k]

/-- The same actual additive map on the distinct scheme point groups. -/
def schemePointActionBetween
    (φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point) :
    (specOver F k ⟶ schemeOver W) →* (specOver F k ⟶ schemeOver V) :=
  (affinePointMulEquiv V k).toMonoidHom.comp
    ((multiplicativeHom φ).comp (affinePointMulEquiv W k).symm.toMonoidHom)

theorem schemePointActionBetween_ofAffinePoint
    (φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point)
    (P : (W.baseChange k).toAffine.Point) :
    schemePointActionBetween W V φ (ofAffinePoint W k P) = ofAffinePoint V k (φ P) := by
  change (affinePointMulEquiv V k)
    (Multiplicative.ofAdd (φ ((affinePointMulEquiv W k).symm
      ((affinePointMulEquiv W k) (Multiplicative.ofAdd P))).toAdd)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

variable [IsAlgClosed k]


omit [W.IsElliptic] [V.IsElliptic] [IsAlgClosed k] in
/-- The nonkernel affine point lifts to the actual denominator open.
Keep this elementary calculation separate from scheme group-law inference. -/
private theorem rationalOpen_lift_between (D : F[X])
    (φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point)
    (hφzero : ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y),
      aeval x D = 0 → φ (.some x y h) = 0)
    (P : (W.baseChange k).toAffine.Point) (hP : φ P ≠ 0) :
    ∃ z : specOver F k ⟶ specOver F (RationalOpenRing W D),
      z ≫ rationalOpenIncl W D = ofAffinePoint W k P := by
  classical
  cases P with
  | zero => exact (hP (map_zero φ)).elim
  | some x y h =>
    have hd : aeval x D ≠ 0 := fun hd => hP (hφzero x y h hd)
    exact ⟨specOverMap (rationalOpenPoint W D x y h.left hd),
      rationalOpenPoint_incl W D x y h.left hd h⟩

omit [IsAlgClosed k] in
/-- At an open-chart point the original rational formula gives the target
value and proves it is nonzero. Separate the two-curve point transport
from the geometric gluing. -/
private theorem rationalOpen_action_between
    (α : F) (hα : α ≠ 0) (A D : F[X])
    (hshort : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (hshortV : V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0)
    (hID : Weierstrass.RationalIdentityBetween W V α A D)
    (φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point)
    (hφsome : ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y),
      aeval x D ≠ 0 → ∃ h', φ (.some x y h) =
        .some (aeval x A / aeval x D)
          ((algebraMap F k α)⁻¹ *
            (aeval x (derivative A * D - A * derivative D) / aeval x D ^ 2) * y) h')
    (g : RationalOpenRing W D →ₐ[F] k) :
    schemePointActionBetween W V φ (specOverMap g ≫ rationalOpenIncl W D) ≠ 1 ∧
      specOverMap g ≫ rationalOpenHomBetween W V α hα A D hshort hshortV hID =
        schemePointActionBetween W V φ (specOverMap g ≫ rationalOpenIncl W D) := by
  classical
  obtain ⟨hx, hy, hinc, hmap⟩ :=
    rationalOpenHomBetween_fieldPoint W V α hα A D hshort hshortV hID g
  obtain ⟨hy', hφval⟩ :=
    hφsome (g (rationalOpenX W D)) (g (rationalOpenY W D)) hx
      (rationalOpen_map_denominator W D g).1
  let P : (W.baseChange k).toAffine.Point :=
    .some (g (rationalOpenX W D)) (g (rationalOpenY W D)) hx
  let Q : (V.baseChange k).toAffine.Point :=
    .some (aeval (g (rationalOpenX W D)) A / aeval (g (rationalOpenX W D)) D)
      ((algebraMap F k α)⁻¹ *
        (aeval (g (rationalOpenX W D)) (derivative A * D - A * derivative D) /
          aeval (g (rationalOpenX W D)) D ^ 2) * g (rationalOpenY W D)) hy
  have hφQ : φ P = Q := hφval
  have hQ : Q ≠ 0 := by
    intro hz
    change _root_.WeierstrassCurve.Affine.Point.some _ _ hy = 0 at hz
    cases hz
  let Φ : (specOver F k ⟶ schemeOver W) →* (specOver F k ⟶ schemeOver V) :=
    schemePointActionBetween W V φ
  have he : Φ (specOverMap g ≫ rationalOpenIncl W D) = ofAffinePoint V k Q :=
    (congrArg Φ (show specOverMap g ≫ rationalOpenIncl W D = ofAffinePoint W k P from hinc)).trans
      ((schemePointActionBetween_ofAffinePoint W V φ P).trans
        (congrArg (ofAffinePoint V k) hφQ))
  have hz : ofAffinePoint V k (0 : (V.baseChange k).toAffine.Point) = 1 :=
    (affinePointMulEquiv V k).map_one
  refine ⟨?_, (show specOverMap g ≫
    rationalOpenHomBetween W V α hα A D hshort hshortV hID =
      ofAffinePoint V k Q from hmap).trans he.symm⟩
  intro hh
  exact hQ ((affinePointEquiv V k).injective (he.symm.trans (hh.trans hz.symm)))

omit [IsAlgClosed k] in
/-- Use the actual point bijection to transport the separately proved
nonkernel affine lift. No scheme-morphism equality is rewritten. -/
private theorem rationalOpen_scheme_lift_between (D : F[X])
    (φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point)
    (hφzero : ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y),
      aeval x D = 0 → φ (.some x y h) = 0)
    (x : specOver F k ⟶ schemeOver W)
    (hx : schemePointActionBetween W V φ x ≠ 1) :
    ∃ z : specOver F k ⟶ specOver F (RationalOpenRing W D),
      z ≫ rationalOpenIncl W D = x := by
  classical
  obtain ⟨P, hP⟩ := (affinePointEquiv W k).surjective x
  have hp : ofAffinePoint W k P = x := hP
  have hpoint : schemePointActionBetween W V φ (ofAffinePoint W k P) =
      ofAffinePoint V k (φ P) := schemePointActionBetween_ofAffinePoint W V φ P
  have hzero : ofAffinePoint V k (0 : (V.baseChange k).toAffine.Point) = 1 :=
    (affinePointMulEquiv V k).map_one
  have hne : φ P ≠ 0 := by
    intro hz
    exact hx ((congrArg (schemePointActionBetween W V φ) hp).symm.trans
      (hpoint.trans ((congrArg (ofAffinePoint V k) hz).trans hzero)))
  obtain ⟨z, hz⟩ := rationalOpen_lift_between W V D φ hφzero P hne
  exact ⟨z, hz.trans hp⟩

omit [IsAlgClosed k] in
/-- The actual localization-point formula is independent of the choice
of presentation of the field-valued source morphism. -/
private theorem rationalOpen_scheme_action_between
    (α : F) (hα : α ≠ 0) (A D : F[X])
    (hshort : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (hshortV : V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0)
    (hID : Weierstrass.RationalIdentityBetween W V α A D)
    (φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point)
    (hφsome : ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y),
      aeval x D ≠ 0 → ∃ h', φ (.some x y h) =
        .some (aeval x A / aeval x D)
          ((algebraMap F k α)⁻¹ *
            (aeval x (derivative A * D - A * derivative D) / aeval x D ^ 2) * y) h')
    (z : specOver F k ⟶ specOver F (RationalOpenRing W D)) :
    schemePointActionBetween W V φ (z ≫ rationalOpenIncl W D) ≠ 1 ∧
      z ≫ rationalOpenHomBetween W V α hα A D hshort hshortV hID =
        schemePointActionBetween W V φ (z ≫ rationalOpenIncl W D) := by
  classical
  obtain ⟨g, rfl⟩ := exists_eq_specOverMap z
  exact rationalOpen_action_between W V α hα A D hshort hshortV hID φ hφsome g

section GluingApplication

-- These declarations already have their own checked geometric proofs.
-- Do not expand their projective polynomial constructions merely to compare
-- source and target types. This is local elaborator transparency only;
-- the kernel still checks the original definitions and proof term.
attribute [local irreducible] scheme toSpec cubicIdeal grading

omit [DecidableEq k] in
/-- Specialize the existing abstract kernel-open gluing to the actual
Weierstrass groups, supplying their canonical structural witnesses.
The open chart and point action are parameters here: the localization and
the two curve equations are not unfolded by the final application. -/
private theorem complete_curve_kernel_open
    {U : Over (Spec (.of F))}
    (j : U ⟶ schemeOver W) [IsOpenImmersion j.left]
    (fU : U ⟶ schemeOver V) (q : 𝟙_ (Over (Spec (.of F))) ⟶ U)
    (Φ : (specOver F k ⟶ schemeOver W) →* (specOver F k ⟶ schemeOver V))
    (hlift : ∀ x, Φ x ≠ 1 → ∃ z : specOver F k ⟶ U, z ≫ j = x)
    (hlocal : ∀ z : specOver F k ⟶ U, Φ (z ≫ j) ≠ 1 ∧ z ≫ fU = Φ (z ≫ j)) :
    ∃ f : schemeOver W ⟶ schemeOver V, IsMonHom f ∧ j ≫ f = fU ∧
      ∀ x : specOver F k ⟶ schemeOver W, x ≫ f = Φ x := by
  have hfinite : LocallyOfFiniteType (schemeOver W).hom :=
    inferInstanceAs (LocallyOfFiniteType (toSpec W))
  have hred : IsReduced (schemeOver W).left := isReduced_over_left W
  have hsep : IsSeparated (schemeOver V).hom := isSeparated_over_hom V
  have hprod : IsReduced (schemeOver W ⊗ schemeOver W).left :=
    @isReduced_tensor_left F _ W (schemeOver W) hred
  exact @complete_kernel_open F k _ _ _ _ (schemeOver W) (schemeOver V)
    (grpObj W) (grpObj V) hfinite hred hsep hprod U j
    (inferInstance : IsOpenImmersion j.left) fU q Φ hlift hlocal

set_option diagnostics true in
/-- Specialize the abstract group-scheme completion to the two independently
specified elliptic curves. The point lemmas and structural instances have
already been constructed. -/
theorem exists_global_hom_of_rational_point_map_between
    (α : F) (hα : α ≠ 0) (A D : F[X])
    (hshort : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (hshortV : V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0)
    (hID : Weierstrass.RationalIdentityBetween W V α A D)
    (φ : (W.baseChange k).toAffine.Point →+ (V.baseChange k).toAffine.Point)
    (hφ : ∀ (x y : k) (h : (W.baseChange k).toAffine.Nonsingular x y),
      (aeval x D = 0 → φ (.some x y h) = 0) ∧
      (aeval x D ≠ 0 → ∃ h', φ (.some x y h) =
        .some (aeval x A / aeval x D)
          ((algebraMap F k α)⁻¹ *
            (aeval x (derivative A * D - A * derivative D) / aeval x D ^ 2) * y) h'))
    (x₀ y₀ : F) (h₀ : W.toAffine.Equation x₀ y₀) (hD₀ : D.eval x₀ ≠ 0) :
    ∃ f : schemeOver W ⟶ schemeOver V,
      IsMonHom f ∧ rationalOpenIncl W D ≫ f = rationalOpenHomBetween W V α hα A D hshort hshortV hID ∧
      ∀ P : (W.baseChange k).toAffine.Point,
        ofAffinePoint W k P ≫ f = ofAffinePoint V k (φ P) := by
  let U : Over (Spec (.of F)) := specOver F (RationalOpenRing W D)
  let j : U ⟶ schemeOver W := rationalOpenIncl W D
  let fU : U ⟶ schemeOver V := rationalOpenHomBetween W V α hα A D hshort hshortV hID
  let q : 𝟙_ (Over (Spec (.of F))) ⟶ U := rationalOpenSection W D x₀ y₀ h₀ hD₀
  let Φ : (specOver F k ⟶ schemeOver W) →* (specOver F k ⟶ schemeOver V) :=
    schemePointActionBetween W V φ
  have hj : IsOpenImmersion j.left := isOpenImmersion_rationalOpenIncl W D
  have hlift : ∀ x : specOver F k ⟶ schemeOver W, Φ x ≠ 1 →
      ∃ z : specOver F k ⟶ U, z ≫ j = x :=
    rationalOpen_scheme_lift_between W V D φ (fun x y h => (hφ x y h).1)
  have hlocal : ∀ z : specOver F k ⟶ U,
      Φ (z ≫ j) ≠ 1 ∧ z ≫ fU = Φ (z ≫ j) :=
    rationalOpen_scheme_action_between W V α hα A D hshort hshortV hID φ
      (fun x y h => (hφ x y h).2)
  have hex : ∃ f : schemeOver W ⟶ schemeOver V, IsMonHom f ∧ j ≫ f = fU ∧
      ∀ x : specOver F k ⟶ schemeOver W, x ≫ f = Φ x :=
    complete_curve_kernel_open (k := k) W V j fU q Φ hlift hlocal
  obtain ⟨f, hf, hjf, hfx⟩ := hex
  refine ⟨f, hf, hjf, fun P => ?_⟩
  exact (hfx (ofAffinePoint W k P)).trans
    (schemePointActionBetween_ofAffinePoint W V φ P)

end GluingApplication

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassCurve

namespace RHLean.Geometry.NativeCM.Weierstrass

variable {K K' : Type*} [Field K] [Field K']

/-- The exact rational differential identity survives the actual finite
coefficient extension used to obtain a translation point. -/
theorem RationalIdentity.map {W : _root_.WeierstrassCurve K} {α : K} {A D : K[X]}
    (h : RationalIdentity W α A D) (f : K →+* K') :
    RationalIdentity (W.map f) (f α) (A.map f) (D.map f) := by
  unfold RationalIdentity at h ⊢
  have he := congrArg (Polynomial.map f) h
  simpa only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, ← derivative_map,
    map_pow, _root_.WeierstrassCurve.map_a₄, _root_.WeierstrassCurve.map_a₆] using! he

variable [DecidableEq K]

/-- Equality of equations identifies the existing point groups without
changing any affine coordinate. -/
def pointCongr {V W : _root_.WeierstrassCurve K} (h : V = W) :
    V.toAffine.Point ≃+ W.toAffine.Point := by
  subst W
  exact AddEquiv.refl _

@[simp] theorem pointCongr_some {V W : _root_.WeierstrassCurve K} (h : V = W)
    {x y : K} (hp : V.toAffine.Nonsingular x y) :
    pointCongr h (.some x y hp) = .some x y (h ▸ hp) := by
  subst W
  rfl

@[simp] theorem pointCongr_symm_some {V W : _root_.WeierstrassCurve K} (h : V = W)
    {x y : K} (hp : W.toAffine.Nonsingular x y) :
    (pointCongr h).symm (.some x y hp) = .some x y (h.symm ▸ hp) := by
  subst W
  rfl

/-- Transport of the actual additive action across equality of equations. -/
def pointConjugate {V W : _root_.WeierstrassCurve K} (h : V = W)
    (φ : W.toAffine.Point →+ W.toAffine.Point) : V.toAffine.Point →+ V.toAffine.Point :=
  (pointCongr h).symm.toAddMonoidHom.comp (φ.comp (pointCongr h).toAddMonoidHom)

@[simp] theorem pointCongr_pointConjugate {V W : _root_.WeierstrassCurve K} (h : V = W)
    (φ : W.toAffine.Point →+ W.toAffine.Point) (P : V.toAffine.Point) :
    pointCongr h (pointConjugate h φ P) = φ (pointCongr h P) :=
  (pointCongr h).apply_symm_apply _

@[simp] theorem pointConjugate_pointCongr_symm {V W : _root_.WeierstrassCurve K} (h : V = W)
    (φ : W.toAffine.Point →+ W.toAffine.Point) (P : W.toAffine.Point) :
    pointConjugate h φ ((pointCongr h).symm P) = (pointCongr h).symm (φ P) := by
  change (pointCongr h).symm (φ (pointCongr h ((pointCongr h).symm P))) = _
  rw [AddEquiv.apply_symm_apply]

section ActualLatticeIsogeny

open NumberField PeriodPair IntermediateField
open SchemeTheory SchemeTheory.WeierstrassCurve

/-- Apply the same two-patch proof to the literal lattice isogeny and the
two given equations over a finite coefficient field. Only the original
translation point is adjoined; no model or multiplier is changed. -/
theorem exists_scheme_latticeIsogeny
    (F : IntermediateField ℚ ℂ) [NumberField F]
    (W V : _root_.WeierstrassCurve F) [W.IsElliptic] [V.IsElliptic]
    (L L' : PeriodPair)
    (hW : W.baseChange ℂ = latticeCurve L)
    (hV : V.baseChange ℂ = latticeCurve L')
    (hsW : W.a₁ = 0 ∧ W.a₂ = 0 ∧ W.a₃ = 0)
    (hsV : V.a₁ = 0 ∧ V.a₂ = 0 ∧ V.a₃ = 0)
    (α : ℂ) (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (hαF : α ∈ F) (A D : ℂ[X])
    (hAF : ∀ i, A.coeff i ∈ F) (hDF : ∀ i, D.coeff i ∈ F)
    (hD : D ≠ 0)
    (hformula : ∀ (x y : ℂ) (h : (latticeCurve L).toAffine.Nonsingular x y),
      (D.eval x = 0 → latticeIsogeny α hα (.some x y h) = 0) ∧
      (D.eval x ≠ 0 → ∃ h', latticeIsogeny α hα (.some x y h) =
        .some (A.eval x / D.eval x)
          (α⁻¹ * ((derivative A * D - A * derivative D).eval x / D.eval x ^ 2) * y) h')) :
    ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K) (hFK : F ≤ K),
      let W' := W.map (IntermediateField.inclusion hFK).toRingHom
      let V' := V.map (IntermediateField.inclusion hFK).toRingHom
      ∃ (hW' : W'.baseChange ℂ = latticeCurve L)
        (hV' : V'.baseChange ℂ = latticeCurve L')
        (f : schemeOver W' ⟶ schemeOver V'),
        IsMonHom f ∧ ∀ z : ℂ,
          ofAffinePoint W' ℂ ((pointCongr hW').symm (latticePoint L z)) ≫ f =
            ofAffinePoint V' ℂ ((pointCongr hV').symm (latticePoint L' (α * z))) := by
  classical
  obtain ⟨D₀, hD₀sub, _⟩ := exists_polynomial_over_subfield F.toSubfield D hDF
  have hD₀ : D₀.map (F.val : F →+* ℂ) = D := hD₀sub
  have hD₀nz : D₀ ≠ 0 := by
    intro h
    apply hD
    rw [← hD₀, h, Polynomial.map_zero]
  obtain ⟨K, hK, hFK, x₀, y₀, hxy, hx⟩ :=
    exists_numberField_point_off_denominator F W hsW D₀ hD₀nz
  let _ : NumberField K := hK
  let i : F →ₐ[ℚ] K := IntermediateField.inclusion hFK
  let W' := W.map i.toRingHom
  let V' := V.map i.toRingHom
  let α' : K := ⟨α, hFK hαF⟩
  let D' := D₀.map i.toRingHom
  obtain ⟨A', hA'sub, _⟩ := exists_polynomial_over_subfield K.toSubfield A
    (fun j => hFK (hAF j))
  have hA' : A'.map (K.val : K →+* ℂ) = A := hA'sub
  have hD' : D'.map (K.val : K →+* ℂ) = D := by
    change (D₀.map i.toRingHom).map (K.val : K →+* ℂ) = D
    rw [Polynomial.map_map]
    exact hD₀
  have hα' : α' ≠ 0 := fun h => hα0 (congrArg Subtype.val h)
  have hW' : W'.baseChange ℂ = latticeCurve L := by
    change (W.map i.toRingHom).map (K.val : K →+* ℂ) = _
    rw [_root_.WeierstrassCurve.map_map]
    exact hW
  have hV' : V'.baseChange ℂ = latticeCurve L' := by
    change (V.map i.toRingHom).map (K.val : K →+* ℂ) = _
    rw [_root_.WeierstrassCurve.map_map]
    exact hV
  have hsW' : W'.a₁ = 0 ∧ W'.a₂ = 0 ∧ W'.a₃ = 0 := by
    simp only [W', _root_.WeierstrassCurve.map_a₁, _root_.WeierstrassCurve.map_a₂,
      _root_.WeierstrassCurve.map_a₃, hsW.1, hsW.2.1, hsW.2.2, map_zero, and_self]
  have hsV' : V'.a₁ = 0 ∧ V'.a₂ = 0 ∧ V'.a₃ = 0 := by
    simp only [V', _root_.WeierstrassCurve.map_a₁, _root_.WeierstrassCurve.map_a₂,
      _root_.WeierstrassCurve.map_a₃, hsV.1, hsV.2.1, hsV.2.2, map_zero, and_self]
  have hID : RationalIdentityBetween W' V' α' A' D' := by
    apply rationalIdentityBetween_of_map (K.val : K →+* ℂ)
    have hWM : W'.map (K.val : K →+* ℂ) = latticeCurve L := hW'
    have hVM : V'.map (K.val : K →+* ℂ) = latticeCurve L' := hV'
    rw [hWM, hVM, hA', hD']
    exact rationalIdentityBetween_of_point_formula L L' hα0 A D hD
      (latticeIsogeny α hα) fun x y h hd => (hformula x y h).2 hd
  let φ := (pointCongr hV').symm.toAddMonoidHom.comp
    ((latticeIsogeny α hα).comp (pointCongr hW').toAddMonoidHom)
  have hφeq (P : (W'.baseChange ℂ).toAffine.Point) :
      pointCongr hV' (φ P) = latticeIsogeny α hα (pointCongr hW' P) := by
    change pointCongr hV' ((pointCongr hV').symm
      (latticeIsogeny α hα (pointCongr hW' P))) = _
    exact (pointCongr hV').apply_symm_apply _
  have hφ : ∀ (x y : ℂ) (h : (W'.baseChange ℂ).toAffine.Nonsingular x y),
      (aeval x D' = 0 → φ (.some x y h) = 0) ∧
      (aeval x D' ≠ 0 → ∃ h', φ (.some x y h) =
        .some (aeval x A' / aeval x D')
          ((algebraMap K ℂ α')⁻¹ *
            (aeval x (derivative A' * D' - A' * derivative D') / aeval x D' ^ 2) * y) h') := by
    intro x y h
    have hp : (latticeCurve L).toAffine.Nonsingular x y := hW' ▸ h
    have hd : aeval x D' = D.eval x :=
      (show aeval x D' = (D'.map (K.val : K →+* ℂ)).eval x from
        (Polynomial.eval_map (K.val : K →+* ℂ) x).symm).trans
          (congrArg (fun p : ℂ[X] => p.eval x) hD')
    have ha : aeval x A' = A.eval x :=
      (show aeval x A' = (A'.map (K.val : K →+* ℂ)).eval x from
        (Polynomial.eval_map (K.val : K →+* ℂ) x).symm).trans
          (congrArg (fun p : ℂ[X] => p.eval x) hA')
    have hb : aeval x (derivative A' * D' - A' * derivative D') =
        (derivative A * D - A * derivative D).eval x := by
      change (derivative A' * D' - A' * derivative D').eval₂
        (K.val : K →+* ℂ) x = _
      rw [← Polynomial.eval_map]
      simp only [Polynomial.map_sub, Polynomial.map_mul, ← derivative_map, hA', hD']
    have hαC : algebraMap K ℂ α' = α := rfl
    constructor
    · intro hz
      apply (pointCongr hV').injective
      rw [hφeq, map_zero, pointCongr_some]
      exact (hformula x y hp).1 (hd ▸ hz)
    · intro hz
      obtain ⟨hp', he⟩ := (hformula x y hp).2 (hd ▸ hz)
      have hpa : (latticeCurve L').toAffine.Nonsingular (aeval x A' / aeval x D')
          ((algebraMap K ℂ α')⁻¹ *
            (aeval x (derivative A' * D' - A' * derivative D') / aeval x D' ^ 2) * y) := by
        rw [ha, hd, hb, hαC]
        exact hp'
      refine ⟨hV'.symm ▸ hpa, ?_⟩
      apply (pointCongr hV').injective
      calc
        _ = latticeIsogeny α hα (.some x y hp) :=
          (hφeq (.some x y h)).trans (congrArg (latticeIsogeny α hα)
            (pointCongr_some hW' h))
        _ = .some (A.eval x / D.eval x)
            (α⁻¹ * ((derivative A * D - A * derivative D).eval x / D.eval x ^ 2) * y) hp' := he
        _ = _ := by
          simp only [pointCongr_some, ha, hd, hb, hαC]
  obtain ⟨f, hf, _, hfx⟩ := exists_global_hom_of_rational_point_map_between
    W' V' α' hα' A' D' hsW' hsV' hID φ hφ x₀ y₀ hxy hx
  refine ⟨K, hK, hFK, hW', hV', f, hf, fun z => ?_⟩
  rw [hfx]
  change ofAffinePoint V' ℂ ((pointCongr hV').symm
    (latticeIsogeny α hα (pointCongr hW' ((pointCongr hW').symm (latticePoint L z))))) = _
  rw [AddEquiv.apply_symm_apply, latticeIsogeny_latticePoint]

end ActualLatticeIsogeny

end RHLean.Geometry.NativeCM.Weierstrass

end
