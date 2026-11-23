import RHLean.Geometry.NativeCMWeierstrassGeometricPoints

/-!
# Gluing a group map from one denominator open and a translate

The geometric-point cover is upgraded to an actual open cover, and the local
scheme maps are glued after their equality on the overlap has been proved.
The second patch is translated by an actual section of the first patch. Its
formula is the first local map followed by subtraction of the image of that
section. Thus a homomorphism of geometric points, with its exact nonzero
locus, supplies an actual group-scheme morphism, without a proper-curve
extension premise.

This is a native two-patch derivation using the preceding residue-field
detection theorem and the already reconstructed group law. The underlying
open-cover construction is the one in Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/
MulLeftCompOfPullbackPointEquivMul.lean (`exists_over_hom_of_locally`).
The source archive states no license; attribution is retained without
assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.GeometricPoints

universe u

variable {F K : Type u} [Field F] [Field K] [IsAlgClosed K] [Algebra F K]

/-- A cover and compatible local maps can be checked at the points of the
fixed algebraically closed extension. The resulting map is still over F. -/
theorem exists_hom_of_geometric_cover
    {T Y : Over (Spec (.of F))} [LocallyOfFiniteType T.hom]
    [IsReduced T.left] [IsSeparated Y.hom]
    {I : Type u} (U : I → Over (Spec (.of F))) (j : ∀ i, U i ⟶ T)
    (hj : ∀ i, IsOpenImmersion (j i).left) (fU : ∀ i, U i ⟶ Y)
    (Φ : (specOver F K ⟶ T) → (specOver F K ⟶ Y))
    (hc : ∀ x, ∃ i, ∃ z : specOver F K ⟶ U i, z ≫ j i = x)
    (hf : ∀ i, ∀ z : specOver F K ⟶ U i, z ≫ fU i = Φ (z ≫ j i)) :
    ∃ f : T ⟶ Y, (∀ i, j i ≫ f = fU i) ∧
      ∀ x : specOver F K ⟶ T, x ≫ f = Φ x := by
  classical
  have hmem : ∀ t : T.left, ∃ i, t ∈ Set.range (j i).left := by
    intro t
    by_contra ht
    let Z : Set T.left := (⋃ i, Set.range (j i).left)ᶜ
    have hZ : IsClosed Z := (isOpen_iUnion fun i => by
      have := hj i
      exact (j i).left.isOpenEmbedding.isOpen_range).isClosed_compl
    have htZ : t ∈ Z := by
      simpa only [Z, Set.mem_compl_iff, Set.mem_iUnion] using ht
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap F K))) :=
      surjective_specMap_field (algebraMap F K)
    obtain ⟨x, hx, hxZ⟩ := exists_geomPoint_mem T.hom
      (Spec.map (CommRingCat.ofHom (algebraMap F K))) hZ.isLocallyClosed ⟨t, htZ⟩
    obtain ⟨i, z, hz⟩ := hc (Over.homMk x hx)
    let a : ↥(Spec (.of K)) := IsLocalRing.closedPoint K
    apply hxZ a
    apply Set.mem_iUnion.mpr
    refine ⟨i, z.left a, ?_⟩
    exact congrArg (fun q : specOver F K ⟶ T => q.left a) hz
  let 𝒰 : T.left.OpenCover :=
    { I₀ := I, X i := (U i).left, f i := (j i).left,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun t => by obtain ⟨i, hi⟩ := hmem t; exact ⟨i, by simpa using hi⟩,
          fun i => hj i⟩ }
  have hcomp : ∀ a b, pullback.fst (j a).left (j b).left ≫ (fU a).left =
      pullback.snd (j a).left (j b).left ≫ (fU b).left := by
    intro a b
    have := hj a
    have := hj b
    let P : Over (Spec (.of F)) :=
      Over.mk (pullback.fst (j a).left (j b).left ≫ (j a).left ≫ T.hom)
    have : IsReduced P.left :=
      isReduced_of_isOpenImmersion (pullback.fst (j a).left (j b).left ≫ (j a).left)
    have : LocallyOfFiniteType P.hom := by
      dsimp [P]
      infer_instance
    let p₁ : P ⟶ U a := Over.homMk (pullback.fst _ _) (by
      show _ = pullback.fst _ _ ≫ (j a).left ≫ T.hom
      rw [Over.w])
    let p₂ : P ⟶ U b := Over.homMk (pullback.snd _ _) (by
      show _ = pullback.fst _ _ ≫ (j a).left ≫ T.hom
      rw [pullback.condition_assoc, Over.w])
    have hp : p₁ ≫ j a = p₂ ≫ j b := by
      ext
      simp [p₁, p₂, pullback.condition]
    have he : p₁ ≫ fU a = p₂ ≫ fU b := by
      apply over_hom_ext_of_embedded_points (K := K)
      intro x
      rw [← Category.assoc, ← Category.assoc, hf, hf,
        Category.assoc, Category.assoc, hp]
    simpa [p₁, p₂] using congrArg Over.Hom.left he
  let g : T.left ⟶ Y.left := 𝒰.glueMorphisms (fun i => (fU i).left) hcomp
  have hg : ∀ i, (j i).left ≫ g = (fU i).left := fun i => 𝒰.ι_glueMorphisms _ hcomp i
  have hw : g ≫ Y.hom = T.hom := by
    refine 𝒰.hom_ext _ _ fun i => ?_
    change (j i).left ≫ g ≫ Y.hom = (j i).left ≫ T.hom
    rw [← Category.assoc, hg, Over.w, Over.w]
  let f : T ⟶ Y := Over.homMk g hw
  have hjf : ∀ i, j i ≫ f = fU i := fun i => Over.OverMorphism.ext (hg i)
  refine ⟨f, hjf, fun x => ?_⟩
  obtain ⟨i, z, rfl⟩ := hc x
  rw [Category.assoc, hjf, hf]

section Translation

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]

/-- Translation is an actual isomorphism of schemes over the original base. -/
def rightTranslation (p : 𝟙_ (Over S) ⟶ G) : G ≅ G where
  hom := (𝟙 G) * (toUnit G ≫ p)
  inv := (𝟙 G) * (toUnit G ≫ p⁻¹)
  hom_inv_id := by
    have hc : ((𝟙 G) * (toUnit G ≫ p)) ≫ (toUnit G ≫ p⁻¹) =
        (toUnit G ≫ p)⁻¹ := by
      rw [← Category.assoc,
        show ((𝟙 G) * (toUnit G ≫ p)) ≫ toUnit G = toUnit G from toUnit_unique _ _,
        GrpObj.comp_inv]
    rw [MonObj.comp_mul, Category.comp_id, hc]
    group
  inv_hom_id := by
    have hc : ((𝟙 G) * (toUnit G ≫ p⁻¹)) ≫ (toUnit G ≫ p) =
        toUnit G ≫ p := by
      rw [← Category.assoc,
        show ((𝟙 G) * (toUnit G ≫ p⁻¹)) ≫ toUnit G = toUnit G from toUnit_unique _ _]
    rw [MonObj.comp_mul, Category.comp_id, hc, GrpObj.comp_inv]
    group

theorem comp_rightTranslation_hom {T : Over S} (x : T ⟶ G)
    (p : 𝟙_ (Over S) ⟶ G) : x ≫ (rightTranslation p).hom = x * (toUnit T ≫ p) := by
  change x ≫ ((𝟙 G) * (toUnit G ≫ p)) = _
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    show x ≫ toUnit G = toUnit T from toUnit_unique _ _]

theorem comp_rightTranslation_inv {T : Over S} (x : T ⟶ G)
    (p : 𝟙_ (Over S) ⟶ G) : x ≫ (rightTranslation p).inv = x * (toUnit T ≫ p)⁻¹ := by
  change x ≫ ((𝟙 G) * (toUnit G ≫ p⁻¹)) = _
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    show x ≫ toUnit G = toUnit T from toUnit_unique _ _, GrpObj.comp_inv]

end Translation

section Group

variable {G H : Over (Spec (.of F))} [GrpObj G] [GrpObj H]
    [LocallyOfFiniteType G.hom] [IsReduced G.left] [IsSeparated H.hom]

/-- Two translates of the complement of a homomorphism kernel cover the
group. Both local maps and the finite-field translation point are retained. -/
theorem exists_hom_of_kernel_open
    {U : Over (Spec (.of F))} (j : U ⟶ G) [IsOpenImmersion j.left]
    (fU : U ⟶ H) (q : 𝟙_ (Over (Spec (.of F))) ⟶ U)
    (Φ : (specOver F K ⟶ G) →* (specOver F K ⟶ H))
    (hU : ∀ x, Φ x ≠ 1 ↔ ∃ z : specOver F K ⟶ U, z ≫ j = x)
    (hfU : ∀ z : specOver F K ⟶ U, z ≫ fU = Φ (z ≫ j)) :
    ∃ f : G ⟶ H, j ≫ f = fU ∧
      ∀ x : specOver F K ⟶ G, x ≫ f = Φ x := by
  classical
  let p : 𝟙_ (Over (Spec (.of F))) ⟶ G := q ≫ j
  let j' : U ⟶ G := j ≫ (rightTranslation p).inv
  let f' : U ⟶ H := fU * (toUnit U ≫ (q ≫ fU)⁻¹)
  have : IsIso (rightTranslation p).inv.left :=
    ((Over.forget _).mapIso (rightTranslation p)).isIso_inv
  have : IsOpenImmersion j'.left := by
    dsimp [j']
    infer_instance
  let js : ULift.{u} Bool → (U ⟶ G) := fun b => if b.down then j' else j
  let fs : ULift.{u} Bool → (U ⟶ H) := fun b => if b.down then f' else fU
  have hj : ∀ b, IsOpenImmersion (js b).left := by
    rintro ⟨b⟩
    cases b <;> dsimp [js] <;> infer_instance
  let pK : specOver F K ⟶ G := toUnit (specOver F K) ≫ p
  have hpK : Φ pK ≠ 1 := (hU pK).2
    ⟨toUnit (specOver F K) ≫ q, by simp only [pK, p, Category.assoc]⟩
  have hc : ∀ x : specOver F K ⟶ G,
      ∃ b, ∃ z : specOver F K ⟶ U, z ≫ js b = x := by
    intro x
    by_cases hx : Φ x ≠ 1
    · obtain ⟨z, hz⟩ := (hU x).1 hx
      exact ⟨⟨false⟩, z, hz⟩
    · have hx : Φ x = 1 := not_ne_iff.mp hx
      have hxp : Φ (x * pK) ≠ 1 := by rwa [map_mul, hx, _root_.one_mul]
      obtain ⟨z, hz⟩ := (hU (x * pK)).1 hxp
      refine ⟨⟨true⟩, z, ?_⟩
      change z ≫ j ≫ (rightTranslation p).inv = x
      rw [← Category.assoc, comp_rightTranslation_inv, hz]
      change (x * pK) * pK⁻¹ = x
      group
  have hf : ∀ b, ∀ z : specOver F K ⟶ U, z ≫ fs b = Φ (z ≫ js b) := by
    rintro ⟨b⟩ z
    cases b
    · exact hfU z
    · change z ≫ (fU * (toUnit U ≫ (q ≫ fU)⁻¹)) =
        Φ (z ≫ j ≫ (rightTranslation p).inv)
      rw [MonObj.comp_mul, hfU, ← Category.assoc,
        show z ≫ toUnit U = toUnit (specOver F K) from toUnit_unique _ _,
        GrpObj.comp_inv]
      have hq : toUnit (specOver F K) ≫ q ≫ fU = Φ pK := by
        rw [← Category.assoc, hfU]
        rfl
      rw [hq, ← Category.assoc, comp_rightTranslation_inv, map_mul, map_inv]
  obtain ⟨f, hjf, hfx⟩ :=
    exists_hom_of_geometric_cover (fun _ : ULift.{u} Bool => U) js hj fs Φ hc hf
  exact ⟨f, hjf ⟨false⟩, hfx⟩

variable [IsReduced (G ⊗ G).left]

/-- The group law of the constructed morphism follows from the actual group
homomorphism at the fixed geometric points. -/
omit [IsReduced G.left] in
theorem isMonHom_of_embedded_points (f : G ⟶ H)
    (Φ : (specOver F K ⟶ G) →* (specOver F K ⟶ H))
    (hf : ∀ x : specOver F K ⟶ G, x ≫ f = Φ x) : IsMonHom f where
  one_hom := by
    have : LocallyOfFiniteType (𝟙_ (Over (Spec (.of F)))).hom := by
      change LocallyOfFiniteType (𝟙 (Spec (.of F)))
      infer_instance
    have : IsReduced (𝟙_ (Over (Spec (.of F)))).left := by
      change IsReduced (Spec (.of F))
      infer_instance
    apply over_hom_ext_of_embedded_points (K := K)
    intro x
    rw [← Category.assoc, MonObj.one_eq_one, MonObj.comp_one, hf, map_one,
      MonObj.one_eq_one, MonObj.comp_one]
  mul_hom := by
    have : LocallyOfFiniteType (G ⊗ G).hom := by
      change LocallyOfFiniteType (pullback.fst G.hom G.hom ≫ G.hom)
      infer_instance
    apply over_hom_ext_of_embedded_points (K := K)
    intro x
    change (x ≫ μ[G]) ≫ f = (x ≫ (f ⊗ₘ f)) ≫ μ[H]
    rw [MonObj.mul_eq_mul, MonObj.comp_mul, hf, map_mul,
      MonObj.mul_eq_mul, MonObj.comp_mul]
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd]
    rw [← Category.assoc, ← Category.assoc, hf, hf]

end Group

end RHLean.Geometry.NativeCM.SchemeTheory.GeometricPoints

end
