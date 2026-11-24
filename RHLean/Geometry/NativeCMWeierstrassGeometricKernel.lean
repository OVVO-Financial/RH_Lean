import RHLean.Geometry.NativeCMWeierstrassRelativePoints
import RHLean.Geometry.NativeCMWeierstrassGraphKernelTorsion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The actual graph projection has finite geometric kernel

The second coordinate identifies the kernel with a closed subgroup of
an actual geometric fibre of the original Weierstrass equation. The
explicit 2/3-torsion result proves that subgroup finite. Its no-torsion
property is supplied by the actual flat generic graph and the etale
multiplication calculation.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfIsReducedOfRangeSubset.lean`.
The native argument replaces the general semiabelian/abelian-subgroup
supplier by the actual Weierstrass equation and its proved point
base-change equivalence. The source archive states no license;
attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Classical CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

open SchemeTheory.WeierstrassCurve

theorem exists_lift_of_isReduced_of_range_subset {Y X Z : Scheme.{0}} [IsReduced Y] (i : Z ⟶ X)
    [IsClosedImmersion i] (a : Y ⟶ X) (h : Set.range a ⊆ Set.range i) :
    ∃ b : Y ⟶ Z, b ≫ i = a := by
  have : Surjective (pullback.snd i a) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h ⟨y, rfl⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i a)
  exact ⟨inv (pullback.snd i a) ≫ pullback.fst i a, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem finite_geometric_elliptic_kernel_of_no_small_torsion
    {R : Type} [CommRing R] [_root_.IsReduced R]
    (G Ga : Over (Sp R)) [GrpObj G] [GrpObj Ga]
    (W : _root_.WeierstrassCurve R) [W.IsElliptic]
    (io : Ga ⟶ G ⊗ schemeOver W) [IsMonHom io] [IsClosedImmersion io.left]
    (n : ℕ) (hn : n = 2 ∨ n = 3) (hnR : IsUnit (n : R))
    (htor : ∀ (Y : Over (Sp R)) (x : Y ⟶ Ga),
      x ^ n = 1 → x ≫ io ≫ fst G (schemeOver W) = 1 → x = 1)
    (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) :
    Finite {x : Over.mk t ⟶ Ga // x ≫ io ≫ fst G (schemeOver W) = 1} := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective t
  let _ : Algebra R k := φ.hom.toAlgebra
  change Finite {x : specOver R k ⟶ Ga // x ≫ io ≫ fst G (schemeOver W) = 1}
  let T := specOver R k
  let H := schemeOver W
  let ρ := relativePointMulEquiv W k
  have hρ : ∀ y, (ρ y).left = y.left ≫ mapHom W (algebraMap R k) rfl :=
    relativePointMulEquiv_left W k
  let s : H ⟶ G ⊗ H := lift 1 (𝟙 H)
  have hs₁ : ∀ y : T ⟶ H, (y ≫ s) ≫ fst G H = 1 := fun y => by
    rw [Category.assoc, lift_fst, MonObj.comp_one]
  have hs₂ : ∀ y : T ⟶ H, (y ≫ s) ≫ snd G H = y := fun y => by
    rw [Category.assoc, lift_snd, Category.comp_id]
  let σ : (T ⟶ H) →* (T ⟶ G ⊗ H) :=
    MonoidHom.mk' (fun y => y ≫ s) fun y z => by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [hs₁, MonObj.mul_comp, hs₁, hs₁, _root_.mul_one]
      · rw [hs₂, MonObj.mul_comp, hs₂, hs₂]
  let κ : (T ⟶ Ga) →* (T ⟶ G ⊗ H) :=
    MonoidHom.mk' (fun x => x ≫ io) fun x y => MonObj.mul_comp x y io
  have : Mono io := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hκ : Function.Injective κ := fun x y hxy => (cancel_mono io).mp hxy
  let C := κ.range.comap (σ.comp ρ.toMonoidHom)
  have hnk : (n : k) ≠ 0 := by
    have hu : IsUnit (n : k) := by
      simpa only [map_natCast] using! hnR.map (algebraMap R k)
    exact hu.ne_zero
  have hC : Finite C := by
    refine finite_closed_subgroup_of_no_small_torsion (W.baseChange k) n hn hnk C
      ((mapHom W (algebraMap R k) rfl ≫ s.left) ⁻¹' Set.range io.left)
      (io.left.isClosedEmbedding.isClosed_range.preimage
        (mapHom W (algebraMap R k) rfl ≫ s.left).continuous) (fun y => ⟨?_, ?_⟩) ?_
    · rintro ⟨x, hx⟩ _ ⟨p, rfl⟩
      have e := congrArg Over.Hom.left hx
      change x.left ≫ io.left = (ρ y).left ≫ s.left at e
      rw [hρ, Category.assoc] at e
      exact ⟨x.left p, by rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]⟩
    · intro hy
      have : IsReduced T.left := inferInstanceAs (IsReduced (Sp k))
      obtain ⟨b, hb⟩ := exists_lift_of_isReduced_of_range_subset io.left (ρ y ≫ s).left (by
        rintro _ ⟨p, rfl⟩
        change (s.left ((ρ y).left p)) ∈ Set.range io.left
        rw [hρ]
        exact hy ⟨p, rfl⟩)
      exact ⟨Over.homMk b (by rw [← Over.w io, ← Category.assoc, hb, Over.w]),
        Over.OverMorphism.ext hb⟩
    · rintro y ⟨x, hx⟩ hy
      have hx1 : x = 1 := by
        refine htor T x (hκ ?_) ?_
        · rw [map_pow, hx, ← map_pow, hy, map_one, map_one]
        · rw [← Category.assoc]
          exact (congrArg (· ≫ fst G H) hx).trans (hs₁ _)
      apply ρ.injective
      rw [map_one, ← hs₂ (ρ y)]
      have e : ρ y ≫ s = 1 := hx.symm.trans (by rw [hx1, map_one])
      rw [e, MonObj.one_comp]
  choose r hr using ρ.surjective
  have key : ∀ x : {x : T ⟶ Ga // x ≫ io ≫ fst G H = 1},
      κ x.1 = σ (ρ (r (x.1 ≫ io ≫ snd G H))) := fun x => by
    rw [hr]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact ((Category.assoc _ _ _).trans x.2).trans (hs₁ _).symm
    · exact (Category.assoc _ _ _).trans (hs₂ _).symm
  refine Finite.of_injective (fun x : {x : T ⟶ Ga // x ≫ io ≫ fst G H = 1} =>
    (⟨r (x.1 ≫ io ≫ snd G H), x.1, key x⟩ : C)) fun x y hxy => Subtype.ext (hκ ?_)
  rw [key x, key y, show r (x.1 ≫ io ≫ snd G H) = r (y.1 ≫ io ≫ snd G H) from
    congrArg Subtype.val hxy]

/-- The actual flat graph supplies the no-torsion premise, and the
original elliptic equation supplies finiteness on every geometric fibre. -/
theorem finite_geometric_elliptic_graph_kernel (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (G Ga : Over (Sp R)) [GrpObj G] [GrpObj Ga] [IsCommMonObj G] [IsCommMonObj Ga]
    [Flat G.hom] [Flat Ga.hom] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType Ga.hom]
    [IsSeparated Ga.hom] (W : _root_.WeierstrassCurve R) [W.IsElliptic]
    (io : Ga ⟶ G ⊗ schemeOver W) [IsMonHom io] [IsClosedImmersion io.left]
    [IsIso ((Over.pullback (spMap (algebraMap R K))).map (io ≫ fst G (schemeOver W)))]
    (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) :
    Finite {x : Over.mk t ⟶ Ga // x ≫ io ≫ fst G (schemeOver W) = 1} := by
  obtain ⟨n, hn, hu⟩ := exists_small_isUnit_of_isLocalRing R
  refine finite_geometric_elliptic_kernel_of_no_small_torsion G Ga W io n hn hu ?_ k t
  intro Y x hx hp
  exact graph_kernel_no_torsion R K Ga G (io ≫ fst G (schemeOver W)) n hu Y x hx hp

/- The following cut uses the standard translation of a nonempty group
fibre into its kernel, and the Jacobson property of finite-type schemes
over algebraically closed fields. It needs no geometric rank or mass
assignment. Source comparison: Alpöge (with Claude),
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/
LocallyQuasiFiniteOfFiniteGeometricPoints.lean, pinned as above. -/

private theorem finite_points_of_finite_sections {k : Type} [Field k] [IsAlgClosed k]
    {X : Scheme.{0}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hs : Finite {v : Spec (.of k) ⟶ X // v ≫ s = 𝟙 _}) : Finite X := by
  letI := hs
  letI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  have hc : (closedPoints X).Finite := by
    letI : Finite (closedPoints X) := Finite.of_equiv _ (pointEquivClosedPoint s)
    exact Set.toFinite _
  have hclosed : IsClosed (closedPoints X) := by
    rw [← Set.biUnion_of_singleton (closedPoints X)]
    exact hc.isClosed_biUnion fun x hx => hx
  have hu : closedPoints X = Set.univ := by
    have h := JacobsonSpace.closure_inter_closedPoints (X := X) isClosed_univ
    rwa [Set.univ_inter, hclosed.closure_eq] at h
  exact Set.finite_univ_iff.mp (hu ▸ hc)

private theorem locallyQuasiFinite_of_geometric_fibres {X Y : Scheme.{0}}
    (p : X ⟶ Y) [LocallyOfFiniteType p]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Spec (.of k) ⟶ Y),
      Finite {x : Spec (.of k) ⟶ X // x ≫ p = y}) :
    LocallyQuasiFinite p := by
  refine LocallyQuasiFinite.of_finite_preimage_singleton p fun y => ?_
  let k := AlgebraicClosure (Y.residueField y)
  let t : Spec (.of k) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y
  have hy : y ∈ Set.range t := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of k)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans
      (Scheme.fromSpecResidueField_apply y _)⟩
  have hsections := h k t
  letI : Finite {x : Spec (.of k) ⟶ X // x ≫ p = t} := hsections
  have hfinite : Finite ↥(pullback p t) := by
    apply finite_points_of_finite_sections (pullback.snd p t)
    refine Finite.of_injective (β := {x : Spec (.of k) ⟶ X // x ≫ p = t})
      (fun x => ⟨x.1 ≫ pullback.fst p t, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp]⟩) ?_
    intro x x' hxx
    apply Subtype.ext
    apply pullback.hom_ext
    · exact congrArg Subtype.val hxx
    · rw [x.2, x'.2]
  letI := hfinite
  refine (Set.finite_range (pullback.fst p t)).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)

private theorem finite_fibre_of_finite_group_kernel {C : Type*} [Category C]
    [CartesianMonoidalCategory C] {G A T : C} [GrpObj G] [GrpObj A]
    (p : A ⟶ G) [IsMonHom p] (h : Finite {x : T ⟶ A // x ≫ p = 1})
    (y : T ⟶ G) : Finite {x : T ⟶ A // x ≫ p = y} := by
  letI := h
  rcases isEmpty_or_nonempty {x : T ⟶ A // x ≫ p = y} with he | ⟨⟨x₀, hx₀⟩⟩
  · infer_instance
  · refine Finite.of_injective (β := {x : T ⟶ A // x ≫ p = 1})
      (fun x => ⟨x₀⁻¹ * x.1, by
        rw [MonObj.mul_comp, GrpObj.inv_comp, hx₀, x.2, inv_mul_cancel]⟩) ?_
    intro a b hab
    exact Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))

/-- Finiteness of the actual geometric kernel controls every geometric
fibre of the same group-scheme morphism. -/
theorem locallyQuasiFinite_of_finite_group_kernel {S : Scheme.{0}}
    (A G : Over S) [GrpObj A] [GrpObj G] (p : A ⟶ G) [IsMonHom p]
    [LocallyOfFiniteType p.left]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
      Finite {x : Over.mk t ⟶ A // x ≫ p = 1}) : LocallyQuasiFinite p.left := by
  refine locallyQuasiFinite_of_geometric_fibres p.left fun k _ _ y => ?_
  let t : Sp k ⟶ S := y ≫ G.hom
  let y' : Over.mk t ⟶ G := Over.homMk y rfl
  letI : Finite {x : Over.mk t ⟶ A // x ≫ p = y'} :=
    finite_fibre_of_finite_group_kernel p (h k t) y'
  refine Finite.of_injective (β := {x : Over.mk t ⟶ A // x ≫ p = y'})
    (fun x => ⟨Over.homMk x.1 (by
      change x.1 ≫ A.hom = y ≫ G.hom
      rw [← Over.w p, ← Category.assoc, x.2]), Over.OverMorphism.ext x.2⟩) ?_
  intro a b hab
  exact Subtype.ext (congrArg (fun z => z.1.left) hab)

/-- The original elliptic graph projection is locally quasi-finite:
its finite geometric kernel is proved, not added as a hypothesis.
This is the next step toward integral extension of the CM action. -/
theorem elliptic_graph_projection_locallyQuasiFinite
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (G Ga : Over (Sp R)) [GrpObj G] [GrpObj Ga] [IsCommMonObj G] [IsCommMonObj Ga]
    [Flat G.hom] [Flat Ga.hom] [LocallyOfFiniteType G.hom] [LocallyOfFiniteType Ga.hom]
    [IsSeparated Ga.hom] (W : _root_.WeierstrassCurve R) [W.IsElliptic]
    (io : Ga ⟶ G ⊗ schemeOver W) [IsMonHom io] [IsClosedImmersion io.left]
    [IsIso ((Over.pullback (spMap (algebraMap R K))).map (io ≫ fst G (schemeOver W)))] :
    LocallyQuasiFinite (io ≫ fst G (schemeOver W)).left := by
  have hp : LocallyOfFiniteType (fst G (schemeOver W)).left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom (schemeOver W).hom))
  have hp' : LocallyOfFiniteType (io ≫ fst G (schemeOver W)).left := by
    rw [Over.comp_left]
    infer_instance
  exact locallyQuasiFinite_of_finite_group_kernel Ga G (io ≫ fst G (schemeOver W))
    (finite_geometric_elliptic_graph_kernel R K G Ga W io)

end RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

end

