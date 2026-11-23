import RHLean.Geometry.NativeCMWeierstrassRelativePoints
import RHLean.Geometry.NativeCMWeierstrassGraphKernelTorsion

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

open WeierstrassCurve

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
  letI : Algebra R k := φ.hom.toAlgebra
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
      simpa only [map_natCast] using hnR.map (algebraMap R k)
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

end RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

end

