import RHLean.Geometry.NativeCMWeierstrassGroupEndFlat
import RHLean.Geometry.NativeCMWeierstrassMultiplicationUnramified
import RHLean.Geometry.NativeCMWeierstrassFieldFlatDescent
import RHLean.Geometry.NativeCMWeierstrassDvrFlatness

/-!
# Actual invertible multiplication and torsion are etale

The proved infinitesimal multiplication calculation and actual field/DVR flatness criteria produce etale multiplication and its literal torsion pullback. This applies to the constructed flat graph group without a smoothness assumption.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsUnitNatCastSections.lean`.
The source archive states no license; attribution is retained without
assigning one. This native cut uses actual schemes and local rings, not
an abstract extension or abelian-variety supplier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

namespace MulEtaleDvr

variable {S : Scheme.{0}}

theorem mulN_eq_pow (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = 𝟙 G ^ n := by
  rw [← MulUnramified.comp_mulN, Category.id_comp]

theorem isMonHom_mulN (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : IsMonHom (mulN G n) where
  one_hom := by rw [MulUnramified.comp_mulN, one_eq_one, one_pow]
  mul_hom := by
    rw [MulUnramified.comp_mulN, mul_eq_mul, comp_mul, mul_pow]
    congr 1 <;> simp [MulUnramified.comp_mulN]

theorem pullback_map_mulN {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (n : ℕ) :
    (Over.pullback p).map (mulN G n) = mulN ((Over.pullback p).obj G) n := by
  rw [mulN_eq_pow, mulN_eq_pow, ← (Over.pullback p).map_id]
  exact map_pow (Over.pullback p).homMonoidHom _ _

theorem isPullback_torsion (G : Over S) [GrpObj G] (n : ℕ) :
    IsPullback (torsion.ι G n).left (torsion G n).hom (mulN G n).left η[G].left := by
  have h := (IsPullback.of_hasPullback (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).map (Over.forget S)
  have e : (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)).left = (torsion G n).hom :=
    (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN G n) (η : 𝟙_ (Over S) ⟶ G)))
  exact e ▸ h

theorem isUnit_natCast_sections {R : Type} [CommRing R] {n : ℕ} (hn : IsUnit (n : R)) :
    IsUnit (n : Γ(Sp R, ⊤)) := by
  simpa using! hn.map (Scheme.ΓSpecIso (.of R)).inv.hom

theorem flat_mulN_field (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] (n : ℕ)
    (hn : IsUnit (n : k)) (hG : LocallyOfFiniteType G.hom) : Flat (mulN G n).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) G G _ ?_
  rw [pullback_map_mulN]
  refine flat_of_formallyUnramified_grpEnd _ _ _ ?_ (isMonHom_mulN _ n)
    (formallyUnramified_mulN _ _ n (isUnit_natCast_sections ?_))
  · exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))
  · simpa using! hn.map (algebraMap k (AlgebraicClosure k))

theorem flat_pullback_mulN {T k : Type} [CommRing T] [Field k] (σ : T →+* k) (G : Over (Sp T))
    [GrpObj G] [IsCommMonObj G] (n : ℕ) (hn : IsUnit (n : T)) (hG : LocallyOfFiniteType G.hom) :
    Flat ((Over.pullback (spMap σ)).map (mulN G n)).left := by
  rw [pullback_map_mulN]
  refine flat_mulN_field k _ n (by simpa using! hn.map σ) ?_
  exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom _))

end MulEtaleDvr

open MulEtaleDvr in

theorem etale_mulN_torsion_dvr :
    ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (G : Over (Sp T)) [GrpObj G]
      [IsCommMonObj G] (n : ℕ), IsUnit (n : T) → Flat G.hom → LocallyOfFiniteType G.hom →
      Etale (mulN G n).left ∧ Etale (torsion G n).hom := by
  intro T _ _ _ G _ _ n hn hf hG
  have h1 : Flat (mulN G n).left :=
    flat_of_flat_fibres_dvr T (FractionRing T) G G _ hf hf hG hG
      (flat_pullback_mulN _ G n hn hG) (flat_pullback_mulN _ G n hn hG)
  have h2 := formallyUnramified_mulN _ G n (isUnit_natCast_sections hn)
  have h3 : LocallyOfFiniteType ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have h4 := locallyOfFiniteType_of_comp (mulN G n).left G.hom
  have h5 : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have h6 : LocallyOfFinitePresentation (mulN G n).left := inferInstance
  have h : Etale (mulN G n).left := Etale.of_formallyUnramified_of_flat _
  exact ⟨h, MorphismProperty.of_isPullback (P := @Etale) (isPullback_torsion G n) h⟩

/-- Properness makes the actual torsion scheme finite. In particular the
constructed integral elliptic seed has finite etale invertible torsion. -/
theorem finite_etale_torsion_dvr (R : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G]
    [Flat G.hom] [IsProper G.hom] (n : ℕ) (hn : IsUnit (n : R)) :
    IsFinite (torsion G n).hom ∧ Etale (torsion G n).hom := by
  obtain ⟨hm, ht⟩ := etale_mulN_torsion_dvr R G n hn inferInstance inferInstance
  have hc : IsProper ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have hp : IsProper (mulN G n).left := IsProper.of_comp _ G.hom
  have hf : IsFinite (mulN G n).left := IsFinite.of_isProper_of_locallyQuasiFinite _
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite)
    (MulEtaleDvr.isPullback_torsion G n) hf, ht⟩

end RHLean.Geometry.NativeCM.SchemeTheory.IntegralExtension

end
