import Mathlib

/-!
# Construct finite faithfully flat covers carrying the required point lifts

The cover algebra is the ring of global sections of the actual scheme
pullback. This is the source's construction for lifting torsion points
through multiplication by N. A finite family is lifted on one cover by
successive base change; no point-lifting or cover-existence law is assumed.

The scheme morphism must genuinely be finite, flat and surjective. In the
abelian-scheme application these properties belong to multiplication by N;
this module neither replaces that scheme by a scalar-root model nor proves
the existence of the polarized moduli object.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/`
`ExistsFaithfullyFlatRoots.lean`, `FlatRoots.exists_lift`,
`FlatRoots.exists_lifts`.
The source archive/mirror states no license; this notice preserves
attribution without assigning a new license.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace RHLean.Geometry.NativeTheta.FiniteFlatCover

abbrev Sp (S : Type) [CommRing S] : Scheme.{0} := Spec (CommRingCat.of S)

abbrev spMap {S B : Type} [CommRing S] [CommRing B] (φ : S →+* B) : Sp B ⟶ Sp S :=
  Spec.map (CommRingCat.ofHom φ)

/-- Lift an actual affine point through the given finite flat surjection.
The witnessing algebra is constructed from the affine scheme pullback. -/
theorem exists_lift {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] [Surjective f]
    (S : Type) [CommRing S] (t : Sp S ⟶ Y) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : Sp B ⟶ X),
      φ.FaithfullyFlat ∧ w ≫ f = spMap φ ≫ t := by
  have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
  let e := (pullback t f).isoSpec
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (e.inv ≫ pullback.fst t f)
  have hff : ψ.hom.FaithfullyFlat := by
    rw [← flat_and_surjective_SpecMap_iff, hψ]
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨Γ(pullback t f, ⊤), inferInstance, ψ.hom,
    e.inv ≫ pullback.snd t f, hff, ?_⟩
  change _ = Spec.map ψ ≫ t
  rw [hψ, Category.assoc, Category.assoc, pullback.condition]

theorem spMap_comp {R S B : Type} [CommRing R] [CommRing S] [CommRing B]
    (φ : R →+* S) (ψ : S →+* B) : spMap (ψ.comp φ) = spMap ψ ≫ spMap φ := by
  rw [← Spec.map_comp]
  rfl

/-- Construct one faithfully flat cover on which all the selected points
lift through the same actual morphism. -/
theorem exists_lifts {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] [Surjective f]
    (S : Type) [CommRing S] (J : Type)
    (t : J → (Sp S ⟶ Y)) (s : Finset J) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B),
      φ.FaithfullyFlat ∧ ∀ i ∈ s, ∃ w : Sp B ⟶ X,
        w ≫ f = spMap φ ≫ t i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨S, inferInstance, RingHom.id S,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert j s _ ih =>
    obtain ⟨B, _, φ, hφ, h⟩ := ih
    obtain ⟨C, _, ψ, w, hψ, hw⟩ := exists_lift f B (spMap φ ≫ t j)
    refine ⟨C, inferInstance, ψ.comp φ,
      RingHom.FaithfullyFlat.stableUnderComposition φ ψ hφ hψ, fun i hi => ?_⟩
    rw [spMap_comp, Category.assoc]
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨w, hw⟩
    · obtain ⟨v, hv⟩ := h i hi
      exact ⟨spMap ψ ≫ v, by rw [Category.assoc, hv]⟩

/-- The complete finite family is realized on a single constructed cover. -/
theorem exists_fintype_lifts {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsFinite f] [Flat f] [Surjective f]
    (S : Type) [CommRing S] (J : Type) [Fintype J] (t : J → (Sp S ⟶ Y)) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (Sp B ⟶ X)),
      φ.FaithfullyFlat ∧ ∀ i, w i ≫ f = spMap φ ≫ t i := by
  obtain ⟨B, _, φ, hφ, h⟩ := exists_lifts f S J t Finset.univ
  choose w hw using fun i => h i (Finset.mem_univ i)
  exact ⟨B, inferInstance, φ, w, hφ, hw⟩

end RHLean.Geometry.NativeTheta.FiniteFlatCover

end
