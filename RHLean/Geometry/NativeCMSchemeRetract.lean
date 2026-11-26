import Mathlib

/-!
# Smooth, proper, and geometrically connected scheme retracts

These are proved geometric properties of an actual split scheme
retraction. Smoothness is checked on affine neighbourhoods using the
corresponding split algebra maps; properness uses the closed immersion
of a section; connectedness is carried through every field base change.

Source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`src/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/`
`LocallyOfFinitePresentation.lean`. Only the declaration cut needed for
these three properties is reconstructed here. The archive states no
license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace RHLean.Geometry.NativeCM.SchemeTheory.Retract

section Algebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (s : A →ₐ[R] B) (p : B →ₐ[R] A) (h : p.comp s = AlgHom.id R A)

include h

theorem algHom_surjective : Function.Surjective p :=
  fun a => ⟨s a, congrArg (fun q : A →ₐ[R] A => q a) h⟩

theorem fg_ker [Algebra.FiniteType R B] : (RingHom.ker p.toRingHom).FG := by
  classical
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := B)
  refine ⟨t.image fun b => b - s (p b), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hx
    have hp : p (s (p b)) = p b := congrArg (fun q : A →ₐ[R] A => q (p b)) h
    simp [RingHom.mem_ker, hp]
  · set I : Ideal B := Ideal.span (↑(t.image fun b => b - s (p b)) : Set B)
    have key : Ideal.Quotient.mkₐ R I = (Ideal.Quotient.mkₐ R I).comp (s.comp p) := by
      refine AlgHom.ext_of_adjoin_eq_top ht fun b hb => ?_
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq]
      exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hb))
    intro b hb
    have hb' : p b = 0 := hb
    have he := congrArg (fun q : B →ₐ[R] B ⧸ I => q b) key
    simp only [AlgHom.comp_apply, hb', map_zero, Ideal.Quotient.mkₐ_eq_mk] at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp he

theorem finitePresentation_algebra [Algebra.FinitePresentation R B] :
    Algebra.FinitePresentation R A :=
  Algebra.FinitePresentation.of_surjective (algHom_surjective s p h) (fg_ker s p h)

theorem formallySmooth_algebra [Algebra.FormallySmooth R B] : Algebra.FormallySmooth R A := by
  refine Algebra.FormallySmooth.of_split p
    ((Ideal.Quotient.mkₐ R (RingHom.ker p.toRingHom ^ 2)).comp s) ?_
  ext a
  exact congrArg (fun q : A →ₐ[R] A => q a) h

theorem smooth_algebra [Algebra.Smooth R B] : Algebra.Smooth R A :=
  ⟨formallySmooth_algebra s p h, finitePresentation_algebra s p h⟩

end Algebra

section Local

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {i : X ⟶ Y} {r : Y ⟶ X}

theorem section_comp (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) : i ≫ g = f := by
  rw [← hr, reassoc_of% hir]

theorem apply_apply (hir : i ≫ r = 𝟙 X) (x : X) : r (i x) = x := by
  rw [← Scheme.Hom.comp_apply, hir]
  rfl

/-- Affine charts on which the actual retraction is still split. -/
theorem exists_affine_le (hir : i ≫ r = 𝟙 X) (x : X) (O : X.Opens) (hx : x ∈ O) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧
      U ≤ O ∧ U ≤ i ⁻¹ᵁ V ∧ V ≤ r ⁻¹ᵁ U := by
  obtain ⟨U₀, hU₀, hxU₀, hU₀O⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  have hix : i x ∈ r ⁻¹ᵁ U₀ := by
    change r (i x) ∈ U₀
    rwa [apply_apply hir]
  obtain ⟨V₀, hV₀, hxV₀, hV₀U₀⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hix
  obtain ⟨a, ha, hxa⟩ := IsAffineOpen.exists_basicOpen_le hU₀ (V := i ⁻¹ᵁ V₀) ⟨x, hxV₀⟩ hxU₀
  have hV : Y.basicOpen (r.appLE U₀ V₀ hV₀U₀ a) = V₀ ⊓ r ⁻¹ᵁ X.basicOpen a := by
    simp [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen]
  refine ⟨X.basicOpen a, Y.basicOpen (r.appLE U₀ V₀ hV₀U₀ a),
    IsAffineOpen.basicOpen hU₀ a, IsAffineOpen.basicOpen hV₀ _, hxa,
    (X.basicOpen_le a).trans hU₀O, ?_, ?_⟩
  · rw [hV]
    intro z hz
    refine ⟨ha hz, ?_⟩
    change r (i z) ∈ X.basicOpen a
    rwa [apply_apply hir]
  · rw [hV]
    exact inf_le_right

theorem appLE_comp_appLE (hir : i ≫ r = 𝟙 X) {U : X.Opens} {V : Y.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hVU : V ≤ r ⁻¹ᵁ U) :
    r.appLE U V hVU ≫ i.appLE V U hUV = 𝟙 Γ(X, U) := by
  rw [Scheme.Hom.appLE_comp_appLE]
  generalize_proofs e
  revert e
  rw [hir]
  intro _
  exact (Category.id_comp _).trans (X.presheaf.map_id _)

theorem base_appLE_comp_retraction (hr : r ≫ f = g) {U : X.Opens} {V : Y.Opens}
    {W : S.Opens} (hVU : V ≤ r ⁻¹ᵁ U) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    f.appLE W U hUW ≫ r.appLE U V hVU = g.appLE W V hVW := by
  subst hr
  rw [Scheme.Hom.appLE_comp_appLE]

theorem base_appLE_comp_section (hi : i ≫ g = f) {U : X.Opens} {V : Y.Opens}
    {W : S.Opens} (hUV : U ≤ i ⁻¹ᵁ V) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    g.appLE W V hVW ≫ i.appLE V U hUV = f.appLE W U hUW := by
  subst hi
  rw [Scheme.Hom.appLE_comp_appLE]

theorem exists_algHom_retract (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
    {U : X.Opens} {V : Y.Opens} {W : S.Opens}
    (hUV : U ≤ i ⁻¹ᵁ V) (hVU : V ≤ r ⁻¹ᵁ U)
    (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    let _ := (f.appLE W U hUW).hom.toAlgebra
    let _ := (g.appLE W V hVW).hom.toAlgebra
    ∃ (s : Γ(X, U) →ₐ[Γ(S, W)] Γ(Y, V)) (p : Γ(Y, V) →ₐ[Γ(S, W)] Γ(X, U)),
      s.toRingHom = (r.appLE U V hVU).hom ∧ p.toRingHom = (i.appLE V U hUV).hom ∧
        p.comp s = AlgHom.id _ _ := by
  let _ := (f.appLE W U hUW).hom.toAlgebra
  let _ := (g.appLE W V hVW).hom.toAlgebra
  refine ⟨⟨(r.appLE U V hVU).hom, fun a => ?_⟩,
    ⟨(i.appLE V U hUV).hom, fun a => ?_⟩, rfl, rfl, ?_⟩
  · exact congrArg (fun q : Γ(S, W) ⟶ Γ(Y, V) => q a)
      (base_appLE_comp_retraction hr hVU hUW hVW)
  · exact congrArg (fun q : Γ(S, W) ⟶ Γ(X, U) => q a)
      (base_appLE_comp_section (section_comp hir hr) hUV hUW hVW)
  · ext a
    exact congrArg (fun q : Γ(X, U) ⟶ Γ(X, U) => q a) (appLE_comp_appLE hir hUV hVU)

theorem exists_baseChange (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
    {T X' Y' : Scheme.{u}} {y : T ⟶ S} {a : X' ⟶ X} {f' : X' ⟶ T}
    (hX : IsPullback a f' f y) {b : Y' ⟶ Y} {g' : Y' ⟶ T}
    (hY : IsPullback b g' g y) :
    ∃ (i' : X' ⟶ Y') (r' : Y' ⟶ X'), i' ≫ r' = 𝟙 X' ∧ r' ≫ f' = g' ∧
      i' ≫ b = a ≫ i ∧ r' ≫ a = b ≫ r := by
  refine ⟨hY.lift (a ≫ i) f' (by rw [Category.assoc, section_comp hir hr, hX.w]),
    hX.lift (b ≫ r) g' (by rw [Category.assoc, hr, hY.w]), ?_, by simp, by simp, by simp⟩
  apply hX.hom_ext <;> simp [hir]

end Local

section Smooth

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {i : X ⟶ Y} {r : Y ⟶ X}

theorem of_hasRingHomProperty (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R A : Type u} [CommRing R] [CommRing A], (R →+* A) → Prop}
    [HasRingHomProperty P Q]
    (hQ : ∀ {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (s : A →ₐ[R] B) (p : B →ₐ[R] A), p.comp s = AlgHom.id R A →
        Q (algebraMap R B) → Q (algebraMap R A))
    (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) (hg : P g) : P f := by
  wlog hS : IsAffine S generalizing X Y S
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) S.affineCover]
    intro j
    obtain ⟨i', r', h₁, h₂, -, -⟩ := exists_baseChange hir hr
      (IsPullback.of_hasPullback f (S.affineCover.f j))
      (IsPullback.of_hasPullback g (S.affineCover.f j))
    exact this h₁ h₂ (IsZariskiLocalAtTarget.of_isPullback (.of_hasPullback _ _) hg) inferInstance
  choose U V hU hV hxU _ hUV hVU using fun x => exists_affine_le hir x ⊤ trivial
  refine HasRingHomProperty.of_iSup_eq_top (fun x => ⟨U x, hU x⟩) ?_ fun x => ?_
  · exact eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · obtain ⟨s, p, -, -, h⟩ := exists_algHom_retract hir hr
      (W := ⊤) (hUV x) (hVU x) le_top le_top
    let _ := (f.appLE ⊤ (U x) le_top).hom.toAlgebra
    let _ := (g.appLE ⊤ (V x) le_top).hom.toAlgebra
    exact hQ s p h
      (HasRingHomProperty.appLE P g hg ⟨⊤, isAffineOpen_top S⟩ ⟨V x, hV x⟩ le_top)

theorem smooth (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) [hg : Smooth g] : Smooth f :=
  of_hasRingHomProperty @Smooth (fun s p h H => by
    rw [RingHom.smooth_algebraMap] at H ⊢
    exact smooth_algebra s p h) hir hr hg

end Smooth

section Global

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {i : X ⟶ Y} {r : Y ⟶ X}

theorem surjective_retraction (hir : i ≫ r = 𝟙 X) : Surjective r :=
  ⟨fun x => ⟨i x, apply_apply hir x⟩⟩

theorem connectedSpace (hir : i ≫ r = 𝟙 X) [ConnectedSpace Y] : ConnectedSpace X :=
  (surjective_retraction hir).surj.connectedSpace r.continuous

theorem isClosedImmersion_section (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
    [IsSeparated g] : IsClosedImmersion i := by
  subst hr
  have : IsSeparated r := IsSeparated.of_comp r f
  have : IsClosedImmersion (i ≫ r) := by rw [hir]; infer_instance
  exact IsClosedImmersion.of_comp i r

theorem isProper (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) [IsProper g] : IsProper f := by
  have := isClosedImmersion_section hir hr
  rw [← section_comp hir hr]
  infer_instance

theorem geometrically (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
    (P : ObjectProperty Scheme.{u})
    (hP : ∀ {A B : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ A), a ≫ b = 𝟙 A → P B → P A)
    (hg : AlgebraicGeometry.geometrically P g) : AlgebraicGeometry.geometrically P f := by
  intro K _ y Z fst snd h
  obtain ⟨i', r', h₁, -, -, -⟩ := exists_baseChange hir hr h (IsPullback.of_hasPullback g y)
  exact hP i' r' h₁ (pullback_of_geometrically hg K y)

theorem geometricallyConnected (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g)
    [hg : GeometricallyConnected g] : GeometricallyConnected f :=
  ⟨geometrically hir hr _ (fun _ _ h _ => connectedSpace h) hg.1⟩

end Global

end RHLean.Geometry.NativeCM.SchemeTheory.Retract

end
