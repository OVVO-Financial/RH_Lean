import RHLean.Geometry.NativeCMLineBundleAtlas

/-!
# Actual regular component sections

A clopen subset of a scheme gives an idempotent in its actual ring of
global regular functions. The proof glues 1 and 0 with the structure sheaf.
Multiplication by this function cuts a section of the original line-bundle
atlas, preserves the transition equations, and is an idempotent operation.
At every field-valued point the resulting section is exactly the original
section on the chosen component set and zero elsewhere.

These are genuine scheme sections. The intended period-component sets,
their geometric moduli realization, and their Petersson masses remain
separate construction steps.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsCoeffFieldIdempotentCuttingPeriodSpaces.lean
(`exists_indicator_function`),
src/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HomExtOfGeometric.lean
(`fnAt_comp`, `fnAt_spMap_comp`), and
src/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ValAtLem.lean
(`valAt'_res`). The source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open RHLean.Geometry.NativeCM.SchemeTheory
open scoped Classical

namespace RHLean.Geometry.NativeTheta.Cusp.ComponentSections

variable {X Y : Scheme.{0}}

/-- Evaluation of an actual regular function along a ring-valued point. -/
def eval {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem eval_res {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ X)
    {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    eval x V h (resG X hVU f) = eval x U (fun p hp => hVU (h hp)) f := by
  unfold eval resG
  simp only [RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- The actual global evaluation map, with no convention outside a chart. -/
def evalTop {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ X) :
    Γ(X, ⊤) →+* S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp x.appTop.hom

theorem evalTop_comp {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ X)
    (f : X ⟶ Y) (a : Γ(Y, ⊤)) :
    evalTop (x ≫ f) a = evalTop x (f.appTop.hom a) := by
  simp only [evalTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

theorem evalTop_specMap_comp {S T : Type} [CommRing S] [CommRing T]
    (φ : S →+* T) (x : Spec (CommRingCat.of S) ⟶ X) (a : Γ(X, ⊤)) :
    evalTop (Spec.map (CommRingCat.ofHom φ) ≫ x) a = φ (evalTop x a) := by
  rw [evalTop_comp]
  exact congrArg (fun q => q.hom (x.appTop.hom a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

/-- The source's component indicator is constructed in Γ(X,⊤) by gluing.
The value statement holds at every field-valued point. -/
theorem exists_indicator_function (U : Set X) (hU : IsClopen U) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ X),
        (x (IsLocalRing.closedPoint K) ∈ U →
          eval x ⊤ (by intro p hp; trivial) e = 1) ∧
        (x (IsLocalRing.closedPoint K) ∉ U →
          eval x ⊤ (by intro p hp; trivial) e = 0) := by
  let V : Bool → X.Opens := fun b => match b with
    | true => ⟨U, hU.2⟩
    | false => ⟨Uᶜ, hU.1.isOpen_compl⟩
  let sf : ∀ b, Γ(X, V b) := fun b => match b with
    | true => 1
    | false => 0
  have hcov : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases h : x ∈ U
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have hsub : ∀ W : X.Opens, W = ⊥ → Subsingleton Γ(X, W) := by
    rintro _ rfl
    infer_instance
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro a b
    cases a <;> cases b
    · simp [sf]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · simp [sf]
  obtain ⟨e, he⟩ : ∃ e : Γ(X, ⊤),
      ∀ b, X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e = sf b :=
    (X.sheaf.existsUnique_gluing' V ⊤ (fun b => homOfLE le_top) hcov sf hcomp).exists
  have hpt : ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ X) (b : Bool),
      x (IsLocalRing.closedPoint K) ∈ V b → ⊤ ≤ x ⁻¹ᵁ V b := by
    intro K _ x b h z _
    rwa [Subsingleton.elim (α := PrimeSpectrum K) z (IsLocalRing.closedPoint K)]
  refine ⟨e, ?_, fun K _ x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · show e * e = e
    refine X.sheaf.eq_of_locally_eq' V ⊤ (fun b => homOfLE le_top) hcov _ _ fun b => ?_
    show X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op (e * e) =
      X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e
    rw [map_mul, he]
    cases b <;> simp [sf]
  · refine (eval_res x le_top (hpt K x true h) e).symm.trans ?_
    change eval x (V true) (hpt K x true h)
      (X.presheaf.map (homOfLE (le_top : V true ≤ ⊤)).op e) = 1
    rw [he]
    exact map_one _
  · refine (eval_res x le_top (hpt K x false h) e).symm.trans ?_
    change eval x (V false) (hpt K x false h)
      (X.presheaf.map (homOfLE (le_top : V false ≤ ⊤)).op e) = 0
    rw [he]
    exact map_zero _

private theorem section_ext {L : LB X} {s t : L.Sec} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s with
  | mk s hs =>
    cases t with
    | mk t ht =>
      have he : s = t := funext h
      subst t
      rfl

/-- Multiplication takes place in the original chart rings and respects
the original line-bundle transition units. -/
def mulSection {L : LB X} (e : Γ(X, ⊤)) (s : L.Sec) : L.Sec where
  f i := resG X le_top e * s.f i
  compat i j := by
    change resG X inf_le_left (resG X le_top e * s.f i) =
      (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
        resG X inf_le_right (resG X le_top e * s.f j)
    rw [map_mul, map_mul, resG_resG, resG_resG]
    have hs := s.compat i j
    change resG X inf_le_left (s.f i) =
      (L.g i j : Γ(X, L.U i ⊓ L.U j)) * resG X inf_le_right (s.f j) at hs
    rw [hs]
    ring

theorem mulSection_mul {L : LB X} (e f : Γ(X, ⊤)) (s : L.Sec) :
    mulSection e (mulSection f s) = mulSection (e * f) s := by
  apply section_ext
  intro i
  change _ * (_ * _) = resG X le_top (e * f) * _
  rw [map_mul, mul_assoc]

theorem mulSection_idempotent {L : LB X} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    Function.Idempotent (mulSection (L := L) e) := by
  intro s
  rw [mulSection_mul, he.eq]

theorem eval_mulSection {S : Type} [CommRing S] {L : LB X}
    (x : Spec (CommRingCat.of S) ⟶ X) (i : L.ι) (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (e : Γ(X, ⊤)) (s : L.Sec) :
    eval x (L.U i) hi ((mulSection e s).f i) =
      eval x ⊤ (by intro p hp; trivial) e * eval x (L.U i) hi (s.f i) := by
  change eval x (L.U i) hi (resG X le_top e * s.f i) = _
  rw [map_mul, eval_res]

/-- An actual global section is cut to a chosen clopen component set.
The cut is exact at every field-valued point and contracts each complex
chart norm. No moduli component or Petersson measure is postulated. -/
theorem exists_component_section {L : LB X} (U : Set X) (hU : IsClopen U) (s : L.Sec) :
    ∃ (e : Γ(X, ⊤)) (t : L.Sec), IsIdempotentElem e ∧ t = mulSection e s ∧
      (∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ X) (i : L.ι)
          (hi : ⊤ ≤ x ⁻¹ᵁ L.U i),
        eval x (L.U i) hi (t.f i) =
          if x (IsLocalRing.closedPoint K) ∈ U then eval x (L.U i) hi (s.f i) else 0) ∧
      ∀ (x : Spec (CommRingCat.of ℂ) ⟶ X) (i : L.ι) (hi : ⊤ ≤ x ⁻¹ᵁ L.U i),
        ‖eval x (L.U i) hi (t.f i)‖ ≤ ‖eval x (L.U i) hi (s.f i)‖ := by
  classical
  obtain ⟨e, he, hval⟩ := exists_indicator_function U hU
  have hcut : ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ X) (i : L.ι)
      (hi : ⊤ ≤ x ⁻¹ᵁ L.U i),
      eval x (L.U i) hi ((mulSection e s).f i) =
        if x (IsLocalRing.closedPoint K) ∈ U then eval x (L.U i) hi (s.f i) else 0 := by
    intro K _ x i hi
    rw [eval_mulSection]
    split_ifs with h
    · rw [(hval K x).1 h, one_mul]
    · rw [(hval K x).2 h, zero_mul]
  refine ⟨e, mulSection e s, he, rfl, hcut, fun x i hi => ?_⟩
  rw [hcut]
  split_ifs
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

end RHLean.Geometry.NativeTheta.Cusp.ComponentSections
