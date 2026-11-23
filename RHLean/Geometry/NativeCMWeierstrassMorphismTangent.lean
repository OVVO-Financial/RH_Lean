import RHLean.Geometry.NativeCMWeierstrassSectionJet

/-!
# The actual scheme action on the original epsilon vector

The regular-section derivative comparison is applied to an actual morphism
of the same Weierstrass group scheme. If that morphism multiplies the actual
complex exponential by beta, its literal epsilon coordinate maps to beta.
The proof works over any reduced coefficient ring embedded in the complex
numbers. Thus an eventual integral extension uses this same result and the
same integral vector, without assuming a Lie-action compatibility law.

This is a native consumer of the local-ring proof reconstructed from
Levent Alpöge (with Claude), CocoSgt/riemann-hypothesis-lean@
7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
`src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdealValDifferentEqOne.lean`.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Filter MonoidalCategory
open scoped Classical Topology

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassMorphismTangent

open WeierstrassCurve WeierstrassLie SectionPoints WeierstrassSectionJet

section BaseChangeVector

variable {R : Type} [CommRing R] (V : _root_.WeierstrassCurve R)

theorem vec_top_le_coordOpen (c : R) : ⊤ ≤ vec V c ⁻¹ᵁ coordOpen V 1 := by
  rw [vec, ptHom_preimage_coordOpen]
  simp

theorem evalPt_vec_ratio (c : R) (h : ⊤ ≤ vec V c ⁻¹ᵁ coordOpen V 1) :
    evalPt (vec V c) (coordOpen V 1) h (ratio V 1 0) = -TrivSqZeroExt.inr c := by
  have e := evalPt_ptHom_ratioOn_mul (algebraMap R (DualNumber R))
    ![TrivSqZeroExt.inr c, -1, 0] (isUnimodularSol_origin (equation_inr V c))
    le_rfl h 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg_one] at e
  exact neg_eq_iff_eq_neg.mp e

theorem vec_mapHom (σ : R →+* ℂ) (c : R) :
    vec (V.map σ) (σ c) ≫ mapHom V σ rfl =
      spMap (WeierstrassTangent.dualMap σ) ≫ vec V c := by
  rw [vec, ptHom_mapHom, vec, SpecMap_ptHom]
  apply ptHom_congr V _ _ _
  · ext a <;> simp [WeierstrassTangent.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 i
    fin_cases i
    · ext <;> simp [WeierstrassTangent.dualMap]
    · simp
    · simp

theorem evalPt_extended_vec_ratio (σ : R →+* ℂ) (c : R)
    (h : ⊤ ≤ (spMap (WeierstrassTangent.dualMap σ) ≫ vec V c) ⁻¹ᵁ coordOpen V 1) :
    (evalPt (spMap (WeierstrassTangent.dualMap σ) ≫ vec V c)
      (coordOpen V 1) h (ratio V 1 0)).snd = -σ c := by
  rw [evalPt_spMap_comp (WeierstrassTangent.dualMap σ) (vec V c) _
    (vec_top_le_coordOpen V c) h, evalPt_vec_ratio]
  simp [WeierstrassTangent.dualMap]

end BaseChangeVector

section ActualMorphism

variable {R : Type} [CommRing R] [_root_.IsReduced R] [Algebra R ℂ]
    (V : _root_.WeierstrassCurve R) [V.IsElliptic]
    (L : PeriodPair) (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • (V.baseChange ℂ).baseChange ℂ = Weierstrass.latticeCurve L)
    (f : schemeOver V ⟶ schemeOver V) [CategoryTheory.IsMonHom f]

/-- The exact exponential comparison forces the algebraic epsilon
coordinate. The coefficient c is constructed from the actual tangent map. -/
theorem exists_tangent_scalar (β : ℂ)
    (hf : ∀ z : ℂ,
      expPoint L (V.baseChange ℂ) C hC z ≫ mapHom V (algebraMap R ℂ) rfl ≫ f.left =
        expPoint L (V.baseChange ℂ) C hC (β * z) ≫ mapHom V (algebraMap R ℂ) rfl) :
    ∃ c : R, (integralVector V).left ≫ f.left = vec V c ∧ algebraMap R ℂ c = β := by
  let j := mapHom V (algebraMap R ℂ) rfl
  have hf0 : zero V ≫ f.left = zero V := by
    have h := congrArg Over.Hom.left (IsMonHom.one_hom f)
    simpa only [Over.comp_left, one_left] using h
  have hw : f.left ≫ toSpec V = toSpec V := Over.w f
  have hg : (vec V 1 ≫ f.left) ≫ toSpec V = spMap (algebraMap R (DualNumber R)) := by
    rw [Category.assoc, hw]
    exact ptHom_toSpec V _ _ _
  have hzero : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (vec V 1 ≫ f.left) = zero V := by
    rw [← Category.assoc, fst_vec, hf0]
  obtain ⟨c, hc⟩ := exists_eq_vec V (vec V 1 ≫ f.left) hg hzero
  refine ⟨c, hc, ?_⟩
  have hvj : vec (V.baseChange ℂ) 1 ≫ j =
      spMap (WeierstrassTangent.dualMap (algebraMap R ℂ)) ≫ vec V 1 := by
    simpa only [map_one] using vec_mapHom V (algebraMap R ℂ) 1
  have hvjf : vec (V.baseChange ℂ) 1 ≫ j ≫ f.left =
      spMap (WeierstrassTangent.dualMap (algebraMap R ℂ)) ≫ vec V c := by
    rw [← Category.assoc, hvj, Category.assoc, hc]
  let U := coordOpen V 1
  let s := ratio V 1 0
  have hJ : ⊤ ≤ (vec (V.baseChange ℂ) 1 ≫ j) ⁻¹ᵁ U := by
    rw [hvj]
    exact fun p _ => vec_top_le_coordOpen V 1 (Set.mem_univ _)
  have hF : ⊤ ≤ (vec (V.baseChange ℂ) 1 ≫ j ≫ f.left) ⁻¹ᵁ U := by
    rw [hvjf]
    exact fun p _ => vec_top_le_coordOpen V c (Set.mem_univ _)
  have hJ' : ⊤ ≤ vec (V.baseChange ℂ) 1 ⁻¹ᵁ (j ⁻¹ᵁ U) := by
    rwa [Scheme.Hom.comp_preimage] at hJ
  have hF' : ⊤ ≤ vec (V.baseChange ℂ) 1 ⁻¹ᵁ ((j ≫ f.left) ⁻¹ᵁ U) := by
    rwa [Scheme.Hom.comp_preimage] at hF
  have ej : (evalPt (vec (V.baseChange ℂ) 1) (j ⁻¹ᵁ U) hJ' ((j.app U).hom s)).snd = -1 := by
    rw [← evalPt_comp _ j U hJ hJ']
    have key : ∀ (v : Sp (DualNumber ℂ) ⟶ scheme V) (hv : ⊤ ≤ v ⁻¹ᵁ U),
        v = spMap (WeierstrassTangent.dualMap (algebraMap R ℂ)) ≫ vec V 1 →
        (evalPt v U hv s).snd = -1 := by
      rintro _ hv rfl
      simpa only [map_one] using evalPt_extended_vec_ratio V (algebraMap R ℂ) 1 hv
    exact key _ hJ hvj
  have ef : (evalPt (vec (V.baseChange ℂ) 1) ((j ≫ f.left) ⁻¹ᵁ U) hF'
      (((j ≫ f.left).app U).hom s)).snd = -algebraMap R ℂ c := by
    rw [← evalPt_comp _ (j ≫ f.left) U hF hF']
    have key : ∀ (v : Sp (DualNumber ℂ) ⟶ scheme V) (hv : ⊤ ≤ v ⁻¹ᵁ U),
        v = spMap (WeierstrassTangent.dualMap (algebraMap R ℂ)) ≫ vec V c →
        (evalPt v U hv s).snd = -algebraMap R ℂ c := by
      rintro _ hv rfl
      exact evalPt_extended_vec_ratio V (algebraMap R ℂ) c hv
    exact key _ hF hvjf
  have hdj : HasDerivAt
      (fun z => value (expPoint L (V.baseChange ℂ) C hC z ≫ j) U s)
      ((C.u : ℂ)⁻¹ * (-1)) 0 := by
    have hd := section_derivative L (V.baseChange ℂ) C hC (j ⁻¹ᵁ U) hJ' ((j.app U).hom s)
    rw [ej] at hd
    exact hd.congr_of_eventuallyEq (Eventually.of_forall fun z =>
      (value_comp (expPoint L (V.baseChange ℂ) C hC z) j U s).symm)
  have hdf : HasDerivAt
      (fun z => value (expPoint L (V.baseChange ℂ) C hC z ≫ j ≫ f.left) U s)
      ((C.u : ℂ)⁻¹ * (-algebraMap R ℂ c)) 0 := by
    have hd := section_derivative L (V.baseChange ℂ) C hC ((j ≫ f.left) ⁻¹ᵁ U) hF'
      (((j ≫ f.left).app U).hom s)
    rw [ef] at hd
    exact hd.congr_of_eventuallyEq (Eventually.of_forall fun z =>
      (value_comp (expPoint L (V.baseChange ℂ) C hC z) (j ≫ f.left) U s).symm)
  have hdj' : HasDerivAt
      (fun z => value (expPoint L (V.baseChange ℂ) C hC z ≫ j) U s)
      ((C.u : ℂ)⁻¹ * (-1)) (β * 0) := by simpa only [mul_zero] using hdj
  have hmul := hdj'.comp 0 ((hasDerivAt_id (0 : ℂ)).const_mul β)
  have hmul' : HasDerivAt
      (fun z => value (expPoint L (V.baseChange ℂ) C hC z ≫ j ≫ f.left) U s)
      (((C.u : ℂ)⁻¹ * (-1)) * β) 0 :=
    hmul.congr_of_eventuallyEq (Eventually.of_forall fun z =>
      congrArg (fun x => value x U s) (hf z))
  have he := hdf.unique hmul'
  apply mul_left_cancel₀ (inv_ne_zero C.u.ne_zero)
  linear_combination -he

/-- Whenever the embedded scalar is the image of a specified base-ring
element, the same actual epsilon vector is multiplied by that element. -/
theorem integralVector_comp_eq_vec (hR : Function.Injective (algebraMap R ℂ)) (a : R)
    (hf : ∀ z : ℂ,
      expPoint L (V.baseChange ℂ) C hC z ≫ mapHom V (algebraMap R ℂ) rfl ≫ f.left =
        expPoint L (V.baseChange ℂ) C hC (algebraMap R ℂ a * z) ≫
          mapHom V (algebraMap R ℂ) rfl) :
    (integralVector V).left ≫ f.left = vec V a := by
  obtain ⟨c, hc, he⟩ := exists_tangent_scalar V L C hC f (algebraMap R ℂ a) hf
  exact hR he ▸ hc

end ActualMorphism

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassMorphismTangent

end
