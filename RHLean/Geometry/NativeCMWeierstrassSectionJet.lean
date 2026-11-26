import RHLean.Geometry.NativeCMAllPlaceTangentPeriod
import RHLean.Geometry.NativeCMWeierstrassSectionPoints

/-!
# Regular-section derivatives of the actual elliptic exponential

Native declaration cut from Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

- `src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdealValDifferentEqOne.lean`
- `src/Development/AbelianVarietyTheory/Proofs/ToricGeometry/TopLePreimageOfValAtNeZero.lean`

The derivative is proved on the literal origin coordinate ring, and then on
an arbitrary regular section by localization. The exponential belongs to the
same equation and coordinate change. Its derivative scale is exactly 1/u.
There is no general uniformization or derivative-comparison premise.
The source archive states no license; attribution is retained without assigning one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Polynomial
open scoped Classical Topology

namespace RHLean.Geometry.NativeCM.SchemeTheory.SectionPoints

variable {X Y : Scheme.{0}}

/-- Evaluation on its actual domain, extended by zero only to give a total
function on complex points. All derivative statements retain the open domain. -/
def value (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : ℂ :=
  if h : ⊤ ≤ x ⁻¹ᵁ U then evalPt x U h f else 0

theorem value_eq (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : value x U f = evalPt x U h f := by
  rw [value, dite_eq_left h]

theorem value_mul (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    value x U (f * g) = value x U f * value x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [value, dite_eq_left h, map_mul]
  · simp only [value, dite_eq_right h, mul_zero]

theorem value_res (x : Sp ℂ ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (f : Γ(X, U)) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    value x V (resG X e f) = value x U f := by
  rw [value_eq x hV, value_eq x (hV.trans (x.preimage_mono e))]
  exact evalPt_res x e _ hV f

theorem evalPt_comp {R : Type} [CommRing R] (x : Sp R ⟶ X) (f : X ⟶ Y)
    (U : Y.Opens) (h : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ U))
    (s : Γ(Y, U)) :
    evalPt (x ≫ f) U h s = evalPt x (f ⁻¹ᵁ U) h' ((f.app U).hom s) := by
  unfold evalPt
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem value_comp (x : Sp ℂ ⟶ X) (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    value x (f ⁻¹ᵁ U) ((f.app U).hom s) = value (x ≫ f) U s := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U := by rwa [Scheme.Hom.comp_preimage]
    rw [value_eq x h, value_eq (x ≫ f) h']
    exact (evalPt_comp x f U h' h s).symm
  · have h' : ¬ ⊤ ≤ (x ≫ f) ⁻¹ᵁ U := by rwa [Scheme.Hom.comp_preimage]
    rw [value, dite_eq_right h, value, dite_eq_right h']

theorem top_le_preimage_iff_mem (x : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U := by
  constructor
  · intro h
    exact h (Set.mem_univ _)
  · intro h p _
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim _ _
    subst this
    exact h

theorem top_le_preimage_basicOpen_iff (x : Sp ℂ ⟶ X) (U : X.Opens)
    (f : Γ(X, U)) : ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ value x U f ≠ 0 := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · have h1 : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f := by
      have := Scheme.basicOpen_appLE x ⊤ U h f
      rw [top_inf_eq] at this
      exact this
    rw [← h1, value_eq x h, evalPt, top_le_iff, CommRingCat.hom_comp, RingHom.comp_apply]
    generalize (x.appLE U ⊤ h).hom f = g
    rw [← isUnit_iff_ne_zero]
    constructor
    · intro hg
      have : IsUnit g := (Sp ℂ).toRingedSpace.isUnit_of_isUnit_germ ⊤ g fun p hp =>
        ((Sp ℂ).mem_basicOpen g p hp).1 (by rw [hg]; exact hp)
      exact this.map _
    · intro hg
      have : IsUnit g := by
        have h2 := hg.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        simpa using! h2
      exact (Sp ℂ).basicOpen_of_isUnit this
  · refine ⟨fun h' => (h (h'.trans (x.preimage_mono (X.basicOpen_le f)))).elim, ?_⟩
    intro h'
    exact (h' (by rw [value, dite_eq_right h])).elim

theorem top_le_dual_iff (v : Sp (DualNumber ℂ) ⟶ X) (U : X.Opens) :
    ⊤ ≤ v ⁻¹ᵁ U ↔
      ⊤ ≤ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v) ⁻¹ᵁ U := by
  constructor
  · intro h p _
    exact h (Set.mem_univ _)
  · intro h p _
    obtain ⟨q, rfl⟩ := WeierstrassLie.surjective_fst p
    exact h (Set.mem_univ q)

end RHLean.Geometry.NativeCM.SchemeTheory.SectionPoints

namespace RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassSectionJet

open SchemeTheory.WeierstrassCurve WeierstrassLie SectionPoints

variable (L : PeriodPair) (W : _root_.WeierstrassCurve ℂ)
    (C : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC : C • W.baseChange ℂ = Weierstrass.latticeCurve L)

/-- Complex points of the actual equation, with the actual coordinate change. -/
def expPoint (z : ℂ) : Sp ℂ ⟶ scheme W :=
  (ofAffinePoint W ℂ (AllPlaceTangentPeriod.exponential L (W.baseChange ℂ) C hC z)).left

@[simp] theorem expPoint_zero : expPoint L W C hC 0 = zero W := by
  rw [expPoint, map_zero, ofAffinePoint_zero, zeroOver_left]
  change Spec.map (𝟙 (CommRingCat.of ℂ)) ≫ zero W = zero W
  rw [Spec.map_id, Category.id_comp]

theorem eventually_expPoint_origin :
    ∀ᶠ z in 𝓝 (0 : ℂ), ∃ h : (W.map (RingHom.id ℂ)).toProjective.Equation
      ![WeierstrassTangent.originZ L C z, -1, WeierstrassTangent.originW L C z],
      expPoint L W C hC z = spMap (originEval W (RingHom.id ℂ)
        (WeierstrassTangent.originZ L C z) (WeierstrassTangent.originW L C z) h) ≫ chartY W := by
  filter_upwards [AllPlaceTangentPeriod.exponential_origin_coordinates L (W.baseChange ℂ) C hC,
    (WeierstrassTangent.regularY_analytic L C).continuousAt.eventually_ne
      (WeierstrassTangent.regularY_zero_ne L C)] with z hz hy
  by_cases hz0 : z = 0
  · subst z
    have h0 : (W.map (RingHom.id ℂ)).toProjective.Equation
        ![WeierstrassTangent.originZ L C 0, -1, WeierstrassTangent.originW L C 0] := by
      rw [equation_origin_iff]
      simp
    refine ⟨h0, ?_⟩
    rw [expPoint_zero, SpecMap_originEval_chartY]
    have e : (![WeierstrassTangent.originZ L C 0, -1,
        WeierstrassTangent.originW L C 0] : Fin 3 → ℂ) = (-1 : ℂ) • ![0, 1, 0] := by
      ext i
      fin_cases i <;> simp
    rw [zero, ← pt_smul W (A := ℂ) _ _ isUnit_one.neg]
    exact ptHom_congr W _ _ _ rfl e.symm _
  · obtain ⟨hp, hep, hz', hw'⟩ := hz.resolve_left hz0
    have hy' : WeierstrassTangent.affineY L C z ≠ 0 := by
      intro h
      rw [WeierstrassTangent.regularY_eq L C hz0, h, mul_zero] at hy
      exact hy rfl
    set a := -(WeierstrassTangent.affineY L C z)⁻¹ with ha_def
    have ha : IsUnit a := (neg_ne_zero.mpr (inv_ne_zero hy')).isUnit
    have e : (![WeierstrassTangent.originZ L C z, -1,
        WeierstrassTangent.originW L C z] : Fin 3 → ℂ) =
        a • ![WeierstrassTangent.affineX L C z, WeierstrassTangent.affineY L C z, 1] := by
      ext i
      fin_cases i <;> simp only [Pi.smul_apply, smul_eq_mul]
      · change WeierstrassTangent.originZ L C z = a * WeierstrassTangent.affineX L C z
        rw [hz', ha_def, div_eq_mul_inv]
        ring
      · dsimp [a]
        field_simp
      · change WeierstrassTangent.originW L C z = a * 1
        rw [hw', ha_def]
        ring
    have hp' : IsUnimodularSol (W.map (RingHom.id ℂ))
        ![WeierstrassTangent.affineX L C z, WeierstrassTangent.affineY L C z, 1] :=
      isUnimodularSol_some hp.left
    have ho := e.symm ▸ hp'.smul ha
    refine ⟨ho.equation, ?_⟩
    rw [expPoint, hep, ofAffinePoint_some, SpecMap_originEval_chartY]
    change ptHom W (RingHom.id ℂ)
      ![WeierstrassTangent.affineX L C z, WeierstrassTangent.affineY L C z, 1] hp' =
        ptHom W (RingHom.id ℂ)
          ![WeierstrassTangent.originZ L C z, -1, WeierstrassTangent.originW L C z] ho
    exact (ptHom_smul W _ _ hp' ha).symm.trans
      (ptHom_congr W _ _ _ rfl e.symm ho)

/-- The actual dual-number evaluation of the specified origin vector. -/
def epsEval (c : ℂ) : OriginRing W →+* DualNumber ℂ :=
  originEval W (algebraMap ℂ (DualNumber ℂ)) (TrivSqZeroExt.inr c) 0
    (equation_inr W c)

def locEval (t : ℂ) (r : OriginRing W) : ℂ :=
  if h : (W.map (RingHom.id ℂ)).toProjective.Equation
      ![WeierstrassTangent.originZ L C t, -1, WeierstrassTangent.originW L C t] then
    originEval W (RingHom.id ℂ) (WeierstrassTangent.originZ L C t)
      (WeierstrassTangent.originW L C t) h r else 0

include hC in
theorem eventually_equation : ∀ᶠ t in 𝓝 (0 : ℂ),
    (W.map (RingHom.id ℂ)).toProjective.Equation
      ![WeierstrassTangent.originZ L C t, -1, WeierstrassTangent.originW L C t] := by
  filter_upwards [eventually_expPoint_origin L W C hC] with t ⟨h, _⟩
  exact h

theorem epsEval_fst (c : ℂ) (r : OriginRing W)
    (h0 : (W.map (RingHom.id ℂ)).toProjective.Equation
      ![WeierstrassTangent.originZ L C 0, -1, WeierstrassTangent.originW L C 0]) :
    (epsEval W c r).fst = originEval W (RingHom.id ℂ)
      (WeierstrassTangent.originZ L C 0) (WeierstrassTangent.originW L C 0) h0 r := by
  have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (epsEval W c) =
      originEval W (RingHom.id ℂ) (WeierstrassTangent.originZ L C 0)
        (WeierstrassTangent.originW L C 0) h0 := by
    refine origin_hom_ext W (fun a => ?_) ?_ ?_ <;> simp [epsEval]
  exact RingHom.congr_fun e r

theorem epsEval_snd (c : ℂ) (r : OriginRing W) :
    (epsEval W c r).snd = c * (epsEval W 1 r).snd := by
  have e : (epsScaleR c).comp (epsEval W 1) = epsEval W c := by
    refine origin_hom_ext W (fun a => ?_) ?_ ?_ <;> simp [epsEval, epsScaleR]
    exact TrivSqZeroExt.ext (by simp) (by simp)
  rw [← e]
  simp [epsScaleR]

/-- The chart is generated by its actual two coordinates over the base. -/
theorem mem_of_origin_generators (S : Subring (OriginRing W))
    (hC : ∀ a : ℂ, algebraMap ℂ (OriginRing W) a ∈ S)
    (hZ : originZ W ∈ S) (hW : originW W ∈ S) : ∀ r, r ∈ S := by
  have hCa : ∀ a : Polynomial ℂ, AdjoinRoot.mk (originPolynomial W) (Polynomial.C a) ∈ S := by
    intro a
    induction a using Polynomial.induction_on with
    | C b => exact hC b
    | add p q hp hq => rw [Polynomial.C_add, map_add]; exact S.add_mem hp hq
    | monomial n b _ =>
      rw [Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      exact S.mul_mem (hC b) (S.pow_mem hW _)
  intro x
  refine AdjoinRoot.induction_on (f := originPolynomial W) x fun p => ?_
  induction p using Polynomial.induction_on with
  | C a => exact hCa a
  | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  | monomial n a _ =>
    rw [map_mul, map_pow]
    exact S.mul_mem (hCa a) (S.pow_mem hZ _)

include hC in
/-- On every element of the literal origin ring, algebraic epsilon evaluation
is the analytic derivative, with the original coordinate-change scale. -/
theorem locEval_regular (r : OriginRing W) :
    HasDerivAt (fun t => locEval L W C t r) ((C.u : ℂ)⁻¹ * (epsEval W 1 r).snd) 0 ∧
      AnalyticAt ℂ (fun t => locEval L W C t r) 0 := by
  have hev := eventually_equation L W C hC
  have h0 := hev.self_of_nhds
  have hE : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ a b : OriginRing W,
      locEval L W C t (a * b) = locEval L W C t a * locEval L W C t b ∧
      locEval L W C t (a + b) = locEval L W C t a + locEval L W C t b ∧
      locEval L W C t (-a) = -locEval L W C t a := by
    filter_upwards [hev] with t ht a b
    simp only [locEval, dite_eq_left ht, map_mul, map_add, map_neg, and_self]
  have hE0 : ∀ a, locEval L W C 0 a = (epsEval W 1 a).fst := fun a => by
    rw [locEval, dite_eq_left h0, epsEval_fst L W C 1 a h0]
  have hconst : ∀ a : ℂ,
      HasDerivAt (fun t => locEval L W C t (algebraMap ℂ _ a))
          ((C.u : ℂ)⁻¹ * (epsEval W 1 (algebraMap ℂ _ a)).snd) 0 ∧
        AnalyticAt ℂ (fun t => locEval L W C t (algebraMap ℂ _ a)) 0 := by
    intro a
    have heq : (fun t => locEval L W C t (algebraMap ℂ _ a)) =ᶠ[𝓝 0] fun _ => a := by
      filter_upwards [hev] with t ht
      simp only [locEval, dite_eq_left ht]
      simp
    exact ⟨((hasDerivAt_const (0 : ℂ) a).congr_deriv
      (by simp [epsEval, TrivSqZeroExt.algebraMap_eq_inl])).congr_of_eventuallyEq heq,
      analyticAt_const.congr heq.symm⟩
  let S : Subring (OriginRing W) :=
    { carrier := {r | HasDerivAt (fun t => locEval L W C t r)
          ((C.u : ℂ)⁻¹ * (epsEval W 1 r).snd) 0 ∧
        AnalyticAt ℂ (fun t => locEval L W C t r) 0}
      mul_mem' := fun {a b} ha hb => by
        have heq : (fun t => locEval L W C t (a * b)) =ᶠ[𝓝 0]
            fun t => locEval L W C t a * locEval L W C t b :=
          hE.mono fun t ht => (ht a b).1
        refine ⟨((ha.1.mul hb.1).congr_deriv ?_).congr_of_eventuallyEq heq,
          (ha.2.mul hb.2).congr heq.symm⟩
        simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
          MulOpposite.unop_op, hE0]
        ring
      one_mem' := by simpa using! hconst 1
      add_mem' := fun {a b} ha hb => by
        have heq : (fun t => locEval L W C t (a + b)) =ᶠ[𝓝 0]
            fun t => locEval L W C t a + locEval L W C t b :=
          hE.mono fun t ht => (ht a b).2.1
        refine ⟨((ha.1.add hb.1).congr_deriv ?_).congr_of_eventuallyEq heq,
          (ha.2.add hb.2).congr heq.symm⟩
        simp only [map_add, TrivSqZeroExt.snd_add]
        ring
      zero_mem' := by simpa using! hconst 0
      neg_mem' := fun {a} ha => by
        have heq : (fun t => locEval L W C t (-a)) =ᶠ[𝓝 0]
            fun t => -locEval L W C t a := hE.mono fun t ht => (ht a a).2.2
        refine ⟨(ha.1.neg.congr_deriv ?_).congr_of_eventuallyEq heq,
          ha.2.neg.congr heq.symm⟩
        simp only [map_neg, TrivSqZeroExt.snd_neg]
        ring }
  apply mem_of_origin_generators W S hconst ?_ ?_ r
  · have heq : (fun t => locEval L W C t (originZ W)) =ᶠ[𝓝 0]
        WeierstrassTangent.originZ L C := by
      filter_upwards [hev] with t ht
      simp only [locEval, dite_eq_left ht]
      simp
    have han : AnalyticAt ℂ (WeierstrassTangent.originZ L C) 0 :=
      analyticAt_id.mul ((WeierstrassTangent.regularX_analytic L C).neg.div
        (WeierstrassTangent.regularY_analytic L C) (WeierstrassTangent.regularY_zero_ne L C))
    exact ⟨((WeierstrassTangent.originZ_hasDerivAt L C).congr_deriv
      (by simp [epsEval])).congr_of_eventuallyEq heq, han.congr heq.symm⟩
  · have heq : (fun t => locEval L W C t (originW W)) =ᶠ[𝓝 0]
        WeierstrassTangent.originW L C := by
      filter_upwards [hev] with t ht
      simp only [locEval, dite_eq_left ht]
      simp
    have han : AnalyticAt ℂ (WeierstrassTangent.originW L C) 0 :=
      (analyticAt_id.pow 3).mul (analyticAt_const.div
        (WeierstrassTangent.regularY_analytic L C) (WeierstrassTangent.regularY_zero_ne L C))
    exact ⟨((WeierstrassTangent.originW_hasDerivAt L C).congr_deriv
      (by simp [epsEval])).congr_of_eventuallyEq heq, han.congr heq.symm⟩

include hC in
theorem hasDerivAt_locEval (r : OriginRing W) :
    HasDerivAt (fun t => locEval L W C t r) ((C.u : ℂ)⁻¹ * (epsEval W 1 r).snd) 0 :=
  (locEval_regular L W C hC r).1

include hC in
theorem analyticAt_locEval (r : OriginRing W) :
    AnalyticAt ℂ (fun t => locEval L W C t r) 0 :=
  (locEval_regular L W C hC r).2

theorem top_le_chartY : ⊤ ≤ chartY W ⁻¹ᵁ coordOpen W 1 := by
  rw [← opensRange_chartY]
  simp

theorem top_le_comp_chartY {X : Scheme.{0}} (g : X ⟶ Sp (OriginRing W)) :
    ⊤ ≤ (g ≫ chartY W) ⁻¹ᵁ coordOpen W 1 := by
  rw [Scheme.Hom.comp_preimage]
  exact fun p _ => top_le_chartY W (Set.mem_univ (g.base p))

def chartVal : Γ(scheme W, coordOpen W 1) →+* OriginRing W :=
  evalPt (chartY W) _ (top_le_chartY W)

theorem evalPt_chart {R : Type} [CommRing R] (e : OriginRing W →+* R)
    (h : ⊤ ≤ (spMap e ≫ chartY W) ⁻¹ᵁ coordOpen W 1)
    (s : Γ(scheme W, coordOpen W 1)) :
    evalPt (spMap e ≫ chartY W) _ h s = e (chartVal W s) :=
  evalPt_spMap_comp e _ _ (top_le_chartY W) h s

theorem vec_eq (c : ℂ) : vec W c = spMap (epsEval W c) ≫ chartY W :=
  (SpecMap_originEval_chartY W _ _ _ _).symm

theorem eventually_value (s : Γ(scheme W, coordOpen W 1)) :
    ∀ᶠ t in 𝓝 (0 : ℂ), ⊤ ≤ expPoint L W C hC t ⁻¹ᵁ coordOpen W 1 ∧
      value (expPoint L W C hC t) _ s = locEval L W C t (chartVal W s) := by
  filter_upwards [eventually_expPoint_origin L W C hC] with t ⟨h, e⟩
  have key : ∀ (x : Sp ℂ ⟶ scheme W),
      x = spMap (originEval W (RingHom.id ℂ) (WeierstrassTangent.originZ L C t)
        (WeierstrassTangent.originW L C t) h) ≫ chartY W →
      ⊤ ≤ x ⁻¹ᵁ coordOpen W 1 ∧ value x _ s = locEval L W C t (chartVal W s) := by
    rintro _ rfl
    refine ⟨top_le_comp_chartY W _, ?_⟩
    rw [value_eq _ (top_le_comp_chartY W _), evalPt_chart, locEval, dite_eq_left h]
  exact key _ e

theorem fst_vec_expPoint (c : ℂ) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ vec W c = expPoint L W C hC 0 := by
  rw [fst_vec, expPoint_zero]

/-- A regular section on any neighborhood of the actual origin is analytic
along the actual exponential, and its derivative is its dual-number value. -/
theorem section_regular (c : ℂ) (V : (scheme W).Opens)
    (hT : ⊤ ≤ vec W c ⁻¹ᵁ V) (s : Γ(scheme W, V)) :
    (∀ᶠ t in 𝓝 (0 : ℂ), ⊤ ≤ expPoint L W C hC t ⁻¹ᵁ V) ∧
      AnalyticAt ℂ (fun t => value (expPoint L W C hC t) V s) 0 ∧
      ∃ d : ℂ, HasDerivAt (fun t => value (expPoint L W C hC t) V s)
        ((C.u : ℂ)⁻¹ * d) 0 ∧ (evalPt (vec W c) V hT s).snd = c * d := by
  set U₀ := coordOpen W 1
  have hU₀ : IsAffineOpen U₀ := isAffineOpen_coordOpen W 1
  have hp0 : ⊤ ≤ expPoint L W C hC 0 ⁻¹ᵁ V := by
    rw [← fst_vec_expPoint L W C hC c]
    exact (top_le_dual_iff _ V).1 hT
  have hp0U : ⊤ ≤ expPoint L W C hC 0 ⁻¹ᵁ U₀ :=
    (eventually_value L W C hC 0).self_of_nhds.1
  let q : Sp ℂ := (default : PrimeSpectrum ℂ)
  obtain ⟨a, haV, ha⟩ := hU₀.exists_basicOpen_le (V := V)
    ⟨(expPoint L W C hC 0).base q, hp0 (Set.mem_univ q)⟩ (hp0U (Set.mem_univ q))
  set B := (scheme W).basicOpen a
  have hB0 : ⊤ ≤ expPoint L W C hC 0 ⁻¹ᵁ B :=
    (top_le_preimage_iff_mem _ _).2 ha
  have hTB : ⊤ ≤ vec W c ⁻¹ᵁ B := by
    rw [top_le_dual_iff, fst_vec_expPoint L W C hC c]
    exact hB0
  have := hU₀.isLocalization_basicOpen a
  obtain ⟨⟨b, m⟩, hm⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) (resG _ haV s)
  change IsLocalization.mk' _ b m = _ at hm
  obtain ⟨n, hn⟩ := m.2
  have hkey := IsLocalization.mk'_spec Γ(scheme W, B) b m
  rw [hm] at hkey
  change resG _ haV s * resG _ ((scheme W).basicOpen_le a) m.1 =
    resG _ ((scheme W).basicOpen_le a) b at hkey
  have hX := congrArg (evalPt (vec W c) B hTB) hkey
  have hTU : ⊤ ≤ vec W c ⁻¹ᵁ U₀ :=
    hTB.trans ((vec W c).preimage_mono ((scheme W).basicOpen_le a))
  rw [map_mul, evalPt_res _ _ hT, evalPt_res _ _ hTU, evalPt_res _ _ hTU] at hX
  have ht : ∀ s' : Γ(scheme W, U₀),
      evalPt (vec W c) U₀ hTU s' = epsEval W c (chartVal W s') := by
    intro s'
    have key : ∀ (x : Sp (DualNumber ℂ) ⟶ scheme W) (hx : ⊤ ≤ x ⁻¹ᵁ U₀),
        x = spMap (epsEval W c) ≫ chartY W →
        evalPt x U₀ hx s' = epsEval W c (chartVal W s') := by
      rintro _ hx rfl
      exact evalPt_chart W _ hx s'
    exact key _ hTU (vec_eq W c)
  rw [ht, ht] at hX
  have hev := eventually_equation L W C hC
  have h0 := hev.self_of_nhds
  have hdb := hasDerivAt_locEval L W C hC (chartVal W b)
  have hdm := hasDerivAt_locEval L W C hC (chartVal W m.1)
  have hda := hasDerivAt_locEval L W C hC (chartVal W a)
  have hm0 : locEval L W C 0 (chartVal W m.1) ≠ 0 := by
    have e1 := (eventually_value L W C hC a).self_of_nhds.2
    have e2 := (top_le_preimage_basicOpen_iff (expPoint L W C hC 0) U₀ a).1 hB0
    rw [e1] at e2
    rw [← hn, map_pow, locEval, dite_eq_left h0, map_pow]
    rw [locEval, dite_eq_left h0] at e2
    exact pow_ne_zero _ e2
  have hane : ∀ᶠ t in 𝓝 (0 : ℂ), locEval L W C t (chartVal W a) ≠ 0 := by
    refine hda.continuousAt.eventually_ne ?_
    have e1 := (eventually_value L W C hC a).self_of_nhds.2
    have e2 := (top_le_preimage_basicOpen_iff (expPoint L W C hC 0) U₀ a).1 hB0
    rwa [e1] at e2
  have hmne : ∀ᶠ t in 𝓝 (0 : ℂ), locEval L W C t (chartVal W m.1) ≠ 0 :=
    hdm.continuousAt.eventually_ne hm0
  have hmemB : ∀ᶠ t in 𝓝 (0 : ℂ), ⊤ ≤ expPoint L W C hC t ⁻¹ᵁ B := by
    filter_upwards [eventually_value L W C hC a, hane] with t ⟨_, ea⟩ hne
    apply (top_le_preimage_basicOpen_iff (expPoint L W C hC t) U₀ a).2
    rwa [ea]
  have hH : (fun t => value (expPoint L W C hC t) V s) =ᶠ[𝓝 0]
      fun t => locEval L W C t (chartVal W b) / locEval L W C t (chartVal W m.1) := by
    filter_upwards [eventually_value L W C hC b, eventually_value L W C hC m.1,
      hmemB, hmne] with t ⟨_, eb⟩ ⟨_, em⟩ hBt hm'
    have e := congrArg (value (expPoint L W C hC t) B) hkey
    rw [value_mul, value_res _ _ _ hBt, value_res _ _ _ hBt,
      value_res _ _ _ hBt, eb, em] at e
    rw [eq_div_iff hm', e]
  have hE0 : ∀ r, locEval L W C 0 r = (epsEval W 1 r).fst := fun r => by
    rw [locEval, dite_eq_left h0, epsEval_fst L W C 1 r h0]
  have hF : ∀ r, (epsEval W c r).fst = (epsEval W 1 r).fst := fun r => by
    rw [epsEval_fst L W C c r h0, epsEval_fst L W C 1 r h0]
  have hE0b : locEval L W C 0 (chartVal W b) = (epsEval W 1 (chartVal W b)).fst := hE0 _
  have hE0m : locEval L W C 0 (chartVal W m.1) = (epsEval W 1 (chartVal W m.1)).fst := hE0 _
  have h1 := congrArg TrivSqZeroExt.fst hX
  have h2 := congrArg TrivSqZeroExt.snd hX
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, hF, epsEval_snd W c] at h1 h2
  have hd := (hdb.div hdm hm0).congr_of_eventuallyEq hH
  have han := ((analyticAt_locEval L W C hC (chartVal W b)).div
    (analyticAt_locEval L W C hC (chartVal W m.1)) hm0).congr hH.symm
  refine ⟨hmemB.mono (fun t ht => ht.trans ((expPoint L W C hC t).preimage_mono haV)), han, ?_⟩
  generalize epsEval W 1 (chartVal W b) = α at hd hE0b h1 h2
  generalize epsEval W 1 (chartVal W m.1) = β at hd hE0m h1 h2
  generalize evalPt (vec W c) V hT s = X at h1 h2 ⊢
  rw [hE0b, hE0m] at hd
  rw [hE0m] at hm0
  refine ⟨(α.snd * β.fst - α.fst * β.snd) / β.fst ^ 2,
    hd.congr_deriv (by field_simp), ?_⟩
  rw [← eq_div_iff hm0] at h1
  rw [h1] at h2
  field_simp at h2 ⊢
  linear_combination h2

/-- The actual scheme-valued exponential is continuous for the Zariski
open conditions needed to evaluate regular sections near the origin. -/
theorem eventually_mem_open (U : (scheme W).Opens)
    (hU : ⊤ ≤ expPoint L W C hC 0 ⁻¹ᵁ U) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ⊤ ≤ expPoint L W C hC z ⁻¹ᵁ U := by
  have hT : ⊤ ≤ vec W 1 ⁻¹ᵁ U := by
    rw [top_le_dual_iff, fst_vec_expPoint L W C hC 1]
    exact hU
  exact (section_regular L W C hC 1 U hT 0).1

/-- Every actual regular section is analytic along this exponential near
its actual origin; this is a supplier for the later theta atlas. -/
theorem analyticAt_eval_section (U : (scheme W).Opens)
    (hU : ⊤ ≤ expPoint L W C hC 0 ⁻¹ᵁ U) (s : Γ(scheme W, U)) :
    AnalyticAt ℂ (fun z => value (expPoint L W C hC z) U s) 0 := by
  have hT : ⊤ ≤ vec W 1 ⁻¹ᵁ U := by
    rw [top_le_dual_iff, fst_vec_expPoint L W C hC 1]
    exact hU
  exact (section_regular L W C hC 1 U hT s).2.1

/-- Exact comparison with the literal integral-coordinate epsilon vector. -/
theorem section_derivative (U : (scheme W).Opens) (hU : ⊤ ≤ vec W 1 ⁻¹ᵁ U)
    (s : Γ(scheme W, U)) :
    HasDerivAt (fun z => value (expPoint L W C hC z) U s)
      ((C.u : ℂ)⁻¹ * (evalPt (vec W 1) U hU s).snd) 0 := by
  obtain ⟨d, hd, he⟩ := (section_regular L W C hC 1 U hU s).2.2
  rw [one_mul] at he
  rwa [he]

end RHLean.Geometry.NativeCM.SchemeTheory.WeierstrassSectionJet

end
