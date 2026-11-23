import RHLean.Geometry.NativeCMWeierstrassPeriodUniqueness

/-!
# Actual integral equations for the ideal-class periods in one common field

Order stability of an actual ideal lattice proves integrality of its actual
modular invariant. The finite good-reduction model constructor is then
applied to every class. All integral coefficients are descended into one
finite number field containing the original seed field. The principal
class retains the original integral equation and its original comparison.

This is native composition of the reconstructed modular-integrality,
finite integral-model and ideal-class-period constructors. It does not
construct the ideal-isogeny morphisms or assume their derivative integrality.
No arithmetic mean or height is assigned.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField PeriodPair
open scoped Classical BigOperators nonZeroDivisors

namespace RHLean.Geometry.NativeCM.Weierstrass

/-- A genuine order-stable lattice has integral modular invariant. -/
theorem latticeCurve_j_integral_of_order_stable
    {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℂ) (L : PeriodPair)
    (hL : ∀ b : 𝓞 K, ∀ z ∈ L.lattice, σ (b : K) * z ∈ L.lattice) :
    IsIntegral ℤ (latticeCurve L).j := by
  obtain ⟨a, τ, ha, hp⟩ := exists_lattice_eq_mul_tau L
  have hm (z : ℂ) : a * z ∈ L.lattice ↔ z ∈ Submodule.span ℤ {(τ : ℂ), 1} := by
    rw [hp, Submodule.mem_span_pair]
    simp only [zsmul_eq_mul, mul_one]
    exact exists₂_congr fun m n => ⟨fun h => mul_left_cancel₀ ha h, fun h => congrArg (a * ·) h⟩
  rw [latticeCurve_j ha hp]
  apply isIntegral_modularJ_of_ringOfIntegers hK σ
  intro b z hz
  apply (hm _).mp
  rw [mul_left_comm]
  exact hL b _ ((hm z).mpr hz)

/-- The inclusion of integral coefficients through the specified common
subfield keeps their literal complex values. -/
def integerFieldInclusion {M F : IntermediateField ℚ ℂ} (h : M ≤ F) : 𝓞 M →+* 𝓞 F where
  toFun x := ⟨⟨((x : M) : ℂ), h (x : M).property⟩,
    (isIntegral_algHom_iff ((F.val : F →+* ℂ).toIntAlgHom) Subtype.val_injective).1
      (x.isIntegral_coe.map (M.val : M →+* ℂ).toIntAlgHom)⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem integerFieldInclusion_complex_apply {M F : IntermediateField ℚ ℂ}
    (h : M ≤ F) (x : 𝓞 M) :
    (((integerFieldInclusion h x : 𝓞 F) : F) : ℂ) = ((x : M) : ℂ) := rfl

/-- All class equations live in one actual finite extension. The original
seed equation and comparison are preserved at the specified principal index. -/
theorem exists_common_integral_models_preserving_seed
    {I : Type} [Fintype I] (i₀ : I) (L : I → PeriodPair)
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W₀ : _root_.WeierstrassCurve (𝓞 M)) (hΔ₀ : W₀.Δ = 1)
    (C₀ : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC₀ : C₀ • W₀.baseChange ℂ = latticeCurve (L i₀))
    (hj : ∀ i, IsIntegral ℤ (latticeCurve (L i)).j) :
    ∃ (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
      (W : I → _root_.WeierstrassCurve (𝓞 F))
      (C : I → _root_.WeierstrassCurve.VariableChange ℂ),
      (∀ i, (W i).Δ = 1) ∧
      (∀ i, C i • (W i).baseChange ℂ = latticeCurve (L i)) ∧
      W i₀ = W₀.map (integerFieldInclusion hMF) ∧ C i₀ = C₀ := by
  classical
  let _ : W₀.IsElliptic := ⟨hΔ₀.symm ▸ isUnit_one⟩
  have hV : ∀ i : I, ∃ V : _root_.WeierstrassCurve ℂ,
      IsIntegral ℤ V.a₁ ∧ IsIntegral ℤ V.a₂ ∧ IsIntegral ℤ V.a₃ ∧
      IsIntegral ℤ V.a₄ ∧ IsIntegral ℤ V.a₆ ∧ V.Δ = 1 ∧
      V.c₄ ^ 3 = (latticeCurve (L i)).j ∧ (i = i₀ → V = W₀.baseChange ℂ) := by
    intro i
    by_cases hi : i = i₀
    · subst i
      have hint (x : 𝓞 M) : IsIntegral ℤ (algebraMap (𝓞 M) ℂ x) :=
        x.isIntegral_coe.map (M.val : M →+* ℂ).toIntAlgHom
      have hd : (W₀.baseChange ℂ).Δ = 1 := by
        rw [_root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_Δ, hΔ₀, map_one]
      refine ⟨W₀.baseChange ℂ, hint _, hint _, hint _, hint _, hint _, hd, ?_, fun _ => rfl⟩
      have he := congrArg _root_.WeierstrassCurve.j hC₀
      rw [_root_.WeierstrassCurve.variableChange_j] at he
      rw [← j_mul_Δ, hd, mul_one, he]
    · obtain ⟨V, h1, h2, h3, h4, h6, hd, hc⟩ := exists_complex_integral_curve (hj i)
      exact ⟨V, h1, h2, h3, h4, h6, hd, hc, fun h => (hi h).elim⟩
  choose V h1 h2 h3 h4 h6 hd hc hV₀ using hV
  let T : Set ℂ := ⋃ i : I, { (V i).a₁, (V i).a₂, (V i).a₃, (V i).a₄, (V i).a₆ }
  have hT : T.Finite := by simp [T]
  have : Finite T := hT.to_subtype
  have hTint : ∀ z ∈ T, IsIntegral ℤ z := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact h1 i
    · exact h2 i
    · exact h3 i
    · exact h4 i
    · exact h6 i
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ T) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => (hTint z hz).tower_top
  let F : IntermediateField ℚ ℂ := M ⊔ IntermediateField.adjoin ℚ T
  have : NumberField F := ⟨⟩
  have hMF : M ≤ F := le_sup_left
  have hTF : ∀ z ∈ T, z ∈ F := fun z hz =>
    (le_sup_right : IntermediateField.adjoin ℚ T ≤ F) (IntermediateField.subset_adjoin ℚ T hz)
  have mk : ∀ z ∈ T, IsIntegral ℤ z → ∃ x : 𝓞 F, ((x : F) : ℂ) = z := fun z hz hi =>
    ⟨⟨⟨z, hTF z hz⟩, (isIntegral_algHom_iff ((F.val : F →+* ℂ).toIntAlgHom)
      Subtype.val_injective).1 hi⟩, rfl⟩
  choose t1 ht1 using fun i => mk (V i).a₁ (Set.mem_iUnion.mpr ⟨i, by simp⟩) (h1 i)
  choose t2 ht2 using fun i => mk (V i).a₂ (Set.mem_iUnion.mpr ⟨i, by simp⟩) (h2 i)
  choose t3 ht3 using fun i => mk (V i).a₃ (Set.mem_iUnion.mpr ⟨i, by simp⟩) (h3 i)
  choose t4 ht4 using fun i => mk (V i).a₄ (Set.mem_iUnion.mpr ⟨i, by simp⟩) (h4 i)
  choose t6 ht6 using fun i => mk (V i).a₆ (Set.mem_iUnion.mpr ⟨i, by simp⟩) (h6 i)
  let W : I → _root_.WeierstrassCurve (𝓞 F) := fun i => ⟨t1 i, t2 i, t3 i, t4 i, t6 i⟩
  let φ : 𝓞 F →+* ℂ := (F.val : F →+* ℂ).comp (algebraMap (𝓞 F) F)
  have hφ : Function.Injective φ := Subtype.val_injective.comp RingOfIntegers.coe_injective
  have hWV : ∀ i, (W i).map φ = V i := by
    intro i
    ext
    · exact ht1 i
    · exact ht2 i
    · exact ht3 i
    · exact ht4 i
    · exact ht6 i
  have hΔ : ∀ i, (W i).Δ = 1 := fun i =>
    hφ (by rw [← _root_.WeierstrassCurve.map_Δ, hWV, hd, map_one])
  have hW₀ : W i₀ = W₀.map (integerFieldInclusion hMF) := by
    have e : (W i₀).map φ = (W₀.map (integerFieldInclusion hMF)).map φ := by
      rw [hWV, hV₀ i₀ rfl]
      ext <;> rfl
    apply _root_.WeierstrassCurve.ext
    · exact hφ (congrArg _root_.WeierstrassCurve.a₁ e)
    · exact hφ (congrArg _root_.WeierstrassCurve.a₂ e)
    · exact hφ (congrArg _root_.WeierstrassCurve.a₃ e)
    · exact hφ (congrArg _root_.WeierstrassCurve.a₄ e)
    · exact hφ (congrArg _root_.WeierstrassCurve.a₆ e)
  have hC : ∀ i, ∃ C : _root_.WeierstrassCurve.VariableChange ℂ,
      C • (W i).baseChange ℂ = latticeCurve (L i) ∧ (i = i₀ → C = C₀) := by
    intro i
    by_cases hi : i = i₀
    · subst i
      refine ⟨C₀, ?_, fun _ => rfl⟩
      change C₀ • (W i₀).map φ = _
      rw [hWV, hV₀ i₀ rfl]
      exact hC₀
    · let _ : (V i).IsElliptic := ⟨(hd i).symm ▸ isUnit_one⟩
      have hjV : (V i).j = (latticeCurve (L i)).j := by
        have e := j_mul_Δ (V i)
        rwa [hd, mul_one, hc] at e
      obtain ⟨C, hC⟩ := (V i).exists_variableChange_of_j_eq (latticeCurve (L i)) hjV
      refine ⟨C, ?_, fun h => (hi h).elim⟩
      change C • (W i).map φ = _
      rw [hWV]
      exact hC
  choose C hC hC₀' using hC
  exact ⟨F, inferInstance, hMF, W, C, hΔ, hC, hW₀, hC₀' i₀ rfl⟩

end RHLean.Geometry.NativeCM.Weierstrass

namespace RHLean.Geometry.NativeCM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    (G : NativeGeometricHost E) (τ : E →+* ℂ)

/-- Every actual integral ideal-class period has the integral invariant
needed by the simultaneous model constructor. -/
theorem idealClassPeriod_j_integral
    (b : ClassGroup (𝓞 (quadraticField G)) → (Ideal (𝓞 (quadraticField G)))⁰)
    (L : ClassGroup (𝓞 (quadraticField G)) → PeriodPair)
    (hL : ∀ c z, z ∈ (L c).lattice ↔
      ∃ a ∈ (b c : Ideal (𝓞 (quadraticField G))), z = quadraticEmbedding G τ (a : quadraticField G)) :
    ∀ c, IsIntegral ℤ (Weierstrass.latticeCurve (L c)).j := by
  intro c
  apply Weierstrass.latticeCurve_j_integral_of_order_stable
    (quadraticField_finrank G) (quadraticEmbedding G τ)
  intro a z hz
  obtain ⟨y, hy, rfl⟩ := (hL c z).mp hz
  apply (hL c _).mpr
  refine ⟨a * y, (b c : Ideal (𝓞 (quadraticField G))).mul_mem_left a hy, ?_⟩
  change quadraticEmbedding G τ (a : quadraticField G) *
      quadraticEmbedding G τ (y : quadraticField G) =
    quadraticEmbedding G τ ((a : quadraticField G) * (y : quadraticField G))
  exact (map_mul _ _ _).symm

/-- The actual class lattices now have actual integral equations in one
finite field containing the original seed field. The principal equation,
comparison and period are all preserved, and the analytic class mean is
the one already proved for these very lattices. No isogeny hypothesis is
needed to construct this family. -/
theorem exists_integralIdealClassModels_preserving_seed
    (M : IntermediateField ℚ ℂ) [NumberField M]
    (W₀ : _root_.WeierstrassCurve (𝓞 M)) (hΔ₀ : W₀.Δ = 1)
    (C₀ : _root_.WeierstrassCurve.VariableChange ℂ)
    (hC₀ : C₀ • W₀.baseChange ℂ = Weierstrass.latticeCurve (EllipticSeed.periodPair G τ)) :
    ∃ (b : ClassGroup (𝓞 (quadraticField G)) → (Ideal (𝓞 (quadraticField G)))⁰)
      (L : ClassGroup (𝓞 (quadraticField G)) → PeriodPair)
      (F : IntermediateField ℚ ℂ) (_ : NumberField F) (hMF : M ≤ F)
      (W : ClassGroup (𝓞 (quadraticField G)) → _root_.WeierstrassCurve (𝓞 F))
      (C : ClassGroup (𝓞 (quadraticField G)) → _root_.WeierstrassCurve.VariableChange ℂ),
      (∀ c, ClassGroup.mk0 (b c) = c) ∧
      (∀ c z, z ∈ (L c).lattice ↔ ∃ a ∈ (b c : Ideal (𝓞 (quadraticField G))),
        z = quadraticEmbedding G τ (a : quadraticField G)) ∧
      b 1 = 1 ∧ L 1 = EllipticSeed.periodPair G τ ∧
      (∀ c, (W c).Δ = 1) ∧
      (∀ c, C c • (W c).baseChange ℂ = Weierstrass.latticeCurve (L c)) ∧
      W 1 = W₀.map (Weierstrass.integerFieldInclusion hMF) ∧ C 1 = C₀ ∧
      (((∑ c, PeriodArithmetic.latticeLogPeriod (L c)) /
          classNumber (quadraticField G) : ℝ) : ℂ) =
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt G.d) : ℝ) -
          deriv (periodCharacter G).LFunction 1 / (periodCharacter G).LFunction 1 := by
  obtain ⟨b, L, hb, hL, hb₁, hL₁, hmean⟩ := exists_integralIdealClassPeriods_with_seed G τ
  have hC : C₀ • W₀.baseChange ℂ = Weierstrass.latticeCurve (L 1) := by
    rw [hL₁]
    exact hC₀
  obtain ⟨F, hF, hMF, W, C, hΔ, hcomp, hW₁, hC₁⟩ :=
    Weierstrass.exists_common_integral_models_preserving_seed 1 L M W₀ hΔ₀ C₀ hC
      (idealClassPeriod_j_integral G τ b L hL)
  exact ⟨b, L, F, hF, hMF, W, C, hb, hL, hb₁, hL₁, hΔ, hcomp, hW₁, hC₁, hmean⟩

end RHLean.Geometry.NativeCM
