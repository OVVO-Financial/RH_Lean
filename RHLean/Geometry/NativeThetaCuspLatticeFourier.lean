import Mathlib

/-!
# Native lattice Fourier expansion needed for theta Poisson summation

This declaration cut proves Fourier expansion for continuous functions on
an actual Euclidean lattice quotient from Mathlib's torus Fourier theorem.
The integration cell and its covolume are retained exactly. No smoothness
estimate, successive-minimum bound, or automorphic structure is imported.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean,
src/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsLinearIndependentNormLeSuccMin.lean
(only `dualLattice`, `mem_dualLattice`, `covolume_span_basis`). The source
mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Module Set Submodule
open scoped RealInnerProductSpace Real Pointwise BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.Poisson

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))

def latticeCell (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] : Set E :=
  ZSpan.fundamentalDomain ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)

def latticeFourierCoeff (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : E → V) (ν : E) : V :=
  (ZLattice.covolume L)⁻¹ • ∫ b in latticeCell L, e[-⟪ν, b⟫] • A b

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L

theorem isAddFundamentalDomain_latticeCell (μ : Measure E) :
    IsAddFundamentalDomain L (latticeCell L) μ :=
  ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) μ

omit [MeasurableSpace E] [BorelSpace E] in
theorem isBounded_latticeCell : Bornology.IsBounded (latticeCell L) :=
  ZSpan.fundamentalDomain_isBounded _

theorem measurableSet_latticeCell : MeasurableSet (latticeCell L) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem volume_latticeCell_lt_top : volume (latticeCell L) < ⊤ :=
  (isBounded_latticeCell L).measure_lt_top

theorem covolume_eq_volume_latticeCell : ZLattice.covolume L = volume.real (latticeCell L) :=
  ZLattice.covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain_latticeCell L _)

theorem integrableOn_latticeCell_of_continuous {W : Type*} [NormedAddCommGroup W] {f : E → W}
    (hf : Continuous f) : IntegrableOn f (latticeCell L) :=
  (hf.continuousOn.integrableOn_compact (isBounded_latticeCell L).isCompact_closure).mono_set
    subset_closure

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L] in
theorem mem_innerDual_iff {ν : E} : ν ∈ L* ↔ ∀ x ∈ L, ∃ n : ℤ, (n : ℝ) = ⟪ν, x⟫ := by
  simp [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one]

theorem cexp_two_pi_I_add (s t : ℝ) : e[s + t] = e[s] * e[t] := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem cexp_two_pi_I_intCast (n : ℤ) : e[(n : ℝ)] = 1 := by
  rw [← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1; push_cast; ring

theorem cexp_two_pi_I_half : e[1 / 2] = -1 := by
  rw [← Complex.exp_pi_mul_I]
  congr 1; push_cast; ring

theorem norm_cexp_two_pi_I (t : ℝ) : ‖e[t]‖ = 1 := by
  rw [← Complex.norm_exp_ofReal_mul_I (2 * π * t)]
  congr 2; push_cast; ring

variable {L}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L] in
theorem cexp_inner_add_lattice {ν : E} (hν : ν ∈ L*) {x : E} (hx : x ∈ L) (b : E) :
    e[⟪ν, b + x⟫] = e[⟪ν, b⟫] := by
  obtain ⟨n, hn⟩ := (mem_innerDual_iff L).1 hν x hx
  rw [inner_add_right, cexp_two_pi_I_add, ← hn, cexp_two_pi_I_intCast, mul_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L] in
theorem cexp_neg_inner_add_lattice {ν : E} (hν : ν ∈ L*) {x : E} (hx : x ∈ L) (b : E) :
    e[-⟪ν, b + x⟫] = e[-⟪ν, b⟫] := by
  rw [← inner_neg_left, ← inner_neg_left, cexp_inner_add_lattice (neg_mem hν) hx]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_cexp_neg_inner_smul {A : E → V} (hA : Continuous A) (ν : E) :
    Continuous fun b : E ↦ e[-⟪ν, b⟫] • A b := by
  fun_prop


theorem latticeFourierCoeff_clm [CompleteSpace V] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [CompleteSpace W] (T : V →L[ℂ] W) {A : E → V} (hA : Continuous A) (ν : E) :
    latticeFourierCoeff L (fun b ↦ T (A b)) ν = T (latticeFourierCoeff L A ν) := by
  simp only [latticeFourierCoeff, ← map_smul]
  rw [T.integral_comp_comm (integrableOn_latticeCell_of_continuous L
    (continuous_cexp_neg_inner_smul hA ν)), T.map_smul_of_tower]


omit [InnerProductSpace ℝ E] in

theorem average_fundamentalDomain_eq_cube [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → V) :
    (μ.real (ZSpan.fundamentalDomain b))⁻¹ • ∫ y in ZSpan.fundamentalDomain b, g y ∂μ =
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1}, g (b.equivFun.symm x) := by
  set T := b.equivFunL.symm with hT
  have hae : T ⁻¹' ZSpan.fundamentalDomain b =ᵐ[volume] {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} := by
    have h1 : T ⁻¹' ZSpan.fundamentalDomain b = Set.pi univ fun _ ↦ Ico (0 : ℝ) 1 := by
      ext x
      have : ∀ i, b.repr (T x) i = x i := fun i ↦ congrFun (b.equivFun.apply_symm_apply x) i
      simp only [mem_preimage, ZSpan.mem_fundamentalDomain, this, mem_univ_pi]
    have h2 : {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ ↦ Ioc (0 : ℝ) 1 := by
      ext x; simp
    rw [h1, h2]
    exact Measure.univ_pi_Ico_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hμ := Measure.isAddLeftInvariant_eq_smul (Measure.map T volume) μ
  set c := Measure.addHaarScalarFactor (Measure.map T volume) μ
  have hone : (Measure.map T volume).real (ZSpan.fundamentalDomain b) = 1 := by
    rw [measureReal_def, hemb.map_apply, measure_congr hae]
    have h2 : {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1} = Set.pi univ fun _ ↦ Ioc (0 : ℝ) 1 := by
      ext x; simp
    rw [h2, Real.volume_pi_Ioc]
    simp
  have hint := hemb.setIntegral_map (μ := volume) g (ZSpan.fundamentalDomain b)
  rw [setIntegral_congr_set hae] at hint
  rw [hμ, measureReal_nnreal_smul_apply] at hone
  rw [hμ, Measure.restrict_smul, integral_smul_nnreal_measure] at hint
  rw [← eq_inv_of_mul_eq_one_left hone]
  exact hint


omit [MeasurableSpace E] [BorelSpace E] in
variable (L) in

theorem exists_equiv_innerDual {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    ∃ b' : Basis ι ℝ E, L* = Submodule.span ℤ (range b') ∧ ∃ φ : (ι → ℤ) ≃ L*,
      ∀ n x, ⟪(φ n : E), (b.ofZLatticeBasis ℝ L).equivFun.symm x⟫ = ∑ i, n i * x i := by
  classical
  have hB : LinearMap.BilinForm.Nondegenerate (innerₗ E) := by
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;> simpa using hx x
  set b₀ := b.ofZLatticeBasis ℝ L
  set b' := LinearMap.BilinForm.dualBasis _ hB b₀
  have h : L* = Submodule.span ℤ (range b') := by
    rw [← LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB, b.ofZLatticeBasis_span ℝ]
  refine ⟨b', h, ((b'.restrictScalars ℤ).equivFun.symm.trans
    (LinearEquiv.ofEq _ _ h.symm)).toEquiv, fun n x ↦ ?_⟩
  have hij : ∀ i j, ⟪b' i, b₀ j⟫ = if j = i then 1 else 0 := fun i j ↦
    LinearMap.BilinForm.apply_dualBasis_left hB b₀ i j
  simp [sum_inner, inner_sum, inner_smul_right, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_left, hij,
    mul_comm]


private theorem hasSum_latticeFourier_complex {A : E → ℂ} (hA : ∀ x ∈ L, Function.Periodic A x)
    (hc : Continuous A) (hs : Summable fun ν : L* ↦ latticeFourierCoeff L A ν) (y : E) :
    HasSum (fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν) (A y) := by
  set b := Free.chooseBasis ℤ L
  set b₀ := b.ofZLatticeBasis ℝ L
  obtain ⟨-, -, φ, hφ⟩ := exists_equiv_innerDual L b
  set p : (Free.ChooseBasisIndex ℤ L → ℝ) → UnitAddTorus (Free.ChooseBasisIndex ℤ L) :=
    fun x i ↦ (x i : UnitAddCircle) with hp
  have hq : IsOpenQuotientMap p :=
    IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk
  set f₀ : UnitAddTorus (Free.ChooseBasisIndex ℤ L) → ℂ :=
    fun z ↦ A (b₀.equivFun.symm (Function.surjInv hq.surjective z)) with hf₀
  have hfp : ∀ x, f₀ (p x) = A (b₀.equivFun.symm x) := fun x ↦ by
    set x' := Function.surjInv hq.surjective (p x)
    have h1 : p x' = p x := Function.surjInv_eq _ _
    have h2 : b₀.equivFun.symm (x' - x) ∈ L := by
      rw [Basis.equivFun_symm_apply]
      refine sum_mem fun i _ ↦ ?_
      have h3 : ((x' i - x i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]; exact congrFun h1 i
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 h3
      rw [Pi.sub_apply, ← hn, smul_assoc, one_smul]
      exact L.smul_mem n (by simp [b₀])
    rw [← hA _ h2 (b₀.equivFun.symm x), ← map_add, add_sub_cancel]
  let f : C(UnitAddTorus (Free.ChooseBasisIndex ℤ L), ℂ) := ⟨f₀,
    hq.isQuotientMap.continuous_iff.2 <| by
      rw [show f₀ ∘ p = A ∘ b₀.equivFunL.symm from funext hfp]; fun_prop⟩
  have hchar : ∀ n x, UnitAddTorus.mFourier n (p x) = e[∑ i, n i * x i] := fun n x ↦ by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, hp, fourier_coe_apply,
      ← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hcoeff : ∀ n, UnitAddTorus.mFourierCoeff f n = latticeFourierCoeff L A (φ n) := fun n ↦ by
    rw [UnitAddTorus.mFourierCoeff_eq_integral f n 0, latticeFourierCoeff,
      covolume_eq_volume_latticeCell, latticeCell, average_fundamentalDomain_eq_cube]
    simp only [Pi.zero_apply, zero_add]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    change UnitAddTorus.mFourier (-n) (p x) • f₀ (p x) = _
    simp only [hchar, hfp]
    congr 4
    refine Eq.trans ?_ (congrArg Neg.neg (hφ n x).symm)
    simp
  have hsum := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f)
    (by rw [funext hcoeff]; exact φ.summable_iff.2 hs) (p (b₀.equivFun y))
  rw [← φ.hasSum_iff]
  change HasSum _ (f₀ (p _)) at hsum
  simp only [hfp, hchar, hcoeff, ← hφ] at hsum
  simpa only [b₀, LinearEquiv.symm_apply_apply, smul_eq_mul, mul_comm, Function.comp_def]
    using hsum

theorem hasSum_latticeFourier_of_summable_norm [CompleteSpace V] {A : E → V}
    (hA : ∀ x ∈ L, Function.Periodic A x) (hc : Continuous A)
    (hs : Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖) (y : E) :
    HasSum (fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν) (A y) := by
  have h1 : Summable fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν :=
    .of_norm (by simpa only [norm_smul, norm_cexp_two_pi_I, one_mul] using hs)
  convert h1.hasSum using 1
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun T ↦ ?_
  have h2 := hasSum_latticeFourier_complex (L := L) (A := fun b ↦ T (A b))
    (fun x hx b ↦ by simp only [hA x hx b]) (by fun_prop)
    (by simpa only [latticeFourierCoeff_clm T hc, Function.comp_def] using hs.of_norm.map T T.continuous) y
  simp only [latticeFourierCoeff_clm T hc, ← map_smul] at h2
  exact h2.unique (T.hasSum h1.hasSum)


end Expansion

section Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def dualLattice (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) L

theorem mem_dualLattice {L : Submodule ℤ E} {y : E} :
    y ∈ dualLattice L ↔ ∀ x ∈ L, ∃ m : ℤ, (m : ℝ) = ⟪x, y⟫ := by
  simp only [dualLattice, LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_one,
    innerₗ_apply_apply, real_inner_comm y, eq_intCast]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem covolume_span_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (o : OrthonormalBasis ι ℝ E) (b : Basis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) = |o.toBasis.det b| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ (b.restrictScalars ℤ) o.toBasis,
    MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis, o.volume_parallelepiped]
  simp only [ENNReal.toReal_one, mul_one]
  congr 2
  ext i
  simp

end Dual

end RHLean.Geometry.NativeTheta.Cusp.Poisson
