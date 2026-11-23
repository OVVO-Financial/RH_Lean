import RHLean.Geometry.NativeThetaCuspLatticeFourier

/-!
# Actual lattice Poisson summation with its covolume

The periodic sum of a continuous, uniformly lattice-dominated function is
integrated over the actual lattice cell. Its Fourier coefficient is the
ordinary Fourier transform divided by the lattice covolume. The proved
Fourier expansion then yields Poisson summation with that exact factor.

Source: Levent Alpöge (with Claude),
CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4,
src/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SummableLatticeExpNegPiMulNormSqDiv.lean
(`continuous_tsum_lattice_translate` through `tsum_poisson_lattice`). The
source mirror states no license; attribution is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Module Set
open scoped RealInnerProductSpace Real FourierTransform BigOperators

namespace RHLean.Geometry.NativeTheta.Cusp.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ V] [DiscreteTopology L] [IsZLattice ℝ L] in

theorem continuous_tsum_lattice_translate [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x) :
    Continuous fun u : E ↦ ∑' x : L, f (x + u) := by
  refine continuous_iff_continuousAt.2 fun u ↦ ?_
  obtain ⟨g, hg, h⟩ := hdom (‖u‖ + 1)
  have : ContinuousOn (fun u : E ↦ ∑' x : L, f (x + u)) (Metric.ball 0 (‖u‖ + 1)) :=
    continuousOn_tsum (fun x ↦ by fun_prop) hg
      fun x v hv ↦ h x v (mem_ball_zero_iff.1 hv).le
  exact this.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ V] [DiscreteTopology L] [IsZLattice ℝ L] in

theorem periodic_tsum_lattice_translate (f : E → V) {z : E} (hz : z ∈ L) :
    Function.Periodic (fun u : E ↦ ∑' x : L, f (x + u)) z := fun u ↦ by
  beta_reduce
  rw [← (Equiv.addRight (⟨z, hz⟩ : L)).tsum_eq fun x : L ↦ f (x + u)]
  refine tsum_congr fun x ↦ ?_
  simp only [Equiv.coe_addRight, Submodule.coe_add]
  congr 1
  abel

omit [NormedSpace ℂ V] in

theorem integrable_of_lattice_translate_dominated {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x) :
    Integrable f := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  obtain ⟨R, hR⟩ := (isBounded_latticeCell L).exists_norm_le
  obtain ⟨g, hg, h⟩ := hdom R
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm,
    (isAddFundamentalDomain_latticeCell L volume).lintegral_eq_tsum'']
  calc ∑' x : L, ∫⁻ u in latticeCell L, ‖f (x +ᵥ u)‖ₑ
      ≤ ∑' x : L, ENNReal.ofReal (g x) * volume (latticeCell L) := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        rw [← setLIntegral_const]
        refine setLIntegral_mono' (measurableSet_latticeCell L) fun u hu ↦ ?_
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h x u (hR u hu))
    _ < ⊤ := by
        rw [ENNReal.tsum_mul_right]
        exact ENNReal.mul_lt_top hg.tsum_ofReal_lt_top (volume_latticeCell_lt_top L)

theorem latticeFourierCoeff_tsum_translate [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x)
    {y : E} (hy : y ∈ dualLattice L) :
    latticeFourierCoeff L (fun u : E ↦ ∑' x : L, f (x + u)) y =
      (ZLattice.covolume L)⁻¹ • 𝓕 f y := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup E volume)
  have hint : Integrable fun v : E ↦ e[-⟪y, v⟫] • f v :=
    (integrable_of_lattice_translate_dominated L hc hdom).norm.mono'
      (continuous_cexp_neg_inner_smul hc y).aestronglyMeasurable
      (.of_forall fun v ↦ by rw [norm_smul, norm_cexp_two_pi_I, one_mul])
  have hF : 𝓕 f y = ∫ v, e[-⟪y, v⟫] • f v := by
    rw [Real.fourier_eq']
    refine integral_congr_ae (.of_forall fun v ↦ ?_)
    simp only [real_inner_comm y]
    congr 2
    push_cast
    ring
  obtain ⟨R, hR⟩ := (isBounded_latticeCell L).exists_norm_le
  obtain ⟨g, hg, h⟩ := hdom R
  rw [hF, (isAddFundamentalDomain_latticeCell L volume).integral_eq_tsum'' _ hint,
    latticeFourierCoeff]
  congr 1
  have h1 : ∀ (x : L) (u : E), e[-⟪y, x +ᵥ u⟫] • f (x +ᵥ u) = e[-⟪y, u⟫] • f (x + u) :=
    fun x u ↦ by
      rw [← cexp_neg_inner_add_lattice hy x.2 u, add_comm u]; rfl
  simp only [h1, ← tsum_const_smul'' e[-⟪y, _⟫]]
  refine (hasSum_integral_of_summable_integral_norm (fun x ↦
    integrableOn_latticeCell_of_continuous L (by fun_prop)) ?_).tsum_eq.symm
  refine .of_norm_bounded (hg.mul_right (volume.real (latticeCell L))) fun x ↦ ?_
  refine norm_setIntegral_le_of_norm_le_const (volume_latticeCell_lt_top L) fun u hu ↦ ?_
  rw [norm_norm, norm_smul, norm_cexp_two_pi_I, one_mul]
  exact h x u (hR u hu)

theorem hasSum_poisson_lattice [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x)
    (hs : Summable fun y : dualLattice L ↦ ‖𝓕 f y‖) (u : E) :
    HasSum (fun y : dualLattice L ↦ (ZLattice.covolume L)⁻¹ • e[⟪(y : E), u⟫] • 𝓕 f y)
      (∑' x : L, f (x + u)) := by
  have h := hasSum_latticeFourier_of_summable_norm (L := L)
    (A := fun u : E ↦ ∑' x : L, f (x + u)) (fun z hz ↦ periodic_tsum_lattice_translate L f hz)
    (continuous_tsum_lattice_translate L hc hdom) (by
      refine ((hs.mul_left ‖(ZLattice.covolume L)⁻¹‖).congr fun y ↦ ?_ :
        Summable fun y : dualLattice L ↦ _)
      rw [latticeFourierCoeff_tsum_translate L hc hdom y.2, norm_smul]) u
  have h' : HasSum (fun y : dualLattice L ↦ e[⟪(y : E), u⟫] •
      latticeFourierCoeff L (fun u : E ↦ ∑' x : L, f (x + u)) y) (∑' x : L, f (x + u)) := h
  convert h' using 2 with y
  rw [latticeFourierCoeff_tsum_translate L hc hdom y.2, smul_comm]

theorem tsum_poisson_lattice [CompleteSpace V] {f : E → V} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (u : E), ‖u‖ ≤ R → ‖f (x + u)‖ ≤ g x)
    (hs : Summable fun y : dualLattice L ↦ ‖𝓕 f y‖) (u : E) :
    ∑' x : L, f (x + u) =
      (ZLattice.covolume L)⁻¹ • ∑' y : dualLattice L, e[⟪(y : E), u⟫] • 𝓕 f y := by
  rw [← (hasSum_poisson_lattice L hc hdom hs u).tsum_eq, tsum_const_smul'']


end RHLean.Geometry.NativeTheta.Cusp.Poisson
