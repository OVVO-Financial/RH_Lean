import RHLean.Geometry.NativeThetaAppellHumbert
import RHLean.Geometry.NativeThetaGaussianSeries
import RHLean.Geometry.NativeGeometricSymplecticBasis

/-!
# A nonzero holomorphic theta section on the actual native periods

The theta functions are actual Gaussian periodizations on the original
integral lattice. Their convergence follows from positivity of the native
Hermitian form and discreteness of the original period map. Their
automorphy is the previously constructed Appell--Humbert cocycle.

Nonvanishing is proved, not supplied: the perfect integral polarization
realizes the coordinates of an integral basis as imaginary Hermitian
pairings. If all the periodizations vanished at their centers, uniqueness
of absolutely convergent torus Fourier series would force their constant
coefficient, which is one, to vanish. No Euclidean replacement lattice,
chosen theta section, large tensor power, moduli scheme or algebraization
is assumed. The final theorem chooses one actual half-different before
all ranks and signatures and constructs the section and its invariant
Gaussian fiber metric on those same periods.

This supplies an analytic theta section. Integral algebraization, global
cusp spanning and Petersson normalization remain separate statements.

Mathematical source: Levent Alpöge (with Claude),
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`,
`Development/AbelianVarietyTheory/Proofs/TorusSplitting/`
`CoeffEqZeroOfOrthonormal.lean`, and `Proofs/ToricGeometry/`
`ExistsThetaSeriesApplyNeZeroOfLargeForm.lean`.
The source mirror states no license; attribution is preserved without
assigning one. No upstream compiled object or terminal RH theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField Filter
open scoped BigOperators Topology Pointwise ComplexConjugate

namespace RHLean.Geometry.NativeTheta.NonzeroSection

open NativeGeometricPeriods AppellHumbert

section Matrix

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

private theorem differentiable_herm_left (w : Fin g → ℂ) :
    Differentiable ℂ fun z => hermForm Hm z w := by
  simp only [hermForm, dotProduct, Matrix.mulVec]
  fun_prop

private theorem hermForm_sum_real_smul_im {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (v : ι → Fin g → ℂ) (w : Fin g → ℂ) :
    (hermForm Hm (∑ i, t i • v i) w).im =
      ∑ i, t i * (hermForm Hm (v i) w).im := by
  simp only [hermForm, sum_dotProduct, smul_dotProduct, Complex.im_sum,
    Complex.smul_im, smul_eq_mul]

end Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
  {H : NativeGeometricHost E} (D : NativeGeometricDatum H) {g : ℕ}
  (P : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)

/-- Each summand is an entire exponential divided by the constructed
nonvanishing automorphy factor. -/
def periodizationTerm (w : Fin g → ℂ) (x : D.La) (z : Fin g → ℂ) : ℂ :=
  (factor D P Hm x z)⁻¹ * Complex.exp (Real.pi * hermForm Hm (z + P x) w)

theorem periodizationTerm_eq (w : Fin g → ℂ) (x : D.La) (z : Fin g → ℂ) :
    periodizationTerm D P Hm w x z = (phase D x)⁻¹ * Complex.exp
      (Real.pi * hermForm Hm (z + P x) w -
        (Real.pi * hermForm Hm z (P x) + Real.pi / 2 * hermForm Hm (P x) (P x))) := by
  rw [periodizationTerm, factor, mul_inv, ← Complex.exp_neg, mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

theorem differentiable_periodizationTerm (w : Fin g → ℂ) (x : D.La) :
    Differentiable ℂ (periodizationTerm D P Hm w x) := by
  have h1 : Differentiable ℂ fun z => hermForm Hm (z + P x) w :=
    (differentiable_herm_left Hm w).comp (differentiable_id.add_const _)
  have h2 := differentiable_herm_left Hm (P x)
  simp_rw [show periodizationTerm D P Hm w x = fun z =>
      (phase D x)⁻¹ * Complex.exp
        (Real.pi * hermForm Hm (z + P x) w -
          (Real.pi * hermForm Hm z (P x) + Real.pi / 2 * hermForm Hm (P x) (P x)))
      from funext (periodizationTerm_eq D P Hm w x)]
  fun_prop

theorem periodizationTerm_translate (hH : Hm.IsHermitian)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (w : Fin g → ℂ) (x y : D.La) (z : Fin g → ℂ) :
    periodizationTerm D P Hm w x (z + P y) =
      factor D P Hm y z * periodizationTerm D P Hm w (y + x) z := by
  unfold periodizationTerm
  rw [factor_add D P Hm hH hEF y x z, map_add, ← add_assoc]
  have h1 := factor_ne_zero D P Hm x (z + P y)
  have h2 := factor_ne_zero D P Hm y z
  field_simp [h1, h2]; ring

/-- Completing the Hermitian square keeps the exact pi normalization. -/
theorem norm_periodizationTerm (hH : Hm.IsHermitian)
    (w : Fin g → ℂ) (x : D.La) (z : Fin g → ℂ) :
    ‖periodizationTerm D P Hm w x z‖ =
      Real.exp (Real.pi / 2 * ((hermForm Hm z z).re + (hermForm Hm w w).re)) *
        Real.exp (-(Real.pi / 2) *
          (hermForm Hm (P x + (z - w)) (P x + (z - w))).re) := by
  rw [periodizationTerm_eq, norm_mul, norm_inv, norm_phase, inv_one, one_mul,
    Complex.norm_exp, ← Real.exp_add]
  congr 1
  obtain ⟨u, rfl⟩ : ∃ u, z = u + w := ⟨z - w, by simp⟩
  rw [add_sub_cancel_right]
  have hs : ∀ a b, (hermForm Hm b a).re = (hermForm Hm a b).re := fun a b => by
    simpa only [Complex.star_def, Complex.conj_re] using
      congrArg Complex.re (hermForm_swap Hm hH a b)
  have hcast : (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast; rfl
  simp only [hcast, hermForm_add_left, hermForm_add_right,
    Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul]
  rw [hs u w, hs u (P x), hs w (P x)]
  ring

theorem summable_period_gaussian (hP : Function.Injective P)
    (hd : DiscreteTopology P.range) {a : ℝ} (ha : 0 < a) :
    Summable fun x : D.La => Real.exp (-a * ‖P x‖ ^ 2) := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  letI : DiscreteTopology L := hd
  let e : D.La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hP
  exact (e.toEquiv.summable_iff
    (f := fun x : L => Real.exp (-a * ‖(x : Fin g → ℂ)‖ ^ 2))).2
      (GaussianSeries.summable_gaussian L ha)

/-- The positive native form supplies an actual Gaussian bound in the
existing coordinate norm, without identifying that norm with the form. -/
theorem exists_periodizationTerm_gaussian_bound (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    ∃ a : ℝ, 0 < a ∧ ∀ w x z, ‖periodizationTerm D P Hm w x z‖ ≤
      Real.exp (Real.pi / 2 * ((hermForm Hm z z).re + (hermForm Hm w w).re)) *
        Real.exp (-a * ‖P x + (z - w)‖ ^ 2) := by
  obtain ⟨c, hc, hco⟩ := GaussianSeries.exists_coercive Hm hpos
  change ∀ z : Fin g → ℂ, c * ‖z‖ ^ 2 ≤ (hermForm Hm z z).re at hco
  refine ⟨Real.pi / 2 * c, by positivity, fun w x z => ?_⟩
  rw [norm_periodizationTerm D P Hm hH]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left (hco (P x + (z - w)))
    (show 0 ≤ Real.pi / 2 by positivity)
  nlinarith

theorem summable_periodizationTerm (hP : Function.Injective P)
    (hd : DiscreteTopology P.range) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (w z : Fin g → ℂ) : Summable fun x => periodizationTerm D P Hm w x z := by
  obtain ⟨a, ha, hbound⟩ := exists_periodizationTerm_gaussian_bound D P Hm hH hpos
  refine .of_norm_bounded
    (((summable_period_gaussian D P hP hd (half_pos ha)).mul_left
      (Real.exp (a * ‖z - w‖ ^ 2))).mul_left
      (Real.exp (Real.pi / 2 * ((hermForm Hm z z).re + (hermForm Hm w w).re)))) ?_
  intro x
  exact (hbound w x z).trans (mul_le_mul_of_nonneg_left
    (GaussianSeries.gaussian_translate_le ha.le (P x) (le_refl ‖z - w‖))
    (Real.exp_pos _).le)

/-- The actual Gaussian periodization, rather than an abstract section. -/
def theta (w z : Fin g → ℂ) : ℂ := ∑' x : D.La, periodizationTerm D P Hm w x z

theorem differentiable_theta (hP : Function.Injective P)
    (hd : DiscreteTopology P.range) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (w : Fin g → ℂ) : Differentiable ℂ (theta D P Hm w) := by
  obtain ⟨a, ha, hbound⟩ := exists_periodizationTerm_gaussian_bound D P Hm hH hpos
  have hc : Continuous fun z => (hermForm Hm z z).re := GaussianSeries.continuous_form Hm
  rw [← differentiableOn_univ]
  refine GaussianSeries.differentiableOn_tsum_of_locally_normal
    (F := fun x z => periodizationTerm D P Hm w x z) isOpen_univ
    (fun x => (differentiable_periodizationTerm D P Hm w x).differentiableOn)
    (fun z _ => ?_)
  have hz : ∀ᶠ v in 𝓝 z, (hermForm Hm v v).re < (hermForm Hm z z).re + 1 ∧
      ‖v - w‖ < ‖z - w‖ + 1 :=
    (hc.continuousAt.eventually (gt_mem_nhds (lt_add_one _))).and
      ((show Continuous fun v : Fin g → ℂ => ‖v - w‖ by fun_prop).continuousAt.eventually
        (gt_mem_nhds (lt_add_one _)))
  refine ⟨_, hz, _,
    ((summable_period_gaussian D P hP hd (half_pos ha)).mul_left
      (Real.exp (a * (‖z - w‖ + 1) ^ 2))).mul_left
      (Real.exp (Real.pi / 2 * ((hermForm Hm z z).re + 1 + (hermForm Hm w w).re))),
    fun x v hv => (hbound w x v).trans ?_⟩
  refine mul_le_mul ?_
    (GaussianSeries.gaussian_translate_le ha.le (P x) hv.2.le)
    (Real.exp_pos _).le (Real.exp_pos _).le
  gcongr
  exact hv.1.le

theorem theta_translate (hH : Hm.IsHermitian)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (w : Fin g → ℂ) (y : D.La) (z : Fin g → ℂ) :
    theta D P Hm w (z + P y) = factor D P Hm y z * theta D P Hm w z := by
  unfold theta
  rw [← (Equiv.addLeft y).tsum_eq (fun x => periodizationTerm D P Hm w x z),
    ← tsum_mul_left]
  exact tsum_congr fun x => periodizationTerm_translate D P Hm hH hEF w x y z

theorem theta_fiberNormSq_translate (hH : Hm.IsHermitian)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (w : Fin g → ℂ) (x : D.La) (z : Fin g → ℂ) :
    fiberNormSq Hm (z + P x) (theta D P Hm w (z + P x)) =
      fiberNormSq Hm z (theta D P Hm w z) := by
  rw [theta_translate D P Hm hH hEF]
  exact fiberNormSq_translate D P Hm hH x z _

/-- The Fourier coefficient is defined from the same canonical phase and
Hermitian form. In particular its value at zero is one. -/
def coefficient (x : D.La) : ℂ :=
  (phase D x)⁻¹ * Complex.exp (-(Real.pi / 2 * hermForm Hm (P x) (P x)))

@[simp] theorem coefficient_zero : coefficient D P Hm 0 = 1 := by
  simp [coefficient, hermForm]

theorem norm_coefficient (x : D.La) :
    ‖coefficient D P Hm x‖ = Real.exp (-(Real.pi / 2 * (hermForm Hm (P x) (P x)).re)) := by
  rw [coefficient, norm_mul, norm_inv, norm_phase, inv_one, one_mul, Complex.norm_exp]
  have hcast : (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.neg_re, Complex.re_ofReal_mul]

theorem summable_norm_coefficient (hP : Function.Injective P)
    (hd : DiscreteTopology P.range)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    Summable fun x => ‖coefficient D P Hm x‖ := by
  obtain ⟨c, hc, hco⟩ := GaussianSeries.exists_coercive Hm hpos
  change ∀ z : Fin g → ℂ, c * ‖z‖ ^ 2 ≤ (hermForm Hm z z).re at hco
  refine .of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
    (summable_period_gaussian D P hP hd (a := Real.pi / 2 * c) (by positivity))
  rw [norm_coefficient, Real.exp_le_exp]
  have := mul_le_mul_of_nonneg_left (hco (P x))
    (show 0 ≤ Real.pi / 2 by positivity)
  nlinarith

/-- At the center the actual periodization is an absolutely convergent
Fourier series, with the minus sign fixed by the chosen inverse-factor sum. -/
theorem theta_centre (hH : Hm.IsHermitian) (w : Fin g → ℂ) :
    theta D P Hm w w = Complex.exp (Real.pi * hermForm Hm w w) *
      ∑' x : D.La, coefficient D P Hm x *
        Complex.exp (-(2 * Real.pi * Complex.I * ((hermForm Hm w (P x)).im : ℂ))) := by
  rw [theta, ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  have hcross : hermForm Hm w (P x) - hermForm Hm (P x) w =
      2 * ((hermForm Hm w (P x)).im : ℂ) * Complex.I := by
    rw [hermForm_swap Hm hH w (P x), Complex.star_def, Complex.sub_conj]
    push_cast
    ring
  calc
    periodizationTerm D P Hm w x w = (phase D x)⁻¹ * Complex.exp
        (Real.pi * hermForm Hm w w + (-(Real.pi / 2 * hermForm Hm (P x) (P x))) +
          (-(2 * Real.pi * Complex.I * ((hermForm Hm w (P x)).im : ℂ)))) := by
      rw [periodizationTerm_eq, hermForm_add_left]
      congr 2
      linear_combination -(Real.pi : ℂ) * hcross
    _ = _ := by
      simp only [Complex.exp_add]
      unfold coefficient
      ring

/-- Nonvanishing is forced by the coefficient at zero and the actual
perfect integral polarization. No nonzero section premise is used. -/
theorem exists_theta_centre_ne_zero (hP : Function.Injective P)
    (hd : DiscreteTopology P.range) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) :
    ∃ w : Fin g → ℂ, theta D P Hm w w ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨bas, _⟩ := NativeGeometricSymplectic.exists_isSympBasis E H D
  choose d hd' using fun j =>
    D.unimod.2 ((LinearMap.proj j).comp bas.symm.toLinearMap)
  have hcs := summable_norm_coefficient D P Hm hP hd hpos
  have key := GaussianSeries.coeff_eq_zero_of_fourier
    (c := fun n => coefficient D P Hm (bas n))
    ((bas.toEquiv.summable_iff (f := fun x => ‖coefficient D P Hm x‖)).2 hcs)
    (fun t => ?_) 0
  · simpa using key
  · set v : Fin g → ℂ := ∑ j, (-(t j) : ℝ) • P (d j) with hv
    have h1 := theta_centre D P Hm hH v
    rw [hcon v, eq_comm, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)] at h1
    rw [← h1, ← bas.toEquiv.tsum_eq
      (fun x => coefficient D P Hm x *
        Complex.exp (-(2 * Real.pi * Complex.I * ((hermForm Hm v (P x)).im : ℂ))))]
    refine tsum_congr fun n => ?_
    have h2 : ∀ j, (hermForm Hm (P (d j)) (P (bas n))).im = (n j : ℝ) := by
      intro j
      rw [hEF, hd' j]
      simp
    have h3 : (hermForm Hm v (P (bas n))).im = -(∑ j, (n j : ℝ) * t j) := by
      rw [hv, hermForm_sum_real_smul_im, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h2]
      ring
    rw [h3]
    congr 2
    push_cast
    ring

theorem exists_nonzero_theta (hP : Function.Injective P)
    (hd : DiscreteTopology P.range) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) :
    ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ ≠ 0 ∧
      (∀ x z, θ (z + P x) = factor D P Hm x z * θ z) ∧
      ∀ x z, fiberNormSq Hm (z + P x) (θ (z + P x)) = fiberNormSq Hm z (θ z) := by
  obtain ⟨w, hw⟩ := exists_theta_centre_ne_zero D P Hm hP hd hH hpos hEF
  refine ⟨theta D P Hm w, differentiable_theta D P Hm hP hd hH hpos w,
    fun h => hw ?_, theta_translate D P Hm hH hEF w,
    theta_fiberNormSq_translate D P Hm hH hEF w⟩
  simpa only [Pi.zero_apply] using congrFun h w

end RHLean.Geometry.NativeTheta.NonzeroSection

namespace RHLean.Analysis.AlpogeThin

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeGeometricPeriods
open RHLean.Geometry.NativeTheta.AppellHumbert
open RHLean.Geometry.NativeTheta.NonzeroSection
open NativeRawHostPolarization

/-- The actual native datum and period theorem supply every analytic input
to the constructed nonzero theta section and its invariant fiber metric. -/
theorem nativeDyadicPrescribedPeriod_exists_nonzeroTheta
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (B : Ideal (𝓞 (nativeDyadicHostRaw e q d he hH).E))
    (hB : let H := nativeDyadicHostRaw e q d he hH
      differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (k m j : ℕ) (hk : m + 3 ≤ k) (hj : j ≤ m) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
    let P := prescribedPeriodMap H.toHostRaw B hB k m j
    ∃ Hm : Matrix (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1)))
        (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1))) ℂ,
      Hm.IsHermitian ∧ (∀ z, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) ∧
      ∃ θ : (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1)) → ℂ) → ℂ,
        Differentiable ℂ θ ∧ θ ≠ 0 ∧
        (∀ x z, θ (z + P x) = factor D P Hm x z * θ z) ∧
        ∀ x z, fiberNormSq Hm (z + P x) (θ (z + P x)) = fiberNormSq Hm z (θ z) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
  let P := prescribedPeriodMap H.toHostRaw B hB k m j
  have hP := (nativeDyadicPrescribedGeometricDatum_isPeriod e q d he hH B hB k m j hk hj).2
  obtain ⟨Hm, hHerm, hpos, hEF⟩ := hP.2.2.2.2
  exact ⟨Hm, hHerm, hpos, hEF,
    exists_nonzero_theta D P Hm hP.2.1 hP.2.2.1 hHerm hpos hEF⟩

/-- A single actually constructed half-different supplies nonzero
holomorphic theta sections for every prescribed native rank/signature.
The half-different, phase, metric and section are all supplied here. -/
theorem nativeDyadicHost_exists_nonzeroThetaSections
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    ∃ (B : Ideal (𝓞 H.E))
      (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)),
      B ⊔ H.conj • B = ⊤ ∧
      (∀ σ : H.E ≃ₐ[ℚ] H.E, H.gal σ ∈ (nativeDyadicFrame e).Psi → σ • B = B) ∧
      ∀ k m : ℕ, ∀ hk : m + 3 ≤ k, ∀ j : ℕ, 1 ≤ j → ∀ hj : j ≤ m,
        let D := nativeDyadicPrescribedGeometricDatum e q d he hH B hB k m j hk hj
        let P := prescribedPeriodMap H.toHostRaw B hB k m j
        ∃ Hm : Matrix (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1)))
            (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1))) ℂ,
          Hm.IsHermitian ∧ (∀ z, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
          (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) ∧
          ∃ θ : (Fin ((cmTypeFinset H.toHostRaw).card * (k + m - 1)) → ℂ) → ℂ,
            Differentiable ℂ θ ∧ θ ≠ 0 ∧
            (∀ x z, θ (z + P x) = factor D P Hm x z * θ z) ∧
            ∀ x z, fiberNormSq Hm (z + P x) (θ (z + P x)) =
              fiberNormSq Hm z (θ z) := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  obtain ⟨B, hB, hcop, hinv, _⟩ := nativeDyadicHost_exists_prescribedPeriods e q d he hH
  refine ⟨B, hB, hcop, hinv, ?_⟩
  intro k m hk j _ hj
  exact nativeDyadicPrescribedPeriod_exists_nonzeroTheta e q d he hH B hB k m j hk hj

end RHLean.Analysis.AlpogeThin

end
