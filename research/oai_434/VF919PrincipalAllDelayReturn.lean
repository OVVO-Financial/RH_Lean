import «research.oai_434.VF919PrincipalResponseMass»
import «research.oai_434.VF919FiniteSlotReflectedGain»

/-!
# The original principal residue returns every finite delay

Claim 20261110-coordinator-2309-EST/FFR2, independently accepted by
20261111-referee-1. The whole rational multiplier is shifted to the right
line before the finite response is integrated. Pool data stay fixed at the
outer scale, and no delay is discarded when its inner argument is below one.
The physical remainder assembly and response inversion are separate results.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open Complex MeasureTheory Set Filter
namespace SevenEighths.PrincipalAllDelayReturn
open HeckeFamily HeckeSignal Continuation PrincipalSignalComparison
open PrincipalSlotEstimate PrincipalMellinResidues

namespace FiniteResponse

/-- Apply the complete labelled response to one fixed signal. -/
def applyTerms (f : ℝ → ℂ) (c Z : ℝ) : PrincipalSlotEstimate.FiniteResponse.Terms → ℂ
  | [] => 0
  | a :: p => a.2 * (Real.exp (a.1 * c) : ℂ) * f (Z / Real.exp a.1) +
      applyTerms f c Z p

end FiniteResponse

open PrincipalSlotEstimate.FiniteResponse

/-- Arbitrary physical exponent, with the original raw L-function quotient. -/
def slotResidueC {κ ι : Type*} (chi : Character) (H : ℂ → ℂ) (c a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A eta : κ → ι → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    (Z : ℂ) ^ (((a : ℂ) + t * I) + (c : ℂ)) *
      Complex.exp ((((a : ℂ) + t * I) - 5 / 6) ^ 2) *
      H ((a : ℂ) + t * I) / LFunction chi ((a : ℂ) + t * I) *
      slotRatio S T w Q A eta ((a : ℂ) + t * I)

theorem slotResidueC_eq_reciprocal {κ ι : Type*}
    (chi : Character) (H : ℂ → ℂ) (c a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A eta : κ → ι → ℂ) :
    slotResidueC chi H c a Z S T w Q A eta =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        gaussianContourIntegrand (quotient chi H) c Z ((a : ℂ) + t * I) *
          slotRatio S T w Q A eta ((a : ℂ) + t * I) := by
  unfold slotResidueC
  congr 1
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal chi a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv, ht]
  ring

private theorem slotRatio_differentiableOn {κ ι : Type*}
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A eta : κ → ι → ℂ) {P a : ℝ} (h : SlotBounds S T w Q A eta P)
    (ha : 7 / 8 ≤ a) :
    DifferentiableOn ℂ (slotRatio S T w Q A eta)
      {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} := by
  intro s hs
  have hd (j : κ) (hj : j ∈ S) (i : ι) (hi : i ∈ T j) :
      DifferentiableAt ℂ (principalSlot (Q j i) (A j i) (eta j i)) s :=
    principalSlot_differentiableAt (h.lower.trans (h.norm_lower j hj i hi))
      (h.phase_bound j hj i hi) (h.target_unit j hj i hi).le (ha.trans hs.1)
  apply DifferentiableAt.differentiableWithinAt
  unfold slotRatio slotProduct
  fun_prop (disch := aesop)

/-- Shift the complete original product, not a termwise left-shifted surrogate. -/
theorem slotResidueC_shift_right {κ ι : Type*}
    (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c : ℝ) {a Z : ℝ} (ha : 7 / 8 < a) (ha2 : a ≤ 2)
    (hbeta : HeckeZeroSupremum.beta < a) (hZ : 1 ≤ Z)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A eta : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A eta P) :
    slotResidueC chi H c a Z S T w Q A eta =
      slotResidueC chi H c 2 Z S T w Q A eta := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound chi a hbeta
  rw [slotResidueC_eq_reciprocal, slotResidueC_eq_reciprocal]
  congr 1
  let B := 1 + slotErrorConstant S * P ^ (-(7 / 8 : ℝ))
  have hB : 0 ≤ B := by
    have hP : 0 ≤ P := by linarith [h.lower]
    dsimp [B, slotErrorConstant]
    positivity
  apply vertical_integral_eq_of_polynomial_gaussian_bound _ 2 ha2
    ((gaussianContourIntegrand_differentiableOn
      (HeckeSignalShift.quotient_holomorphic chi H hH ha hbeta) c hZ0).mul
        (slotRatio_differentiableOn S T w Q A eta h ha.le))
    (C := Z ^ (2 + c) * Real.exp ((2 - 5 / 6 : ℝ) ^ 2) * ((3 / 2) * C) * B)
  intro b hba y
  change ‖gaussianContourIntegrand (quotient chi H) c Z ((b : ℂ) + y * I) *
    slotRatio S T w Q A eta ((b : ℂ) + y * I)‖ ≤ _
  rw [norm_mul, norm_gaussianContourIntegrand _ _ _ _ hZ0]
  have hzpow : Z ^ (b + c) ≤ Z ^ (2 + c) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith [hba.2])
  have hexp : Real.exp ((b - 5 / 6) ^ 2) ≤ Real.exp ((2 - 5 / 6 : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hba.1, hba.2]
  have hq := HeckeSignalShift.quotient_polynomial_bound chi H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (b : ℂ) + y * I) (by simpa using hba)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  have hr : ‖slotRatio S T w Q A eta ((b : ℂ) + y * I)‖ ≤ B :=
    slotRatio_bound S T w Q A eta h (by simpa using ha.le.trans hba.1)
  calc
    _ ≤ (Z ^ (2 + c) * Real.exp ((2 - 5 / 6 : ℝ) ^ 2)) *
        (((3 / 2) * C) * (1 + |y| ^ 2)) * Real.exp (-(y ^ 2)) * B := by
      gcongr
    _ = _ := by unfold polynomialGaussian; ring

private theorem kernel_two_bound (chi : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c : ℝ) {Z : ℝ} (hZ : 0 < Z) (y : ℝ) :
    ‖gaussianContourIntegrand (quotient chi H) c Z ((2 : ℂ) + y * I)‖ ≤
      (Z ^ (2 + c) * Real.exp ((2 - 5 / 6 : ℝ) ^ 2) * quotientBound) *
        Real.exp (-(y ^ 2)) := by
  have hn := norm_gaussianContourIntegrand (quotient chi H) c 2 y hZ
  simp only [Complex.ofReal_ofNat] at hn
  rw [hn]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (quotient_bound chi H hb (by simp))
      (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le))
    (Real.exp_pos _).le

private theorem kernel_two_integrable (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    Integrable (fun y : ℝ =>
      gaussianContourIntegrand (quotient chi H) c Z ((2 : ℂ) + y * I)) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (HeckeSignalShift.quotient_holomorphic chi H hH (a := 2) (by norm_num)
      (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one (by norm_num))) c hZ
  apply integrable_of_gaussian_bound _ _
    (hh.continuousOn.comp_continuous (by fun_prop)
      (by intro y; simp)).aestronglyMeasurable
  exact kernel_two_bound chi H hb c hZ

/-- Mellin dilation holds for every real delay and every positive inner argument. -/
theorem gaussian_atom_dilation (G : ℂ → ℂ) (c : ℝ) {Z : ℝ}
    (hZ : 0 < Z) (a : Atom) (s : ℂ) :
    gaussianContourIntegrand G c Z s * evalAtom s a =
      (a.2 * (Real.exp (a.1 * c) : ℂ)) *
        gaussianContourIntegrand G c (Z / Real.exp a.1) s := by
  have hx : 0 < Z / Real.exp a.1 := div_pos hZ (Real.exp_pos _)
  unfold gaussianContourIntegrand evalAtom
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hZ.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hZ.le, ← Complex.ofReal_log hx.le,
    Real.log_div hZ.ne' (Real.exp_pos _).ne', Real.log_exp,
    Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_mul]
  calc
    _ = a.2 * (Complex.exp ((Real.log Z : ℂ) * (s + c)) *
        Complex.exp (-(a.1 : ℂ) * s)) * Complex.exp ((s - 5 / 6) ^ 2) * G s := by ring
    _ = a.2 * (Complex.exp ((a.1 : ℂ) * c) *
        Complex.exp (((Real.log Z : ℂ) - a.1) * (s + c))) *
          Complex.exp ((s - 5 / 6) ^ 2) * G s := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 3
      ring
    _ = _ := by ring

private theorem response_integrable (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c : ℝ) {Z : ℝ} (hZ : 0 < Z) (p : Terms) :
    Integrable (fun y : ℝ =>
      gaussianContourIntegrand (quotient chi H) c Z ((2 : ℂ) + y * I) *
        eval ((2 : ℂ) + y * I) p) := by
  induction p with
  | nil => simp [eval]
  | cons a p ih =>
    simp only [eval, mul_add]
    apply Integrable.add _ ih
    simp_rw [gaussian_atom_dilation _ c hZ a]
    exact (kernel_two_integrable chi H hH hb c (div_pos hZ (Real.exp_pos _))).const_mul _

/-- Finite integration retains repeated labels and all arguments below one. -/
theorem finite_response_contour (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c : ℝ) {Z : ℝ} (hZ : 0 < Z) (p : Terms) :
    (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ,
      gaussianContourIntegrand (quotient chi H) c Z ((2 : ℂ) + y * I) *
        (1 + eval ((2 : ℂ) + y * I) p) =
      signal chi H c Z + FiniteResponse.applyTerms (signal chi H c) c Z p := by
  have ht : (1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ,
      gaussianContourIntegrand (quotient chi H) c Z ((2 : ℂ) + y * I) *
        eval ((2 : ℂ) + y * I) p =
      FiniteResponse.applyTerms (signal chi H c) c Z p := by
    induction p with
    | nil => simp [eval, FiniteResponse.applyTerms]
    | cons a p ih =>
      have hi := (kernel_two_integrable chi H hH hb c
        (div_pos hZ (Real.exp_pos a.1))).const_mul (a.2 * (Real.exp (a.1 * c) : ℂ))
      simp only [eval, mul_add, FiniteResponse.applyTerms]
      simp_rw [gaussian_atom_dilation _ c hZ a]
      rw [integral_add hi (response_integrable chi H hH hb c hZ p),
        integral_const_mul, mul_add, ih,
        signal_eq_contour chi H c (div_pos hZ (Real.exp_pos a.1))]
      ring
  simp only [mul_add, mul_one]
  rw [integral_add (kernel_two_integrable chi H hH hb c hZ)
    (response_integrable chi H hH hb c hZ p), mul_add, ht,
    signal_eq_contour chi H c hZ]

/-- Explicit all-delay FFR2 estimate. The order and minimum length precede Z. -/
theorem slotResidueC_all_delay_error {κ ι : Type*}
    (chi : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c : ℝ) {a Z m : ℝ} (ha : 7 / 8 < a) (ha2 : a ≤ 2)
    (hbeta : HeckeZeroSupremum.beta < a) (hZ : 1 ≤ Z)
    (K : ℕ) (horder : 2 ≤ (7 / 8 : ℝ) * m * (K + 1))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A eta : κ → ι → ℂ) (h : SlotBounds S T w Q A eta (Z ^ m)) :
    ‖slotResidueC chi H c a Z S T w Q A eta -
        (signal chi H c Z + FiniteResponse.applyTerms (signal chi H c) c Z
          (principalProductResponseTerms K S T w Q A eta))‖ ≤
      (S.card * (5 : ℝ) ^ S.card * 4 * 2 ^ (K + 1)) *
        endpointConstant 2 * Z ^ c := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  let p := principalProductResponseTerms K S T w Q A eta
  let C : ℝ := S.card * (5 : ℝ) ^ S.card * 4 * 2 ^ (K + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let f := fun y : ℝ => gaussianContourIntegrand (quotient chi H) c Z ((2 : ℂ) + y * I)
  have hf := kernel_two_integrable chi H hH hb c hZ0
  have hr : Continuous (fun y : ℝ => slotRatio S T w Q A eta ((2 : ℂ) + y * I)) := by
    simpa only [Complex.ofReal_ofNat] using
      slotRatio_continuous_line S T w Q A eta h (a := 2) (by norm_num)
  have hprod := hf.mul_bdd hr.aestronglyMeasurable
    (ae_of_all _ (fun y => slotRatio_bound S T w Q A eta h
      (s := (2 : ℂ) + y * I) (by norm_num)))
  have hfin : Integrable (fun y : ℝ => f y * (1 + eval ((2 : ℂ) + y * I) p)) := by
    simp only [mul_add, mul_one]
    exact hf.add (response_integrable chi H hH hb c hZ0 p)
  have herror (y : ℝ) :
      ‖slotRatio S T w Q A eta ((2 : ℂ) + y * I) -
        (1 + eval ((2 : ℂ) + y * I) p)‖ ≤ C * Z ^ (-2 : ℝ) := by
    rw [principal_product_response_terms_eval K S T w Q A eta _
      (fun j hj i hi => lt_of_lt_of_le (by linarith [h.lower]) (h.norm_lower j hj i hi))
      (fun j hj => (h.mass_pos j hj).ne')]
    exact weighted_principal_product_partial_power S T w Q A eta _ Z m 2 K
      hZ h.lower horder (by norm_num) h.weight_nonneg h.norm_lower
      h.phase_bound h.target_unit h.mass_pos
  rw [slotResidueC_shift_right chi H hH hb c ha ha2 hbeta hZ S T w Q A eta h,
    slotResidueC_eq_reciprocal, ← finite_response_contour chi H hH hb c hZ0 p,
    ← mul_sub]
  simp only [Complex.ofReal_ofNat]
  rw [← integral_sub hprod hfin, norm_mul]
  have hg : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have hbound (y : ℝ) :
      ‖f y * slotRatio S T w Q A eta ((2 : ℂ) + y * I) -
        f y * (1 + eval ((2 : ℂ) + y * I) p)‖ ≤
      (Z ^ (2 + c) * Real.exp ((2 - 5 / 6 : ℝ) ^ 2) * quotientBound *
        (C * Z ^ (-2 : ℝ))) * Real.exp (-(y ^ 2)) := by
    rw [← mul_sub, norm_mul]
    have hn := mul_le_mul (kernel_two_bound chi H hb c hZ0 y) (herror y)
      (norm_nonneg _) (by have := quotientBound_nonneg; positivity)
    convert hn using 1
    ring
  have hn := norm_integral_le_of_norm_le (hg.const_mul
    (Z ^ (2 + c) * Real.exp ((2 - 5 / 6 : ℝ) ^ 2) * quotientBound *
      (C * Z ^ (-2 : ℝ)))) (ae_of_all _ hbound)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1 / (2 * Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  have hp : Z ^ (2 + c) * Z ^ (-2 : ℝ) = Z ^ c := by
    rw [← Real.rpow_add hZ0]
    congr 1
    ring
  convert hm using 1
  dsimp [C]
  unfold endpointConstant
  linear_combination -((S.card * (5 : ℝ) ^ S.card * 4 * 2 ^ (K + 1)) *
    ‖(1 / (2 * Real.pi) : ℂ)‖ * Real.exp ((2 - 5 / 6 : ℝ) ^ 2) * quotientBound *
      (∫ y : ℝ, Real.exp (-(y ^ 2)))) * hp

/-- Exact original physical normalization at the tilted first exponent. -/
theorem normalized_source_eq_slotResidueC {κ ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal HeckeFamily.O) [NeZero M]
    (chi : Character) (a x Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A eta : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : ∀ t : ℝ, B ((a : ℂ) + t * I) 1 (1 / 6) =
      slotProduct S T w Q A eta ((a : ℂ) + t * I)) :
    sourceResidueIntegral W0 W1 M chi a (Z ^ x) Y Z H B /
      (sourceResidueConstant W0 W1 M *
        (Probe.principalScalar S Z (1 / 6) (slotMass T w) : ℂ)) =
      slotResidueC chi (fun s => H s 1 (1 / 6))
        (x / 3 - 5 / 6 + 1 / 36) a Z S T w Q A eta := by
  unfold sourceResidueIntegral ProbePhysical.verticalIntegral slotResidueC
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact normalized_source_double_residue_variable_x W0 W1 M chi x Y Z hZ _
    (H _) (B _) S T w Q A eta hc (hB _)

/-- Full original residue, same signal and outer-frozen finite coefficients. -/
theorem normalized_source_all_delay_error {κ ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal HeckeFamily.O) [NeZero M]
    (chi : Character) (H B : ℂ → ℂ → ℂ → ℂ)
    (hH : DifferentiableOn ℂ (fun s => H s 1 (1 / 6)) {s : ℂ | 7 / 8 < s.re})
    (hb : ∀ s : ℂ, 7 / 8 < s.re → ‖H s 1 (1 / 6) - 1‖ ≤ 1 / 2)
    (x Y : ℝ) {a Z m : ℝ} (ha : 7 / 8 < a) (ha2 : a ≤ 2)
    (hbeta : HeckeZeroSupremum.beta < a) (hZ : 1 ≤ Z)
    (K : ℕ) (horder : 2 ≤ (7 / 8 : ℝ) * m * (K + 1))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A eta : κ → ι → ℂ) (h : SlotBounds S T w Q A eta (Z ^ m))
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : ∀ t : ℝ, B ((a : ℂ) + t * I) 1 (1 / 6) =
      slotProduct S T w Q A eta ((a : ℂ) + t * I)) :
    let c := x / 3 - 5 / 6 + 1 / 36
    let f := signal chi (fun s => H s 1 (1 / 6)) c
    ‖sourceResidueIntegral W0 W1 M chi a (Z ^ x) Y Z H B /
        (sourceResidueConstant W0 W1 M *
          (Probe.principalScalar S Z (1 / 6) (slotMass T w) : ℂ)) -
        (f Z + FiniteResponse.applyTerms f c Z
          (principalProductResponseTerms K S T w Q A eta))‖ ≤
      (S.card * (5 : ℝ) ^ S.card * 4 * 2 ^ (K + 1)) * endpointConstant 2 * Z ^ c := by
  dsimp only
  rw [normalized_source_eq_slotResidueC W0 W1 M chi a x Y Z
    (zero_lt_one.trans_le hZ) H B S T w Q A eta hc hB]
  exact slotResidueC_all_delay_error chi _ hH hb _ ha ha2 hbeta hZ K horder S T w Q A eta h

/-- The original excluded character and source correction discharge the
analytic hypotheses; no signal-growth assumption is introduced. -/
theorem source_correction_all_delay_error {κ ι : Type*}
    (eta0 : Character) (E : Finset (Ideal HeckeFamily.O)) (hE : ProbePhysical.SourceExclusions E)
    (c : ℝ) {a Z m : ℝ} (ha : 7 / 8 < a) (ha2 : a ≤ 2)
    (hbeta : HeckeZeroSupremum.beta < a) (hZ : 1 ≤ Z)
    (K : ℕ) (horder : 2 ≤ (7 / 8 : ℝ) * m * (K + 1))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A eta : κ → ι → ℂ) (h : SlotBounds S T w Q A eta (Z ^ m)) :
    let chi := eta0.excludePrimes E hE.prime
    let H := sourceCorrection eta0 E
    ‖slotResidueC chi H c a Z S T w Q A eta -
        (signal chi H c Z + FiniteResponse.applyTerms (signal chi H c) c Z
          (principalProductResponseTerms K S T w Q A eta))‖ ≤
      (S.card * (5 : ℝ) ^ S.card * 4 * 2 ^ (K + 1)) * endpointConstant 2 * Z ^ c := by
  exact slotResidueC_all_delay_error _ _ (sourceCorrection_differentiable eta0 E hE)
    (sourceCorrection_bound eta0 E hE) c ha ha2 hbeta hZ K horder S T w Q A eta h

end SevenEighths.PrincipalAllDelayReturn
end
end OAI
