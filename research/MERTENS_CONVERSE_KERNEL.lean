import «research.MERTENS_CONVERSE_SUBPOWER»
import «research.MERTENS_CONVERSE_MELLIN_DECAY»
import «research.MERTENS_CONVERSE_CONTOUR»

/-!
# Integrable kernel for the reverse Mertens exponent map

The actual regularized reciprocal is multiplied by the actual smoothing
Mellin transform. A fractional smoothing loss combines with a smaller
reciprocal growth exponent to give an integrable height weight. Constants
are uniform in the height, smoothing parameter and endpoint.
-/

noncomputable section

namespace RHLean.Analysis.MertensExponent

open Complex Filter Set MeasureTheory
open scoped Topology
local notation "I" => Complex.I

/-- The actual smoothed Perron kernel, with the removable value filled at one. -/
def regularizedSmoothedIntegrand (ν : ℝ → ℝ) (ε X : ℝ) (s : ℂ) : ℂ :=
  nativeInvZetaRegularized s *
    mellin (fun x => (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s

/-- The regularized kernel agrees with the repository's original kernel off one. -/
theorem regularizedSmoothedIntegrand_eq_native (ν : ℝ → ℝ) (ε X : ℝ)
    {s : ℂ} (hs : s ≠ 1) :
    regularizedSmoothedIntegrand ν ε X s = nativeSmoothedMobiusIntegrand ν ε X s := by
  unfold regularizedSmoothedIntegrand nativeSmoothedMobiusIntegrand strongMertensSmoothedIntegrand
  rw [regularizedReciprocal_eq_inv hs]

/-- Holomorphy on the complete exponent half-plane, including one. -/
theorem regularizedSmoothedIntegrand_differentiableAt
    {a : ℝ} (ha : 0 ≤ a) (hstrip : ZerosInSymmetricStrip a)
    {ν : ℝ → ℝ} (hdiff : ContDiff ℝ 1 ν)
    (hsupp : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hmass : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1)
    {ε X : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X)
    {s : ℂ} (hs : a < s.re) :
    DifferentiableAt ℂ (regularizedSmoothedIntegrand ν ε X) s := by
  have hrec := regularizedReciprocal_differentiableAt_of_strip ha hstrip hs
  have hmel := Smooth1MellinDifferentiable hdiff hsupp ⟨hε, hε1⟩
    hnonneg hmass (ha.trans_lt hs)
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (X : ℂ) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl (by exact_mod_cast hX.ne'))
  exact (hrec.mul hmel).mul hpow

/-- A real-part margin at most one controls the entire complex norm.
The inequality itself does not require positivity of the margin. -/
theorem norm_ge_scaled_height {σ : ℝ} (hσ1 : σ ≤ 1)
    {s : ℂ} (hs : σ ≤ s.re) : (σ / 2) * (1 + |s.im|) ≤ ‖s‖ := by
  have hreal : σ ≤ ‖s‖ := hs.trans (Complex.re_le_norm s)
  have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hmul : σ * |s.im| ≤ |s.im| := by
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right hσ1 (abs_nonneg s.im)
  nlinarith

/-- An integrable height weight for every positive fractional exponent. -/
def converseHeightWeight (q t : ℝ) : ℝ := (1 + |t|) ^ (-1 - q / 2)

theorem converseHeightWeight_nonneg (q t : ℝ) : 0 ≤ converseHeightWeight q t :=
  Real.rpow_nonneg (by positivity) _

theorem converseHeightWeight_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (converseHeightWeight q) := by
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 1 + q / 2 := by
    simp only [Module.finrank_self, Nat.cast_one]
    linarith
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) hdim
  have heq : (fun t : ℝ => (1 + ‖t‖) ^ (-(1 + q / 2))) = converseHeightWeight q := by
    funext t
    simp only [converseHeightWeight, Real.norm_eq_abs]
    congr 1
    ring
  rw [heq] at h
  exact h

/-- Actual reciprocal growth and actual Mellin decay yield a uniform
integrable bound; the arithmetic endpoint enters only through X^Re(s). -/
theorem regularizedSmoothedIntegrand_bound
    {a σ q : ℝ} (ha : 0 ≤ a) (haσ : a < σ) (hσ : σ < 1)
    (hstrip : ZerosInSymmetricStrip a) (hq : 0 < q) (hq1 : q ≤ 1)
    {ν : ℝ → ℝ} (hdiff : ContDiff ℝ 1 ν)
    (hsupp : Function.support ν ⊆ Set.Icc (1 / 2) 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε X : ℝ, 0 < ε → ε < 1 → 0 < X →
      ∀ s : ℂ, σ ≤ s.re → s.re ≤ 2 →
        ‖regularizedSmoothedIntegrand ν ε X s‖ ≤
          K * ε ^ (-q) * X ^ s.re * converseHeightWeight q s.im := by
  have hσ0 : 0 < σ := ha.trans_lt haσ
  obtain ⟨Cz, hCz, hz⟩ := regularizedReciprocal_subpower_of_strip
    ha haσ hσ hstrip (half_pos hq)
  obtain ⟨Cm, hCm, hm⟩ := smoothingMellin_fractional_decay hdiff hsupp
  let K : ℝ := Cz * Cm * (σ / 2) ^ (-1 - q)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro ε X hε hε1 hX s hsσ hs2
  have hspos : 0 < s.re := hσ0.trans_le hsσ
  have hbase : 0 < 1 + |s.im| := by positivity
  have hmargin : 0 < (σ / 2) * (1 + |s.im|) := by positivity
  have hnormPower : ‖s‖ ^ (-1 - q) ≤
      (σ / 2) ^ (-1 - q) * (1 + |s.im|) ^ (-1 - q) := by
    have h := Real.rpow_le_rpow_of_nonpos hmargin
      (norm_ge_scaled_height hσ.le hsσ) (by linarith : -1 - q ≤ 0)
    rwa [Real.mul_rpow (by positivity) hbase.le] at h
  have hmel := hm q hq.le hq1 s hspos hs2 ε hε hε1
  have hrec := hz s hsσ hs2
  have hpX : 0 ≤ X ^ s.re := Real.rpow_nonneg hX.le _
  have hpε : 0 ≤ ε ^ (-q) := Real.rpow_nonneg hε.le _
  have hrec0 : 0 ≤ Cz * (1 + |s.im|) ^ (q / 2) := by positivity
  have hmel0 : 0 ≤ Cm * ε ^ (-q) := mul_nonneg hCm.le hpε
  have hexponents : (1 + |s.im|) ^ (q / 2) * (1 + |s.im|) ^ (-1 - q) =
      converseHeightWeight q s.im := by
    rw [← Real.rpow_add hbase]
    unfold converseHeightWeight
    congr 1
    ring
  unfold regularizedSmoothedIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX]
  calc
    ‖nativeInvZetaRegularized s‖ * ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) s‖ * X ^ s.re ≤
        (Cz * (1 + |s.im|) ^ (q / 2)) *
          (Cm * ε ^ (-q) * ‖s‖ ^ (-1 - q)) * X ^ s.re :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hrec hmel (norm_nonneg _) hrec0) hpX
    _ ≤ (Cz * (1 + |s.im|) ^ (q / 2)) *
          (Cm * ε ^ (-q) * ((σ / 2) ^ (-1 - q) * (1 + |s.im|) ^ (-1 - q))) * X ^ s.re :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnormPower hmel0) hrec0) hpX
    _ = K * ε ^ (-q) * X ^ s.re *
          ((1 + |s.im|) ^ (q / 2) * (1 + |s.im|) ^ (-1 - q)) := by dsimp [K]; ring
    _ = K * ε ^ (-q) * X ^ s.re * converseHeightWeight q s.im := by rw [hexponents]

/-- A uniform constant for integrating the height weight, including the
normalization of the vertical contour integral. -/
def converseIntegralConstant (q : ℝ) : ℝ :=
  (‖(1 / (2 * Real.pi * I) : ℂ)‖ + 1) *
    ((∫ t : ℝ, converseHeightWeight q t) + 1)

theorem converseIntegralConstant_pos (q : ℝ) : 0 < converseIntegralConstant q := by
  have hi : 0 ≤ ∫ t : ℝ, converseHeightWeight q t :=
    integral_nonneg (converseHeightWeight_nonneg q)
  unfold converseIntegralConstant
  positivity

/-- A continuous vertical restriction dominated by the height weight is integrable. -/
theorem integrable_vertical_of_heightBound {q u K : ℝ} (hq : 0 < q)
    {f : ℂ → ℂ} (hf : Continuous (fun t : ℝ => f ((u : ℂ) + t * I)))
    (hbound : ∀ t : ℝ, ‖f ((u : ℂ) + t * I)‖ ≤ K * converseHeightWeight q t) :
    Integrable (fun t : ℝ => f ((u : ℂ) + t * I)) :=
  ((converseHeightWeight_integrable hq).const_mul K).mono'
    hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- Integrating a proved pointwise majorant bounds the normalized vertical
integral. No assumed inverse-transform estimate enters this lemma. -/
theorem verticalIntegral_norm_le_heightBound {q u K : ℝ} (hq : 0 < q) (hK : 0 ≤ K)
    {f : ℂ → ℂ}
    (hbound : ∀ t : ℝ, ‖f ((u : ℂ) + t * I)‖ ≤ K * converseHeightWeight q t) :
    ‖VerticalIntegral' f u‖ ≤ converseIntegralConstant q * K := by
  have hi : 0 ≤ ∫ t : ℝ, converseHeightWeight q t :=
    integral_nonneg (converseHeightWeight_nonneg q)
  have hInt := norm_integral_le_of_norm_le
    ((converseHeightWeight_integrable hq).const_mul K) (Filter.Eventually.of_forall hbound)
  rw [integral_const_mul] at hInt
  have hInt' : ‖∫ t : ℝ, f ((u : ℂ) + t * I)‖ ≤
      K * ((∫ t : ℝ, converseHeightWeight q t) + 1) :=
    hInt.trans (mul_le_mul_of_nonneg_left (by linarith) hK)
  calc
    ‖VerticalIntegral' f u‖ =
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖∫ t : ℝ, f ((u : ℂ) + t * I)‖ := by
      simp only [VerticalIntegral', VerticalIntegral, norm_smul, Complex.norm_I, one_mul]
    _ ≤ (‖(1 / (2 * Real.pi * I) : ℂ)‖ + 1) *
        (K * ((∫ t : ℝ, converseHeightWeight q t) + 1)) :=
      mul_le_mul (by linarith) hInt' (norm_nonneg _) (by positivity)
    _ = converseIntegralConstant q * K := by unfold converseIntegralConstant; ring

end RHLean.Analysis.MertensExponent
