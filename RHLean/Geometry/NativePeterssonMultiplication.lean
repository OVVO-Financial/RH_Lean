import Mathlib

/-!
# Pointwise section size pays the actual Petersson multiplication operator

This is the analytic construction in `GlobalTheory.ShortDet.petAt_mul_le`
and `normW_mul_pull_le` from `CardLeOfDetEqZero.lean`, upstream commit
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.

The metric is explicitly the real value of the weighted `eLpNorm` with exponent
two. Products use the product of the two original pointwise weight factors.
For the source substitution, `ev` is complex evaluation on the frame and the
weight is `lieFacZ * nfac`; the source's `homN_mul` and `petAt_eq` identify
these definitions with its Petersson norm. The finite `eLpNorm` and measurable
product are explicit hypotheses, including the measurability requirement of
the pinned native Mathlib API. No operator-norm bound is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory

namespace RHLean.Geometry

def nativeWeightedPointNorm {R Ω : Type} [CommRing R]
    (ev : Ω → R →+* ℂ) (weight : Ω → ℝ) (f : R) (x : Ω) : ℝ :=
  weight x * ‖ev x f‖

def nativePeterssonNorm {R Ω : Type} [CommRing R] [MeasurableSpace Ω]
    (μ : Measure Ω) (ev : Ω → R →+* ℂ) (weight : Ω → ℝ) (f : R) : ℝ :=
  (eLpNorm (nativeWeightedPointNorm ev weight f) 2 μ).toReal

theorem nativeWeightedPointNorm_nonneg {R Ω : Type} [CommRing R]
    (ev : Ω → R →+* ℂ) (weight : Ω → ℝ)
    (hweight : ∀ x, 0 ≤ weight x) (f : R) (x : Ω) :
    0 ≤ nativeWeightedPointNorm ev weight f x :=
  mul_nonneg (hweight x) (norm_nonneg _)

theorem nativeWeightedPointNorm_mul {R Ω : Type} [CommRing R]
    (ev : Ω → R →+* ℂ) (weight weightu : Ω → ℝ) (f u : R) (x : Ω) :
    nativeWeightedPointNorm ev (fun y => weight y * weightu y) (f * u) x =
      nativeWeightedPointNorm ev weight f x * nativeWeightedPointNorm ev weightu u x := by
  simp only [nativeWeightedPointNorm, map_mul, norm_mul]
  ring

/-- The actual measure-preserving action and point-evaluation identity give
Petersson isometry. No norm-invariance premise is supplied. -/
theorem nativePeterssonNorm_pull_eq {R Ω : Type} [CommRing R]
    [MeasurableSpace Ω] (μ : Measure Ω) (ev : Ω → R →+* ℂ)
    (weight : Ω → ℝ) (pull : R →+* R) (act : Ω → Ω)
    (hact : MeasurePreserving act μ μ)
    (hweight : ∀ x, weight (act x) = weight x)
    (heval : ∀ x f, ev x (pull f) = ev (act x) f)
    (f : R) (hmeas : AEStronglyMeasurable (nativeWeightedPointNorm ev weight f) μ) :
    nativePeterssonNorm μ ev weight (pull f) = nativePeterssonNorm μ ev weight f := by
  have hpoint : nativeWeightedPointNorm ev weight (pull f) =
      nativeWeightedPointNorm ev weight f ∘ act := by
    funext x
    simp only [nativeWeightedPointNorm, Function.comp_apply, heval, hweight]
  unfold nativePeterssonNorm
  rw [hpoint, eLpNorm_comp_measurePreserving hmeas hact]

/-- The pointwise size of the SAME section pays multiplication on weighted
Petersson `L²`, with no host, component, or dimension factor. -/
theorem nativePeterssonNorm_mul_le {R Ω : Type} [CommRing R]
    [MeasurableSpace Ω] (μ : Measure Ω) (ev : Ω → R →+* ℂ)
    (weight weightu : Ω → ℝ) (hweight : ∀ x, 0 ≤ weight x)
    (hweightu : ∀ x, 0 ≤ weightu x) (f u : R) {B : ℝ} (hB : 0 ≤ B)
    (hfin : eLpNorm (nativeWeightedPointNorm ev weight f) 2 μ ≠ ⊤)
    (hmeas : AEStronglyMeasurable
      (nativeWeightedPointNorm ev (fun x => weight x * weightu x) (f * u)) μ)
    (hu : ∀ᵐ x ∂μ, nativeWeightedPointNorm ev weightu u x ≤ B) :
    nativePeterssonNorm μ ev (fun x => weight x * weightu x) (f * u) ≤
      B * nativePeterssonNorm μ ev weight f := by
  have hbound : ∀ᵐ x ∂μ,
      ‖nativeWeightedPointNorm ev (fun y => weight y * weightu y) (f * u) x‖ ≤
        B * ‖nativeWeightedPointNorm ev weight f x‖ := by
    filter_upwards [hu] with x hx
    rw [Real.norm_of_nonneg (nativeWeightedPointNorm_nonneg ev _
      (fun y => mul_nonneg (hweight y) (hweightu y)) _ x),
      Real.norm_of_nonneg (nativeWeightedPointNorm_nonneg ev weight hweight f x),
      nativeWeightedPointNorm_mul, mul_comm _ (nativeWeightedPointNorm ev weightu u x)]
    exact mul_le_mul_of_nonneg_right hx
      (nativeWeightedPointNorm_nonneg ev weight hweight f x)
  have hnorm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hbound 2
  have hre := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hnorm
  simpa only [nativePeterssonNorm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hB] using hre

/-- Pull the input and output back by the inverse group element, use the
pointwise bound on `u`, then use the original two metric isometries. Thus one
short section pays EVERY translated multiplication map. -/
theorem nativePeterssonNorm_mul_pull_le
    {H K R Ω : Type} [Group H] [Field K] [CommRing R] [Algebra K R]
    [MeasurableSpace Ω] (st : H → R →ₐ[K] R)
    (h1 : ∀ f, st 1 f = f)
    (hmul : ∀ h h' f, st (h * h') f = st h' (st h f))
    (Cm C : Submodule K R) (hCm : ∀ h, ∀ f ∈ Cm, st h f ∈ Cm)
    (μ : Measure Ω) (ev : Ω → R →+* ℂ) (weight weightu : Ω → ℝ)
    (hweight : ∀ x, 0 ≤ weight x) (hweightu : ∀ x, 0 ≤ weightu x)
    (hisom : ∀ h, ∀ f ∈ Cm,
      nativePeterssonNorm μ ev weight (st h f) = nativePeterssonNorm μ ev weight f)
    (hiso : ∀ h, ∀ f ∈ C,
      nativePeterssonNorm μ ev (fun x => weight x * weightu x) (st h f) =
        nativePeterssonNorm μ ev (fun x => weight x * weightu x) f)
    (u : R) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ᵐ x ∂μ, nativeWeightedPointNorm ev weightu u x ≤ B)
    (hfin : ∀ f ∈ Cm, eLpNorm (nativeWeightedPointNorm ev weight f) 2 μ ≠ ⊤)
    (hmeas : ∀ f ∈ Cm, AEStronglyMeasurable
      (nativeWeightedPointNorm ev (fun x => weight x * weightu x) (f * u)) μ)
    (h : H) (f : Cm) (hproduct : (f : R) * st h u ∈ C) :
    nativePeterssonNorm μ ev (fun x => weight x * weightu x) ((f : R) * st h u) ≤
      B * nativePeterssonNorm μ ev weight f := by
  have hcancel : st h⁻¹ (st h u) = u := by
    rw [← hmul, mul_inv_cancel, h1]
  have hproduct_eq : st h⁻¹ ((f : R) * st h u) = st h⁻¹ f * u := by
    rw [map_mul, hcancel]
  rw [← hiso h⁻¹ _ hproduct, hproduct_eq]
  exact (nativePeterssonNorm_mul_le μ ev weight weightu hweight hweightu
    (st h⁻¹ f) u hB (hfin _ (hCm h⁻¹ _ f.2))
    (hmeas _ (hCm h⁻¹ _ f.2)) hu).trans_eq
      (congrArg (B * ·) (hisom h⁻¹ f f.2))

end RHLean.Geometry

end
