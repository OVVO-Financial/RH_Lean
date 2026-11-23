import RHLean.Analysis.AlpogeThin.NativeRayRealZeroGap
import RHLean.Analysis.AlpogeThin.NativeRayZeroFreeRegion
import RHLean.Analysis.AlpogeThin.NativeRayExceptionalZero

/-!
# Analytic continuation of the same constructed ray-ideal family

The arithmetic constructor fixes the field, root, modulus, ray group and
coefficients once. These theorems apply the reconstructed analytic proofs to
that literal family. The parameter remains B = 4*d*M^2, with the original
300*B growth cost. No analytic family, continuation, nonvanishing or desired
prime-window bound is an application input.

The source arguments are attributed in the imported native proof modules.
This attachment imports neither an original compiled artifact nor an RH theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open NumberField
open scoped Classical

namespace RHLean.Analysis.AlpogeThin.NativeRay.LFam

variable (K : Type) [Field K] [NumberField K] (d M : ℕ) (r : K)
    (hp : d.Prime) (hd : d % 4 = 3) (hd100 : 100 ≤ d)
    (hr : r ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2)
    (hM : 3 ≤ M) (D : RayData K M)

local notation "𝓕" => ofRayData K d M r hp hd hd100 hr h2 hM D

/-- Continuation, series identification, original polynomial growth and real
symmetry for the actual ideal coefficients on the given ray datum. -/
theorem ofRayData_continuation_growth (χ : AddChar (Additive D.G) ℂ) :
    AnalyticOnNhd ℂ ((𝓕).F χ) {s : ℂ | 1 / 2 < s.re} ∧
    (∀ s : ℂ, 1 < s.re → LSeriesSummable ((𝓕).aChi χ) s ∧
      (𝓕).F χ s = (if χ = 1 then s - 1 else 1) * LSeries ((𝓕).aChi χ) s) ∧
    (∀ s : ℂ, 11 / 20 ≤ s.re →
      ‖(𝓕).F χ s‖ ≤ 300 * (4 * (d : ℝ) * (M : ℝ) ^ 2) * (‖s‖ + 1) ^ 2) ∧
    (χ * χ = 1 → ∀ s : ℂ,
      (𝓕).F χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) ((𝓕).F χ s)) := by
  obtain ⟨ha, hls, hg, hr⟩ := RayCont.continuation_growth 𝓕 χ
  refine ⟨ha, hls, ?_, hr⟩
  intro s hs
  change ‖(𝓕).F χ s‖ ≤ 300 * (𝓕).B * (‖s‖ + 1) ^ 2
  exact hg s hs

/-- The complete prime-power logarithmic derivative, including the principal
pole correction, and nonvanishing to the right of one on the same family. -/
theorem ofRayData_logDeriv (χ : AddChar (Additive D.G) ℂ) (s : ℂ)
    (hs : 1 < s.re) :
    LSeriesSummable ((𝓕).lamChi χ) s ∧
    ((s.re - 1) / s.re) ^ 2 ≤ ‖LSeries ((𝓕).aChi χ) s‖ ∧
    (𝓕).F χ s ≠ 0 ∧
    -(deriv ((𝓕).F χ) s / (𝓕).F χ s) +
      (if χ = 1 then 1 / (s - 1) else 0) = LSeries ((𝓕).lamChi χ) s := by
  exact LogDeriv.logDeriv_F 𝓕 χ s hs

/-- Real characters of the actual ray group have nonzero regularized value
at one, using the original quantitative real-character lower bound. -/
theorem ofRayData_real_nonvanishing (χ : AddChar (Additive D.G) ℂ)
    (hχ : χ * χ = 1) : (𝓕).F χ 1 ≠ 0 := by
  obtain ⟨A, c, _hA, hc, hbound⟩ := RealChar.norm_F_one_ge
  have hB : 0 < (𝓕).B := lt_of_lt_of_le (by norm_num) (𝓕).B_ge
  apply norm_pos_iff.mp
  exact (div_pos hc (Real.rpow_pos_of_pos hB A)).trans_le (hbound 𝓕 χ hχ)

end RHLean.Analysis.AlpogeThin.NativeRay.LFam

end
