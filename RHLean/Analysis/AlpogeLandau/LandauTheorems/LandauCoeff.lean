import RHLean.Analysis.AlpogeLandau.LandauZeroFreeCriterion
import RHLean.Analysis.AlpogeLandau.LandauTheorems.IteratedDerivLaplace

/-!
# Reconstructed analytic window dependency

Mathematical source: Levent Alpöge (with Claude), src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauCoeff.lean.
Pinned source: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/LandauCoeff.lean

This local proof reconstruction changes the module/namespace boundary and is
checked against RH_Lean's Lean/Mathlib versions. It imports no upstream compiled
artifact or terminal RH theorem. The source archive/mirror states no license;
this provenance notice does not assign a new license to that source material.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000


open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHLean.Analysis.AlpogeLandau

theorem landau_coeff {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) (k : ℕ) {s : ℂ} (hs : 2 < s.re) :
    (-1) ^ k * iteratedDeriv k Φ s / (k.factorial : ℂ) =
      ∫ u in Ioi (0 : ℝ), (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by
  obtain ⟨C, hC⟩ := hP.growth
  have hev : Φ =ᶠ[𝓝 s] (fun z => ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-z * u)) := by
    have hopen : IsOpen {z : ℂ | 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact hP.laplace z hz
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_laplace g hP.meas C hC k s hs, ← integral_const_mul,
    ← integral_div]
  congr 1
  funext u
  push_cast
  have e : ((-1 : ℂ)) ^ k * (-(u : ℂ)) ^ k = (u : ℂ) ^ k := by
    rw [← mul_pow]
    ring
  calc (-1 : ℂ) ^ k * ((g u : ℂ) * (-(u : ℂ)) ^ k * cexp (-s * u)) / (k.factorial : ℂ)
      = (g u : ℂ) * ((-1 : ℂ) ^ k * (-(u : ℂ)) ^ k) * cexp (-s * u) / (k.factorial : ℂ) := by ring
    _ = (g u : ℂ) * (u : ℂ) ^ k * cexp (-s * u) / (k.factorial : ℂ) := by rw [e]

end RHLean.Analysis.AlpogeLandau

end

