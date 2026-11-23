import RHLean.Geometry.NativeCMAllPlaceTangentPeriod
import RHLean.Geometry.NativeCMSerreEigenlatticeDegree

/-!
# Actual place-period mean in the original Serre eigenline degree

The same integral equation supplies every entry of the proved positive
place-indexed analytic profile. The original integral Serre eigenmodule
retains its literal B^-1 factor and different-twisted evaluation image.
The existing AllWt degree is therefore the full embedding mean of these
actual lattice periods plus the exact finite discriminant correction.

This does not replace the period mean by a class-group mean and does not
identify the analytic profile with a scheme-theoretic Serre Lie norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical BigOperators Pointwise nonZeroDivisors

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM
open RHLean.Geometry.NativeCM.LineDegree RHLean.Geometry.NativeCM.AllPlaceTangentPeriod

/-- The complete embedding sum comes from uniformizations of one and the
same integral equation. No arithmetic mean or tangent-metric premise is
supplied; the explicitly constructed analytic profile is retained. -/
theorem eigenCoordinate_actualPeriod_degree
    {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E)
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Algebra H.E F]
    (W : WeierstrassCurve (𝓞 F)) (hΔ : W.Δ = 1) :
    2 * RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg
        (lineNorm (embeddingProfile W hΔ))
        (LinearMap.range (eigenCoordinate H G F B)) =
      (∑ σ : F →+* ℂ, PeriodArithmetic.latticeLogPeriod
        (lattice W hΔ (InfinitePlace.mk σ))) / (Module.finrank ℚ F : ℝ) +
        Real.log (rootDiscr H.K) - Real.log (rootDiscr H.E) := by
  rw [eigenCoordinate_line_degree H G hroot hbar B hB F
    (embeddingProfile W hΔ) (embeddingProfile_pos W hΔ) (embeddingProfile_conjugate W hΔ)]
  rw [← Finset.sum_neg_distrib]
  simp_rw [neg_log_embeddingProfile]

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
