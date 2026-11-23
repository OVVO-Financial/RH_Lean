import RHLean.Geometry.NativeCMSerreEigenlattice
import RHLean.Geometry.NativeCMLineDegree

/-!
# All-place degree of the actual integral Serre eigenline

The coordinate map is the proved injective evaluation of the original
O_F tensor_OK B^-1 eigenspace. Its integral image is exactly the extension
of B^-1 D(E/K), so the existing AllWt degree applies with its finite index
unchanged. The positive conjugate-invariant metric profile remains an
explicit input. Identifying that profile with the arithmetic Lie norm of
the represented polarized Serre scheme is a separate obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open NumberField
open scoped Classical BigOperators Pointwise nonZeroDivisors

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM.LineDegree

/-- Exact original AllWt degree of the integral coordinate image of the
actual projective Serre eigenmodule, for the specified archimedean norm. -/
theorem eigenCoordinate_line_degree
    {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E)
    (hroot : (G.rt : H.E) = H.sqd)
    (hbar : ∀ a : 𝓞 H.E, G.bar a = H.conj • a)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B))
    (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Algebra H.E F]
    (n : (F →+* ℂ) → ℝ) (hn : ∀ σ, 0 < n σ)
    (hc : ∀ σ, n ((starRingEnd ℂ).comp σ) = n σ) :
    2 * RHLean.Geometry.AlpogeAllPlace.GlobalTheory.AllWt.deg (lineNorm n)
        (LinearMap.range (eigenCoordinate H G F B)) =
      -(∑ σ : F →+* ℂ, Real.log (n σ)) / (Module.finrank ℚ F : ℝ) +
        Real.log (rootDiscr H.K) - Real.log (rootDiscr H.E) := by
  rw [eigenCoordinate_range H G F hroot hbar B hB]
  exact coefficientDifferent_extended_line_degree H B hB F n hn hc

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
