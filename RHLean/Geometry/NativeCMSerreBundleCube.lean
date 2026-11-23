import RHLean.Geometry.NativeCMLineBundleCube
import RHLean.Geometry.NativeCMSerreBundleSymmetry

/-!
# The actual cube generator on the trace-frame Serre bundle

The eight-term cube of the already constructed signed bundle is
trivialized by pulling the seed's actual cube generator through each of
the four actual scheme maps for every pair of Hermitian frame indices.
The represented module remains the literal projective coefficient ideal.

This is native glue to the declaration cut documented in
`NativeCMLineBundleCube`. It deliberately exposes the seed cube generator:
neither the four previously proved polarization properties of the origin
bundle nor its Gaussian metric are silently treated as that theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Classical Pointwise nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace RHLean.Geometry.NativeCM.TraceFrame

open SerreScheme SchemeTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : NativeGeometricHost E} {D : TraceLattice H} {ε : ℤˣ}
    (F : TraceFrame D ε) {S : Scheme.{0}} {G : Over S}
    [GrpObj G] [IsCommMonObj G] (a : OAct (OK H) G)

/-- The cube trivialization is constructed on the same equalizer and the
same original signed Hermitian-frame atlas. -/
theorem schemeBundle_hasCubeGenerator {L : LB G.left}
    (hL : HasCubeGenerator G L) :
    HasCubeGenerator (F.schemeObj a) (F.schemeBundle a L) :=
  hL.linComb (F.schemeBundleMap a) (fun _ => inferInstance) F.schemeBundleExponent

end RHLean.Geometry.NativeCM.TraceFrame

namespace RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

open Formalism.HC Formalism.FrobeniusOrbits
open RHLean.Geometry RHLean.Geometry.NativeCM SerreScheme SchemeTheory

variable {φ : Frame} (H : HostRaw φ) [IsCMField H.E]
    (G : NativeGeometricHost H.E) (hbar : ∀ c : 𝓞 H.E, G.bar c = H.conj • c)
    (B : Ideal (𝓞 H.E))
    (hB : differentIdeal (𝓞 H.K) (𝓞 H.E) = B * (H.conj • B)) (ε : ℤˣ)
    {R : Type} [CommRing R] [_root_.IsReduced R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (a : OAct (OK G) (WeierstrassCurve.schemeOver W))

/-- A supplied genuine seed cube generator yields a literal generator
for the actual coefficient Serre bundle, with B chosen only once. -/
theorem coefficientSerreOriginBundle_hasCubeGenerator
    (hW : HasCubeGenerator (WeierstrassCurve.schemeOver W)
      (WeierstrassCurve.originLB W)) :
    HasCubeGenerator (coefficientSerreScheme H G hbar B hB ε a)
      (coefficientSerreOriginBundle H G hbar B hB ε W a) :=
  (coefficientSerreFrame H G hbar B hB ε).schemeBundle_hasCubeGenerator a hW

end RHLean.Analysis.AlpogeThin.NativeRawHostPolarization

end
