import RHLean.Analysis.AlpogeThin.NativeDyadicHostDer
import RHLean.Geometry.NativeGeometricHost

/-!
# One arithmetic host for the geometric and theta constructions

The complete derived host and the exact geometric-host record use the same
field, integral root, conjugation and positive complex root. In particular,
the geometric signature is the literal original CM type, not an independently
selected half of the embeddings. All host inputs come from the original
arithmetic regime; the geometric datum and its moduli remain further work.
-/

set_option autoImplicit false

noncomputable section

open NumberField

namespace RHLean.Geometry

open RHLean.Analysis RHLean.Analysis.AlpogeThin
open Formalism.FrobeniusOrbits

/-- Assemble the geometric host over the SAME completely derived arithmetic
host, with no additional CM, root or unramifiedness hypothesis. -/
def nativeDyadicGeometricHostOfDerived
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    NativeGeometricHost H.E := by
  let H := nativeDyadicHostAx e q d he hH
  let _ : IsCMField H.E := H.der.cm
  have hqmod := hH.2.2.1
  have hdmod := hH.2.2.2.1
  exact nativeDyadicGeometricHost e q d (by omega) (by omega) hdmod

@[simp] theorem nativeDyadicGeometricHostOfDerived_root
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    ((nativeDyadicGeometricHostOfDerived e q d he hH).rt : H.E) = H.sqd := rfl

/-- The same actual conjugation acts on the geometric integral lattice. -/
theorem nativeDyadicGeometricHostOfDerived_bar
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (a : 𝓞 (nativeDyadicHostAx e q d he hH).E) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    (((nativeDyadicGeometricHostOfDerived e q d he hH).bar a : 𝓞 H.E) : H.E) =
      H.conj (a : H.E) := by
  change alpogeNativeHostConj e q d (a : alpogeNativeHostField e q d) =
    (nativeDyadicHostRaw e q d he hH).conj (a : alpogeNativeHostField e q d)
  rw [nativeDyadicHostRaw_conj e q d he hH]

/-- The geometric positive rows and the arithmetic CM type coincide exactly. -/
theorem nativeDyadicGeometricHostOfDerived_inPsi
    (e q d : ℕ) [Fact q.Prime] [Fact d.Prime]
    (he : 2 ≤ e) (hH : HostHyp q d)
    (τ : (nativeDyadicHostAx e q d he hH).E →+* ℂ) :
    let H := nativeDyadicHostAx e q d he hH
    let _ : IsCMField H.E := H.der.cm
    (nativeDyadicGeometricHostOfDerived e q d he hH).InPsi τ ↔ τ ∈ H.cmType := by
  change nativeDyadicThetaPositive e q d τ ↔
    τ (alpogeNativeSqrtD e q d) = Complex.I * (Real.sqrt d : ℂ)
  have hdmod := hH.2.2.2.1
  exact nativeDyadicThetaPositive_iff e q d (by omega) τ

end RHLean.Geometry

end
